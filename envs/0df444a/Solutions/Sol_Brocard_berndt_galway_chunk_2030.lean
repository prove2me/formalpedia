-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:29:22.827646+00:00
-- url     : https://prove2.me/submissions/1dd9ac95-59a9-4ec9-ac7b-317c3ea45ce3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 364928057 ≤ n < 365107913 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 364929307 1250 364928057 364928071
    0x20f07140102031308031b0c0901061b06050f0114040221100b0c07091404030e06030a0608031b070b1204061104090f050403021e21090607030c17040509 67
    0x54200280d4180c0d00c01c009440002d078520303105510b2160f8916940fa140d81c0003c281c0c0d150004450341e07120591038001070809500381c000d130404100740e183c400100c69606c01004090200e01140d030300b641c0495418000c1e980250022280c1034140d51412142d0b80d94000d5003203d040c0614010701000015000b0002c06c100910356104a2070900e40d1031500302400c407036040d0014441400046000c038540080000d451081e0346c440740c4100001c400c00a040b01e618801220001d0000d040002000300030b08069010f140c2210000e2408602241c451241c241103800041100300c940345450700c84608074034100b01650042441c5900140b0302428185a40c401e5040184003030200c90700c400ca450300d03403019001150003c101c0d100d030401c0402d80304281c61002e800103880540040c8100c2100ca61100d920316840e6510315011030003042e0450500860320424400d542d2901c055803404c0c07000d1032458807420001d204062207070340c4d41c941c40c1030b25280501c540c000c4a020050200802c0c00184507544607a0701d036a8101403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 364930557 1250 364929307 364929329
    0x3090f05031203011e1a04140616020114190e180717060102030706020705010c1106130308060307031b090c020105070903020402180310090b060906030607120b0d03170601020f07 78
    0x504280c88194017189070740400d2a04403001c0c00542c1c2c1c01d40040140c006d03602500714449030203103079a003003108500803d8242610703484802d01680042d8000c40d0036080f20a1141c004500306404100c1c03007622555000840d502040810318041c0603850b1014040c1074504054402000c54100404020903240d0030f062811540780c0b000000c0740c504ea0003001981c16095000c60295500d410502e00140130b001b41c2c041407c041000c80425030035800e80421124070444212445080502e45600c00302e90b0400080d2455805004119002c0b0204612500f50780c45604a5030b0706030b9050349403460102c100c2e510b500101c7d0441e45000c0901080603408a5824101d07030f0100c0e0301503242c4030071441f00d4074510070b0380940781c1d07240c07041c0d45030705a041c611074110100300c0d8092440000141d680c0b40c01d01c466404100d94117036042d002100090407860062070b5203105215590400074905a032400450381213032180d082507003c40d540072481e64080154102640c0d01940c01c1c40580f5940718048600c40d5904018041c403030101c0307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 364931807 1250 364930557 364930589
    0x18030912030509060406110613170d0b0a0308030613062103020102130602010c0e0324041406130c06020a020d150b040203011409060114070b0606120403090f0503120301 74
    0x161180b800d54807455401040d2581d59a603c2c0c0000e0000c02c400c80f00704005003d1180043c002556550740c11a25617002010032680e0b030020010107a95912890748048000c0d80d607842c2c01c0d200c0e1560740003100614440d0904c81c0d600d040c4001080001c0c00030406234600c0760700b05481480905006d00a440c00e12140504200c90010245420380c064061904401c686841c40c60300000c10300d50540011640138a603451381c04010306110145078841c0b460314100c82d0103c80c5512002252079104d84515441030140652100590395085820f0130503400b07513030011115003921000340074064502304840c02000c450005043c40e060b5039001c80c850880600000c0c00110b6140f8035050400c00d15013100302c007880020000c556075a101c545207201400742c0007500e03028480c10800140c2c00c1d4050036050100542c012040d600342004d50361042d8501c003000380040d030409000d209035100c110a1800c0240242d21a80301c003d031060420040001c0181ca40e8802d6200354000180401c500d5040070441c0c1c10349580a43c0b01c4464 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364933057 1250 364931807 364931813
    0xb0d0504150507030506010e04060e0f0604181b150215040804090e070905010e010f0306020a0504030c0b030910050c160c1a0a12023a110d18030912 65
    0x10701e00a44214192400e00d401c1119965142c0c2c0260720481c405d0302c1d01580c41c0c05010500c0f0482d5103600601c1e100364000740125044144260f01c10340e004100501c00305010071040701c20800c0c1e4800007804c075044e00d0585e000a403e01407440881c4050004030040c40245c00c81824020b68600301c40010308000c04c0c000e00400c0510402400300c8000e042401018018034030210310055454500d80b007000080340c6041c0001c55052184010326040303031703d03030240614410708607110500203600114200081c003204100000000d40f917501302e03100400e10000303170030b4880c605a0744540c203000c44040600c043c1c5203401700f04142004c00380151100d05a0007001400c0444092500c1800202c00f07030005104d0404c50420441c03020302100040600d00301682d580030800b0038031600e40040c0e00404400d540109070f14829020004079012002d412012f0b48581003902c400e1610424040b01c2407544010855040000c1115110301c0368002d03180c0c4041e030424501c4e542107458400528110980c000c1c0280c20001d514800e043c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 364934307 1250 364933057 364933073
    0xa0303030f1104230d030e0909071805090f0d270807170d0c02010e010503071806020706021b131d10050109060501020a03090b092d0f0a0b0d0504 64
    0x740d6140d50042d96101d8681143c4075a42845034030301036801c07150540303400c004d080c0f524040400341d902d40c5407209420b1420081207a03800c8006c0038501144114a40090400c64414004058051080c1c002030181409541ca509149030f40c422040c4a03403020500e0401e1a92100403400100201000c16034000d8400f64441e04610aa503c840c950348103840c0c021902d000144481c84031040c40c602180c2d484003100e842074460051610001c5e02056040e04d03452501d5018400440c0d00c000c4600d0407100300004800040c60351000c1e501b150006030b001000038495542c0412001580180c03030140380303c0b080c0e500340008141850080003481c03e5911240240040643c0c0240204407441c19015038041588512a0100800007407080042031401c10b600041c0719400402c000500c2038045c1d45407000c250070500c80700d602d5807000c26400e8010395031104900d41c84001550780d2800c1c41c1d108001922446000f01000303000c0d400c139072030107201d110541c004002100d2040c04a658103a6821030125040ea44d50403c82c0e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 364935557 1250 364934307 364934321
    0x3070c0213020405040b030a121229011107140f0d1703040b010902094207060609020c03040303030c120509010507080906060f040515060a0f08150a0303030f 69
    0x241001c801000c5460480258010300142d602c1602c3c104103400020303007003640e1850f60100151191025083e10b02e9103d00c60350403408060310205000c1000c03801d001146070450a01c0e4400d0241690014004800c0e41e413091480100340d24a1004248517414003007515200c0d201e07200c010b485000d03400d2100300e1381d4561030541e1100c507030031a0340c2c0000328524408984043d4801c58040307411001c401c0000c41c211b0468803c0e2103014001420b45d0709004580c41186000c0c81d91501d40c091544800d41100901e22022000f00c54460640c00d2010f440d5807a919084094542540010444500602c45c0e0341e1403000000a40c0c080344d42500c0e0110b05008504002d4401c40e8448100061050500e4104449214150000c501a41c001d5886200d95510180940c0c0c0b180c070305640c095804119003030100801d103415001203070487e400300c00150825007204002042e550012100d240890049258082d01c0d64100c010941d1100c0b200d0585625483c4100003d10356500038003004003810342c1c42c18901811001503008038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 364936807 1250 364935557 364935559
    0xc091806010f14030105040f0f02041104080c01020115060c03081009050a0209030f0c010504140a05060304030c0c0e0708010b22080606040c0c0b060d0212010c03050712051b03070c02 80
    0x664558692540300b1110701d040c0100c0b81c100000d088107919500303052183d588030b0b81d00081502c2c0c0d00c017450740d51480000046041a40d009841c4caa5200348940d000000b4401016800c0003081b500100030006400d41d120001244d8000c02440010088581c20a0010f5440b0ba850b103050681d994030800c0211555610340c214940035441c12040007000c000c258014500141c0807030031510001c030103c000039032300c0c07880f0030b03509000900c103100030071030428900c0b45008000350040c0440b0605d0b4031b607004039183d0742040f14180c00081e950b1188e0b00512100c0b03c00080a00f910342c1c0d460089103402c1c1000303400311606105008414400007044890301c148920004681200140741c9206955980c8450fa034400c01552842d00c200c1c41c1c01740c2c2c000403500402e140141254011514840c9646039810814604000d940c1030380c200d4034044034030b4000750081c45180185c0280e500e0004860604034402081110b001c2c0141d030405280005100340704640034920304074404228031156036940c1324070080f5002e2003680320003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 364938057 1250 364936807 364936813
    0x110d0506180c1c0c020d0f03060503060a0501170a0302030f25060608010b01051303020603100f08030703030605010c02030c1212040320030d080f100b0a02100b060a020c0918 76
    0x2002100d01c1500080290f11031007a40400f62000f100001811118240e50090150303000020710740d1518081c014941c140180340c10006840e640d03803c0840c0c101002200c3c044100b80c1d940d0011f202078103101022003e0010241d006040d960000ea40107507491150f41e14280c0400804181d0084000300240c003000144c1ea981c91070365410703440e0701d0001c01514250245560315400e00c200c401d1154807400984d81c0300707a600101100e950f031446d020302106a2001d000140d0401e11000301181c0000c035295400010700860303009603920b03d61400c00504403101500007504001080da6070030050303a000682402c12203811070703012100403c80d6088901d4103c011800418840012400205000700507042c1410020340e07200400c2d141c070104c000c060f00c1e9880e04c507061000c01c2218000c220000c6808000301c0c0c0c0700c501c240c018568a5181c6805401c40c0d01310307201d80700041e0702139003050700c5a400070f0041c924015400c3d02c1403400c0452900d00603440f0086c40b00440e000b00e04000004100b05001c0071900d400e0310200c019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 364939307 1250 364938057 364938061
    0x81204020d02040f1b030507050706051b03010b130e0106050f0d0906180311070303050304031b02030118030f0914011422170601030b0a0507050c12031801110d050618 73
    0x30b104083c03c0c5d81e440084d03209a4202820300214040c1c099917110314070580d5100c0c501078160342c0d030f64001c0002500c1c40004c1d0180300641035224000f540190302814074211181e4031004419544411a400e64000682c034900c50740c0104103141c1c00c0030a445008511450313032078603526030405400017010f40d12409004c80c3d0174041e5052210b0714811010310014029941d00d852008948101c507070702c08882c403004000072820000140401d00c00c5402101d281181c0e00d2010742101d035900000d0a581600b0341300140f040e40711828504068020f1600c07589000303181468418180b811a241040c030b844880140d040c842e02602007032140c0c05400840b44004801621503041080300314041027040030602804444144000240d124203200044490403a03900c00d4001c8071960301c440c41c0d000034180c0546490103002084c0810324001c4800c2c80511945014450701e984c50b071170329020700030390703480614035079181640b5005552200c184040200c81018403014404204c0c1c5c0c540c9000b241e80001c207084001e8980c042107003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 364940557 1250 364939307 364939331
    0x2071203050604060602010911010c0c12080a0f030507120b030c04050f010302010212192006070f0e0d0b0103170717040509181b0102010e121312081204020d0204 71
    0x2001d180900000e442c2000940e44540d0140d00300d503803000001d8802060700e4202c1400c0d6105040080000d88205c100840c0c1d1969a1520138440300340300b8044400c00c0010600344017442d4402881220b00080d45010301c038904000c000070b0080420107041c12056901c56111180603102080706041d034039000b820030081840c21142c60340c204002808200c4c0140500c0036043c021000c80c4050350325070102d05410905101500b40251510800001e001220055074621302c01070460901c03181d4881c04490311001088100b81c0307c0241910046181144680b20392300c0c03c180803c1c012400e0703a05407548550741c020301d018028141c48040c0903615004020405480c0110702c0c826402c009041210303819100c010031074441544c40d00c2c146084001d482c0443e8880714151034a0078045403280760340d1070706000005240e10074220007820103132a0300c0c440681c1c5600050000710000302420200083c11140020301041149564420f580d00c180381a6540c16400400400e0640d620b02ca10851040e40c001c100300480181c9407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 364941807 1250 364940557 364940561
    0x3130606181406030109241b021507181e0807060207060305310f0c060c150c02121b06040b0a0b0f1f0507050106060804020a1401080408090402071203 66
    0x801002d1401290360007103400303400e05004801740300d80d10008078240c82c54401c804106a10101c1000b829983e101c1c3c1042000e211807041c2c0403401d0850380d01601c09810154401c0003a81c44c05130030700003041000032503e91a140c0b1454003c0035504c601c4500d0b4541a1030004100320b82219801002c07140c06145000107059800080340c5080f1981c5807424403003942c0384844900480740d9481450410744a840c958a50400710341ca01d1203400707102d11807007000c030b0440b600c4059407a40704e43c01190100d28580c2100042c01500d00d8500c54440103000140f0265080c4000292104244200140e021101040c4104816962a010103c0140000441e00c0707078601410000c030045015200b07000c0c568a03003400102d5506110541d01d10303481c0c1c003400ba404000081844810b46900c04901741c01003080a00000000420a019040091081c2c0d07031844224101401001308403282a4413850f0807402940c0d55000303d91b00314481d140d2090b004180562203000314804a07019100d03064004114908007840011210782603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 364943057 1250 364941807 364941821
    0xb030d08010e0106080907061b060504060c1715040522061d0312010e1b04030b06030609070324020f0c01060312030908030a0f02040506030a0c0e0a0b0313060618 71
    0x500420b0b002a682c80300291a036039003d88007140f15801645041c069540542c0400c0c2e045101054182030030b1034152100d0040b10420b4408440c440d859071100c00c03165500035082d12a80440714a000d5803070400902e80c0d02c000d02c4400c8070760b00480d21180003654403c1281015001501d000840d201c2a20b40ea24114008010014050800200d042c8038110500000016118004030302000526a6401c1070021085074038000c122000342400551848448042c01c0c0282004510504560f507035400c08108041c1409001000300d001030340b082008102103581807a050400d8640312100440807008111045d0213441000c0c0c00e018401000584001402c0c2c05520034411a406048070034060011040101c040d80c2d5095006461840244003141c0c0000071684121854209814011b01d02640c2d2004201103410440d0002402c90340d0751000f01001383c008140070410303d01111a103603ca400c0111604441c0809481c400031180022880001c0000c1544071b4405040520311a0f04c9819007020010050928 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 364944307 1250 364943057 364943069
    0x503130816030201080a15090e030c070504020c0d03110d05040f11060c03040501180905130b01080703020a091d070807030c080d020705100215010308180a140d02040b030d0801 77
    0xe0642030140d211070300c0c03640700550307505a4039064140c454000c100058900759050b810b07003030714000000840e00e00e1031085403440c5071103401030741d29041880011b074141555541701302d0113180108080340310701601042c0300940320362508002035940c5c801c1402c0341c01c0d401022807a2a00e03a260009100c24009040c040d4441075118000045104084100384001405410868400d95200f03000c00e02a541c0254002c42d00240303c0c0c1a0f44d50059030b1802c041081d50015162803011800d900400d209001c00003c5060140c03000784010510303503203103034040351407020170380702d1002da00c0d50b10400c50010324034440c4010400f0003440115280c0c6502da2001139154000c0e8030089070f00e9080c00d40005102e641c0031a210514000036006089400e1514082c007800307003a004184000c42c0513a07111241c1c069030b8403a065018501860420b520b4072060685803080501c6104c0580c4515000c0f0020059000103900880b62a030040c0d03404203c078002440814068109625202d6060080d81d801c91400d03540f0642c81812100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 364945557 1250 364944307 364944313
    0x31f0902060430020a050d05030f120f010b07050304180e0d110c0a08060403110a14070f090203060a030201030b0301020d051608010509040c0b07080c010903030c0201150501080f0402010c05031308 86
    0x10441200d1490f03507040c11000750480c4404104001604d0011501c2150314000c00a90b0324250324942e44c5000c40e803040000b446401c0b22441170205040c0200080750151040c5640380d0706e00780715900c6496407070040340701e403140e418248000b801408066401101c440203d2200311651401105070140c421007070f1400c074103101d10070100544560703d080c0c00d24904660100003d0700003034840307441c1164048043c20070101c10b0b00c90150000c2c001890704814000200c0c0920240c002c6506051595101420755805400c90500500a01c116552140070141c222a03090034001074545400001ca4003900410030f044550b00c0c91300701006144104103142040b070389955a507081080ea05c6030208120f0100590b001b40c281d000110003400a0085180203110690007103c1c2c460500144205141c2034421003841140000e8491348048030a40d024082c02c2c80800011410302c400741c0c00c060000700719030b40080482064204a13404101564001c030f42c0041d031960001d042d00c4c3d48009038141c4403181a100e211b030040500c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 364946807 1250 364945557 364945619
    0x3070f090f0e1819060c1704020d0317090606010801062a030905032a0402070b010308160b010b070c0e0603100f11040b040f0821030403031d10060b09031f09020604 72
    0x39204c0c1520741c002007c3c08950845945850b004d1149641001a0460a2020003030301c2161062810b440c071485075180800501c0b1f00e10f031100004140c20010b9001c1c4081c420344e044c00c814091801c00901c81c08807040300d039084100c0e403541801c0320342440355881a40c05000354003041c0007030281e4a4444d0052858106a054a00b03030040078042203220b1408041c281180000050000a000100070700100140b1900200058000d44404481b00e03c00c0c0e11203c8100c2c1d0010b028410003099020441c0202070744d103201d0702c0e60303d4904d02103034a8118851034203026541e1411858419540342d84002801442600c0391511161100150181075003d401140d02d03140f18680002020500040c884103281203c0c3c245090401100745414211b80020704210305140d203030394001cad40c0000b8400040218480c210300400d41414456050301c00c55085400c212040c2c00100400c1340161000111090900d007070403c038a1801d20b81d84002002001c42d10070007580807400240001c0d820440c01c0c0e1400507900010b10096500e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 364948057 1250 364946807 364946831
    0x240c12090b0c03041403150123030d080105010206060d02010e060702060c010e010b130903050f0f0717032e061110110703030b0f011d06040305010504060203070f090f0e181906 77
    0x5045a11007480c0300031f40e42e1005010a180e00c03400124103c0c4991034013840c6081c000002070918a0001d04000001c400c0d07001000150381c1040080c0d00040c0613aa030300707003420143d00020841c9910342560350142030300103a283e0440d183d102c22103c1000c1e1100c020001040000c0c2858040c0002c0700c07801d4401d503048044010040c00130300c210310346198180c4409140079220000c040c19500074495014902100f4419900420044012104e5082e0750708680d640d42c0c40c0141014454003c2c042944201550480d0a58415540303c4041c1081d958075042c00c01c2700030380441e0b107145003100c10240c683c6030b28100001c0c004a84080b00250000910944041c0940044070090201c2800700300c20b03050001d49100801d14078161080c400129244029100c01e103070a07240c2d10351a0a40e003003a2011203901d1380c0007080004d06d0390701c4440c1c802000c01d98074200c2031207458055601c0100005004185000d01e0207000300314203040717400c0d40d456201d941c4001d07120480c0d401c03071443d40103111103001652001c1c2021441961 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 364949307 1250 364948057 364948063
    0x10516090e0a09080f03092508071707031209050901060305130212010f02040308040e0603071d13020a180b01020303130b040503040b040f240c12090b0c03041403 71
    0x16035aaa011038800ca603264601500034201c5000e080e2440301017001900210308000009510409110f8000c1c40d4034030a184880c1c4e10b11540b09003a40092038182002d02a5030008940c5d5001c4aa12501c3c0603602d07140c6e1604242404011351004000340192200340c411030b900201e4810441d8411035044941d60b82c3d881c03055007510011110312101c0c0342d81c00200710041c83c0001c1140781503a02c04000281c0c014000e03081d041240d0164100750381154001c28100703c2e48012616041d0b05c08010340141124500d80912031105212000b002d44401210074006a14070141c0c0b841c04211640060440c5101903032000604040309400c0840c00c04682069251030030795000200301da020740e05c8044501400c8034980c5941f01900c4000d0401c0752140030030000003501a090501900c00b0307210700401119100d15202c00c64500c42040000c440400c09206203002500380c00c80081010305402c41d211001440c15040c045503001c400d0b0700010600b160100780c0046002001010340140c4070a030020002c5030341e4503410542e03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 364950557 1250 364949307 364949309
    0xd0216150c140c01090b0a0e01110918040609150509010c080903190e06041e0602070605030613020702090403030509010b090610140c0d0807030b06070b06010e01110a0501051609 78
    0x40481c6240556440620100c802803101c801c00c1c0000107541c94413507440c0041450207556247c4056112919410300180a10602c01c0713003803500080c1441c00d803118020400c40c040d080710002d05100b40d0700010701400080d0304036242c0e250b80310343c1c8030501e0754101c098031004203c2922900d12641c84d1400b12030180b4040c00c600c60203001280d0003123081c03032142c0a041855800c880b0f1104e041004101c42041b40707807a1031001d44054038404204842001030140c000c080c1002d20b910010865002030801c00c0141d03001022a50000819500c03119249502589103000c1c1c403071400000d41005000c2d0400c024140e16070312180c0110f600300000d110101c7c8000400c4041c40080e500994020b01c62503001404c0c0c0c1c020380c1d001c2c220b041d44440031410082c0c500302560030481e404541d4000304550754104803005505120303440e00c0107400c0b96a6410300c8800c0c1c80d1403540a034000e00c11030602c0941a0b50b24102ea0081c2c01201045056404131003a0000310f1620078040e003400d032440d00062880c5513801280e01d000d81304c020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 364951807 1250 364950557 364950581
    0x30c17100213120c06030507021902040b040902061c050a06061407020102011e1a0109060e090402031905010911090702030307140721020f2a04020d021615 68
    0x4850000e0040c4004029840216007102200214500040603a0307105000103550380902c0b034510145160940240c01e50303d0051083c411034002906d4030a2004200038171100c500d4068800081c80c0c116100460024a00c440b0040e501032004034002ca4813005005201840c00c20407501403145464843c0030100344c49050084902103400c082e04040400c0003540500f4445005100204980704c100c05400d440024000c00e8400d10354a6846404904040c5e10400c1e0f4810028603103500503601d420402421045034101d180e20034803100d004181995410442c0311400d10b90750201d050001407070b10b080c0d0300815042d58212010b6030100c1d0b815606250003443c1510070b40c2144c010310304c1c43e9540c5c04200c1d0410741d0354880441030030040c400e0b14045200c084480000a511204203001080442000703442e0007144400c0412980c042d40c1c00c1944001c54401110546e140c100ca0b8a11703002d02c08000402a003d1203180c841c02900c00700b072540f21108080040d20119008108a00c0c00f00d8828000c4820b40d400c2c0d281c91 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 364953057 1250 364951807 364951813
    0x309050f0d200405040821010302060a03021b07060507050708010504020a030b1b07140f0601032006040504111c06050306010b03040203030c07140f060c0d050c0319030204030c17 78
    0x20800300c0e9501c40003401c0b000e429071403600c8001d92007001904860054030f050300c0c08070b07000c1120045004e5050007a111301e61507040710740a40d85103900007003440c4525102601056008030344424090102c21a9000a043c0070003a02d60050326440c00400940240300c05680d644030380000001d41407030602c5444e016a070003030070424145055840e8a10700c0040a04002c0e20801c01e0101c05001c00100f0000e4248240700c1d981000001c2c500001c01d6251880c170010450340d54000100400c0080d100c508062540c0d100905003480c0c40c030585000495600603544040c1d002401c082401d330740c402c06c10700200509040d0010702c010100e15901c0d810100d40c214090b1680550003000140100c03103228001c1c55000388000c0490b86006140100d1074140000d56018050020144030001460710b89441200144081540c6c690304100004810740e50303802284940c0c50503c000080c2e200c80d084c000703000300c1704108402c01d03190300d4213210124010000e611a100640350081300314004144141e40c0c03c65850081514001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 364954307 1250 364953057 364953079
    0x3c0605030604111f18060201141f03020603090106080601060c0c06180915090c0216051e120607140703020606040b01200f0c06131205070306180309050f 67
    0xd0304800c0b9103601400c5a000d01c000d51100004c000104100840004c00ea68a0b6034004110096194200054101d101136905106031607003411070311050700e640280701020b03298000b2181c000c00c81460025400c082c3d04200c0010400c40c0800c0e054000d40101c0d03101c1c000300d952aa999100c03c940c0303201e0009004100721800b03d801c21480748296030500c104103104180c3d1010942e20b1904400f1507603543d0301005660100001081390501074400d81642d0444c600140107541d0030702c00072141800c0ca5000d11f903c00c03c2c0440820803015191400c2d984401b20240002426182a008c403542d102000c48105d0005101902c21007501501d81c411b540c0c1d00c2d07505400a00e0240c68840810016261003d2064100400728043c20340c2c0b0042e0319203a808000c1c00001034040420100c0d001800c0c41c5003486124041c4008204032074080c50070f40e21000495410b408207220341807040ca1b02908100c0d41d540050061420404a402c1c81d000404212210303910075100c8046843e603503000d01101503441480c1d69804001195 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 364955557 1250 364954307 364954313
    0x3070503070912210201110f0318010c05221a16020406060f02060a02120c1c022107021612022409011b02030705133c0605030604 57
    0x2031900840c40303003003111080b51604400c0d011514000030075184405090802040398202c01c1c0c03c09842e40c2c081c4000d1010f1094001e0122084c811281c2c0c07503040c80400800500c0c0c2c00d00c400c4001084080000007481b80b43e403021070040c51508122002c07805845c401c07e1103155900b5061035502129001c1c0c4d002c841c40314140345000e20540003119031841d54049100c0ca440140d60307911542c005410700d6104d61102400c01503000345060b8009082c0500d152041101c20072440b110044203134081002000385603100c19141e801d243d50b044803990303005d4450010420400c026501006e007019104103005509440c3d031146c200300e80c1c90b001c50480455075508008180000740c0581040b40b807040c0003521880c3c0a048280d5840861304100762503120712080861924280e607403104c9500000d0603800d451119101c0e190300025182c411a115591090000390300e900c0320000789810007a1144440100e202250180000d2250030001281221402c0385551468080301140e6110b04025500050028030305076465075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 364956807 1250 364955557 364955567
    0x26061509090c03070324090b03120d0b1c1a060103090f030f02030705060a0509010c0207060228020301050405010509010509010612020f0102120d061503141b04080a030810120302030307 81
    0x7802c20420546c0300c0c0110600d07820030b030102040d48081e0040c10f00b001854a119001150348040486210382c0060800c0ea0071102648140c0c0c1840c0750800d00012050381c0000003442d0a00e000003030150301040c100802040c05880d603141e1008071224414502c103681c0b010011003c0301c4001400400c1e1881e00c84410002c80d1040301c0744604201c41e030045910302011a100d052400c1401c0360340d80c1c411a168130800c40001c4081c010208040315030300080444c6400d100010307498642c0c004941c4500104400581032130317545e40030501640ca402400802c160f0405060403400703094101c0e0042400d40c240804911540c0741441580c0c100d400c00c503481c0103002a55400c00c0603c94030300038428114170510785414001ea051500810707805464060010781585050031154072020501800320a0618010f95000c0d42964000681d07442528a00e070421014043c4416101601071600b080000b4840c0d000c1d41d804054100c0324181c005c0400307c1c0300903507043d500d403200e5117160542c010040041e001400410303c040c0c055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 364958057 1250 364956807 364956811
    0x30813020607061a13051b0705030a0e03070902070302010b0a05090115080a090605010806090d03020301030809010507020a0803040906061805030304061d040507120c0311030c07020126061509090c03 87
    0x7038100d0044c01000c06001948500c0c0c0540080c54442e41c450611030459107a0f04144941042c8000d01da041520f903454050701c81c0a10000071087c0304402a034400300c0e54061000c540a0081d0040131034441030b203030400a0081940d0740980d40100030400010440c1e1824042c028120340c1d00d0400940710700c04000049442d400c1c050285814039841d025500001202c6010300340c0030707104603002023100b86400c0c40d5542c980560b60300c0e8901850720400050000c105250101e54124500382882030351075000780302040d0802510341c01195680008038010962420b43e0b00301c08122241e5035503a006800d500350703034600282403074070409038594003c01040000300e01607420504481c40a66054100e25000c10100701074650883d42400000e49903d50320088684522408009021500c1e04005050040030300942d5440007401c0e03080040c0d001b09240d001c5a02c1120091980042610740d2503c3e01d00504441a10160569002d4070561603405c103210701000c00c00c01d50740c074810700600a10b440d85524800301825400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 364959307 1250 364958057 364958081
    0x3010b192f16080d090608100501080601050d050c0301080d1b02011404080a150c020d02060f09031b030304140d0903200d140d02010614092701020703081302060706 72
    0x940a01020349402c50640b2100400c118000340102107110711004107841d0241c1c2040043c00302c85401e000180458402c501d080d642e080c01c2018141d1a2100181c9441c040c1114016449050008200301c1000800c040c5048030350000c210360745880901801e5990f0b422412009010381c41844400001d0344c0710710703100030320105480d02581c60592036105448c1041c509100942e01a40c598800700f024254a1041102805840c4050000e95410b208000d448100c09000d02c4208003011010602c0709001748112244505945000c07000e42c1002010240c8a401c02c9906803002c05d503c49400c02a500e0214008106c1005541d5000075141183d5414865a5040e0808a140e40460441600546404540054090040007211511038011030a14031782920031105034116410181e0412420081c81043e580000b0200c410802d41d0f902c407135240c1e503120021042c0b810140d4000c1700c00c8100b00419030080c11250f0083d40c4001007aa0740190200c1810349000340250030400400801c5c0200d8a81c1d4004959218 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 364960557 1250 364959307 364959313
    0x60307032105090607050610050a03020906010305150303040e0103300507110406090207060b0a05100c050102091008040302010f02090a05040f0e0607030b04150305060c13050603010b192f 82
    0xf03500001306080303400816007261141d02031010710443c0e03401040c5070001000c04846210040c1c1c1581d000c95040c1c50085c00b0207040c180c4441c0407035411004c0500818203c40003408994070380d9581d00440c46898001c0c8826100c044440350802e680d2121099414882c0c1d078072841007044101c440400b11410741c0454005d45140e45800d5003c01555103501894004045003100542c684009060107400c40304944800c900c12a01280c00f0042e580381c0c101e042c5008100b501300594128418100980039225204030036a110200882040600b608005854000c80c0650f008010320403c0410a41c03c81c0b00b144200c5a0200900c0030801031450075800011000e8409040412a0060071010610b0301406440443c00b00f138039205481800c0c2054491300d00351100e000303030001c80945181c0f255034070780074003618600c4984000600c1181c00300300454418010400944429965039440c030080f040ca401814102c055071044403251f0704d04500c688ac15030b401d80101d54003503000c0e03205004184000d0680d041c09002c580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 364961807 1250 364960557 364960567
    0x32202030709060905090109020121020f041508070201020c1c051309020c190228080d0c110915060307030e031b01111822020307020f06060307032105 66
    0x1880610a0301d000306140c100101d082401c0c05112800c2d500002e000341c11981c500468000541e910544031422000d00030551540ea11502e1038080c00391040085011603a00c0018001038004004001611141400d0340c88040c41c1e101c8010880c00d170300c03070891503a02d2a40080541403039643c030642281c42c0c5000380e003421480c102031034140c014007000c035a000303201c12036010821111048061109540c0c0f034038840c11102c808151030380040d120b000300020201005103042c0d0001c2841078503500101c041d004107021071329413045004e4020010380200384122642000110030300c00d642051021680901001c408038000c00c000d81003488201c0e040108a4002c041c0c442c0c041d454003040074002070005142c240c40044142000301120390a40d5942502200308400812101e820301c1c018035001c11901c82d04440d449502d02c8841c1d1000460290b500702d2040c0144000240400d203500040d190312410b001900366203056840c20304150700ea00a1b8400900709020486020030361642080a207004e141c0d03981001e0703080c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 364963057 1250 364961807 364961809
    0x405060d0902030a0f0201120606051204061401120314030601050a030c050d09111504050a03150b181605180d2d03030605030106120210030605060d1a030f03032202 72
    0x80e02e213005a4002411080400541d6444210000f100314146402e0014501d8140010494890350500010000217140170404000750703a0080501c400301a510a00d240d40c480c0001c2441d02c40c0f0186c01c601083c07001000c4881c611546054030b11491058603500d040c184071000641c05018110800c0040000c20002c0c0784100ca120720504100c1030089030140c0503101440203001103852070649040d01d445050104014980c3c62509803070940f0b130720401441125019000329005041c0c068138065000804030080c0c0000300c41e000182c0d1040c5450600ca0220031030b20700003039506100d50652400c00d0b02c802814064907080107001c44240d00d101c1d802440b200d00300c01112a08504110380b000c4003c211043d80c03181456854060400540000c6008111640c5400d1200008080d0660000d004910640046044034000d80c80b4400800340644203a6032104c044982030005d01310101380190403480107440d0b03102810b00044034105074210f100158076540703d03c0140d0340003e0a80c03101030f901030030280b951001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 364964307 1250 364963057 364963063
    0x11809060b070611042d08030d020702010318050303060d140f0a020907110a03031d011a040606021504060213090e0a231c111906060b0304080405060d090203 69
    0x4151982000c0d480300b80628294041d50804440031403c00340601c002c0c41200744c402d042000c03030200c10900c2c10030074800c00071100655045a00c5260140008101e900c031902d40c035001401c0392031007642d04004000504140e808180a40ca101409c01d40c001d0001407114182101c18a1401c2e000780b1a10f51b4607810b00860714a860510008419250007915048046040c0050038913004205070a10503610140f038034605644a401041c01340816840745003003100400280d03a418002143c0d00024091046401c41d018003428a8010103405945420000a026407000c01d0a094070f1448030712110700c54860340c075400d000e50030110441d003445008000018a44000d8410009030340c6028000c0c1225600506108003140c1c02e601040d50300c3d45000503a00c500100114020300c4102c00a03002c1d86680b01800c0c0111400c8101b042d21010341d10400c20090100980e2103580e0100354403035003081c00015158210450a804151401000e4940502c01400f07117281c0000500342e90100240b0010b8000865000a45 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 364965557 1250 364964307 364964309
    0x62d0a09060f0303230307030504030903061407081e04060f020906070303050603011b020a0201080901390e03150406290a05092403030405060f130f030f0201180906 72
    0x3140501c05030800030590008140d00701540c1e14000c2900a54170002e1000d118400102014105603843c0c002034101400345070440055600288100039144c404140f1400080d006e076070030350128070002d00250038194000c914070210183c80c8440354803500c1c0c5983e00f0014003000b105a9480c50740902004000c0d0320750703a010b2711169020f6a0042442d040c14403e050844101c1503100d1103903070120b03200c404d2660300043c0d04c07080c8a03420320b0000c1d01c543e00c40119a00500d88800311010064854405140d54414148154201c1d0106a03450242e0b06c02c4650640344010503504031605500000b40c0800a64102918180d01500684001c60003408284480310303030f044080342c1045d00421160b40100c1c6030510030180009040f060700c01d0b85041c1072802c4403060710551010724060062207072402000e01c0d20305200365401400e025200c0c1c0d8451a21200008903a04164090581c0e8070603020b00040c0030000390500c00447c4d800000548100925400440760382803400362003a0f0115800d01d001031038110a01c9088 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 364966807 1250 364965557 364965569
    0x17031207090303030b0a050616140f0a0c05090702190816030c0605060420090a03050115051c0201050d0f1e020406030b091b09010c0503040f0e062d0a0906 68
    0xd000c1402c520b0050116041040854051501b40d50300b40850f40310041120088241c00d210b41060507030502e020104001a0300980c000c1e4040d4888150410070001603204c21640710303030600c41d203d0351140305000c640c503400c6030b2020040e40480203840203d1508407141401078003a83c0041d26100000c220350841c0c0035098421400501c402c0b040d201400402d1059541181d0201c8051102848038500b00340402c3d003030314041e034403100001a108400c1d551407980000540d0f001c0024000d00b442c035000240f2140c5076101e918019000500003100716084503000c401001c3d8145c4400d030910500d968020001c200d80d045e0188226a90700942c050754029560f407140c540020350300580c2d1203040074002019604200c40c1c09004600034001c0c8041108161041c80e000014000843c0c1c580c00443c0049800f07040710070018045000c00940452410303107912036002994024103908030542c44450a1150511304049080006040000034440c0e554405046031114080102081039131901c59007004200c0304550300c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 364968057 1250 364966807 364966817
    0x81201080c090a05091c09050405040b06030c030d0c0b041a04060c140a1e0302070b010b040602060601170a3210060c0b0129040603050403020609010501080717031207 73
    0x41c042460700082e81c0e82d001c515002c060040d428901d050958460a045400b01c16814402e058031505100c1c800400c024000144144020b0030705052401c0700070070655240c0e010f4013600d002c050f074604000500c19400d0207030b55254021440315031604d0001d00f00140089584075a5100107031440110010788030302036801040c1c00180120a80780c05072410f0230200030400042800c2c45092820340d0001807003521031001d00000d0341035008140d4210000e1260a0f4005c281403d007000200f01c014020001e88152107640d000c031541600d40134010342d1510495000f44060105035800603070b09100a4211855a40d080010b20462490b0180146d10003440781c0d40715400551044d0402c00c0130800e045010004101c2d0341010100074000783c44461004105009209000051050400b01460303452005400400c584103095143d40e04c440008000d818242c4041c0c0042c49410301050350120180704040c12541a80000d103040e914100700140030f0404000346d43c0d441d001c01d10a400b529403400a031a4821034496440b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 364969307 1250 364968057 364968073
    0x5060703051e010b120609010f050103021c0603030203041701020f2502040f09030311030403020604240c32090f0d0813170105010f060c0501020d140a0f09050a0305030408120108 78
    0x4445e42c034400080206100381c84030b200400c62140b140c010a41030764020b290140c1c3d140301c010000030310381c0b0304900055001c610f045000400d2543c04000b81003501c8100b90591000742c002d090722801d07401000d850350706260b010050f0120015901d040403d840100301c8842d01992000d400040455180d42800e140c801d450b040c0035010907506214000d10b010b00d1141180c2181001d450003991000002d2004004a6007000200402c0303400b00454021103440120911a200d11080010642440c1d100e09510304e0000100c4130400c24100450344200042c002803083c104040c2c1c6040142182001a15641104d030410310000407800c110300400d20b208481c070000c40028074003000140c020f4440000c03a541640352200510108035070965003400c8800c41d18000e240c050884c00d10381d00900c030324100c000c1c58520b40711002e050740100c24030f0140f1038a4040300c10000e011080340b44d142640c48440b00281190414240c400010307004102464000340501c41e014200000c01402440e00e080c00c1c0c010b0b122507801118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 364970557 1250 364969307 364969327
    0xc0f04090e0a06151503090f0b04050f030f0712111c05040302041802010e01141909120506010e0601050c0606150c030a0509210d0e040227030f060405060703051e010b 73
    0x340e481c4001c03171307a8941009550040c0d111013012507000500141964400c0e0085818802d040007440280d0000300152540c9050101641c2c12aa0010f40c045501d0032000840079402c50188103074058001060300545904490120090107040211a5103014400e040c480803004d6200c0303101c1c0096107400c0b0071700101d003000b03a400050015000780d80c1040c108030801d20701c81c1100030840141d03004150f200c4801803240781001401d880b10303001504078501a030710b8070400c00140140000c029040311381c001040320030b42c0c41c1d410044540344100c0603c030105521900215101703042c01e18560300d8201411751081c1c01c0c40c504594035800d6034812100400000c602094008040c0780c850a4040c2010360055442d10a40c1800851621407840800801c144100c10400c64065215a0110341100890401000800d032000034800045c00c1a2140c0c2070292040b4038502116030000030b4000d02039034110000701125654907400710040c0000030008021f000c500b0318201c502c0c102103010700e4044c200500d01c10707032500200c038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 364971807 1250 364970557 364970579
    0x110a030b0a0b03060d0b0a090b09030a1701061d030120030403081e0c16050f0f0f030a2304120b01030311010506010509040e151501080c0f04090e0a0615 67
    0x30b00162094102001844040d90f01c0c00d2000d85030a90210303115440703540fa40d514400504135140e019201100c84010001605404001400461a55210030388840c940c05128440c00c1024000d00010400701001c04450020000e549080c1010050010400c420030050213076101c841031a0111041401000780010941c0002c20998080e0704a003688d010004078214803100c540d00a41914217801000a200d0740014408000034000c0e5045406c440110040b0901956103181e0140c0700321075070140b0b41380d1460050b07010040b40d14000e00d42d0f99030420000030090000701c070110800c0b07040788003008100014004034000d440c104024021405d00205602d181009400f2440c07101c0c10380c1d016403401d010445160b81003c02d41e14441b40c16100010300203980b08070585001401081000c12000030020054910745143c40c02d55a004280d881a0340b42d141d0219000b4903000349000c5a5416400384014001e14019074485a0a140d4403421100200125101d040448800384100b4540c2800144103015800c800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 364973057 1250 364971807 364971809
    0x118090606120503190509010210020c011805100b0415090e0709150f090c0206041101110703060506040c0206010e0105010e06070b070309050d090803120c040e0106020a0c050f010c0312110a030b0a 86
    0x80c06c0852030583d400340000d446203403081014118690203c0c490f8150744095120309409030300c0f03540511000a003400c08698079080c4010450600b803c141c000f80b043d0919006000c0300c02c0c1c0401c0ca26000c641084040c0000c1c9c45481044140c42c8284280082c82d102d26001d040082c40e00c00c41024003160801913550a000000d80020007602c1c14401030003141c07580054025840b5421011069940c40202c0c0102c8003002240364084007489250804428070a0a0380407a0080c04100c8041103080110301c010703a00c6280900ca01e06024880342c1c0100181d5001e441c8881210f50700400c0030380b51940c260b45464585c0310580c0d1400000c1d9440d0850380401c0001c00c4150784c4905a8100900300750710b000b9050340d49200380b0803e4100c0d40c40c44000304203072072888030070b613000b400c0080001070f2a5a11000003d65840990206075010030180c08000b5a600701030040f0486090b040e5070b074414010503610107452504800c041004819601c0b140002200310b0b0b08094081c0386c01ea40e5000c1803244011080004140803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 364974307 1250 364973057 364973107
    0xb0406050a08030a0f031b120b0405090a030c080909130308010503030408121605011e06051f11070f06201b011107082409060118090606120503 63
    0x25684042c810b140b000001c1c2d03641c80c0704515042a103000c2c410400c83c0900800e0143d213041091040d90000c084e60420032200d0820b0b0611030401254491408110030340e007090f0307078145a80e00248104c0b00445e01c588085a070321402181c401c1d16000d0080c0c003144009104444040b92106241d216004040e8881d49450041c6000c41c0294182418020460b03281c03069442480507500b0005140758076541d0310852410456080002000034082c0c10f021120f03031414046400300310900e8010089442d00d08030f1440d146c94200c403024104c41d4280c200007514550b0710065041207620034010006160612803c03140040e0070980da402e4008025040d8015402e591406840b01075041071813481100500c1450340c803950351003442c011304d410001c000c0c40c5003042c8190f00000d116000f810f4074102120241c980d549140b0b01c40c0c0d5030401040e640d1254054440000f80100c04e400503803100c0c1214160b25a40160410a003c0d190001d0170310799441301034505100d094400c40f4240c1020800d0b208290f04c00f07030050702a04c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 364975557 1250 364974307 364974319
    0x60d051c17090a081921050906090c2b0b0408041e08060c09010e03070305010c1202070b2707091d03130b090f0a0305010e010b03060f01062006040c0920030402040c020c03100b040605 80
    0x10700c00c2d0000d501550203300c00c10f180002c0f54082c058040d000200b11000d1038000c42c00d0a01c50900d4200594540d016018003407801c21102e403886104440c05406800301c030241c001401d04e03604c40c0804948142c0c0080c2815042110385071402403075550174490600118810300000650008891000e401d02590b6803140c0e111510510014001c035407452740c200e9100a02c0f0b40c5407080c0781415120b442031220311455144042c03080800101d088140d65128000c1c40002d0744145800800351001e440d030328440c842d0001413501c071a1008010030b07814100a0001810014203421b2907213100d0011410050082d44142c0309a912020011190308007845040c180c1403040d0080d01d12450200f41e14100c0c80c07018401d072003c018039501461a009400008418002c036003c041d102c00303040c50b041c030f0341d0131400380d02400540070326040e802d42182c4040048010b141403c00520307400e6958980810004185010070b95040d0f000317014070487e19a60600442d05d0a450700c042c00103040851409000c01c882d055000345000d08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 364976807 1250 364975557 364975573
    0x30607050f1818010311033d0b040f060504060803070317040501200702030d08011203030b0a05040c0504090506060f03060d051c17090a08192105090609 67
    0x41c20140c1110b04050101d88180a040c40c100045619140500300390095901d0120001c41009460041aa0b80c40c008400b110148040b544510180038034100e88807502c0400c01c0c605580a081007020710501620b6003000060307560050700460241c6189412640e074066848001703005600e010301c10240540300003002035040402654024010306500d1001c503010864040018041180075000816105c3e2542c4a46d5002c1d0030310024903036542c201c484128072074060b0403440300f003d601c184030f418103c03550a903080d1a9402c5a480070b9000302040072915400c51342e0a0000304680e1611301030b19003204005d59641c0c0d030b00ca241942d100c00300c2d4009040719202d948104180c6008544140683c0c2d0031000448601d500da6410745015803800d44200105101a80b000d002c80904582000f11064245031400e01e000c09076403002e030190303202c80301303910020b24000d020701c40001981c8196401c0341400005080a500100482210010088840310b0086295032a10100880128244101c0ea00895080c00078a884 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 364978057 1250 364976807 364976827
    0x90c090f080c1c0f170405041401060816020c0d060f020a11070b0306010c0611070b0403020f0d0e030d030c180305100b06120f0c041205100606051207080a1b090503060705 75
    0x142e1105080504585004429417440305044002c5030002c200041042010b11f01149231916441003d210391004603020100040c1c6200c071244103403e40e164568040e1604202c803108001d000842d10b6000ea0761684d40d0f00702032401282620040043c41307910b45641d0500c544040840f1b20740b901e15006001075007002c0c820b00032180d030482c1e656803416a2000c004070300740c1e008851080304c0d4050401301401c00c404031003d0005060300850164120241c01c41900c81c265907015055500c10200c8a070160594090a05603480d107201e40e1080d0f0301c1150074074141045054509442c1608205500156074035080640c2c40c41d820051842203039415201079a0141c00e00304010606c929540004150703061001142c4009811b0b1489001150f000d840e451030079007600385142c00c00c555a810203041e00d035415880c04101144540c014410b503800032800100401440c1d07640d1404541030840038140e24036194130f0700f940b2015641c48000c1c2c003640d022030b80d844a154611300b500b014a4180c01520f0f4109011003000703a02d0364 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 364979307 1250 364978057 364978073
    0x90e0f030a120b040905061302011805011e0e12060906101401032a05090a0906210f02100513140303121b030112170310090c090f080c1c 60
    0x10b000c590030b00018001508002150142c611100010024015681044800121361810740846070003a81c50048950b042e2090344450440d80c010140483c4c40b910803045c400c401800c0d511408e12091800c0d101800c00800440c80550040c04031901d1038200004000c20b80304101f1109910240e030b888be40294505d89a0700007682c40c0c2e092003030b0b4105601c40e00a4081401c4c1491100c28060010000b81e19903000c0076001030280d0440c0036054840c5a000f90f000030034091074022102643d107105003e03c03801d01105818440c00c02250001c03105c004d1901200005a40c3e4480310003d80d0505494940d5a21254803113109000310642080c505801c84204a0406072400400d4400c03440d4012030480450b00c071810003c1c1801c2c1d40300782242100300f0000c000700c0d549802c0482e4041c018410060f442e209030302609003010600045545245111400301d042144240c4c68120b60b4030620302e42003000c0d00d19182c1c0400f0b08080d020b500320785a203510181c001c00c114100840030304418a002034407010300c08105d5031000d40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 364980557 1250 364979307 364979327
    0xe01020901141e040f06020f0a020a0e0a151503050709080709110f030103030302070c0f21150903181a0f0a210516030203040c171204090e0f030a 64
    0x808640070586401c0e0000041942c402d41c0182d010381034485179103500c00401401180103500041c05500d140306c1e4014400903024084560050404031103030b0074001e0204c82428020405880d840c0c4a04504d000e001c8e20003400c4020700449501c190414525040180c2a40d03030241c820810030208000420180700d0101d1984160361189201158035800820b0112043c080e000800340c4140707000000008042d050360003804018400c0c0c1c0c50300350542c3e031071084110703900c0c2510610803c80e00c141b440c0054400568005400b052082c2449010b03145109210011680e011a041300811484030703040760f000b038901134202d009048a0110003290f9a209a03040030b0340c0619038a0520540002c52411543e80c000d0045d40c544042c4005001803d102100715640a4003003a140003d8070144c4401d40341c4900d01c2070003100c5c030039500100e14040051415140d11000c5406aa802c034990280703034000b101c0880ca1100500c0101044000805c44580c09400c460803e59800d20106140d40108200326103541c2002c8a64 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 364981807 1250 364980557 364980587
    0xa0618050616020c09010e06150a0f0f111b0f12030702041d0d030c030506010503090c0904031209060209030c040b0307120507030204020d020d0533060408030a020f010e01020901 78
    0x141c241d00d40322059141400c00204c244c0c0c0520100b00108484a00b202080d00c0b8010890f44400e041d0b40e0b40110780d01d1032003041300d208001900c6181041001f802503055404501c2f19141004031400011402030800c4021030401c0c030241000c01c210404c0745000d040c082860401110b00c4001040c0c2080304c60356031300c203813400240940d84507024052244500005101141c1034401982c01200940500500500c0a5011403000c82d181001141309540724105403441404034134000c0c05044900410442a200e00400031410440000c48805003103043e4010300c13180600c07407030026032a140020201410304698844541c0981d261600b05516a540020001d0403644c0c0039001071810314880c100f8909101d800e07000a5003182c00010448107104081e40203041ea404189000c00140c0c81f15400681081e41810548094844058210b141818440308690080d100101341c2d82c80c04d076480d55000e007150402c024803005a0028220442e04402c2801001d0341940180001c41c9813102c51000601001800b400003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 364983057 1250 364981807 364981831
    0x30a0e1e1201060b040602030c060703180b0a0608031305030708010c090e070311072001171603061509050901060801030503190c0515070905010903080d2a020a06180506 74
    0x80041c1c2081d0700c0700b0080c00354212a203a4417521050044d41c0c940c403644046003948140c07000500014400c1c032500e241c800c0c1c86569609116a00c3e00c94a01e10b64010380302e1200c09684d140c000480f080204000c03c8807130b91102c071340c0e0b49aa14050825081a510754072814050f41042050b4110700d511190000513a02c10701c010f10001d40b00e50404900401c036012000b094240002160000d2210300c2e5403016442815a100101c01002c0030700440358001c10302004807619842c4c2020481e00c940488410070b401300a460001107069481c0c0101100c4004020840040f03070701140144151700745250802c1c094941c5081c540065403540d91100c1da2403143c25261499400c80b5030b0070310012807055080065554000040300c4981013a0a2400c21404060b900400405e8586900003200d500803c0341404a80c1c01078909800d01c00200e0046028040700903000440c0c00c1c83c14150540513104c2c0750200010720060307008201070f0a05113062000c070742c5258441071210038a048003a00103280091100c7d400b6204800f4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 364984307 1250 364983057 364983079
    0x60109021e0307030b130207050604060c210606090e040c0927120207060f0210090f0c1502010f09120f03020f040e090c10080c0c10050702030a0e1e 65
    0x504070106051a40d801000c0d4030010034440785551582002da5142e100702c450b80001c02e0400b145504901c00c9450044c02908003900042c041005a80046965006d5040c044485648603c400480540b00c10180800503560481400600d80c011a1280a0080c52440c400076043c41c0e100d294101c0041e00c6200c45013911204211000440b0211581018040f02041d904915441ca0204880c01245e8207110040c07150360030000740070f44a11882c542d04081c0d500644a24040c009006014022080050b02d02c480302d40001e40c0090300320840e141c028201d91003604501c4800e1440242034409020350342c0140340c10141d208002c68262018420030190314200524403400050b8160301070300a02c100b0440c003610100c6c4c001006d0b0f080524691260302c0c00d100761501080c0c00c070200441e0584c0030311181c0015050000041802c2c18039001050003a4600702140e040328012030510081e02c5041300c40c0d00058101282c90a0403036000300b88a81601c07021102d42e4007440710010700034010308642e85424441e200f0030b45 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 364985557 1250 364984307 364984327
    0x1050f1309020304150e0102040b12040c08030a050304030f09050105030a021303060609060302040b1f0f020111030709030506100806160302120412120e120c1e0706090e060306010902 80
    0x22a21006041c1450155100d1509003070081c02d241c90310390141d00301070501001030b030000010700c00c032002d03103250b10640c0d400d01080e0560340b076a0f050010411070b803054000c4000724400780104050700100f12503940c3c0316a079107803501d4001e1903180d03103542d81000c0c4240c50f401442181e800c002640d81c40380e6515001030f101e400c0101300d250702e04015030014156510303156002c28100c00c0f0340c1121083e24020356080c84024105030602504280202c01c012648100e0703040080c0040c8a00000c0d04072032600e200110782100744030044205544159800b001140c0c85a0041080160601c491703588014103101c103d1289150010003512039030010f10761300c503071205103180c410344074042c0e81610304131140404528020302c1e152034404200140c3c0480d00020840c540c8042c1c080081600504010f00041c1d4042e18551418070b911680303d400200844540d0b00074a00d0801c0041248000249840c4801d001040540c2c642040608084a07541041400348140070400501d51000242c80341100d200281c01660380f05420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 364986807 1250 364985557 364985587
    0x1e0303020a022e030f0e0c06090f030a0605011d0c07120f140d0204080601050a0b0403020603070509100201050a05070c020913020102070e07020c01020d0c031d040605120a120305010501050f 83
    0x1506600f40c0b0301c000c00c1046003e0389a032001003030560882c801c000e5809044c0c500c6c4c0e80c0d0b5080c807203410b42c032010402c128105820082c4c0c0ea50394044001e8111501132041d07a40c0e005c2524001d8010500a01c5107603040000c1d002210b81c00c60300039815803070a616120168903a00c03c90050041d1803410b2100168034190340900c030740025000141c1024010742c54000c0c2d240801e0103540544140c00407072089900210b114a0607610340000c03140040d0690303144c24903640c24411240c100415400500a0070b01c402d1a488c0c40b91040d0b415031010340d0f1b00018003840c4c6502c400003104d202400c0c0c94200540c2c00c48034001602c03180701254004211a0717515486c140c4602c0101d281c10603503000000205948414020810703000034010300700c07034030036001c0e01c0b00c10002d002c048900350031a0002900050500307601926010110040d40c3e103002001e0720105095841c3d40110786004001803254000c0e5101440040610554800c224200d40300b40c902070269502d427500017000f07401221700244a03078800190844014500c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 364988057 1250 364986807 364986859
    0x302090406150b1611030f0607230d0c080a11070b0c070c1e06020318101211070303150602060c030c190e0306151f05040b0d061e0303020a02 62
    0x8215a131043d050304076021240031183e041314040303100800b42840d4039000c500810384000b080c0040405503102c0008540340f10000041e03008014a440280c40341c0305c5481c0091500181e038082c0803c901c040088001e00070700c0002c08113000c89203040fa006043d0181e43c42112000c1d90405180005601e5001c5201044e20030400c0c01068024600c000080740003071034a007a425400a46412030803591780300410f0744c0364841c040c1c0f0716000b260008070321865860702911000ca000c0b114600141c600c81142c05d0002185d16110400d5440036010504100b00766140c00f44000610a4080311702d00c0d03601d0920081e5440750003610443c1c0b026008400111024600e0303080d1401102c8115600300800d58000c3d0162480c50400c648502a0007084009031314100d407810008540e03400540341490152840e403190b000c040501c804001000010407001580002c21405468612a02c20300040c0552800301020034810742c2aa181c1c510302c40e108401c00219402003040c100303480d01941c0000c8180944480081d00541c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 364989307 1250 364988057 364988069
    0x50a09090501240e0306010e04030c060c110c030c090a051e10050907031b1101020f0f0306041506050403110a03141e01090213090302070e1f0b0301030209040615 71
    0x60400002003401d08000c0740e941c03ca9540110600007004907104856001800c5185505948a0070040214141405555074000c0c003d29200599000503030355a0191100045440c00180501e81c0304003001001307001030818404100c1c000c044600041020400003d4010801c0001070350314400100c0b9420103690440f00c110900c2c420802a141c118125629400305015850250050b07200095400c0d00900c05d1410b115413000921302c031403111803000c0343c00b03080e100400a240d5400740f1044202c03400c10741c007038040484001b14154a91034207402b804101c90b140072888880b0382021004000b901d07009070440e410360350460340074040f00c46040c0126001c03c0d101d5200801c0178445013041542c0b280003040d2081c4410341e5896500b028072156041c01c0c2070300c02800010794014520310006000c014582c0c007003002d00344203005032015503640e1f07169141205005c85a403164002290034084045101030300c0d40010b0701810300140c5c00e55046030042807404a00400003010f46a80e81107a20b0254601c040003002001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 364990557 1250 364989307 364989311
    0x907060914030316060204061704050319110d0e0f0301051605070204020f03010602060f060a140105210403180e010b0a050702010c231b010c030f030b031c02100b030c01050a0909 78
    0xb494036000a5001d071240400207500081c4048500c611509c829005540010086050603804083c1c0d94080311410341d5a0103000084070000d40d200e9060007140c1141e400d585804840c0c241e00000e10003a09104080203200c0d915003820172070003100d042d0754044144135524000e91a00400d10125009110307010800b00c541d1004000060300c2940090150700c1889080782c0411151142020b110080d00e09000d403440408071407103043c803154810300141206521180146003100c80f801001858000251420f80001d55143c441000c80103210301644020074803500d181c441503142120030b07a528001c000482003005400603811007568410240c00c031003590045054818000d410180007804c0c40d404a49a54a000b003560000182212421100780048107131103d100348000d81e602100c402603000e00c0d182c2823542d07070b050b0b01403162000c012040c09880082e4800a20600403640a4a032000c3d16549000c11400c004d400602510081204000d02d03030f0130700b0803075281c451850059829117025000310440b24 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 364991807 1250 364990557 364990597
    0x501051917030904051510181e0302130912020c0d0b0606220f0503010b03060a1104180507030509010504030c02090714070609020117010f03150b2709070609140303 72
    0x4404c820700f2800300c210454480c03c130b180d0111f900f6500119501062292400c101030100a22410801541c1400103416000f903075090310b0750300054403003503024081164690346603e040304200060f821403000803a140002d01c01c070f0700d44800140c0405e42c0c2410041c440d14044010481c030f03072140c00540300c0d07140c0201e008402c0b8148003081000c03076141d10b2107504000d440301c4000080a003810320030781862200140181032550344000807076028025800010207261340c20400010307040c600e0202c4040d0303002405000b044a003080140141500c50107000700c00c49924100038880001e401c0401d20b02e00c5075042c0c46d00000c541d00c0e04026508041401c4140340542c80c0000c91204200b241c0d4060300040703100b600c9554000700c01c191040440b0400740982200c1d8040300a051011910289000124116070ba602180c0940c000010911503540c00400d00d400102c1a843c0001c140d071001e01042d4001050402815402e2600d0002000e101462048051110070494031031004d450500855500e080802c2e6030300206 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 364993057 1250 364991807 364991821
    0x1406030f0c07060b040c02210c03030c07030c02030d0305150a0501022d070f081203010b031f0f03030509040605060c0a0201030e0703020303040e070306060f09090c0e0a09020c01050105191703090405 87
    0x140208c0180380c03030f10f40c0c40e081c1c0e8047d01003081d00595010710039460042d4290759540045031800e5000c11400e40c2031105640d030000059504000d0324a10003460b6802240f6414001016a800000012403038850f1680c900180a2664002850079600d86c501e8003240c207502da003200c019501d800352074030341289000340c20b0080f655804c1e40807090704841c03c0804584012883c0b401d44111408280680c81c0903941c00c00102d0708000e00c04544580960484001c41d0302260340c0c1034a41560400d5501c1140481c3d40401c1401551400e40705030f400801040c0d80051400080c218610340320782c0e900340d00034180342e540c500d149003107841042400c01555000d41200d603030340d4489001d800754203022154180041d00b80700c00414142d2003044000001015a100c0034141402c1101542c080d01d801c0700140d0401c10481074a1017240c2c0c900d501c00000301241000161740300c2034a1206801c1d500143c00003405030f03244003021082190050110000c9402500308031001a81d0529194210b209010f07031140c1c02402d02d4180244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 364994307 1250 364993057 364993063
    0x806010c140f1506031504020105071403040e06031c0e1c1a19060803070b041e140c030307150c12050703050f090a03021c0c0203161406030f0c07060b040c02 69
    0x1841030b0744040c03103c0e5507203040401d9907030f03001500c4034426005d01d0f50206005500880c05441c503203100742034060342350b1b41c8601a40c4c9107802c10741c89100040c1c80c6a061040b103050a001e2032481300311071280c0070444212040050300010084800354000d00b11181e046c007510341c19250040c0480d600c40c0002694a003120300c158581101610441c0005020722648404000707284543d1040b20308036005141000310503211140c10140040c0b0540b015103142d1018526103842c02034400c2c3c41880b86032200240001c01240b5850000e014049501070790080000202045c01c2580c1e6503610201448007040508000504803664006440302c001d000307007003c090007180381d01078102c90320410707004103a41c0c1e140c1c0e600f5914581d511602c02025004d03070800180f17004112441d000b002c0040059080500406000d41e005c6407400349a4103403060b50341152141445131301100c6140d1082180c040700e00504500701601044076100000e0304003068003400041003003c116064000c3d80e01244001c0c000c001c50540a600651 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 364995557 1250 364994307 364994323
    0x1815040503010608070905090a210e031507030e030903030d09081303080c210d0c030e030c0703050706030905030d150506041d070f200c0402040f0e0c0a0806010c140f 73
    0x11842c0d01f020300183ca90480090039071080da4109020364402c40c2d804100360070001100003101e003000109c2d00d4060094408020300e4540d000012007803c8136180200c00142103a8903000200d22a410401a000e007a80d0008180e41d0b0008200c1030008403000d80b0b103460241e074071410a034501000d214240000912141c80058440c1103003a0301500d8102e21040801c856101001b07440e0000312005000389000780203c1ea220141c000d4080c103000030440031040542d841c60f00201c08407000740e840318005104120082c0b11400050a00342802d0100751133961350f880e02c900414a80542ca0359540144a1540300b01d40d01000061801800032a6642d85480c402e903103810000b0306c51384200d540c3e031b004925920300c1200c1100c06e81c0c1c60703951a0510780030000c0e0078000c40120024180110b01c81c00c45807441c240d032148000c00041400404034010750b86003e14002c2403030402420b1603180381062119030707891500414150b52182091074000c0d4440120b180207401307005a43d0300e00f0998442c042c1c3c0311a070120000b030494 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 364996807 1250 364995557 364995569
    0x60921070f050402070c06030209030a050303011e0e010317070507180b0306090a02130b0f040c09031e02010801060302030c0c151005040908070f021201090c0e0903181504050301060807 81
    0xc149a40c0380c0b410300080e0711909a000341040303030300b140c00c00c080d130301c26405080120001415a41801d2042e01c0380341c50b40d082a04082c055580c1c1554481c01380442221480040005005a5510358990340b140208403040ea24042044480000d190040140610448c805441c001f1810321802d94242459401000e5039600280248607a00200305603800006004441590051444440c9443d40c0c5420000e00362484d000c83c0c000040c01c6000d4800e80c1c49004100088030165240540603145040c007a11203a512540c0300d08a4008003403410260344c1c404001815141d881c10050b940342c035041550442d910845610701110301a04a8400308014210171180c0501090030400342072a840300d04000490300024001010044108480d10005200b41082203800f4001450102403020b0307858620f080d601564022554025100b60501c510704800760f90640092803103004508002644c4141c00510645000d51881a07400c218000b1002c0c2000d8221009810060000d00159a40d00c00752544c440b2140500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 364998057 1250 364996807 364996829
    0x702061b0313140904060c140d020309011407080c0a0e060a27080a06111b01050f07080c09010c0219081c0f12021e0a0f0f08060f06092107 61
    0x203c1010180084581d0a0014280071543d1216075074040285620401d01048c4030307001100740d0007116400050001c8403802100907942e441c00750b102e0790031100000c900700300034082042401a920380c0700688503401a000340c8541e076603410401c401c1d503400f000e42600d20f9001100050295500b540040088880f4102c80d10745580804841a6a0b40440903400f400c0c0040e84080c07214004541e04da045401e84038041c0c0740d074a2408201c2101c29441e101d4000740c01041e13a464805000001011890303642e4000380e01e14040210741840c0e60584402d2003138218090400c0081d4501009558450741d00f0802d0641a801126080d55a03c000030b84804002041c000504c403c860031144041c082c10100c15103490640d2001560b0b0b60b0089030034001d40044420a6851251990606004002c0c500a01900700c290b2240d00e12401120ba0003004480e030811001d04001441e41440900e0b00d450300300310880c00f4107d9010340c484071404081141e80c68545606023811400c41820b640b02040403c103e01551420800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 364999307 1250 364998057 364998059
    0xa0906050c1803070501020d121418060112031d1f020a0201020f070b0318030403061d0607090f120219120212160b07110307030312060503060c09060702061b0313 71
    0x8154690b44c03684070f000e016030008050240e400e031050111100800d0b50796400546100c041c0038000c4071039011207200d00811003808040080324010404540101072208000340314a109503802495401400101c0025419907500e0030403680c1c40880001030001c4246640310780f8106020001e6036002001400c3e40540180c400c1c03030540d202d01041880030f0f502141d002c2451a280c00c4484c0030841e00808529680303000500020000910600411450103040600040543c83c00810f40c0d04064014140310180409001d04112242040004004403580811920094401400416140f4050511407030180301c20031808a2042c00806584601d240241c4c0c00c201d010302c000c0000b656400c0e00e02c038880500c40740c9400c20000072001900034001a441044040170000e441004030740b9100c0c6640045010072828100f20b09003840b5881918020542103008241c42e040c0f05481c0c550381d204680045000302000110070056440710703021034101c0c000003104101d1444101002a40700d8200300000441b022100034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 365000557 1250 364999307 364999309
    0xa0203190815120a0807030207120c140d050709020c19061b1106040f0f050102030a0e06060a0b03011401050903030f0703030c2d0909151d1308030a0906050c18 70
    0x343c0d15112112107008044940260b1107020543d009100105c0031031248d1103012548062800003c0ca1903441000060112820021040c000411800c54070340225100b003908804140001048070498081c2840180e440141c181803504116044240070015030014070b20708200303e001d50040000b40554012942607003060501102c5981c40c00b46140c0a580c08800410049001d5001040304c661188111445c5d804a566456003a80c10441c1ca001c0151340e1001c0350000800706100b1158001e4003294152080740c1041c0352004140410300640c0c400700e81c07090048071542d02500840300d82400c002d08490302ca40166101405c1a8801c100440000b410180b4090300d02d1701031240c240315401480340180380c80c1001c44e401192002c00000f00000c000e410500003808009501c06c0b9140c0b044146840c5c50720906041c0c800201c0300852680c41180c3c018203040241c40883c10f211104d401c1e074018034150b6a9250000f080c009028804000b0f420a480d0030302340040c06040d00c2c01485890303840e041d2083c403062001c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 365001807 1250 365000557 365000569
    0xc010e060112240c08040204140105030a230304080703031704082b06120c0e0708010b0c0a0b0f190605030309010507061d030a140901090302060a0203190815 69
    0x7220b250b5a2061505a0600260b0184040e20450000201001480d12420441d0043c3c89009400c0f02c00302e4030b010188070940c01e080c014030a440410b0b0350868415454040841d0f41d43c3c9001e030002d054040308107180c10000400384141143d281d40d00081b030740c9840e03e441803141c403902d0314401240031640320301d101026600510b44107489a5004001a81480034041180c17094201403010002c101148254040c08900c00b40300301001340c5003c035000c541c10b20561602d140f4241558120107803050009042014071503100980303e040d80d0601503080e803590304803e582c074170f0101183d900a24030b0858000f0054140ea0900b1410320498003c81d120840b802c01c0d54486e0200e07243c0780101074054200300614007465002d040100354040c4280c00004001084010319440404503a051024541000502d03840203580700041e003202000c54020380745080b4034100064800056441300a0255101046800ca0070f030017031007030380d81007403035020340034070110405c2401801d100c000c0f183c0d044a0790b01344040c420142001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 365003057 1250 365001807 365001809
    0x21503071704080909062403060109050609061e070501020d020d0518060a20030901050627041b031e06060803041a130503070e0406050604051608070e04060303050c010e0601 76
    0x865992a0501600521000d05030080005400c481066642e440c410340c1003048001c003d5050660b80c8d242d04100c000103100d21582da1003248280e406125808c51a5100011076200035500160125044119204034080b40140c1501038065480460042c48000160300100004502802d0130400359a07a142c180804940c01440301615034040d01c0000c00040c00c2da805502411400c0c85000e11005030707603038041100d0703004844881d5683d4440050010030b0428180c085182805030007041c85d40d220480041c24001d070014070182102510485046000c0380e081c0d0030401564204108214400ca90044560708810310001103d216162440020344414040306aa040d5448003507041c0d003480f06000026000c0e000035010140c620055800014696020003101000703000000e00300e00c1034549414420304580c00100524081c501704810080500048040c02100703a225040094207070f00c541504480c10710b00104c0b95600b0604d407a0010050680003000341c0a03200f161402400107281d40755616480e0340007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 365004307 1250 365003057 365003063
    0x20606010908060a0f0615030207260a052a011401050405070906030b0a080604030f14131e03051e0610080307020607060b0402030c2d09040f09021503071704 69
    0x1114000c180800c4940e0480b41c1700881350b0402180d4140c4419103412080320380f0384501d0201342d00264000c00c1001c1e901ca120414100460a0b1495880e045c05460300341c45a220400700304100042c14403e0114400d015080482c0d550000c042443d400e11003190007400700230104131802036208000680303450903004051041e1804d0b41c3d50306605107014030640140102d0020305a0080c619503022408400410105209a000342d0b070b44c141201c0303403a40141c218002ca18240d400254102f1561160f1004494100100d036000000c81c03521106c0070408404171491900010b0842c01210340c0042030704110340114641c04c031214140d90964551803625003080344248500364090b0800d01c402c8015241007400741401a00036035020070180e590000240c00ca0f402200c03641030140000c980d1500301c5000907100286090902c2c02482140955880c241c800d00520f103a00c0d1050313407111388104108030150014800d031030b07000e00410300d50800d10003a030301150022141040000d89909450348112204e425080c040e82d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 365005557 1250 365004307 365004313
    0x3061a0306060604302a0602070b09061e0a0f0c0f0f02060705030d061403010c20070504020d0e160338090c040b0301020f0f07050a020d0c0501020606010908 69
    0x40390000075a4182d49a0100f4203481c10ba64040c103200c0c03252220107540d034921803488601c9001c0b2052503806e1003400c3c0413400708002d0282e54113220113600014100c0036070b80381c02805603c640b0010001901882040c1c46d80d0206269607185003866010007014051a400039240d6115080c1420b404071a0001002006842d0100c0080b2500224250032072009682c0d0000d000135140059a4686900e15440242d10429483e030320b0004100d882c02502c56140300d000101c0092201035400b403401480200520703095122580040d010b0901023070200170a1004240240065403504100b503084401008010081003290181103104000c1070329410440d016240d00a402c88a40c000006508996280051084004c040c21150056401007102205c5100f106032100030448030f1440001e0005884c0c4094245000c1d13030046c085003141140742070541e981032001100058880b109401c0c10b515081440c01e0180d04000c045c1d003039400f4041e40100007016600e01380c00311441c94030703420011202d04c00103101c1c94400390 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 365006807 1250 365005557 365005559
    0x2010f0302090f1c0516050f010302180f01030f18060506181b07140f0f030408030405040908040302100915090e06010c1113090302011b09061103040f03061a0306060604 74
    0x200e021903561143c02c10070303213828990605a94490749000003100e45244240c07442d40702003080345840b00850007050001c0c070302541001c03e520400c44c096984a0116071184890010199290b4487e030700071055009110b5051221030300190380090041041d10081e01c089051400040c898106503c520303608054220090505644200c0031005401030708140001c141001c1041c032001c503d44418447d801b200d2680030309105220700104514110b0034012145040d0800d02c410054044040180c2d011540d003540c0215400c40341e071034403044510503038100a503c50301c040d0400c44520790184043c000d540e50403031800f601a4401c1d0041c0c802d0a010304c18004141c680000003060355205030551400d143c0b2074441e28165007810320001d0351424020900088250340c80501605140d030900841c8890964040320652003c1d1442004022000720300582c014002c8010f1139074803030002002124000c0c06104a0342180c0c035100d24214018140c0700e030b840f244084d61500000d0a525000c03c81d10700501c00104014506 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 365008057 1250 365006807 365006809
    0xb040605090408161209090e0c0a0506090102030c01110304020a080606030a060906180b060a12210504090609060e0705310305010516171b0f0f070c0302010f0302090f 73
    0x95000528084c01034105420f1000000d500340c0400301c1030000f43c2c0300d020003682804102e138101d0b484655180030560080c43c150813240c417084004016100c0c15600903986004650060b45035200f00070011200d5840c0c100b1440b85101c5000185001714030031900c0ca0080340ea80d01d0b501f990b8060944125034581c100313580400c001010b035400a141107100e44000710700b1500d409411285010070000a0712441c1c480c41c00c114a0303103444603400003e084c40b42e070309840264890b100d000c1a5821400b1244161030502c450b020620301a8058170000c0901030000d2103120303250007285003c1e0010703108417219900541d001c541028000c00a540e2103100014240d806400b09500d400c1001141d5208214103d0701c454003c40854804e006a034460b80c0580000e1880210141004202d01010300300251802e043c007091002480c00f911145000b90107042409840d488900340881c128400d000860804083c0051107604005400f15100300f128002d07260440d040c0c105140907000c2c1e00c111122940c0c000152040311801e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 365009307 1250 365008057 365008073
    0x30c10020a0903020d06151a090d021f21020301051309020a09090809090601050909130614041a0c0a1b050102070624050303210414011a040b0406050904 67
    0x400c41d500c0c58841d00c9282c1c0d035004100c1080c0028010303100180c803400c2c8180c00d00008801c4200078855480d41e0200704520300d420070b0382d0b8040d401641e48030305208180384066582d0040420103841178600d442c4041348603000041e090202d10b0b400d4030000c45500c04100d443c0056482aa412220068249402031444004407401407000d000200e901400ca05000b0450105502c00c03280001e104a500f155a01f03a4841000300e040002018181000000c101a40b4a9103c003058950050003103018180f44a4462a046024040c00d0000700c0c072003844101080180013910006801c450304030015070042d03842d1981e0340c0340b15220350904100454503050444006107507030100c01200301d006000050400c0c5040d510344040e40c0303001c64249450303203607206400146104010460300504c0c0c1200110710300b07980d80e411000ca0782c190001048040d400000040d052186020740da00ca5131754050001c22004e2800c5030001404150f100c48503018078940400e80f085400c0600c030b000292100180210241d507550b0740d455203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 365010557 1250 365009307 365009317
    0x7110f18070c1209180203011a130b1c050901060e2a0f0a09090b090a0e0319050307020c06030c0318030714060103171809150d0f02090702030c1002 65
    0x2041442c000d000c001c140349103141c842d00c40040d615500c1182c900403014841117804000b800300b42d44100010001c00214000c5601004040d5481588800c16042d5003804900142d0085003c1080064405025100e850740d03480d10044a00040000d612500059402c03141c0c0b0380940f28401e58060701145542c8202d082e940d40c40e14101512156041c070382c2d030000c0d41e240c00481503c040b07035401154940340f41360404c41c03c44c060310801c041040100d602c000005d40c0c0e0320020b00020420390b0750700300c1003407000d0081c8100d85045c0c15030464115103091183c0d000300164001c547c00f074014007030000080403a10340501101d004d0003d01130741c0d03410b541b40c299000b000341120003420a00c074801003042d030300007640382c0c1d10700348081c000b0310003801c0d0079855804d06001c0780c50802191006804104210042c10103a00042d824011058400315115683c6056802c003c081e40910154001c401203c00313401c00c500c00000c500c0443c800d803410441522241403c3c1d070303a405070750001c1e00207070009103600000c0c2115034043c107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 365011807 1250 365010557 365010571
    0x90a0c0314070503120a08161b06020f070311070801140a02031e0108011e0c050a0c05011e020903070608190b06090d05060708150612060a030803010b07110f18 70
    0x901c05543c90000903d40b2034140b264650146020507003d1203c0e401c1080250f000d0701d0301030811130f08050040c0040072480740035a180b0704401d41d0307501142840701c55410fa40310410681840707543c0d60b0590130094540744a841c80191b0728410b2280204103004180184a104030381141050740544620b0072200194100504ac07240c0a414541c0314068211040380c41c074000d081d01d1000080500b06038100c0d2070300c0c2e2240b6003602d06060074454900e410561040440d04100f00c5072914081513001c80c501140900750301c00c103c483c0880000030705100800c840d40140100ca000718100e600c0180e42d1841581d0880045032280d100503480c1842d00c0d48075401c0e402c10071809038000e0145280030502e2000482880644100380d80a40c4540c08005d40c5907000a005900490010700000860000100241480c41800000d0441c211541c000c00c5460300c4803d046400b0f0f69006045a440c1d40c0c5030302078101e035500a01c1080c1c8a03503426840581c00c508103240f0041880303501800304054010703c940500400b0001402803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 365013057 1250 365011807 365011813
    0x106170c0607060e06070c050106081903110c03030d0606081506030f0403020712080309210f0c0705030106030809091e07110a020a23040203010b18030307060204030f0b090a0c0314 79
    0x403206403050117804c0c403503021512a0900c1c8a014100142100c1c41e070b13000350080342d108040041d03081900703140044a840d81840c01304050840084d006017400c1d485103455400d4400801d541817066416006042a07900300e6507607a1a035a1001c40744600d484400032420b41001c1c0030000b190350541072160a0303900501034012100200d540e10040355003195001000d81c0c0c00303c004414130410744000d000b22074401c252051a951795042c030b0030007012248200072400c0032401e40080c50100a140500078540105030040013044400c7d9a0b00344801300758840c0e80c110384651111000200d00040000c040301d140c0703900b46015410380c0da5100301952030b85050080075846100703e250240060307440d244002d001d022881c91080342000642c948420712040284030511981c014401405a44901415540026920303181081925410f1003c40d056204a420203800b0900004010091154071080c0090b86841061244000e944507000395840e20100440103018507074810382000854204c0640004d1420241c040d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 365014307 1250 365013057 365013071
    0xf06050d140a0b010303080a050601030e06060402030a0b06030f04030201061a0a03050c07061d1903080f100503030f03010e01060509330c011a0118030318180203090106170c060706 79
    0x3d40d01030303081c264002c0f00041d88900130400e0002003401151b4221000303080a0141252400840e42c031140010240c0307004030350200015289601d150085000740d4805410b41d45e803824054140b40d0403120889056025608000d8001140305080c00c6d0b401c3c002c10341600301e5080c0700c0201c00072001b07004043c1c00f5041c0050180000004034480d842049020342c405d0310a204051810407070542800448200800e000c2e103072611200100740c01104a55100e036601d6a080c210f5031b10b08901d40008412031300f00c550544400b1509003034250540307000354161040039002100d143c3c0e07609001c940c1031141c0048031f81c21900001140c40101c00d00065501e203844028002c810b079030400c0503510301035041040c200c58a6034660f030800960140c203000c5500444d401386440c4030280e0340d1005005007040c45200c014100458074803052108540300c4604005884940312060118600c001c0d000d001e0341056035161081c1d442c0410000c1d22141c4250301136483c01c0d080c800b4017140c65141e803c01100b03410014050300d00d20748540f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 365015557 1250 365014307 365014313
    0x5010e13080a120c0c0201020114071d0a0306050c03010905060d082710050711040b061c022a0c030a170c010912032a1e05090a03050601090f06050d140a 67
    0x6913071442d15807030b90b404941000c103000080c03e60f4007080c400300500341c0b01014880500d42c003c4141c106010900c2000310102c2d02100400c0403100c607a4000b5188525010600a0800105000318104c0340d5025080c0503640f25101000081400050010402e40c0b0070061010001c20301c5e400840410a412000302c4001da01e507010900d5031068041200c000341c0c0c00507218003000645001c4ea800440196020041080742c0340c08124a480341c000c444129000d030040e6081d40c107500ba011104444500f00c1d50404d0140d8030346200501c01b44c8214034001c0e60160560305000c904001900d0017459400c840602c90001d816040ca910661002d09507800035501ca59045010910540005001e80200d03a0005290082e40064025030354001046e40a051240c1c448030f5405a4480303808812070840e80c40c09a106071002d40152164403d42503010341000c1080c0000040c081c011810314100c40c0c2040c0180304c21810300c00b045c0304851807402025031207044461820081102c4140a071000c0401c001103a9010340c90761 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 365016807 1250 365015557 365015561
    0x902090c041e081e070b071101080703020c1507140711040e0f0c041503020405070801031203091a04020102120d0f1a1e03032b05010e13080a12 63
    0x100c0301000d14000041c1085150001000c200300422100349841c182c5091110158941085011044208400c000362015a510a020841c014803c0c221801d507108518942400c08441404840d804210f1080000d41c14600a00803a040c041e02000a010f60180ba41e82c1130601c280d001e0042c100300301e81038050403d07640d250380052000720300072000e006181901b18108415150f101d100300905402403468103c00c0b10000440c0380402c1d42c00c4034042141e401ca1050003940903490b81c00a075009041c1b0051000040d00002440e050341e0040260001d6404070303003016000c0d035041820041c1000f111400c101c00740c040c20b5034541d030071510500c180c0c1c0118280d5031045400760441440004159592590020108c4161240d0b044403116445500300c0c6c05400c400246002c00310040c000603040070b14903040030b0b55605100701c0b10798a8000d43d038804a942040f16185400b00c240901d91a030340d103408008180340c1c1890b02e000303104004204062041a500d55648892038004000140600900e403441e0800101c0038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 365018057 1250 365016807 365016811
    0x302120f0702030910030212010f0501170601020a020a0303120506011d0d08070501020c1e010618022110181a1c0b0408072102030a1103040306050f16021519090209 72
    0x42d54000d88c0b5202501c4401d0070046043e440851843e1400c0c20800281c0d070401132281002c150f0a11840c07a5958044c0141d04042142d0802075028121401c04000c160f04071069a1101030b410004204960f030b190b0040d40c1c1c0300e140c0c18590314100030b4110321071740c10700d002807803e2142071051300c04a05042c065690542641c00c841c141082c030740c0220780031101d54817450b081e890040680c44000d21841c0e00d060001290344034040b10308490305400160b50803206007070822031030100b040c0c059803560034541412104200c102c68082c942180580030b6180c11400303103d0080500c442e46c0364483d04070003540c0c40200700600303024103118a190074142c01143c0c04240c0c3c1d945134030701c0b4601400d2503035550701281c5400b8039150300540701107814681c5485020b240c0d1340e0000c142d604600c49800c04403081564000f0b014914080c83d880140902e04150800640584245c1c860b0f00030f03034044021030000412400240c1c3c6810218501624268104e00040d00d101603d1800081e1014241000502280f0f9500800c00110003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 365019307 1250 365018057 365018089
    0x120608010903080c07020108070e010e210c0312090405040c0906030809090f090a1e0606140a060512042301090303090c0f03050303010e0a0225120302120f07020309 72
    0x256204641c141038110268650114181c0e2515191407610743c00030307000c901d024051504100101180d4003603640180e038240c4a9600080c8840c0040d1980d801d0f1420785816400f803101d060003050b14010030741c02c1c0010384d0048000c401d96240d0400c0090002e100003088010002d0321003081c040f50000d10300f01213200d910f005c1c6028a2142d07a980d101c034006e0146c02c0801402d103480c0084288200300c00e041010500040c0d50340e0002c0d68004468004070100d0348602c000b0400313014203151010000b28460240070000f240c83c401d0701e41d0b09003503907a504183e07481d014015001c002015031100203030000314060740c100b441c801d600007c0f030351845c15281840c1c2118540c0204402180c0e941804a09004001154800504110380020065411565201e860f400180300750900c000f81000407402992039901070b41c0e00704444440e0282a40700c50390090350350b00e5400d04290b501e80c0c07030140d00801c198400c1c000c9801c0035032070140c9840c3e241c545101c800c140c040010107260460000b449550090f0b502c0541c22886500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 365020557 1250 365019307 365019311
    0xd060b0c0a0309060c050a231e0d0908100902010c150c09090b0d03051303021f09090203070c020d020a05090a090506090307051504060b0310020406270909020112060801 74
    0x900d0b407602605a10190700a40140201400004000f51001409035409907100d080c44048000003541103a210803091420a4140102c0200390070b45180000c00c126010034400c2107407c9042d2001090b204181c03680a003582c560401240a155410960058a4014418034094025903810380344c656a400c80c08450b03e00d400c0d00e89040120b0b103a441a0000040c04913030608100d1103007200e000408082038840c0003418050081422204048041d00701c5e4002d60700034191441d0303d19090710303011000800550360070103c1c040746000301e242c00080c400d6a2050703c0d244c036a401c0d820103980800604002c440da0407030780188d00c41004102619544c043c18003405080c0740103c3ea178091454072604008005090003516403090001d034010500000700415041581c0341c4030300450700c4504003003000c1c241008515030180b142c44085120510070354010403c540312035403034650a031032490301e0740103070600305d140c00d2401c110094050203e5002580032088580c4141044000c0703c2c4602610010b8070700990061a240e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 365021807 1250 365020557 365020573
    0x1902030a052505091e09010602032101080a02091f060f020d0201150306090219081c021c0315050d1401062709060902030303040605100506120a020d060b0c 68
    0x160b40701d0300340c0a964080184449054202c103030014000c1c06803943c1a84101242d5903001c120080300e0004024a2001034502d8002e503840e080083d540c0e40c05000c030030102c2c61180c0c240b800102c1c0401844c605980891014001703c540301d408000c20254081c02840c000400300c4014007400341c002421a00401c0c0d01d445070143d02650000181c1030030011030032003046d64100051a11101305640d11102503a60204000030b034003040e8008200e6080b035543c20301c5084000840b0208100f54000b94507104800f201a0491030103c8900c2e08903101c48194211009160410000c2e04405010740c001440180707412200e15800d40d83e890000d06000000b000c103a81e00b80050003d040e1039a02801502c0c0030f0a08240720714542144503010000002c1c80303101440001c3c0e030b20214101081603a8002ca09541d4000703088946900309410074800420042d1039115594040385000100c41c10407905660380b20070084c0c1c10310819902e10201030043d40c049960a000c203681c403140419001c0440010307116940150b4010a110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 365023057 1250 365021807 365021821
    0xb01020601080a03140a18030c0f120b060925121b091202060d2a030e030d020706090f050708060a0b0a0b0c282006070b1902030a05 58
    0x180d8107800201c0107412858030340c0b020940044c0d8201e00401c28055a964031003a141080b1800d04545e00c0c90518040200000018850032072490020b403007070300710181035240d07440111038403050480c0d00c02042441101c00007042072500c0d61180d50300288043c50004c14510700454503c41d40341c801007480110302820103c03586141e1500c40d0043c01a00c24114004500040e5800740484545104116201d00341800800c2151901c1c419608000d80d681c01c00d20021140b1036020440a170404c0003034602030715610307169403214400d0203190103241c60000910300e445540c030144800795200e0407007698000d440781e0440b40000c4119600c0c038003040c051005000c03010b050104071402c002c40a0310044000c1d040c03807043c00c0c090b03070340891031001c0716074103060f507940c8030400040070341488a541c0c1c3c01482d8003107400e15442a851019034548010344a01030035400380060382c481a03c21900c00054a4024031f041c80344d88001801051459007104148170000e400c1500d50041c1c10503640b0032103c1c2c0c03068540311024440b803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 365024307 1250 365023057 365023063
    0x30c0c0b1b0a020a12031103042606060105271002010905060108070b03010b1b07030311070819082116110c090a0c030e030d0209010e0618060a1e030b0102 68
    0x1104120070050a811040d603000501c96003a24000c0d4942425500340c2c0008150140e420f84070841c0e103280640361030786e580e41c0158403604650500b0a860112101030880304000c08aa01c0d4440e0405840d41c5e420051010004034281d0440456802080106030881c01d59503108040e05900e0029940003023141c03100e41c50041c0c10120107a10001c4c0e1603000d01420b000d01d10041c402e03681502d142a281644603000c050b1000003001d03114070000d900d40699680071080c10340c09000b04ea801140401143c01d91641c03113074541e55038603401c070090042820302ca58940001e602c42000b0b1010601d49441c4810102c10340710b0007003609030b00b680c003555074a000e11180500c540d0004040700301d00e620140503214035260403000c10a113400090200364003942d43c4080000d8a80664881e14404440c60300300e0383c0301c180c41500c010003903200c55849030129600c00d03d041c015140c40c500b29040d8062860641907401517620a002c81504840800c0042c002c1c401c0e00501c5000f612607030302c42d400e00143ea0200b00903005c00700182c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 365025557 1250 365024307 365024347
    0x608030f0301300305030c070614090124030206070602190302031608040f0209060a0803040320030c18070e090a0207020f060c15090708070e090d02071d04030c0c0b 72
    0x802a03840d9040707020820998400814119010b085c070036501d0b659044450707020311441d10000c01c002e10303007a42c02285c0e0081030b0f50240300d5210304000704403806202ea4040710144008010f1541002401814801820100080c1050a1040c0d50150a1400007000c0f0740303460114410f0000001d40c08410040302c584c0c1c40c1400f00b05400d0340d040c003030344600342521900e0f40003940c0e0714064018441c8401007405a1503803261000101800300a4030303195a101d00d070044190120410070004035035802107a28042c034020408410580c0000c144040c030151800001c54896070083c5008113125443c03410708a43c0d181d0160340f61207051a80001a0b4400d2030344104211680c0d0021300d94001e900c10f00c01c10304411000101d1f5500a03100d041020840d83e15200c1e128a411000d8000e40744a024440002a103815007092050140d0f03140f40541d01910b1003d201265100701f40c0c490705181000810001400c0208001903c1e00140240f9000030365048949a00079081e009900440b4150340c000b0f000040c0c0620300d41c80700c4c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 365026807 1250 365025557 365025599
    0x20412050c010806060a030902030717010b090f0105010206190b030610061d09130c03020d050609150415110702030f0f010c03091101080903070609110108180d0809010608030f0301 79
    0xe0b0b11424000007182c45ca004011445051558aa1040d001d541d01007081c50005c01840302c1c00307542e012100701c265019182500381a4000c2c0303140f070003042400340c000b41143c1c10384034107a0042055507104401502414078a50b11490216900d244240481d20148080b9214003011003220034100c1c0ba02c2402020801440c00d104030641040040d040c141c0d03604205550004c4803115501038040141c2809080080e007540002c0d80092a042800104100450100c3c490b40d0b8400030b03501e000c0c54114000365140700894009203e01c05840c40360808100d03031f6020200e02c907038501000d0b00306a0940d0100c0d00d07040c1140909902640000740c3d0340e0000100b4003904809210703610b42485181001d0b56071300d00d20800c0000300c44c1807005030070004082d40800c009844010790865800d0104282505012081d94540c120745070010b00c508000903041c1c90040c401c01e034184048001404901c1c04072900319401e913000f41c104035141d500c901000510060410180400e10800c0a005a0301e5140104203214006203e07058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 365028057 1250 365026807 365026817
    0x11060f070c0e040b090328120204090506040e07140d060e0f070810020a020312060411130e070c02030c0d03050f04030501022701080a05150901090c0f030213060c0606030501020412050c01 82
    0x43c0c9004c7e104014240c094000c9800182c1440150309800d660f440b003502c4403041c19510204001541c0991500311a001c1c402c2502c0400c008819003400f1f646132940d84c06101c2004000000d08090f9041c024940c4151901a080025401c00c10340086820141e050106000701c1e40f182d0f8050280038018007411240d2001c10500310700c1c2501800c006500c1740103000702038188050304c0e00001e00540320754000d140f088420a080302d03915080285031011050705402a41c2c0800d04c207000050400c1d0040002a0055400074001c1c0041050042004102810344500310104030080c01107010702190403001c0c2018500ca113000ad40c541150180d00e41403203203030000716200d010400e544943c480e40c01225a58201108840c00325055a0f4446000303a84000341c40981d400800d0000005000940c0360302c070075110100356462840c031103c440b008906900400581601284411504014280c0a07808001440c6d00c11500425070564036282d190898100358041d0030003655a0801c8002c200c4d00f4806845500000d00b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 365029307 1250 365028057 365028067
    0x40b04060b0a180203100e070903050c09061507030201060b0c010902150f030718050607060b030625051606020c06070801060c0507090b0103090c0801060f0801020711060f070c0e040b0903 82
    0x800820b4060f0782180103465000001c07528090030881c241000e001d1000e00d040c440c3c02e060000800c05061448140c07150b010701112110140707061140c140c0108401058080a010f041c843c42d11981d0010908906541d6282800908181c403000903040d051ba101000041d883c00c1401880034618000c071070304030310220400098003080740d541c0c1600e8008800e441d024503034506112148407030388040c1e003205511180109003c000c011030f60300300b4491001d054069a0094841e608000e1500814902c07154421010484c0d41c02e005124101a00711543d48180120604035a510703010308903400096542c00303d80140041000b2241c00102c0b0390300500702c80c54040144502074a845071074165038040c5aa00300c1c1c80700300300c940c1a80f1941100280e5900825a00d00c102c0da9624454020055442400329030b01d000d61000071402e0061080d1001d540d000511000d42d03622040c01c0003440c0d031080c2d8a0301c0501c0740910103000802c44c1700c4401006004e02950704080c0d4105401c18180600e0010b040504d69801002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 365030557 1250 365029307 365029319
    0x111606030b0f1804061d061006030609020306030a02060a02031b01090501050123040506220605030c0301060302010e09041e080409110313030f051e0316030606090303210203040b04060b0a 82
    0xd0365a50054010a0009601b50786060120903910004043c000f20b114800c24040e04c0031000b48820215180e40d2020410a680d566500080e40000c540003945500300390a0381c009418004000c0980305070903c142ca03d0141c00e00021000c0388580d92149004d82c0d03503507421000700102485542c0c050b2031220060254141f45d1105c540020070342240c0d6500a41d160004191140ca070612003a01c81034004811015041c5140d50b08801400c191180c2486403140403600b084c1402c0c10310695003680d8060b928465115070382418400d0038000900100c0d50019440d9110004240c500d45c40301400d0f1040541d50b50307840c641050b00081d01d0724001303520400c02d01041882b007500610704103074121a0341802c10782d4400500f000161014028402100b0707001c8115103007007850042e603034009d42c821540e031040c0c20305005001c00c3c11400c1b20340358011a00858404441800440d000d00c440041001c021070543c04200c503404003039810303030308165811030315421880140010001c6500038100380342025034500a81528000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 365031807 1250 365030557 365030599
    0x30a120e030304150c02030904090f020a1413150324060e060a05040902040e010e07081207121101020d0f050601080f04020f010c030c021504080f060906010303111606030b0f 76
    0x400312060055541700040859070007032094030f10145004100700961016030a118810303080c2c10200b04e204005181000c203441c0142030001140308005410081e4600c00312400c0d40040502c4d440c42484038805141c0040092820360b803a4105e041d0341c2e21200178642017a4541402c3d160944c221192011145040255a07120080d440c800c5031001c4401094000d100c1c00414028010b0814041940d400d007842501519070020341c00b421650040300710740096100d20f8014415000c2d100004285041802107d105184101c00300b0070710b0206100014030308440d50002d0012104040a4045000c2d00c0d0343c100217040d0313080001c15601c4401300d00300d4655460300da0b0001d80c0300341590110f64140300e152042c130020300d4032800103000100d46c00f405210911070085811983c03070300903108111051240c0c441035202401c001c00c146000304010b80080026900316a415199920a00c80d03a100300d00c80c1c0f030078104140005000d072200502803a1400298519520248070b103804410600e03c0c060000346400f0380c07200d0128 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 365033057 1250 365031807 365031833
    0xc0602210d02030406090204060f080d021603060e15040507060f0e0306010308160506010b030402041d0c0d0204020c100f0f141f050306160f0c0206030a1508030a120e030304 76
    0x42240183d032582d840c6403000041007100800781d0024580302010030a000c446d440c102c1030f50300280c1140c020046036034040b40c1c1c80c10010420080102100c10820005901d1340084441110110a45802c450b000c203a004815404603800e503000c0d400441c042000540090544116090500d03044002c0401000070075074854040c030004051038800108240c1e03010b00b4449880c0780c1075016085d20007a59440b0501882c0c1d800c10780d0203034440ca1030030407034208051810500d41180b120001c054040b0004810410444640c4003101380d070000e03001c1100d81c500f00418802d00705c50520402001519500004d503040840d2092055850380903d44104582210425000b9690280c90100d484541c9045211004403145a81e481700b40c1620440092202c030300e060258490103805643c0ccc401d6203161050f482241c030307100d2204019411980070004941d11440c141c200c1290507290b10340d03181c07280c0c1d03a803030019141d60700c20b0440400040203070b81c0a425001c25070003804840d9801c20003c40c203500705511201b024000c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 365034307 1250 365033057 365033077
    0x4060305010e06100f050c03070308010504060509060d0809060706020d0c02100c1403061c1505160e060901031b020a020306010e0615130f030605040209090601030302060c091c0c060221 81
    0x2042500c1c034685103e00107d1f110031188105683e140c51322031401a014604c2801118412810030402084606100840c0c41c82150010318201c00d2186c140c5414059900400074190805820031018012802c68002002403c5080400048030000e0380b4000741008140c844403c80c940c240101035000b03076800244071904489103c00150380b40c9840000584901c120b241d10b05000d08480009000d00401500351500222110014819961601c0f542c0416528010900d0702003000401440603a04151018201c0c4c1d4206050004203071001080c1e01841c0c7c0140700c55840180d0103d12140c045003402e0280754014000c0e078070b00d00b0b0142000340009000c4010900d0000c1d046030041502010380c807070160600000c0c40d01140d03000785c0d82d442e420320201070700044030305134080c40802e8041101c0c0900041c03580c0c12690168043c000d20b89588039059204d6100f00e07076440d8841e0148005042e06078084501282c030750710070a00c100c81c140c90540003900308480d945007044400503100d0703071070303402d09206040302d00c0817074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 365035557 1250 365034307 365034317
    0x30301141c060c021c050f070317010314300705030d0f0207021c020d06020d06180212130c0501030906060b03070c0c08121209030906070804060305010e0610 69
    0x850004100c1c15500c500021903404007204008040c000c0c2076000524800c80307070307096482c1c6109803074034400420317510010400000c03420403d0020b01d04091b0040d00f00d1621078544241e1001014035100404502030f042510250b032440d42c14842d1004c1000310340500c68a03107030400d0b03601200c582008600043c50300420304c90040003c0c10b20410400344129610305d160660204401101885548001d40089404078021145c034030240c0c0004884c0d413040c071143c82d0f0040102c00502032a51715032001c0d40007000c12051450b12040082a4a005050b032190001d6100c0030050b1240782c6604000c51105000d0200c000205ca11448030000c1802e084e03060090b103000f800d001c240d10140c0e07e4200000d000720b03888482404008014821100d61060220918034060311820351034985900b101c03500c40700ca240e060010810100084045505403160b00c9500c0f40420040d00d08180e85007003c6040b0b0382c89030100321b9480200090134804580c05200701805042c0040c5003518030314080d004641805a03080e0450103005c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 365036807 1250 365035557 365035589
    0x40507020c1c1502180d17040b030402091003030c111c110316080703140a0b10030512090d1b0b040612110307020d0c05100219020c0909030301 63
    0x40d000700220540c400c0c01074500a48201c00703958000c2e5001410340111000b088007030741014482003d0080d00c0c4644022800e0051780c409100c2000444c40f0029012100720021046c6031160050f000080c0000380074000700d00d580c0e8074251042100c02d1100401e9002d00340b0000c0030071710110342c0c03043c0d5407440140d01902001c0d11031500780c0000c6080030540c03201240303505030b40505803c101d00410b8806485034183e003103481c0c03146c1b0640c03541d601c1d20282c06074101e0b90780135540410100d900080c2d0410600703000c00903203140b05641d4a503420642c070111350aa0035440b03038034420010003804009062040d241100894200b4000000140c4000b1001c03a001d4007080100f041e4000c503d00d03040c074820040030081d00c0300e9525551881d002c3e003e00a06041151f0075850401c28035082d0030100103c80c414a45035001d01a04004540103980000c400c00703042e0303514458903e402c80042010b2000f4100701d05140b170040040d10350781400903d00301c0d200c511607000300d43e03a20038407103600400002e882c1542c500401e80c10307000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 365038057 1250 365036807 365036821
    0x40e0a260d0e010b0102010608280b01060309050d05030c0406050c0f0703060f0606030603021302251110020a020a03080c190b040303060e190518030a0806190e01050405 74
    0x1a40049a403540c900800290044800341d1551014441c80700e03100c0284800107019006a00700d030071522a0f24020740002e0790f6030b0440304480312208000844505410003241c0030381c5450300d15480980000002c06e0f503503032805041c0441007128400240f00303460b00c6e91a6103455103549841d4011407013206d0a02c140881c4140350000107100c5076448080e140115aa05541c03824180b010780250f00c40300c901c19192900200358944240180b0060341d80181541516400301c1059078001d44c1700c80c40b845140c0c0400041e0b42c0c81c0010380c01c90110414090320000c1c540c11403440402513200ca4541680065500640043e00141c590102c0c40c0d046a4101c1d04041e1140006c0480504086c5528158503000903022182820480300301780702d0340558042d6030100500d580310b541403415070070140c4422140444098540c0c050281c1c907000b0301d83c00610790039030310b0325000110026891904180c42043c007241c20b40c020055a81080c010f1100154034400d02803401c2454810254240320060190324051a21080090300d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 365039307 1250 365038057 365038103
    0x309120c080a05060612030705120a090e01060806130209101d0a03080315030609060c0904062c07030b0d062f0409060e0408030106031a03060c0406020c040e0a 70
    0x101015000e4400d950010315143c2c4e1680c0f000c8a4079881640954210324003901c00209458209078858028030b8008210701d05e12145070031039440351082108002010818422440c0110700800729901c42e4a11350802c2d00c01c005d19180c491010410b8107206000349540d0780d6600c07000c827030b078003601c0e04156281e00c190b2816280c0c850b01111003541c0205003403d00104100828000354030410013203081d44284031080041507145c02060784c443c3d2041c0d0146002c00c0701d28210f040100003220300204001080d90b03840700360411880307005002107004091300c0c2d8600e480d10b42c10701000b80d10800601d0104420071035440010160014980d020b0052952810460030710b12020782d42404d0702c41d0302042504509016080e100e080d5100340200083c250404500140300e8900441c45c034016940b004019086a003009401c8000300710341d41d4010401c021400c0211090b403003d000709400b0311000c2c5241036885041080103490030ba201204280070364901200315009020206291070040d40c02220041081c1000c400511 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 365040557 1250 365039307 365039309
    0xb0f01090608190c050403060e0d08010b13051003021b0105010f170102040b030a060510170c0306032103070e090c0a0e01050c0708010b1804052d0a110a0807030309120c 74
    0x98511310b03280c1c1a00c807068006002d001102d02c200428042e250940380603588410005a1020101d2038000040c4500007003540680f01d182402c00f09040e81c103a4842c00a505004840554004242d0001c0e00f10710300c1096540c500f260489200003807025516140c0719070107106041c420820322001d80401540644020340441d0010441c504803940ca9080c080c02c803500900e440d2040c103214450181c0228034a034015500900480c1e1145c0c0c00c1c42c1983e8408449580e20f83c4001c0c503869041c0110a1081f0781483c110200311621140920000d0b201e00d00010040c02c180412103c0903c41d000390340030010048614411640080c3c994a810401101c00750300688150050260301900c81c0540100071800010560010741065007c5605004561013581400285801610003030b002d80c100d909122901c41c2c00100c500c000f5040000c2007449000b41242650800c1d0762414122240080f003040083c0519040c2111070251660b28040d0400d0307455943c01610106442c426415454031284401051111102101c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 365041807 1250 365040557 365040601
    0xb0a140a0f0207060e0c0a0e091f020405192907060b03160602100b0d050a020f01052208011a0a03240c020f2802060313080f0307030b0f01090608 64
    0x4400f07015021342072515281b1101c08030740902100c82e00028607160502c3c00d503000b10080c4014215800c02c2c203195047c80b6684900e5214810b4081000141e03030f031102c1041c030841c242d0034000a11510b00300b42c050100c0c010400d05800140ca19410b10301d100261107022180260351007000010341031802c0c8007180c1030a5081c82d408003580d440ca03030b00103034054000c5140a00f4102240042000300c1c0740400b000000708044901410a62106076201c00608141880e000c0528050600b9400c1250006908600107202e4500b12043c00f425070f81004003000034050292195544501c600c400c41500b008074100701601d00c80600818501114608406c40d55042d140e05c4605038407051000b400d4412020703640380b03000c442d00510303071181c00d0603808101040c11000718810b54040a000c0d2806a07a002c010003600040e243c00d00d100d44440c0003400181c2d0b00b40003440b24040c40001c01c0d1320780c0b50520010b42103583d442007142c01000c08040d07030310071aa80a12034105540080c01c088406485542c4034001180c0c21248130 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 365043057 1250 365041807 365041811
    0x9060a050d0b0d051e070b0702090a0f0218150412150204030203100c020c0306060102030d0f0e011506090b040b0d02030a0207050604060519091101050a110115030b0a140a0f020706 79
    0x2002c14404c020032080c0c46049030050b01003079910311700807266071040a0b10482c20102800e0044100528003070310b10580106a032140425405039070101c0b8412a8440c0c000c04c01c400e880f410710a00e641c00c050340d040380700b510541c4a5908003403a244d5800a03200482200403c405103c11200c44c090040d030341510013540d000f6040756820503c103002c1070010000c100030007000d8400c2e01061541c0745800141c0b184260011380c0514106081240c84a01401071201c0b44c80044d42c90785802c20200c20300748960032403405840f5054140f5490300b0070141010450350415076100750208028131020b07880303000300d510681445000607629030b01c0510748802070103604001405801403200788010b03c0019080342e4090041e01d1020030b40c0400c0c1105c07003004c03181010801050b100c40d80d1020b0815601540140002d0b00075420400e0042d60040f0b110341c211001e8403080754014401c440c043c014020710f07030209a400284c090042100f103c107295000a118802041343c0c0d1601d841d02c902101600f0743c3d4054a0400f40e1290301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 365044307 1250 365043057 365043079
    0x604060b120312010f0b09010c060203090708030712030605011803031407020d0605040b130b040f052d100c050706270b0613060e01030b040222020310090209060a050d0b 74
    0xc9400d030f54402c0c80b03001e4820f24600004180d1900c07006c00c44110351016103d01248110950b03a450194200030101600d90203071103400941c1c2c031820300c01020704505c5030040301a032004111000c0e0031102a6000136040140000f41c20168154007444242030ba03405080c0b6184811408002655030310070f10b10001e41220b40d1341500002c0003001d07040540600d1103042d243d04140d588260001141c035130f10f00d000c0c0042e20b054001c100030402d903c01042101e40a031080d1100440101c910f54101c52400102d4405062110f0803a18400c90902031050740c900300381c4084c002c00c0800c1078000c100b8025400080c054980e1507154109100c0c481c14820b00c160f140c080d1548141e41f00307041042c10444115510b42c010041081c50100341d600c00d12803c419511694010b41003a421a01e9500d215400100100d80080d96041400082e000041450250b02d02c0ca810250b03072450100514140e80070164041e00c14140144003000069032079105940000071030703240140c0c84009510320000500203070303a200c0d41c02c070f084024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 365045557 1250 365044307 365044327
    0x7060c230102070b01060302130e0c090315160c0c0b03090f0d02210c21090a030c03030e240703030603060908030717070c14210d1a030604060b1203 65
    0x5071416038004c40001d4020380e40d0350b42c15001da106d5415181d03008401d4440900110120340700e07058201c01c0c07144040d41040310300b40110f4507005007400a2001003480e01d04200b140301c01d61000348800380d400d01d4a1040c0d620169900044901d550254140c0c509020001a240700d070200015000b071004039084900e11200500c01948603d207900c0d500b0305400400424101640745002200d81c8140902c1c010103440340b08111140d44403070b41442001c4603007010071908080f070b51980d004002550159020021062035464040c006402801c0b038140542e180c01224082209038400145901d02c00245683e42c49140b481c4c00c0b40200010381000303044a2038070b041d80017440a0b070382c0954031400c2c140e122000140007508140e81c10401c11a210800180c94400c450b001540111105403401207080444541e5a5160080e10b00d4890041400303142020214841001c1035042c000d07560700d01d0001581c035400f00b00c20001f094541c01c3c003d0000d004180c80f41c4403c0060b85a202901d0708921000301600d131519007400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 365046807 1250 365045557 365045561
    0x60f0d080310050a03050309040504081c0c0f0806010c03080910020706020a030506120601031506080f0c030d05040e0606030408040305070f060314010b071b120503070b01080f07060c2301 82
    0x2d9080540200d1a10000c00e05050020140058a0704080118203244929003007001400d4020011910101d00f4001c425540403450b84030310413481624004200250013140c0100300c00311980500b1300300a1405c05204250760003081c02070110742c2500d03214555a8606031740301d1070003184910602c0154800a10282403081d1a400340000003102c2d0703030030f00140d1282e1b8100702402451b1182c0c801e40d5000040100002044030b0300440380d07a00522401300f1030664031071005080c43c8040e040c40041e0340100008241500c2d0a000c1d10100740e9442c1080c4d41400d04007014000110300080001e03000310000404141800fa42d90103441c0150342c0141211241903d5002c8207a05002a1090001080c00e1203a550410340040c01a54103845040c0c11590030320600ba100e41544499500ea001d050b150340f100d01143c41c0038000e1950311600e00890003140e555002c0d16001150001c164004001500704809210190202184007070440b240c514124240c02c2c203506000049030710030038986840a160039071418443c407042d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 365048057 1250 365046807 365046811
    0x2901210b0f03030403020102060f06030a060c120f021c110c0a1b0e0c0a03051302040614120d050714010f0624020c0303190912030c020a0909031205060f0d0803 70
    0x5a510300003070100d480a02d82c2d20702403400000d016800031000652030880313213001c140e0f000c90020115400b05e070054945101722106a49003c00149140081007091416409500e00b03101d5640f40851909400f002c0034001090620280343c3c8035500c4890780e00c462003994007640c03030300610714060b03450042441c50494019840034502c02c001002c800000505884040b10b110310403000c0b907640301d15000751008110010a0024001000d240007544c901001da2168130590020785409a118040641218100562951200b10340b40b481d51000ca05140360aa00606649800380d02000c0440c01c100010300140c058203084000101c500e103050f00c00140510351030809a00c0750040b890030300c551442d00b60100d0715080942c140e660183d01c10403032000c500300849218644030415180005170181c640402c2e80700350718005420340016034208034400540c544a10790f00002c03d420841008114400c0d9009481110059141c0240a55542c0050100c1d116008216000b810041c021030610400e883c0c20041170b001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 365049307 1250 365048057 365048059
    0x902040212160f05070201030c12050a0614030a020a060f0912060207021206091e100203091c1b03050702120307051b01210e031c06050103050a2901210b 67
    0x80c80c0d01d1940d02a0180480303035411811136884500d46070031500150040c0045000300801c102d02c0450300303541c3c45103030310076280034034403480b0301260742e600d0052442051611070300d40398466080109428010380e60300c2c80365012951a4203000407103030586441a0f4510401c0e9004510341e001c0c05400b40100301c010f900078003140340308948001c80310441069041d0f8500f0110b40e020019401288882c14031100800c0003107100540c4012103507010b02d0484a42e083e44c00686101400d80c3c4084210040c426115428030495083d502d03229090384619040301030080b05100d00a410300400103508015511480c1114100d1094001100e540d100300e4541241c3e10001d80391721000c0b00038403035003800c400d612131003290004900309101103445010110b00e15000b4001e01c401da4220f4801003080030500b181c02005c18590b125007035400a0914030340800074007540c03001001c1c080c2d4507141106145061080842c552401106801194a90f01000380166009001e14425401858140112014440d00742e007241424002c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 365050557 1250 365049307 365049331
    0x5041e0b0705010207150506100e12010614310c02161415093f03070b0106030b060316030f050a1515050a1d0604030803011401020a03050f0d0902040212 67
    0x3070310b00a104200c0d1003c6c3d50950b07001001c11001203901c0d00c40c03c0740240411008121816542c00e244119084370951f078846444d1071100c0c290130301d00d4038010121a07a0f407401100540c031030804529040c08074170b00380c5480007005079032851025285403080004180c0001189090001181c0f55180c031032044846049040c45a03030b540740e0140d0650012819100d55560240c0241c4404448000c600f080414016501c5055800300d007a50b0503540b02400e5400102c09000007459a48182d1f043c82c48092205030020002d050078851400c0040e2140003c40c2d9210381d142021030102c4612640071805000625101c00c13040d4106030a00649403130755400b048480c81003d0003d201c90f41e690400180c0d0761205894200400d40a0081800490248110f4100280044864080c2c2c1c0b01c0b4400040540d041900241e410741e401200500c900f11401c40703070310001c507001d000510040b1007941d8010f01c688aa5644000040360101c0d140d40c076032515400011140c0d600400564030781c062680d4103c2000d00459040c2e80e555 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 365051807 1250 365050557 365050583
    0x11103060f0301060f050609010e060f031e100605030a02070b010b030a151503020c0a0f121b23071a090306070c0f0803040f1407030314090105041e0b0705010207 71
    0x450144142003c070395400d00b174a08164034003810482c86400102550f81481901503441d0300c213594032001030010501030502e5035141d013480b034400c4502c0d0301d5030150102c19070b03000710606c8801d504203008441294058540305640e030342d074882d02c10084d00034a00001d25208a403800800d22007960000b95108040c510380801204034204c204d903040190170710404090355001089a01c4441c800d4004041c0d03c96480304132100445070380d40e02104258100340075104081143c007164007999000d090541c4c1340000540070712100c10035445000c0d0720402e01c3c4250f0304010190b2003800c0c42c43c80503c20100145401551200020790740303500611140e1003d590148a0702403c000103100390300640f05c0401e4603401c050004082412503540940320341c00a04195010b070a80c692400024085840114440c080f040241c81082c2c99844c0143c040c03442c07a04c400000784000e002c00001e82c2d80c00815141190401546000102c040800c2075009183c142c00403440c5410000c0d2500030b000c0150014416203200e0400d001400e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 365053057 1250 365051807 365051809
    0x903010c0207080c06070819020f0316030e04020a08070309020f15030906011a041205280507060509030a0605041b170f0606150703090b030a09111f0807050408011103060f 75
    0x2403282c04402415000140007007102880c07804608d40103400c45004903080401e018001710f1454020550340f05c40c04030381010840406502c00400d00c0c00c41e40507541035060400548001d04801c0c0c005160b030041681e100218819035981c42d00b84175566101602c2c14543d140f2000f034032031469108071002c10f0140b040400004010a0100e07040d140c03a00b454815a05003410a40d41040e1620400c005495a104030500c06245501420282d01e41011000c2429402c21a615000b410503601b6844003046c4003051100c2000c527200411035004841c2c0c0000c2c00206555140f6081e40c541c502108040c090040c85a4042144000001e41515003000a01200d009140180c0300f180c1c2e808044400d036030001c030504000b0645140d40c801070041c1d644682898940030303840341102000d40e081187c0d0140076036100c0d0800c009100d0448401c0c0181d0f40281c03410200010780c8550400a26022014041000020400125894400d0003600e0140040344001e00c10705141e8140c0d00582e8105171a01c0d40b240302c0141f41c864071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 365054307 1250 365053057 365053069
    0x14032203050718020705030310080f01110406030f020c0d020313121a0a1b030c0f0302070f11010908030705100c2c0109030f150b06030f0112080903010c0207080c 71
    0x1120341c448020802039003000105084050a84248054280c09000420010768140040d62103580c503122502c04007454401528541682c0c5684480725901d044104910490804100c80c04d40301181004908021000c541900030f01c201c88400c5024016210301d0303c0700039408002005901490079408420640710403510914004002c0c008101481c0d5907190360042005a50255215058000c000744c080c8000d00c148104508040c3c42d0000aa6100c4c0c000d01a40e402441d01d00300c020380c1b40b50850030024a951001d0681c024144003910110200100f58516841801c1c1c840c0a000c00c04150b80e120b46091034501d40c3c1709020002c0300c81c1039040c0012566a144580210440300708540e0001c608901d804c89007401d140d0b1141056410001002004808641b044065803031081c490311b1a40ca07004036030362800045400114020340b10300e0040042c007502400250400b410340c2c07000c040e82c3d40f11401d54940f0200030f00c0748000c01c40c2c140d400d06441040b03150700814601c0440344c0d26026159012407400030410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 365055557 1250 365054307 365054309
    0x7050409091e03080103050708010c0c06020d0b0604120209060f010206162f0c0d0c0303120617030a11120d1107051204141008040204090f140322 64
    0x554140400c00c035400c0c5640140c07903094014a04030b07100300801e5500403482a414002500400c00c10740041081180401034403008140200007000003aa00002c02040e000e08072201420b02900420f0060356003680d64002d1700310b00c1c0018442e95545a032500344804c5214110003c0c1e04c03030359403c0000345943c10b081420180c18201640541100c1d03486101fa800181c0b85c50400208009403080c2e820074000084c501e00381084564007018642e45042c0c4111482d0500c5011541c1c003490402c081600043c0445c504078060b83ea050400c001e202c006a0303c10001441d40e60f0050440c4080e4822424500d20b01000403da5611141d68030306840700110b03d0b240e958188003040101e030050801c0b01c43d400c800a58071941402c0210405c50389400d800b616028980040c101c02c0c01c120700b400150410034000303081e440007044841075038000001c00003100060318020004002a01440d1110724520805c14088003190115910001c03600e030070402108416076a420501c0003441da50030038440054461100581d0b00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 365056807 1250 365055557 365055571
    0x150106021b130e011d28020102030703081f1d070905010518010e03030c010c0801080604051507030b130c0207141f020a06052a2d040b13030201030b030303 68
    0x440c0151510202c4008041d076104601d43c41d540e0314400f11010121205200424400c0e6004101400604018599002e5040343c01e0711003031150065100140d17000300980d00440c0e050704100c0415074a2820805480401e40904481a00c1c000e40220340f6480c0300c403002092504880b200d901c40d0b5076030202601d56052902866011880a001f450b0383c00800e6190602940010300d0899000b251410210746541c101062201180c0d446040040003141d002c14481e0041480c10010207060626884060b11540b20f1112000140c0c8404009102c15000340c002c03941c1c1c0180a03044445a0340e8040b00b290043c0103000c00d980050045d140005146c6c2c0c0441c0c0d2045884000900c14a26440c00303440210030340c4030303520080d02580200041d030004104144034040c071130410119a180c07168600c119000b40042c00c941200d130001e900340325880b4241000020340188149028101248c6c2032801140347c03140c0520340c0482c03681c250004e0000024070048081c641100d100b0307203050041c0346005040544a0008849003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 365058057 1250 365056807 365056819
    0x203120a021806090303070209130203061b0a2d0804030905120705121603080913090809010f02120d0f0f020901051c0b0604080105041a011d040c08150106021b 70
    0x60348500d010f00c010040c0c0700300201207a02d42100313540801d804400031500a200031600c2c2d54804203506041c003d09911100c6100624480242c02d54200010301604a20808000b06911600c5a101542e1030503a041d02050200f51024a5074610040c040700003120f08800040c003e400005140c2005111070b01550319500152030505e0030542401041080c480d0928464442e1140103d07403c00c41d49401c002450195610382d980b6458031003800040324074000000e41c002d1401c4035410109054100780d484013078003413138805599080848100e182c42140c041c0f86100686c0040c0040b440d64450340254640c0c2c4c0c070400e050045801d00520076040b400303662605800b20300200401101c0d44804c442800c8804208a8001461140c000c0820100d4210f82c11a8000369544c00c24003041c48190130703151001882103140d1026540c1407250400700e03014981001e07000c002c044004030301000010040d80c07001d82480c1d01200c4114050ba1441400081c0030302c44c0101600074605c110421240383c0101d00c0c1203031009424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 365059307 1250 365058057 365058097
    0x6020f0a020f010b1302030a0209120d030c020a030504090f14160305100f03120201060f060504031e050709111204060b1201020a0914010309060e011d070f090203040c0f03030203120a02 81
    0x405d0020f507000410710b44a07940e00f0413400071166111025034200c5159400104070140300650042c0841d0105a203074400d41d8031203415000003075408000c540aa690380e00c004603d04140d20400c1020b4800c0b581400d0301d45440208100d90181083c440300200051540c1c00c0c05a5282c810b1016144509070056504c802c052070002d00100c0c49030342c841e10030086a03200014400380c0c1c030010740301084416002940000d2000408209110b880040080b090b0f5940990900420b090750710315940300c40c1885806042c07034035041c1c140800c2d585141610301144101ca80c40149261501c7c004008200d09003100f44a141c4010788c0e002c40344014800c2d51078003611621190100c5080503d8080c00e202c03001003883c101034480d050034000426034003030441224122000800d00da01c0c3c0c814460180c00c600701c01c021007580000e40400c076550f00803a01320200c61680d2401a543c3e122800c10101c24512078201d01820300e0a01000010598004003e1422011a505c80e03541c50b103c00e107452003030b44244c0841030001c0e00b210381c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 365060557 1250 365059307 365059339
    0x10c0507020303070f0c030b010806010303090b130e0a180503250b0a110c0312011502010b060d150503030a020303070e040c0804110a2612091e0a0306020f0a020f010b 73
    0x4a120281d000783c850340c00c101e0b6a03507114023045200360011400c0742c1205c1c00400130550813142880203060082071060801c0c269807200e50700010746104848a5000b80000b040003070841e5444070441c0c14080c0180401c0d415541440350b9603501c8003481c02100903140b84500f0025001c0d20495103141c0d8403070900b20841d06c0740d451010203010300c0c03010b03805040420400b140600e001040106010801282000c4585d032428002540c6050b03184403010942e41404082065a0381b420215554540070550001e82d42c10741c0182000456034517041940c1520000682c01d890750b40000c01b442c0319005607036500226041320b00512080d070f10316041600114009802140000c1e00700031100824550240090142603552441c80e15640d5040710310003400395800e050701c8964107040c1310365041c1d910359400e2149803030404408a00b46000201400d00500c041004a0000781c1c0e0701a800d03001140c204c1d00641d01c8a0404441601703640c031054a18026100d14108541034076418001d5980050004041524001c0303248 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 365061807 1250 365060557 365060573
    0xa03080a0207110d11091f17071203080a060918020405070c080a0309030e090408030c0309010f0221100f050118030606241d101b080c010c050702030307 67
    0x2c40704580360007802e04603200c60340b102e0585203400c0340200c14140c500c0c140c0e882442040c1d0303005044403c032600c07407106d0b040c000349001502e2401c40300d03000d1111180426140c0d11a091070541c0d00300c1144a904807904200f03143c2d21a0703803240030b47c0d10b41204000080d5198290811100001300d1250107001e1440450098a000d9004036032107074150401c42c0d0310010303540c0d800c80d56510554140c4040b80d42c407054641410340c4080c405d440c003102a41e41e0740f150708058079104100c2c040100f0b6062464400030000e261507100b90420b2005e0070840c5425921807900c2c81060441100b0074402e020203500c81130002d25845e00b81d144610460b004031154800c080d04080045903001c411302070b151161804944004001400c0f0312400c4010702920f22210001a9906043e0500c20007541c4401c04003c1c0ca03000303414526003402c010410905085035200408003419906541f101001203514080601d10710900e41804112801028000b0215000700000445c84406a69500500304040c0d0560700910001000076050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 365063057 1250 365061807 365061817
    0x6180b0402120c340b06010c0c26011505040b0a180e0c030d0f0e010314190b01170103021e0915010e1804060504170d0b10020a03080a02 60
    0xd0009450312400740544000c00038151815114031200241101c030490181505950341248000d000c0d003000311110821110301c00c500c1014040c9034240010403016070088490a04443e401190780c050540c1c2c0d540b800b40741c00c18a2040808100c90150404000c407c184107881c442071449000162280c14203040c0402010790f550030350b8020100800200361140540750040944400d850040f900802410000303042441c0552100c0c06544601e8116400a80080c5129020005450021810228840100d001d06070942c482d040c03444081c002c2c081c5030b03400c50107003007081800f00605000b0110100011105d43c200c16003c1107803802721400500062038158000940c0c441f4050b44074010641520020700c0111066a45110143d00c05001c480c1650308680741745082c0c441101c0348000183d040220410b50600100002d092a0351075000500300400142c004402e200c1da0320306192102e141c42807e80040a203400c045200f540040c840c000142d02c00901d0540040d810358619071652141442c0c0740194100f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 365064307 1250 365063057 365063059
    0x6040b071803081c02090d15020708030708070e01020708100203040804031e210c0f020a080105010f0303080a02030c09270f01030b07032702150c03040602070906180b 73
    0x10490100085050701c08030726001d140200d01c210342e910100800c49000b0080001048181e41c01072001d0400d40d80e5082e508181d0581180c04a40c1d610110120743c0b009110741000141108004024004103543c01040796200d8041616002c00195158006903aa540075100b000e00540c0100450b03124072840d03401031038002d03115800301410251207581d01c004e000039803500511048100e071092028000701d094840d141340d1070600a4649250030350001481c910f410a406000e07801c04092800442d220308801c10000c01c003e00003004256150a141d07654842a48020307070000d001c6e000856281500c1c9c0c03080368001c680c000c04c51480e061841c014082404020707400e14660000d4641c1e00e002d08a5492a554071075905000e0345a040d40c11480c01061481e40030f001031003014074103400c000400c03c103d0b941003e107030542d003514140003605200181c040201c1e060340d0b4002c49004a58210305150002c0500144c904a800380c4440988804541003120741d24456208501000d9502000c130004603404000e48003c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 365065557 1250 365064307 365064317
    0x90f010611070f0e0f01120512031302030610060f020708190503040b04080604140c0306060402090418061b14191125090b0603040b06010207240201110c06040b07 71
    0x6610020034000200c6030340080c14a041403000c1002c01a00001c1460140a50a46c405222185900c5055592802270b20821201c000000461031006064242c4810941e008044404c2440d1280c8800107011580c400c407008250316103e80c1c10018008030301203080c3d500800090810540000402000904640c01a07401c1d00081201180c5144440e0051000d4072040d0014155424645019941d21503101034204154101440d642107503540486d2040d000f9504035800350b121a90140024001e0105c41e400b0020700740703009040c204200a5820502802c10205c84103506400190f100f40d0350640e010300180b419500800000300880030a04504424903031510340070b00f09040311200340e80b9000f80171419a607644402d54004040a280d41048405409060014010002d9034070124a960001901c0203100341b0b510710002e8240d910810011000313141401d07031a240540c8003819009120020b401101c0154206800343c0003118501d070071144423484c55001044140d0360f80d1101c0e8a00c0102a03c8103003088 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 365066807 1250 365065557 365065559
    0x12020f120a0c0e0714030601030b0a0f0602012c0304090906151d160507060e011b09080606030601051003050405011b02010e0c0f030c010804030210140114090f01061107 74
    0x1504100e01c020061040c685402e20303d04000d0688540c0200a140004105030746400c840701c41802c0d030940e5040714080c00d0214811414400003908108590408541000c244400085456054100c9081144107200341001c0d4040d41071b030b400d00c1110180364000c2c03540c03080104201150007588011045402500009000303000c00f400c0901840c1960b106451221a000040d1014501d41ca44250400b440e40241c90042084c10307401391860280c048080c2c1070a1f6142447c25584100303400c0008550151402203141900f00c5401411003036240c05811010b20030480010094280011700320306a9400800550780030408200403806070800401c125555529480180151016408030300762000e07582e0000300c0c45107400686541741c5650407881500c111036041120055490202c0c11940c0f0450a11f8442c1d0b40390384038101a861f00c42241d240c842c40c6850321504182d80803c00d5080380c140c4036070344c01c418404e1000701c00b0880410016070301ca51031503441d00f004100c058040c510360290120a10190340c1e103d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 365068057 1250 365066807 365066839
    0x30203010908030612060402100e1f020a031407080702060702060c1b031911010c2d0b09030a0806040b01030e010e030304020a080d0503071407050f010c090501030612020f 75
    0x5541ca000381242d440300040306000311460950b00b507043d06000d807001040c40d4540b6800180e01800300030360841c03c2c0070021948600783d0300e030b050000580b070410000e101c00c9411000c02c020342d140004441580025a6005092031303010104044a03425900306003901d0802445400300413855000b040c0803644060304100c9031180c00424000300b200b50b8001c0390079803402d40e40d0406160a20350290160746d00b801c0a44644000543d00311016010300c4420304e08040d0310035041c6048007244640e0001ea040242d20664001340c0840d4400c80228080e21410300901c46032507903d04d00b9540d00503501c211010480c200000790b4182810303840340c3c00580c1d05140100c0c079451100c550a01319030481480c00c105030400020042942000c0da5480c009121100040c8903103540c0000c018040d02004d407600c000c2081e24041200c0000445c4142d8100603003150a445600a4410303602d4001c044001161021a0b40303004001825802031040794219600f1103c01003a8106540c00c0081c48040c041c22a54849000d4001e8260 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 365069307 1250 365068057 365068061
    0xd03020f0706180303050603071d040305040f0305030307090605190e03071503020304060c0e151e030a05040606060306230612040803071209082a0d09050a05040603031707030603020301 81
    0x3c60351050f80c4002050880e410010103441000b01501e001e54010b0710b0810440950111035210f06c4010340e180042501d813890101c8881c400c5078004d450210703075001c000c0180310000c40110b0003809103440d06c0306155601c80041e9150700541040044810007016002c001d0f901884940b220044024243d81216495140c080c10341d0801d4401c8900023a804020841017122a102c2e59480c0e420380d0030040421020030b00016201202511a103202400105041201c20000282d028100b010054066142d141c0f03000b415009001c02c9030162155402c0c41c5002841ca402441201c0541c0e0005c9090414011340c0309400454400503440903401013402c000b08140800c4020500d07005a209108103070362410044801032507044502c0d40321040e140303001c4482c40016028001c540440c11101d0b01713010038111a10803101020b840e426042020b0188400e4005007a40c800303502030940c1e400b12180b0220035102c00c1488100d415500000f0f01103005259501000c0340007003102c43e808240d42ca4042107503516036010070300f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 365070557 1250 365069307 365069321
    0xc0306020c0307050c060c06061c061a0f0103110f0c030c060a0603031713061119020c100804020607080f07081204060b09090c060319090f02030f030c0d03020f0706 72
    0x210b82021550000704481400b240302c5840003201c110782000c020400007070f2909400f61040f0321480140509205000c01d030b83d46100199007005007040380308401580c10703005404440e08584100d90146140340150b00903c1905506903801d00c8080c10000d00001d0702c400307136011420a40007131001780000ca42107801040442d2007005038038800b14115146140240c4152902440a035144440408000c560340000c1c6142c2c030b011713400000c04104100c0b03080400015100d80c48840700301c0c8495000d10740d201a000948130028600035241c0300c15050380f80c40221500c91042d580254090700c1040420049020107020b46460b82c00d61134894501207050381c401c64258000660408140400c03c10042407240c144182d1121600a40d454040303807400c204042e07203075009060350a100755000700200781c41c2e0f20704200344d80f42105114810810926541452180d0b040e405004074030900c41c4d00c08101c2e0b084000f00944035984060001009000c00c0c159065020f074026242e1034640500900000010842d5409011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 365071807 1250 365070557 365070577
    0x8010608061219020411031303140d02034803040303061d09060106030e1906060504020c03030a1107020907032307050d0b03070b0a0804020a050a1d06030706090506070c030602 77
    0x2040f004860f205002c2998904103401100c05818810441914218031420000035810324003c0b8401c4d8850000d00b41c28001c51a100780017620200c10850b1303d00084000240b040c4200d0402258110314001e2070b40741106100c40302400203452f0004030469001400a903810921906000c580f45448101c060401c0072203003122041d02e2402402c0c02185082800b5541c00f4065928081c44007000c0303103c90a41da0081444982c6c04509400d500c1804e00440b41c1c01407010700360040c01036584000c0d881c28169203401c1556200102880c0124450366040a0303c1200ca102da4040e01128165171809410f400a2542c200d01c4c09105041018400840c03400c858800c0c49208207460b401e03264086d4030b0301003084401041059000381e00c000f07000d00084500c1c406844400e90380c0e1401180903950b40c4081004018181e020f16080200c81e103020070122046401d06903450301c110240800303a501e034002c042d0340d5400380c840e940124205030b0080c085c0741003810050086600845002c03080c540d40b6601c00f0100c0e8014a202 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 365073057 1250 365071807 365071843
    0xb0714010b042309060402010c020904060b0a060c1a0601091809050a0f03031409121612020c031501030b01030809030102090a080106050a0b0c1c02190b071e080106080612 75
    0x71040b4140700c40d0115000340c180130041c1943d252560029049c000d01030030191280702d0b100700080800c40150016250008098010454140d90310005070601c8440c0800700c030224004580341003104d009541843c8281c805958207000300e4513082d4542c041448600100c02c0c6030740c4404406010440411081090710312644101c1514030441c1402801c0300d01030b181c01e0310654194401d10840030400100c03c500300944100f05a5030395150424000705c17211440340101441030351b22401904503008141000c4040058086d102d0400c840400c9205072082400002d00f9000e01c1001840070681400280c0441203000d0001850b02d49007800003002c07105168080c1e01030740c0d101c200c248018184000300c2402002c0010b84142000e98885000c0e8851303010112400441504042c4075200714801c02072010a8582a038845140308901d00707264503011000c480d0380011809042c08080740c05480d0b03004094000883d038800695900f030000446030758901820b450307806940c96411011700c8009100044440b100040031b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 365074307 1250 365073057 365073101
    0xa11030f0724020a11011803021903050d110a0f02060d240503010b090a050709050d05030408060601050c0624060c0609060702032a0102071e1406010b0714010b04 71
    0x82c034500070485a002021900040810400200c0148541c408544242000e800c0005c5800c00408030001c10742c8065480101c0c0428108140707108a855400d4901420030385a4040803030606645000380c40800c0f80007584250014004280e0490b8681e030040d20092a8030301d0328400203660390036541808419140500b004c403600c503c07160340c0e264040c01444280c1c001e0098400003000106000d500610241e640703511500052505441080f41c500540740007840204142a507040190340d0b0340103400344200c20b01c41d00303010503c9580544141c4010b18000300041c101d41c0d0328150741415641544040c01ca100c02905007010f410343d60080038140c60030181d0010f00c00c501c0c3c1100486c0c03421001401680c1550002c011599004102103040441040380d12582109040a400d5240c028451544041e01803840040080c03481d06464180d502041d015002064000b200c0201882d00c411003845054881c000401a620014405103a2107084039800301c000202c2e201d01c0e102103001c0d1072a2900805401540e00c2e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 365075557 1250 365074307 365074349
    0x50901020a09061b1511210705040e0a020901030f1a0102011503110d050f07090e060a060b0d15050d030306210812090a0609050d02010c0206090a11030f07 68
    0x2c01e900040840c0e01d0106084440080342294000501c070014081009075500c442d03100b100f0350416958080d44241803130f0b0341c81e0208400b000710b00c1a01d07000c0c0c0c0c0c8404e8110104128030700c14815107095500141500c40640c035901c41400080d484194160705041c2c86894010f203c04c51403140d81e024000308001c00050004d0788000a0841e402ca0f02d12603031030044070000303101050040c0490001e00e4020346452030ba500f01818107074a001601094504107100710f490102e101507143c3c1284540d0b42c021411102d2a441d10409802502c1d92805043c11034003003408088803135882504a0901540000000000c1903100c0c80031411442d14000d06801003a262842005402051a20081c6100307003041c0203020241c140d80e42491510940100100c0b03928503030049494054188410126140d0114081110711054a455030321034071290b03000c60265281141c008005400410090310420070540540400c10f207070b641300407007013041c00802900f512a00404070f640700301c10881500600866850340242d214548 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 365076807 1250 365075557 365075567
    0x609060501090810090302150c0405041b080f06010c050601030804050f0d03050405040b130e011a180402090c04030c06091a04060f08041e0b04022e11010609050901020a 74
    0x240c41a81045000c0c9010415403030f0100b90700103015101c45000c250f064150800301d00d02004944c1d007658038110350085c040c001d40480010320841e181a40c003846020b25200740c00305680b4048500001158801001584013541c0719003040c0d0000307050410302c13143d04141c2c9034246800c80981048031a010b0009080c4528600310a103160984000c0350f80380050304460342c2c010501d0280e0302c5820301031500d034610759238240d070b0700300c429070140d200c06004001011a03001d000d4003820398040d04800e890002540d810682c24410103181004591003080c15041d122642404442a03006040313081c401014400400001c08025002000f0907507540e030981001d061800b101000c00c0302c0f29107a41b410b0002c0008228454000036420a06411030811441d20741d034600700081d966903900d1000d106a240d9010000410500d406900c0c0a0350098904080c0d151800c07500c411484c0158031222015a02031201c046400e04c5959003a58248540300017041c0750307035035107454000d845090b56400d0043c2d4022070359091056104c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 365078057 1250 365076807 365076809
    0x20c0a0b100503030705100b030102072405070e030c01050702060d05130b071d1314100e060d170a0201060306060617091204060c0305040b0d1b0c02010e04020306010c1203060906 78
    0xb03e002d03616000e11a502c0990703441c248100c10b40c0164031180800d50503a030070b5069502c1d07180c008840318415040c0842c581c4110100030780b012034292400d004588a00d108448056603c90301034001e150140702280107544030742092500302e0b480001040099210051402803500030185491040b041b815140b8042e080381c0390042c11a03040017a4030301c400300141c0e10b20a000c0d08400b0207841e0311151181554001010708201c01c2c100480ca07000300e0138003080c070641c00100c100f1a0a40214401c0903110385080140015001101600d109502003021000c112400c004140d401014000012501c0d500d5440c01d0540e201544401c003c41e81034007141c01480031005481d07612040c6980a40b0301c01d8040b241100543c01240904400c00c03010359a6201003500440c05c80c0e000c2c00e0509a1580c0700c5448a43d0100905000300f4084040c4000020b60207206000c1c2c0a40c4040ba0b50584440c19512800c0701030000030340008081a042041040003040031984010307180035236202d40d07078011515900340310b0058182d03452 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 365079307 1250 365078057 365078059
    0xf090510081903030506010c1a0105010e041406150c07140405070507020a0b090a0306060e100602030f04030b04060902041a01081602061311101d0a1404050a020c0a0b1005 75
    0x40280c0030300c1c03948102e40b59107005605007400030301520f40400480d040444038100034940c0e04440560511003100b402040d04030f1380700340d071080b00c210307145018001603c00700d04120301192405c002064071441c15100f0f5103c8a02541d810604103403d44000c10b24202003640b04114103110150040d01c1805e20303000e603586c41180350902d9450710584d64040703100b1400500c50840c81d0300c0301003002103043e601c04401c10000c64200b00e0074089651920703c03e00c00c03c102601c03001d14500d03040c07038002503490000c13003511100080c58001e1401c003451500c030300304900002001111007940d945000e43c01a0303924424883c681c12016090719031118000000f4100e03000142510503440d202040200c1d00c59400a141036124000d50609442d50145141000e0150410b0400c242e00c815100b101d1070003240c0c400003618000c0c4469018215022540c0c050003003101c11801080c00b020080b03200a001400c1a800081d00210384080051410186000d01401c0031001c405c2150145c1d0b2040a01100c3c0c001030a4410103000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 365080557 1250 365079307 365079313
    0x102010c170a0914031803070e07050d0b060f040b03180705030a03110309031f05010e06010f030b12010f0b03070b03011202010f1701030c06020d0806061e040f09051008 74
    0x75940c0152080802040350199075155941d1408000340f00150f041003003003150807207458440340a00400403400780c10030031b80248110100007070003400c08010503008640c29107a0300d103400368246240010700001035000c1e400402c10410712501d050760800400c003e103000420a0b440e4203001041d042d04d1000902403142070341c81180148210b68001c01e424040f00d90505040b440c420040c1c458030300f1030041401c41680360280c1c0030030081c40300e21011010f4801c08a072408001c5a1b8036110f074000190000e498107400079054100154a103400396102c84100c1c000144000d40f002003040001d030035110102003003d8040d84446044451381010805003000d400c286134001e04541c105540e42401803c8000083e041010401510248900640c890f14040c040408890090345c1c5a040c00141016103104031b40c014400c50100740003051203141c1e1700c1c5c06003100803c0580f404014030360000c0c0800d6024060f600c140d20402002403050b9011705440f0040c41540000b080034030717140c0d01d0046000d20300d0b40942c0c60340d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 365081807 1250 365080557 365080577
    0x1150c03020616030617070512032b0212010803090a270b0d0b070f0e040c09031205040e040c060e0604030b061314100f0602031611040e0313050102010c 67
    0xe4000c5031440e40700041804481600070381843c00c501908080c1d0100002d95030f03513a100c4880620108486065850646024541229040c1030301e80c1e80c81103507000025001041c0c81880d0781c02c01c000d88200f8003501d0600250030128031707002014003030f902a40510076592000903550454101000441c1c020840305100c1040c020b811004c2c1429203408004003801c165440c80d5881e5140d079030030010132107182c01240d130242078544004090f103045000320700071780403a080f028843c406250a0207910740003903140d56a0740d0268915540d81840c465503a0510083c80414023000c903201682c4036466200c1e502503210501094030340355000e407911a03050f15407030040104000600c0481c40d20881c43da08540241c41140c0c26038100400301000704002004500c00700344203000e11070f07401e2040f8181001e0300c050003400494296201801c0e40e41c0c2c401c03802030300403091084078004040341031880d0754220814040c00120301000c208079080d040d94010000801a621044e0052056503824800d406080c0100d0406025031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 365083057 1250 365081807 365081813
    0x105040b090409020a18050a15030f02041e0e070f140607080c01020d0906091a0105010c060b27070314011202060a0903080f090f06030402091f030c0e01150c 69
    0xe8440c41060034001c41c0c81d03201d100215112107000ca0001c1c211000035030b11200f00070302d1070320103444242e503000d010074140078070800f00142801c1010212540705008102c40003042d42030001416545d248030b11030303420700710398840d898180c1d004406036510240083c2c01918200212842041c0c20343e00309040c0340502415501c81c82c0c6074281104d070900e400440858480e601410441c0c064402d070203c0038602c0b0305050000741004010b4001c0d90407203201d0300941c04002c2d4070017440c0f0807501091065a00003200f041d10074000c950640e0200c0071841d00030f0910221240c00d03400184aa55842020704402c19640c004c0110181e81803040100c03084080700801c3d59035141074030f28061113905141c0a44a03100015001d070819004000040046901c54030060700c641c40d031902408540c000c4210b81d1300540803091409801e140c820304503031003294000c0001405840f8280640001c1b00c26192601072150080307404408201220b40200080c0011807020343da40d03051281629030041c4541800c81402300c040c481c1000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 365084307 1250 365083057 365083079
    0x80901050f010b030a091a0919020306010506160204020406171303051b0c09090f0c2e17090d1d0d080a050d14040501060f0b0f0711090a05010501020c010504 69
    0x4507103000041c103440fa12505c0c01c480041c80202e400902d803400d11400300303145002c4840220300c2160900d09986096868450001c600b600038039009516030480c1c0014403a502c3c014010701040c004016003a6107001180e03010400302d0740560040000702780c840b00c004100c014504d00040d84a000d80100500c149400e07903001e040ba001d074080042d042c040c00c040e841d030300303003020000b445880e02e0003090408641000f001c50380d01d402e2548104107082c050070208050508100c940c40d2110907202000005050000301410340c22800702c460034082156140e40f1600006081c00210302030103418015104c461100c1d0006800c2c82214078102c241401032030b000d00300655456038100c4031590400022a60b4440d442d0040303400d07108080c50b10340000c0c03500540031a5401c55005041c483c510500080004c2c42c1c0381c41070580c09075500e10484005d00c00c2080070f6402e08807108043c2c241c0d140704418840c83c5071149000250340440427954002040c0d62000100919a41002348800b180703003c0c2051880d10f0b080c140c038801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 365085557 1250 365084307 365084309
    0x5061c0209070302090d0320072409080d09140d05060f18032109060c070f050a0b0c071a100e0417130612060b0d090201030f05070f080901050f01 64
    0x100c100c2900340002c1c50039009030112011017400600308410b21949140180a111802c001c8500100303604001d00c248101c00a6040f01b40c9609044202403860450020451156510740d01c000300601c015000480b900d0030800941450030300e8481c80201424030304d801044121280380b0070310a5402a4201005c16000305401c0e8000c142c00015071000d566129001c45038500451107480d240c0b0000030401c60004003a08500005518202c41101a03101c1304003d0342e8920054800c480d0415040181e00c00180c0d2054801510700d2060040d2544c8a05640314010506c000b200d0014a2503000580c00042212107120000c0e010580006240d81d41411070010708440c01c0e50164080e0455001d0109052101484821070400005c591440c1e41d000ca50303828558203042032081002050020f03441c0741c40c21005006400070380307064280030790601080d950b0396009814403100507814160343d411101c3d0704000b90700545100e09101d40391104038004c901c40040c0003440041070340e519649440c041c40f01c1000c0000c0614 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 365086807 1250 365085557 365085559
    0x30f01290102060130140a11030c010f210204030c0e0a06030c091d1b1207030209040b0a0b0d05061b03090606040203090f03041508070c12080702010f0e0c0405061c02 73
    0x718040045c001c0b070400d05203400c500900030f0000c1e003c0040e40c1090014100315003900c224140280d500201040c035a480d0300f10b003100d501080f1201c1e020881184a609884942440303685200e07401c1ca4090218000c03a4890341050310401d06121041c0030b00f40300c0d84d1007550000d0588400b0001e0601c0c1da120310f0610141800382980b500e448206100c032051007000704885003040801a24882401058090007103008900450f010b405080c03a0075000c28000728200088039005803015640d03642d00d03942ca03200e1440042081c12100d64071a440b1900740c450b02d44c0c030005184900c0003001c25040103081c1c500030441031880340700d80b41e2003041000f8140201080c80c0b50040019540562a078689000d00d605224090450603020b00c0003040020b041400d20304480c0368002c0607240c560b8182c4800c001200e072046040781c041c013000310201e100841140305590301d5600c100315100010f04420801e40603015245290141c5246500000c64440c4a00d407034421240c111404032108007802e06013554500607262041000b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 365088057 1250 365086807 365086859
    0xf0105010e06040503010f14070212030c1b06090d030b04020c12070305090915090f040f02010c0201050903030703020f07060c1502071104060308030405010f02130e06030f012901020601 81
    0x180c1e040e4640c2030564000e000000c0c003d014030b48044444a0040181824203d0760b80d1004012441c081d001040c0031034408201081e01d40785503180c0741583c000364880410300700050000d803180000e083d010301c121805080300c50007504504001640003026030740304440c01c610840c4100564800040005510400c0e01e000c0303000f042d2900702900703081d107090140305029500034480b0803c00c0044c020b86025040080400c47e421500c41e01c0b1040c811004080481d001001c3c0c80d020821340740035601420404031f51078414546a454250329602107811a0040d00c0200d01507400101181502e0b441402030401410940c41e001c40c10b10500d48038000015200b041315450317a940020600103009070007144d041003590140007400b6259403464070340403c0e4000c40b001e071019480c0038121900e100240c000c07140c3e003a52403031101c0c1c01c0707030700342020116040000707444140c1c54400ca400b0301c03031489401c0c090352080280c40c00c00c04103e046032400e41c0f010190030400c00b9046400cc20014407600b8516200722043c0ba01c8407000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 365089307 1250 365088057 365088077
    0x7090c021f0e06010315151802070c030501020a0906030b1206010e09010e030403080307022109011218060b0108071e0302071505010f090608070f141c120f05030f010501 74
    0x203800014440244404224003c0100100503c10304d90000700620688040030420b000d2494252030382c14400d0f0149003100e0030f4210401c450807105c3d80192001c207000f440e501719030740c1c0d03650758050881e40001742034000304803120010029a0b80501c610b403d01d080c140c0712548400c1040d0381c5151966014010340036420751031720204900d41025170020700b0304401002281e9a46da100d05005c200d64000b200c220005100f02c05000c44289561220000302030014004181002024001500d0040c40f11550580155070340741c43d03034402c0512909004c03c03180940d0000844d40941c100040941d80000c0c4441f050140c000e40507001071982c21100812600b4515006845030081d00c0c11004040040c2d0203094560308110010031803040e030001000032615144820840d90303941d044210740701e034a0740c440c04206c01102e810801c56801d080e0fa003c5004040208280901c41407243ca4928403c03090341d080c0c5d52004941e912200340c1c5c0c0c0041c0b81825142131420b06078194900030101910358001400b81e24100401812 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 365090557 1250 365089307 365089363
    0x2030103080f220f0e011203020a141f09060b0913020904111e0906010e0d020f04061502030901182106110408010f0b0109030c360e07090c02 62
    0x40d244624500341c0310544070b0381d4400300380c0385011640c0280701d185d10400c000021241c07421a0b5683c40c650303040c0c01034140170f401034845041c1403102e02c00c100c403a0300941950303801c3e11040300f0481101d00c4641000142c0c4885d41d0408100715081c0c031013440e00414040341400300418402c1c42c98a942641100c130000c80c2c0e600da10f03080c0c00055030101c495400081a0b00c8120f02d0b40394540c69294619020b036114429a0b0ba502c0045602a04400285401c00d42e449404c03000341c1020950400440005003021032540d680306610700b54281410800340061b0004900903c0ca0340c2c0c000300e0780e08a002d0742c1040f05281410640710150340c0c02443c100c0e00c01c02030300300958410005540c0052940300d0780d80715081d890300d584c1c0004501a000031a0400d1080e80781504903c860760055120f50160303500804060f00302e90514440c240801d0b08030403d54601442d8012000101c98000d2840845407094a0003041503d000c0f040c143c40c10202e42c1002c0c0241d13003013107400000b040d400510190031990031918010000c1c0646 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 365091807 1250 365090557 365090587
    0x120801050d0f1707110102060603030f04091d0307080c010c2606010e130b01021c09050d03020111030408091309030212090a120b071103040e06100e090709170102030103080f 76
    0x96500e02c40c0d400e0124600091000c64401c10340505000e8023520b5903680d4401c1010f841c2c0c0f240590643c0040420b120074030120b407850b48010f04400c1035800074401c0c1c1c000044154a1500058002c8440c5000020540e0307081d0800e0207040d654005506000a424980d002100000480400c550521401100c001050b80c1c1c8246140e40340c140028040c3c8204c24039500c40b00020b81441c000c650301521512000c00c09810042c101d44550914603958000103608003404c001c109100c001c0c090303003150349868400b09085140d100560107a40304500181d0ba03488504180030300030107001d00c000d20301c52600c800c1d0f40100e50041a4012004c40f41e084c550f07562100e410016041c0d0307620750400e00c481000c560742d10f02000070303071300090380210000d4440c45c45510000242d142d403407290f8060b038003e81110138003186003400c000c0c1c80c038021041141403035040241c5000c00300382d03415070884855001450304c1c141084807000f5a079400c1143c400240003503282d503040d40c80d440d888c4d00c11350980044407100080c0c2d80305592007103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 365093057 1250 365091807 365091833
    0x3091507061103180303090c0f01140a0e0f041529030a0e1204031a0a0603050105090d140406140706020906220f03050d120b0616120801050d0f 63
    0x4a2010412514500c01d0380b006030700b080780c0f142181000c0e0344040c4507010380042564803400c509801850202c0480d0103002c06020041c1e1010f042c071444c0421103414003010400f402d11600c0c0365071454948040301d030401002d802040c2c82c1da40102d1178031100310345e01122024440251440e01004d840c44401910603d02c00b100079524400042001106015083d106a001640760005000c1201c060181900340002984140d1100804010034a000f1803c200c001c0300100c0c0d80720034903120000c3c0340740c3d80e6243d1900359002102c200300603401c5500e007c01200e030001044400383c04154902ca05240c1030641c080c081486040c2d080d03120f04000310b08181000840d40450380c0144000d408252201142c00d031f4405001d0440101103100c042c0920003180c1e51200780710441c1101c3d00000140090001c07584162502e03034400c01e0102d4015103076184459940c454000410404000b0320407021228000e003002c601a418020080e07041103500e9004015582e070703158800c1c02094101ca900328419506252101d160504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 365094307 1250 365093057 365093063
    0x30506060919090605150412210305060901090203090304050f120706021506040c0503060f03072c0c0a0c02061b0604031106060405160e04090233090303091507 70
    0x101251050322012032400caa0440b500f601082c400b86465408010340781c02030000c22403e00e6024802081449a2005602146405a0010b00444552140e02e040700c0690414080109441e6001e105190070000300841c01414507130011404c4d81401c44410740c9038403951140e1446000c180100001e996211980082940310f40e80c125807100c0c6c3e440d074001c0d448000c9441038010060400001800500b800d01902200c51356981c1c17050319582d10002080003011a010450760107210303180c004039101006091b80b4403910016955403c82400035894205160401805603103040814441d40c29101e40001d2134410942c0e04948081e103e0349039583c0865809684065a902803003180d040c441403507000400e0100d00c050305c9068407000d61b58081484107580003a1035010300c0000900303011003614460300c0d00c1c0046000040c4003142d4084144c0001c4d5100c01121a84081501d0050759264040050481e0b100315145406001d804c102080c00040d07140c2c02419001c500070006c2c9103210058901c45011501841d80c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 365095557 1250 365094307 365094319
    0x203040503010e01200901020a0303090f0212010e1002040f1202031f02040f0602031c05060a03140c010206091c0f03060e040c03031209020a14120f01020702040b01110d0305060609 79
    0x1001190f120b010386814000f00c81103c448503165001d031039215080703510140d41071f0020100440e20303640841c0103041086043c1d07000c164170b841100040c0d642c0b40c1d00005c40070400c40046000e8210351b224500749000010305046452042108002d02d4040c4031100e0102c5120000302a00a9124004642000c0a031034103055103829000200b2080310069002d04283c50840b21400c03080d075100c041c241d0f600e1082044c20f502d950009101e40502002d29000700364000c10251200001c5039881d580c2d80a41d0030f010b14680c02d150082644030300b2550781004602e80c001c040c000140300c100c5501014000c0c0344544081c4800304941000b5103a0b50030f009070030500050005c441010003903d800e00b000d000008071800304078000342070b02e910341e01001c0c0345000302e41026400404101009141a100b4490b50031041056038000300020a5418540b1080c05403a10140c079a000141e40ca440f0b500c10041220314948609042c0440b801076501c1002d000513580310380c10714034203002615803074090015205000346103609074004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 365096807 1250 365095557 365095571
    0xa050904080c10091a0c120403020c03010c020102120c09061603031407054f09020a09080c0a0311120703170403050f120f0a090306020324150910020304050301 70
    0x401c00e030744100b00550150854403011700e081200449180d1058880c864101c02c00e0041c641c00008002269030030a100e801100c111044050204e406c1d21342501265015035070201c0d10716991590364607400c0e440106540303014a05034101d400107405005510080040340007580343d020416000350310210460403031900c5005a0304d00100010150390180301020080c45204030301c44208400381c403000540324015020680360b2442101c20780350401c0c0900740030744800380300040014602c1881c070040c02c00814035500c80c0001820891101e00d0700030b2080c150b40c09040081c004001050001d00580e92216045459000000038908007030314000782c07a040913200b251404a5040952448401071048a100d03034240c40c428100d050040d91180e0801e1030501150401700f044400400a0380014030701000d00d800c6c24003010343c494803040100d070030480d0b1101603c62144541040e04490702d0307000d885950100c690f030200041ea181080e4940c080c07003580d98081e44010b4803e40011380240251000345ca03018000304062 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 365098057 1250 365096807 365096833
    0x10051e1207020114061c02031204260a020117040503070c090e0706030e0312040c091503110402180405151f081b041401050d1410050f0a050904080c 65
    0x15401a584203000d5841d181076103000a4204d0800780c810b610062041d020f05070107110700341800d9600f00089a050051909482c449202d500151000d4030460503d1030180c80343c01803214170b1071841628142c142e4010000d410040c1c0c0e00880760340f403039400c20400d81e5041d01c8918185240d4080d00400402c02c1207031800c0400c40040540c03007507006070001011a00304030ba0f82d42081d0201d4840f42c1036075402c1d810401000f0220700c03000841c070744c010740300b51000120036586058510803201580641101055160410001d00c070040c403140101d000100d8085282082c0c0d400044810140000c4080c003940d242c60010300186051300980c900c5180180c6540c2d084007a0702581e6640a0442518801090002001c10021035410721200c0c5c501e1030329844146090f05246669121030b4201d810241044010000b603000401503004882404108a0404445007450154242d04010981103d40104d0003d4104d031040c1e034481e07a40108440e02601c031519030703031035070b042805481c49041c908052500c1500c1c059540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 365099307 1250 365098057 365098087
    0x90b04050604061508060610180f1505120604150812070c0e130308090c06040602010e0c0108070f0c061d07150503040804230a0b0901110102040510051e 67
    0x110754441c402c104407120640c1c0d007031100740045008100302541310354001500303404c10781802322800c40c1c0381c01c083c030616400341c6000440101e1074000344019050a00100306d18000048209144140d6041c21420142ea1155202400c180103100d80e1180351910442c1d8201d07a004182032000d89910026180386803081d42d00c000b4a544224000c907903031180c801000820721032103035003280103a0141d0f1920020300c1003a05c0c2154013840c05003803c51180a040d80c0608182d4030003000b08020030240d0000314200740900c081034280102c500c12030341803282d00820020016403010b0340b10900b501c40c0c10001902c003041e080c83c000130050081c000c10003080d0b01e408080505030004415003114190720841d5442038002034100d0301c40c002510b0080251800344814000d00c1c4000a106180808110884000711101c0380040d2041440d90700c1040c001030300082c4004503591048400d155070740e8641c000c0d031070545001c000c10145043c50780c0e003d007088408607035400048145a402c1d480b09800c51003003500e0f65411030a40c91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 365100557 1250 365099307 365099311
    0xa1407030608070f1401080a060e19050f040b01090f0e07030302070f15090b07030c170309010b01020c06030c0f0d0204080303071d0901090f14040c030b0601052506090b040506 77
    0x55148070f00340c00010040941002d00041d26110a0000101c2c10204015214010090100301c1c1071502c130000800c6080d40b050040c1e20070000385003001c80003200312190801f01d95018228a9a0044030800c00c0003060701e02e1202811030f24000400920301c0102c10311100101900000003459024810002007031690009050b019a402c28140b014103d41c1c81d06500810300e12580200c000c40c607042c100704601040240a000460302a040c00240904e8030360b41c4031617445460781d810600e9400441800100303d0b0920a00b071115030300380010001c01d591007000031414003008107411900320000506c5540b0001050139120a02c8031140c0a42d144e640f00c0100c0c46d200d820894000c3d00003440705110282140314902c9400c0380c050042c182850603400d1866190180c020f00902004603910303080c2d542c044c019128980d6210700d00030b0581800d11400c610b40340e036200700c02524042c1006000d02005000c60038514201502c1014030039107051030302040c50108042c00d00b07828040c00b48500241080140000411000c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 365101807 1250 365100557 365100569
    0x10b0304020108091c0509010e090a0e07080a030c08070f0c060c060b0607110f0303160b010503010506090f0a050603070906150f020f0d0302070f020402030c07050d05090f090a14070306 81
    0x10b540783d555142d1300d030b50303035000440c1c0d80d8003c44000100781340150080c0000d10101c00c062510020400203100425031411003541c1b00211680d076810103494a0500340901c00103000300311f000d4020694543c8004081c08d01d0040c02030840b2000003182d00030481e071201010310043d881005402080c1d6039036006040c4c1c4503040e5003500c1e1281411032951852800345e0498a865901c540c541c10b141010405004502d490300050f0358152000304040107000780110040311000d0300c01c100540042d030400090509456020781141c0c010461002405040991103001d01d512600288000442d40c1e10200041c1c60000c0c07951040426038070b00034010401100c0800b2400b01c0c0603094440c0c081c00d0b1450001241e41e42c21102600f400ca400418480142a110f9002043c540d802050038440201c0b46400060890340241c038032140180e00080e2030720070060141300ca5140e4040c18140b150410711001e01242d400c40e06105a54032800c034000002d100e611142e0302c0504c06048541e03070142d240c60300344000ba0080c80c0034021a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 365103057 1250 365101807 365101817
    0x606081006050301090b16030b030f010b010e0a030c030f0c0506030c0a110a0c1a0d0c090f09060302030c0103090203010f1505010908010615111c02150105030f0c13090b010b03040201 80
    0x4505403c0500840032040c0d4041003c03815903440e68040c52004040e007044d0010980c0b0341000701e000369403c010011081ea82900001001d015680014061200305440d842c0100792050041001c5105d0940d02c0007200d401034440500340f41685001042007a141d08495071140011043c0b00140301044094158500e00351141800600c54000b6143c0c0d4007005100140341808c2c010b804c0c8a41140b603407044a4940780601074900300305811021100761007411040c0c2d00000c03140781042020508290405009040d80b0508102481c1560007003511000060b00309030500da22100356404545095101300c0941503004030400645003600f5a01c1c070821000e1158a0025426038004201001c040c45820111180a40c4d1800300f10301110701580d0000803c400c00c4014000c01c500180680700768180310244006660141840000785540c40350440c0041c0c1040740264801001d00c0b06040d800650040c102400711600580d110b10b50114401030140c44074010040e141103800014040c0903280614040da200344c0354 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 365104307 1250 365103057 365103059
    0xb0315011d060d05250b04081c0f020a0813030803040c05040b01050a02070911040305061e0c0720121212090d1422080c040f0c02280606081006 63
    0x800450502c9034070f000e8880e8210b40400c0c010314940b1030700780301009800c00042040c9660303584001c1da01e81081e031120b030a94201e40794003050034544011180c540c0351242015801c030005401c0081d5030300320038580101103990009001401c9590099850015a07018849c2c0d41e80e8030741442d01d04090749603481405e01590410600c0341c510741c0980305503400e44016a004103292032030007070403c0140040303400e0140414420880480031410602c440380c455540c00042c10680d150001c80c1d012103150090140109101c10711414000480116080361894114004003503101d1b00180081d81751103601c000b0102500c68090008441e41c0c0ca04042c100d0400c0000c07203004c4554034221502d4503400b010300407100041d400494603043e00c601502a00c40054404cc4008990f0600c0a0340040341401d504035400561110051419070301d403500400700c01180c041d406010301285d40201039a61105826082c074106c05080740e910459a017007000c0301016030001d9052100302c0c2d5954846880f2612500b955014a00340a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 365105557 1250 365104307 365104309
    0x31d1f0807080717040204090203010212011a030c0409050603010f06120506060a1406070f020604030309141801050409050c0301111c020a09060516050609100c0305010e07030b0315011d06 82
    0x120b424414032580c4c9850b02042900d40c080c3c0e080c000d00400890380565102902405030b00d0910140140f901415115016541003604110040c010002d00680b611820010000310705d011605503012102c801d01c010a944d1641400a40500454420310580078a4101e0024414003940e0b500b140c803038080d0042e540e40c1d84840040c001c0300c502500800405002910707103080d881c18400001c03e145030052080352404007650780010f05139402603005400003528000140011a00d510000c03050810071144054002840700307009008840500c1402e100b103030307130b030980702d05000060000e5004000700400030010000d0041541c02a41c2050f100e02004410161200c3d0120400b84200c4030700c2103494640061481c5040e0301290181e00003011340210040b80068040000c204000c00c1d4091424800907200c0320028a041b0401c455101c1c030100d007014100001000680d040915103500200fa03440d01003108900c51021a24210241041c1e07962002040000620150720135200809a5242c940c2c126154503200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 365106807 1250 365105557 365105567
    0xd3806071703040c090213050916020d0305270102180102030406051608190f110102040e1803120c030403090501110c0d050c0a0602010e0601090513031d1f0807 70
    0x24000800c0000e070110421030007001d078005598040e00c03409840440c29122100d100507600b090342c060003c1d0440e80c100344101d00d003a0803110385c000f0900d0500b0964804c0e10701c0003507030f078400c82e084c03030040c15940c40210326441d60913181d02c4541c400c1c910051081316001100c55000f03500c21918001d00340c14101400e00c0307540c800f00c1203c003101c145d40e8545040c02e60650b03441e0070781c20b040da10072507291100300200c0c0240c00386280b00032032280e00390300c5800000700b41c03420180040f04075142030385241e4410842845a24185e0003410380001c0011150142d40e01c145556030720f9482070b14900f080101010082044002d220310003507114034425a601011182e4a600545955651000e100d2180c0c120440c0d010303040c01d00d000c0a851040c010780032912200d2031a008160500c0e041d400c940f0060751111900e0025800800a81c2d00500e0890390070086840d101682050800b442c0100804208191900d601003540078034000415800c02403007250401c551030000714000030440280000b048007400054540f43c00380e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 365107913 1106 365106807 365106817
    0x33601090312031821090b0903030f0906070f12090f03120f140f120f0c07170705120c010f0c05031810021809101404020d3806 56
    0x2c170401000c02041d900000f100c4c040c01c01140da01900c0010071521182c80201c1600d0f283c1402100050680c803c0c40f90107001d078803d60700042c0038002511041d87c0042c0c0c40c7c1d01c84502d0b090f594040d640c9145103602c40a410f1200200c00c20300028080e8140c2c00c0c3c0c81c45c8500d002c4058a0007224404600d40003403980440074840803814480000e14030b1070891704038000500c40c621503e051000c01105100c0d10500401c0418007003500c1c00d035813412000b9500402d505c00143d8a00d840f200c0c0750410141c000501d1240e60b503080c0b84075101d88007810300c200101c1105a0762818516a242a02020307030000047c102d10b01442515031030111083d01c1d20261840e540c886128184401403542001031010700a00748040307803501e880c4c1c10022000b00300d040b001d4541080d2805611060707040c0b46030b0700402c0020300102690a029005009203c1000d180048074071440d50180c000c0b50851003404505d000e8 = true := by decide +kernel

theorem cover : BRFrame.Cov 364928057 365107913 := by
  have h0 := BRFrame.cov_init 364928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 364928057 ≤ n) (h2 : n < 365107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
