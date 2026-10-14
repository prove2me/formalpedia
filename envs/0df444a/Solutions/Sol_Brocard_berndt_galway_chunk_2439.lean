-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2439
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:43:19.282291+00:00
-- url     : https://prove2.me/submissions/38269c5e-c100-4b51-89d0-d3a14e7ec365

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 438489208 ≤ n < 438669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 438490458 1250 438489208 438489241
    0x606060703050703210c0e0a05040e120d0b090f070f0c210201021c0203190501060804030503071806080a0606110c0f1f08091207020121060b0a02010e06 67
    0x1035a90703e01e00000c513501034401000504650340e0700003c01035408080700252107201ea040c0e2054580c000b1621401c810070200340f8040e001280a03d05060142100300000180030081e03038100d05071992511000c081d6540203190880c40c071540488144103020a007248a820580190b0702c0c0d075a02c103469005c400040c1d50041c1d20b54030080900380220500305c4201c951002c01843e0800500c005440d000384035042d000301c0140d904000c400e0b0703680081840021610f15500d200401c0020a041c03001e90301d000300c040c11a403002440034003400b00001c0066855032144074002d13242c0805021280c2019120b0000500714002201c980c071200d480c100011404034002c00441402c040c40400030401c40002c0c8040c46001c2c0003510303400d41c00c000501040880349010201c002107124240c2da40001a103051282e1528085117061101c0b40d0000411101c00980d034040e512401c17014110b2164a51800f0f040044401440035610100080380040383d03454915038103401031401c4801050895115403501000340c1c040e07001c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 438491708 1250 438490458 438490463
    0x3030b0411090d03090e0114030f012f1606060510020c030d0e0409050f0d0f09030203280203150a0606021b0126010308120106180b0c190507060206060607 68
    0x101032001082920f0b080d0002860701e44039217041807009a95124410010a080e040700c1ea0075200f9440799003090604014800300701c2c1001e070007448403032100201c019144001b81500c41c040c41d0b1400105a81c0c0f070303000d412a10054011010081c01042c941440390041003280122481041c091140300b08003071000801c40c9002e440100505120100000b060350b40c1500078620729001911407280c400825428002c010303070718000d08080d20041c0480d080042081442c03036508820f02201300b4003030025031400907090311004040c592815910400c0c0c03035200c0d1102c0350000f00a5152241141c1681c02801c03c45e005405880c40e64400c0c822181c662009907142c803e600d0084040c11aa440040e0341e40d0710840312070700e00c1a00d003600318070171051004002504240c03d80042d14502d10000f00002150820302000e401030200b46400110200300f07400d50280820a0300c13450086c2d0a0105000741180c2080c001043c00303020110780c540004816240c400d1f160300961080e40098012100010704c281081c004481c041035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 438492958 1250 438491708 438491741
    0x91e030304290a2705010603021221092215051c021003140907030b0c03010602031806040b0a031407020c010212070c050603072c060708030c2503030b04 67
    0x29074094030f440042c10396500340042c9800744012260340140030000084c0c0e09006600101d402401c2d40184880358038808040a866400310400c0d165210b040710f0380c140480c4501c18596510340c40c180006950078000c40800755042260015005d69244542c04522b54404450400c01030f280e40c0c0303042182c0d5030110308803d0303000b0003c020904014600781950300403014440c1000a040d04440c0345050b0040e00441d40d0b504c0b1640090710900178441d141e1b200702d42c04031000c0a80d902e950705104c3c00035124001c14100004281202c0841c4070142d44440549000e0242100c285454900ca40402000713404040342c5540411212808101c50910102e141d1800c0501a0004d2002829041d030310000795000402c03d42e030100c448480030400d43d480300c0007107028003910340d11046501e0601000d80081034000481d15201c003817020546065450703410075191580d4120501507141e5036460b075001864418103a00d2001400c120041a268842c3d002070b41d840d190080c0c0e01001660300a0051100b180e01c0d003c6059800c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 438494208 1250 438492958 438492961
    0x6031a010f09060302031003050f0703030e0306150108070c081c06081c052511031903021c181710020a0504270905070617010b070b091e03030429 64
    0x50080c5c00454112403003803c444d40c195503a4450307500385003120307a00805a800c02d140820a16a1000764220f102c417048000c0d00b00350401d000145043c15041501d64180114600002e9046008407485070185410441607540d810041c40c66013031540c20111842c00c220f00d02480071500a00000c0c1c94451080e0f120440d01c95242800070039101d5030800344207480c0b600f00341c40040b00c3c20403424298a48080c442d0621079805610b01e01058140558070b040400101050541400800d0380069601c8403005440d1690a00004241044a031140d16040e400f56502650000140c1e2040601802e0020030b00402614030b11550200500c0680c42042d80080001d0000d100c01d00650307800d140462601c5143c0d440d9042d01c602e0205040c0e050f515a640146d60305e40010004010958111030360003882c10329002c01c462a903040c0180b0881a005010340a069550108009030122008009030b1240c07400c58964142c01c01e05c903418882da60740c02220102c0c0c4c3e02140f16252b60306003490400031b1005400c0200c540190703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 438495458 1250 438494208 438494219
    0x317070e0a0b130504110409020c01020403020a0b070b1914090304030303113a090f0b01050402090d06020d0e030c03031605070503090d1119034d0a06031a010f09 71
    0xd0861501b6420f0500c8040200180000722840201074000281001513110345ca94010451200841d5003c000f0404080102c04006012030b0306003031b0302c880800070512142c4107003041817004013140205803400e00918801e000300101c00001400c1100d1081e501401100070f00c62005d2603c0c0203c03441a0303c0b000b440210340d21210b03040b0800b400e03e045000e00c280d030394520007085a01902c843c0b001c19580d5295900c0c0c850305010b54001840c1c0034050039141035190014443c00320344100681c1c400502241e40c04503082400222a0700f151407010b42c410100c90702c64980000c0d0701d803a42e00695403089003000c082d5070402c4ca00d0041c8290b400f200d8114000c0c506242041d001d200040d41070341c4041301e06500c00016041c55a03603488210054070401d00581a40c03d081d071810151500b040c0ca40315000c007089039035454110003010340b181050303025031a443c0f14902d2071070000d250451605c243c481d44501a4200401c00740c0c0d140d400741240c03481d04140e100f80c11707102c8001554802c07185003004000481c109410f014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 438496708 1250 438495458 438495461
    0x304080706050307120c08090d0806060714030d1d010509070608041b15050406020c040506090103080a02010e010f0e150405060a0b15040608071404080604030c0317070e0a0b130504 79
    0x138000a0790402d4103042100d0a11103003110700f90b10005d00070664034414072081742810084c201a48115003404031007030921100086e4580101d40d002002c6c0c541041950441003014800c0e241010300326081802001c10b6031101482c00e000c040811442d030762030400010182800000c41904440c0c40b51117280040c0c803161030780d04800042104c0c1804040044200080b0205080c4800341c2030902039840548642c14980000d00741715501d01600c0c4114141800c2c090b081d40c51014260440e58040d207443d81c1c5040410040c1c1c09416000022611075180c680e20202443c100d030040000c2016080c20f0300c1c0200207906001c040c199054034040e00f1070344110b0000e040441075070700c42d4401160080904030b05140e0940846202c0d40039802900000d0606c0e014001410707003040380c45080c9680c0903000c501b060304220038159154802403024080010758040c0c102814044d41044090500b1443d2000c06440c1942d005007211300c045841c00d028560031000014008501c0301543c2264100c5051000d01c5440d00e004c210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 438497958 1250 438496708 438496711
    0x9020702010509030d0e1002010608030d180b0744060a05031207050607081b0906120a0903020c0d030804020904050309090f010e060604060c031809141803040807060503 74
    0x7418003004000c0040150340801680703102d883c26949540c4c94801c080103200341160b6441c0c0c0c0c10709583c1804000c0c81080340c0441038403903065600d0000100c04581c2085030405205509000d00140e01d40f00030b1001003a40280c48500484082c440c10340089006026655072070b51210600b43c08251459000c00003071804841203070081c0c402000382e103249444030000703030815500c404624000c00c0002400b01c100b04003402040c1d40221903080042103450210500352502640d0b21100d48401800030f602c4130559038001c1981d255042d088a51800c515007054400d00a00b030700c1d001900507110b154000440f91800340114400c055240d650007100381c07070300da0030300101c200e010b170003203c090006215559081c0c850203442072017081d001c0d0484181d54580b20b00c0b80d4800038050a8280903042c200f00c1488115084018089040d03454540500c4200028000040080b020b40050200700e040c040001e01560711018150301501104482a88140380890305035a64440e40c41044019040f58070100510360082d0f0245 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 438499208 1250 438497958 438497963
    0x50d110301060512030712020d0512040602040e04060c09090506061b010f0c05210f04031805030102210c19212306030d21060506030406140a0b0a090207 67
    0x101d207075621000029140424501c3c0d845003541701051042c00d01c00144000002d411250018122009404100400d10710804801d5241e1380079010101d010000580e04840040c480510080140d00789460301d940a0181280420006580300030041342d09002e620a85014050052001c2e01e400b40c0002c500844240c088091a1155a10201401100710601410701c0c0e05c0469074030355030f41e10a0071023070ba000c01503e1004014808030442c05c00440c204c060321400e82054060605070410903148824440900007034000d0303905035001041c421412481300302271303c00e011040e2042601c01e6840c5616040c6134002c0178400c2c0744980012010031151401140410500810742d643c03421002c240d010b41d10f042c0e0300d0444440c248000000c1c845541b40e2943e40071030b5007000003180030344100c80c1d10180040c14641d0103c1e10000c00c000e0600d051192a40680c0290028040a0702d029101c0c034241c1080c000070102c40404070903940b20b560003e60205558070401e100100c0c0281034040e00341c2003801450007900007202c02c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 438500458 1250 438499208 438499211
    0xe0103020c0111092b021c050f011d0303090a020103180b150111030a09060f0c060e1b030a050703060b0f030a06050103021309020306040803071806030b031501050d110301 75
    0x403003058520a00428107003025544181d903485002030b040c00701d05d0b002031200c1c0320a400c0b500892010a8941294901303070f550100c8440620180446252840c020034950083c4984100c10345071000b00d4040d0000e840140102c0d00360301880001e00120b1340ca9100845100c5295007010070340c080198060b500c0715900300c0b510840c9403821181651202c2c0c0c5c0d5a0251441d5034802080485540b2640e48607819000c50700500d80954182901e000001d4010341320b03402039100f0f00c42818202c0441c240318034504844180c002c101401515025120700c2d0300d441001c4144041202c007210820a2400c0c0003a218044541c0200103203403161440d00d62000401e040090164480303802004240c195904003c4000150f000d008000303115490f5204010f00038004170b11900e101410902080096980400c02c0c40c0d00503008032506070740303584d10b007000c40d0b03064140300340041101780311a4045041d5074141d000a010110036000c450800f08906082ea43c24042441002d50041da159900c4000540716080f500715050301500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 438501708 1250 438500458 438500467
    0x303070609030314090a0203060606070b150102250302090c091003050a0204170105070329060d0e0303160e01050f04060f120c051305120a0311101806050f0f070e010302 74
    0x80c02844020207460b140d401b60302c4070840b803080d4034081c800782d5003122003111608e1401e06150384020311268004c1500e92603501501000b61503034024040401c040388000c40b8084c910f0500b010221640507503001c01d9010300030380e00002c1d0361002c00704202e441806000300b4616120318a801c0413005000d0040c440d074122038003030000040030410002020540c441010022403140b078034141c020201d400401040403c81e40c403040c1d88000413040d511203085160281c4010b0f0b55a424a10750030003030700d002103550490384030000130407034100c0300b00103660250741040e0350324a4801d044000445072170203022144015550208404c02c8094050304007032015003040d060072150300e4485081d43e02200e407094104808a80005025100103090554040190104039450030b0355151075158a950703007400c49001010b01600d101c080c0800d08041003816800c003002c0c24140a03461744444c0d10100910b02c0c0e6400c848050038071010510104d0400326243c841c0a011006180340c0da11032004036803d04143d0710346414580d0800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 438502958 1250 438501708 438501731
    0x21504050c090a0f2a0e0102150a0207031b0816020d0609051f020c10090311060903040302010e010f02060601180b040f030314070804090209040b1002060f09010b03030706090303 78
    0x12036601c43c05142c600081c03800c8001076102d080e1003403034081e01600002240e2000c110303c1035441ca07244000551818158101040700103034541200034412000010003141000305107061a00200021403095840c28100440080d041c40c4880042d2401481180280414a40061040e2000c0c510500050481c4841481d586681d011940139110036541c5400c85460040f003258520007941814140c680304500e00040150a95210304075101002ca07002e8a40000360141441070182e000041c0310201075500b2400e096011559a40c003a210480c00702d16030090726008c0707600400c07500e0300c03082d50354000d000d030b541d01c40004640c000c501d0f0340b920001082c2e1560208030401d001c0042c0001c0e02c0080000404103044d400c2c041e00c80c0100c1c0b1314a601d885002c01c40390780021001c4054800711034441001680b20f071144000200948064564503820400103145414001d038000383c03040c00707820303011f03203003000e68440d500c44e1801c2c1c81d0031409050b0154810406080011000d50140c144940a0b00d00000e07100b4442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 438504208 1250 438502958 438502969
    0x50402040b190603061e14010212040e0405010501090e030d050c0c07030c17030301150c0812070f120b0a0513020c01050403050a081e0106030b0d170d050a060501021504050c 76
    0x1000d80601c18280c1c40a10000e6090703c41c810281a42e1801d410b402c450303070010446d1118050098003844000042410443c0e4001c200a0740e003250120801d0703072100e40f10b10101811900c200d0341030362107600382000081c030200795104488500c4540d0f00903500d44007000400c3d0b00034190150000001100810621943c1d8509114030030246210b00c00541000e03240806080d0200084000d400450f003040004100d542c1c5801008008907505083c11440f0039540c0c02d141f84640134400740c08800b901442c0c2040685544007d4181c0c40c1901074542c0010b00401000410482d0380d040700751604520343d64030600c01403520310941007001400312005071601882001603801c0d26010340f030490102d6004182600c81c01d401c0a6601d170300182d48648900c1c5000358031a0a070b80c00d101840790ba805d05035681620740540d1500200c0381030080d040903040522641d81c44080b5040d40c4a030b0301d1401340925000103d010300900e8084c40084840590040440c3c0c0c0d4803004541804101030411550351158101800494846 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 438505458 1250 438504208 438504229
    0x120619060e031005010807090605040b0d1b05031e010c0201090c2d08240609040b130c0e0907050103110a2a0b070f0810090e0f0703050307020f0a030f0204050402040b 73
    0x300060103a5928023a041000c0c0d48894001038170403800c1c22a410542c0d154000d06540c481c2e0407010003200043d6080d0090301208181d00615018041c44100200140d10318034201c0d03110b04e103c0c00811150005010880c00c07162450001030030300c11002001c004c11110302c150980845440c5a0f0a02c0300040401e080514110b60703846a101030b04a252448013001101c0600706803081040c034818040d01c0c4c070500040001000500091900c41a04041441c2c2c06015420169031035003c207a54119580310044110b80c5a800c4801500a00c241032000c6a954400d006104001c44210080d0f410f10703000c01001c1e250303003a00e0308090309102e08402c03c0c01804540300c1e007440d4086000300480401424107020080c00842c2008140c07040c02940307070501815000d4005844225459241d00003250200440d0440c14802001c210240502c501c540200c10b101c13002c0003d16900f4400c03500400561103500034020b1030603e5210107081f007004082401e015080641066520910052000404410103400121b4481d40f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 438506708 1250 438505458 438505469
    0x30509150d0506090105011701090216051b0a061103040e06030a0503030a05060103060e06010c060507030209190504060603331d1008012706061208120619060e03100501 74
    0x300d610a21015050041c444c030301400017840c20146483c0c164000005014040c45120b6016034002104440121040b0310407100c55407100940e860710b240c040c0d2100e031018123023100c10b214099050002580b24003c1d014a88840c0500025504003403030010822200303107000340701035011701078140a074001a00a00055104084801c00042d0f42d040440006049605582125500d903001106010042c2e8000301c0c000c135a0b55000c0004120ba68400000724041d000b02d4400b02d4014221100c0e406248580101d004282da8040e01c0030003e1a5881d80110300781d0b01001c2001c400310030369000e03a000070500d80c0030b0380440060503070740204007a42d241e01291007100c1b00108861603880c010b0901120080742800c00008080d624002c0c085100b4280d500e030300c250307404540358501a141521007000c222840d0015001058071075005840510242054001755000d411034069201c0c0100000b02e5900d4940041402d00e4104842d00402904040080e60151550150070340c0c1407158100c416401e10a070b0151074080d14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 438507958 1250 438506708 438506711
    0x9030a08030901150e0c09010e0604060f030f060608011701020c0d030207110103110405060924070308070c050c0603090118080c0f030906031f090908070308070c0f030509150d 77
    0x151042d41c15007120101c2c1407184030b00e55455403c00c102601c1000e5030f50442501320080d40d1f15003400b4010781e82011044030131a000800890001203450308607160910400094800b0b002c2030707201030216022100e2902034038003c1541c0d84014410290803a0007001e80310546000140f80062158100e850603980100d0100025000507800c801c2201e00110070320349500a080a102200340705c10100a24065030080c0381c0100000710b00d0034070340d40d245181490b03a1102440c420f01c49050303803101600103074403800007607002c20400d9020600c240c1c401d076a586001a00807029060303000c0d6243c02c104982c4d02c041d00b07103071813513481d81c20303c00c550f00010000d1004140729003141da81d034000590000d414118405410105904140011780c010f131030301000c8941c001d20103005200c1c4103034200d01c03d800c001440c0c0c204111492602031390208211205c401000a14002e880e001c541743c1d11480111102d900740d00c070041040c00d105540000080c041d0300a404a814002c0901d0000103108815000ca5081f0882c1c84c503185 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 438509208 1250 438507958 438507961
    0x5061e0c060108011a0d050c12011409010c03060e0906070e210c100e06090409060908030a060e06041803030b01091203021513050327040f47030309030a0803 69
    0x122200707450304051176041d641200402e0070381c0c48140c2ca64462004160045a07103507114900000c080d4003001202405020f444218188208814000c00354060305002091528002080c41a18951032900c510704401c000c00450340e8001003101c4040742c070908a90002031103610322903208a090f920b4007469180e04c0041841010700c00411003010074500031142801003100c0c100d07040e51203d000301d409021040e80d0114216510741340c8400103007a812001340c60706c000801440100551500f06c0030498a0610000009803207090030801150340703045a28040d1041c9041140010780a50400300e00c4043c1414921510783d40c5203164000e5001403541100140c1040c00401804030012a5032034003c18a001d43d20040c00040d510360f40e4034030a16041e2800680712107107186111503801081d0b150310744050401c0c0160101d10040001906403154500c0d8440050b9118403041000108880515116000720500a01400d06007040c003061040c2c00c950140410041c45234551000c02020b0100e5210342c8489590b07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 438510458 1250 438509208 438509231
    0x70606090e06060a050d0f0206122a0f0405012d0e0301180b130c08120702011d0105091003061d0402030d02210c0c040c050408011505061e0c06010801 66
    0x401d00003c0070a031095106190034461034460b1400240075951102080002500500000300c1c640030b1900c100304c00c1e03c1e81404002000c4090900e00f2008001c40d2030450041d403078030a500a55005662801c503451406000802c2158820180f0001d00414410445162150691076000900c41c49030204042110360154050300c1c20b091003000301c0840108075440340c02c41f2990b1000a294000340102e100c003100c03042d801c8140213001d0030000003820b07194100d1380f211400e03400840c100e800c626001d9011034940e0603180c01007880d68a00721081c01050303459a10b850104010400c0d4962691424010150b541102041880186010407046900c000c401409468035104041c90b16000000c1501150050703004141140503040322403000301809230764252180b001101c0c82d03140c10400e408066000d820b01c030b46000038030340180090040d540070100a100038a15007203a0b0505448a01c00c030b58100d403003008511441140006820f121042140203170380b0301020000c0b41d0b840c010003070f0410300c0f540c3d5654500170701 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 438511708 1250 438510458 438510463
    0x10c0302091c050a060c09170d090e15041802130609060b07120507020d02061210121e03020a0c180c1e110309060a03150501050f040911070606090e 65
    0xc0345880c00d400e1800c402e55a96415110629520000c4c20703140c0722070340b140034940507141c40300c0a04040c0d00250301825490041580c1d8041d51000704021980088000c0780351190414240c0c402c21001c1824440301d80d44405000041080248406070304000980070303001a80c80344e161074003104590710080b8650b0b0034072170300d0000c503101548004020380f0200000301c0000c2800110100035109424520344440084c00441d0031110780c0e8074020b6005c40002623440080d20b240030194003800300c4c140030300400c60300c40c3c844e2807041501c0c5201818003040c038140d03040c01c0c15039440900d401710310130b10544142d0071195503107900404140d004070303210790a1100d42d403041c12028070035512440074600e000620f03900d100010004840680640c0380c104201c42000038111034080044561600003d0041c503078541c00a88000c008110420308040c0300d0914020000b4158400e005940c03012411010061a291a05034050b0040c070a403400703010710742d60a005007030101d0040d100b10001081807400208a00f1081c800d002e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 438512958 1250 438511708 438511729
    0x14040e0a0e060103020d030c24090c0509010f09020d0b030d0c05010506010302270102251a0f040b031906030c0504140108100b0f130b01080714030a05070e03010c030209 74
    0x4055000400404c0565500c5a81042441e09805c009031602c6880c2080618201074011080e010b1400d10040040020382d503110b4041075001c1e031601e05e485900c030010030001e40e00031702c2500e2200003c16410f0115000943c000d1030302c1c004405001800000c0200031a0406120544c1e41c0c0105500002c2c400600a00f8000c00368010000d103011440c121842e00d42d8452414070f031218041c2c44198903080785e4264003c00030804c030240e140750044503000e90651203d804220314042c05501c0c3d41c12940218092010b081541da1070308030684c02e10f04207070400c07000d008a0f800c0100f040703070028003c15410001a8141c4144009035014400858441d41403000b071101343c0d4072600180e520148a07000411100c140450010100340d0380c0040402c1700c400f0840060302c1b0000c900c0000b54003900c40f919613828034582d42c0c031841f0301110070703298400281d48034101510141640c501ca0411804100005005003100c1c0c0e0265502c58034a00b8000501020303500443d08492100285101095001610000b02d00d8030701c2590 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 438514208 1250 438512958 438512981
    0x90c0304170a0801033306080c01090b1206031c031a010804030c060506060d0f02041703031e040c03050f1e01091a0703020f0310031203020306031c14040e0a 69
    0x9807406411280081c10b61205200103440540301c1440261068024083c0e1100f1b0300042d94103c0c040901804032000800036407123044800d11901240c01d0155000300c00c80c2045400c0e00003100d0611100050320a0f0086008000607452f02031180c2c1400c81c2084050000c0c2c00480c15540000c000321000703084401c61000000303082c140300000e01008000780d0300c420481c138060b522040100b8a51110b00214085004406140840904082010a258500764058800c550003000c7c83c1c081d42c0c800d0f4410640328407040c0c6a03a82d001e040c104044e040301d4000440f90b0380040c801d111207a1182e9407030302c070a403c0041d2140801b40d1a00a03040402c3d20200d820050404460719100070402c01529a9405e1600392060064804a01290340042d114600a41c1514008021014104c1c3d9901e40310700482a103021900003101d0284807100e040408600ca031098034403c0c5ca02400a218084003814140e12454044145038100451000f8546070703100120007034002442a4200688242407110140c1c09540e01c04500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 438515458 1250 438514208 438514253
    0x2030705041e0c031512020a0b2703030906120f09030406210b04093e04020706090c0f081009030806061c050c07020f09010e06040b040209090c0304 65
    0x8906100610180c0b001c40c0401c100d8000900b045410001e43c05000030f50f0b4002030340c0303040c010b002400c0b54200c40d085c00014421240e01a0050315040040700d5400703184100007580082c0701c0c1455900307068402c500c4180c20000d0031281800350b4800020f44c55403002d81d41c003085240c01c0c0c09104505501511490700455000003841c2083d050020080c650020709411080109414500300726440d0305030700403881400c02030014400741a140c2414600c1c00800190058114056010441e01c04007150105508440b040e081102c0280d01d8810000650800d0a0903112603039503492030700c00a12038403440e90003000320b02c09840c500c81c6000c00c0c0034104035280e103910054074100340310103000990040d1166071085044804645030354041700c0652000880c03190281c0410300e0001030080007101301c0c0152100a1088034591600b030401800c0c8004010700384100003843c07803081c02065041c0391540010b88064409072006040c1000c190006004800681e04c550b41140c00106010a214400030b1000308001100e42 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 438516708 1250 438515458 438515471
    0x30d090b0a0507112809090203031c02120114010e010305090303041e06020406080a0b040b01021518010216060506090f04030818010203090c0f040c270e0406090203070504 75
    0xc0c0840c2441100558420090700241c1c020800c40c0075006140341c10b80c060084d182c041c0d800600d08440c2c1c03c14039001040c0f8904030034001211810f5025950f109a8058003541c20a00000b803030202e4400d820b01c0d10244543c091140396200c9504200c07450081004502d00c1c010b00032124009000c1202d20090780d1304060a0004001d031000c00002100d17041a4421248031010f2020341d181b10400e118010024201e40c0000b40004149074401e803214000c10182500300700626015042000300c402c140749141c00341c0c000030b004000400740da911156102c00482402d0007101894448503089a00c4041d00c04041074000340d070038043c812035100d4643d104406440300506810000b01c1440c1c00c1070000c2008080140000c0005c03000044000d1074016650500025500c0e410415001e0342c46040940d09903000d145810030914641c503040c0030b2142600c4041e01c030b4030021070206810310a0240d2041001e0a05940003030b00142100c000c0701e440d4440c9004440010345c840c000d104042c10306100b580098899414940c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 438517958 1250 438516708 438516719
    0x141b0706030c03060e0f0a020418050601031506020a030e031608070807120b1603022502031c050f0d0b191a0304031e0c0209012c010f0308130801020a030902030d09 72
    0x51017a4201c80045410202940e980303a03940003a11454001c407402406d1560400c1c0703c1007a5402550080001341ca05100009001c0740c8500f00c07522034414400180d000440c5c010200e03000748184645004003500f902c20341c9186803c1405484519405048130b503005020401c6512414441100940300c510061820411640c561010001c0040c0211290048401008010b18001d5048455040c64032005001e84e40b07a410449031003403080c4030264003d00031860f01110485070300c90341055524181d210305040885203a040e02454210880e114007044d610302015a2a1340d4003400300c5a000120201c0d052060305015200b48005100c020101118000b4014080080d400c508940c03031a103803180030305e00d5a4a40c86012651070440b1072019400180207000460ba40041c00301035020140f0b82134140f00301081000403044101403d01c1aa907080c05d2945051002401010040c249590040e2001402c10744981c911400c990084c860311010030b59505405045040c00d0040b16000c030200d0070521861403610 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 438519208 1250 438517958 438517979
    0x10b040f0608090109020a030b16020115091a03070b0901020f2a130608030315030a0c060c150606091d040308040201081b0c0c09130c0303141b0706030c0306 69
    0x703028920600a0240010306003510950002483c0340d0000c040f102c1030342da241041d4480600594451f5101e100c04405544014014062081400b500d4010f03c580180703001d0750b40c4024100c0a44511100c502d40a1901d280d540411689010f030243e020070f1a919070200c400a80b41056424403440b4a4000301c05414026021400c503282541410305020043d90361500010b1002100075561040180303440c101103004680003018612545030340d81400b131407600d12410580c1e10701d800c1c800100800442003040c4003041c814140100c225201c2c11031900103103000750b0b40b24155000c5420000000b01e60160400c1203444840c00c10502d02e803240490486410aa200100502c10080c006030500100c0804903104c040110b000301c1c26032815100d1b042c0c5443c1448101030f154581c02008511a10840002c90340e6980100d81600885a200c548801c071300b40345990988a1080160002400c114203201c1001035581440d5042110f1801d203018140d61814040d0150495180e0208841094074004040c030140b4001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 438520458 1250 438519208 438519239
    0x7090b03010e10030f05070f05041e0c0c050a110f01081e040302071a03100803040803041202012003070b010806060109140a09090b100b0f07032610030b010b04 70
    0x255145420343d442603403205000c111079000802c1c1501c034440c600c09000c400704040081c0c81c441010f0480c0c0f2640c2304104025140c0c81880b001001c2800315180c803514200d0f600420752070f41e160500c40c01c0c004403601c2d000c1c10560a50b0040d908100e5091100c00580f42101d14420350401c2400c1c59010343c2808200d4000303031050b201c1440102c0c0c11380e001040600d0b0017041840c00031b045120500c1c00884600c16003000a030800c0e6401c1300c0b00c45183c6404106080d010042d1001d940c1c0080003103050a11780400803140b140340f69400d9050020204502c1c00c0c0750008441c100b20901d00500450f96a00540b410301e21034981603200e1185078002c1e506004241c0ea0060b688812a040d501080d500122903c4c0000c4400c225544210985847c020b611000c112078415011700c905100710f000c40703000e5560300e900d030040c1c8900d8410120280782005010000780c06003072a000c41000c9690840d01c010820300b0407025103201901c21090405007642c00300104865100d92078054000d1a00d01403e0518103031000c0883c024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 438521708 1250 438520458 438520469
    0x13030b22060515100210051003050a0b2802030105100c0c181104090507020f0109020303030a1d0d050d0c1b02220603030504050a08150f0a0603050307080d0507090b0301 74
    0x7100c002141428001c150503c21828006104404110a10708042e50315800d44100d6002d05040c08000340d20b13011211380f01803c617a040005810616441d40d500c80c015000104104e0380c00040301030842400f903890004401c00c4041e00001640c0307505010800c05041b4502c80090100700782050410f00241c414255082107455900e0080100c000c0c12a90704081c0000c822a0041d514010070001912507903504010301405150b025500e01c0310b401d0403400c0c01e032405050069056402000031480c0107145070b1240390f032004491845041c4440380d0048608050030088010b0006a010481c02c042c01185c4c41681c640d25a030b4144160041c1010340d20781c0305c000401d030703010748200d102080d00c02503402a90307181c48003629400d8003000000e440c1e150103001a0068003440e8080c3c0801400424503400000b020440003540001121107640c5690040c102c10400620030040aa115640000066010000380c2100c0d4851980103403a2401c0441074021103000030801400c0020600702000b0300120481280e0540300e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 438522958 1250 438521708 438521711
    0x501090902181302091e0114030705160606030b07020a150b130504020301020c070b0d060608060f0f010509040204030602040306050f071713170c070b2505070b13030b2206 75
    0x12483d4884200902030300f114260405181058610b40300c000321106006e80e0405d07211040004000c902101160000b1103003400490010468229662140e40d203c030000c80c802d804c04110303642c80382d5071a003018034143c4603a80964064580a0100300002464030740124205000f0416803101c00006842c503066291a90384d02076032800814190340b0290101c49030005908219829039a860403001d01c194403469400d600e0910f81800802ea0502c145242401588014003000c040c0c440e0604001c0c0d0300c0007006600b070502608021144140d11030740040d1000314000c03040107880b00e2070343c240402a0344c0020315004102d45548100f046042c0c10001a00f016420740a940c25180e407000383d0a20204810940a080e00c1d0018840c480c0c60b454a200038410044450b0030740e510642d5944a50b0030345d001d61604a00d54020f0000104400340f2140c40700071021b070145049655082e40e41c844050b40741d000305a041c407019030003d41030050158001c01035800052400461088100d203a40c0c2081e40109270000510a9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 438524208 1250 438522958 438522979
    0x11a04050f0a12120806060a08060f01230405120304030b07050c070503012903061b0f1b0a170304020d02060f210108010c05031608070504090e0601050109090218 71
    0x10340301d0600b0040074003a0f0321800d54000241d410711007494914220707100c00141005001402604044054841074049510f86540c503843e04030030031404440115059040081c013110070015100c0a2070355620000c165800c40303aa07141440103004601c103440300341140b154000c1104000050510703580542c0314000707190182d211003000141c242820501c1d07024903171540c00c0002d001d0202d0155246551240e0b40744030000c1c4c0c05060241410748a09044640f000c1805c43c1a040c1c89070010f0800080585640e07450445161880c242525102c55001c80d030300804170fa101e103240c40304006520885180c0008100d031201c2c00c40c9000c1e0b0001d440030107417090080c090038000c00c03160704403244035043c0c403503a00d400d42030031480051443c0c92000d028000d2103104070382e60a00624581150080c011203004098120707402d02c001c20000010350b14201c0c081d03c1082000340030400024605003038419100c50701c0d8410302614a80d454840014592030080d0003a9072564030402c0500d01c086079140b03034100c6002e41514a40f00d40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 438525458 1250 438524208 438524239
    0x30f050d0938062206030803060406080105070c0809032b080f0903030402010e04090803070c050105060109030b150102160306091b0b0a110c041410090c0503010332030a08011a0405 79
    0x150b0412212201c132850a1580110420983c0d0700a14895034080d40e080111a564903030039400d03117070240da81034041110140380704041100b18000b0b0030a184040d0458450745251080f1103016001d00d0000000c03465140342c0c41039840d920045a44d000842044041c070039041080100d6101d00c00604002e0602120030890301070f60b01c03540c002c0d1041c2d40c1c105c081d550b120b2419110240c482e40329620f0440c3d4035460710f00061007941c000c03003241c801c1c6da821507d0001280d03505008030380c2031001c0c0120641903210701116210b9400c1904040c3c0042c600c01d4502003a003400c0351800340e003040b00641c10203903184540c20080c0250141a01036a072141c0e0507140c505008000850410b00303020340321180d503030043c2c1054800314028501450351800760486003081040030f0741e42c007800d80440300d4992410740000c004000410114854902844216501e450045030246c04545481015010345d15045110340010039072049030741d00031031172600501040490404a19201c1d40d5002d540c811400799034403845610080606 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 438526708 1250 438525458 438525499
    0x50117070c0605090d201002070807020918010c030b0603270d020115120201050906131e03030806010207151d030f0c090121030f050d093806 62
    0x600700e4001208208a060440340240c0b00c03180e40c1c941d000440e40c040800010014070003519000d003050340c03000d825041140c0c902180039500c585019603070003006102c848003599a003801c980c0945006809621258400e483e02401d50700d03c7e00e5003405141c9000446000b03074a620081325440300104e482c20038105504003071500c02e40b040c4e80c1c80322524444c04480c419100d40561007683c40000c49940e100600e50398008504115030301150003400100c090282d04542e05000c00500b101d91201100c200300c6544954070756007050034441181905401c048420014190000c1c2040d41048082c8050b0001a061542d0103c00181c118598800c00200d2014540a8034091450030002c0d4001410398450010588141d1ba840100c24205c44c4038152190000903840a00040700640250400907107083e10040c0e01e09403409a0490044030611070104540c009100580c4519074010388a14144842000d0a1442c61180c3c10039a400444400307898a002003840c403d1441d00350720580417100c040d91000810200e60 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 438527958 1250 438526708 438526727
    0x1090906020d05181005010b0a0c0227060f09060108060609041d03040311100e01030f0b180f07050a20070e0103050c011407261309091103030405011707 67
    0x11142d840c2509000c021540d0341c1d410031160b140081254070100130340200604449080c811201c00b13002c20002c4c040b031385d0f024030030003040c40d40020a298040811402c600702010321511640d11074580f9901000350703c2c5411039214071401404e55030150703c1d242610001c0e004003806030079140314860120381d04009540e0b40d001070105414205c41080c251000f42259580c0e5001400300b1603400320844000382060501d8902c003010048940c5d80c0181003030302c900054000f8415040b10a02640d183d9010300c89548540c2400f00c4456202c00010f003862030645180c200c2d031034010744a001040f401304a02404039034080d02c400c2842a514040d170040800710b100292909c2c03016803105881140e10000041807020108106800301000e032960b100e06040c000f004c4c5800c2c8201007004114008115503a01c500c00c2c0043c04591800030751081a1822204c007402c6052049164004d00c85591510700e1103007000201032006242c114260020344c03c1038140000a414000c0400d1010b00c200da0b001c0015580c07d200f11640c030f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 438529208 1250 438527958 438527977
    0x1103040f022404060c1a0c03040b090304050d1b2102040b030703020315090d210209040627111603080c160b090d0801060503060d03140a0e0a09060501080109090602 72
    0x1641c542c1d5400019044105d040c00503213840440c1c0030b014840c0003180d810700e403045407140c652a145540d269600c001a01c4042c100200d80d02c000e002c0494a6250110489081400780054605203010098210080c902e0307900101c072007000c00b000800da000049a4901c8807a941103a0108400014034003080c500302242d0720280d418415090380301e2080545009542c014034401c025207240c12441d0720107030744418100c00200605400754090032040c5d1002da01524010b0b0000300040317031a0f903454021004d1000361125200c041c035410482d1038828480c6100300c0000c208060701042c20b02c00041e95080178807901e00409818400784c1000101c0101003c3c08542c5043c0c441d0001710b0860f00b080c01c00700c600c0700c2c085510f03080c1c510807a1700406003c1d01501690b0304075003080d43c541d03241d41d40d0b04051081e51500c10404900b402040040c1c81d601e10380f02d1010b88041c2c08155504264018140300f0864048081e80c85014502d140040511081c9d0b40700c441d41c1e0640360690004a40f807010707071070050002d1184000e138 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 438530458 1250 438529208 438529279
    0x10020f09060d0e0d0c030c020913050d02010510080a020f011b0b160905040b030604060e0a0c090509060714070209060105040504090605250e0d03050c0d11011103040f02 74
    0x220040c00080c3d84119502000b04084503800c8901050036074000c4003003070700076021412a030002c000500e4a0050141e104e18042d1015001052a41d5400e1030910040c4200015075102c8041110049204411500501c2c818005000390207030368001c1114100302c80c0806042020364030814110701044401021129400b0186070351529000b400c100508440110f058000b80e01030b000001d10345080e000751b0051301030080c060b14035516141c0d1828001c000100458900c3d01403990080301084442e19084010b0480000114080c50251350b21420043c000b00a941403065035201401900e00341c40075104542d80c15603d22210b91105001a03401d07001d2680b100d640039040100c0c0d0020000240c001c6800fa24400e070314618019039070b0800326078584140c3d41d83c60001d90070050f240704e02d2a1040881200c03d01a0030321a150400c11740c02141011940b084400200f0280503034080c83c004c0910800001008180041d8214109551a06241c03903003460702900c50715030640202c460710261000900c10101c40005d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 438531708 1250 438530458 438530467
    0x30906030a1e0203070e040b01030b0301090302010b153a0e0a0506070e061206040f0510080d0512010b0309070e19060b030c19020307022e0306050310020f0906 70
    0x300000d0080074600d101c04401c6100542d10b1403241c0e0003568040c1c18a03898840702902c0e290148001007044452380e60405071030389031462291300c02388180200c060181e070011440106c10700a1003107884001100300944002000030001454510340380c007001000d0303002440c040e809004000d01024460b41586250145070084030000c120001175100000b5100340300341c8000342e84901081d42e48180d044001078205004112800c3e0120702c0c4480e05a115400910001c2c84601d4a070003a0110b070000c03121032258140e41c00d018030041a0400c10500503491504d44940f40249135691040122410f101c0c2c17080c0d8160102c08a5030410b024490308001c0d011020299000e07180c10f08840d07015000d20818a880f46240c500c2c0411071807042011a4819550f8500c102c6c0f078008410705405c000100207600b001180014420702c80141e40d40082d020200040c0c11305083c1d02e00300800001040e0316a0802c0e4824140b03488000c01064401103119600d05905ca000143c46036100d00101100c0c1c0300b80c05843d03038099400038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 438532958 1250 438531708 438531721
    0x2010c061b030507030506090603070605070201020124050a0b0a09050418020301090b150a082104030f080a08071b0b4305120103170c0d08180a020108040605070203090603 75
    0x7403283d80310b21125501030240351a0b80b0140002080280c942035003541050b002808203038042c1d00180211403040c400003c00b10b01c4c0200704a42d002461400a0f0040010441001a881d200c02204e0280204240c048d18040c4402d5001e400395400c2d21615028030b40310801c0340d80c101004001800e846401900034011043d803454250f62804049a18503205034035100d00c070035070382403503c2000d003503039044d800600034409211f08800c122000640d903e041c0319420040400041e00d5030303458680e4548115205a180e8001301000303481410000c0c14a400c200300e8100e1440c40d000545c440820301a0001d03184209512140744281208a600c00b004170091900c4c1514442c90b400c0c411030030016010318500040b04800031104440b98402d00d508868103444e0040180f010038000380c41040b4409103c640f061a05070090200b6041c50308044800000c140e80d002080780741429000d042200035031107000b43c655112594006007880c1000b8101030f08040da1040080d034558000c00c210b5440b0680100b02585902e00603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 438534208 1250 438532958 438532961
    0xc030f1905040c090608070e04260c030c100b1804020102010b03010c0809060112200604030c03030302090108250813020a08070f090203070906050a02100c170906040f02010c061b03 79
    0x500c2690032541c60440001000d0354041f501e030050324001d10310a1896160340c0c48600340300a0003000d420341924040e120b043e403008031400900c202240140030b540c80300c00a950702030508154642c13800c1c8403428551590041e0ba180f8840b400782c1d03218040f10307441036111030004078018134000006035015840c2c04101805a0b4000c4040d5108038001000c42c0c20311382c0c031441c1c681410130340c401008000b5889804842d40f044080c460300b0b026140090704c054140755030b940b01c00d907516107642d0050b00440c1d4001050f0320b50f968007a144070340c821002420400c0030000c03400c04079001c800070b210510411000d840800c50072402100e10034034081d0014600d504d1192111031258840a552044081b80c0e08600c1c000100c1c8091402924400c4920b03484030b100b40b91402c10b00f600d5590068041c0811805401101800c4c403103184918140d060090b5181c1c2c500302040280032100c101e000d010000554043c4040100094207149a41d60f03040c0c0c20300e080140c2d24030030b252010150050412800e082d415055100c4902c0358103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 438535458 1250 438534208 438534233
    0x1c03151701090b061503160c080406030506100e030c060a0c050604210c0515040203010f0c120b01170103020411040e090115050d110402130504060f080601060203030c030f190504 78
    0x30f5141100192100c100f0050805003c17580300a41c6a4144000780104884004c40f00c4041e400d0704101112088960704c215a40e44550800300c0420764400c2441072604004485800190117070402540002e05000000d070b0307604485240a20580c070004480385402d2160b012150820703401011074203207060030300d03040214101803040e00002c02c0100c00d500160603c6514462142600000a040f516004156442424500400a9130599202c0c0c00060328014030b8882e002c00990303217a54900f0354103504000301c410384150351503550402120341400301440e12114400c60440c2d50464001030b0300030588203040c02c0c60080e0751003001e0b1a1101d808118620606410980444445245440324540c46900f0000b80002c090406006030281d51003803050340c102035006015034003118401c6205a03a071030000409540341c0f40c10450384480240300400001c20708001d1240504000c2c00910300b1854940e03035141d4180401020883c15000b40c1c4081401840d5485200721400f140b080180900d103450304204144044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 438536708 1250 438535458 438535463
    0x30516060329040c0e09070c0b060604180e160e01031b180c0513080309030708031603180e151e010c080c1e060103060e1c0315170109 59
    0x1d2044806401040e0041010302030044105191440c0200003071000500381340890100b4028644850f00d12640c4108601e07200e075440d039503940c3c0c01c9081031904100c100c1c4081c2000b070142c0c409101c00e015454400a91004251042d1000140b1200300b504641c078121942d06108480110b072880490ba01082868540c16a80101c44154405d05115030400040520f03220b525140f2198000d12080d5140503003129030151b41e54980f80e810008490140000c000704c6901c51152a1310028141e00b4609040c82500001c11080700918204299800c500307400c4012031388010104070000000054111544405001030500c400008601d4075003901401c01d1900c200080a218a012400f400c038402080c0a4205440c001030392800c02e04102e80d40c442c82c180d00700c511551008c0c01440d03240b98000d1341e145403035406640d5a00c004d00607540346007006d03411505441152020b51700412401022000045007040c132205403460300140e8010940c22440b000301a5030002140303070007640309801103001c05401c0314813501d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 438537958 1250 438536708 438536711
    0x206120115020705060f1602030708030d1a03061602210a020f0607020325021215010807050612070e0a03030908250e061507061a060715020c01060305160603 69
    0x480c070103090fa40c450080c89410381c018401c020030706090b42e4036000303000c0b040303500e40a81c01d50b420a640020300b0301d07280d504206010707070002c034000300f604095024254480301ca5100c0d1a69450f6450080f07034844c40d005081d0351800745100c61054080380300700312603100a100b2040761050004d689401600d00c2d4080041c6c81c0042c0300742c84650303211000225440b80907054540080d8500060800381e00444e0754429400c7d801030038841a01d40142e01c401d0541c0001c40d00313403400762074100c00407000d14444400c10f800c602c5c05a440040c0510803074441c1c4045400806001c0075000c425941c80360b04540c109440046071343c0100082c0350020030150804910000c0e142c040080d15002c2007140324a0b62500e242c0703800b8060080e502403042000c0b012448040da04101c028052140503040c186440c0c80704c0d400f0303c10450701c041d5036501000420b074150910310b40910088816078541141a01d03025007608484000d1541ca07136000a40ea01c07440300940c8100000c640c42800d40d504403150241800303c103501c4d441543d020a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 438539208 1250 438537958 438537989
    0x80c070f0b0a0e15041a0a1e1b060b03010c0825090302040f020702030d050c12181e031002070c080307021806180f0a0f020a1b0f02061201 61
    0x10800841a6420b02040c1d94807a080f04042808001c000d0310142007014a00c1e2041101003800320080b00c01c0420440d6025000f43c0d1b8a82080c00200344042201f079802030140044204214280e2203c034a100c4805c0021350301d00a2500b0f42001e1b002007480084286c1d140d0300c0d0941c84480e181d009031403644560007421100030750b43c80c481160a0981078421410707000541000c414001490950320000c50061100c0e001828a109540031a10300201241540d020490108030a4188001001440481e0110f081698106190b00014400d64000508000c4c85000b01b03900040c1e80880800c2803e60810000301240c428030200c02c81c000c002e501629094845421911010441c400c0c00000c458281c0e601400103100500c0708260a5100c000182000760b01c80c4451055200c100c1803108058050348450241d507160381060013456049400000d1210140d80c0140302c00e02a40e84c0210503440e50400100240c140c00d078940c81c00f40d2203512940e1001358021400b00d42a0146c82080141c02c0c180c03580303845402c400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 438540458 1250 438539208 438539219
    0xd0b0a0507111f0f05010e01090623040f0e010606120b09040c0303080a150306020901080901060e0a110405060703090512030c060a1e0c02010c020d14030f0c07080c070f 74
    0x2c080001c148601c26900c10a40d205081c1c44841c0c800810107001e400020314540d40d18511029120203038014034001c2d500c4030042c45682c005100300e90080905c98403580027000f503107040c0103c8443e0761020a00c202d503200c0101c10750030702e42c0e08aa13407000e00d01c40c020003000f601c0e980040c0c0690780213690401d84a180070070155a50a0030510f80d40125002840c0c41d8600e4950f0b43c045503030b501e0050100390319a48070780b500503100c14031101c0140518070808000d07032945400400100110300040560a0680c1400010000180081c01c1d80307400240c6650080303200d4403404070080c103522641c0e112940207080013841d00305250340401840142c8608444400c80e82040d5540640da07070061146031151a0041e00100e00c2c03040481e4070024103424151488006132105040710000c8904136518140541d446807130070000107505000c507455015103070a200052803195503c0c8825400f0042041054100c4007001c640800d6054040d25999a801000300d566812000c074996103514485c1b1031020021080a8007148 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 438541708 1250 438540458 438540467
    0x4050103050c060307120504050c15120c0903070509010e04110108091015170d0216140405040305042402061311090411030a0813080f03030a09110d0b0a0507 69
    0x100c075000401041c03064000c004120311503001801d4a4180441c51103e5120f82d002402214490b03802100504141c0d0440e100b031006800003000c5803148a0801c001e444108800212004d8000c040e02c0d401540303802c040b1000c40e141c5455900000e9100d442709000184d040000301c280c074401da02c242c000c010301036502c0c001501d0180c0185c0b444c20182e04500c00070100903007664044011103015500141130f01381d0711420090115441e51040003144c0101042030040d41d0100f1a032100038551510044205160030303000e4860360803140d00340d0701c02c94440b008201814841d0007a5400380c4030752414070780d580004140c1d1006488800c0000c0780980079800019200741c580558a1720034a0300008041c24059480040180441000700202c4026061054140043d101040f0b0b40d002503101e00c015503554021064020101c0e0350301d0b848032207035a02c842c0001c4c0340f8000100580303401598034000420502c07841d1501500302807002440701e420465001101003400300f0030341500c5c000e001c00030042290342c0310002d0440d0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 438542958 1250 438541708 438541711
    0x20d3207110117130c0e0109020903010c0e010e150c06090d0e04050105090c0705010e37120f032009090f010506190e0907030e0601080102040e0f0402011e02030d06050405 75
    0x100f0600007900000e2440c0c500f0745924401078030620341719032941d44411103075460700401e80040d11200d90100e002c00c5c0c541400d01c00c200704804d140c1403502402140d000000c15010600310640d020340394440b41c005c60142da8600303a49202c009001510f1003490401c80c403039a100140e107165800600168144110f504151203814169040589800d0040d038070324040070050b074403031402200e0340e65075541034202c1501c0900009940140b000b89400c56002c084403100e030f80c004800d01021103103003020740800009903514081c0c0e80000e001d0a19000d44038484106800510113921210040085e1115046813214400010419500103e402082c55151000729005c403003024003815821000401c0010000111071031000b030204100c1c5402c00c00c0c2d03007611000c15801902940c016001c03030746a0750718410080c0140007407405854144021401e05181c402c0180d090764002d0034190550180c0c80c0414156446000300c6000c1d89071003410b840c2c4520034600d0003540c0c0da2081111805c0c030707440c1160200301c1e413400d80502c0c2e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 438544208 1250 438542958 438542987
    0x140d1710030f05030702030a14070501020c1c1e06050714031603020906090a0311030c0909070302040c1e080907290313020d08030f1006020d32071101 66
    0x30441415540c034141c0900003640306480b5840103105040050340e00b0040e0042691050030039614100c4441d08107440c110300d9809c030700d040d9000118800029150341c14080c41c03100c50101c1512007071495050541880030303056110610300560030081401e100181d00114040c2c0c1e4035588145103064180c043c5012800b0540b600c4501c00c00c1404500b070124802d402500725100c00a140da40382403103270000544030005c9079004580e15030807482c03608040d1034280b020b0040440103480741910f52a00080041c0c4890311070000a10480e55898103801d8240304a4902c2c1c50b943c0342d40b40280300480680c1014060300c1040b1150181031080710b0012401c0031180d52860740c03d444031811170f1240007084070b00f8100c80d00001c0c64144e000f4241407a1001580d5005010221140200035156481c2001c1446040c2e01c43c0090070f08a010070700380400c0182030350001e500c524445030b41c54401d50412001da101540e84540d035010910064640c600d8111100000e00100400351090140503e08100c940042da01051540c506 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 438545458 1250 438544208 438544231
    0x80c060603060a1109130f06030c050a090902060f0a05270405070e10050904020717070308010b070221160807180e03120a0b0402030403080f18031603020a140d17 71
    0x2c0c05c841341854048000404000140030503900300e0a61618129032580d44151810840702108102c141003102060001d00200d40050000d5070207134006c81c02c0c0d4401c00ca000103128000088502200b0321490513611303a59203c505804410366151110144442481c0c41c103403040d4540801b0030705041c0600580c461059000e842d088901c00c0d5444181d815421400c8105d80107030702001030000091105070111681c458415442d504d81e0304a0400400c1070b4816081074007512002c0003010b025a1b01da081c0d124240d4058101703070301d1450855455078103100381d2688541c04400f0b01000800c07486d20114144041e9810b682400c000d004e207034018103041d14060150445150402c101550425080d8180300390312040c03005010440a00120228040340d00c122070503000074001d5424428a030400709881508001c000e002540031148001e07210b034403172090704200c00324484102100420103000744981700e101900517402c0b144821805490303030344800841445000044480d04106104144210064054012020b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 438546708 1250 438545458 438545467
    0x90b040f091e0c0323121617070b04050706030c0509060d0509031b1c020c030d0f031107050303010503010c110c06090a1707051c0803061309080c060603060a11 70
    0x800881040c024003d03151080f0080c0003001081036207210040d04150318600c60030b01c011482e100390819481e29100c403105038003048107140010040d0098034590380c12003001e010884802804101e107125000005080c1c40f22101080700b07204000c20503008990307082e10148054003a44800b1030752803080241141c8d201109210407003465590303503c41daa00511001c12246000d8012442c20980c0050041c60701d110b900400358445a80245100d80381c25844600080c04c80c2e1061500080d00d0f124019201d60130458001d110003519407281d0010000d206120504d03607540e1722681402c0380c83e030303009010342400382d030802c88221000340c41240d84401119070321016000e0b03c0c03107030020409a0340c0080481507120b0302e12203020644000c268040030310717258854020820316190000740444503101c0c400e66103485010f401c0742c90110b1408801c613036000f141280e1002411400031803820003002c01c54000b9001100c0030414803074084000400a0141500b10200c0380c5a5440f01d00d284103894402c580006540e0b804e22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 438547958 1250 438546708 438546743
    0xf060501030c05090904140a021302131a031f05131406060f0a050903030d02041205070621020706060b03090706170105010903030309140f030a11120301180e07090b040f09 75
    0x42d03800507c819140a8816960310b903000211201010701c070114203d6800a200745c60802c0c8102c80e407000b4031480030b1000c0300380984845040e4a001c020001c003010707082c214100c010341034482211005440c00130600c15404412406000007007001294809401c000d50000c6111807a042040e25a080c24540310b8514210300e00d0400c885541040c0b1115415200a0140740721000300c2d40080c20180c0f200080707114a0341ca05040952410079240c2c80307101031044490112040303050055054002c100c00c4140507a49401a01c1c00c2c0c002400d1540c0200c00344080802845240980401c0510849209035031741200312000e80102d0703000b54020311419000c07492401040000038000e41002213294051858010340d07003801c0c0e2000b41804081400301485410000d0301c0000b2581048403003d103810504000c100d00281031410f0030ba10311041c001c12002900a19485600c00c1080d04608440409074042daa21a0303523410380007001d0030040140b1880383c0c0c1020b0341c0c00d40c000e00500c0340c051429005a0091a8011006d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 438549208 1250 438547958 438547973
    0xc04090612020f012a0b162a1401110307090f0e070f030b030d02030406021203160c050f0f100f05070f051605010212100f06020a170903010f060501030c05090904 71
    0x805148641050f802041448141791004540546000d090112060300c3d0501c48070144010315011001070003982010451291028800100b0381c98010076001181c3c099400e0076a0a203420015505a41d0700302610800e408070b500c0045e50054049403610020f850700c41da8101c1c10340d2014001c0c00001c00d2403e000a5105106400c4080c4416150038001980102a0003182c00c2a10100c9a0800b40e0f00009080002c11380c1005a4071011061545c55411170500d6a82441d0380061040043c04100817500f5580501c442030168088038850364080342c0c005096140303071a8841c0c3e5490300e5151041d20b070814a0385a00902e00525200e4507940d5039040340354100c4001901c66810142c510b90081d041e43c40792000042c000d20080c080e181040300e0b10100392528140034a40280c1c141c0044510040c1c07200c08002d161380000d900215540d1003201401e1075001e0382402489030040c0f060150303040d800e2586100542d21b141d0301050035a031082e40d00b40114445d00d58141e42e544500000c56400034600d02c0020040742c0710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 438550458 1250 438549208 438549227
    0x1090606173403140c0a050604030503030a05180703121701150c0804170106090608010e030a030b18010b03071205010605091909020403140106050a140108090c06030c04090612020f01 80
    0x541c9410040341d807a41c1328820100c00c004001072241e44004000280c0e8940003c650005141c00c07540e591404d0304554031161640009040e990b61240c0314008030703080c09500a0a04110401c2004513200c4a03541c1c100106605240c4c0c00d03120200c1e419416406c580700ca03910304641650000b00e0341124a01c220f1034115250301c440c1d00180c9001409010100b84405401141d00360007595800200e0038074103112042080310042d60104542d0303850441e680b41c61280200c01d55030320030114100007813980c2c0600089400310340154020006231502034008943c610715500614001c3e4442c2e514420066141400401100c5080c060480480e405215101c284e01c1c00301c0c2c0141700c40c0d202e00c8036540700540d5800030700144d80003a00201c1c3c07402d0a25900c0f850130303a0240724210042a044500394445031601589143e11750a5040340380c100840c00c0002000700d401004005500e03c800f8294680c1e92412000ea41340d1a0040e010307030040e03141000400500540c10000c00c040e4950010030481a50410f4001540c03911807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 438551708 1250 438550458 438550543
    0x40e060d06020a180506130b130e010b0c0609160b090406030803010e160f0c030804060902030715021e0c04020307091701020d0506030a1a180109060617 67
    0x1030300c00100002454034005400f001c01981ca40c1080c40921204081001800b604410f0280c8024489480940c0c05600403404030b0f50141c0c1010743d118500910f0300503602d4190400c40390044104000034105a03860001c04100007448140c2e466a01d404401d00e454680e5010802800841d6a40c1440341e400024002c1c90304000007000011800d0ba2596088101c0c1c009a101070000c1d03a0800070040510401e0301c40c00b08100d501c1c80c0003082c45035040c4018040000425001c0d08003d01080040c0c100300382a03000100160300201207450f81583c0c2d03005140740c5240003080e100117025003840c500c03070447c9030074900031080351407400b90682ca000c2c101403000035040103040b4010010044000614003003111a4040203c148000240c0d0b201004080e0b41c003680d0010742864040e5020048950202c2c03481340015000c2c898101d4084044d850b0160003622103986000000907075403178006050708101056000134201c590482c1041d034100c0b00c1c00c0034562242c0c0e8021114001d400d14443c4101c00c40204005a00d5450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 438552958 1250 438551708 438551719
    0x4020c06070509122b180b0322061d0c03070b090406030b040309090c050901050a230406090513090201021504061d030a121e0b040b090c031009050c040e06 68
    0x295585040d4603084d139250244a049966600f100001c0040c0c0d65800640704060400803100018540b61b00030010591007084407280011001c941000d03500740c406a042d070003513913a8401c2002c80d4180b41004006142c1c032005c1d410644810074080010200d450001244020050001c3c1d07403505900883c0c552080e0340e8164025079607080400000c040f82e4409000714080e6486074261800c184003a41126007150a28081c401d00340043d400c5c0d682d2000c00c80300d00a010349005c40c00b080d400180d55541c20804200712100c58400300b00820340541c0003008000b00c0300100c402503c484428202e18040720207101001c0e0042c5c0000c1e002c61446604090100c1e0403e2240c200059010311b820112101000841c2c2c4600580d0000a4062005603020360010800740c1910001c008445195225145074055584880b4a59445884e4004251345d646c2c13010280e40e40c0a01009010310f003945504017039130320456892207002d91103a00894152142d215a40c811450016154034007410070a6485944400a000d030380d101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 438554208 1250 438552958 438552979
    0xc03031a030a0302100e0601050f01050a021f1509020403050c060c0f060f150117061302120a060807060201060b031b224403070602042304020c06070509 67
    0x98404001115071039000340d02924503080c1701c015040598880c114507000e242d002400502059980144a042c44582400c18507500c0c0740648042c1e04111800c035a146442c000034610351710b02c074413075080007819001400752241d5242c0c464115000f00d00030b5020142440d0b02c54000030303c0c1414000001c104c0c42d80c4c0b03e01211a0000d19400e01850700d03034116095000e0101c6002408801c0204a03401104007009003015046038000903400608110010000e070b2144103540302031104500e043c1c0c110f400445c00301d0701c02602072400441c4040644080e1045034882e106001c0700040061041c440c083c01d403119480100e241d512509103100b10001c0b0040300e140851010880444140c100380c041103951500b210410142e58503094000d902019007549100740c0100d1090042c082c010707405509602d0050351680080c0200b01c54400c50320714000c1d00401090144006070115440e4003000c04441d9400c0b1807003580402c14403000510099003d0210454035540c490004120070b01d009070094080110081c0080d00705 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 438555458 1250 438554208 438554261
    0x504020714010f0c0905060703021506040b03060906061519050901050405040f1a030111030a050919140105250806060d1a2407030815041e06150c0303 66
    0x31150b4940c0d00ba0f5800ea911044015003a070050100002031400f200c0860404807192400303074803031803009107607a800410240000d0096540790b12001d0000000f8044038602c0ca40003020960f64003050366814440c1e4081c907509020454071008580c0711a801c05801940d0281c0054259000d4200c43c00b0b950500c04148004100350300d07180308400751401103c902003030248002d03008801c11001e00d0740840c041d904102d4441403000d00030302101d0f080304404500045d1643d80c0c500c21801c0503410110600c804800500040612403204414400905a03000030000d03911020700703050040401c543d88844604504000294890241414035881070018210034038009010552008444c1e1048415450b0849017115120908010748500089081c40984443c9680c407441c1140b0507000303401000f0704001ca080c0018021240c51001c40c090b00130081d0007400300c803100b002c0c041d40700c0e00106050314082c0c0c0360650005002c01e825080d00d20141d050785a00ca08607449441c00c034081c0c012611010288140740c1c007214032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 438556708 1250 438555458 438555461
    0x5160326040308030702060a0c030203011202060c0c090f09010c0c0c0302012712050601050a030206121306020706020d0c0206042307050d0b040201090605070803130f0c091a0306090304050402071401 87
    0x204005e2540a01a176140101031201107a0309000030108161052005000c412003400340b41071070035011150f03107454818885105161010f0480d030990006005018402180c0e0700000680c044e8003440028004601308000448020450000161800c00080d40402c00355010310100b00044113807440c0040c486914980d0300e030f807003451603004c881c0d0b00b07080894140a2103400d00c02240500b404403000f40c0071313901c2d5800041d858092604d85032040d512010110b604036035121400000c0c51342c0503100359100c8506003003080080d040f150030060224100900130392110b00c089125032246500819405103140da540038411040c010f481301d000103100d45c9202080c4c8bc1d5650f0515007071b1911502500d8014a0203100045c0401120351100040c0103050000070006001d6809030b075800b204c0c001c20f200c0c02d44135034108007086103849040035000244a200c04500e8185640102044843d05d40f0300c01d099081a10a065884100312450b102a8001f40300070310540c50142c0040030500d018004401510842d08003950 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 438557958 1250 438556708 438556711
    0x90312010612060f0509040204022805040302042f130314060907051005042312060f06060c070e060a1d0702010b0109050603041b08010f020301030516032604030803 72
    0x1002c1500e801950458900d1402488040c02045183c50380091070035011461801d4042c0000344a07580125083d15841030302a4620b16a0b906070928000284409102800680c401d0100303a000728203002c0e100903180052608580b20107160404103209c20958110400c1c40d0304112112000100505000004aa80006420408004c0d240944681d041240c0381ca460700e000f96000f140941c20714148820710700c0c0c2003415078084a214060028284412030184131585a480125950200c660600c090344568005550343c40f98500b14032101c0c40b030f00c600007003000c3c0d8025040c0a440661190720240580b544000541c0d0b003122018101e0040291034105100d50040f44402020f02c2c010014204101e550382400703400c01420342030909018150401c0e02103080f9200007440078001030301c1ca10080c030410307481c2c80018008040b450020010b14411005c0c40029500c2880141e40c107100340ca00c80076103100c0544a07002240e0340240000b5036009080c00070820300742c0c64a00c0041c003080901c00040400c0e170301c20096 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 438559208 1250 438557958 438557969
    0x9030102070809040501170709020c011d0a0c0503070b040911190c0c060e0604030b1008030c0a050c120601030b0405151003050d020604050309010c02060c01020a0903140a02060d020309031201 84
    0x1e82c83e40740a1081c0000c5900580c009080c0d20204003409138002400b28070b280569605d60009603a0318550045240541880a100700c2c1c000030001d15a00d0089010810300b60040c803c00a550900b6694030400d640c0340468003035502c05003810482000112440e0f0700c06000070f11440541070408100324400324211110f0b101c000041500603600500300316040006a002d001c041c102429550410380104000d0300031030200414540004e80070440d04008841040300400603035040300e5544c800e6030035a0b5100c84082100b102c481c4148074800d5041d20701001e141c88103150650007480706130302e0354a4000790b9030780140068031540964075400302e00d81c030503402140c400c40b070480c40b4117070072855460010f02c4c00d18100513500454006e0307018040000c00100459003401e0003481d02840078440d9000040803446000151307a02513100080340501c103038200c03400104690242600c60744241840300120f071140d6031158025800a0204088881600a0350285030840f19038001c80e0b0511030300710941c4484038000c0c0c100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 438560458 1250 438559208 438559223
    0x30e0d050f1c0f0902180106020d0c0318030c08070504020c190c12110a06020c0a050f180a1d070b032404140402030c0a03020a0b0d110a11010605011b030c080903010207 74
    0x150117504043c03110340d42c101d4103600c0649040d858544000e4551030808002c40800800001d10001d051145800e4119151006460035615590f072510003207081261180340c046018000c0000756034a0203100382d0300c2d400303c20809411013617414100300c1e62108405404a40c240d00103000840d00311603080860a06034132901a02c801002070000308183d107552540400304550000000c0301d55070312f40c40a22011a4419111019160743d010005603212540c0c01032144444c50040c1040760034903250b00b2103805002e8040340a6a60100c41009540f40e00c00380c00340c0301803a01c0420204400843c0c90140002c040400410110181c003840c2c009000d6032100015070043e034985070240030541c5030502c090101e802048444400c441e19541c0418841541071040b0340e10540082034100d100c035010f03000840100f14445250340d65042c0142d01810a890071108902a036103401404145540102484540c00c0d07002d2008040c4c044540c1e9080342c0200703403010101d405010078080b0700801d4609002600115216691 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 438561708 1250 438560458 438560471
    0x180204031104050705070f0303060b0f0409110412080a0203090a06050319061a090d02121e060f0c0319050106020703030806090112020d1b06080403030e0d050f1c0f 72
    0x406510316421014241c0c403607441d04050046445d0008212804141e002000050041d500d0900f0b030020540c1d1b6000d0450703014001844101041950010401d07140542d42c10400d60820290130300c0b0794000c602500340c203898100214000702e4030103000b1345400c0200d40304503440c00f054a0003049590020f0390005001c0b8801000348401d40540075219460650b1403001046914a4411885c81a840b180380702510580300103182c00381616404000c1c140030b074024080e90b290f5201e2191b200e5031101319011403404121080c08000c003152000c5030490203080d03408080c140680f68484c5010386588040c20303002c103100c84841c42100f410001d000d041d00800c80d5401030151585942800307080020000d15551140d100880103011a0010b5090b41c22087d40568041b0804100c40c90000c16159030086000d0440c5c040400001d291544a18054412031080d40c0c140040450700214541d208650742108002c81c1e02800b200e002e00c4070900281a82a404940d0700106452413010141103c00c2c89500c640700645944 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 438562958 1250 438561708 438561713
    0x902030a0803071b021f0302040e0c1b0616030b0d1406100b0c06040605060a0e0408040302011103072003010f050109090201090f060206010e0408040503060a0c03050106181a0418020403 81
    0x22000003440004281403076141880740d0004600310032008105a0604140c900d10100c6c600c079034140e03406401450041c8207542003142415600750404003070300710f01890700c0342c1c3d0f481d4042c0301140ea540900b0038554118040c10140c4030a07070140c0b00050360a508802c22001400114003000041c0702050031300d1004c0c1c2114101410800d80b01d2002e500035620501082150200c41a000101c15034010b03041140042d00307441d03103030004400031100d0303200040541403142071106200040000344102c1c0e2003600ca0508a00b0141150340d124010b046029000c0c82c0c01c0100a25140c0707540e81451101131008000051002d4405400d0f002c503078080e0450305001d5070f00c0040404550304055860050700c03e03803540e80340842c43c15a00139907070041405000c8610004c81c0201d010040700c2c00598016000080a490003880c2c0100c100d4010901c10403240e0019043c90300010b5018003c860b0144404800c00d8640400c03814855041c405a0b0003032401d180b9004100b03c0050710b4412000b490712810100140940c1d00e61550 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 438564208 1250 438562958 438562967
    0x1303020a0503070308040b03090118031701060305010312080a020c15010e0a02030c030c0c070902030901140c0a050a18050d050d03050121060b12032d0c0c0105030a0902030a080307 79
    0xa81000b03000b03500c400010300118681380709036412111321080350f542c0c80c3c2d80c403800d907405004140c600e801d6000d0024211010036411100380c08604105120420040c2e80e0384d14128180c078000c0c80064044c108040c400d044403441891559800070700024098685035001000a01d040c650b111031500c2d01d00f801c4014002500c48101041c0c100100c0b140550a41c180200090130074440501500400c5000140034200300806008000041458000442d180e260030340c07030b075800713071414149841403020b80c24001042c00c1c94903401e0b01d000800d59600d0317900f0305412890a403070907000b000c42e040d040300003140001216690f140500c101c2903c650042c01400b2070145014058034010380001001526907958180950320118018941b10b4201c1c030b01081103968140420350340d082c028101e403018000081d4440c24412845080300402002041070914044e021084081601941000100503000041d0640c00c5607c102e0256810084968000a02000590000c0e103052441036045451620201c20040c015410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 438565458 1250 438564208 438564229
    0x13060501020c060a3504030503090c040c0e150408160618030201020c0d0f060c1d0a0311090c0d060305010902180702122b240311040f11130302 63
    0x751111801c1049214002e81700c6480c0d0f0303140c8800c00b44e15030318400e00c0540b200d004925480c1c0c020f50311107050034603080c002c0c02680b0803640550244505000120301d41000d11444000212a0b62040e14044c294000c00c050f1181100f0388000c50b00e4140700103c0d1a41043c0301f0340d07004181d07034038140e103030540b4014002c0d10103400b1142008000c01940700070800f43c0d0f00480c140084540c2208d1f030003c00e5202d4900b034103d6040c003041c05000145456802080f150b0482c900904c0500c40d01040c80b65500002c040044003500c0340002019000c0210180109041c9141c51130342100401200b10b00308a501c0d01c54000b183d00c2588150341070303912490303400d0942c1040e00754000c403800310b14244e0751079207080c0c0e0010b542c801c031040b0751200d117800000b180e007800b00c1c1881c0c04a52041c0d084024a8108040d40005c00c003030107202420300d100f519419110400d24030080c1840c01141e600411441300d0807041010000203041a01c030132961942c840d001030165585040040c041ca91110200700b41103030550040c4440d0002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 438566708 1250 438565458 438565483
    0x90b03270f150f0109091a0702060702060a0603051002130b190801170607211509241502070b071406060102010614090a110301060f031a060703050d06051306050102 72
    0x14510a1100c0ca6800d4030320305040d00c0e082d181c0811b116101d441c06100d00511103011103000c416403c00c2c0070081da0b0119290b40038030700690840741c00d80c83c0c04000d20221401e6220050480e4040c01d100e00781d005242d006070080d02d0709103000807a919515120056146c0c041c056981c104007626042866954102c000e0314007512415013890700d10a521682c296454101404002c00d11201101103045c2c01412819410001081041030000c14008000b0310100c0006004203a0701c14241000fa80841110482e011201c4d024201070030142440d000b181c0c02500c004030224411409984070120381004040020005c50784a84480b025107040301c0d46607030808102600311411641000400c003c1040c100700740c5110008101e400d000d05803200c40080c4020302c040140c031034074807002000004a4170b4020700410841540b585003400300220581c11505507e03e45007020b507115606010050100340304001904a82c1a10440090304503200c0340000c0610016048151134603444503400e004035641440301034907084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438567958 1250 438566708 438566743
    0x6090106051302090a0b19030f09030215070c12091e0b18030c040908070507090c020303131103062a031003020d050a0807050a020a15090b03270f 64
    0x50809000882e94003a074000d108200381c0115080c451603860610703150040442c008001e584402459001c0040b2451840300c5e0046850000c418144032158050800c03441e5156000d803814102c2040c0001e0740e0307180984480100113004a00500148001141e0705c407094403611401482841d006200403141880780d03155510000c0c0d660200a0840c1c90703829126008050000b01000c40c1c1d414020038a000c80c4070f50429030140c103024651080c4280e407002020600d010b40140d404a80d1206002e8040c0c440a21050307005a008100180340c030854641d1041d1007620410807251045203080c002460440c05a0b10f24240d0741c440c680f19039522102c501c1408504003081c2403a0305500e081c0d0905040030a03a440003a0040c0e45070108031080110900000318a154880300d07903504d85070346040640ea1019081002c0740106546400401c208800364802c0501071041e0751005000c5040c0010f0070602c0e04040c0170920111802c0c230503094880701303002900d41149100e9000308107180341c01c48017034078181180780c8842151 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 438569208 1250 438567958 438567971
    0x1050a14073009091112010312140708040b090105040801090b0708072d090e040c0504140f070c0201110d020f06010f1212050d24080609030d050c161202060901 70
    0x83d0031160140c11608100c1001943e110b440e02410101e100e49071001c01c040c042ca000110420031504142c0014002c1039840303415420141034840024030680401521044080c0020000500e9540c024105090103241950401e60f44207002803c1d1901c00310308990115001d010040743c545c1c004e010780e50201c1c0c0da20f4004880d224a0040b8030726880e2064901400e07150b0080d030219114010030401005200001203417100d4909401c00003443c81c50b074010588254140000c0420000d90721403480d014a18000300c0007003d444a50055504e45140c200c220b060100c15074400310b00c0c180502000c0c0c3c2c00501a00540f851098140003203040a2050700800000f070a06501404260441c01c8007010003039010006005140b8840820380e505d00076195408001c608041401282c00c080251040541c298a00314034820f13501ca9602c55107900e41103550005545c4140040f402407034154001c00e8001d080c044441d0728000f40e00303d88240a1115140580e000042c035049100031660402075142e00015280080008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 438570458 1250 438569208 438569303
    0x2060a0213050607061d0f101406120109020307060e040b03062806050603040c03030314010e15060910020303010312080603100b03100e0105010f050a03050a0201050a1407 75
    0x910203400b0700d90107010042541000c200080e80608802c42000303070007411010080a002e561040850800022805003c441028284041c081d8060350382c0c000d50032861942ea040c092200401d28a00c0440d0f56640b209885030250700c06111001c041e0041d0365502c206c600014040c4019141c848078620b00992088003009581c03140c0c0340c2c10b000c0c104030920040481d082c100101c00083c6c0002d03006039078040301c000280810040d0b0280d100e8112807103610244427060351008442650402445201d00711265400080e0303180a1480425044000082001e402d1107880340101d02103c1020b4400c0c5c01691001005105120601c100d03000d45840701d1500700700d14502840840c0d204d50f400303400b0003019034990031000e5443e41e00380a000701c00c0014803410040a801024807034082c000c00e00c1092981e80349068003040c5801d1842e46c080943e0342040080c1154029a0700446495101d000780b20100958500065100b15201004001550044240079400906811652891600000c80418900b15078210404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 438571708 1250 438570458 438570487
    0x905150613030303150305120403140115050f0411070b04060506030a0515071e0207030b01060309020d0209060f0603010905161d0f030f070617011a19030f06080a0302060a02 76
    0x180c1c3c1e072601d00032408900500e005c0c0004066904020900d000e45008420b18003011030152046038050003024440403042082142211001101d00e040049404070604c42c0e03082c450300794410580b003d40001a0309144203c0c0c01c0d45600a080100c41c500005020b11003403069500032190098011800b810146080744d844554954052210070b1300080200002900c40d07000340d0085000440841100703101c0360840d0b400039151380070b900003150118031140003c81c2a40c443c0c0700f2031800940c05040e00c841c03201c00b9000c10900000c02080d007a4022000481c200c101d03150800a0b5008200400010420b401d2541d0300d00000641d0242250030840904541c05061500c141401d14522055685040601082002c642030150207810014030b031040c144002400c43c0d2028103000030000d400d03c40c0820780d80399500c0800400c8800c001030070124040c0b20300c0c0d0610801c0c5000140341c041c2420001003041103444501c050301c0259020b1200c1c0c2e0041c004090078035406000581e8003440c0c0d94000c6140100f5007900c0c60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 438572958 1250 438571708 438571747
    0x27041a0a03110a09050c07030f180e1f030c1a091c060b092a0f07080c03040801090c062006010b09040b0415051306030c060e011809051506 61
    0x806011141c129900b958903508600d002070000480b05014078a440869449242c1c0840c500320001010010400f05040c8038106501c1d544603403042000d9804c0c40c2910352404000080d14850001f03900c66091001c4c000a040740300d008600c02c40918558500c0e02050032407072a1a5071200e03e40540400c03c030070a0340d4541e0142400000720000b4601e00070801d0401e80006c081814080d0340041c0082d041c00000c1d41500e403803e08805036a0b41d2221500d6181103141224040d000044414690a00900001548000c00303031901440341c2007240d00f059a582c2500e400d40e50024410b480c2d81320000c0e0184a1250701c284058588009000b50303005841d480b0581995942c0b0500c9000c0302c0c1c0c0c101040000160b559078100c805144002070007408a402d6880084040002c203100f80307407240b041406000c506202500400c0c1c01c99420140ea2805140f070100141c654052001c407550410240707081040301c2c0c42ea00031100c405001514000079032403400e02d03450024801e046007480d105032400d100302e07600f4031a80310000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 438574208 1250 438572958 438572963
    0x81e07060c12170103061b0c05100c110a1506140a06031a0a0803040602070503060c07020906060d02070b1515160609050607032c0c011427041a0a03 65
    0x205900201e4000480d6440ba102c481d00091800f80c0d0000011300c00e844d0040040300f5141c4922035600881401c0a6844a1000c04010704581100650740f500800507408001090414200888008503984066003460382054044410551721760501c01503002d03c0c460040540391950003031a40449440000d402c2c0308982c401d40e410103860b2500450f4840e015408280d100c28082c0c02c400c00c0c0c075210382c505501e0b038029010b02c0c0d0051080b184001104e142c0090868000c074109000720f0310b8016035800f4405e10300e0000705070640001c8204400c00c908046031000f000712134091400c140103814603072a42c3e01c2035030b0500c510030712907203072406064004115101101d0035209103044101c4401c0c000c4c501030b40034007440c00003c1c000707025110400140c030b038158000a180e8600c5000d81200c07403110100368110f925184042140c6a4840c41502c40e0359402940c00752051041043d1142c01c2180c0300320340305011001c018103031203034480d500384a2b0b0f550706040c01008803c0b64500e10421541c0c0284021415010252102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 438575458 1250 438574208 438574223
    0x10e060d0804050301180203010506061201030f080412050604030f020303060102030d0203060d080c03120c07080901051606050702010e0601050a151206180204181103070e030705040501081e07060c 86
    0x3600030854968200e5000b050050024806141c9106d100e0103c0f00c12000180d02035420103000031541e1500b50b044641c00300e52103a40c48816421a11a51480d000180e011104500108001b107981500200c05241ea075109400601c0c0c14981441c0040a828200e0308100a5500c24030903c00260380110a56007001505800140c896136240b002608120107928060030181000420300d2804401100408030400c40c44250380311074540d403180500300c3c0300c1c0300780103004040184048942507104070020701000c035180004039204100354554008880082ea40400580c2d9a2a6a5450f80c8000e00c82a07004020444582c003129260480030300c83c0c02450350601003000202440140b05400590000300030305495a0b260710101b0300701c1920b8000350700c18000c420f0000720b500d15000e50071720140144020000c8009a01703003143c6410100360303840013100c0426035040c02004804034158076140f007400e00a0540d14000c042d039050310440543c1184581460400c15006072500317202c2141c110707112000e41a40102ca = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 438576708 1250 438575458 438575479
    0x90615051e0406050607140d1b0201080702010902040515010201061a1803070e0f0a0b04090c05060d0906090b01050f030f12070201050c0303070903031b0b0c0c0f06010305160509010e06 81
    0x60028109608280e9100305c1c081902e80a1102c00e012441c10099044112005e01000202c1030742d031168030b11540150003003045403002c010351051140c260031440e01e00000c0703180702956001405541048881003203130711010328a0b5140b903a0901401c4c001380742030340200d80c403079030900b007203803a1445141d8180381c12076401c103c255401d440400601004056459512119082074000d91294100581c1c0304031500e8103080c01104280351a01c6003071402035021400c11a950f14000070300c021504240740d10007400c3e5849141402090342401840d030b605d403217600a036226604003020020341c21101482c00f0300030782c00007200c00481c10340002c885650710303c03410545849184a200480720361140b06200c13001d0303020200602100e141c105140400ba81e1180d19051051040c90500c0500c00850040190419051340b02107061051400014094a04650255084002c007512254503002d0300707171b1049666601c0141c0c8001081d054401d03040207030900301c5d45046294900020750851441c0034000520442c42c02c01d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 438577958 1250 438576708 438576769
    0x1c18020d1205040e0903040f170307120e030f0604150e060c09040b210f340306050103030206010e0606040b0901031a03070f03021906021c2109061505 66
    0x202614000c00c0315001d0641c1c4c501d44904d01c60b49075001440340c2c05400ea65031002117403884a80c00ea540d451882480110f090180e81e8442d49035120041e40b160042c4401d4104180490b01c06011004108840710010304050801e45402000820b186a01200e618500f000d0840c50800c0818580d8200e0088101d503a01c9454a20015004140030800035501401c1100e010701030700c4000f41310100844500084d9a80a0503101810b03032101c100070f4084500c442040020505809504108086001d160f144c3c0000c0742d440765a01000c942080c3c005a0244e84400010801018440f00c07041d40700100b5940c45081ca890b01400e04c400e40503c500301410700d1f446803040800d044421941042404000307040b01c004070780c1c41c88125200503140c00240d0080c15102d8044d070792065100014421950554000c00030810700d280c0781000017900303010307400400404042c0ca000308030b900f81e186000b0503814500001d01042616000c1d0840d003158060040c00310100c00c0410280da104160b4801842c150b0985041075626103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 438579208 1250 438577958 438577967
    0x2010c15050a0b0915091303020a020a08070e090f12030414100b1e0a030b04081309020301050109060234030602070809030d1823061c18020d12 63
    0x994152242034607000400c1900c009a800a50803050f080c0c03060006a05d07280029550400c00340d1240750004103030070204d80002036203c031810720b2074001d105450741c419041d80014001380e803a40c880b06155002c40d80034005020203044d07254001215000812020020b12141d41d180c000051000c3c00310403000c400a800e00800c40c00603078035402002c060b21f2840440140c290010300b170310206107010b2139030a1906000110303c080346054051b801001500c0240ca5030791020401003006008a41004040c42142030409210580c0c42c0030f0500000003589a606040c0010980f0b8250b9004100315804100c440300041154005810540d001034a00c201e040341d6502c407040d1100590344014000c034400122003040c882028080c1507444411002d139144003d102c0300860700f0348001545100c42e004c1c080c200304480404200611211400042d40090a040003070001e04542c00407030b40c2401010311001800340c02801c510964490409108514800d1402a00403600480100f8401032164055101840685009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 438580458 1250 438579208 438579233
    0xf1a2218080d05070306061b0b270a15090b13020301061701061d0906013011090106020d12020702030307052a03060c07031d100f080c031302010c 64
    0x100340303402da45001181d01d01e0000c1a00b280c00c500003a207003c50120351381e445070030304200655000c842903d0346910368889040c1c00d000079106403008101c2c0e00c41c0803d001058203d018000d0f44500c040c1207a6500303400c106000c403d1a4000790401031804000500140401c8111900600c42204d41f0504807181e1012134010416038001410300e40480304040300c20f21054000d00162040420329680240e103905003014540d40541d0f40312601c1d08004018801036000c40c2d03080141c1328008291903020000c0c83c5808180c40d0780c6500c00c0d0313804508081490441e060140709540101150f00c01088110b00d00e44004018006015001440d00c4d0006542410b65500304240c9080c15000000c4d84e03091001080ca4520150b0207000b14280311000345140107c80c900810060710071003c1c1c20030076180500e155402c654641165005020700b820f2014010540d4440a0b0880c619462544600044903c01807002d00442401046014500381c2001000070204485ca810102c007542820603e00c00314084c6000c0104d01c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 438581708 1250 438580458 438580463
    0xd0203070b0903010b0d030f0f0c0807030e040507181e0306020f190801030218060d0f0605180106050f04110c0a0302030a0305070e0904020f04020702040f1a2218 71
    0x3036104045840d0344503800400400e28124001c0001070070f1401840f00d4000d03920805004102040d880c1c0e4004d40c05824401d031424220701d07080c003003c1d042e540e884040d82c00100381035000401c0d00c4580c8605003058401e05400020a08000c2e140009445a501950895000f101400c816040307148410300092486c1d14061980310344290b45410b40100c2c001da00350003c0349000805200010321108c880d02500d6414180c0750050140410b40b01c00c1c02c1206030310a03015001a030816008501030002c40e0050f04a0084030b8030803800481c5500b003c0500c985062018580080c141e49059020080c1da9240d4102508c00d250640d800320b40040801e40c4c9000e5401001041d1145001e44201c41d01015800b00080c00c03c036203070341c6003040641c5038a0001c464075803c142250740c00c0700c099030205025103014a001e64410000500240c50406a62f011605640071401e100d05055114000101c7c0100c10b0707a4101800481503801c2c40031808603603903a00c031080325440504902c954a01d0348810401300d0f20802e102840c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 438582958 1250 438581708 438581713
    0x21f050f19020607230f0705100515030c18040c050a081510081009050712031d010c030539100614060405060c16030b0403110606090103030309020d0203 67
    0x40e108440789845020055180c0140140c6002813030150040703030721028041010103203282602080380f0300320455024030589250f030302c030a10082c0009503082103140d030706002c028000304850901017003a621540840c14114821f0308110a007020700c0c0ca43e40b51340200300a00584404503511141400c0090f11800e401035034011003070340780c0410110070002d1058440b441c2d0301200040c1d07030b42c0c00206543e803400c1230080002030741000325140212952a08035000d154002d0301664034542d40d8030020400ca001101d401c6010a410703541322242d00708032000000104a080c2080b0200c0189071390300408a1090204005a07945048203041800d0303410300c4c5440089c1c12446a0351190403031001c080f581e9006856031411600c2c1400d80201e0141d060030f000d410403560150045040600700005c06c04950000f005010b681d00c14114115240c098a44001d0011800350701c1081003420a42001046d800d4045596101640814140802c82c1c84d01122141100d815240010340c1982d40c5c0f0001d100304003200c801030b6252 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 438584208 1250 438582958 438582967
    0x70204021606180b06010201050f01270c110f0a1e05010e03030f0a050604060807060c0302150a0b0111070f1205010b13060501030c0219030807050d0c121404021f050f 73
    0x1580141c1d4035050713401900d58444079a02c03800128261a0115510090040345000402c01c401510020546070780d41c209100d403458491180c070b0780486806d01759900c00148484403a080010007844400c540c4044400507042c1e2a40390307106c4007007105030100741a201e40541e25000e800c3c080c0a511860748010040182e03681c80c00c06150388a0118010340340310203e1803400c1c0209415180c5440340100b1541c100003e8080b461402d80182c85d0003004010580950003005143d5448a48060310300744260801c03280003e038081c00100040c820700d419012444240e10041d02884078107038904c00c841c01c80b1009003410030070300d5052914a0240003080b02550b0880210343c021101440b194003d041910b8007a60304003c49080404102d03a142c0b200c0c0c00d5425030700c2c0803442010109118041303659103c03805043c00c5d80707441803103040b0314101c4449a080000107800030319110b208812034040e50900401c2c1c181005941e042540020700700c00402d054402c0005015030507840340c0390041d015107403d10031000502d503c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 438585458 1250 438584208 438584231
    0x6082113060e09160e090604020706060f090516020a060c0903050105040309050909010b0603040809010309080c16050a180b010e04060308030a0c1e180b0a0f020d0311070204021606 79
    0x51044411100d80305028040000c4c2041e560704041240b458869a90400e10468140c20300c82d41d082c0280040d50440d4080005001051903030040000500c0c2040c401449145490343d10001c841d8041c003681c03001403a02c4c2c4881d03810750f80041c140e640c0f1a0004000a82003600d248140c2c0d0f080f059034070043c465401c0a080000745a0810780301030482e070b4261086030260340c03001f947e14200d4128445907544581c0030f00204000c241500e002c1c1c005908103042c00101001540c441e0b802c15000f895210980340e01100340980500d6041040400031b0100f503ca08488505250041120f480d891001c1081c0559886074580160701c243d46241001c000a0410001540c480c10301c80d0304c9920446400705254208000407980758410300d141800c0300c040c0c5035140d11359a1750280c100d030304841491120940d003c00c100b001c103038003440000400c4125429102c0003a07039200701031702900b0f150302c02c0c82000601d441c294071113043d400544101d52030158100e03001070380d0350704400e41d8214441d001c05c4007403d00d074034140f440d014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 438586708 1250 438585458 438585467
    0x17010204030c060c14010c0903060902030c0604080d020f1b010503091002031602061006051605010f0f050103110d08041502160605070b10030c090207020d06150f090608211306 77
    0x34907400b071700c4a000102c2019a00600b40d81c020001e000009001443c1000030a080343e02c50a0b0310340c030040907240496042400603c03150819081208107030002052028016010841103201e04483d07001b40501501d1500c84000e40095425001c0c107120000000070013a200601003c0c607e40b41c441c07811905c03810100662070b1311812189502016105503008140d111035011030043c00c41d000743d51224648205070034030003000c1d40c415104440640d00c40f80f11714000d2801d409000011032008100088640c50360500515000034041b03001e000c0d520710059500490010f100b220151002100da03800e0b00400e100301280352030303000402866202c250000101c1c019602500070024240509030195103070320380e42441c00105002d03100060200c3c0820004002e0040590041d010441c00207111621012503a22540190b0f1000b6070b84030706a4201002c01c0c0300140911900d080544010142040118180001c084d52a856036401d4001402c444101038000c0e4105021070380da42015011904140365181c10290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 438587958 1250 438586708 438586727
    0x5030a090815150102100614040609020c0d0e011403100914010f120201260108071202032d0a060608010c17071d06130510020309090117010204030c06 66
    0x10005011a840000c08960000e1941d000982e192082903035521400030b540c040c0f51035450303080c0c10341c05421261441640c4034030408000301321104600e84952444010402107500130703003011800a105108590790402d0005003080380c07290505212600210480c01603c800010010b1809144800020450721a10302c00710301044621850052114420032168100c1c0003100b4001d24552500b0200c04104000034900c2ca40c500b00d0042c1000f080101c03555481034215182142361004c11200300c0700402c1100010000c0ca00145020043d09080c4446980042c0d04c417070071000940b00080300f0b46000c03498001d5000202291030368500c2203c052408030b142203809085030f4445c4869951900d0a8800f00500a440b00d42e14920071080ca02d460360b8500c002503038801c40010415826541c666107240294898000a0030380c4042c90340301401d02031400d410801d004080c00409811500240101c5905468980415041d04c1d981e204803c440c140b21302483c1d0090003690310240260b041c004000582070380009621 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 438589208 1250 438587958 438587977
    0x60f0d03050c0c400920011404050d02060c031215060307140a0207030510021309140f0405011107060506180f0a09080c06010e010501111b150d06030503 67
    0x8495912000d01040b6803402580c180e04100700381c3c0390b183e13141c1c401880d80c440b0203400d652602001040820781a0000c9a401c01c608552601c40542c221060b55400002c104030385000340381014001d42050101502d6004a214881c041c0c6480c1241a0455441e03100780c42c0c000800c1000c0381e880740a420780004001e00709450070b50b028842c004214646040100480b4400c1905031145041a80d101406440642c00358101104600644101100065051042c050074034944080540c580b00c285160641d40f04403a4400041e05181443d40c494804000165503800341c0110044a03255803941002809840003441c10f850076040020b01c8820461075602c0300d40102c2040da100d48000d60105048070038410140c405424042d0070074002030030f180540c0c002018981c8a606e62a0400422903003103031403d4020b8200c110751261040040c000c5d541c1c40071100020342140e00041140b590251413a0780c6170350400400e5401001d81c02e4084d00300c16140800c50304d204a0742c0c0f504020381c80d900d04280d41ca80d007128118 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 438590458 1250 438589208 438589213
    0x40308061503060d0b04330606020703050c0f010219050105010303030b010507211b050106140303040312080612030a020c040e150c03072c150f12060f0d03050c 70
    0xd01d0340c0001c50500352446030301e0203801d104084001ea2604080d082d40180105d5028000c400d980e42100000c0e441e400a451454440701081c1350308807800f0090340c945411010842d48500c80c02c1000c540f00140e089140c910541e450380c8190200c0c0c00403801c010011914070243e4460306884420000705600c981c0c100c034083d036800c10405418200441d454480d99501605d8404c50203500d000f880001003a01a02c10745c0d60502c000081401b401c8032861740d000403811b0320701d65501d1404000b000c1d00e10f0044450007408074007035850b180c2156100b460311320002c03280038100702c01c08000540030380f40d220f21082145200c40c2100e40f030707640841000b5550f41c509a01d041c0654200b0305592203d95000481915440d0481c11400c8030356034205109059800003000c2e442000200700003900c1840400c8500c1410200101e05412110700340d8043c410b8518250082c00400324080050142d00f0384c0c464107a581401441382c04680c661540c0001510320042c0c001c80d994880076800a8004243d0844010052034020805 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 438591708 1250 438590458 438590479
    0x305040302240316051e040801060803030108030a030b0402130801091709060409022802060403081312030510030204020c0102040303030e01060b0a11010216080901030f1e02091804030806 82
    0x1400c004100d07510b00da1806125003400415820801c030b060941c440052850322600307040d40f085a544c86440c44003808060568001800d00c400e1000307014200c00b80a48000039840d6515211200d03940e80324141d0301e10205513603404c40400c0d5540b41e40444100304000444801566103c0c0d0741203001b807080d0401261118030811011002017940000d40720070369001005242001c2c60080c609002e54010b5a030051118013080c03141302d0340c50074280d14403502403181c0e00602061415207805001c050740038042000d0211011900760000310880d00e248d5100c0314524001c40e940d100e82302441c103a003101380c20083d07001d40042494441c4c0f20055000c3d000b100e0080d5410303c4031035106070000c1d00f21507050103030040381601003110007099401042d403903282c0d10f42038000500d802c100d000b03103562140d14800100d5251000081c008110741e418042d81883d0799032608200020100d0101007141085000400ca101c0d03a00032500101a50302d910810300407a10841074101585801c0c503005103500f41c11100c0318032503400801d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 438592958 1250 438591708 438591739
    0x106030501210c1202030a060f02040e070509060901031116050d02070f081b0a15020a0204051e011a0f0408030306041b14031512010c0201050105030a0308040204270305040302 77
    0x21550b11403540c0103003d010301e481c00e000992000a030f144006a0b01445a03402c1c1c440010400d00c1203007a010050b41d00107031a0380c20158114140c44000d070800302000030612503000303a40d80343c2c6c2c111000319009003000038030018950010011401100388154107540100303030345814414041009164149a5400e40b5007264580c01d03110a840b0081c090802580d1210000c3c0042c0e400041004090410041540103802d5a810340300440c14195000700005030014005602141014010241c21070403290b100d0b22042d0328041c9a000c3ca820501c24000a00d032200c102d006690030102c100c51184910000842d6941d0311203201d15039940c002d49015005615100040f05c40700daa072200b02414114581d80d071100b00740c0d00c11019001c0c4c0c10282000c512507008041041036070742c0f42d80c05403400d01080d0001203131007040c90102034211032050303100c28000d410035017690000a40c084da003e40c3c00365049030700048403032448035651101610940d40e4014400b060010b0800d02d60040080c3c03046910856100700d400001c0d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 438594208 1250 438592958 438593009
    0x210110c100503150d051014010b120645130c1206060b0c0c01092408091501030f0c0f0f030206090d05031812030a0e091302090106030501 61
    0x3001d03440005201840803441510015850f00102c00006040c2105c0c202a503c801e0700f050520020108100d0355690801a005c0c0c064510300d0041c18450030b07550621284c414500c01025005114600c10300804129280d66100490007118080306c80040c0b81a54804241c03002604c2c0c40710140d40418144a000036144a40401000505590006030150420310703001911005115110089038107d888580101f01400214054071195800800802c200e0240c100054614003807a048840d4072500784201106c15031600c45d5601d620403451a1140c6142d07100e401da18145603403250811074000307181b00000140012280c0c0f20714042d02940d4590b050b25a42c60091140080350710414003c515512001c201500d4018003415400070081d1540180b41066602c0034210380c4600747c05001403c05407403404840c20b00601c845101d00811009500d0010300c0302c0c1c05012808810034561084a00e0800074034150118040380c1b003c6079001d00346e01401e50311000c1c003502500f824002e801d90940c12615a501010740c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 438595458 1250 438594208 438594229
    0xb0109020703110a050a1209080d120b010e06030105061b07030c180203130807020102011e06140105090a05060c0703050601090504141519140c07021026060406030210110c 75
    0xc00400042d07800d9a107947c1480011041402400211580003401103010f0100007425031040d5500c21a0410110b41801100c00400f0040c3c10000c0d441c0314940c1a8a40c0822a810360380211a060785400c000e46070200c0c2030462000344103890086000003c1000f0303030312084a050312481400c11060818402c0c07120200e00044800240c040d801038a81404070b00110000d00301d040c018030000c603111524121500929095110004146903035801c10001d130070350000d14071000e007024070b00b0600d010302070310024607021020300800e40f1507400051368201c0518200100c6009680c010242c0c0c4c1e566940b104160010641101c06031201c00910340c3e141d002030404240908141d500040081d02ca440f000780c00a040303100d82071146441a0f03584070407812024152201440f0780c0104196a40c0c0b880f00c2e1043c810f540703500c9046003007840118240c1d002e00050644084444030002c84114400d5a1080000381c05400c131036201a401015042100100b680c0c00746030214070090f040300b10703081e5201c500284440c4480707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 438596708 1250 438595458 438595463
    0x204150c121b0b0f04140d02030318010902180103110d030819020d0614100e0307030f1b090f05070f020c0402071a0106050d05010602240907030b0109020703110a 71
    0x94003205825690701a900b500911204400c54418042665031002d01030305041e1020014480050304010400c40703ca0f21040c0108141006002160403405001e035603800003800500c8074020f58060341d050000c00354060300c480e68000742410842c000c1e10919aa05010070b020a4480180c00100d544184c181103c000755520b5056540980316a034104400c03840044100d20500c200d6020020354030070104c1360040c03002a00d07916078820715001c5e00404101e04c0d00804100042407007958941003029603004603404003260703007280c40c00c070444107540b82806102107411100c1800724040c0901081e640341691104080d003600171010490768075445401d13030b000341c1055a9000141d02021604495040030f402a01e0124400c040368204c901c0c25009014070030400740c00150008038082958480c1240c00d0007058014031301070025040745070f031742c12030140221700c420390512181001402283e049801009a940210740100f140c0049503111940d00002c0d600030074066000500500041002c4880031414514503035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 438597958 1250 438596708 438596723
    0x22051014030304210c0806070e04050f09060c0a050408061501020c03010b03100b04113c070f03110a03050c0c093106020307020106030303180b0c030c0c0109060204150c 74
    0xc003004d40034107101c008803c0480e0700c6007520800103030b06101004002d00690058640340c5403100c03000180412907100030301268140003801c003804240140480d10540041c819090265110041c010642c0c19200700c5e844100148913000400841c19007982c0180f441040907800e0381e076a082102e0030142680c03d2458419450f40111a290082e444198400b903043e41010b00049206074a081c40d0b0700756508405542103c0040b00e5a500228076089001c2c100003068800704051512701012040b000e6004400000301101e0320391321130b2000c0c18000c003490b800c00c0c951074088400c4110945801801c54014030142e40f9603100f403040030341c4140307018000248500c140000c1e90b10780c800c01540c0722607080e000ca04400000b10b11208081c0114100d40011032090b903040e00003042c072178a90710f0002c003112460b0050410b03101104012800260f0502da40541054814000940f80d884003100142540b18403c80482c083d860903003a0000c118041c0c028000b201c0500e145108110364101003610240c442450050440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 438599208 1250 438597958 438597989
    0x2210a06061716051602031906060b04080a0f020a0504150f0f0b031f0e010b03090706080c090904030207050a0e160c020307060c0809040221011a070222051014030304 73
    0x1988110060301d410394490050b1171000102c0d80210741881184040c66004244915a034428060f10380902c41c010f100002c0f815103040e24081e00e00d0340320b0000142c0117014008045103041503580f42c007441006448c0081007080495268a01d1001c0c0d100b06103d07500071150001030000d0604070303e0036500211800082024915500c841112820042c40c5403404041d030402c080200781000116840750107424240c000e5903503820540211031901880d503104d4020010b600c0100090484103038141e4003400001d594032061501d940c60f00703906042d09a041142c001181020004508868908450007480140c0740e807001840c2c41c0400f03c0e000c84074080e010350198003040c1c0410001d03104040c5045610b02603240d0302c1c2409a2040017a061ba407014203459801214808078401c01d9084008050060508072026440c07540d4607842c07074a55014900c00644140c52010b1805030b0140b11140740003280003550802c0055181030802016955102d0240440c1c2c1c1d8410903400c500f0f0f060000481d01035501c280c0103016103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 438600458 1250 438599208 438599251
    0xb09010c02130f0e01062105070b0c0619150905270c0414070e060c031e0417010b01080105040e0a080307050a0219031e020a060c02010e100605090402010302210a060617 74
    0x1581d01a04049a131427040710000a40c0b9000c90014151035a00e1501a2000d411700e40c0c0c41710743d00c806068804080510300031201404404011401c1d0480d0420b030400b042555500d130780481c02c1c400c441505465a4105150070000d400b000c1441c810b1200201c0d404c002c0001041656071040c40b00f00c0302030001c0382d1101030041d52445e0410280c100c0440305400c0f240780500540c42605c092040f00350307440001340e02103014010800140c0c1e030003071540c1259008110400101000030301004061081c5406140e4618000400917010b000e0203d210350000381c001d170b503400c149100a00c0c41d40120102070050003a2401c03405143d4898048466040e01070b51030506558124070000000c40c2422109030a512901c2d218400050250280030303103000c2c06800003d110401c044003c0d05008003801c100402d5890400140160303925080e040e0b40064080c6001601d65600c107180180c2c2180001691245104035030800201c1c0b030710364002c0019995590354440c200050100d4010000c0c2080d9010049a00c0c0024040301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 438601708 1250 438600458 438600509
    0x7080102031f0b0901140d14041a091c02070f1202180c12060103270b09031c0203060301091e1205030c07060c0216080303180c03070b09010c02130f0e0106 68
    0x184509a200307082c5400447d00b010800c40f445003c60400f098000170070442072103482440112031510380f20702d0600b40c0c90018001d9468030419010030300340000114209460714070030081c400c060140d201c10011019140c0420448804c040d51040384524940258251000300607440c0030b004000c03110307009040921403003152110406c000c140038105a5240141c24520400000c00280c5012096074903c10400350700380b078460311300000d1032030099620400c450304803650001c1d490b4810740e817150001071300c0e070300d404000034050031117540090000d01080700f14156034140d044c00c00b000e1a01c05c445203810459466800d54041c04100d0700040310180503c10000407d0b10b0750842240c02410740f040c0e0300d00c0410103249038040c4c1801d410503c110341c004810000e03003030390284003d0140e0842a0040c0000780035a800030b6a900c011340110160080c0200307116070720ba4052100d00c00c3c003070340c02804014411f04d40a50f000c0180410700c0810001c6040c41c21424204006201e400e007a510303a040c40400f145142800ca08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 438602958 1250 438601708 438601727
    0x3011a0112021e0d141014060705011803020d021c080a200310030516030b0c0d02070f0807060b18060409030c0605010e0105090a0c09060f02010e07080102031f0b0901 73
    0x1071050b05107034030038810210100051402085181000513442c1071171900e8404004024100c03107000025981c140400d03180c3d418511280389045507615600d00d01d61a1890250246c010b40b14480b00710580043e08268010920b298280c80d10703821a00940711030007412159985000602d00803c071040b000c2800429560881c04980c1c414210413402d4821a0752285030640c01250075541c0f01d65000e00038001c2000c01d001115040044000d10080360f402d54a812400c49400381080021240010348100641c0c403a40595540c0c60304903108121220560170480c0d496031007c107080b80d110340340800c2c0510030710b00040c42441c401d21081c0c20f04140c0d0f45020500009004800044d010300003145054000543c080c05658040d206c0800222240d51420f42441480c000281018481e10f090143d403d40040c1d000108004440c2c01e03140242c902660084160300501c03000c44200c00c503000e910030120b25148150001c501501025415150f401880f02881198108a006004811204201f01d80302c9620803032140307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 438604208 1250 438602958 438602977
    0x61e06010324170c0a140f0a0b0a03050a06050d03120b18150f060a020d081306020331050309102604030f0e030604032f0105040203011a011202 63
    0x1c0b000d039101d0780e901541560082d8001e01001c0d114901c040d01990702408004812001556078440040c1092181d0488003800c000e498000c65901c481c5000030360760407050300001c217942241c4a80d140b801e250020091700b001c4484260083c1068800503041c20885845682c594061340c030580200c8103400d0350000307030a8503901b16501c000402d800d04001080092039a00850380d40d8210089024170704244441030143c403055a00c10310003844031b40304060700070404c22007403011450010704654441c04070341d100c55062071000c0c1806101104010031032040c20b0318085c490300c142c00d458001604c002500740c6450440d4900a040f40c0041c0454100e0341003112988203c0c206904004142e0300da1310004000c0320445c07441d000310740d6040c1003d0105050700805d1400f000940381c6018004142c003035010a950346005400182041500c116040010180c030742245080e040c4003400e5102441c580c04030501804e030948069109500c8e0507400d00d10008030b1141ca080044068403070700124802681050020f40002000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 438605458 1250 438604208 438604241
    0x2010311041e090b01081e0415020f070c050603010b12090304080313062a0f02120316050f06090d05220e0421021207060e120c061e060103 61
    0x10034058044021000c400c1070b161070008000c3d24000442c42611035000056051060391030500c040c0509102d42041c0d401c4101d03a800b43c0d00c0e2914074000307007545a10b210a4001030301c003181d400307207400710b1000405105000d15005803c06031141c04100880c4801c2c454560003543c2041024101c50281e03202541c4003500000303407810960380c0c09641d42540d02007000302c1d10407030203241c0a2181a4105003100240d191000d91040d078010019244444070f0100c003c01740034400e403800d01c9000c5540704443d02e04004155401c4e00d80ba00e0074501840840f40346c0394411121802111100310301410300142e500c1c800d4074403800a1000d200018420b0b00d19500001c15101600114000070120305407c3d030b01d41c0001d05000680907540e04d45070500000d50081901c10342e006152100140b80c56907400a002c0d120744036084992070340c550b40c0c0d143c0300307008054030243c3d9441070040c00504804944c43c0005007020710340c3c01d0252202e564034a0060b04802c200d840e070805402c00c0550201c0e815501c60380c13010740010f001004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 438606708 1250 438605458 438605467
    0x9070506030a180f061b05070f0b040609140303060a081203060906030a06020414040506030d0c060b0d0213091a01030c120c031b09270602070f0816060c0e0102060402010311 76
    0x1e490a00480d000000c0d1841c80e103526080075480301d80300b01d44410348460320701079003030207900e94070701d0440320209c000030303000100c01d801240920035954010400f05510500782c044401512407030759200d4104071080f43c8550103824001844007000301d0001030320501e0100640c40e5698210400c0070500001d421150144501301000d000079010344000d101174004c0700048e2108820440070841650300081c00503019400042200c1c601310f400100a0b9007040d4404408541c805098001c215103540b50b11010350300848142d1b510074440601e0307004e175002900412850080403616040312808400a220043c08a89084400c0012002451010095901c284038403403003141d0f00d864904408500080210300c0a46041c0100024040c611030080883c1d0a42c1d030300c20700030101a24039501401c0c0b0503800b9020a80000340b81d0104154000102c01d2583d0003030341907443d07244620810000038403100040b40c0862a1100155005020f10a4098204816801000c9560342c0c0d500440141080303d5080841c0c500902 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 438607958 1250 438606708 438606713
    0x2090d0213020c030a0e03070605070f1106090a0308090f0f0d080307020a0c090c120e031605070e0106081504020f030103030e180c09012d0f1101060b0301050909070506030a18 77
    0xd10314640380da0749031b45100007540c0c02c145c104825a071114013841010090400040c42008003014215088040680e8a4805c0408124180f0401423895449176204030b01100704080c1d03a014050140d02034414151007078114080c4241648004211a0321069000322180040d00b55802950710400c54419200900c20300e40d942a4103202030b410001d003031900d80240d0b200103580441a58842500c500301030001311229086d4039140d12a040b004030740c0d004d9100761481800320400c06040185440382c03002d2115a91020001c0003508240c40110419440e00080b107001d18040c02600c00c0684c200c0d2280340385902e1541d05546c8203082803c2e40e078000c0110246290540c03003c0c20a40e01c55405185100e030740381420b800040840c2d0014004100d40f1348800c403c0340e0103102c426a001c120b03544600303088610062a01003030301d100e80c07a00c0e12145190300701900800d490b1141e00156040340c100340ea0840b01030300c4410560303072108041d0041c40d81100c4188005204004640c1044503040e10f075002143e90240c194 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 438609208 1250 438607958 438607963
    0xd060605040906061d0402010504061b080c0f0607020106030b1302040b1023040e0103020105090102030d0501091b050c1f180f0209131a0711160807080102090d0213020c 74
    0x40301502c1d00341d40c4d40020420158250b5040c03500500f002c813a01e0311454240d0000c0d145000354001c403000c10414041d40b490110704106415606034002d0302c115214003104240c56980c640200300c2c0300341da008400c00705a41e00d005014080580340d12052402c56030340d0b031488032038248032000c070141c0e070054881c000c102d503075115203002d030000041030780c2c0301003540c0c0c00484034840c40d61700d200410100c900104030400208804000302ea0540b40e0929080795a00342c0c440c0101c0c6540124455054190702e80f00c00016810382c1e581c824180c80880ca074040800105801c4140c40303038021600c03643c000d80c002041e803002c0da44800340180100c40180d8000924498900d02c00c07000300e00100ca084a10b640c3c0303907450000750319000329074035401010700c0500c0346507088070341d20809403a80c3d24030442c010310015004203c0f29406050058512040c40301192541050620b031994103000714070400020740603694000c1582070301802250154080500380380b890800950030701c801140400300420b801036092000400740a0103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 438610458 1250 438609208 438609221
    0x304051908040e0c070609120806150426031b2b080a150315051b040b0304030e120607030c0203030105030304030f110307170f010606120e070f2709030c020d06060504 73
    0x2070040026030a006800141c80789c03402400031880b800c80c0010b03040c25500900d00312400d507001d0303051103038008180d1300c0ca89129030004038042c01203010200e00c41c924083c1c014001d4108240e440c00700c17007810003043c4600340e18443c0c00c0d015100217191800c4150023140154103842e04014800c80000300408010180442054103400495400c5ca03502c413448020307c0d5501900c0e07000340c0c2d00030401e500c4107442d907042c22151240b0b20803e204034401000103418180105080c94610302c026043c580444c0304189615110101250904082403801490251162002099a059800103001145010306580328407002000f4108100d404141e5043c080340952828000800240a800031844600c1107030051181019424070845600b60f1510004000c125400020042898041030000a9103200006c1440c14085070f600b210403010f004c40c1000480c003001c00354811010b120300140485140c0b1516500f000c1d2151408050001350290700380c0d00140c600103201d80404d80c0b040c2c400180040d551404a400d131100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 438611708 1250 438610458 438610463
    0x501082e03080307171b270607030507030305100302011d03031b0c010225051e042c01060e010303031d0105010902043b061c080304051908040e0c070609 67
    0x10806000075132094030710034083e08268442c410191020380001300d1010341c043c5031001141104a07c6080708000285d0b130302c407400900080c0c0403a59071700da20f04001d091a40644030440000c4e2030400040d04500c400c80c050130503a941691001d000e1860343d5103081a03a215246041c0d45404104034501c0000c0013039000d102102c100802501c01c0c41081c2002a05100c800102352040c0c10b80d40d000f4030840036081900b00c080e0f807402c0794035240e00121291880b41c06403215101c50741007031415000b00d8038148580b56050701e40b559004110507503011525041e003618114400c2040ca41034502c01800004d010f90043d0600c021480c41c4000c000c40e00019403402e41d1020390010200a03400502400904c401e8406a83d030125400541940740c103007054500700119900368800d0000f010390002c80c00603030710940a41c00c14400e103000240d44a0060800550311341c0141d8040b00c80b4420f46501902c6011900f09640702290808021424140380540085806100074240d0b00c040e141080703030340700055192040c0c1050a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 438612958 1250 438611708 438611717
    0xf040f02220302090f0118050a09020d0f0c0b0a02070506070f120f120e0c0f0a082b0311190201140c0c060901020301180b0a121a010501082e03080307 66
    0x42ca9401400300c40725002d014140b086004d82e00501100780501d40f41034080d088070070001440d540f100c4a0600030207144c10000c0d031101d0b12009603020701001d4180ba2500a000c1c07001070907415617541c0182d80070300c941d40c03086000d81c01401c02004280b51400141036528003619541c1640003031642e500c120781400c0802d003400310b0305403001201020f1303004c0f2901c901000d0b026010421450080007c1da60748110745c061500c2040b00c2d640ea00d01036180d41c4d12080080c802541102c200c80443c4541080b440030b01d04542043d500c00c40840c80c102482802a0f0070b09090780307a5103502e001c0500140c00340040390103101000355900d602d00c4203103c15200604500c00c3c21a509415101c203c800155400c000c409080102542e00600040c00701c06c0058980324030f0f0868400d0b0004007092244082405803602d0381c08030001400c03400c03890b0701b40408100c0c03602c84030084650345000303603880b031005480340034094aa9008814030b00b040c2500780e060230134800d2004090750444559044d5250344216859004641a00006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 438614208 1250 438612958 438613027
    0x2040f1203080601020106030c0e06010c0c06200a0206070b0a0207050706080405010b0108042a0e01090b030f07031109041a0702010209040e0609030f030718080604110f0f040f02 78
    0x40e4860201034003d80244002c1c0520b80c0345803620a45500c8138011211024050300200e241d60b1b0144503040f4082d41d201074050440b40d07455001a0480c0d82c0e01c100940060140d85103100e603181c0114011038074682c001d01c0b040c04d04200342c44001e0075540080c500035400f42c0c20420840411410404c81c0c000f040280d40703082e07041c0350902e0b1450a5a1102107a10305003d14842888001800c0040c1688180c0c0c1c0031486201ca0b03003c16001400c0c90180350f0045294030a488008076031440540c000c0783c0f000c8015030440780c1441d091040c0755681ea200d8440a484a100d02c0000c11980ca8003d00c543c0d04180903407401c6041905800c1c80251500040e14010007503036001400c0c0c0124185401140490450302c0044c122500e0281d070314a40f07030f20a0349a0401c00070000030005d2840d9004220745860103c03118201c1c40301584805580b07603035843c01d13102655440b9410000302c0344d03440d1440e000085660f01403c030081d0030000b00188005001d02d0002e110981360280002e8800003410b602427440d03144a0395042211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 438615458 1250 438614208 438614213
    0x5071505061c0507030809040204120b010501030528020a05040503010510050a1202010e0d022106150609010f0f02100e010929040308100306061412030412020103090602040f12 77
    0x10360840c002c0c0c01040101404000400d07000300700c1600f00c1e41c002141310f41e280803210000b002440340c0d0b00a4424030b003102240c08280018818091b060b5142030300d08120603101c4110807400d45003c4d00c42d001c60300d504078107800e41480c03640d0042e01e821141824040e0a0035220340009094400032603070001140280342040006207002c014410052031020540000c0084503000244011145050340d40680d00010030300e4210340316030495500309007880c000e013220b01c4012529251190350503140e07120103454580b691405458064212004030700d058441c00078110444e001134510300d581140784820b41c0540c44035004c482c0e1090055007001c0c4c41d20000040c2415031032030414010802624917013411042150385000700440080034940043c2c060404050030769a0243e440200f0745103800080c0340300d0410000007492400c041c003041081c41d041b40c201225110020b0071644d01e0056115061b05903082140c03140240d400b950100710000c0c0505000b41c541501c0c0c103000510034625074402c94242d294103061009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 438616708 1250 438615458 438615469
    0x61c050a0b0603062803050d02060702011a060d0903030b060d090c1d0103140a05031c180803180c03030a0207060f03060806010b0d0f0606090f0803030c0a0f0507150506 74
    0x210410803142c903410750a1140105040d42441d04004c0410321020b9a054012409080041c0045900404582000001180c000d445040565003200075600b00401024240d02254484100c1c80d00035248030b04051a0621000242a0005c03054041c540d44200c0340c41d4584808004015002d81c490010829909030b107803141d80c1080b02c0e07200c05270039a1000c40c000140301c0c0c80b00720a411241c03c22901c603824040c0488043c00c00c0701026009215120000d846045400c80788085285040e0548041021404500714104494800c0740c5c0100401401c0002070f031850011403040000414000c200d0302c0d00d050600102c1c0c60365102e0040000982d0085504025440e88444210080c944a16041c04114580300242d5510034040c025441c56403804910407400b06a56481258a000000002d00490b0317510280a00401914010507400e640c0400d004a4802d4000080701d0180c0c0c0411600b83c60910300c02000c035240d020503c80c0c542004410403689011805103109105e517000c20b12000100d03070400504001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 438617958 1250 438616708 438616721
    0xe0f060c0a081c050f0103030c05071203090e15090610090b040f0e06031209040b040f02070b0624030f06010e0d030504150c020609130b040e1011090d0f02061c050a 72
    0x2d078a418138080090802d0400d8042e030450343c1c5170a203200c1c05400f604c0d20b00d00f171400e150080c56143e551903101205065001484908032040b56030b100003d51200001c81152080303e5007200d4000f1800d50224001e400d1807664400c0200040c41e0070700e0816200c041040c100c0c0d006138012038100d49003110030f0040324030070a45d036904000101c0041040740f840240c0301e1124021200741c030344515502c07640031069880b55004045411100b01d4119030302d901625001e1403044050704e403a03005041500b45c4a828880340042d00701d514612925560466540400d0302544c02c1004200e030b81001040a103400558403503500500455201e925402e80329400d025507202030000140345041000070b036501042c003586541c02199154002554400070b20540f100412000e4469102500e412501c1e2150b001050f110201d4140d81c0602c0f220001d00c000001802c20031800c0c02000c10380b40c0d10042e032040400004001e2a00e01322a2440600020300b0107900050600c1807250141170500059110000c01810f90340034450f03007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 438619208 1250 438617958 438618007
    0x3010f0c09030803040809090115080708130b06030a02091311010216061d1c1b15050a110a0605060909010912030e010207140102040e0a0203070e0f060c0a08 69
    0xc0040e0486040c00501c100454400949051030000108040c001c62100701c1c1d0007031a000d00751510650f0340e002d000880c01c0030a4010f80000383d000011a903000d105900c03840c003170400040103010310300054a628080c1800075000580c07512a5010350350040e218148454800d20099a082c60000342505200320301019514501d81150800b04164070a50020803800c0281d504038a00b5a419003180e10040e01030a028890f042ea101c0340c07c94031001040b80c15842a45501d10030f500c01c014100f090501076803455894002d1905d404034001d07002a03860700c03800151029178802d00c0c2c14800485c00c0c0320041c4c180340d45450143c13140341d00c403001c0010508003040c03900c0c2c000121100820140c0826210500d4160500c0c2000d020940c803a40b40080e100405d406845c40103400c190480496a040c88846000303501c180326041c0000c0120f800a0580020b5200b07403845076400d0303104c1840c0c1f16000010000c0119a201443d903118005100848100c001003044c4400c5610600c0c2c416661441c41d1404000440c400102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 438620458 1250 438619208 438619211
    0x1603060b0a090e0a06020d090b16020d0905060a0302030712020f07140309090f06010203090a0f0510110601050103021b030d0e010e0705010c0b04170c0c01091409070c02030f011a03010f 81
    0x500318501c0e0001d440718101740c01c0980182c40e2001038001401030710044802801e61843c0b4000d012016000e560584610251502164202c004070702c0c09031480d510138811070361310010901c00018018080d40040d684000a4030381b0410030f05000e1040d60403030f0410541c1e1241000c0205048042000321400d00c107044d503641005504044456000401140009080702030464001c004242c081c0d00810a90b01041c400500c01c0c0c000301d0700e8010700c024503000c03482010710800d107030000380b80d0141c001c13200d603900c01820001804040e030170180107401a40c01079802c051034064507003602c4a030a20610182c00c40440c1c0a0001ca40040c01c042014255441184d0304070303140d0030000040104c2e0303030803d4024007a181e1007025004141d840c3d0820909540c2c0d400714922003903030000350500c040074003c50600301407403090721030700c104ad0740341e5100c0354001107c0c0d00c005030130001c00804214064014044014118401400c0710010819681500d082d0350090903408210f8200910358003c504e828040d00301d05401d0940d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 438621708 1250 438620458 438620471
    0x903010605061602100e1503090622060b0f040603080304020f0a26030d05010f0e0106090b04090b0a05100e040b120d0f17010f06080f01080304060e031603060b0a09 72
    0x42040302d03d510190024031500704580a0350007140106120a41c245008080c03a1031050402c181036aa0b500c100d030303001003502802d00058410600c0b0b010600301141c40c140d031703030038121103035035a44d0020074400b0540b41c2d00014014803020075580314081c2001652048640315164240707881440300c01c000b240f552500c504030b010002d0150b21119001c0c2035003070399810007000798004101080c43c114070480702220485806c200c00454500041841030301195040b0607559103580c0d03550b8040b10180100e00888116101c02c02c404c1124040e030b174202001000e0004d001090303040e035402c005003448912510980104410640542c054540352145102240c0280e560411801c10b030719100d0b0711021304600c084188840c2010040c03009202e1601c16410103172080003209207503100c10301c20480742c0081c0700d118005002a0b00003850a030b00c007407050741200c9412000718101410010161003201040920b40c5d014807404c2441d5a840100b40f070400d00540c014540021908541c000340314032500990021940e2070300b00341 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 438622958 1250 438621708 438621727
    0x1b15050f04080f0a090e1302011409090708090f0d0e01030c14040501030207031407030503010512030a0914190f08010b0a06020601030204050a0209040e060628050d0503090312090301060506 83
    0x5045030402d495103082551346201003003064440181e00d070042140702000d401003100040c81d180c002ca88040c001d8903104c06a02c010280420184180c501c1d0a4200750b5038000b06900c2800707643d0103074120b0700302c106451842d080040400c0c9003080c454085800640c1a10074800c1c156094415084170079940e10300480900e40c3c004014280348198844c0604050b40024100145441038031458841ca40804246035180140c1c100248560001c0c00740341e1254401d09820644a8030002c111403c0075401d40350080d0551910102c90280284208210f800003400301001c010080f84000c0707500900110010280700b142448074880c2100c280c918068050982600240b01141d0001466411a60304907408102992620643c00190240e80360a90f0028145020002441804a41e240c445d2000303461014201d2805001c0c0c100c40403220303540d21421802000e0602071400d0011801901c41d0295040b02d2030325074107101007031514070022036003101c40c1008542950760349002e010b101700034442114000e050080720f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 438624208 1250 438622958 438622973
    0xc0702101e030f1a01140a09170a020301050609040b040b0408160302011a0301060e0a050705070611180a06200c0d0804170303070e0d060b03010f1401050d0807030f1b15050f04 77
    0x1d21006c1c80c0b0202051040e44184a01c0344a07014018003c040354440140303041032556800d9002c4202e229500f414001603c9040c1003071818861a0084d50790186a1500c0c0c1b02c10340070031400f50050302c41d404100503100c42568003051a007021482036000040e43c191008012200c1c0e148a1301d02c1d480b9034140242004040407604900d508074166010004107038403615002d96182c4a500c40003000342d8104402d5011204000d0081d002075603903088441410014482041868182400340402181d9486040c0e41000030182c00003041f050484200c1c0c044c0703085040041e943c2c40c0c06070002c4071a10000101441481016a440240407010000441c25410402400380400c02d4010003036024140a90f0080140002034000300081e40e00074008010b6940c10840c0b000283c51000c6094040c100e4030000010345050022500141e82d4001c0c136a2400d1401c1035600b11041c1401c00400c03000c1050301d001200c0c2041051540841340b511031041d9000e0b10558601501c25540001d200b500184002007c010109018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 438625458 1250 438624208 438624227
    0x30403110712080d0b01090303021b010c050a0803011e1406031e0108010b1c0c03230d020d26010501050c030f0705010609140c0702101e030f1a01 64
    0x250801003460003440140c540350181c96801502104840031444007840075050041541c0444e0010502002020a00648460409210040c0180d010303800c1c05407540020303108007445100501d071041141c178003034413450303d0840d00d02821341d091400000100883c1400c40c286c0d819600620380038600f40d0780341860400b42ca0182c45102c2d030191000200007184000c401038109240b8185205109047d612080f2650082022403030950140f0100a008501007402e91800b103034159203c505441c455080d9601c01d9450000703043e04082e005009c80304980098024000342c0440f080a0303005085030020008024100d003160039583c28035031881110f26614031512040c1e075040d5007003820500d0340c03802c00706c2c0340c03518620039601444464030000c0f45803400c01906402c4a4101c5070482002d100907070034240da1900d01781c1c00b030365031680b095010804c04005040101c0400b421406600340704100320481e40b09107802c004412080000031796251906040c01209103e80b440040c1080c064021188080303001a182990 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 438626708 1250 438625458 438625463
    0xe1024060c0305070210020a020108010f030b010504020a090b0315130605010c0311030c07060c02042d0e280b0708090c041d12040f080a020a05060c010f0614120d050304 74
    0x2007220741d100906010784112000581d010382a00c102e0400d0040003500d500c0c00c01022800030340340c5000060f80c02c2c580c1507400c2c1070f244c02101c51401e0b64640010080258002000035051155103a00052000d94a20240d8410002a4000a0070b8022181001040300d40b20310003084007484c0010501032641c3c030000d404489a4181815000780c00d90032003181c914042c100a04040c0e1049201c040b03481d0350301c0303080f08480f070f84256018494400039894124607403030140d281d8020308181c81d2614042c4561600030a501820090a84400b42141401285402100ca840031039465000c0c46400810010045d51f0b0b900180c2850309001710b00308140c0320340e00e0f081002e090a1040d0340f10229142c210182c03001000d22500081c04545500d08108203114940d00648100400d9400308800040c000201003034281d15264001c003020440760410040000750313040084030040c2503684909125080115100c2c54018203120414003001c24100b4040080039103248071112890b400c00c54006440681207001c0c0c1e03402070b5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 438627958 1250 438626708 438626717
    0x50106050f030f27030c010e0304060806210d0518030a0503220e0109090309080a03021903021e070918080d0203060d05120a09060e031b0f040e102406 66
    0x110b0303000f010b004140307100d0801000e184c440000421442c8000001b05042042c041c0244100111802100e49078080ca20420340491240c1000400914180c0840c0780c0c0d4031110f0359011003000e50ba0507040d240c84041c1e07007400081440003981c0c81d480517103001a10b10030300e0110700030a112100c036039515032039000350407094101492604000c0803a8841002100c0940a10103d4211640c1c5d00c0d07400700b02400302c18030190042036061001041441c0301150140203a50185c000f8600090303490140381c840c1d15140c3d0190114040c1900c402c00500d100040c0402d242a008000d2000c0707824000c0ca40c2c203c46003c0c00e1f904030134011403403090000b0400800e440044d16202d00068480c0c0d6100301080c150510448020918060744007840c005103031000141c00b80d038040741d4400c16402d4580c401510007510100081d94181c1c42181c031500d24000220060340cc0803030262a003020510745802107004d80d00a90181c0d9210781000401a118000c0ba02c1202401a08569034103250402c1032504c2c0189615406440b0801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 438629208 1250 438627958 438627961
    0xc08092e2424050306030a050f1612080a080a020c0a0b060916091202011806050301090c050301050303030612070f0906090b03070612020a0c0b1f170706031806020c030c01050106050f030f 82
    0xf46d40902c5008405500001a0380503962188840303510303124000d5003a02071903440341000c00d24601c8907040c0c8000641c0a170085240070305110042e10940d42c010045c0030419000c010b521120701c000e02c403c0e5000c1e4031a15000754541050400c01c45501c0d0004c05a061880320b44440304900342d403015030b020464800c000c0490380f40c40303613000480f074038002038004103c4101041800606103038403000031412143c500e2806c02c14020413813400c0361240310a2040680c5980184040b03809860841482603085c105082261a410754411040c40d02c40c825a105105190b0740e402c0401054106004e011481c2d0001c0340640112802c03c0c4015102800c0c02c540320f0340c1180e0210f010b04801c1e0142c102451084d4102201c2056803a082130b0010724140b4500649940310035801001038290b00c1c0070380c55284011060b020307246582c14120114000e000018140d1001c8001c130302990041035480c4010141100f00c60059691151084c10303103801e64006a010800f0441d040181c0c002941d03200094a0704003924080d401d030603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 438630458 1250 438629208 438629221
    0x7090314030c07060503091902010c0201080a06090c0f0e0f06030112050309040204090c03140c041a0909090a0c06050c0d0e040b0301110c010c08092e24240503 70
    0xc501a0803050340c524030a201001c28805e0300507003d9489428200c3c1107524211440707980c0c0400c146800c000038003142e0a82071580c01503000700305031a0b028102c40d9002400340d5075440762405550015448801044000400b02085980b2402460030040f065960005075442400415400d00c414420340150b100c00b0200c9904102061045410000005005644454440d244e0701c1c010002d01c1c0c2c02e100801c0c0f13004c03100c00d2890440325540340305148441640342005d24001100071424074021107a84c8142c41004103006558401e1840c9000d00c02d014020b00980e001e0b0b1401d01d0300020650041400d00c40148000e010904000500c800c888180d450100074400095000c54040c201e4008503a40c19424002400201c94440380601000700c00340c0000e11452040e01c406a608000c140c2da403000c01c0d00302e080009000000642019a0364021b000084001d04826014074200c1d0003000c500204554412815905910038078044005084c0c0d1404a071802d010042d04407803401d01912009043c0003011000892 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 438631708 1250 438630458 438630463
    0x90504110402250b0109061403061b040b1c110c1f0b030d030f0f09110d030c020604090605210c040e03040504110d1a03030a0302070f0609150e010507090314 69
    0x2039003c42d5080c480044040d40c5481000800c0074090150380900d0540000b900c00d814070003603501d84102401402c255180d000c0114040c1140d402034030441e00c0308000010300c00b42c5050060046540814500102c5000c044211080d181a0910a042c2020601120b0800c250201300140101c5020500181404e1a1200b4001401d40380c446c80b40e041c0100d084102c0c9454068001030001d20018004104000741c04205804894105001a107100300c0300c6910388550800d2040004d1542c0a0309062000645990000ba06640103800881085072101810092414a014103e80ca0a0b0a512061070340720000c015540d14040c9070501032240341c80d0b40c1040103100f41401114003601001e8000d001060310610500c10071762290340e28180c2c86240c10131820040035905642c0c2f4140170300034003651400840c548100e0107900001005d403600c18128010000040b02c1c2d12520a049100b0440c480e41c50030281c0e1030307000326101140d0002c0640d043c90108030f266948070744540d050346d82c000700c40101c10b03a01c7c0300c5151 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 438632958 1250 438631708 438631747
    0x406030210030b0a151106060102070f0612021210080c03060c070602030403030906021819080a0b190c08190b0603181501030b0f07030213050906030a0c03030e0a090504110402 77
    0x40f2902c1170750a54880356220040c000c5c03c0d080802100c4684c0c8400c401240d884900c0e21840d80161103e20080c070250384145540a8491020714025007061101a183c40803c00c00341c8401030003041c103d004105100040c007185080e500201e002c1c0229140450805605200740d03100140000e900100282c1058001d910001034660030150440d02c0746400c4044513556400c0d030380090b1003072482c2c030040181984441a100140e40880c0301600b07200c216540e407005840c40c0648407001c544c48000000c91044528825814100395541c2c0c1d101442c100008800c0ca0000c4003010b00ca034444c20101100c000362039010071a90088680d13211084682c190040c5142408024800116828445400002800b0782e403200b65016010b03046d00e0903400d0f00c0d507241c264124425204107000030003807100100102c6c074000b070115a000300090305545041c050342e524003040e142ea81d0800c42c0400c21881700e255241c103014884c5009001c200108104a08003a203e401d00041e108041c688920340010708040005103012001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 438634208 1250 438632958 438632969
    0x7020a060815060d20130503030412020d02120d05040609080604030f0f0203120a020d11030906130218280612080d0b060a09080c0904030f180b0a090807050406030210030b0a 76
    0x1722500000501c1d1100290f05c5001c0b4031500032106000401d9034036010045404540d151010100c041009074240b0003d01544d4900f6603011449020314500040b0034031080000d41c04560301c403540d5074100074001c2c1000714190804a8981e00110421001035013000c1a070005e42d040707090a00c04091081d904074914440c0701f2800e41c1c07881441c0d05014403489144c0103000704e030b4440a01481070708501f0a1080340b50100320b0317800103a6480307113021903660f01c000340c00740c0703e201d0019280c002038030700791031650310005025560306400e00c001201d01c80341e58924101058800991141c00e022180c0b80442c1007080044814000d0100203000440e00c3c2c0d00070003984059a800da016200c07a4a40340c03c8440074081c88494461540e4901030614507902615090b14194031441d81500c403540006c150520442c0d400e40ca022440c0c0e102c000c0340c40041980d0f00010068a500c007001d41c3c0d04401da81c1412032481c200350070303948043c1c06142045414401a43c459001c02d4800e010752800056040f00d0800045860070a82d124 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 438635458 1250 438634208 438634241
    0x1906090c38190c02090a0504020a1e1a0306151912020412050f1005010b0a08070309050708010b031606270e162c0607080705060c07020a060815060d 65
    0xc0d410b541e81c00c403107072a12041c0211000c00c05545d5a0046c44165030741118000d60201c444035050046017400c41c00e01c03800310200f04944d42a07a803681100440c0d0360314001322004181010081101526041c2c03590700080281071480ae0400918002c07543e00500849004002d20a8924801d4042c041c1d07030303040d03e0080c4620700d2214074220325030400648490002aa407005070003481071000811a2500429040700c45001d50b41d8500181460204c5034003101a2440c410951280e081d031022900030080c45018103140400094540424000c141c9007403400c01110782400d40c10002040890b402c094054590580910b010111000b111405100511a82c0161682080da03405002c2d0001ea01041c3c0300d000801c540b41c0c00300b5144150382841161b00120f280a03d8803501c04048006170078254090884030744030302e01c0e56003464201c5e6a51400c2850423500c50b00700e100c000c10b4850551030943d821500501d81420700170740b1402c0035030f070030034401d2101c5a880303000f2800010040c0d40441164818030105010250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 438636708 1250 438635458 438635497
    0x6080613081c091208040b010621090201200d021e0705010f0212030c09040605060909010306020904020408070b03070314070903110a15031b0e0906121906090c38 71
    0x504807074000d072003c7d10a0f030000c4c400412140d001d410040c0c0d0340c0c1010300c400c08001d6000c19202e00a41980c540482c1000200c52011000c01100b004c1e440d4000c4030000a81240100042d0003031903c003800b10308045090358500400b071a0000800c0c3c56090b5102842c20283e1400c40720005da14001510342d0003c030450f000010001d4001c40c407000f03010100c8040701d061209940d99020012103010300d044140c0d01504000040001030b0340c2d079005081c1040041c4c005814165168511030038000c1c107500002034260000200b101c085ea140c480e4095007403071031b44422818202040020402801c07404002d01d526045a58200503984541e40344004000b4045900c1e8124040423008004d00088249400801e140c14060b05081780109442c0210240180010b049596910200300404004400501280c021000b1807640c5080c070808250b1201e0103041c1c01305a082003803410388555050350744078104010300485032020b0000050240c5441006003035921099034045920b25800e88114081420b45125000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 438637958 1250 438636708 438636743
    0x501020c06181e0d0f0b071718121204020a06050c060414010902040c030e060f071d0a120c03030e2e033e030c040b0c010213060306080613081c09 64
    0x22030305d2400c511840c00200d81c0c0e00c50440903074a81c4001030130000c4171924200014100f1084445090f10b915003182150018080c16480b101c0550001d031100d220380a00340c0c1004203508040c42000020442c600d0414506003c4400507605d481001e40014070318640340c015506509000d402c2145010340040080041040700e40003c0e009024943c080b04032402010002009401c0c5024040d114103156101e030300d803004260407050750300f01c0c084030103e03070000c140b000c00b1030308144641c95058007500c203407001e409860a6040103004240c2c00d20a80780300d401c08241c101c0318507060458104844180041060515600600c1503024101d0641c8588407024154110700120301c11103a04441c0c07800010fa10b890710840c00988881600c0308070385440120100700000c101000310b42c1c0c02411518042d100050600c03200b101e2091000486501100000361a480184044c420600c041070b0407410a010820780d45440c0d0761880e03102e02450151b24100c4401c44a180000ca0340c07508803070402640306200c0b05100002c034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 438639208 1250 438637958 438637973
    0x3020c060c01020f120108100905030d11040906090b011d01050a05031909060204050415030203060f1306050703150e0f150f030102070605040b090d0824040c090501020c06181e0d 78
    0x921a507521445449070003840d030152032094028276a0000051490040708000d039802a01e0f01d096850701160341003000044400007846554007034a80f840c408588805101e000400d000c101140c120583e469807903180a80f070303170484101c40b5102c0720b9003041501c0755511504110b0001050010421242c1440c0000e0304018490740204181c40c4219020841605210805084d205180c00001d40550240007c03d120045414100d580200034220312071b400d10030350f035601c0144d50081c0e03141d2000c681c49000d800191070003044804090400004c40700d000c0c0c40d08920b09244001e01a1000d05084040d101c10f003100e03211400301c404101006402523550b075a851a00a0003804216015184419030001150143c0400f143d090041c0c2c141d0b50304d84c101626101681c01c1031552030005801d034000c0c030110194480c5c0b44c0f03002d0104a00070365224914603501c0e040019041581c01099184503203000c200e60003e4144030080485600e0094030441b5407804204805406c942d4000c5c03180743c1c0f00381182e09000410640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 438640458 1250 438639208 438639211
    0x3060f060308122a0304020906030a1e0308180c0405060418030215010b12040605060f040c08060112051603332c040b060118081b0a0303020c060c01020f12 68
    0x480c1203202c030b00402d002000c251084c0f0080010801001000810090b1074190030700d94006000400b03845007e1602d68414405901000110300720341c5200b0b4002c4203050700003240c0c90780008110184000400c1c1c20700d400b511019403140b10b034410b40d51a400b003260703a03d46500640c0030380f601041307050502c1101d0078065540c201c100d820000080d012000480d020002d00e003035036100600c1c52113095142c1c9981d540c49000d008001c1245400c61004007515100d640c850207941c000840b691078141350703070802d01300040c0b00e81b80b039442d00c000c0c0c02d0410b018003200700b40115240d141507803513140004000c1c0c400304d1400201e00b6a015604101040050002c0c21100c0403200c020490b07085040806541407100c0c1014000b2208601c00c0b5000e1220750001030126049860040e4413210503d010000070054100c14911408070740c01401c2d0b2035000c083d265506501030b01010055a6045511450f85803035660029581e100c1004954001d580114800700c40350000d4050b912510300da8058161195054140c0c1d0061400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 438641708 1250 438640458 438640471
    0x92205030417010f140f0a0b1504030506070c030813020301060f0905060109080105040b010302010c060b121605040e07030303150b0c010c1d0a05100c0203031b0618030403060f06030812 81
    0x103000b803004c4410200b0300c28801020208881603010790b41d9201001290381004018989054582c4046e440c160341c0ca204030b18022180c00807540e00c587c03d604080d0b1511130000c2c9084140001140318a0101c0c1d00035640c1a8085403c2400a030002d6541c80400d001d4180380e407126890041391a4003060990f80c640106214501c03e98601341481d650b0000a801e03200141e0f0060000c032183e0780144099481403100b844024020038010815804a034046802c40f80350040301c0406800420126400070420081c440042c082124180003184103503240680b108ca451000605250744c3e4041e921010021101c2d40300105614182e0a0311421047c0d4101d000c0c25043c030200b000205c405502032010103000c800041501006041c0529250601003800031000d0820f00090502174001452001650100010701e507107500d0385140c40340c003030300c6022103854600701800b1350138501c0034520018803d400000c141c0c0e04603508000302052601c5d079400100c0052203242c002809104001520bc50101286040b1901803c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 438642958 1250 438641708 438641711
    0xe061306080105090d050421170706060321020601050402090a0f08030a090f0e0a110f180f0109061706040b120d0810060207030b15063609220503041701 67
    0x5054541c01c4425204900070302c144038442d00c10010680280341051100c8c107105480d00e03404040e84500c40f9030150800242119002d0310f684043c8104280d080c0d60781c4050450850445180d0165440651604014001d50780200d078003207036410072035a4000b0810f00170411380310082c0c80c503521090040d841c0d81c003055640c0042080d0540006030394aa000d06801120000840e501143d221204028050aa41d43c0d030b83c451503800340100c0700d11003081b5005100343d83c481c0c011096007040318802c0c0300002c990044114107001720203804000c6507401816581404869030000342059590b103001400500443d04116044941d1078003803000c1100008004000000940b0b4410907940c030350300d00c40d0300070718a80941401600500410400034074044403181d0081d0b00c03c04456101155840420056005403011203400000e843c0c580d002100014501d4403590348014160129001c080042900114007809801d1600140c0b1000d0000d41c4089084140480c2d1010941760388030759641e2402d075022094201242c007035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 438644208 1250 438642958 438642973
    0x9021009062a081b060112050c0f030303010b0d0905030f0c0f0c030c0103020a0201110304030c0308220b07120507030f23070f050c0d020d09050111070e06130608010509 74
    0x94082586444400c50494201c2c1c0041c803a40d541c90440360440d0705840450001d01141c80440607042c0501c0703000e80010304100d51002c3d6a07080041c503020f003501a640c004e140156110280341c0f004000c8070f0550703500e40e400706e84d41c60301c00900070005c1051200241040c040800d028085050031380081a01c1501030007243c2140800d081e1468a40d0100d0111503803550200845401c0e55001e81c0151201901d1800000340c580d01e490010991540101c0d011030014000151000416810a16403904078034001841c03102c0410b02d000d459030500d0240c5c006401c503442c031070020350aa403292801c020300944010080c001c1d400c1046000c2c02070114000b44100007810070001c049028081e00d246901c10781600c4034110151180e2409490500212200608110041004c0340c0f250100b04032803100c5e18981d500400d440354038404010301426098000c14104041d680c0c803c4ac401000041c1c03a001e80c1c4c255801e800ca10307119100001d00f1121586a0342c40c81e0360600e6000036070814103500c018400c0086800340c0f40103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 438645458 1250 438644208 438644237
    0xb0702010209090a0b030a02040507091a0301030c08070b09011b06021218030a05090f04060f180c080c19120e1005070503091b01021002030a0c02070f080c0609040902100906 76
    0x10b45d081c1e481e595815034081c040800c094038040d00101e80003002c0b4200750301a207454801c5c0c400240f603615031081c049540000104108210420024010b01449020f0a5018103002d02c20314981b003520851810030099074039012070500c038082c00503043c5510110840d41c64032441c0f900c0020f60011220701113003000f101424400d0b80000300458408140950300c0d940f50608030380c00c01508030100200c09130007640d40c10020500044281c401d001403c0385400044600e02d08091400c140d0320a0310003c4104081c8006109480c14500c0903510f002114428a080d2031034007030011600d5102c444160301d106428000000c40b840c1c5e01140d04a900c0d515540c05010381d94920f0001d41d82c5210079240580c442d4041c01c04140c01e500c4403136107080085014815a0f808010503140032042ea007045e100843c03015902c40d41200c001c2c0c0c0410583d0028020752010001b0a454400280d444201520007903006a1001410811564030381c3e00100055a00812203040000c0340d50004041008a0150724007081413081043d00303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 438646708 1250 438645458 438645461
    0x60905070906140a030905100e0a05010b0409030503071d10030614040b06040b1e0d0c080603120a030b0d051014010e0105060a030207030e0d0b091011030f0709030b0702010209090a 79
    0x40900c6a80105160044c02c0e6000c17401020030950590740d41c068002135401d804c080e401070244000d9250000c214010160511500b118a07480b98240b0a44c03514a40c80002a088410741c0e5000005081240f24941c0305190b8104104407d420907a0003100189d02024960301503100c00191050460713440e9044120358284070449070360405036a444070043c13000300414481c0300000c00a001024002130030b041111411480b1981150b00e00103a500d494041704545180d01c0507032203a000100f10700600300c00e04480d11a001e24480c3c440d00d201055102c440740041c0d81c5801c040b03240620340c4081100d111103a000302d194001e1110c1c2c0c4000c000341034950000960041c2c03500a46060740c1008000d185410201c506c00e500940c01514110240084450401d40070799803a41d50b00d003924001e1038102030614050801c2c80c1001d90484801c014070b458025004250142041603e40c401c1803282c4940f520340b100d2105940f90303001584000c0c01501e0b900100109140e0640183c002150241c1c2c1240080c0c0340c2034640070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 438647958 1250 438646708 438646727
    0x18010e0d110339070b04090507080f0f090f1006170d092304090f0302060a020703020316170706140601050c0c01080402040225050f030901090b030910060905070906 72
    0x841001e1075038440c10b4245112032042c2001500d40c24405001c004414480782400402e5000c0194030002007402c1041d0f00c0c070f6000d2300e98454110301d0007400c0c8d807901c0068260100700103003008484004c4c4100107017103001e0400c490a011100101245e040303685141d0758030050500790080c2101d208200010ba150000300080110f950346050710344600345418500c05080e1080d240c1d02d001440324490081c3c1005803a54459214500d02038024400400718508000e85080006854412039500c104110700110740d0210030f640307001c004011004961043c50070070711135101503a4040600104001890b40070000154804910340c50300318060521650b075640103484e00d005a90f0341004903000080116403540c0306151241d805403000b4001420a0504500b02c1c908504902c0700262010350f0340180c1061090420401c0c18944256000358a4041e010703000811901207803090710504580400880c400e0b04080c448109282d4158104000c5180d6449062020f0201665482c02040b400d0000ac94018814811407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 438649208 1250 438647958 438647977
    0xd15080d090303300b040e0c012c03010203190c020a0b07120e16090b0f030a02010809010e160519140d030c060c022103040c0302040518010e0d1103 65
    0x941c80c0c01c2c61510b05071100d8408a40607581101d00c140707003008001c075404040c0e400d005041c0c800952040350500380f1085901d01140049240e00600304052130307a922680d000c075603222100010141002d805104172020085140850740b5500110412802078a80410708950503140401481070000002c0240e03211408940041c0000441d0000100203900801841c50405410f40c0006000007034000c1050505081c052500002447c1c5482004101c0a50041a04c8600c0c12500900f060b19480c00103039443e0941c0000031b0510421500182c142842035002c02c00540e001c6096403076882d0a00240d601c41d003175a001e818030608650030401d000081d000050015544105000102c00980500700030007640079000845c00c004220812100080702ea001d0419803030b9050b002007601002401c280b52010034241c091170080801801000041012032070000100c0382c06a0740091a0303101c0c215840c0800412a041c5d070025801e28042800000000401c00c50a03030752645e9201c00800f54000841c0c032441162840c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 438650458 1250 438649208 438649217
    0x20303130e061e0f060a02190602041a0c03070201030b03031210150201020a020601300501050610180308130b0a021b030106120b101a190c030516060b060d15080d 71
    0x4c00b02c0b01c2c100000140850a842c2c01142c21400480c00858811451941c0841d019138000c00d007000300740c02400b24a0580c0380c0d05407105040c440200705d2a41ea9004411007c0c2c1015202d6100d00c0041e202841110080054130314007200314a030550381441815064071403480054040000104403c1c410b20a44882030303481d60160401c1d034a0035682c07112244052542c500310601c3c500d000c221584c12100c074030000034410b170300114091a10208203c400109515450b081c0414003002c10301501b10720604105407940514056141d4020911a050290b100d401220050038000b44000d042034000802102c00c058044000d13144540c2c5ca4103043c02d8601501c1003621411036000d600d400642c031138081b02d90082d21009900040d03507940b119180402c2e45103503824600a03001482100450811084400300115030410800994080d0342c010542d00c900489a0462441058040e08001c001d820001c440a8002c0c2000c0e00c4000f100640030040c40002d900c10300300d4241040028115002040240d070060381030b2107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 438651708 1250 438650458 438650479
    0x60a050112090312140907270c0207030f030315090b03100b0f030319020607020a0305030606130e1501030f0615050c0102040f1503051005030c010c020303130e061e 72
    0x2030009451454011000c0c00074000d4015220280c0c0e100e22011740c840c4019a0455003880e8040d070307003030803a0307a0820900300b071005000d01c9139a5185400c2508c0d00e2080c0c400050603020801089081c9076454100410000069440b50f040c10383c1030b0000080440c6502410074a980d4451101040358030a600054141d0810175544150140e02da1041e4079584020300000302400c0d0f50000282554885041b00602103204131110540700d5041008aa00100900082803d0718058034090035501000f40079500c034100000303045143c1c07400b88503400e006004070022090f1600340b0308032542200700d00f0444d80740002d14000c1001c42021160140384100c500b02c02042e404100e0070241100c2d590f0104c1c0040c0090342d000c010014551142d1149140100290404215502030010005050300c1029000407420070300780c1e00a200b04d6501040c2c43c1c11a0740c0908001141c00c20301e201007815030141d4101053392100c941c41c00146007491881d0944224412a1000b00c1ca07807003801c44520403407101a446802014108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 438652958 1250 438651708 438651737
    0x110a14040b040603080408070e18060f0618040302010f0c0215060405060105040f080105250e010f031d0a050c180c03061305090a060e19060c0e060a17060a0501 70
    0xe00151000c00701900100fa402d84a44542c070807a03115602c8510541d00910003042070a80150701941c1005c2c0c0d800302401c100021800702d44c0c0d2410f01a02110100c503500010400c0307542ca010500360355095408051043e4039185c10081d0007404080c03944c40c406401c102549050f03500c0031401d00d207403012406000045481d0703c1c05000c002c10004202505100b003c03c408925051120408402044124000306151421506190600c03008080249401107892442c8144980201084c44544020302c2d01c855031a00c01601113024140c1d030514100611098034480c0f0500402003054010380780a801202e0761f418240301800902c2e42c01c51b2403a01c480c8020404181141102001140c02080040c4098017000c10401e100e000c5400c1504d25010f5540b0103119841040418040d04401c14518030103407800144220440d4042d100681d8003c01c41540e4074002c0f8149070040301700c89048200900b08545410540d103018080820181e0030000803075618001500901d000320450302513582c10b03510000f0300407245 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 438654208 1250 438652958 438652961
    0x206090f070e36030d060f0b0a08090309040603050618161505070c060f0e0a0b040306050a090b01170106080c01120b0117070903020a080f0c0108040309050a0e04110a1404 75
    0x52052150003d9070300c445100040061002c0303490040f0001030341ea202c0040b0043c10071200300d40d1010409101c0d001c2c00f0400b83d6480400e44d24294030070704012646540d11000f10341184540d482e0303298441c0c13a1440200c10b1090028096101c9e0045401c0030f44540c82485850b82e490141240c01c0d2003210000e81e0601100328014007040c0d40b4016424140c0c00c0400990303c000c1d510b8025041903001441e400002d82d50154440c0c8014400c0c0f100350313100220302d420045914118480c0340000303421592520046140c1c1c606561040201035000500d017115540c5509180020540e203000c2550b103507090074404200540007090306c5004030016110403140d580c80b040130740082c1024480450501c091085008403c00e0718460940c42122035948403c050341c1140b040020b041d0b030642140701705600c41d8110756600f4400103141a8100002d003091000c1d50745600c1c048034541c42c590401500200035400004050400f51a010b000f10b1080403809801d0108500f0300404c0c50303461007800e0500104050300c040d181420f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 438655458 1250 438654208 438654241
    0xa05041e08040f060f030b0a05010203030a1a040203041103061e1303030905070b0a230d090c171615120203070e031903020105073b100206090f070e 65
    0x1d00905052070380e102c8000314242c4041d8003c1c000700c1d079030402c2145811b60511072420f00c1c00d01282d1516140b0b0800c40004d40d2800020040384001e6514081024007504201c035030149007a0051055649151a1174044501c220b9080814040c2c0700742004149101c445043d000d0404001020b0303104155100c42d802c1030114118181a81071694900442012860920006025050041300303966074444032900200b0784008007100c2c125640c0c054420750044085035088030070f108240b91000c42c05c29020305200030f050385c2950040c5403002c03010040c40e940030004152000c2c00e55000e8100c3da00151303100220414403041c100326000044200d800c155510186070b01858016103140f40c005106404840401d1038007540f600c072030420744031541001c420980e0900940744c0c0070500740340910314030f091406014061240301c0d442c030b8100701c03a509196031054050800f40903c40001401001c0680102e41c1c0652180c00998144070980600c0f1084003010600080403412112000c003441c190b03613a085100d0044024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 438656708 1250 438655458 438655463
    0x904050604030302070f1401050f070c0c051003110c06061503090a2409080c070605040e161e0806030c04060605120a11040b030a0f091a09010908030a0c03050a05041e 73
    0x6c41e418040f4405018200c6048100c100010703107801c02141ca800c0c03104005129600308004402034000191490355070745c049030302c00c0e01c0d000d82d0104120310640181140800e040c07805c0b0f0300814084c8050782c0000d202c81c01094280d810701101c4181081c1e8400321300c070490704d41d40c09612890f2028002640701840801010b0184e00c0c208045400403003020070b56801788426203d030f003000704507201c02e11014003400c001008181000ca2410303245c000f80d4151084010001020440c1003042c014500340245840d40c100d40010161041080c0f2040020f081d920f01542d80e1030283c0703e02c040c69192400c0ca403007910196041c0d600e80b603060011100800716044c800511820340261501c440004a200d004050f0000d40322400c0d04540380e1900c040d180007202c2654001c10300d500c0c148520080403440c04518030b000c0240c46081049035a13650407185025105030a001400351a000003041401c0f02c80740c0c0040c9040a0564082c484d58031081840f500381d80066802400c07900c008440030a40e10b0191000d00046ca1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 438657958 1250 438656708 438656723
    0x20d020904150c05180306070f0c030302190306060314010e01090b03070b12071b110402030405031c06050f0108010e01050904050a0b07030b040b03030715021c0f1406090405060403030207 82
    0xd030041c07222030546103502283c00200f40040355072400581180040720a10303005400034402071408003802424050250921006e00400d804001c05041c2302c3d8040b03800c2d201c2178480050f035003c03407142d0041c01000c071486688002031520307240380c5000c20a402164103c0700081c4100501d47d0030640020000c02660780e840da4584100240001e02d404080040c00d0b5101c18101840140e00d010b1a0180c041c1643c444011415086454081c00061540c490140d483c1400d8a00503160358a80c80c15618600c40c201c140020000d81d5010000f41044170b80024041e2042500c00b0410300701118010343d01c05000303006110396076030024014002414000c2a16600c280200115034030b19485e03868500101e0360540b25000026140c1c8101280c90a00740070380090b04900303900545c9402440d80b00d010b034242503841042e442c10780001d04c43c0b003803e504241400d044c2100940402240c0104690744000f00ba0110000613004a03010000c0e21600c1c10103041c0c0e1041c2d0b004809042c42d940d5660301200258410117007200c4a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 438659208 1250 438657958 438657983
    0x4050417180a0b0702042d02071406100602010c020c030a0f020414040605010503010c11030a080405070512030c06010b0405010c0305030a1e0b0108010905070e0108152e020109020d020904 82
    0x541c1d800b00300710010055114041e81e20045801488140c0c1c000b014a8401905803003c13080350407e0b4003035600d5808880f080c0058807602c2602c0c280980c0541240850020b00c0366000788825450f5035481c0c00c048411a03002040003900029086c0d17100c1500c801d2256140c1c128003480c00c00700301c0022504160a10040000175004070402c010a85e061060341c046c1c03051030381c1e080140402d0400748500b40e40c0c0c1040c0d0402d184c005e00c5d03c43c815980c0340b02e09014402000600000700f02041000c11090018240080401c29800c0c2e992031410342d00d07000300ea042d050501c207401c00041c20810b001c040707030305840e811f03940c218129076551001d543e0340d03002074072144e0704946d58003101c0c0781000000110b406000c0c01950100b20995032400041c031041c07041e00895940d514120901c100e068002c0d080314244603080c01c010045544082c890358075020318540154018014009000c000050310500042a003084105511256480ca000300c2c00c885200100039004042c0b2481100945080149030364018885c03c0b00643c01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 438660458 1250 438659208 438659257
    0x15060c0b061801150e04060e0601050903010e0d0507060605040501030b06120708070b04092016020a0503010c02161401090b090607020d0b0a0c1817030f16020f04050417 74
    0x41c41400d9000013840c2ca02107518210b03007a880344540254910071a01440020306080c4407414880c07014003482d0500c880028009515182074014000702843d8a05a5450a030030080150640c2c0c0700d0304044802030300d0040046041c1c902446080c1c180e0340c00c1501c04090350780c0c1c0310130321040001142c5148100e1140b01c0e00003908034402c10000c009044980c21840c1c49900e00341c4400141c80c1500c04c4e0960040601d801c40084050210548422043c0480c0d0711031081072500224442c024290056601542401c58040100f41c0000c0c8011400484502e8003600903610700300c1c1c16642c450314103030038000759164004021105040c80508050b02c00246401d103040410350018140d600321440407104065920100014034000744140c108020303090034100d2040101d84400e040c0c00c90103016041c0c4164201d120b00c009a101001510103100085009958a00500c2c1070a5803184d2490300485c464008100648114103080c010360b40569480789211016040c0403042440603049445060300040708603290080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 438661708 1250 438660458 438660499
    0x402160b010f060306091e020a0302131212020a03020c09061809010c0e0303130b07050c06121b0a0c02210d081f030f0f08070605010b0a020115060c0b06 67
    0x8080840b000848036107061006403e5404a0780300c862801d14003403503a2500c0d034201d10b900300c0c07580204100507500ea5801c60150300a0285240c0e5075143c00c880200854400340c01c00c1c145060030300441790400032030910f0f0f5040340d960744a140c0050050f041100001441e040882c511500701c84024032282d804441c0544d007002482c012942c400c0382d0381d1101100121550010010001c841096014616210a0180c4110f0002981c810720300c00d298006407840078890300b800810035101008008583d500b0014406d03c0840005586c03091040303907d001c0d040e22803080102115441640c036100c00841c1c0040742c00700039029070b8141003e50310001c1102c4200090700140120020400d16032a502c50074141b54031222513522080110103504210303004180041032004014469403030b031003803003220807002c0c82c503000c5907a0140c4078004210f44d0400c0c00116032144e821014164420042d8000c004101146051031143d80c91849840045078110030340c6004561000340f407940c0070303c014183c2d01405600001455 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 438662958 1250 438661708 438661711
    0x100306050408030612122b0603051b010306051e030703050d050a1d0117090309060f07020108240f060c030301030309030b070f05030f060d0f20030f0c0402160b 70
    0x4600b0b4400000b00426071900050050000e085d50004100203400030f410000d840c0b00c0d800c80703050b00c0c00c80070f8102032540066401c0f210098441030800d20a42c0c1e524940507030359218002c81890205002108105954070270312801707045410040011448900d0080d007401213000c4140595054092850080702040040001441c5915250b4641d6983d4049001c001c040b505504d4140204480320388a01160781c0e031000c041d101e040043c0100407000c1c1c5921403241e14612079540c07074682010300491080601940c1c04007502d80d41d4002e8840e0070703865842800b890000c0400c0100c240903180c195441c5212428040c0100c40340141c003800243c9082d655400d681c0c55a04245c1c000c0700028542c4e14240704111800300e09170b8200311a800d000241512417000501036000081091148881c1c5000143c05540c81410a810741a00030800000004240c1041fa2046036100c4d211406000a03d40d561000c0c00c0c006040003482c6c1e1020054000705480780c040102030b60108040c0841d41c0d0104100e1000720baa40060103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 438664208 1250 438662958 438662963
    0x405070e03100b1003020a1704030207030317070c080f0409141e0f0708070c020d26040503071401110708010b03010b041a0d0c0902160c0803031b031003060504 70
    0x8620300d40324141018588121207200d510b6035030902c0c0009a65860349500c03480002c1c218100903031504030701d400031900107165165260407002c1003410302081c15000300300242039a00035603524171350388075407094209002004d5076203c00142d0f0100d81f00002c01c01d1000a421103d50103541546000e9031221084280c40c010380034031000d4451301c0140304030603a913803020001980c0014101c0c002031400c4282c408013545c00500040c00d00188a0002c0c02003445815010302c0b080d4010418580c4202d0340c2800301c2e23405003822720500c03000402c0d9507440c01c5100660039903044a1005000f0031040742030903c00381c6010700d11280f10f41803000c030002007400c820042c4013070005089107600005e80e40c68201c04060079581e9024905004500d88410090400e0454248406294054a8110103140a840e21010582c0103503c4000014404203085a03103480d8442d103032960900841e40c5c030b03146030380700e0522982b41d02c801d40700640040922554545401440c00c080c5900504180c4110b58007035a030341f2801e00395182280c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 438665458 1250 438664208 438664217
    0xc060c0c041406090c130510081602121b07081516050415031e15080c063a113a18061503121803020f040b040507 50
    0x2000d42a0920b441405040a02000c01c00000e003400c0d00442c0d60f403400a822400c1c1c3c81000107180b4002046024540001c01001c0d100c4402281301c0c510060030010180e40302d6540f001030f102e44000d420700c00511880d00c0b0801842c02407500c040d24009404c01e44004a000c10f0501030203a0000703000d0028000341c0006180c02c100c5004a03e0044100c2e030024a0b1a0506030030b2101c14801400340304920383c050700e1040503c0c103000035585c01032484117080f03032941c01540d0961410700c001d00200c3d45150103964101c4402d0800c40f09012038450030130480303004483d0720401c00b040191021312070010350000c3c2600382401c4003900850114004421003581c2200c002003015100004011040403044607a098000c5032079194081ca00c084c03070801c0140280c9a90900c00200d440b00f502c2031181b06481c1c52001c1b00c0303910540403c111840900c0849264900d8401918034824030807402030250b01600c80c1080d000800425900ca8609541c03c114407150034284594002c0c5c2d407a64508459241c5100344e600400c299200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 438666708 1250 438665458 438665473
    0x50f0a0c170906071b0c0501030e01020909191a24041a0405010e040b010c1704050307120302160602070608041a07030b0f01030209210a170706050a060b07060903020c060c 75
    0x1001d000710b05c100314410103040c01c0b440c000300840c00800915003030351004d1030082000707103100c01458060700070310104540c4450410107011440c2f50101680c07590403420300b82400350403040f002e0851628a070380041e68001c4021a0703040c0624038a1461003801c211401c1589003099128424015140d41106540c100000f0001d402d202c6503801401f4140d10303990888081c0060b84145000a0098550b49030050003041d80d03d149410540c1103509403405001e010b400c41d8406e954820348000c00c000900c0096016000300c14240c4003810041d45010240c44450f0010104103141280c02c0700d4030400244143e4003014040050000002c0c820038184c018101030354045803404510b130400c07a42e2500d960740d55041c984100308200c0c480c1c071000550380c0202c4a0350340c403001e4540350f8200c90341400031071480100903156240e103401101c400c5601401400780502030400141e62004041c40880d045401002d21618060010000081441e0001c14000b40710f031069a0100031301c4400316025402902007111550046030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 438667958 1250 438666708 438666721
    0x1e0507110604030f110301110a02010b090717010605160c0915080609120705120c06040605010f03020a0b071b1508090c06030115090305060109090b0a050f0a0c170906 73
    0x1240024000022035101d4a003a10b507030307103542e11040c450384001c04100940400c1c980076034007984409007107014402256079544600100a000308221a611441030007000041000c0074031985580300200c203c0d414142c1244d007045000d036002c0e0056600040c030102d08000140000e000c3d00ca800004101d01c00000c03441c90000c00c48070004c1072890300f0105480c0d0000f030800610203800201110020700300107601d0b0740d40c01e81c0d080041c01d0512000040158080000d50301000b0f41c40002d0a6204900035041081141d80744c40035907041d040a07200181d071200304030a05026104901c03000781611740c8582c91031a201212403000b01c80000040c0d00c03e05030421466444180a500941d0040d4840c0001000e00401c194403000103505000601460032548504039041e86a80c4c003610b8044050b40d080002c4a8107580c1d2180714002a202c0708204468203090341000c1005500342e03004803806201c44640703c2030142d640d0a43c035001041c0342942d08040111240b180307207000488002160150110401a003514a03000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 438669064 1106 438667958 438667973
    0xc050309030601030b01050a08030f04060f030b0907030506040b0621091f05010603060e0601020606090c09090408130f0e0f07031b030c03150e040206030402011e0507 73
    0x20b60011052003007503520a8102c8100b21080302c0880d032038131a41501c80c042c0d0202d03c048402c3c244014071540d4010300819070108500d14000400c02c15000c00030b100002c0607114040881d03541c2e014814a41014002d071781e5401c0040c0c1d01d4601d00301410600d00004004107945100310035511020490005003484a2410820200d21140f4002d60b00c1040e580180420f10800020900e40403000036000c2d01c20000341c2c03050b4030580240140c3da036000140035801c44010410519094204030383c3c2c41640da5020307407500072400748207610b85940090f003040115180c00d40018028000c1881c042040c0c0404251071544682c140386119034a4490714016006406181c481000c002000984505a00e500d23910030310019030345079028800c034000c003d412003070350005004002c0c41c2e080702d07800107000d4281301d40150f0f017140c0b062401120f2200c4050312410907020030f01d0703420001742d00000c1040078000388 = true := by decide +kernel

theorem cover : BRFrame.Cov 438489208 438669064 := by
  have h0 := BRFrame.cov_init 438489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 438489208 ≤ n) (h2 : n < 438669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
