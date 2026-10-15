-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4915
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:08:40.537545+00:00
-- url     : https://prove2.me/submissions/ee6a3eee-b85e-4353-9118-84512e22d55d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 883812949 ≤ n < 883992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 883814199 1250 883812949 883812953
    0x106051c1a0a23250509091b0703031401060311040e0406060b040b21010b0706050a060317070507120308010b0a020f240f09120a210605100306030b07030f0e0712 71
    0x1080100075018118940c01c1d030400701e1030005c1d0150083c85445801014620002208088000c2040780b080105820742d41d91030180e414020050001c0700880c40502c08000e00000e040c0344a8400c0807064032807400c249090034144031480d034514001070000d0703030440d0b11901d0100d140c50905001704002c10314400034654514042050020320728640c07644040c0c40d601007004000380440003080303526180d840070780040d55035501c1150100078801c942015101d021584208001e898180d40104952070041c402ca40541c0d6803044c1038242600c1e0341d0303401400580c009004010005801c80504018071710340c0103071043c1c5c269840480345401c03201ca216100c02c440f01c544004507444d801500c1600510380b1402c2035604d15000300d090f50340300010740c00c2c0f010000b00001d40440c090712072910b0030241c16400c281c05c0c0303400f403e15a5800245c80f05000b020300c203500d0f0780c10350007032710780223104010843e42c1c01510000d407551090b609400401c84c8202c1c9240da544c44201c00c0f0941881404070402034101c100003403610780c41074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 883815449 1250 883814199 883814221
    0x503011a0405070e010e0d0204090c0b0306030615060909040201020a0212011b0302041a0319061202150a0c031103090a0801050f01050303040e0a1107080c0106051c1a0a23 75
    0x3e85100240300758800340d49000e0b640501b4844074400146c500300c60740c8035103201040080200850103130030311a681802003003480c2243c0040d03000b690100e04444150f1546035162069125544840d544842d04005600c003a0400d185100d501c00d0050056641c034641640118090078403107100e4110f5039640c0d044001c0b5001c200009217520408900e030443c1443d050880001290b100c0c0011025060008400501c1d040018128101034480b00801409010780d20f8107540c00c90b4600752000c81c40740140744164240c0060020540e152a04035643c2c59180401984058900494904081c0401e0004010b890943e4481d45880d20080528100014291510724074041d000281a00030500c6600700300b100b00400881510b0b03141d00000a03e0b00050003101510381d02000784a50741d4002d0452030081006045c0c0b24040d4025821035206445030301c1072090402040c0700750b9025000060185220064160b1501041600c007a40040c03d0180019190410401c0c0b01d6280c2115802031500c0c4440800c1000361042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 883816699 1250 883815449 883815451
    0x45060f15060219021306080f1506010c030c020906240306040507020f0307060203060607020d030e041d1005092506090b030c040b07020a030c0b0d06051020070503011a0405 75
    0x1d101400c5a44050b8040c010f01d8900b585010307200d441504d000480c084050b50000d4020850001111b0003203883c1c0b503070551224000807409040a03501000103142e54041c0c44070746d4441d41d2554455074021495400c200130010007602007a0000010307000060322400740c0454403040a0002c044645030301d05101008103030340c1e000b050403003107400001004180a80010076140d002d80d00100c0944c0720303900c090100740c090054a0012303501c503a40c0300c08038041c1900184405106c5409450034800076240d40310902181d1a42d80103101698020200e40180c15015846560410f00f040143c3d806221f03515950030000802c3d4070380e0054103c80d088200415600320180350001c001c0340c6005030951400c0400042240128800d5481d0204001500c00031580d031900e046029550110300d26614589403500d404558100e103007003440d62490690042076910b00306010b603080c41d1140c3e440480410018481c610040311031011001c0ca84550440450156000c0c010220302602c1c0d01c026200045c4984100400d40d10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 883817949 1250 883816699 883816709
    0x610030c080a0f0201050a0e1005030f070c080a03090c03020405010902041d04050606100c050a0b1603020702032e0f0911101403180316030345060f15 66
    0x40040d103400b00007102c10045449058090a0042c3c0300c0140035825909080c2003918103500514010311601e0940d00400518000d4100500c640b0103650b6541094540c902e034203801503d40700341880540041031003900310741603203071082218292150b035a40c00301d81034403000c0e01300b810340b590080b8060040300641e00507c030880c0910010300403103052030303142d4540b18040a48190300900301407142c01c00040c022014021000c0e4030038200c07034105c10503040c03281c0202001e50703004245201c43c200c0303440c0301c902c01d00a6544454001b0041d00c00700c4500d80c12080a0060f0103642100720091000d0348542000501c81c5409407500d034940881d030b01300285000b0b410075400741c03502c41c4182d400c0c9011221440d4000d0104400030048030031907030749444401091207500a9504020403902c8000303a405500322040244240d5284643c8003400124110700c041501c0c58182007000100248030a0640c50760b00c0400030740d20980d061204514008c10003626010107580e03800104070707000f60301c0d41c40206107007064a61510041c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 883819199 1250 883817949 883817953
    0x10020706052202041a030a150b0117190e0d05030601030609060b09040b0f211009080d050c040f081506150406350a0f0c080c0c0106080610030c08 64
    0x100c00060990107100040064091342e0785068180c50a400062182030302c0c0b000a08031241507903503181500041203403401c111100e40c00c14500d100d2650140402505021104107402c03107981d5040c0264181c05084000403205036210450001c40c4001800700c422484490340d0785580e80d240010000d41568800d40c00f50001ca4a80070040280d1503840c002e03030380042800ca50100d0350518042c00920310341d01404031550703c1b00c215038400d00c0d034201c000c2e00010301c5000c40050f07a00b2a88207088410407502501000f41c010581041480c1a0050b103500a5600c440d2030070429040903152701080f80405219000703c02ca03640000700300d498248800503000d6010f8400c5600c101100c5850501040c1070003248035510501c02d10460703180c4001168160348001340700b200c140144080318407000c0a01080191100c0e0102883c5c29003024811125008a4641500d9030726070341016201c038030403e400c6a001e1a9080350556840c036011500b40c005014480c06140c1d0b01400c005901d085041103007008059a0118842d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 883820449 1250 883819199 883819231
    0xc06031602151e060409061517060402061e19110f0c1c0305040810020901080a020c1902030f1e150f040305071a010602161d16050c1002070605 63
    0x141c90600500f854410002514055a214140401c021380382004008007414182413141403604280004d240c01c0f02c3d07a2103205410007022032a0725403070706403d0790041d400090400503040300090f080707800c2c0b1f42643c001522624208800c020060380385184500d070000687c0d03038101c0081c01201081540c064040c02c101034024444030f0310000e04030960040018040c0f900004404007410b02400950700101803803000e9925100924503294000d5009880a50100b1a0000810100103103807003030341c07038000c3d10100401e04100124400c503664814908101e07890701c1022a410703010b141c240103140100041c01d48809070b241240703a80ca030426080051085004e100302007080700d140507019241e03810603018201140c1d510228184841ca54407003880ca0b110070720000c400001e010f54001051400324800e92000c82c0b6654036003951b981c0070f00d80a08504000740b107000c04030340780e2004800040508081400c1891a0600040f079440c2004802103492089603130100e011b406001c0380e402040c0c0e11800030b00c060340305 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 883821699 1250 883820449 883820461
    0x310020a0314072c0301021b03040e250c060f09050705031020031305060103030f180302100f02072606070f02030d0b01120f05180303090c0108090c0603160215 70
    0x102040946000c16030041301544140394800b0340c121000f83c4803c5011721210308442c148145d40c0c1e0b00512a10108420076000201201d921301910840004d000002305480c071840d0004a60701010060305035004d47d41c6043e550742c0d1288902c00d61450700c2c8218064500a86008201410045100110b40682d070803d020010761400001c0046604202e0054881d129100c108140b82d0701c0b448954001c2040c0f150f04004401d0640100301c07074910751125a01c0c640d48405d08070314540350303090030b201c000d420620700211003c00034050041c108000c1800c2c41190a1a0780c1c8220504a11181c0c9540e0800a00a9004101c10517002e01000303500881070700340400d011001100c003e50701d21030004d000f041560340345602c180c0c580c812004160000d88103a02070081403100007602000b014255170301d0543c1c4008680c410300a06020007903a2141e26a00d000d444180701c0500196409200101002e00314052552030007901d5aa6402850040800340300000d40890006806407828014404000101c283c90f000c01c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 883822949 1250 883821699 883821737
    0x1f0e0303130911070501050f0f01080c06040501030b180a020717070512033301260114030a140102030609070201090c170c0a060e01030f02270310020a031407 69
    0x204540082d0000240a0806040302035140140c03000184a03500705428481690504502e0038041e1081c018013641ca666580300450b030300c2d00d5800009400541c1440100000c0d0b000e98001141d000d03001d040744c03030b1107012424a1452401c0c11217001605582c0421030000740800d640201c0d20304440c1c800124078000d41764a0b4a641c40c285003210070341d54000000080d141c02400d6018407120440d070b0b0b1012080b03100354800440c042c00c070309019900103800f258030300140501c00c041c01d920b0754100d44080103003070342031001d001c15601006280355003501c140900070703001480c1591098805811a8001a200d04054040061104000c1c041c841160304103010440443e100c030b040e01044801140000e201c0041c15030032035007004140340001d41d21208410001580c40c0c1c03c502c5114003490266401c210a00c200f000500890140d00c0c0300904170b0520b081091040700071050700d0f400c00e2100904441124207820b00d41000ea034401961840080e40b5868481404c05654194540203030207802c04100f003031b100b542400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 883824199 1250 883822949 883822987
    0x180b0108100204030c051528080f070f080c0f030c031b0c06131505100306050c0f0702190806180d0c05030306090a11070303060f0911040303030b0f1f0e0303 69
    0x2e031180d41c0e80751200d0307d0180c5c90422078840903200403959181400c12182140300c030304a00b05460105410300000b0b200c1109502c0e03100d200d02515110b505103038803102000c036010800204981c003070010800024a0800044000d0341c8209803008510382d4034542030030794088508400040e40ba54200600819455a60120b501c0713612448811824a00d00c05a00744281c1d802c1d003080b2407568007441c041c20301402020b0000da14041c2c0b0702560701400356460f400290751052107054214501ca40b0300340312030341c0140341c09111075054072100d4800c031301125103d040160521000f914100c081030110140030f41802010300041000380d149003014141c220319919143d84a110051980e4421100d41c0d00198400440b07501c070304501c0051a031745541716038061802400518841c0149a0421200440011040d826010781c2070025114a10103060600d5590150050714072403c01075482241c030312019040d40c9407056424001c0c80310004d040d415500c10703100540072080101d0326a02039007040140c0e1018541d404c00003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 883825449 1250 883824199 883824209
    0x180f020708031324020c06180706120e07150215010b0405090405150a090c050d02030a08031902030403410d0605030a030f0f05070c0e0703180b0108100204030c 70
    0x99154540b0070f10302055aa0072800a80108440a07640c48113803140540c00360968100c20000c582d2035851b81205000031001d031400f80c0c0500e44c030800d000d008003031146040f0000c48805082c080f5840300c01c0034469047c511260000507008003400f03150304d0481da041051503050b106400030280365504000d205040c13481280240d901600c500000f04040110800c150750400044c604c8492440c208105020090b140840d801e8640460741c58010400f481d10219880c001a8002c0061402210030354403110070350801030001040800500206440300b89500043d40b04600c0380d03a5607081400301100741d280200d004502c114689519040a000c150b444241c28208001c071404004e0311030100b000504098180c5411944d018020000e0401c20540c1206000c036480c13645459142840c1850402100c0c14044c019000d0465007032200b04003c6c041708c42c018079802401c00d18012880c98209074001310161914402100c00309403002c01001020002d1203140e01840240c0000d6181502c3e6840381400f1100c54010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 883826699 1250 883825449 883825471
    0xa060816030b03160e0711010209090105010e0307030f081c0b012f010f05011403150403120b190612020f070602090109031704030204060e040b070f02030d06180f02070803 75
    0xa11600b6581c100a40d4041d03000014500310710580320a0700c41c0c00306400b91040c2000c0b82c01d10440c3d80317001c0c8041c026244407183c0a0420801c0e45c3c40c040044905081d401002d54150040e4072011000c40d988105c464030303850046031a01d584001c0702054440400c500c0b6908100545024040000d82ea440390340312000d54902c0100c0040050410b066058032100750f4142c00d801e43c80c140002e5030500c6d80f50031150403610200c082d071803002410024592101c1e44000c204500032038000c0041d0002e8083c14000c10401ca9600700002c481503024040f5070403160b0003d605185150700e0a082104c5684901100e80e0030140d08002e50902392000d030010014018420011b20b565008aa0035041b42d1284144000a40d0090701c1b05500181072052600305034098003050f4000c90600c17801250890000f81606e01039030b4040c8006400c0d80d250042200d000d00781804100c03c60204001c0c0c00312104541c0105006086400c15040c140640c5800c1902140d0f144650505041e0050101001241030030059039402102040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 883827949 1250 883826699 883826711
    0xa0e0d06060f17010b01030c0807050c0c060c06060405160e0d06020f0f0703080106030c0e1009091e0e06010303090e15130e100e061501020118110a06081603 69
    0x40e14001800c0740b5004a034586410b0000020036800d0506480503e121882c020010000c0140045080c1d52210001300d0100f1800000704544501c100010b2000d000500305481d50900c2c2e040001c1c42e81d500c80c5007a81010340c0810248041450184a0103820808180014440c00d400703c5000e8020485802e02c01e00c5001102c0c080c109004407601104d040d820004410741c3d0303450142602e10302c01d401500c0d041d4006400321001290131406841074101e120102d03110102441d42880c20003449504e01100700040110500380002e01d54441e015018500d0800d000c0e003802c440d001d61703081084503d2041c0000e09075100c20010000700ba08071084000351071581e500709520782e64415000e501c442c01c0000682e00117100b9481d8421401c0b40f41d01c481c81d146120b07005d8811452500d01c81800f511244200340340b1680100b40410340904103140c10b0340f19003c040c00042100402e5090180e15040c020b80c0940740b408026042c9405498801d4a00c0c028009900713142001d4144809050f0840c0410210181410b40d80c00b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 883829199 1250 883827949 883827953
    0x41503120e030309030a0b010614030f010302040209060d09081b03160204020a02071503022a0d0318020d0b01140907050405040506010c05030a1713020d0206030a0b03121801050a0e0d 80
    0x841104c9448201030100c5039200b045103041580e0700e00900c100c5002500d40243c90013501101801c890240402c44d0400c1c034980d081d6020080294032031002150b01280030021a03003204910300076002170320302a101068503405a1515420102c01e0405c84124640042080b001c0311034030b07492550140382d0141c0f801a20783c141010280d10301640ca4001c0c0310000000380c101050580c0c180c0003050002d0880302200130f82e1640e041401da60060003c0586642d400000d080813030300307101c1da220144000300c0d4a030113418480180c003c0b840303445085005450042e0a0001070242e954401d0000d24901419161083d031803909010040080c0120f0140600c11a210408599968403d1884210803500601030745d41c0d408980c0c00103810b03004a0b04034171000d03858084c0001d110802010f40c00003815005880c0415004540c2c1c02c2088652000340600c2c43c044d9110843d04482e10108103c04940100c0030020365144c007005000301030010b04c1002c4504000c401c0060035001c680c02020301170040400d441115038141c481c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 883830449 1250 883829199 883829203
    0x1030f0512070f030224041203240e0112020108040b070c120309110102190303020c010e07120614160c111c020f15160302070b0406080105041503120e03 67
    0x401071210214030109020043c06000c80200c5040c1d84241c00700e0b496241003100b00c2e0308800500011a0f42002054000303404541e081480c0b0002080700d1800140e00e030000c61600200003904919201e001c7c40c940014020304d0824170344540507244601d03040d400e88017036071f00080130002c1c0104000d1420744240027190000d4040e0b4804103801d070340890b0342c40c8415140d0000a00814582d1000c2c1d51001d000e1040c06440e5001003013401084502c201d030601598403c2d201076010f98400c0851a107503650b52146151030f40020300c008000b03002c00d031107200c40c06691810204c003610b1820051031065030114003071058111440d90031740003007100d5040c1003007900440e0818002300e410200141d508114461304040c1800ca5107003038040d0b558800c407420b190030701182c0140019404242000360300281c0030404002c4650303824400561a07031180c1304592104e0b884003041d08503500154003000c04200d1500041c0624038086c091199100c02002e1328500551464a41445009400314030030184020612001226102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 883831699 1250 883830449 883830463
    0x1d060f0f010b0c19030305091903020c0d020117090105040507090e190f06050103050f1005090604020415080a0c050906040e1c0e120f122d1c1a061201030f05 69
    0x44c10320916415070390705001d009400c0884031031009014807445151740303070940c4055802207034043e13004043d031600d03110601c00b010f959050140e0500586a040005019640e04854401c40050740089106e0410345805031038211190000c510389824500001c40703e0703000194191440110054030951641581842680034010103006003480c0d0800c1c001201744200000c6988010543e10100d600f03000404000c0401c4840c10350f42c842240d00402c1c0442c000d071900340c00046403240c6c030021208581360303a40700044c6044500d810868488441030001c2125191a40034954000c0e82070f5802e204040e03c0070f8040c2d07101d6103490200481d003011a5181d8901500c6030340121865080503115243c0c0420a040641e0345041a1041c0b01c4544902030981c54942d4814064a01e80d107518480949064140c0164003c000d1040e801d107980d083c4140001800c43c144000145c002246400c1e000551100c203003814181c0c3c80c144001240603400400180000c00c0842412604407a0402030042c491003041c07520509002c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 883832949 1250 883831699 883831723
    0x60f12060504091a1006090314030405090f04050c0108061305090c06071a01060306120303051e07110607080c040e040807082b060302010c12030608011d060f0f010b0c 73
    0x201d401000c3e0100602c00300290a4002d503000103075042d68500e044019846054010b0f50009810f02000b0000110080d0200d40200d1110046d04d007025180c0d004607131403040445100322000e4088c01130005120041c003449021000030303c0d22104600e80b5002180340c03a100103895800b0b06540304001000420140700041030014020280356030344180e801c10003e19040131a60f81c18050200c000080c0c80c82c00391180340c089950020002c540c0d042d290301c0c103800800004098201424881c0608069014400050341c803030209500d4a02c03080d07559103c0c240c5804401000c550900238004107000300340f031810342500e049800d00c409032035580e83c652070b182c1c0341401542001051000081060034119005555001d201180ca00182c601100d0030702000c015190a448045d000c50030359003203103001c1055101d5440e2041030764200494041e50b200a205e0854000d070070703140001e1200380007000354160f080c0301e090f400245a80301401c0c242031205d000210070006100d6843d400f4400204007020940a00240c40c0b152 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 883834199 1250 883832949 883832951
    0x2010e040e1f060503070302030715091a07200a090b010203090603010f06020d030c08070c020418080408100204080c1002070e0109020d18170c0a050a05010b03060f01060f12060504 79
    0x100c84966140ba500b1070109000d0502800c11402141e94200020010100ca40040061045e54078169440403940b150000c441d007002302244003c03800b4111507402201c1d042e60125115500c4846050200b1030107110707078204500c054500014100c0d5a40c1005040580c0d40700c0800003405040303080103034910703c02c0072100794110311301000025884103465071141c1100d074181c080d20b9a20050000440c21030b6840c505042c0484c10840101e801c641c40350717640211291002d800065000d41c042000d0074442041a811101c048002909106a103018000c0c030944a510070030030340c140b6041c1641c240c0c4940b00d41300b110307000c1c030858085203160a10130480c2c5002070402e528110746658440030170401039480380b18031090150500d010407104007079180000ea0f255030041da49940b0340c90309120b0b040f4290300078240c0140302e1140b05408400b20310184507040c03582e03110b000002210008a4203050078003200030704040c00b24451100411402e5040034905140c05402d16107817510a2540800d0002818180c04c426000f03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 883835449 1250 883834199 883834213
    0x4050405010203010602010c0807020a0b28050402100507020a0b090414090606190602061b09031f0f090215030604060e010815091c0513081911030c090402010e040e 72
    0x2000c0d040d0700440c1620255402840488005101590f5414069805000503400b26001c003022070407400f58079422040440b00321581c400340c041003021549000c108140250354540501003145428010a40a5411070400f20f0a1a500390001019802e452141440110000a51503001d035980da000c80c00c13440c0d852800c0320755400e0031118960755400403181d860240c400c1c00c0e016103c087c03e291001c0300315165603001700160343d0782c000366507c0c05180d030074510300c003000034032041d4541d59061004d01d15101c0320300100c000014640680005031408050413100712490002c01c4400741e25500c0d41c540990454820b5a6502c1e20340d04049001004290f001070002005c0d0400420a60000f04030884161580340c01101d02d0717261802c010340c850034140e066540055801020307408039801000503068003444060b40c50800f0760340d000c0076820f1450003c52a4902031116803410100144800c400c694400160b00510f201d14054001c10314140021348083d05000c10070f00012000e81c3c641d00a5092040c000e81a1115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 883836699 1250 883835449 883835453
    0x20303250212030a1113090f180609020f030d0513091505010f110607120b0109050a0519030c0807080706171b0d09120906031509020714010203010303020a0204180209011a09040504 79
    0x13100e006c0d8007070350710325a003050808000301c0c145d402058030040c00e40d80e135070f840300c15a640c03054010a18032208030303046034004510b15441d9900b446910540005c54039803560310400c2818085104045400c0910a1450640600c0c880540700c05058141c50703007828021a65044d00c1d00944001e4801c00b011402c3e84540410450910742c4000d1a044000e050407042c021402101c00568800c0c036680103081d0010440c1c1001c07c024501001c005001034044403c00660f00d13129180c0c5403180c0d0039600242c030346600035402040318500411147c00205058500f5404031071001c0003480c0c400501a02052642c005030b5042c207194541f83c0704a0380612070140f03040007008541c0ca0450568a864a00700000c01d101900000301c8902034003400030113020400700151700c581440a0600250080d88098400072000080c040c207001e000d100450281d070094000303016403200c3d1b10421086d1281022944000c0543c0705071040183c4940382418103441d10355040f0f0b96008581440c2900d580201280310783d01900340400d2000b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 883837949 1250 883836699 883836727
    0x15041e0b130f0b07050a02040c030e030d090c0e04080f071a19150602031b01021902070f15020307030e03030c0d030603060c0c0819030b090106020303250212030a11 72
    0x812a464107082a41041e07039103d008941d80201d40c40580705070007441c0c000c001031800394449000a16241000103942121591980ca590401700074070314000e0750f4030380c94000d0000c00c1c0030780d00017450509424080d501e050764800507240a01035501e8051200440c41e2410010000d000801d8803040ca0384034030710313850a00703801c3d1040c8030107c0004a276540b0709606440511001205202a903196070001c5180c0403a100304500c411080c03103140354895600b4442914030f40b07906019800300c1d6155600420f030190400d103e9010408880d03002d04d620300360f80c50310310700610b8010082e10130584d050300b8041c0e103140100001c24194805c0c14008440d50040045118520380c00da030100d4141c13801640104014070110100346d4074240b02020183c007414051100c0802006148030840241d541071034045044000000458040c500030b82288000d60008400c0184103407441440f6809060302c61a1044003c840784c0d0041c0d1540041d40408504510000001d0301e0070740e05810442d9096101083c26942d1100c04040b20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 883839199 1250 883837949 883837987
    0x80d0c20060c0102091306060c0809060405041103010611010207120c0c080f0a0519030c021c05030301090e190809040e0309100504050108152b170a0e15041e0b 70
    0xe201304101c1b00c0d0741046004a10900050f50b41c0d170f480c1c406203504c940e212094186c100301800caa004c1e03420080414185c035640580c040365010b88042545075414003c0203002ca281c842040201a84140311040108510709a0f2000344040c1342030150030403045040240181c5e074644c0041e0050310401c43c1d507040d41500050500100707030281040e07984c4007500c900420341442c10301c10040c0c0020800030100c1d0140c58220700400d04810381d841d206020340341582c0d94a00b140c109a002c4801c141e9210301044084d6018000c100010240d4415221081450741c0c5256542c0920280280900d50703d44001407120420000c541d100032005014800120004400034041d41c02801014000307030045003c071310541c1c04801748070a0094020b14941e41800695290b000c042c00f9810071500d42c00c0d545403248041103c0c005a5404050014401955150500c030050507441c50f00d04054064035107058000800c606040035241910003004194180c84181500c1c800600000e40040450150006410244611400e441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 883840449 1250 883839199 883839217
    0x20f0907080610110d080916030b06011e080f06040b03070312110f0601213504030302062d010b030108010b0a0b0715061703070c080d0c20060c0102 65
    0x90503480f404401101e203440c540c22241c0740e035404851007880b1329015000086d84105400304448851031602c4419031241c03d82d07072056480d0000e80050092070b5901c140940d080d05207840c0c50500840458200a1009000400c41c403005507500001c100070340c1c2e980d08044d02510004085800e40c98581c1440034032042c0c01130f40d14002c03600c0020451083da0002c0b030400381b12050100030341420380c1f818618148241c40811850801514031a1100c00103044051111140030031602c2501183d0041c20354840c201c03050203268011342d2040c0400c0002070f600040d950f90029030001032a800321608541034240480c040c0c080600d840380700002054200366039028504031481d0b24001e10907030624209110103000315015140c409a030410041000c1804c519440306482c131403d4000903c16a40e07011f11031700c00c0704040c2c0c440e00764100103401c8003800703030080600028117070000150800c01c41c1510003400024520600510107001c0215002107081c00d900c00c41050403001d00100c0d55108140310940c001c0d4009820 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 883841699 1250 883840449 883840459
    0xd050f07090501141e0a08040501060e1302240703122702120f0607020d02010e01060f0e0c09090f01090c1418060405060d05160813020d020f09070806 66
    0x90103032842440014200c5006031100d001241050040f03411030ba100102c111398110840c030400742d8480f50400140a200c01c0c0d99100411401c0914200d82555066440740e000c01d044d00090003081d0a5103001e101903541c0c119207400c6002250400f55000e081341da01c0000410300d021480c4414150000952090104103810400c030308001007a040d041c000307003a280034080058100101e00141003d000005c207a8030040f040359115403551200301e10f008400c0720810300681141e482810126024010f20b1140e0f00c5003c003c2c17090905024818541d15014402c80e104500c894000c1894010310004a40b64028040e18007400c91034005842caa1000f0217104000215103490f00e4041032a2169104200340045a400c0e5440c01c074034984000c8405c070440082a50040c0c1c00c110000301a5240801001051590040483c080c40c2130003c5520186040010703805000e202d6040010644060b801c5000e242e0b81215481e0340c07108680003141e502a4410310325500400c4100c24010a075400c84005032042e40c080315 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 883842949 1250 883841699 883841701
    0xf090f0f2603040b03060102011814070603020f0904110403050102030f060a141806040b0604080a0501060b031302090a14150a08010b06030105040e16030b0f07030905030d090c0b0d050f 81
    0x4441012014048641c41580c00c14802807000041e12002941c01200510001c620141810300c01000c615070001c0484d1021090b56015891800c240800c40080030b06090460a0070284030980880c0d00c15651220b202d10360b07a01015400d0303007c00c000c0c1c1c5c0165030002c5c002c64417450220540c980200d001e0710020f20034106801c00256104200c0c0c02581e0018000d01000d450340e5841180182c00351010340002e50164441902c03180c02c0d20381c603000c0d0006040c0e000084c1940300341802c1c41c50859510750031291070007008008005078840e18441025000b5419100394003030b0758800281200501150b00382001c00010f030010700c1540c8422540011450341c0c21100408550b41d83d104003030072540d40600c10340c2c101d07105000420107454140d200c09000e134045815600c2c540550400104078024a0308101d503001075890034031400d1f00b6981b8600c0d80c804000d04041104028a4031031964034007543d000000d4642d01c6142d45000c10408240c54002020006c02c111340b44c4004924190190100711124481c40042038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 883844199 1250 883842949 883842989
    0x1150e060109270f0b03010c02010b1e0a120318260607090b07110433240e0a0609060201050606070b040f11101106070f0e010f090f0f 59
    0x302c0f02c210a50000020f5000300c1c000c16425000c0c1100790b000003009030703917085042d0301078a0038041d4a42000c00d0354000031b0340280d4003080019030170b000758410200c841c0b881c084600ca40c90b850341000c15130f0b401502c2300ca01c0c21900d00c0d044402880c032001041c61542101c00005884800c0f141c2d49003c00350054040011103d90895255a6031040341c90400042480701c0c100310130414400100704181c021901081901d12200204e82900c0d10140c1d034189020201351880991400364030300750503180ea044a02d007800e51404050443c0108001c0e0340740082c002540010f02064081e00f501d80210307901800d0509060759512004d8030b411098410384026500f001c0004020f407400c40200c545081c0c0c0b1200912450700c0d182c03a5026a1a010802160003c200c060a00f40701c2c0e8508580214207034650f500c081c020600c801c681414410090721b84028420a158001000d940040c1851440340003840c007030310303100c1904400300c90740e0341c1541c00403c285030054400326081400d6001d00003550502050801a10500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 883845449 1250 883844199 883844219
    0x130807060903092c1501020f1506130c053007091a07021e0d0b04050703030f1d121501030510150812030717090114130201021207020301150e060109 65
    0x19102007055050341c000003804172602d55a4440a100c0610480b103101d604031001914240038800390080c05000719040000c2e524040ea984c06100ea22070a050141c0c500b0200301400ea4020131504445407a038080c0010b0310458190203420b0241d148000068040c00c00c8038000e4580c040c00c1c007030320f000301c48130007120206035400380d04540030603138042d201c02c684050702644c0c00400ca0625130380b140d0060560349010041001e41202d01d00070b80c0180060561603145140c06044001040f10860510a1241d4030310768403140d28071917050f906003d0360f0000114004059090a0100c140c10703605070035210000200510200044105c0180240d6208000035000000264060031051081311955030045854103211602c600295800902c50f08228016940b00c011078486450708441d6984603039518000c0804068603417400700d170008030385018440781078610b0300001d403201008000c0030306d0168001242011914250f00040c41100b001c2c2404609503112803e80f030468209603102c0b4005803541001240d04400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 883846699 1250 883845449 883845509
    0xb18041412030105040e070b0f040e01060c0f1b0812180a05060a030b040f0c1809020c03070807050a0b13111e10180609180e0613080706090309 63
    0x1805501c0e5045030f00c0c0004000103403144400c030181e1401502d40c00508444001702030400720301d03815042c5031240d051486000301030300160701000800a13464a48004541081e0302107039107a400052036101048422036581d400c4100358800c0244e40702c0d180ba18650b50811030094070a00303005001c174010784001041009a081c005004940d07100c1c00c204903a401d0035009030310140440f54050000709035181d116441c83c0495099001c0d02000c03a84241d01c8901d900c200369068409420b008a00b1410901524102c03a660700610000401c44c0000043c2d00040c400b040100e400c800b9400402c000051900441c00070440203a03079130407500da1004a1100e2440d190092001e0540400c0c911040c3c032004c83c46040000c540a81400e072000d00c4010480d4050084900300001d000d0441600e48071031b580d1514010b91060030307207202d0020343c5c0b82c5000c1d4044504400401c1640c0c002144042c1a00c040e9041d051030031082c4140c88005104c50300c0e050001c0201508074010b02c086984201101d03500c52080b81109140e0b0312 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 883847949 1250 883846699 883846723
    0x9052805540907240206060a030302070603020a0203040506030c0c0601080a02030a060c0e040504200414130c12050607080a021602011b060e06150102030414010e040b180414 76
    0x1554400340903540700c061a0041d03000e0406822640c5071030303481c000351624400780700307252000e030904101c0c0444107a0100131090b0001c00c00d5403d611410b2440c1c900940325192130081004254001408402035442001500c0142ca0002c043c50b60342d050240a2144552101d0f00d004040d02411000250a1401040119507150044c01902d1080c0b1141e8130200140301c000000820312017504103000303094651b0720406108510610004034200307480030600c4140c0141c460b0062050741080c40d200340c5002c07403803020f03074000030101c19440384000e191900c0440d45c0300d40d0308002c3c00240000c40000071711100003000340c05003100303484064064440782080390580c4514500c100c40703c5000c8142c18015403090307039800c803880203c9010310700c1070006503102c0083d44c4103140e008145500c82002d210b0b00032100700a44103011401d00055280a1400094002c03400c00c00d04000d0501800301c0111005469903040070a00420040c1100821881e020150040e40d009840c1903800300e0b408100785049843c000340d01032040c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 883849199 1250 883847949 883848079
    0xf02250809040f061707060822110604030524010b0405030a020d02010e040e010618141614071203050f0903120a180f030f09052805 58
    0x20690720300b8407003d000801ea110030300c559030301c00001d10b1514180f00c00091014840203030000901e004402081c110307000c0c14200c0b0085107803895041e001031413500051030383e41c0070340500c24032407888001401502840e070014142d800f41d46600c44006c0e07040c0007418a410303a06032280c0d805980707500151900740950302072640c040c1c1c4007031510809480c040c20300c2c0c038440340305142517050300441c50042000d407401c41c0b001c1041a0f442e508203000300d041390b11030841140940c81d0200405101d90300641c0601c5405000b148054000304001184180719552135400c114402c81c0883c0e5070f00e118584407030172440b62011880040d240ca4081341c000c048600b459409803010300000c500b1b06001c2643d40c1c210060180500c0c6945503200c00c1d034200c60b5071010300594064055684085190201e0401030030b140494480304040100320102131110760740d0140c1070035030b980a21038010180307900e1080c0c401c40302520f504080da10840b503001c61021410440400c10944121300f0710a020703618004089002003a404014003980 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 883850449 1250 883849199 883849207
    0x50606070201051c0e0a030909091109090f07060e0f15030718030b0106020102031e0f0403050a030213090b12060417091801080102071101020a0b06061b010f022508 72
    0xd507100b000901121814106030004e80d54800b40c008080301c40710002c501c1c0c1c0d81c100c0102c0344203160700510a03e00411408030140140071403590b6200c1d010400d0001540b1603c041404607184030420841060b0040d00c1e00700711910742e03460740c8014028004802c440d602c1205e10518099281c10004220102127a0810740c42c1c0c02c58032004002c0d504d00380200007032880001171000000200383d120303d001e402042c10b6000182d032030420703030522903018221381019400d0a252400340034074030000d104c61541c4903415141290f1a4489600c00b1800f901c02c10402036140a00c440c400b09600c2555440300c5540b240c2294440c0c07030100f16281c0d4a8482008603006042150b801852040c0302c5c600030001d1907610001007020151000225003200380c00707000c0e0001d840b030b607601241142c100100f84402d1020820240020503461030150b4034a4115003000f002140961000f1651805681d81c65168509030101e45000b0320030100d030110107000a420081000401240c0207904a44100c10140740d10015a0486116454 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 883851699 1250 883850449 883850453
    0x304030915230c030702030a0606030c1a0304061d0607090e06010f050d0203062403041e150f0b040e0a0203160605030a0c02071809020306092802030f0f15070305060607 74
    0x2c590040100301542c0d00040168500595041c807001d94024814000000c0c4541503052900b220b14a5400100156501081c4241100302480c00c0c0d0381d106900610200315010082e842804165111261680714031400043c01131403a08038030400155809a01c0000b1190344550045036125040e0b180880030039020092a415259240c00a5500100c042c122202040000403640640c50340c4031aa80c09030070001c41800104000302a030440c458030348142c01844c00d80241c0f90b414964072040301c6451810340d11400071541c41745d950091200b05e80020010410b0b10b0020301d42d192180075100c8200e11034065005403d0020000e02d9084040e94101d940701d500790340d00c00c0700c80310041005005000030f6114111002514641d140c1c80e1250f15456100c01180401e450b01c1031515081c03010f0702003041604914414010007042c118402c100c0d40768458202c0e054141170010a0408080142070603060281035a0800003070000500340a16480400c603288981e910300008808503002a034515511407010081100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 883852949 1250 883851699 883851767
    0x13050411090a03120e0d02010806010c030e12030703030b0406060e0d06060803032517190609020c0a0b0f061311160507080c03150a0507090b0304030915 67
    0x8603403160005410724040c50103000400c0e9903055401100d103240c10281d084000b640c0072001c1e044110041d150509403042d5a40060407004008101604000543c10202c06040c82903c540429110142070380f82668140a0001d441c1d80c4501c41c280d000c241091030380e9585090512802084034065030300e001840c2e45000070007610a82c010b501303542c66900c9034004a1501401d100960040312540071402900202440700c12888400d240c07898188800788104107022081d4110095001003c5246011081c02c505540c2005000d1034001c001500d00c007145602e90501c0000c4d04483d25405002406095075030081d200c2c00022007140c006401000007440300b500000580c11030f001c2560030080903800c0c44802400c11400700310f12001a20603034001c00040020803420b0001044002090b000b8001c180134050312f10003440d0010b070400c052140e480e000a441e95206142d0000504a030031001c2d65203040c241001400300806015085122101c0502d21502e64043c110b890134640f0048032400c601809150084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 883854199 1250 883852949 883852961
    0x9111201030b070c050706090509090303151201150e04020f0613090f020415080f07030c1e020703080a050403020307051008060904051905010615032a0207030b090d020c06130504 78
    0x10f0510020302d01140c0014011311950f0054002561410b00c000d02d0201080300c01d04c8090070b1000f0b41d03001081400310b2141d0080300c1d50220764040e1449205402c1840c1814010000034100321040c10840c840030442055090119000d03038000c99541205140140401ca110b00c5a0455104e4081c0b04490401205215030000c1c04802002c20703005060950300e20070b91000c5041248810b00048000b003c2002c80301242c801b181d0420a580740402c14042281001340c85400c083c480c400c907082c1017043d86401c2d50702c20001030010316440064541c984069031030240c11600b00d07010480c468000e00001043c981003010340079000d0b10466884681507180c00051110400b80a04142d400340517540200030a514019500d88405200301300008000d8601f100302c000201001c0c08100801d4100044030b181590329010310700030700c920b2090801c05041d010009a10b4030b0600d0344000c2c002c0d0b0b041400c1040908010446102c44c6525409803214805c0d54020040036100700e195807820031a1407a410f03c1a81000c4c3c0c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 883855449 1250 883854199 883854211
    0x120b060c2104051201020702040e010b0a030305030402061908190b13020c0a02060f1308010b062b050705180307050135130201020f060f1801200409111201030b 70
    0x1c1d282a84030000300b81c0d08143d8500c2d004840e9000034100c070071401c262040c0103a40c04080c1c000c012800301c0e40c001070341c4210170340f10141c00c002c00800491300750342d100012a400500d0b488511810607180c9600601149801ca440381c290100081001c1840c2900c1d0058011007035004103400800c000020104c0003d40040c2c0c81100e56100e44e04102c401030f00c8010080400d4421108542d46840b0700c524080300d4040749411081e40c50341010516846a1555000d80300740700c0ca090030400940c00001c44501c410000d151141c08200d082c90300340135000c3e420000800c10701c001c004251000300c10780410b01d0341d904442e20600c0c0c001108401080804100c072100c00008881e142c82c44080d01e071810307090580b00e03481955604c2410303015a0710102150f804009d0345003a0001d0002421b010302c0d0900c007081004c4002461202d80d1036010070920038500c029481404c0360b0181d255450b65840641c82e480406402c240101d00d03031035181c0780c480046461103000341d030612a0b042d61042e030613a0866a443e0540071024101c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 883856699 1250 883855449 883855513
    0x7050d110a06020303100b090d0f020d060c050a031a090109230c0409060515030c070330050105190b0a09030b13060621032d120b060c 59
    0x38400d165074444072000700501d00d0b94015600d90900301038104400701d099001c03903100082048914400d4403001015010f20341c0005070440c40d0310721800802c00901401c7c40040116291582d070310392494002c0301800c0150000d6030304025141c0c5079250040a003000034415a405903140340100305680d8603411261100c5003481ca0f02051094241c3d0004000c00300703132031031324500784045001d100a00c610310a40000382800ca0302c0301100300c180344e07001c4001d00c005018442c160b00000b03845401d15004014011104102d018000c3d245642e40d0003d40d02d012401c1c00d03001e03801d0b0928000090764540343c65101038824655020000c02c81c50840000350561080702813074180580c41c02d0010116501001c001c1c89164041c0c14a0301e106100c0c9400b42c102d9040f50880308002e40340401990036990011700080070154541001e224240b00404079294404c4070b0940c440b0840e919440c201055a40f010200480c2006e0360400d0040c18100010000540a00342c000d21f11075008444140104003035000e07902d645128241 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 883857949 1250 883856699 883856723
    0x70f0210180b0403060b090f0103030305101a0a02010b10021e010612140c010309030503040209060a090507020f1b03030a1d360f0a0902010e040f0606020d1107050d 72
    0x440101c1001d540d110500e030b0700d40454100240040c6008503d009a0200c40c03244107498952201c141003081800040d0405540e0b8001070303c8404802c140c0c0c0080c101c104907011065601040b00c0c01940c2c80305084c58015401d01030001c0da82d040c120031111155080c1e8010302100c07581c0c68600340e0b0040c84002c6842142d903c2d00c1000407000300c012446000b1034007407851141d81421156603c1e1800c000f028010341014905528036020136072010560741c2003541101e0180356515404001000244203400100c3d025182c401800350140d0001800c0c14201403810a641c95640c0c8084848401c10f040304506c0d4054204020404141e442034081c003034080a405810006000000042070412400c0e003920503c110301280b0502c1402d41807551494446003003070702c2140d64a80b001d4a240d81c80c00292144c2086034071150400110ba000c0e8041d43c40103040a0300401030341030480004c10150981c2d00c204409400f076031600c0742c1c2e020320801981c1881100c040007071a03040e2811003400300e10214900251420100c941c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 883859199 1250 883857949 883857977
    0xb09100918140a0201022803053a0f0605060f03040c1701050708010909032709050c031006020d270803070507052815050f0409020d0b06070f0210 64
    0x20100b0089024100010048010203200191400c42d010200c0780140c10010300c0301c913021958000c180c1301e0507810300d805510b607044642c07107031034080346160f180b01442c0744000100110009410140603800000c0001e0184144450342a4100c5650740031f15508005c08010901c406c1050200a40c2c000c1d12803d0104845603407039090204c50341082144200d0b594558050117101903011781980d02600c0ca4000800c400c48055a01821001da0f030064605440c0818507110031007804020841c0c028903141806015a1603e00103645c42c03a8022a80310012084c15940419068800a0038107180c2d03815890305502e0314012103c8505030410b102d80b0756919001041e002c42d40c1a401d0015103030091040b0001c01350300f400d0808000c0c40c520341907001c0d0340912044c40507000d81e00c1c2d6520540c08486230200f11140c61396403241c04440034828054500060000041d00281e4500700354000c00007a0b0101c48108113400e8101c04002e480d100c0c2e080c018101c403840b941d2410144c0341000c5130404088841c04c0400341c01c4052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 883860449 1250 883859199 883859213
    0x504050607170c011b03181401061211030f0601030b0a020f040b0d0f110c070902030a09050304030f03030506090610050c33090609210f1303060b09100918 68
    0x20020340c80c8594503600d082450441d159140500700005d81001e114441e07954402901d03c3c4010b0601410f00da0450000c000101d00a601c11380c0586000c0d05040003200482c2050024050b110035070901a2107034080d10745d00100f0100d00c16040c0c0394406103240c1c0340c2c4c84030000303103001c0d4009400c10310030820100000281062580e0090515a2039114003091401c04446000100c40020f480c0600c04441007005002d22000868041c0035210414001038030794032180200d070003e00843c08028100d1000103000f00901c8400060340c603031684030346d80c180800d80d00c100030f00208000c150703403d40d0010841d80e20030b03034240c2c055409020000010030858505045022005082c610f0314031102c075403580c1c98462117500b485800040f60f0300c56003a0006203030703c0c20018000b603510700300502e48100ca0380b1100510300315402c4d06011152a00503294140d922010244000c107460700907480304403174592070007040d01001c1c1008404a03104100b170340c2070300300718a28001580d0701400601140104014458481310001060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 883861699 1250 883860449 883860457
    0x5010f0c031d01050609070f02070f0306050f0702030c0a0206090f04090818030c030d0e0d060921020d0c030e010309050a05060106271a0c0102030f060f010e01050405060717 76
    0x4603a80100b45032102d0584103260951885110885905120401c1000c2d116410030540100c81ca20780240407004080049040001e290172110140300f078000000309104e820b80040307014400081c4004066102c01d8002c2c1d0340c074440c1440601003a0898000c02001d883c080002d44039403040031308150303d0b0309103e10010341100c101550488800c41c0c0411404002c1c00e01f80c2000e40407840c00c1d4018070300720812100195072607544018600030000c2c0715034a40c2d8592504202079800c140e02c200c0a01c200903441ca000c0c10750105001c100d4050026142170440c1a42c40001c041030b140c001602c500f50f1503121900c04807201d0401008180c10316480d06c0075640000c804001003645980504082c085950402c0001021191485c141d4494100c544d03802105401c00403866408a940355640d140600705180d52840c2c10f4010450340c0e5a0951010042040043e9900380a0744038020486462a803000d060700103458403540b0191880c0040c009010a010343d0901c44001c0241902075090104401860064841a644 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 883862949 1250 883861699 883861721
    0x50703050c060a14011208030a09060b1005090418020603070f051b010902091506032a0403051c021b0103091703070513055b020f0c03071205010f 64
    0x1607102505a134a40070440381601400d24907841d540101e078992991555404090200d012081c3c0e03800000080040c0d41d803014209040243c4913030b003c42c42254000e4182e40280f46514002c904007a80030700441c030050000e9242c0b6600803e024255112584c049482422000c180401e002c000c0100d200c18211420540d43d9928961001040b154803d106000940c2009080034400c0740440118414503035841007540d41c0030303002e00c0d00c443c040c40d04100440c50380e1135051001500c005000401009000340030030003201c0c4042d003031074852410464000c220303a544660760f045c04241540303540040301c2d984039801988002d401644e00b03000b03a00c04500403100e00e605c1078800c40042000001d11000c5541c62008000081204481c1001d5000c1c0604440e0342022804510b1035020a4440143c4c004071000001c0d400588542d4452202c002d42c0d0b000000c2c1b145e60070155100c0548140b800c2c2040031000000e19249401d000360250206034944041d80d00c1102e81a60b040340d280d5202d0391100b04084403880b961141003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 883864199 1250 883862949 883862951
    0xa030c110f0a06140108151b0f040e07080402010801140d0503190f03090c0311060d1109031b030c270718240810030602030a090309060915050703050c060a 68
    0x40680350200441302c01030018002030401c2001009243c0300800c054050329a8003001c03102a40d503500c103101e080905c009100d941040080b6490000c20f1030b54000c1e00c29101840c80d203d10645426805032110003007101c1c0240020768580050140f40008019401c40d1600602040da011a46075100c40c210341011240304032142d2244040c0c0d035000da1140e5031050300109414104000c14040c2c036080b4515000e40009800304054480c409099200c41c011034001c46440c0208002002a5020540c2c01ea40880d0388540b003031090b62220b95007400056911f05e14084006d00625034042080144800040c41d4480030040d28441c28204101c0e0f10020340003445085166500062001c1c0ca0b002940b01e0b0407250410329880030004890617610b0b00008810403280a1810700f9242562103c64050403410030f81c10003400c0301c2c004001c1c0030045280d03820100c5498425226155100d84805c0c04a8100a41c0d06c18681c3c03ca50b0310342500141402007004042d010b001e490150701c1c000d03131034810601d004821b40b42020a1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 883865449 1250 883864199 883864213
    0x1f1b0b04020406241d2d0f0a1404020906040303020606181909020f0d030305041a10060503090312070e10030b0f060d0e012d0506060a030c110f 63
    0x5190920800307015050000d58002041090840e03224449610820f076000d20180020061045d05680084154200002c1000070413280c0d88522101c058510840784117095400143c800b0a4035007080ca140e030440703003d48403070009458001001401c0d00250340e03954004c0d5080110160985607800140090341c0681c009003d030b4141001880840c140406038840c1000e003a4050110420b18400029007045100700045805d44c2c65000151685107003400030340e070001c8103c01c030608040e0140c00c268400c0340903086102100088045554010100b2551030910002c81c1e4003d000390341c0200040c50b000032080044a0a1101105100400d5041a120200460843c8420506510700030512000c005140d01d400c1c00104a5440032a11502d91007012500c501c4020600da082c130a04c035801700188442030f8000380208114030024910444c2c1852990142d10404070104082e012140203143c003901d0301030140703071402812180440081008094410030000c1c003800b400e070015010041899041c040780090002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 883866699 1250 883865449 883865453
    0x207020a21030909090309030f02031236090609040f05011841030c070b071209050d08030a1e05070e011d09090f07090f0e0109021f1b0b04 61
    0x294460791144800c1303401d00c030003440000d42c800b00200861351710810203041c549552000904050900300b18550305440031031640c032054180324805400c003000801c0c110b400410021300f03e2100b0600015642c100d40c44802042c0142480d00c5d000340d00c18011840f49410840d04d546150a43e0315688001d8007182c4c0c10003080e403d010f00d151400003800d8240d106d0b9180310310710149000340e48203554440b40c1034031042111003005031801c1c400c82d103021124005035803441d82c5aa001400ea81c011030b409071016a01c43c60700450380c5000340d00c0401655002404c1d40e043c7c0c40d0b02d40c1c540c1001d0348010301c0030381078540382c100d441c1c40c60301034a594883d814541c540100c0d05240140b0300034903500c0c4040300181084400080e070740100800d40491003207200c1c243c4005000317907582d1018a00c0d01c00d103120450113510482c4000143c580301035002d011940020b0310f0502a003404401202d003a100102c1000e540303d50050b4240f1000071005070015800310250511846115280c1400412590741c8042514a11000810042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 883867949 1250 883866699 883866707
    0x606080613050f0a0c1b0c0f120c090209120a030807080907030327080d020309040f02310503010906020c0d030501180207110d1b08031c0207020a2103 66
    0x209600444008025030301d0844110b000040740a0461310103070755144900d12138a0b00c030303202d440c1d00013841080e40841c03010a4070300f0306402d0762944659842d407020610b0204108039a0010020110380081200100390700f0246284029441803018580c0305034070495210300510203000c0810b0f241d00a0716400c0062400b000c001e48200001001080c154100e0340003800000e400554901400c4601698040d10b0114030310039007100c08442c0c00074043d9102d140842101983d0000050001d014165001c2c0002c09034145018140d0191060200861114100c0c600754040e04841140305174460428080d06240d442011030b0850320041d400381c0b840303031700003404000b08001000f0f00c1d03503618042c0c9010045585014942920454020604805260001005000d101d40e00d2800f0b42e04401c000c00e10003408a00340340030b079200c001d440b10080c500320030250009800013000c07081c0c074440c8244565406801141c40c0c450350007175020300b004030392040c0e03410004a140442e4000d080e1501c00d40855900c003480301d03401c000e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 883869199 1250 883867949 883867969
    0x102070f09020903100c05040e0a18150e03070b07050703021c030f0e0601050105040302060d09050d0c1b060801091512050304030b161205040203100c091e03080f030606040906060806 80
    0x12510074102080031071032682c030004413230885840c003a01842580f02c1546400150240350010411a5581a0000f05000c0c080c1501c3c105103c000358100301c868151840c40ea140d0040740c00c0034200c02d0312500041c5003135010758000c1207113610030b01c103031481c281c6040d4030102812301c5400e40c1070010344e070b6040d00c12030602a0710034012182c00300030017440070358540030009006100c0c0d070000070300507a404101121036540d00d800c0008559448001d440702c654044000912003440a8001e40e1480005062071810f2200030740b522055821542e9030809aa09001c401d50107071400a20000d158410803034001219840c03013800e20b00701881580a541c5e02c81c81c43c1031000d08038001511803449040030070415a0001e401c02c144410b0442c507a20003194594039400028103010107003105030612410204445003e42c0d00020307003400e46101c2c00d0360080748104940e5071600081d00d40002080320b4010060700c140404004040d5a01440c010040780c81c142c1c443c000002905c8071507109c071000c20f40c0b01062003050f00c6c10340000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 883870449 1250 883869199 883869223
    0x507200310052403101b09120b0412020a02040e07030b0f07050a031a06031f08010e060c0310080709020424021c200f0606040212040308060102070f09020903 69
    0x6005600f000c444450300c04500c080c03030786071141c0204015445501d050007450124100700e0b10401000f910580e0026850030300c80d0380080054039950011500e000d8400301c000715142c00488c610b4040c0d54607502d2000801f2185015000d5100f810420401a500c2e4000c1902c00d058010140007030724a5468400e100080180c41920344d004d41c0020000385a41c020159a100340c0c142c80c0115891a1143c54140c5c2060450344c135035000390002007044400844001010405000200500710740c0e0b944410407802c81c2d1018040d078266400001c082980401c1c2880a190003141c5c40404088a40c4d9600f44503142014561040e06000d070007150070040502d186508803e001a5100121290b01c03010724004d4070341d40d41e0312741c068000e40904480c00b265881115020141070000001e8200c090302c052966a0320500190000402c0c818240021400e04040c021b80742090b8046481e00b45c940c40d90b9030141e0b0031281c01440780c7d0440c490f0100021b03401c0d8207448040b001b0300e41e403100103945d4404441458140305442c000d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 883871699 1250 883870449 883870451
    0x204090c020f1213030b0c09010e04050601090303030e1204031a0714070f14070b2206080f04050a0f08031503070501021b0613030303020307090f030b010e070507200310 74
    0xa0502ca02801042411103000d00c42500d0b56a0000902c0d10441c111490f000900b07a420040104071740307180040c3c01060341007404d8a4222509101c0c00c10041038800464944c0e001480490041002a0198100303184840d001c1c000e95500358100840c01426402941c019103806c0364100f403d903029002c4010b0715800c000c1c070380742010030001c0e00c070407407602807061006c000c01c0c01848140ba44288800440007c6074840c42c2025640e030981c0d14200003859800c4200500038074541c5003c01c6034280252140402101c070319454203c0c0075175980c000788020060044c41030b034860260242ca2000247e4000744c0c81305c0544580505500c80c1005d1420704203911034411528040e50020005102c5a80c0019144490f05490203d410075400a400418603500450202c0041c0e84c2c0c040c41d02004168240d005140f0072101a654500c0c12036403105040e4201c803480c4805800c40070303080d0040c0000c0301078a1115500001038241f1328078082e215541e0032401440c420404100d1203c12114941c2d42c070b0140a12288030142400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 883872949 1250 883871699 883871713
    0xa0312090506060f010512101a04150f02030d02070c03062306061b03030a0c17010b0901030f1d0d08060301140109090c0512010212060105070b06190b0a030204090c02 73
    0x30329a03642d540007a210f01d102c0c011032428201141c0c851070440d42100d9031a02c09503000c0c00d01c01c1e4003401031078050065289104c856082d0101410040b400e440c100c549051403120710740c042000a07160441000404811408100100141441117000402c07540344122801c1504a1450030701c202214a07032130000503a4455a20b4125804011049003034008400b161059039806100c15100c1828208049019403800080100070ba03004030760348520a82d003c0c645400113000301134900c89010b8842400388544c412010b0080c1c403800d5110b03504c0001c1e81c0d194204001000720300da5000c154828400d4410b200320342d11140350241030039881200107401001c00c2c2c00900c541c42007102020aa58014001c03040d00d566200e02030824000303041c046500502000e464501c81004044c0040d0207075000103494141c404520303012554039482042282d42840d001084230361030703481d40d90070000008000601615480c0107914045140d110001c000c05c020400da450040e0341381d02c0c150140d02039409210f565810344d04909 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 883874199 1250 883872949 883872953
    0x120c03020c0d031e1a0a05040612060903031d0d030e070f09180212061021062d0603051204080601181503034a01030204170a031209 58
    0x4480784080d0003401d003c20031508101001c132080c945101c0f83d02045050440c2d290040561919264081c42d040d10380845194442c4180401c0d02c10610170000d00001001d115008240c184d80101800be00c00e240c04501e542c00342c4205214034a181c654001140c018500380303c001740e00f40c4181e00720510080080c0070301e076240c429490b0041e41c403407003010015038485110b400e400030a111050340c00c1ba03000303103461250720b10200542c0d603d0000300c4904180d160f101d60003088518544018202e000d900d021103100187c40356803440003600d05800c12260803134000182e0002021000103050782c2141031030b0001807082c69418000d250020b44e100800507101c041100f40281b18006c070b0708905440c1e07040401d01008845410304030090140b0200780000b20032401e8048100743c0d000e903c06504011000030207030b107029074116400107440702420000d400c00741c10325110300c1d85012990b01150420305050041c20565206203d100100c0100036090868008a25010405410010740140154142003c201d100956 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 883875449 1250 883874199 883874203
    0xd0509031b10030e030f0403081c11071e05070b190305010803070b040312050c09090105040c17061c12021204060e1318030807080915010b070f080406120c03020c 71
    0x402050b01050388031881c264102d0010800c60f481030300d50001507a0365964030308142000d80c0011030304a000da485071780722030383e025424050010340ca9600c118003440c1404560300d4240f0710700b0306c041541103082c015a200000c0790051102c1e100a181801c4519540c00849285000141d0740d80030584c207040c513010041c020b152002050304d01e196401841c2103141d8507141016556100e00d003107002c030680d040c14104642c64101c0030141c030282c0003c0d140101542d0300c4030100320a0380d45044c1c0c0800044e20507418a0407a1100d908907640101025004000254219454420440712003202f40c406040c5914513804a0b5810030004d181d4a601020316070800d8204000284201403010f5064403481c80e0021007001060968050702d0130320b265445546100d2424980940075a0f01150200c01007030080000a607260307008106010350410981c0b0f100400da0074202c03030f43e200e908005002d80d00781d040150410700003180300c00104081c081c80d4541147c80c0300d60b503541c0c000340c9404200315800c00d401400381015103c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 883876699 1250 883875449 883875469
    0x108120409020703030e0d090303020d0f0e0f011214060f09070207090b0312070b04060b09060f150702030307031d0406031718040c0c020f03010203090613050f0d0509031b 75
    0x4410001d0307540c0c0544d0504a018008001a00c1103d004503031030788058582111391031017220f2080e000c1d1441c1240714001540c0f8040107801d808046000c511004c007082c90403a40050503020141071107140310354210000c500b00d413040182d0400c140428018801540b802e090000c180080c00c54a2280d01e2604280003910350206220300e0050a440b503095010541d024401d900303002803000140e81c2c1ba26500e084c1994200f5080d242942c3d031614100d29000b0f64100028800e204200140118030380040000078000c968014405032221b0242c05c1c090580143d60600c02803040c54000e90391800941500d40300e0881d03100359514100d2150745002e10410000700926811145e01022050036501c907180c0001d0740701c004020b034080503446840d0001d50703020b103a0002800c01c502c0e4001d8403c8084021f40405040c201c0c40309880d0011158401e00014240510710140104c04a00c035070159014481c246104528002c614103100022583c00304094400d410108071510150400381c030400000900d842c041410100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 883877949 1250 883876699 883876709
    0x30102090114180306160e04050103052e0e06010303021b090601030c170408030703110408120a0903050f0a0b0609131502070b090a0212060103050303071805030316030801081204 78
    0x400070420070340c043d07240620080300c0340c000303425681940b811518510303580000c0940400071501c0c1c1002c0c0e280605280c410103068907803041c002c041c520551002d016131600814902003241c54480100c0b66240c045003c0d6100b101d051a008040e154158074029003080c00c0c0e101510540c201c2c010518805655028000c2d410190078200061143e401c00c1c402c40750103083c01c0410900400c1242804104881a001035120340709594082180580240c51210584a1403090310816800000408840642100140014070050801e8580b403907980d52442c0c10020700c0214846079810400d461010b0013010b00c44d89620080445682201d80303000e80c04030100203d0200c02404503074a00c07020028510403a8111800740741c02403269009440c11f19074017987d41c002003c0032405080c41c0e607441981c0105c0010143d0580e81c4c0300014500b15030356064101c1b0305c061940b4250740c82d45204000001d10382c40c01d0005203103034503000840c40500d0b000c07130030050300c201c0060348020f1560f444803442c000c480e295201540c01344d40c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 883879199 1250 883877949 883877987
    0x9040b1f0302040c081b0705030301030605092b0e1807270e04152a02120a18050a0b040320120d02010509010b0904031b080d02090f0301020901 63
    0x80d610240c51550038290340000b0340207440e15940c030390036a40000a81e8882d0b1402030fa02080540e0b65100103400340039803400140507a10a10041c0001030035508400e1748102e808088401c1c07240d0720345410030007040c0702c0c80f8071000b8059101c0d00500c0705da011150700d4a604d0195614080c0b020311091080e1213120080c00001040034420741030003078000d0400d54000e03d41c2017440010041d034881360714209030744041d0380c1102c17546a8119010f003213216a0160841c00c00c05882084108601312140503610b00c03240c0e40f09421805040e84203560184190040d00104000b0b1b603c0c2842c3d604030349402d1032810700075040540b2950040008200310300c080c0e0704941c182c0c0d40c020140140c2081154070115101c0166010740d41c84054159125a02d0200043c1c05c840a0802d81c0240b1040d26010352030750884003010318107500b1451660020700132900402840e00c1d40812032803004140c1b907080e15420303c40d401c030103520303c81d183d0001413050041c0b800951080441908034000c52914264400207004071000c02a002199 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 883880449 1250 883879199 883879231
    0x3080a0b060906040504020c1213261908073002010e0606220f0e1501080a111f030608160e07080c0c030c0a150b010c03050d0608100e01060509040b 65
    0x9140c10700a501c113000901034401e803240342c2e0703e9000c1c01d480b40c24041e10702c3e900484d500bca42c0c02e40205c4060581f44400d000604075040305c2070386d282e1915129074819220000204074010010340301c400c4c1c0140c286030315240810043c0314040070070761807800800080e0440e0f0500d41c0d0141c0514000c88c10319080304045603000c0300d880e8240c1c100091200740680c136600544c5440d89021030703540d15400403070140c207d540980c0c800080854080608042c20300466406610420805c000140b1040300402102001007055104002c150bc40c00114488041c14400184d1a400e042000180421030b030003109080c1c81c4c051039041c1c1013140c54502c00c00b00810500030800440301023140e17034202808560317200c103c3d0381c162030340c488244602c956502c1000100326041052140c1c04c198032212449403006841c4144c1d6039100d200c80c0d5840c100c0d4507806c642c1c2809051992034100150900d420000c03132400e8000c03800c0100d070030000520030700e085071125486540964484010800064180e0300d00a40c4000e49801415507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 883881699 1250 883880449 883880467
    0x30f060414240d17030403030605010903051f0f02030405011a03120f0d0b03030708121003051507111501051801062a0204060612050c0405010c0b09011803080a0b06090604050402 78
    0x107070412074203000d0001c4c44496401c03480b841010000b9849907020361410b0050319680d000459038000e40c2e11014203907400514080d40d0a00c5490145012800010004142a03184840b444100d0f0b0056400b00d505a40d1180e40c0401010311080c002c076511422400741507440740844400c087d51060805220b03045c180090b42000c40601540030b600030305405170459407580046d241c09071407039010303032400441151802c0005503440a481a03c5081e04c2d031010203841076460b4419003590144001c1e101300c2c2840b240410300c5900380300c02c0010004060f100c0b98102c066501d84014000104104050040c500040000602109400c540c0c2c01c0c50f6007141c0b84504040c0070402c8501d410503008800020340c4981400300015119501605050010070100f000304265291885403080302c0c0704e42e00c01c4034080b030070581c03001c8041000c1c03503082540404500d00200304051610b504403c01d0585c41400c902040b20201070000200492207101d00c100020b941c024981003080c00042c1c1980941e11895105036000200004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 883882949 1250 883881699 883881709
    0x120109021f0c11060c0307120905030703030f031505100e0405150d080705210711010f0e04020f040f06022d030301090e01140103080418090803010510020a08030f06041424 75
    0x6444030b1542503d840b40988d143c00044e40a082804400145070684045aa8540031541e41c0450741d00d07440c0d0720381c1c0c1002058260040c0c00302902c58180c030040700d01c0024242d1500e520b80d00d14034456a0f9900d80c100840d0041004413200a84114281206d1241c155129280c403246884850303007006c211500d50300c0e1884c141d842c0c000221641031240c0d160285030f080c80400070380500940381c8600260f480a8241c0d8004481080c0702c0c9140c0700c00584c440402c1065400c16500404218010b0000545000e13200c516507260b0f20050346c0f0040040c0d1000200b0141488407400c099110078107100000e43c0e401d422000141e5900043c00780b81042699000001d04090342580004503c0b907030b800b00408250f03503c0c10810225080303803140030369105078039402100b4040c103442850f081c1580001d8050960f420402480030001400319040c00b940f2401a45801207403122003d14030401d0907800b1001c1070300d441d0b0144000e07280f21020710368044800d002802158102001000c0c00303010040702018860b0b4960700020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 883884199 1250 883882949 883882957
    0x40515070f0b01061101141503070302041109090c03130b070c1a063109020f06040f08100e0c040b01030b0a09360f02010e120109021f0c1106 62
    0x4000301465000101001820a9118100c5903161110401e10b0b450041907821f03134139022400c0800a45400010300010654446424680800340499140b5520307540810120794208003400f841c2800410309452500d084c441080c0d101c04149030150660070000e8505042c001c50311002001102d0702c40000700342c1d92007401c620744c00729085007000c43c44100b0035403e0300a003c801d540c030718024080701d003004812804003155110500b41c0c0c0c40071b2440456a2280100080c482007908030b9000302d010741d4241017550303040041c10241c03141c450b80301e860519210b282c501e002c8a4400c1071052904002211070030030030210300100c0000081e00c0105001510800407802445400240303580a801c0000110740c10301c0e02d5100d42030480410142c5c2444000100c42c40c01c0c0e003024490324001e030b1980c407010040041d4003075403034040851060600900d10b0020704000384411455007070001c4940c0d99181000706618203818026080407141c40b003054240c240000c0201981007802014000c0c0d240001c0152454680e1802c84e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 883885449 1250 883884199 883884203
    0x60f0b0313030e061b010c021c050705011407020318010804020d1e06050a0b01200c13110a1d2209030c08070809120d0c060b12010c110106060c050304051507 69
    0x11035403050301d8038183e2201000200030040c690701e03041f418141c860000441c0c64030503a0000e041034105401d10300488455010740400c840035500c41c0070b080010143c001405000d12000d40155407244541c20900042600e08840d13581001400030034040036858030601035607143e82085400503148036440d0382800c400d9100800412080c40d0204008210003070354800052448242c0c2c0b141a18524071240c10b02c98048103009500581080aaa541c180b0340300780407042c204611a800324201080d050360f00b09a0308040307050300c04164041111004480c2c038044154820400f2100444e10541860103184005414112820026a540c00400505000b038006e2407005502131502135907404d03285081101c87d082a4540c2d400b81f5840d050000380b50a0110342514414403540d01d4590302e4141c0c1d1120300203069501c07203803034105814145042d2045020300401c010010291501340c880440d4941140c02c48515520910401a05150101c00940b020044a040300d0301156149800d4039200801c00d4140304201e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 883886699 1250 883885449 883885459
    0x41805040501090c0b0901090b0708030703020c0a17090a06020f0705060f0405090a0b090906151c0b041a0604090c0317160c0501090608090309040903140f030a060f0b0313030e 77
    0x40011881e0b07585c80240700229003030f45d4412642e0790f146420b0485000740907005110820500014190f903100c1d07805003e84804030802c40340f150295488001400c41c620b00e19018100d00060b00d49803909011141e000200014030041842000b8016401e071600d00c180a186d2280400142800c003007a0108240c0e40a448010940906807e02012503c0140803c1014600034148071001940b030101c08941c980c4100d444000100301080d01101f0030070843d4500910440015920400c000452180401d9900ca648100c01d1034200c21056106d030000000c008296503c00d030b062480c0c540000e5416542e01c0100c3e03510070340e20320003000b08400c0d44030b140c0641103e03440850002800700f030500c40c140c4543d400f290001e8075503040b6151140401c40714600d08407030030007590388200005070303507401c06601410b43d00b4040e16044040030001d610002103503020075019810000f0100910400318201c4c4200c030700900840325403821540c6480b800f045107000c002c054805145005003100c0615000e104103064500703000b00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 883887949 1250 883886699 883886723
    0x908160f060b01051810050d0f0f2d09050a061d010b0a18200a0f090b03060a17010b0303160201030501080d080f070302040b041715220203011e0b01021204180504050109 74
    0x1000c4c000078050300b1007401105081418190048501644032f01101300920072920035501001054006490019030032070b294414141c002000c11400c2c45a1240100b070031121240390340c62104001c2c25a0803640c04148116528581005000420910500c1c0c0c00c550f0280428140c1c41803443d5841e0000d030508840a05000041010141d9400101600d4900030703500c1c0c4401442e01d074980500340340000c80e4100d82000d0b10000500140c0a072000703120302c21000c14004900c4c004804040b03401c6402c80c80c480d051000a02500e14115070305401145d0250828500502407001c0b2000300805082024008103074000c04071020440d0140b003074044a0280c02406180b66a40ea6512084501e160800c079a11314a4003c2e8103130b01504110340007600303000c0c014441d100c065200007045140c0c0c40200c03190080764903659a03024010000d03001454440804854803000651312004800a81071440c420f0041c12081c2c0e040001b4070007072200c1000300204241d03506002030b0075551031401500400b00520054070004041d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 883889199 1250 883887949 883887971
    0xc020604050a081c03050106020307030e030f010c0918091101080601020a05030f07031e0909021602041d0c06190c032c0a0b07020102030702040908160f060b01051810050d 75
    0x604101308440002c0100100c081c11841201100c0c003c1c09007000503001003003010003091141c045040240300003000d48801210b400c180f1421034410550b45400b00710042e500700304031500f0400812580c40e04a4040c0b0521001d642c4620042200314416414403080c600400e078288d100308505e8902c1a0300800312561014080d42540154000500c110000341140003082c00d8040c000c010f00c0c0040026403246013009042c83c80320006034108110b58142c031071002015a01503503850151400031803d4401c0c2001c50001c051034541030800301885280150000c0141c0204c0084965039906e415103e032400d43c40320145450103c07903080c0307a00d42883c52240064003c00c045a180b00c800c000f0b42000302d40b02a40355603151003c480c6070003040f6000c1e015030014000d07803015042070707002240c2e41889005118034011030b000c8a000401c5508a003904d20000c000d404204100c414802c0e00f0f6400c0003402c1460404207443c5010b00f03c0c010b1700c11414020f400d61080c00300400c0c0140c081e0340741c240c181c19050219a25030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 883890449 1250 883889199 883889203
    0x90c0c07090504200108270a060e070b04230607210e0901080a080c071203020a110f090604090f060e0f06060d030f05220b04050906090907060c020604050a08 69
    0x9443c00c0d0749004d48804510151440c66106005040040e16103003140d035a2883d0222445100b00700b62811032008505503041340c1e03014012410040e01c50b400000307074248292110391505c15941c20502031101d0400051040da40813291070041611002d0130304d15866446004030382c041c021440c0051a040c001e00ca562801940d01c200715a420045544034660143d100c820810425002c0c40707050300301c0d000b0722002d001007000b00000301070401180084440301a5a07005015032584514030940c0186c000c80000f200300202110360000c155400ca84a07a01c913482c2000099100c0c0015141c503100d1070340ca661079400c111841015410264020400b00010840c43c040315480d6000450a61060f005840c0040d1452070b18241c03075422943c2640c0c4200c0401096001a0f620f54404124860030810750061100324000d2915418090184200c042c4d40380d03454441403244010003d0142481101030798200103541800103414000c903021460701905240090022507840d12441d04500c0c0c014840c074a0210f540f040c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 883891699 1250 883890449 883890451
    0x12071410020315040902090c0a09030c0902121302030c01030f1409060a0b1504030f0804030803010305010f0f0b011409191d07021c0f090819020a2102090c0c070905 72
    0x1451034102215a6010041151740c1500000d500c144040b0105200380710b0300c4040c140d007101c0d501b40050394075201c1d255440e4170041e541c040c2010f15000540185d5a080c10040181c0041c20440b000d880d100f0544d0010b5151000c1080c0a4105981c4501c1c405400710190011204e012844014195170309002c040561140021140324030f5841c00c1010741a424144084d41c40300c0d0300c00c0e103000c9509060035a0796403203510308024000e4030422024440407003c5020301c0c00542c0214460000010035605064544003591181209440c1f0781c0d103003902840c3d841c0d81129144030103419110481c0d5680702c0175400520341e09030204160f848110b590304041000c2c0d442c0028401e21000f00070b1801c1c074588d28480201e03610344111004440d81010010039000c018010b0503001c502d4013084c10581019620b45101c2490000317948050055031034607100c207000b9410700c1e1302c003000909105242240101405840941004805080240a00e8130400010445042c00068800b000300f0003003a903000c00d41c1c510700c18002d040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 883892949 1250 883891699 883891711
    0x2031b13080c030c011707030e060f041703040203061b0d020406050904200403080a030f0f09030e040606021b040f050106020703060609050105090604090606050a0618080304050102120714100203 85
    0x102d207826020722840c00152911400205075640e94100c40c00b1075892007480c101621840c18103860f0442da18000d441400040c4c4a02040c0c103580210f0700e458201800b00f02a0802c10765000c5008005100161300e010403507030707402006503903a4900c0f403c15005031200d911905a0340107003948085800700d00f0326031000041c104540120b4042c024000c403000c008011035066008114158400c000410004111030301500403030034542030009080c1030103201d800c161a00c1c5002055229603e00950080540000c2c1e08800003a00b510204040d6041ca4030196894080e00d50058080d14005a12003c81e03499410420010031400310030310040d692a000659243e081d400100c03917040c24118013080302e52081c4075041c1200d400504082d0b107521410180030091294000640b41707183c89030301c040707880d4945100c601300914040e92112001d20607090980d200301b406400c040d1550b00104030130805a0303400901420866a6518400d50312002840e14280700502000c41c20345501800c056295810319a501951040f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 883894199 1250 883892949 883892953
    0x70504031a07090524070b0403172703071401021e13060c0201030f0e0c030d1706010f20010902040c0c051e1006080c1216030602031b1308 61
    0x1000c00710182940704100c40d441c00055400c1c0d8100000d15000501403a0b00104240490761038140342c5101c00554080311080d500c4000040a010815a00043c22078400001404e41d039400d0400d124000d182d00c0e502a202008910044d00002c110f800620807034550799417140207903200d80c2c4a4060360703020b90000c0655600d84040821054408202d0307004460b5440710001d01403424a04010382502d0f00042c0317400607410140d90307100c0da4145080c90b2180060343c00c1c0c01002069094552400c041c941a98030355040c041024240200c1d040580b1070f00f00640000d02402e0042e40b800d44600308032880d2202d0318034216880e10100e058200080190720414443d80260350034400e001040c1020f8800d540100c00007803065000310b42c04001e0820419214010710032220903540c1001c061178000b41640d04642000030180c01002c440200317450300b4099580740340f41c48409015a500d0318800e5000c02402c0307100180c403540c2c000000a60a1141d090003100700d0b0743e0b44202c0354480c1d9010307008907044291401403640b18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 883895449 1250 883894199 883894223
    0x403020106170307061d0f0109020901060e030601090f14070314010e010305031903060801090b190b031b1c030f020d090f1a070c030f151a0904021807050403 69
    0x14040c1007002c14504800c0c00031460300045036101402441d4008500d4194405588200240c110a010030404058840300210300a000350040211080313040e0300201c280540304880c1c20132038601080740750440c0d0112384009030a11803040100c01901022360b28134507080000c1e00708841c294050b0301915445d08a004c12041580c3c071090a2a4140c0c800e000242040c1c2c01409052951101084800e158064618000c50310356940c011240c2960160f001c11110240d0002c208000f001d4507000e111002c081c1e92005008114641c00460f890b0603007102804203503045c8004070319040c3c0314003c04001c180103503501084444100d04004205503821244940180550f900c4420003600c42c044038000d0b0380d000c401ca40a00d030301d40346c498010280c258020091a107400e0045c9004581c1442c10100154060070040204102528000803031030540c40d031a00065251200c2125213110120f41d00121070700c10344407090a034480e400010004803c05180d109100c0c000401c0100c050f41c844081d0080b20f104049000309 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 883896699 1250 883895449 883895459
    0x809060301170f03070c14030a080a2007060e0613081e1006051509150a0504080f06090604020d05011b0315051813080412084f0506120403020106 64
    0x200c5c416030502070710400c5840018006102c1005a808007244014100c501206c12503543c40c9540c2c11a00411000c280e0034080f18042529050074145000c26100291041c1c03801c000c1d0280c00403a00181045c010980850010640b00140d560103001c0e010070000c69005100d400301d031b0544142d50008040c0d580c0640f1f07007180328420160060340c0035030b50020011409002260440743d0301e60031807100641c1c007050382200c01c00c500c4401e0004003110f0440d41d0341c0a540354280350143d482d1926461310043c9990040040003000b0801188643d0441e80c1241c50445541c03080c24034a0160032400c1c4005003100c502e0b0b1614001640561001800f0103c82543c01c40c1da9681c3c004001c011040c1100281015201e0800591901107052131408914840c4030440e04041e1549200104007040c140110b6401c40b0005888003401032000c4101c001c1881119010151002c04a80b0b498036a501c1d404080500010020200403020aa0521014140180c041600c8250705c4200d880d8080080c1c40c240c000d03510341000450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 883897949 1250 883896699 883896703
    0x12060c020313152a0206031f09060807051f0806040204080d030c030b0a031109070242240609190f060c031e090e01080f060a1b03090809060301170f 65
    0x41d02007030b041c041c0303454258135800340002503000401d0341c2032a84608e551417a01300c0c1c4c40002440904000c540001d400d0381010300d444d1070b140a60700024452083c585e296510100000000d140c00955450040c05546503800858042d000b207420510f414010000d03407508890381680120f101c80740c1a503040c09801440814440b040300c0f680030190038190104010303a41810400d0038560040b5040c8111030924035482c441d840810420350b41054940b5000400b00720b0300258510070802c007248400c3c0100d007401c0081c0801c0072142501c01501001603410040001c41d41c0e8202604d2144002030440d0410203401e41010681d51554010f0b6404000310510204245200710204035005a054550b601128005240c80c2d1841500703003250400c1045100300401c031901c0250f401070090020000401018104140386828000c0042c15044450b18241112209100c6103075103490724400c43c10001940032240c1410030440c8529a0000d03006500000001140119010100c0c80f8104000649100341250300c070036a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 883899199 1250 883897949 883897997
    0x61605010f29040216020607030c05100b09130c0e09030409110a0f111c03050a0e0a330c090e011e0302040b12121b0712060c02031315 59
    0x482010916402e510709030419a00910f1104042030300c1d40c0440c1429400921543c1c0580e20840c00030311148410010880e0800000c40340c2654500d0070f02001440f2400325804060040c41041121030403103c40b41440440d0242d41c016003440a810380c910305d051411103139240d0140c41002403007464450a8038030314006605448207401c503581c03011540c80e0920001c50351032801c40350000c2580180d03100380030045102d480704454040d90340c401049500d414003a120403150600011a059000040c180740041c1d91000b1401604280020324460303030741c0b0100c00c0b41c4001d401d6844022003e00e08010303480c8881d0444041b40807580c0441105803280e03211803d1115407600f1007013050504192420a00061420340c00030780100c04040d14000d40e080701d2214641c0307806608070621801a2002802c08000204031540310a5040844014420140740c21146600e04c0c40c100300260446956000c0300c180f00d4424011980410086c0d08040d5841e40c0b180400264a1711514415004c5880c42038840b000140b08a041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 883900449 1250 883899199 883899251
    0x10080613060b0d0510180501061d030a02040510033f02060c0f09040c03050a0506060c15130231180b0718030503090301050a020906041202061605010f 66
    0x41400d00500d0510f074009020090510903030943c05000106110300c0c020011110405200c501241c2c552500e00080c005412410300847d80164104441e42a0b48000031240700e00e0703a060340c0006240d550800145548200c40d00000d00388500722041c3c0c43c05400203281302c0550b41d040399584080c8200b140c02e00c0030b080c403c4240070025070081c60000304001014000390805695041e2502e1400c0b1303020b00054219503540b00000003281d915400d002520340e05102d07090b0310420941d402450403001c202c3c0c440d42d07911010300c151500b007801070000d03810880a01c8440c00965001c6d0416500301582449a80200c0413800742007000b8055803c111006a4140942d007801c03480e143c0c0740c0300640b220b92620210410006c1c582c1d01480b480400e801040c01c019044da0000f94080e002540c0c41d103905104050075500058842061540184008020741c1e50303a800b01d808035503040c140f0301c841002038404550035018403000e00102d8051901c8240900c00103410900038101d80b000b040100040f149060358400c541d180b82 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 883901699 1250 883900449 883900469
    0x212010509070b07082a070e090a06020f0403290a0c050a12060e010b040e060a030c170a050a03030c020105060d0c1502010b060a0f090b040e04030f05091008061306 72
    0x100f0480c00d185008000300d40c056884039241c80c682200c1041e8034100c010030840c0580b0648840b48405200380306583c050001e0302850312180c10f0000300c1c80d81e01e4104800240000e070340025850004255030040314000d651024400400c1c09041e54010798103040390007000044000d40d000146803400c0c2c4d104540407100d854640b03500703020b150f8030101c8142900d540542d024035035502020501c240c030010030343d00900c0010340c059521070402810610900d1301910540c0542c40e01c20040c400144c070716892800f81c2d800710748072480f00070b04105018900615850003400e68002c441c0494203042e415088540c4521090b0001c0c84117490341000e00c0110b002a51005c1d128040c0140140401c8505890f4580c8103149840041b0704a2101400a603460340700c500840c021501f0b0515910a894100d115540107021201c0d02d00e041034134080031145c07208001880181000004490851800d00400588071442c4001d031401013607070802000503240610a944880c41012030381001c01c003007605402084151148224 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 883902949 1250 883901699 883901713
    0x8070c12020303030109020d0f06080303071206080d0c0f0605040b1005010516080309152716090b0d08031006020105060d030c0b0403021e011a01050c0d0c080f0f04030212010509 78
    0x18510000350850123582c0e034802d84405581350740018a00615000c0c2440c00081c5a407414050030251042c040381c041c0c2c14540d03007454030400c951040407544086a2045003000c0303000e0081441c00e40350f61640342c80e004000e82d107050240418018030448580c0f081664018840040340c854005440c64000c0250982508090308000000030350001d001d103800a0a0b07400300c880141c00c07801c080d2520103044844244038000c1000c01000070b41c5180358050108010405424000056003615070000041d0050b5482580c90f040800071644403841d100b4185908401001d449090940c0c1020b4141c10610134030f8019030801d0b0121740c0e10300e0443c0490340841c1c0e0648450001e558140d0f206001200000c10503002e60145852000c1814105000000c450703014500000340091800341c01018002a003002c2e0b030400600348030403042d5100005601011300847d0801d00341491051034010b0561245020301c0c070f42060081003407a50f0120700405002035074400c0b1040d18861780c030301840e075080351000c991124240c2c0c0494 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 883904199 1250 883902949 883902959
    0x30118090c081207060b0103090c0902030411040f2901091404061e0f080a02091f0504020a05040504110f0304080c01020d1401171204050f040b0d08070c120203030301 73
    0x1a10a0094034400c900007070680c2c1d0355441c0d0900b00240b8510908050000083c6041000028410745552207001d09042065000c20b4480e42403196041c0500001070358004003080600200221100c100d01d4020301c00c0c05041007144014024214400e40000e641c034404003000076000811114140302d0703030183d461900d424984020404003521765a101034005580720004106a0040c441d40c002004108500c1c1550031300e04000c40100d182907a00c016103541045941e100140da40c1c2d980c4d00d4011240c8075440400580814403032604030043d510280d405440014002d602c540c200d00504100d5508803020805c00035000400201d5100b443c0c0c01103503401041001074002040c8101034200100100001410004603040240840d074142c00b0a0b40303084d244100400500c0c520014082d00e11303600d040607005000703c40c03061803540d015500490f0b102d443c040c0441d00c0f0b103444990140700913000040c4881100409400c0c41c420a42c4540000c0d1040001038401140d0902c03424028401142d019000318a503a20305 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 883905449 1250 883904199 883904201
    0x215070309030e060f0c0601060908032a0f0601090c020a1205130902040e0f0601020c03070e19050a021e19050a030905010203070806120120090123070201090b030118 73
    0x5201201800804020203c03075845400103020121002c170700581c0c0e51124414028a0030905a07c0348042000c281818818032001005a4040c0800306c0500d000380b11005540c02c02900c26030100745078078840c4030314054020000040c0c00341206d4888004001e0603c4d4864101e850741e265a102400030390b0b45a80401443c0d101e00018148000a00000281d007603c8405582c16030744598451280c00c0350b040207000c00d1403010352040380c002100740001e0299141c520086515030800340306c2c0e4440c4802003030024220403074803020700c80c0021050700304100e02e1a21881800080d0848500c07641408003584c1d40002e04106e2004903600900d0b200e00b482c0f42e02030b0301c04080f2459400b41c0b50100030035464801d2100054030900155019000d59242c0001c28640384090200001840841c030360a40c2c14040414204c240801114a0b01c00c040c1081c15601c3c0a010016100d00302c1007054807200900000c151400d2041e1100a481410b100b40d85003491182d444405d044180028015100c10f114401e807004a14042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 883906699 1250 883905449 883905461
    0x603150b0d0e0a030e0102100605130b0438030604170f0d09030203090f1c020409110306010e0103030f02010203010e0121050f160801090c03021009091109090702150703 74
    0xe001c101140104160072420b0a20414903812004101172091000c229a018002e020741c0a500802c10080240780c800000c8c00320848402e1804140d90750000c0708030a498603085840c1030a40c1005500c00c0c1141c11844540c002d203501240c016500301081003c10a190120341140600d4114000c69044251803101103050340c011125120440b5040205000c99030b1309008058042d4040d40155455501020601030501d8100c40c40c1c07441911000d82c82c8003451001d6289410f21501030728002130098440c60134620550721505029450310680c0300026160b1404004030341624465030710310407500c40c00041039090707000070b02485410310212801800780050001004048008480c4904400c0845071500c9003014801982400d2a410000340800e41e011210191001000120b00800c016081c07503c440c40b45d200319001c02441713206440c600c42d20361885121080042e24103a10104003640d08540d80903290792040d1440e902803044500060700c15800030030421021815040300840d03907070f21290201c008181d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 883907949 1250 883906699 883906717
    0x110c06120628030602180307150e0a031a0420030a0b04020f0901060e240724060f03110f0109060f030603050303090c1c0f0f171801090603150b 63
    0x1a160041500b42c0301c01c40803800290300407500141e41741c103200754071001d0240a59440d4002d03400104100316015043d04000362107900e520740303445000c1045000516444e502d50003d4444a000074143c605000c01c80c0c111070240d4800c200000007031940714007955080f000c0ca40d049078580c03c94141d040c0810388a814403940588028181c0d031141d28000b0000760040000c2c0c21039000600070b92340c002414101740521504008041440040c10030762244100284d07c2088801064499050a5108003d200303074202d000d08000071a0603c071880d00c45c0310b608202066407000f0340d18000c1d014015441030901c9505404400d6040e0f5440c480e4504000042d541701481403000000c00d5a102800008a40140051801400741e900680766a03220a170810420b00320179100601400308800e10362000510702c220803844541e00070074456000c0d41504062429001c69600c1c2d00c3c0340d49001884c0d211002c0c003400d00360380000c1d00762503450344292101400c03000c441180065140800485800b445074070303d0000034080040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 883909199 1250 883907949 883907989
    0xf0112020f06070b060906060f07142a1302030112030c14150f061503130c03060906020d11030702030f030405101112010608070c081e0a110c061206 65
    0x1056041c0030405075030120703505966556101080c81020300d40007441c00e070490412101d1a0906141185042840c0301d09900100145803081c0d414806001c1400301015409540482c803052040341041c8400c60a1a0b0243c5442031000c010f00c4850140b00d032080e039040c0c6000400300040b031043e0ba0b0382500c103507000e50010790341c0d482e030441d0174582c03058104007011051b0041d00d64440182000f503480d21204c03178050030440c030079041c50009014049140e81540e902c20402440501e00d100340741040034000c100c54101800700c0781048003001c14800940c009040b40c1035000000c01c00364041811700e940c0c40c08182c4420005800420104441e440c0320b0000e550000d0298055940d103d071100662421108200c80016041002194025200c9848005180140503d06202e04545032005004245803030400b801032a6150128600e0380c1d40034000072451111288007900380d036800c001a07002d0200100c2d0380100c00b603032055200d070200d2414003006469810000301c1041a068480c4410000000131110101000c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 883910449 1250 883909199 883909219
    0x507030e0a0b040503100c0e09041509080a0e01111f180506011a12070c0615060e030c1e0405060324070e01022e060506030a140108060f011202 63
    0x1550750322203694020008400242d503075900c3d00d03040c0b43c14030303200240315100c40340790840008910750041c44007950b2001c21074401c4104e03503485c6007035400c3e0440c0b1015048114034001c003220400035004000d0107213505c1a26075440d4852a9401110107030a0320890210310780108481c981c05c2d51386c1c0c11407030440303165405020400c0e000300b0940b40390100043c541654180e01c40030041101034170710341c0388420100003070840e54507261190805007032055004d8050b900300000c4070401c00500a4992001194156510b03210080355500d00c1d006100580003280c4d0751180c080d005041d03034580b40030a110800c2d0500c60080c000d2281e04c1504100080c0780050265405000b24207043c0d00c040c400088600510f0b4150b50404258104841c2c000c00c50056482d1007410340d402886c1c194806040083c0345142c4201000750380b0360382c10b030f42c81c03200700580020351106800c4440402071000c2c0e400b40e900300c1021141c0381c1590340c0141e81c0e541b150a81c2d944055511010500c031687c010302c1720141d07010f01142a54009010340c640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 883911699 1250 883910449 883910477
    0x110417160b0a0f230706093008250c020a120302060a0902190b0706050f13061a10122d0b19140a2c060f031203090c0405010b0a050703 59
    0x620745c481001144c0741c40e6503c3c0e1003000c0101d21111840a44585090008030885000481e503c03808100c25007030a0040002c0060300c14110070140014440030280000c400c0036000d4006404c00894860492140c070b1640c00101c2c08400c0403c411502c0c0e0341640c000c0c102a160080000b00030b2864600680e04440608050340b6040201d41c1070100412001c0f01c045d64640090502408130350300501042a4551118107109401061100a20303000e07402a00014600ea5083e07a040d00c286030049040b5009041001c003414419003000006400182250b4107011408c3c80d81204880000b40008180700800045602d40e10140701d0303440040c030401c015105000703c40d48042c400c40c54030340a1b40315500740841c4120280301414030307242c1c0000810b14102031a5203803480b200e9400d12040b81c3c1c1e06515076a4009c0b00020010343d9000941182040040c056614443e43d4082400450740111102081c6110311018a0098140303480b031117040300d51444803a820100c031800212040d031300c805015400c000b1002807101e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 883912949 1250 883911699 883911767
    0x30705030114181501140f0909030a1b02030703290a091203141515030a0b09070c020d2406060906020d05090f04110417160b0a0f 57
    0x10040319915085100742c600303003042918001001c060100c16401c0302e6489400007920715145411b5817849002e2010081000000c1880001e00c050902d901c00c2c0c1030814400f81c1030000c402001140c2155489a4010851130040a4001e0030400020b406502c03207601000450007104917888500050b4810480750640c0c004041414841580d0f46899180e85201d15003c019503d800495070314514141801040e894000440030075900a05031541c1c29992030700348805503608141905c00404140d60152203082c124040381c0200210201240994089800700381c9450107117125040301031b402003151002c4c4c112692070840041060640107000000c0c440c822000545034040ca1000d44a182d8440000b03500e4100028601441005100180081049001c40a4940c0c4c0340ca210740942c241d802180112208400310309921481e1b00c204188264110b5076040c0c010702148850300c440301140a001c0795601c400c040819845200d42d0000440c4d200404101124003441d550b5955003040d00400030358100002d0018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 883914199 1250 883912949 883912961
    0x308030103080306130515130c0e01140d140a200412031106090a030f0e090109240905190c0e0405100f06170a0e1b0a03080706090b01050301020a020a110307050301 72
    0x3480081080c20003440383c8c00c3c5020090200c0924040502410001a01c00707805c2c90202031886040207518410560112b001e00103c2d0400d10502404000030102e9038024001ca00055603003840040c24800071512050030f224406c0b4681110b49081841e01d85062013a181c5040f44020403018482c030241c1c074400c80c082c10302042d44a0780a580c060409040140360080c66940e40c401c0c075100344900900c0106094483d00fa03c50f055401080000401c281ca250046010030700950041d0408003c3ea84007080c010000e42141d4010f840c4101500c000740000100340041d00c400004500004200000c200c0d241e160581001e6003020811504c41c0011780c949211041e0040c0326003044000c40e070180c00100300000e006903c2a44024804401c00c44c1c444011002d9866548503075119550070241c40c1100ca1031341d1544103400040d030340507603d03656600540c0741481c0a000c0302c280648140103604000030306410f040c0200c6007180943d0b80940200c1255688000c2040c140c001e405405104206020459460912940d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 883915449 1250 883914199 883914211
    0x10e0d050901090905070f0305060a06020a24051801061a030430050a0206010e010f1502030d0501031223030c0c01020702090708160f230c10020c070f03080301030803061305 76
    0x101c01c01300302417680923040d680007a0003140142052041000100da0201d006103080b40e0004941842c1c05181c02081c90000890f02045036107440d0000340211454080b00601503141d54800a02859646091100d6110b1044001204400c001c10008000138129198020550202c84440755000541402c4507260030490060001140000441c4107411b6010400300b4018030030a81c4030301c810340c1070008507481400140f00d010703001c1d003240180b40043c0e402441038070031300e5840110800a03913949040c45c181d0319401a010b20301041c2d81c07d107150103220b0355030070708803440280c000c0305403540e1a0140d425503103a0001e14201130956080c0000c60050b81c0b44984d45002d8891a45e0b064007505000b00156504981800c81c01c06020700c1d510703a0a40c407034100001e04100c01b4034a010700c03150a212120804948501110125a40101c1e040d0306c07885800d40e405044441030780401c50740880d45442200704c44001d035001c007900004003400100000b600040066a00040c0909a480f03e001c28203401c2c81a11010f50350 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 883916699 1250 883915449 883915457
    0x7050f06160e0306060d030302210705190206060a05010e0d17090f09090d05031b0307020d090504060605071202011104150f0302090d021005041e080f010e0d05090109090507 76
    0x11128080b940010312440c1094102c01034607240c10180002840e04119000c000c09142c2c0106030403000d40c00240c4107513180f0550300344c4000d42d40b40c0054003d2030782d0301841043d10500c0034440c45d2a01d891000818920461014010349181403d1034010340700c9842d40d03151b0baa17000d0821130300071001806008540617605041000540c07150455002c0000c101c14404041d40a51080e02c100030083c000003e04204146244c104599280c482c0c2812040a40b02d441c44041070100020030b015089038000ba8000e0307103001030703500c0301c4030703e51240208070503101503100b014001003017806220080740300d02c1000c01a0101d83c0c000001c0e02c111404104030300c0d4005074000c1c00000b42160035004115006100040261014074003186045010300004062a1061401900416841d54041e0344280a0400c46010340304140306010710311200108245507101c1030003910154040c040310f140c24284140951801c084052014202907103200404890036002042c070141040440301e030001c1c03044003a10946002c0c100303e5603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 883917949 1250 883916699 883916731
    0x3040902040f05030c10031113030b060415350706180602070e28020d090c0503030307080412090b040611010c14040512030f031824060607050f06 64
    0x100c04103a60350f5210a000c0e411504007045241c1c1e4048100074800c0031810000303465907102c2c13403041e01d034041d10070306003810ba0040f0303004000d00184200092044078220390501c480c0102c1074010b0300301d125510815040d0500719405031108c200700019900c1020100c0520142e0b04a144660313482c0505640c0140d007c82e407050064144500204001800f0b010540014a0680d01d4440d1051004100500d20114058840c0c000c0245c02c0f108006150041f01c42c800c05d40d102d11000ca802c0d4018008260110390011441714009901d0a0110569100b041d4a40310010aa5640d4031140d0000c07026028450030040c52030300208083e040100580003803c200c1e03460b5580031503503500042c01c403081660702000f0704c1040040e242034481d1803812201a00e4003074031002a003c0c07200700100d03d54000c0000103e41f030300300030042209a55803100140c4160484600315080c0003150058030440c100c4c002c0a4442048074100002c03581d09000c401081343c0f511841c02c0b56000840500f6807428100d0035100b06699001d60301c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 883919199 1250 883917949 883917959
    0x1030e0c040501030317090d1b060e070308040801140906060103051f0b0a032a0e030106031e0b130308060f0d060504030e1509010516020406050909100c1e12020c0304090204 76
    0x1b42c06198011288401442d044821110180405c0041c1814005000c84075066108029558200f03000240320310040701d49840c3c076890000840c0c0c016014085581d0f180c1180700c0380031094950351a01811080c0050405a00d4000044001d8000141040700d60071254030b8510382c1e06d502d440d00350024800101d065443e1040b00000070103403501c584400c00e9500c071001e81c1415403411210400c84031502820f00f1762100285101017800341106600c09030803c0d0740e06081234034110389006400c8860344100040942c0b0381d43c2640c0321100c0e208075040500026880000200315081c11010321031345a00051111001d042c031380c1d5500040c0e032400c4408400064108031000e1903400d10740c603d0b00c40000b1f00240907090554842c0024040d005044010b881010303100074003829500d440e4000006450090300d86071151600d02009a5078a90b01a0481c100300c0c648465103650a200e241d807525016043c1088621010840303008480c65031003010301190481d400c000d248065001000100028a00300f80c015840764038113 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 883920449 1250 883919199 883919237
    0x2030601060e041a3a051c09123c170f1c02041703030f0f010e010e0601020c0901060f080a020c070b03040c03150b09150102030901030e0c0405010303 66
    0xd11550b07034842a490a83e4106030740b181c5c403100020f039899041000038404800c10103030034400c0408504501426a00003000e200001c60041d40f402d40c031400d1000c91090b944011550003000c0e00c103007070200d042040c0d81c900248009600d90084541180c0d0301c1d01e01e2080212002000d900034900751182c01c00c0b046904100111a1844900c5200d105004e50820316851750041552141080d0000c0045002d01900884407459040d07070041c1c0046840200c5244410800311703a40e9105031118502c4100c03100000d500c0002611a00f0305841d4003520300e00e02079185c000194120f442c051300c2c29040d8014005520304588917151414001c0c0455943c003005605802d07030103000c6010140c00307071a441e401003000000006000940750125851101030075900da03954108000035000d50782006101441032a608001080f00740c01203207841744100c8a405043c1ca500c0d05800800340024001800f40e0014440e4580d80d42c0640e011803113010000f0155031320b0f1205800000c04503802608110b000c110b41000c5003030490b0b11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 883921699 1250 883920449 883920461
    0x304061202120a09062f0a02160603230403050a050d1e0f060e0c040501260f01050a08210306010c08070614060a1410050c0f1b030a03051b030702030601060e04 70
    0x201d105140c5040f0b0210042c40e00000040805020202001401031881fa108101035840b8184c003580040600ea25108014050862210440c00c2d50404500329260b4500e640382d503901450741622280d25200c1a05019034054200d0b00c0b940130305a0356200c80b1103004c3d0610503c60080e641700c407000a00e1035403543d40d200855140d5042080312080d040e04001094003100100d6055442c2403c00303004c2c1442100d080c45144054482c00000320940b0428011602440340d005416540d00304d400038505034072000100d546228102900800d0b400d0340150289090301403000b10313000f56061521881810381c0351034002003680100da00325801aa50440300d04013814000c04144c1009007203c0301c16012340f804002c0f40c03c80d00c01702c41c0c05205208009109008a0040049580b9119071009403881401011640d685403404042c0c2c1c2c01c0740e080f43c2e5103601083e00d800300d929003040740e0507252a0b081164052081080d00c0d92811800003521040002c9405603400300711682c02055035690b02c2000c02000b000307001c00c0e900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 883922949 1250 883921699 883921721
    0x20f1b07060f050715020405130b04110c100506010203090d0503070b060109051008060d0204052703041a070f060207050a1b0b030708190e0c010305180304061202120a0906 75
    0x148200088010b42e0701c00112041c5a410078825503560070f088080c28024030030f9034042580b0150801030501d0010054000200308803080368100000703280400341200521415680c3c4205400041c0b0060300c0c50306a501c000d81082e03061044904090740c0c00c1c0460002003104c401a981fa0340302085000401c6590704207954000020700e1b20740010307468000801c138440b600d04103d8046c4403034103000070015100ea038000074444d03800074002c1c01141413181b01c50285000c9180b00710b8610464503030309405601c0c000300f260104c58040d0040800240844241b0425420021089406102c0c002425000c1260b42c0081d21406001d10094000b004452401e080701d00c092000408980310842010003148038018140c9a0010303482c20300d501c0d1aa90760b0480205000125022010549401010004003038001544d4030200d101ba01c1c200044d8a504012640c4c011130658908a00d40c000c000a01595200300e030000e84010f00c4240141c00c01072075610440030460300b200d0300a20541c0d41d100c200103015850241c802c0c10302e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 883924199 1250 883922949 883922957
    0x30b071d0f03030a1215150e01020c1c0822051306030309090b0112050703020307170f0114010c080c0105040c090902090103060b240c0d1403041203020f1b0706 70
    0x306010200f5100e000b0720280c501072101095203285e0f01c1c60710760408440d42000300048a0890313128003240c0d503010320303420174000080d403c040c0c0e18207030f94000203401103c904d00074200e60703159148a00c001140400035800b1a02d060301445004828103550800314045003407a80f22010b07141c20801805003c80c070001c0300c224200e0411804101194020b80c014041e92000c0c1c60120721070590704011f030385404903444440c000a10b414204808a603060780554010300807035848222045045590350602e006c281c8112a0840383e5400410403080c0d0034450b910320000606120700d90054a45881c1850780150302c0180b281e946520800040107483c60710b840103000d824804120780d00d055000f191142c1814003000b420a40d49000c4481139982d0001800b117407030413100203600b280318052081e040580140c40041c00a02c105040701c440c0c0740c01840c8a03d465104294aa821a0340c3c40d2210b4a11141100d00c001c14107500b005411044440322005140c1c40d0042e21410300c03403c000d42502d80c50840c1d03075844a4100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 883925449 1250 883924199 883924219
    0x50f070c031d0f10020114060429210610062c19030f0204050604141f0e0705030f09060603030405060c16120c0f0501140310030b071d 59
    0xd40100101407500c0708040c0074166241800b001c0381c03507540070010080e80021044aa194510b030305400c5010b48880075100c0348002e07101d2005000944800c194100040c6110b8404c0c07445000001d00a2681080e000302804a6031440d0389007041c0403c2180c45420702500407208110075050428400d1000703011510b09142200c1040980c21404a640038030f10011045100480794640e5030701c030480000c11000641540019641d26001d05d58503401c0f03c0890245040000050311450140b0400440d444001d0000245683d03101801008516503240300404990099021940740c030045541403068141c0d403501c03552400c2c44071003401c11090090180006501500c200b004131f0300d02000351422240250b5130551280704809103d818100c1981c000740b4031034403038100001c19841941c3e585845074041d1080c0d2603400d0300d07103160b451180303410302070ac9000c1408025089142d8485078002c540c880303130f03100700e1490060b26651040d000101c20b6690300d0003e58408041c20720003044101c1d143d42204110790f860b1740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 883926699 1250 883925449 883925453
    0x3011d1509220b0106030e1011030105061308010204030f0201081503070b0d020c0f0c1503060f010e0d0609051b1c0b09031903020a0e01170402060c07090f050f070c 72
    0x90341100a0440c8411808076800c9500d0811a40c42c00300030310380c049181c40040d80c440b900140101300244445040748900d0309020115209849484501c008403d40349186070300746400d002c0e05074007403107414030801d01c40f00300014035040a20281000e94881d505078030f12000302c0c0c000100b01d15806040560400440c2c10072400c903543c0050014102c87c4018030072921400c945500000034054020881d805008841a0703400508000c180d95105450440b848000404036520740d080300d020884074290440341002c2c1403961980940707036202d43c2c5803008208044010855650400707a0b001b03110110762a5002c1c146001d04d02519060942d040d090944552940001c003424000c502c02c80c803003000e480b4104210101d0540d100a04c2290b0441c134211541d1302034400b05250003002944203001d1100000d0242034601021740c840c092842007442c0201c00c408054580e80c00300096a4010500e4000900c54850002990f5080f8040ea0030341000d90040020b0602c2c080c04030051960000307003070707404200e007160702800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 883927949 1250 883926699 883926709
    0x70e0108130209150d0c26100906060801090f030801090c05030f0c1e130f05030a060c050408070609030b0f04050d12090f0b07020f032d07020603011d15 67
    0x2841c650102c68814040e11284050710800751505111034001000582e41d000380b22078405944110380300b11840d00d844541d21081018040e120510010f0325801c4008009004a400d070030400307244d80204000a042561400080e0840c0d41d2810301315241d902c0f603581e0700281278000c00958010001d10300c092107c18003002e03000380648001000b04500541c4000850204d14400b4242e502c104427010301140c800100503580021500450102c11803400c604c0340109848044880c1c003811504090001e1008046c80d5480c1e4000e0000c80000308100030f400d000000304144200b04000040541d512841655421410304c03c0321004010030094150003004184400140000740c4017014605a24102280181064a07607018200a08015054000207100c13078061051422580d0b01031411078003222060f840c403005140d1030b801031030f1000ca21003460260f0049510ba5603158080c44003a6001010b14005980c0d0020340070f6003003a007148150480110010150156290047e0340285680316003100031001400090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 883929199 1250 883927949 883927981
    0x10020610150c0f0f120203180d0f02010e13020301062a03050307200627120904090602040f171203010e0c160506040302030c0106121a101508070e0108 66
    0x421445284000a0a115400050f96003940d40300034108122900c0c044020342d00e81082300781c00745081d85950800410300c1d1800c0481c0e00190710505c180342c0a51390342c00642e01c01442805098221410203000d5407000c01c90b00c000e6010342201e17114a19500c1030340180c0604406808562045010a5490200400d03080804d490f4042050700c4c0501400b490b80b035101040c2c4100c4440d44580e03124150600c00c1c10070940a000780801e0f1500300c4041d0300611240311650328204004000c0700c600f010001081c1e141440d42080504a014800243c6016540d40521031044195030101080c8003241c00e04580d1008140407003001c4100554a423419941460000301a03040043c2c01885442c80006015020940c80d000203107446410406503105441c00d410f0103900d0fa8030070798607406c0c55441c0600124506612024038404990095512550800200200517803208040d04c2400c401d15121000500007480100000d01d03100c05940700b440b076090541c401341058154482080c10300240c403082141d90040c1020385 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 883930449 1250 883929199 883929203
    0x60f0705070605070305152b02120304062105060108071202091f2c27040f3503040302011506020a050d0927150f14030c09040b040201090510020610150c 67
    0x1024155161000ad400e018000d1f880c1d128601000c40c0c00500c650b009410020340600c1a440703c1188040c41c681c2e03030200c800440c3d01c02d002c2113103940850a01842000880c00f4110240300040c0b8080107400003504030030402c01151903411814001c211a03da102000050034450802083c08406107400460004a00c07400028090718a0494141c6110f0608480000316280c415079051b040c141782c1000c10140040300301c1518007640003100341541200340794030302d204000f00802040301c5000362015094160304c090815000c40d920384001c108032504584662000b031010b5001065038001601e0b140c0d0a120f10a50000d05100c11450100848500041406031088254400050420411030b000004102036008005100c00741c00300440c543d610801070700103075180e0300c0f000300c8469110410550307030b014092010751300285110081703000158919001a040340c81410441030711615031021401c41020138140000585c004828800c0030180500d100003e800c04110041000c0007050000d00701694001340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 883931699 1250 883930449 883930519
    0x290a0206070e15030106050c160f140a030b010803072901050409031e0909181106030a090206030f0f130203120a030617011e020903060f070507060507030515 69
    0x80078a690b65540f0307807441018000c4403820344950b141c0d00004e025810500c08000c0c984121306a008500d076540103100100c8039030006269106090000031141070f44c08081d0307150400c40450000c00060303042c9003114060103220f0011511010281004509800e00600e102c80c0403096440c0c2c0c070701c4801d08000b001c1c1562015500402c0e1009245030031a06c580070305ca00c189641500c8071001e601030b980030680104980389400103001039540741158107040e03403280c240141502410940c00c0c140c4d0030850083c2d948002c50b0440000d03030000540210308203900031244001c1c032514000400c041401d100700d80d00d800008040302e581c4464440e5010070764401207580a454070100104070468203d101e50885800b801008090302061144041c50b14040c0c02c48a0f9108090083c0c0440d0390180d07807a62090310400000100209095200d500c8160044240036000303000300320b81004894085402c81c015030f40559525500080c0524150403918115032034400701500c00d02650302081c540412190380340015480002e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 883932949 1250 883931699 883931717
    0xa140c0a0b1003021e062b0e0f030901180f060816051804020c0724110f0c0103150306050f0601021903050d150815060901140315071107290a020607 65
    0x46c3c0318041c0a018110122580660002001e01344c2c43c18102d42580b60414003620901d00303c1907440b80c03940386c03080105038024000000b05602c145030f2020303201d80011a045455071100300386408003240d6044080030a0b4003206024800030142100300d61a4203031320f04a81007084100804a0411100081d948038a0b00403071000d07000c52007400600c000300503584409110340038041c0c98030409802c0131420400301d03085180f607040d4490040b8040002d241c021028110340c080000c01500208100c07039004040623101000480060898400c1714040c64a4500640a52a10748002032030000c1000300c61311681d207400401d10010b50081d081d00d00f4520b0420000c2004170f000720b4488003542d441c0e40030b02d089229021410b03e0302100c100e0f000740512401e441c144007a03030701e99107034104d1444031400007601903001240080c08801c22800f25034000c541498525012040501400c0ca03080054000003100c040701441010744090081d50905511028030b000340c10111413903000b0f5142c1100402030801d00c00c940d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 883934199 1250 883932949 883933009
    0x90311120d030f0b120c0a0609031a070201020d0e0102070c05041808070807052a150316030f0618050a0603050c091e01090e0d021606050a140c0a0b100302 68
    0x1030403c61050401030f180c0d04c005c030705101c0155995a80c0ea000396014050f0303007902103403051140d2500b00a4903040a414642e0002c00d6120191800d00204281d0840d50709220380da0742e80500e03005840001c41103c0015032580303e0360078144ea41c50b00705c0d8084c9200300e15001c5606420603c06040d040d107981c01c024a0347d180c10710390401d61030f140b0910314024000e0060300d9800244440d280040000801e50050f5280d481d0703c410103000d40b107081003510344103401c2d041c0b0020310480f8440c509200c04401d40d01c0c020524403a09440340b0b043d00d2068100c4040311385660800681e10b60381d0f21980c0d61064410806104c09895611a40d0b01c45044c060711a010340c54400c0020803854260350301080c01c0c002c05101d460b09603960b440d40801072200da18422854041c420740e0010007807000130500d00b01e4000b290100811450448c05035555072051441c4028010540f1442c80d44004540181c0744032010301018001c1c0403040e103014540042c0041000044011810051000d0b84840440d0b655008888406d000d42502803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 883935449 1250 883934199 883934201
    0xa02160506010627060203180f03060702061905460b040c08090c041808030411010e1f05030709170a14010204121509080a090311120d030f 61
    0x5660140940c0700305400003a1455000a580520741001506184a88a141000e108001140c0704d00001603100b0b201b007001004e001c254501140400511035441d4a28500100e4100311040300d464015030030000070010200820241041d030607211078000c0089181c040203280320380018454030041840304291101c550302c3c10712402003402c100b680c091400940309400c1440900144000c00380254180341d2940340c070382e0064014030b000b90204000303070403201590404e20004141c100c1307410f04000500921740c408a550180158081e0b402101562505002da00c0050306003803031400024020302c0b40c42d01841e4501c076103e84143c0006100c0c6400d40c0c0d81d1700c0b40d19040301c1c541c1490308000d41042c40c8284220942c40d0000c0c00d194040c0c07141d0340301100780c2d000003031003400c03402184500c100c1240c01056401c0003c00881038000340215410000038612643e0312080d103160060254100841c1741043c046c03040c8412008108820306040701da100d60451447d4010307480e030400508100038540c444000c6600358000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 883936699 1250 883935449 883935487
    0x503070b0d020c070305030409060e070c0b100b070305071101020f1507120e0102071b1203030b06070b040b101a12070908032101092a03093003050601080a02 69
    0x280c2d400300c82601d80c8031b0506503103d80c0144600c240d1035143c50741c000b915411021049100b81e0090f180c11040040d50346526184a1005142c600980425000410b502018102520303401d4060b0340c920303854020510781010340900c03aa03081c9055600c956502400302c0d00c0020303621808502082c6514154072581402e56012300b60640f050a8117080901c6000c010f01d055015003661806003801003c0080785a0b0162607805840c02a035200030711040c402030201c0c0c00f907040030b104040c014044915042071900d0b5800c58820075030b81203c090349000103000e580000c2d6000c51002d000300c603d40440101131030030481010311900f030210100c1502d800c001340c05d450103410100c00900ca040190f84d038071315a120600c4488010b83d039180c40c0d04000c9600100d801c0e101440380340031058400e42d505400042c041c0760101000c505142100405444010300c1e40005d07100c280446204441c0022091111001180321410a402004ca901058034041c200140741e039201e492940c0000d000000161358000250b0300d154040d035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 883937949 1250 883936699 883936717
    0xd0c0303091a1906140d1a04080a02060109020f0301050103050601210b03011a060307050f210609070804030206180a081c1103011203050d0e010c0210050702070503070b0d02 76
    0x50b003070780795103070803998030540318030824000001c403044507122a4803000321110742c024a00544240a18070000381000c01c00d019a00340104d04c0e000304070030300d4498024119411174003142c02007801308000383c0041c2c0412482e400740c45003800170b50801600c40581202d9000501c038840c10140c030b41e00401d01c180d024040c8044e002902d1100c1801008250380c03590050711103d41420300961030402082d1040400b0f9548684a050003000c0910355101c13410b0407544c0d5040300e140c1c5c0c00304050400c403440f013035598005024240323200c07101000b59070b1030401c0400c00200030040c00300060001042c04c200010f68041039855004030812072102c40318000f03618840c039142c0550801081d01900107590440814500711000c2007455185091041081c0c10380ca08041e80800e214202d8050f016201d01f03c0042e0080d0b01070072440408113070009100c0601403095094462100c09040075030462103404581040c40e00460760720040a0008180042c50302001c03e0b62280319100d4600e00010200343c2c40121681c1c1d40444403108 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 883939199 1250 883937949 883937963
    0x1090b0603060708150a26120f180402090a0f081e0a02100e03010f05090c0a08150c16060c030608010b010e09090a141f050112060b0301090803010b0405120c030d0c030309 75
    0x603254010689000d1a03450b80201840350a44511041010354101c90600c0200527044c0d040640b4485c407140d0004c004030340d07594419020b1000745003641324025010700034840100c3e5601c40a25200856051503940c949000007a1000d4005603d02500040c030103d0f283d40c10b442c1ca28105e000054100d40820070304040035455420000c203551090060b80207540242c4201c400d640160480750100141107000d4400c0c80d966810807000110b2101a0b402d00d203a004111492881c50b005001401694400d40f003d4221001039a420821186962511501000d026148000c0103c02d80d904000303030041ca8010195441207000d50009030249000b40300c9001800c1d030007003042081154a0318070580b140c08180c0300c4003010016200d45124a5083d018440c100c4508032044642e0702199203400f00038151015034203030503648813440c40d00003482c000c0095000300711001500ea100c50500e0b00700800703186403001c2041e8550000d030500e1620307540072401800c0840c01d03050100790002d1514054015103240d11000d0008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 883940449 1250 883939199 883939229
    0x2091e0c0706060e06010804120e040c08011e051f091a03010315090c05120f0d110c0603010518091204031505070c05070b0a050c0a0501090b0603060708150a 69
    0x264038903801034591607104900074020242c03144004100e40c801124181d0000c1e10b0f003408100410425116400343c08040e142010031040e4120205094407003200047d070014012000401207014a000072801d5007840c42a00401c41d80f03080009030b1415100254015201704041d5822481809a842140240f0030002030590801004040f459190424070054806143c3d840f1718201d00310b6a88a44c0710000e40c4052000c1d503160401d81807203a0400c09110001c1140701f89020a0041c05013000302d591038182503500ea8000c450080e075664240846900028050316043c0b0040c041681c074444c0c0c038880c0040182203d0310980c0e0b48140585003ca020320106005000000e000c020700103445071000380401018403e004036150040c00b00c0702030040701c8001c0c0461b049000c00f4080d8038514402408580b609285c942e040c0310141e5061360500311072000881e980d0b0354804480e0200221101d1540e400030044014100ca481c1c00c10000c2c00701c0754020304520345030b903a8150054050307880c898101d0203003003149005941 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 883941699 1250 883940449 883940461
    0x6052a011d060402040b060403050604030518090907140d0305030a0f110703031a06071a0405010e071205010609050c0a051608031e160c020f1c03050301060806011b02091e 75
    0x50ba0030940e000e9004600301081d41c1c3c0b40d0300b080c4003144c01701ca40c403400070501c540d5651000c0751143c2040e180da040540301d600584030306940f45000302d4012254140075080302481c0141c07000754640c3c00b01d4810f01400034030340348001294202054aa000d0034644000c640450030015000007000e07010344d600340389032010564509240c0d059001c81600f6403440c5980c00d1a00e0f90708100300c801d000e8401e00800c1d0500044401058074808d80070150454402c0d0b0001c101072130300303100660030010b05410180003102000b10b00b13818003800b401000000c0a104804100074146080346c0c0700d881c80f0700c191581c103000d07000800c01070f801d2030350000c035080d6900254500c0d03d0781030660b040203010300c41c00000d64000c00074001203070000e000b541010004888903111824146000c0e0300b4052022200d0b00d100f81d00420400004920000740c1d02d0464240d446a65403d03035030360526201400e1110f01402060401c03281c6c110081950402035580b070007103601120180c1d0181d440030240c284010700c41d11006904030450041c002c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 883942949 1250 883941699 883941703
    0x509060613030c0608010f0311040b01090b0d02220510050c0f07060305090f0c0f130612060b03061308120408090d080a1103030c03061210020f070c06052a011d 70
    0x401e82c1c104c2d6503041e0083e6a00c2d05040204a2240006081200049501c07066442c107035104019640060410f00b202a580b442c5041d02a0480f18030300d0388040d00020384100680c41120020007038410301e00e440381c29504100c00b00300c0740c1d40034100e00070612000140b4030310b021104004a400040038513084808044c1c031000c008020705015203200c0164494880d0900380d540021405008102c00584420010140201040152500480c60341c05030740d500c0f0710103d030f400280c1442c0380b0040e0203840003207440c0394807509051a0040080140442c00c0305000000c0005084604403210055054240c544c980c540b81072802881c40391281c83c55204440700320400400c00b0802c0903211840d265258460a44007a02d4215140c1c07004584005610382c00b0000296140382032a51389080048080450b02400030050301d01c3c0072a130250040220700302000c12070300104050340f04404045c20b540c2c64041d04208031044070075514562242d01e21b08108000051414060007540050b018194460040724204200c070303c456 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 883944199 1250 883942949 883942973
    0x60603030e09041104050a021e030f1f03060504060e0a0b1b0a1425080c06010605070f0f020f0307060512090c01020a0321060e0a0b0f0a050906061303 66
    0x200403944104101c1114a02082e400303204903006280403000d41c948000300801401d000b408684010b60a2025003941800001640c459611401c245503590400316000032000100410080e201d1010ad220314020ba00000042c4044030791044021610307403a24606032000d0441c040c9000100c0c801e044030001401081100715016021251943c054140700520700d48052044c02d107460041480071020721400f0b10603000500c254081c06506501302c1c03017510170264200d030a00d50141c845410100c1d616160600038002940100392905005142c82d069980c1c4a4613690032030405041a981c2c840f081d0250340b80c4030051400362000a041e10812034075001e01034000c1c4c100101c100c92070a0650005041d01c030300000c007540300300e40c140c00800000040e582d044400071240200100d00240308904801905918020240a0400403103024014a080c9a441d0110b4a4482c58144030b440b004000740c01e1519045114020f6810903100d40b50140e4850020034018420003020802080c50014000140140c0000030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 883945449 1250 883944199 883944203
    0x9040507091d1009142d07051b072304062402030c0a030c0605060a26011e020403120e130c0e0d0c09200d0207030c080304060603 57
    0x812103034680500403221480309001e8006080d02800c000c090b034500c500c28141d40118a86200382c581c0351114400826102e44d0310094403040c081d0310a000c40142020410030110030350410800100001e441c40d400c2d0f244000d00107100348640020100003510700301c035002480ca00c1c3c010890300308913038900c0b01c0d01e0443e0401702c91091143c045841c2c450039140900800c000c0390b401c1e100301150022a0b803d0403944071004105034055100401c07814030030040602c40e0843d101d00949801810301114108002a1a0014681e0b03208071100f44050002c0c2501d0310302c1404241855410b0582514424052030042800201c10784444243c45c0740504082c580f44c00131700660f0310808a88145049010058a04000c10b15240d82d2200c2810340f2030780c815407170307901c1858510032910b0111074400030b40300440d135a400c05c404150741d44c0444160030f114002542c0641c241c55160804004040e003580c6041446501407454901e9100f41c0009801c81494414000405d0068228140b01e03031300e04083c5008030040c1401c0c442 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 883946699 1250 883945449 883945451
    0xa051c150f0b0c071a04150f080115120b01030b04052d0f070806040b1f20190501090c090506040609020a0e0d08040f03030801090e01231302060f0904 66
    0x8045008140e08042c0c44510303035108010500c190070a2005502c86224032172400384500e05100005074203072030507140308191140d600c4aa030003900b0740c00d0040804405802201280c1c108010584109500550910925890300701c0050b00c4035180004030003414641c080715502c58101000e0001352040300c50002c15021101864401c0a2440d1603401384092088a280d50000141c00000341114002c030400c0d64041401000091416410000200d800c1c0c9040275191807641048030030003a6940100c010305003050f5141d40306110130348245905035142c12410b0310740c0c2d880e011800880304000007500210542e5601505d00482c0a86071480340c0010b180840d5410302c5982010f60024241115108a0b004240a43d031003c00c2c030090030382030240a13003c81c001100c4106042100040010441c150400510701c00d5a80c80380c1540761001e10ba095800d1092410707403a914140c8032507138a141c00442c040701c001c641070300e07200666904400d2681e010355111001e03400060001700c1c00030030000540108992042250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 883947949 1250 883946699 883946729
    0x3041e050f031501230d0809030c01110c060c010608030a0c0b0115120e0f100213050910062102121603090b0105010c020607060606020f0f030a02030a051c15 69
    0x100740d5100980da038407071040f40c50540180302510444082d0501190941071501c601c1c54020041001e010f0343c810b00382c40110000c194450a40f0342480103009100c824039002e80b134021000c2045403200f880c605c4051041c0c1c1d000403003202e504001c1d0400d800508490040d43d0300c0d50720002000c1c01c003451100b0101c400303240000010032181d406d0802c411030060b0583c0e80c0442100500d403d90010000c041090440744500c0040d04012a410480701c2c0e01a03400e108c000d0f8840c00710908030b42101c03d682c0c00542c401e030b0600c4100504a4a00ba900804480301860810902108140c13204522003c4c2001c0c008041e0002039507149280d01c0c6141940100700000d1a0380d108645640120100e88800c100100940e00844c0108450b41c03040d01c59505081c00203000600e404103030380d00c80b02180c0030f41d8003100c00358010903440c05045409010081818003008040c52600f0040c040c000d45910407480c50b1418801e010810b0480341c4140c424001c1d00300390249041111401d00d040512110102e8400d4140f4661194 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 883949199 1250 883947949 883947979
    0xa03060312260f16020c040c0909061403030702011b080403050a030e0603040f02010e1302130e0601050a02060126030a3b0f040e030d090203010c08090a031103041e05 73
    0x30070943c428140c0e141c0c8081c80d070701c400c1c0482025070000e80819085104284062019503100d214054803200c030ba44964400501d080100c00a8a1341584880c454000100894100c0d44010080b6020f03030741c0c2443d0004035102c3c51000081800707a9500702a003070a0300420003204020b800541d11080e103000b92200c804444100080101030710080714000c0042c0c1c5000e55550065004e091800700c1074138014003d1514014000042d001c0340c03c01c0402142c0c046010400300590001e056240d90821020300c2c0031071504c0c51811003c0c4d50380c2418030490444000700c071041d40d002c003000413541c0c00c9118601c050320390352811540001c1c4a07500c04040000051a488000614541c0855986102d40010507140542c0851034081100074460340314200c0e001078461154031841c1c5001d100402c40c941c1030807030000d0380c102503005140c2143c40540c10001802524001e010070004d000920090302949031401c600343c0050080094194003903a030007003042c2c050003440c1c0302c0240b407408400c10542c0d000f13403003400840b6042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 883950449 1250 883949199 883949267
    0x30403051f0515010c030309050102160f02100f0c0b0c07210e0a181e110d050714120711031b060f0408040501110c06030a020702010809010e060c0a03060312 69
    0x40f0100d40800c1040100000090080d00409a0f2901a800041c240304c030907583c040803c10301070b400311043c40ca1a0700380c40c01c52038504141c03040c41c01540740c000488400c0000c0609911504180502000a0a00001e006d00445030880d520035503c004a44034006501c01001e61407501c49108074003149484502c02d60a05001114008440113295140515005000008010b00c0c806403d02500d19490b01c503040c4000c02d034000c42c1050100c5071349040d038852a400e060800c44402905000400224100740e180d61510b10042c0c40030f588205141d0701090312907070404c1d64011891440c9503680d01010500d441c98444145c214168a074cd140282e9806664859a4004c0601c0c102c84c010a524811b000605c10342d4440c820340c170040355262040710010125100003070701d0741c4c0045454212154000503840308650707102a0064100000800900881c04261030076500c6000051140400746004500748101e1131003500050010360f04814049056070003000002c03c40d803800551683c40c42003000040e0581c0c804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 883951699 1250 883950449 883950481
    0x313050a020a06031d01140c30040b0c070201022a1503090c06090a1401021f0f06060f0207060311070b010e0105120313140120010501060324050909030403051f05 71
    0xe007824001e02d1b076823070800000294119001c8418402a0300c0000100d1020b580200f051440358085d12480900e05490320303011000004142c010404410f005200040c0d80005040c00484908045c117003807901240700b60840c9014101d2a87e5000390762000c0c00809442071401580074101c01400d903a1500c00d050240700d01886105030107600301c01d60b0b140820000300c0540041082040503c15140c54039a401c10040d04150380115000b0210784d039086050104078540728520040890f802c149185101640c0d001e0349415051103004181a1201e07110314008040300c04482184d0792160300615556141c81d00644132a030240151401101c40c10222150440c001040d1881645103184842c5500c0c2000d00700c103180c0282e203810506101048034809142055070300e5000b500c10070040002080d43c980940101074405045049802040071881c03100b1204509507200c0c00c0d80e40c142c031203180548030340c9a854514130075588050400d014180c400d8408203203089513040c00c1f107170049040c03240c1d45502d08100c266490b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 883952949 1250 883951699 883951721
    0x3030807080406291e0604140609030604050601080115061e11010e06011d010b0304110609090109150603020a0516050a0b072d05041221170c0f0313050a020a06031d01 73
    0x6007d10040094124404102d0300d0800003601903410030190401092810a00b40c408031015041440107005581c0b0034450b0740b03103000718441143d91551420380042d1619682c40200c8141200e0349020102c0d6a000300000d0f81414180002005448049011075071546820301074400d1194034550f5200700c4041040156051782c4a80d00c107945141c5440d81c64120222402c9009504640144550700440e501c0a5031103000340404140407c1c0700c640601da480b000006604000141481400040341d032580c02801d84500c00c4885107040d200d1a05820558548010000010000140d00301000341c42a07000b02080903901c19511212020100c4803004000c00610044074030016105100070454100c24600c81c1c0c07105409602444c000003c2502d2050201d0002c0b08c00c0e1000c210700544000b4090140420513920214402850341002d5007100500c1d0944400b034100c104064071b205444042c068180008416143d004143c52110b66454074050301400320000c01040042c00c0106201d030500040c000d01c00740c90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 883954199 1250 883952949 883952959
    0x10b15040807090606171f090608010f110a030b0d060c0509090106050a0c03030c230307170108060f04050721020a05010804150527030306030d0903030807080406291e 73
    0x6d410403984002c1c44801061409506003d4142d042c4030038804501d440900a4164041421420300c0a0542943ea61060000c0c405103014103000d031020801040d20000b5215180c04590f0b001d030729001403000242e10902600d094a400018101c0e41d400074000d01c508030003600c1004503a0390310303101659076004244107180401c100d8013600d00020320a6204408054250502000381d440a84010b800840749450190b400600002445001e54021782a00301e41d5911103010b80c01d80d130504608644581c40a8542001114484d012508214051001f40007602603000c09002005034406a22071640c00c90001741d004da401900085019446065400d10a5030440005d802800005030224000d100007020342d41e0480070b07002a00074043e407004c0255a800e110200443d12411b0010170941071105001c0a00180402c1480410010780c01c2107402c0d0348004507007403900d001e903141d007404070107481c08600f100c038448001100c690b426181c01200e2200160113454281a807440074224184c0b000c501074005502c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 883955449 1250 883954199 883954217
    0x703090e10150516050c030c0a120f03271a190f09051e12010b011202090303042606160207050d05280b0a060e130203010b15040807090606 61
    0x4880c1d903800d0503501030b0b524080745880c54101d00381c0d0740030b200740800b140ca030f0300110035407115440e0800c038200500e00111030842c052880d00710080e80c3c501803600020203562181107104240b5003d541007160403500c283e125080c0e280c0103100c1e1184030095004003560036a81980300009100408156400c400c2c2c00940c1700544100c202e0190b032a100c040c01c5a00420045207004103d6886a8104030201c0011001c5850340c10700c0482040f8001c84000c01a0405a14091182d8030f030f43c2c0d0103140c40300000c1c2c0700100107079684800710109045120303641002008555050400d2003041c00224a1118510700c02e0030396929803544c042415443c280751520780010b0384003d40510251a0402020030903910070700c2200e0340ca904000d280710b05000591a11040c1d80b1401e80e02900b400040d018455200c0c10110301003118034100030300040d0018000d031113007a580700e042c006101103480035840068a403200030101050060f245030b0804090340709010f01c00303a5028103080004c40000714016141500e40743c1d2145011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 883956699 1250 883955449 883955459
    0x130f150219032001020a030f0506030f12071502130810051611011d06010f090507050d0209060c0703050303060f01020703021c170d020a030b0d020d110301020904110703090e10 77
    0x80c0801404050007a88001103d4194030b01c24401050100701544010a0041f0040d80e01c408036280284071901940200c17503074a400a40100f0a842480500001180c60704500e081411060358050001203845200007071821070b0780d03c002c18500403120340e1030480300102c203180b00c0c080a4a006544a6550140c0c0102201c1c440b401880031001100254000294444149130300e034050110280c5c0a0b109908440010700100c0b205420403000780c08201000d02c5203041402c0d0041241c07040c0421201010384c04680c505e0360f40d40f06012111440203c400f2a40c8042d00d80c03c04540701d0b07005683e102e20030142c000e00000e03554004240107003103c0d0028203640224070086022407000310480000c49001010700c4038140d504044801504044c0111100141c42d01c1000c44003504070f40c000b0746584e1103060103440030801039072003584291030b00d0b501c8401c10503c2c221180100b40a070084200da546d10904204089100e01c0380403014021260196451001031940c071801c5828104068442c01d005084142040c0b003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 883957949 1250 883956699 883956707
    0x20d06181a100201090804090b0a0602030c0c0618030a03030c030509011415180c03070f140306010e06040f0e040c050103180803040203070509010b0711090106051c02130f15021903 79
    0x600d0490ba00003c03c290000d40d0f5107210544c4150000c807200c5540f014018524240303025010042c0c0003d00081d031030220025915503aa52241e00407520540b0009070010100100600380c4829082c0501192840c0e0b9030380c03801038098044840f040300003d190600040684205000308003101080d011300c1e0700e860311080103001014462a00180e0000010744d0010110001c0b8444070384201e5444d010551207051004008020a803030200010801400c251101c00c821030100440703803c0f40302400d0041d010701c240380200c2c0c15801240c0c0031414205549a00284611601c29000c2c4554882c00000b2041a101d0b00150100c603954980074180c1810700d0342c17240c0000c14503c019500f2034001804c44901070b5450000801c1000c2c00d1b0000e0304d013043c021a11004100141d480715220400440e104811503041481c001d20070300604c0500d55201906084501c2002d0090b4100c8540c04180888100041e40307400b00c00c0d113000d00d18484c0d18400c04244000404d91803010410319800010188003080c01c00c0c1c1510708407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 883959199 1250 883957949 883957969
    0x13151e050403021e12150a02030f161707020109060e0708060c160b0a090201020f0a020102120a030f06091407030506012c030109200307050a061110020d06181a 70
    0xb480d5451408032103d295641c21020400030860a001001100f5014100e010721b030a016145007190350050003809000036210058030f03884040c1505822190418031400c840d0640818444948405050103201c001541908058085070007450b00348400000e068900c0c2c1c0d104c507541301c1c6070003541100c00422482070b401401052182070000140c01807005580b104c0d550b44400342c1d200320070903a91341405011035030180428a6446020405040b81c409203800103500e540307041c64140000c1d20001903da003514040c2d442001c1c802c50301e040030080f158031640d802d030041c0400c800c040c410b417000700006051503100c1e001d081d208000c1030752781450040051035072601018004800a00e030040070320b1483d0860b00c0902c1442d103481e004e0b052514403564600d680040b5454004e00c918000d400c02007007030015443d00b907802003c40f4030503c1e045c442c00d400300c44401d090500c1a40c1255000e40002100c2000701090b80010f410fa40c812035035640d44001d8054108221b840103420350500461501c0781304010300d4034000b90 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 883960449 1250 883959199 883959229
    0x909020109080105010b0a2601032909031210141c060207030e040605030106030b0f040c0f080f07060c02030c010e0102030d0f020409050105040207050316030513151e05040302 77
    0x1d01003a5450781d500d142900d409800004440340d0210340c806001d940015400d48030401c81904070703031984d405402c0700ca542c28140005400c1200040c03060300c400c01d080c40126182c50208488014605000641e0340c0c83e80d012185002d110143c1e00d0100381e9a901c044d0400d02110280b8620b04503084607001488a141c070501c80c400441c0386055200804101680010654584281e440a1419014100704400c0380e4031500114001d81c9031880038000543c03001c0d2280c0d0020800980201c03ea83c1e84d01d00041100d02c203402048464801e105c0001d01e20030005810060401340d80d042c1e80c0c505454600c226020b07005a08003a40c980d010300b000c03500e25400707908403171034240041c419285420304001d03c0e00183e5104505000c2d40560024041050321114490300340503000c221030a502d415601e0f162260f030380c020b0925042408800194803000c05000d00126003845140d0141c4121203135803041c0c102d99030011005480042a1440d1200c407444030040380c0210507201c20348940f8141401c54081c020100d00710000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 883961699 1250 883960449 883960457
    0x2120c092a0a0807120612060203040c03052a010f0e04020732010e03070c0515190c05012a030b150c0601051309080711011b030201052a0409090201 65
    0x316049010361200a00c0c1e24040b035120f200746802c003208000c106400d2141500c0026180800c2440b0b01d6000030340c0540703119000100540c898803541041c000d072125030b41c070081040c40380342e0006151804002078000304a17032160b199a1642c089100640d11406140c2444000030040c0780c0e0340d11289002c1c3d024000b264010320308501808610101d0f040e80c81207080d860703101c00d900000c0301c03d07030490709024030419040a9006581040798541d5245060403581c0a440d01c0f0365500003001042013580410380d4095084103030b0f4154034840429014000f0604e1002c140c80f41c1d402d00004a101a0309001511011205c22840c0c0e200d0b00c0ac45d110450080c07100c06285540f08980007a602046114100548000114003010308034a5261008000389a60304070b460300c0d030b000c0c100300003040880c0800003903d244031340180d1111700c442001001202c242885d01100300a25420024402c18191305600003071250f00307800c070540c2c4c030050300001000d00d900001c0410300e100c0c0004c000600c070120041e08030b0072140c0c1c0706040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 883962949 1250 883961699 883961761
    0x1c0f15270903031418120c03030106030b03030c011503120509101817030c060f13060902040b061207090b0f09120309061b06010b0f09040504140f010902120c09 70
    0x1540b15500c1c5000d894000e1744203c00d2610060070101401040724144140240c0c510f4103101e00b9540741c40c0d000512809092507502c158080039610240110740c1548480c02c0201310400354812400b0b6072061502007a150386164200071403840e030155044030164200203000c42010503080c60308503180420b688010f140010140000500c556468070445001d00a98001e117032a8036004140518240f0000c0000385109002d1090082e501c4c4046501555107400c2a03021a030b49010b80007007006030040c6500c940c3c02c00d0b800140c00b407a000b40d840440e40610b95556070100010341c0c13614040040c5c01000c40380c80c1207140c2000352224a00d0700715010301c44090680d0949041104940018142d500484040310b1024514905d40c4050001884428003402d911b09100c1d0800180010b00c8901780078414405004694810100e0103020f800d000204c4a1240790003198000d418188800c2d0190811190407405110a01d041c604400008a0441d6000d6405401c80b00a5510000e44440d48d048003105290b45080d020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 883964199 1250 883962949 883962971
    0x9170705060f060a050d080c150405030901020708070515031312050c010b06210a0608010f150b0c030f180d0f23121c0f1527090303 58
    0x504222405000a8211850469000300760608010030b42d03071040a034140103014035980c4c00522a00542c201c407400ea01c81201c07824031450080c0728481d070200c0703a00003000c10040040000081004509c20f03401c0c1c46009031358a003103664601050252035440720031f13080f50310f000b40350400146a00c0f010b000440091034000d601c0b031072030000c5410700c40700c000360f00003c8a18080d242406541180c81003610b0a0345041e01e000c42070300c20556600d04003900e054018000c103080018541118016040b02c0000b00082c80542c04400000c108000f0410000007143d440002e013103c641065a00709050400a507203403007140007140076182d00c51041450800032071030030b0280b140c588084000c45540300ba01c00001c00b40c0c850078101c2002c1c24501060b1411600810750540c2268041040301c003203054103580325110104091080801c0351074440b400c4000b4900080b0401003003441d08040100380c1035518402000d5241e04015802d07a0b2041d00d404052030f0014090a4540066800012254005c4c038001070000001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 883965449 1250 883964199 883964243
    0x1122051003021306020703020102190317010f0603060e150d03120f02120a020a0c0b181507180803040e0a0209040e011a01180b130e13110909060a09 65
    0x146030034000207a000c601181480e03204403444010b46840e00061401038a1940000c0d6034120f00c4440e040300ca45075108000406024003030340d00803171640c1c60200c0403560712407140c40000c8440b0703c603090029087c03100014240031140007450203580340c40000c1c0d81c0068900d0502c29036080c0500210204000034100c6d0346c81007054030400d0945504034101690b00d5055004214070f40401518144500f031040100c50030b0303a41c02c400d004200650107444a10f00f50790307400d01042200903600c12141203024800d5001d001d0071042814034481c418a48640c2034103125204910142462030244551075441004188081c280001c07540340c3c000400f18001d46864250004501654840300366070b540c070b03034446062940c40036a0040801009001380b030300460f20b07455024203010001c042e100d0010100e00029070000d8844940c903061300a0302e0410450011410006030118203001e04040076101461050801d0120789058071215008456840003856039446201901c0020f15180c001114405007052100540c8100c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 883966699 1250 883965449 883965469
    0x3090512010204030209060114030610030e12130e0601050304030e040609110705100516120b04060312020616120507170106030b010e030c0607080c0703020d0c03060e01112205 77
    0x403180c00562128550310610510200c06000541842aa0a0351a03100368090040c2c940c441401c0b6190824100641c0040c0d008005184504801d80508031081c000c03e002c5000816400c840c8400c1d01031543e58640c084e6518800a44030203001903020800304003c24400c0060b08143c0c00010320002d02c8903a140d8a060031549040035500c40e00102090003028000144030300700249012007828042440d09131004c12411101070208804d12107418102c0c000010305a0102060f010044c00c06c020407500e03810540717140e07004000058010b100785000211030b50707082d0501c0091090b640e15031003201b510380800e15000d010006c0105c401c12000d400c41c0e1041000751408107009209603140002c54801c14000140383d80018943e05000b94040240b0402d25160718017116195034101c04100c1e1181d0140716440d060242c0b41d03102a61146060008030305000c00c00705080c084030701c554810405005040c820f40d090b41c1d510140b440c2c10030024010010f1a050081c010400b000d265000e4010701500d880000f07a040d48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 883967949 1250 883966699 883966729
    0x1050a170f0702061f0b0f0d0911032e0c0e0301090b0615190c0c09051e130b1b040e0c0903010605311d0a0b01230904030905 55
    0x80c400910842c69018000180c2148004000c2c1000c030b402a00f50100e40105403243c2c3d5404000010701120030301c007c03415260900320030201030004960a0508201c04500360300198071901a488801d0640ea421403044080d01d21906103131000528000c00c400020b08040352140d051208503600c003055076070700303204907001940301c0c0703480c0009800c2041c00e02c40c03248501e00c82840310200411403200000c0e0440041c462015031883d107014142610b290104440b2490391100c41c0042c1030505105501112003001080341140d8440c030043c0e0380c0d520982e0101619240805000091103402103850f0302d0000403c0e1410200511085241c140e803001c1d141480d2600300c40180107004042684441032078280204401031000f00c403502201c07182c03c00c0048440c20b2207414a10254807a180340701190034150420310010390801c40706a5106c1c01040070343e803145610a021070702031071880300101d107400c3d4981d040d180d019070030310501071102c1c01c000a00c40d0761070010300182d007400460350000a00740d84680041950714 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 883969199 1250 883967949 883967971
    0x10614220203041a0718121a09031606090516120605090111070501050103021c12030e160b0304060b030d020a030503060a17100e030909060d11091e0a020f0901050a17 73
    0xe13805002d026411501030300008030450380780d06030902180408c000c1c2c19040940040781c2010b51555213060786140308800304948000c1c84120400148840e0b944040c0003a030140003a189603c00720848a041003490b8000c46591414240713040d004079100354405030340300200c0c1000242c004d0b6840c007442e0144c0c00c0380c030042780d0984d150b400600460401d071a100c0029086c074840b47d04101000c1c0e46950101594803c00020541c5c0c500e40c10b200210b040040340b031410802c081e140052a110096144540c0c000c0b41d042e5882030030825201010b050000d202c4246440030f901505000c1040c2d1350403290707540041c180541c0040d000201103a00070b0301c4a0046268200310000b01007000200017103505403204825440c03400c2d0020b000050490301c0c1c0d400a03e50144048414245040241c40e0140f1180150b115a580250ba8102005118500800b036035a070301000c1800204295a10100101079100360314000d0005602402520203e50065025000c080c0550924918083c0e5240002aa00d04108e541c0145c013 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 883970449 1250 883969199 883969217
    0x9150c09011d01080f340f0e060a14040b040b0408150112140102070b0f0105120106030c05040504210e0406090e06041709030609010614220203041a07 66
    0x15a080b0100755104603640c0304018044003903000191160b02d004215009004505001481801603101600c8400040101ea0030340d100840040614241041c024a408208422000c6100e980140c40c41c5100d440001c042c0c0b460700d00b07035200031036594110000500300380405100118045510b5400740011300002c141480c0c859103007000d2249070065808051b0061103041c4010300c40e00d4000d60403401180d0300113000104c00380c2034000c20f60080c840d0f00c03805854010f00c2024002c40c0300c1a20b00d524120b0708221141004510703020078081c200c40075444001c264003d060020082420960029503105001d404081e207040044000d01000d110602035200000b1218032000c0b85614042c032440c0080d0a02107010003850340703404505503503a003028202603c03150108140c0013518041608540c00020b002d03003a0f844500b4100705440c081c0030180128000240800c4c800741387c500b080319054280c003042c001d09004002001b00b004000b54006807050b2001c0901449a0060b8480006c07028000c4240e40d680c03c0301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 883971699 1250 883970449 883970467
    0xf02130e091e0a03030209010c05160509060307080303011211030d0302040f090504050c19051206101401021c0c0b04240203010501121a03070f060210110a0809150c 72
    0x107102d03441c5522040c80d001440c2106240000041243c50789070301d801c006030780e212490f006803070059480700003c1042c407401480703040701c0320b9642da4802103072403d6820540d50b0300d80070205901c488240c000c59200340d2043c4010001d030040102c2001086001d90303880100e4050001c0806d0070041a05451408281c0000f02040041200308400004003500380b000c0201e03080942d0b4680d1111101000540304040851210301100c40c019090030040a0040c040042c0c2c01540c40d2481d00ea01040f9600d0488111110000954814914a401e84944164080c0000900c600c000c001c0300e01c911450081008040c12480000401500c115030085005044548208001442e6001e0200427412075503072072230050004002c0340e6001040d00b400126090000b04440890480a038203520041d03084542c0352154407030010301c00c0301e14401c80e0295105642a5030440190f002d003807060300c00103800c820b0710500801c880d01500d445501d05030703005102c80c0f003a6213a005d2841d126028040c03040da5804c0414200080e090a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 883972949 1250 883971699 883971703
    0xc070503120906070c1a071e0905030f010204060f080a020c0102040e0115230708130e07022803050d0f0903020d02010c0903080909070219230c090a0f02130e09 70
    0x1a0140f02c078544404090307842e1b5151400d200408010096030501c860124008a014251400f194070554100c90f000e2069094000c040b0001481454000e0080c008400c100080c10b0003110203444c01070b1a5400210b000d4101140c0e80107000384405c0c01306a080c031441200c540b081c0014002400025000c603020350400440c044000081d801d10b4003070102d00c0500d0040300c80c4140380321040c05060803581c0d40b80c444d903040501c480d01c00c5405800c5090080103022810101444640d405040b05900b10358135103440c10175294500440d2446404040d90300004100064481d00c010328900e85414000724481d400c42c074002050794810310045016030171586040000d158244a04100440700e031a0542c1e8503451078a54007104c0c89460101800b450080380001d0300707140200014152070a480c60141d4658459007003003240951015660301e00b19504c01d00d03005031920005441480c40d0300040540503251900b001000003464050052009603400307102002144440201c1c0070700a0100000084d094070304681c0c40c038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 883974199 1250 883972949 883972951
    0xa120807050d1e0305040c0504020d060909080703091215180605042105090d020d060605060a0801081e0d0804060e030c070e0109180308060315180724080c070503120906 74
    0x81c20146005d0810000c076a40880003003c495041e40c0050350341400b111a000940002c3d00540d441c0b07410080400100061400200b0010f40030340e498080013511414500c500b1042041e01800c41541d004000001003c0c60780700c112040307010705143c8241c1c3c0aa64582c4240e4100300c4040c0e03000c4241d005000091032290041e05440a041d2615034508454400003a952105002c0c000e400b4500300e605802c1002110f6000c00d01401e401000c0070b8030395043c41402465103100740100750160003050003007032443d0740c000c4c205119101034402500d554004c207442103d6000008100791142c5071501a04101c03454203200401c05461000080c4c0800c43c2800c41541203418180d02c0541c005151000900304031481c00052002141e2502c0c0002e09900d440b000245420380400b0003460120440050080c0b12045400c03440045407814242c4441a1307540360544c480d80710b5088190075515080044484040c070900b51203a01585c000355050030101c0588505103907401820400c6101050788041c4009020100151 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 883975449 1250 883974199 883974257
    0x90303020a20120702030a1704090b06070807022404061805031209010c030302040902030c0436180803040b07180f2102121c09050a120807050d 63
    0x86440c002040a240fa03031000d4400720318281100218a200071503901380102825581c200c2590018404070441110542e400307032180c0d207115450803500801034200b00b0269030541c1e411903400c504154083d02030120035011108401c20018039403001d903020b90031103c05007005d080265280103401000f10651005c90310103403c103e10071740c4511607064a20340b1440440f0380000303082c0382140200d80945001d03030183c007035504015032440c004010454207041c2c4078007a00c2103c19840002258100d5104070044250082031281000035004e180410806050b0700310500c1c0a030b404200c880c11580300d8840001540040c3d4040312031a110a0521900b81e6002ca4000b04400e80b041006014514048612690301c20a01c149000c01e80c1d6071a000d9506608101445452500a0000c0d500b140c8520b000030b031204511498000546100e24258111900c0343c00b4038016a00c010f042c04003401c1c24040c00c1c4040d4540504112000398040005200160080c4180e80322030901d43c54124090603000c044800d800000150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883976699 1250 883975449 883975487
    0x291309170a3e0106050607110315070807031d0c1507020901120c050102071413180f0b0106181a2203060506090403050316050d020c030d0c03020a0f140904090303020a 73
    0x51185da40c620302141c2501d07622096081100c1003000c08242003141808a16a465400d942009101c5401030021403203254035540400144110000c001d0880c00302c18241c42c543d5205803040784190070302c0f119108224190175129400c12034141c0c0058465003090300100300d0503191020300b4041042d41036982010b428240090996241422120521100011089489100082e0307900030b610740242d00400d0784070389000010002c00ca00703060405c542102c61408a8800b00d10000000f0300502c202010b07a0914019a41c1040076868610f0382d2076210380110b401c05203d502008259100340d44100c2d62100f40b9901c0d19451071403032460514a044910040106000312280000c1200181e0300c881182e500a50340c441c10241c000707064000315414041c00b6100301e00300344001001500c1d10000806007800381c44c1e07103005010748030034040100c0507806441203160219a00d00100d20206014000c0b0000c01840382103064244040341d00081c0645413a040b0540109500050380518240c1c0050744a004da140840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 883977949 1250 883976699 883976711
    0x7120f0804061109122b090b03091501080f06070905090c1803030315040b0a080d0f020a120c060506042d291309170a3e01 54
    0x805490380354001c0c0300030010355a0710015090065440b041d11240038000e0804c00e01d03000c0745200c45039038101640710500a201d40c03080e84e24010320002e0840505101968031409000c1c034018103250349400c0039203018900c3c0072701c0304841c0c00b41c6105003099000789123a03001000760301e2404a81e00c0c100100a003176102049038061050215468034600b07990405801100b09607a8042141c0d20f41c21946031b040340ca0350600001050044803402a00720303d04c1080c0880701000301989400030170000b88120f2203001100c1d0841d026140306240507842c0098030001a0040c0c4202840983c1c6036501f1100340010440402e182d00d5030358040c40840d1140c4c1d680504203031000c00c1a07421011511038001031461039540400d503243c0c0b20f990b0269981e04441002c003d484080d0445040c007500c8402090107030701509000700307800c211108642c00c2c98003a100046400c5000c40f14480d04107901000b881d800700c100401406444040c00083d0408080d4440382d00b6a024082c0c00d04030130311154081c80001064101c0c041e681050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 883979199 1250 883977949 883977977
    0x150304031101180f1a0a050105030c04020304110d1b090c080702010209010c02060a02071a1917010e04020a080f0c040b0a03110d060b0a060305070206181e070b040603020712 76
    0x801010955030b005580301110414070701d001c40600380e165200d00c0d1061400340034000c903aa210f0700b01f5410307208100c00380c515290b00da0301030100324082101d02410360b00080403c0706041c1031a6840a00c528012440182410210f41c0c80c08144030140e48044070075136492000d034240c16840110103801587d01c0c03009510340064040024200100640080c1c452200000ca0101c0c4c10300801c04039004007035408004400c1c4071454948001d940124800d5601e004810032085140391052410440b4081c6150200d001d076401c1c802c0304d1031030010051040780c02854800010031a100c042005a100f0306500000348504100e0700140815110b03080b143c2d9015200590f418000a540c607104480308d86404e46d01007034400010700304200a4410104903136040030740b4140220312075505400c0503110340569004c5034031a8540e0780361804000807902c6a0503458005000e9840325a0003060700c206000134136421550090b40f209040c40b026400ba0b40880046640022000c040110214040501c40d94500340209484851 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 883980449 1250 883979199 883979231
    0x1005010f030b0612030c070609180c05030f0615070f11011b0303020c072606070518040906110406090501020705180610030f0510140f060a030c050405150304031101 72
    0x2400d09441a00d10382c0140180c0441001030795088014042107414480d0342d1000275120076100e014482c1000003410a03815941c1250040c0d01403400e113a80e4aa00e503a0702c400320440d41d000040d0445620103400752024001c110307400040d0090300d02a88034440401160302d400079030b09056410040c14401300084c00d80000300c90b204803981c4907405003000759440391904180760038100d03d1780020f803001c00c030002901c40d00e0101040c8259460b49800c111425a01d925609440368001c0c001440185a400300380c2103843c0c146600940480c61140300b01103400c0920088151180d08140c00460014a14003410080c560b41040b940004080560b01070030492070300711046105138002041940200b801c400d0f0a02c8840c42070344041e00b04000b60000704410b003029814020301002c2885441d0500208001a44d100c2c40e046c03846211414000b04014940300d40620250091315000e0190b10a2003001d020000c0e894607040c104020080a2000c00d40c0e417440c0601e4040d021100070340c80e9805d160324200c8202051110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 883981699 1250 883980449 883980451
    0x1605190827030a0c1a010b0304120203030105060906160204050f150d15050c0f03041101091d060f010e06040305032a0c150712021b0d0201020c090a0b060a021005010f030b 75
    0x507860518244c814504100c030f0380319400394120402c0c8a440000203090036041d00610701aa101e0640c1820844504400f2030740d0740402e00030b141c0e00403410804501c40340b900500600d61404101c1c2152600b0459400044c1152421120880451400e0082100e1120100c4a050f214241181e00300030725089915072104a171040100c2001d0581c0d100046161110198103031001d4400a56807156a4a45447d00300c213a005c49220301400328000c1c090100780130300c0403210114141008502150503039600c04c01c105040c1e01e682c030002d05010181340b40e1110303901c034107000780040c6015600940c1d07265400b50020300c214044071281d480910011160070301c445000725842c0c00c030000440d81604400b1020304410050310821100a240c2c1c041c04200c41a04d9402140c56541000441640400814010300b805440301140344c000340140c100510781c107228a024070100c5d0f080b8140708800214840c420001c101650322034603503500582e115403a819002189030003014050281004159070a600e150b0750034014442c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 883982949 1250 883981699 883981717
    0x70e091303091208190504091821090918110a0e0118020d0f090201090602160e10170a14070b03070804140105070905190e160519082703 60
    0x90503a0075070044c40440c5041d034200b00c044400c40700030441e143c800174003240e00c40e100d4428021308248008054416000c4c00c50030b2250800c1e0007442e0f00e50303c0c40b0440030f41101007074a0014407903020300c01b0805803440d03c600d95501019510100a051303440c01c110842c0720350a41704600c1075010000078061980880b4180e03045400180ba03a002da400c800c0c021202038040d20000300440d40c0b4121008107080c040b50046110b0394000c1e29102d440c981c1741c4034200d8a03400782744509211107001210810062280340d003032a0b0311000004400c1482501d80f1010341403c2529035420312254032030148903080c0020000440714600c800c0008182c0c96151a0310700005000040040090003800e20000d024403801c0b240c045401380f40c0100800041ca0030f9640608024014010640141e20200d01401c010039060905026689004c8c03444210340c2c0c0c0c5a10700c034481e8002007900f1013002418004900380b81851444142101556141c00720329150800d403903540e6800960140791884110003400300444804404c031181c10f5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 883984199 1250 883982949 883982969
    0x20a03150627030b0a02040617040203030301150203040f0303090510020730050d030e0c0f0f06030603101a01110109021e06250b0906040b071d0405070e09130309 71
    0x7007404402c005080c60703500180102604008100c0040d041d64002e1061310b00701d0b202c0550400001c16100850b00040390000d402d81c2c402c10045c0541c0c0301411241034420141d10490303142c01d80701d21084045504942c4102d0109202a209000038034001c46c404100d01c240d8401016420301c0d00707100c00c1c41c4040a103c1501881e0210018421300b041c50560001d940e170304041120a002900788009004040017074214801e40038560001419181015140e851520000c1600c004a8801c00811801c1e62001d8080c40d458420f414003403050f0882c501503080406010600c014031070544000151141c850340000300c111340d03d00300303d050040e17480140b000400d00986005c1075501821a0101f0900c1c40744143c80e13a02034010705100340720001604120740c61240300344805056a19900c030754555980c42a0740041c10f2582078070000d15420f100d031000c68202240840000001c80b5001c0100e000c69106661031b20004020307e0319201903040c02c2d0541604501880007039114003c4030b443c010002922401800246 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 883985449 1250 883984199 883984247
    0xc07031e02060a0207090501091a12010b090103030201050708010911120c090d0605010f08061018020d0501031119140402070206040815041b0b25080409020a031506 72
    0x4106180d0000c289a028142c1c56550740c0c1003502079070781c415510622070341c5800c2000206500e5180e00901010024902c1c0101c0003107420402c1280030204011032205565036100422215515461418025406900001520b0030a110300500700071050b0060340300740f030924140d581420309980480303a032894991854025501c03440a02c1c203881c0b0809880d00d0344059585050300078130961794002030413a944554810202c80c0e03620490b42d02c400781140c4a9543c3c0d01d483d0000c010f0074952480c10189103108644c01441d1240c80d00300402215400c1c0c0040e80c8006000c3c01740c0b80c2e0741c2404d055110100c250701030400070703852400b40e58000e00880c0c0d01503d8050346d00401d681c0110344900b801e89004d01003580503202d101010311103e249248040302c3c161a0355062020340f5041040c5508100103840310f0366045850864030070110b076070102c40f07212200c02c04050b6500140200e042007004d400030303140c0b070080548d4400c080d1400070161800c10244941d11504040e0400a594110b00d130300303461030f0504403a1142 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 883986699 1250 883985449 883985483
    0x91e03020d141b0f150301210c0b07031101092102103b0601050402090d06050711072c1b0c0312130c0e1005130501030b0c0c0703 57
    0x8030244600c0b00d01d140d115449071440345038202180e004503036074140c54005144103c01c0410500c450104800f2504203001c0005228154020304e241d180104008580d030b0360b48800e6590910740d480694001c0316034a40c04904007042641c00a0302d6505009080d000380210710b0342c1e4130303203c0c1c1190250b82482c4080c15804078010a0314001c0c00740c00e098500082c03041082c0107004020241805105400701d2140722040a00c0000b20707080040d40814001220061400340c0c2002c090000952000a01650285214202c000090854002c0900c180e4944d0b55440d88180103d4800b8540049500300c084003103050002d1601c5900300d41300d840c060321611810180c1030f8036a0614104101d01105440b46808400258401000400801481001e14440d40b043c141d640f4512906844070344820001c01c0a4422201000001c9400d40703007680095200a14030212541d4400141041143d0b010081c060380e100d00040091014046200391300a00401a0320710340700c26400000e455489030b0000500c1c00145071110380f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 883987949 1250 883986699 883986713
    0x218040209121c020705060403031205040819020d0e120c1011070609030515070219031b0b0f0105101e02010605090711010f0c0903020f0f060712091e03020d 69
    0xc1400d4200507112080b0b41c0c0f01503540040360844640d005807281520004050400504690440342c251784c500595840e411a040c01a160180068402d07107400c0c0451208266030300364207281c8171266001403a4511400e03502070701c0080d0741850140304001c00e6000440103000172138580401c000c12125240c11011b140002c0c0c56013042103104507142c0c414002c01090581e005003803242581c0c01001142c0b90320032070030f4100c00010fa0459844005030010405c040501c0c0700500750700b20041c07082c28040d5400003c646500405101d140f0261081e80742d1406200700181c580003c0c1d4003403d004c2c0da40c80051040003401030a05080c040c1c01310603100c0c00183c1d4100c02c901c00c3d0712500107800d0080410345941042c40005103030030404404141103510f8040107841d054214826504a1107940c0c075200c8a143c9107408014a044040841c5508040415040051590b60b240200050f85c856070303c48100c0c50060f84000c2c250318403504138169811401c02c0e9a04110304da1603101c1c007200da040710b4144a8034003515000f8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 883989199 1250 883987949 883987969
    0x51008100902161109040c0b03072c130204030c03081602030102071424060d03050904051303091418090109060e0705030120070b07141602090a0218040209 68
    0x220034400320703443c00e6000c0300c60205015180212840c0c1e02103119082000030425040d50020000400d44070300708902845940a180d200c0450f081100c609000c01542090500440a045024819070007904681c0c2c42c01c50850294014009030460030306045503111010040c6074000500241c4000c2041d0341c054038011401014103901600954450606190401ca01c04808071401241c1c051440e051289503410010326052a485510400341503c035942403024405140b0820303420400304001c0c420107911540522070241400307403039500d285585130400030300c3c06070b098000010303989240782044402c0c2d4801c0d040840c4030040c240150f0307254032940b100a004116500000300000e003080f54007400c0900c04030720401103035000e42c000c1c090440002000c032080044101c59888003e01803083d80041901d4108517036124030f080c1000440e003240b4101d030f00442c1e04460f0b2103442071150301c4004811030424241031908401610020360a060102d00c00345c22061000c1c1c4224004ca44c0801d0180b01c90303071002d41d21 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 883990449 1250 883989199 883989209
    0xf0f1b1b15051f031b05030619050a0902031504050f072d0824070f05030f041a0a051504050114042d0209030d0507050d0e0a0905070201021206010905100810 69
    0x90b000743d070303684ca041c0d004aa4090810501c010100b0750000d6a0f00340411400c1c81013042d91700d0881e0a40d03048c511600188400b07000c40c0c030000c0c0d803440c0701b00058908012030410080614611103d51805d40751580c07422042c00c100e0307502c035000040308014405291035007204408020141014039441e64640c041ca0010552101d8103070310440e0000701c0310300c0c03000c0e071f440d000d8004602400980e5070707a581040d80c8404242802c1d00014104000103078115820101d00303500030384910300182e0f800105900c4003002480c16191549200c1c0c2c0e807420302205114103c00c41d41140c4042e00d042c45030351702d000c12690b41000842c03000c90043d41c0f030307004d01d4004c0e000000c00c40d541160006600c0038801d28003810380000790030540071180a48174809c40412094020307030a849070306a201c0018104101011001c44003100d0040855402c0000b1090104400d1400c0c01624810308140d40016199040b0001c0300e9000c4101030100340c140302082e40e0034170403502c60040d44681c41e603013810701100c5500e41041f4400102c8140d442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 883991699 1250 883990449 883990501
    0x703091a07121b0f1803020f030309060a05030a0b100804060c020c0909070302040b06091c03020f0d0e01020d140f0f07150b01080f0c07060f0f1b1b1505 67
    0x20b04188401c010340340c41e145515503900200d1500544d010b59192018a07216000c00201980410051901c8102c1e940f08a00c0501664108400039000c90407a41100c0c0c0c3d118081a808020400f9410103032246000056080310341941039a04007002914039100035102821541e150380060503164000c11410420b5031029009041c1450851601d648400303042c0802c81c0b240341002d40c08001890b00c002a5151054000e20305542446229540c040d040b0070341d6400c5055004052081501d8201405000b0201d412601d9803407450000400090403e0032203d59174040c0704d070091041055031141b0080d40c10444030502050703511401756200d130585004000b80141081c0303003125454607002c103d402c09060381000381c81d08080d6490b0040c000d1040ca03003c86028003040c034144141000310300c454009140100c16032600080302400c940c0c1c2d110035590107040c6041100204501c030140c1da1303030000940b400d4400310f15030038082942c1d60341c07001c3e2002c0050170001c50841c0c0350800306a60300b04200080700d90b241e4400d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 883992805 1106 883991699 883991711
    0xf21031a0103020a0c0f06050a14040b0601111e16080a03170a061d07020d0e0108060f010905061206100f020c0907030e120409050703091a0712 63
    0x1640c0300405c003032000300f900030400585203030302c207a0700078940406c1616141329501c2c1528000340d89420340d4100c00e010000400c0c19204141c4d080803007483c1c0303900361621403076005143c0308400c003280d80b0032054880800e070f0741100002c0b48490b0300900e85007030280581d20481c258455440b160b001c0c0c00308a0f24130641149402c1034850313942c0201d070003500040060316071000303400624000381040c0d40d40c0a140709000c0c1154040186c4403800d851803814982c40c10120000801801c0040c0180d4041d15003101d07010403a0f070207201d80c08041c4c40040c00c0703181ca80c1003248540496001c2030b0361090003810604103c1d000c0521550981099803041e030001d00c004550711080c482c1d4400300910340400c040c0c1c1c0f00442e11041405200000e84641e02d00f034450f80f900d0030320001d84221600034040506040c03800404a0004001c01c00500811031100c400c00340e5642c07032050903122880d0103204885411b1400d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 883812949 883992805 := by
  have h0 := BRFrame.cov_init 883812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 883812949 ≤ n) (h2 : n < 883992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
