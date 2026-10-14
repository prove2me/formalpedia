-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:04.510713+00:00
-- url     : https://prove2.me/submissions/2a566f6c-e60e-411a-bbec-09aede03ad6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 365647482 ≤ n < 365827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 365648732 1250 365647482 365647489
    0x1917040b0d0c110a0507080f0604120302030c132d051008060315160f051905070c03060203070302090a09051519080105040b010618210602160f0b010b03060f060306 72
    0x901445402440c0329100210083c4117000c500e032412584104200c070103107201a00c03503640351b540407a8050b0041e0035880e8294440b5000342c0040d54040d2002403a1840c0001d80503064400344031541110a4005420052680090100c1031642108201c02045d103035071803a00000910b4040240d031418200706c241404101c054504001d240b4011482d0401018a071504100390010140c1e0501440c0c009440f089201503200c0c014800c8886100d0100c8841500035070181066505520600c4100c0d07210074401030001c0802d0307003403001e1070107601103640c0580c2e01c82842c0b080100e214099000030480358034080901c43c5403010711603e120544005d40701e003e100000c000c000c0140790010f0340501c3c1b15509020400c410020304040107810313944a82c0300d2080d003201d107000006190429000340b02c0145411101aa100c52112103145200c6103d0742c40940b400c05188011000302b00b9002c0f04807009501080340f40c04000c0c00c09a8503000d001c2841d6064103510307004000624200345100300728050400000030402940703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 365649982 1250 365648732 365648747
    0xe030c012102032a13050d0302100608060a0b0612010e130506091c0804030806013606090509041106030618151f1e111917040b0d0c 58
    0x10403500454591608114180280340900b0807110901c01c5404c1540035100c07018161115004030070640042a8100010f204005d504903400383d0648c82031143c4000300400c14020380001e08881c00140846003041c0303501000b07485094105a2044905100c403000c2c03898600e100a0444801203508146a02c85800c0d5a000ca030f8420b4029000d0302440082152440c03000a030080c0c0c4803c869200307280204c1840048401c41c009039001400103800d44003042840d0b2050000c07d0303803885000d045075080b0544129805554007490020a49400440c2d02004120340201100008201c20b82d000751880c60256034412070b101070740701502e20450340030021541c10307280d08001c410440382c0300e0b40d41c04050403c01350000305109213443d0980b04220980c810000d024600c080c0310a82c003281e4070f5000b81040d10740031002a14003d070100c4810410940304207002e80c2020450040d00050b0090340d240d50700103505102c940441c54507205044c1040402040080c0c0d20110115941800d00d0354001a40441d4030070700b1039088 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 365651232 1250 365649982 365650037
    0xc1c0803060f1203030601020c0a0e060d150212090708160b0f09040606051b160611030d090b07090602030906030109021b160819020d0f03210501090c0e030c01 70
    0x28450080d0031403483d0000000d40c05018240c00b102d290404d03001c10407024442501400010400341c4000c52a45c2c100f960f022062035216a186e8441a10341140c8041240c200290100c1c1c0c0a05850500003602e40511000c4040c02d1520081c0c9a010201410850021541d108100304142c0010b2005801e880c0001a5150b0b442d00a00074400c46603241030041c016005445612107046030620b00001304034002460480c501107003124040c03014035004098420110300724440149003c00c00551046904910030114800e2243c1001440f50420310300003004c0711165040030055500030444844503a99820540b81110514180543d5500c146518a51205d03880b001c2e80005e8450101131125014540c0315034002d449400c0100c036105c4150348107042d07000c0321089001e03401030f075840f22590104004d01070b110310f41d90003420401d00004088608410550b0100100d0b03a03110380e98030051041e91950f028080140d0114600540700d40030000001f500c40740c0c0c4200b06030501c00180300d0707040c0c1e60043d440d6a8010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 365652482 1250 365651232 365651239
    0x30405030d050301170c01021f0219020a1202010501120b091510080f060c07031119150e0105040c091a04060f09050705040f15032a020c1c0803060f 65
    0xc4050100c030180140d0420701469507004108101d80d502c2c1703440015514100b8405030b00415900c251004414446200b10701e80c100500d40070400e084e154010280310b860040c140e507004004030001070910091140720380202d003045904001c0100100041a6210407006801c60005011078440050301498100c03082149441000c616080260080040858008454120081e1503100c6641814141c46210403981d062111005100070b01c0400d12804403080035000308030031038003150784089181c030641c6071030081122811890300141c081070480303014241200c108030009008904195452000540700341c002c05504a43e10542c3d02c50034484001c07024007407400980700708085520b03404030016580b403500810504a0404020501152151b4101c8040350202203400070303103e0500d0902c02613404030051060805441d261a58032940000d503410051392070790145940001141040a400c0c81d2400d09010711800c1c5502440a583ca501d01014948a902202c1e555a9030390702c10003d1901c0c003203100200d41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 365653732 1250 365652482 365652493
    0x170306040b0d0c05030d140d050a02090310022104030f0e01021e0a0c06020c1c061103010b0c0f06060f011101090b0f011d07210902150405090906131403040503 70
    0x7804083c40c080f2040d95003e60030f444803082c0049050703540c59246c0c1c61102c42d9480030049084101100d9000c5500401488000b42ca0217125200082c9020a200c03000520541c0c00a01c4003002d68111500104100b00c95400754034618060310701500c182c1c608141b610030701420901106e400c2c0e00c240440e03030718640c05030a0384d0441025604010fa80702400c000c1191040070000011400500006004d6201c61000b480309800b2895007103c0d40920002d58030407201c00c4d84480103c0700740c50781340e0051400b80ac621400c0a0703e41e4501c5401c580303420f20b1070700c0061440c2c221406000c0b41e901c2d21810904010801e0909241c100450300b0000e00404102c3c3c006000c00d98124244512444d100c1e00b82c0b812180032503030500c0d4a580500c20515061015030b2014046140c60f88901d00e00c3c1e0741c0c80d1901c00c1c03a045a403800101c210164021419501e4200740340046d955000405100900d840d41e050f50b00528090020840c51a02c05000d5042030b10f4040d02600d00488080f0b0100d83d00030400c101da02500014094a2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 365654982 1250 365653732 365653759
    0x100f122613050118080703020628050307030b2b050307050307030c02091f27050405010608010e0105010b03010b07150f0209100c0201020a110a030602160203070f03170306040b 77
    0x100751058500815000504000401c45118903400c558800d4540c0b0a020b00303203181c035541c200170165000d62904249445d1035825000c850302c46002348403429105403121a500d15000d440141201c20700c100103441358801208030103160803c5c0380c00906100f40e40750548081100b5092080c603600428800030902e00c000502c5100f0140d201e8010f260780d41c800d44080000b41c035001152440310344510b070022100d50f810b40b01041003040d4181d140e20b403040c05a10103910419110403a00503164122010386850391500300070054000244500c41e2481e24840c000c00965040c41d51074000742c0300601c03c0c42c40c1e0b050007080319030922580e03d441400c0200c81d250100180b6072200c08110294010004903480307200d5162a052805016103014025a80d05138007130702e598a41680c40d0b0300187e00c42c01901e90040072004001c00000d29610003001c1e1008100e035000030525091040518090044d00046004030171100300300300003100a810104100b030004c104035142c2d0740343c2001c40c00802a501d080d9a00c0701d802103501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 365656232 1250 365654982 365655007
    0xb1f05040e1605031507050a2016090204061d030c060d091b1412120706020c0115081509161203021b0102070905040c03050102070b100f1226 62
    0x203482d0031090012900010350f80b84109a00c3e00008141020140d0304280041c18291155000b0880f41c0068113000b4084003900c010100c2490823020007448a034400850019a0009001c50038014002c01a080d031415040400007401d1201c40e00201100034100e200c0841c5694003408002080b00020300066150310a1171401c501410b4682c000b90f40070002c03845c513003441050800d1041c05503046401603051815140c000d2026401c0302c5200401c0c2c501804c500e0090b0314400800502246000f048003585400c1105078560131600001074440211240d40410003c02c1d5000c00e2241100d100c0c810307441c4080d40d44d00c4850742440603000f0b0300503081c000e0f244007066828880d8921900180a030342115130481c45100103805d0301e40d44039451409070b400100c0c05c1055001d560001d5a0143c404e804011083d903981c1d0303807142a0380003c0c1c0d048842d81d000e5410030501901005c0c42d031004016200020400615290801690501d42c00000c2c0c00c5001c8600300c0f07807030245810811440182123000b102d90f610f00c9c5c00c802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 365657482 1250 365656232 365656243
    0x9060c18050102070e0601080a06050a080f07090902030627010504120809060606160203010b15090108070e01090b0f160305030601090504050f2707061d010c0b1f05040e 74
    0x24202040e100c5000c1080d5200181c003500f600c010040304117136915803034010342e00d0b008002d1503c64082d480f954045910340319810b07a00024000500201182d518000d03196007002c0d56034104401342850035400300c0150341d0001c2c00a070031a9514074210f5280381190154401030004800003140d039030a240c00d00040000ca80011900350031595246022915a5103d064136080191407056205a06004102203001d1900c02a0044e620083c000070b03280c414400494524803802d0341c28600c1040c080340d982810f503007003181140e1000071481c14094110089001810503020742c0100c100d44200812560b40e808103031001ca031810800fa001c069018291846d0042003a4412104d131400030300c2d80354000803a402d01b40101c034061590409840210354680e0070749580035061580c1190417500ca41c03800c00703000341c05118000103468165203083c000e0101d55a0305450100c2d80d449641040325498022002c20005910305400800b00031040459003482c182c003440603110350300f0681d40300307190082040030703100700051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 365658732 1250 365657482 365657507
    0xe01060807030c020c040b040605090a0b0906030a03120203041e0f05011109010909090203071706060102011b0203030f0c0427201822020304031202090f120109060c 72
    0x640800301d0740e54207812400e071101408040e0240e881180145401d00c1c00d50440c41142d02c014000142d85540c0b100003450b40780054444c0e031656a0703600510070450610644080c3e2045051b030040c141d4040c90381d4010301909210b16680103456021000c034003044103848458500380303600c50700c04040140c20f04000c40501c80c1030804485540c64140d821803509141010340304d816030140c50308810180303055a117602030a081441245c0c58091302e00c0100c2c1c1c141c51035040c0c030088022a4000c1055240c110006402c556110038000c08084151400380070440c0d00004480c0d001c1ca41c180d460700c03541c03164124011340f80244d4200007608100b4180913002c540d80d4005a0f01c034003640d00c3c014007005a21500c038844a0b0402d510000d402001017010304c441f010000d06142c0d00b41d0001c1c100b4200c0c6049807c0340d0341404510810714040a4001083c80709043c0d0004074403881d401128421460500e035100064a40826030318482d00644000400314200c00080d44440c540303a8100c801401008080358000b0003221141c0b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 365659982 1250 365658732 365658737
    0x203030c070614042306011d09100204030510110306090402040f0608010e0a110a030201020312071211030105030d0e0319030c05010f0e1606021b062206260f09160e0106 74
    0x80440f44400024205048071962400048010300c05040b234904003074004e00b0301030103109a0b43c051059000e80d2000340025806100901500490906e10340c040d92146415907205420510a0000990341c0c2c0c2c1c80150480c0e411107000032105058146840a00032540c05001d036035290078490042c610000c2141311400303101b107540d2100780301c80300304000004009000290040c1d2080c01082d0341140301c607401503005001400c2c6511003039142c840c3d4200380c8800c181c40340c8855034007100411560908000e4002024100e09105840d42c1c91140401d40c0c40c043d1140380e030403490042c511501031601528160383d049070088000d01408403104090700140c08401c00d804201d21404274600090341d035815a4070b00342c0d00107031301030700320010480c2017006901c0b214504290721020800040b00301c2070924082400001440c40200c580510f0603c02402c4188181c0141150039120021060352800a2804561201c0f0300300354006540c0300d40c21510b10b880c02c00ca45851103540742c01c0c0080381400c19880754904035006903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 365661232 1250 365659982 365660033
    0x904150905100503010e0c190803161401091a060103020f0403080301151107030201181d1b0906030f13140c040c0e01020616180902040f050306070203030c07061404 72
    0x1a81458222030546c001000560031100340b0300d800b0f29004024050b00d81c65441494030f240c0d2100c01b10342c1181d2008213040d10200800c0044810494400b072000c0700c41d100c0324000c00c01071440c2d481d03203022065140101c9400d1413240c000902c15a010f9815249608000c0040d6034071a40c503480c214141c0d034003e025011078061100d0704d03403140902c82d03001400d80c80d0204004c1c0c44514510780c01511005401d500b82800d0242c4550046804600300c0c1d180449001c0c1c800325404c190510f4502d070f105024540c04201d440b044204025203030340d144c00040740c1d04042e58a5002c8000c0d130b1450b20320441200b170940001c0c9440c45030100040072a000094440d10803c04803410030013120000c0064074125084007180f8051f8200302d0000d1800c514800000d0501d91503800c06421500009050f4500105190860302103164049010b0045102c50f4008070042c2009400402c280c0c18000406503032070000500700402080d0024280d03080014607001100000010305507403843d402c281c80c06080c0000038410301d50f1641c40740b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 365662482 1250 365661232 365661239
    0x9051c030e0714060414060d0207060203060901050a0f06050f0409060303020601060306050d020d0602070f0b0a0c0801090218090a060305101409070b09040c0513060507050d050307080c090415090510 87
    0x30f078400f66000d24001d102c2c030700d40740c0b82120041410800700d240f10f6204e04140203a0340c1034003290009081c1d5500c01ca000598902d0303d0b50070010b000c0d0068000901504210b5014420581c000032540c1c25192541415625841000c402e45031902c9980c00c80700c90203040440000400da00003418905030341d000d85081c008251200140600103082e43c1d17000c3d6001201542c03000105412341c0c0101856801a03202d4207641c2e0083e00d84a031008015626021301c555204000007901d40e018400070b0240c01611010b510b0404601c40f8804042c240c500c9151245c0c0c50440070411000c459480180215130000980708030405c10a403120040c1070001d0000340207000100001c0414034007007600c1e13090303071848100c01c2c2c241088002400010012280c4c05014407408000c84121a0501c410b01c00081040da59815501c4090340382103403c1602018840050010600500c0395035500f14000030703804042001000e89030807170700300028040c0a074140026503852a1090101e400c3e44160091881036030400891044242d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 365663732 1250 365662482 365662499
    0xc06160c0210080403020c0901032d050616050c01050a050610050c0a080d09140102030106021203040302060f0601050415080619030c0e091c02030d0c030c020a030309051c030e07 78
    0x9000c14020b5008a140da65001024010300500d0f80060080c412546002d00030400319001c0c10742a0025101041c65007407684100c400c0d00c0703101039600c000c03c02d10460f01e2110b54820b41d032030402500c1e050301049040f03841801d291007442500c149009070402445a401c00c0c001c1800244815141070380101c3c1a0304034002828090401c0310603c11160008018198060b200c0d00015000300b00c00c4041e43d529110404d0100b601441d4080c1840c0040d070005075613514000002c3d1424002407280140d00e4014800c0201194010034200d43c00410745034100c00c01c1c2d0700c0d000100ca15106a80007103c0310f21204c10780d210602e5120f88142e11444058810600003008618000d0303003d030303161000514141761190240140c0038012000e80c0c1144001c811500c00011a051f03400d4880006011a0016032001c18400ba410702e00d401800c51601150800b0030600003200c10084d1100c010001c06018540c03681e0302d1300100071041000031003042040c0d0621812080c0b100b0020081c040071891100e940c85290400310304000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 365664982 1250 365663732 365663747
    0x6030b0109110405270a1413020108042a08031903060b030a021e0d0c0215090309190f230d0201140307020a021f0306170a020d031106040609021f2703080c0616 70
    0x1a016140c0741d2541e619540d40c00d0500d500500c070400385254de146980740102d030700710107031020386507800107180c4440c1c40000d40c0403130b0200b03504401c00701420300c00108400070125040342c0d0083c403031140c0560754211402c030b40ca03201c46003081c50003641003000404420b45606940041c00c291442d070309039120000190144510b100043e41d80390001d0b0004c2119200d01c1c50888440195040e005070043c14041d964244c5180c0080c0541c0500c114512a948151502910304060154182c0445655840341c441e500001d0184010640c2d482a9880000c04242018003c04c41003c210f0707401485042c00c0e0407003100d00780d2541500307200704010070705002020455035101c00300da107980c0110500600b03000c1e9080c2c0820009020f0114180d06018104038801d500380c000703122485c4130f91301690003c110000e151041c41041268100d450340b43c1d0030b08200d6000d05541c0041c480d0700b018100030b1016600d4a00302e41000003001c5540c4000c0410800003480c0c120400e0214035a445501860318440001c140f101c025107500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 365666232 1250 365664982 365665021
    0x10f140114010e0904110306010816051e0a0303090602100203040203120708120f041e02010806060c28060501080d0c0204150909050106030b0109110405270a14 70
    0x4160100050080070303200031a0041c0040305150010000b0480030115041030826a816160980b8000a40d000f5080c1000b5544c01018840d0081c5a040c049075100000303090310303006942c4a050031380c407100d801c446014004d40300b5601c020000071643d5940d1030041c0c0400d5003846000054001c0c0d800e880303055025442502e20454001c0d02900e02e00134040e50402e1075503c0b0443c1180c1f042000d002c0311404184109010780300e0700524074440f0391414241042d4002d00442440175104006071010341f001030340d1100780a6000141076401a4440400001e403505002c4200a03012922601820110306680801c42d1030400724029001005540d032141035040c1c49400342e24081001c906030a04002c01810a03900000c81c0c00404400c0440d03140d01c5141c2c1a054440200c41540d1581d1101d0701481409040c0050900401370f21104116610070b400000f01c882c0603e10665104004514007400c044c00c5000c802c0321910340701c0c8000001c81c54594803d000401c4512403240c40942044005003086c2c1030756580c003500c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 365667482 1250 365666232 365666261
    0x9080606040203041b031b09050c09041a3c061806071a040204050a0c0c061d070b0418020a0804060504051c050a08060405010b0f0a020a1b0503010f 65
    0x5669804040c00040d61004e0011928a40010710600c0c540015990203000303944a54001c1c060300c040c0d071008040c10403031900118401840c141c2404010a125001c40d2545034050303602141c00e4011002c00d8445005035042d01c0e0300148030001c040313a0308030b4011340c00c80c2500e0101c00034100e02c01214590b06c0040d52054040750011002c00040300e2822401c2e440280440004050600d8014a41d8500b8102040c3e20511540550200144000c514060252a600160400b800c0150710120f0000a0401074100006014150340d8900306000c1003400091881040d4280d0480d1302e006c0d69114502ca180c1c1c400d11891006048507134546600880c28021910150199030350384500d40c80343d44031507004140180c030888152140341d03c613814856005000a9802c0b903070340c0f0340d0b0b0388070070390355034064003041000b406503100da8075000040c0000800201500c0d0b1120750041c0c0d041d2034000005041c3c2ca010181c1501070030701701054582d40113200704410f8030419110250000d010300c1100030020400c0e54046100d0f03510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 365668732 1250 365667482 365667493
    0xf030804030305071b060306031a060f12070918030f090e07050f16060b01021603120c05070b040308071104090f061503140705040510030f0809010905100f02010b010908 74
    0x70a2040e009019494004c0d0720017025000104081c00000003958402004281c41d450100f048c005003450007184850a449a43c000d13183c8000041c001c60f248003101031160560424100f81c0711070070841c05005e84524402001000700d104868842c0100301c0f8011000104810003580900f4030802d40d91046070b010810811301034503015000d956541105c100002c0004061000d041101445840c440780c1c280100000900a420900028104015884030a0152040c032008200140e13200c0320300380710004079280000400340b40d480c156040c0400c56001c03180007400424040188211500106126407103105503259a200b4042440152400c030400504808070704101080070614580064200540d507003c00e41740c0c3c6480b03660b501b6040000507021003075a8088801480b903424248102d640003072290400c190403610716a613505a501141100801c1c5882c02f081c1000c150340030b000310038080c10f40200a441103020041009040341d0950700b00340c00641c282000841c55501800b50401543e2000000e00b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 365669982 1250 365668732 365668739
    0x20c0612010f1e0b2107031d070b04030f030201151403010f0e03090f0609130e07090203130f0221030307090f0602070306051504060b0a0306080102190309050c15090a0f030804 77
    0x1007543d04809505d21030345508002801040d5a180c3c009445124240c9002075040050144148015014100188282d00c0b021050020b031512409440480c1e074040c06164100700a441c04a0262103040c08180d91024580382c081303248080d640b0300e040940400d83c0200854aa11004072064420b0150a11040e400420800507142803000c070103115002c000d4240351521000602140031400038840398442d40340d441003102c1c22090240807100003040c410304254110300301542030349148a89900001c0c0940c040036007404c110745450320030310400302c04039044000e00402c4c0380c5903540fa03910031540240001c035112804542a000824031800f9620168014581641540c1da440020700c4041c010038580c0c1d210300d46103000c1c4d42d2640504005818681a820340b6500e11410107800d603a80c41e0842c5250740d005100c1d402080701004143d41c07003404103140c0400c407885907092840c01c0004488581c0c0c2c000488141fa90031300c001100041c40741c01816103100c1003850b520700343c0c0550320040f0b001c0204003031001c00042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 365671232 1250 365669982 365669999
    0x21021507080702011b03020c0c04052e030c0311030d21111303030509011e1e0507061103150604050d03032a08011a031015020c0612010f1e 61
    0x90340610180000900c2968045c02c40140303490855070301c00042d80005290b0f410100500a01013800019071303090082e4201104440144000700000200c00c0c0d502c080c40b0205680ca21020500640e0800c0728501b242c0d480342400c001591901800500902c1040c0d041e0040070310609010307503911603018030440c1201c1038440f40c02c0645000c07000b81d495440280958259072641a4100c00210300c00c1d01c5860303852501ca400507041c810f80000c220b6110030f10303503070441003103400c1795401c101c100304824030350380c010107414081d01c99014450b0061f008500e0811840381d0f002c0c4070702c02180a1100c00e042c880c08003441c407007000703040e1103180202500002c560581800180c040e401c00c0083d03e005041c0f072041c060910001161031b4610716808400101860700402540801c4c44d00b042c400d9000c04e03103e40c91842c0a0f0045c968001c2a48229076803280c60320b0010211a201f03004010440800402c03c6645042c00900d4052100d03081c040c074642c240d03104400060400c43c0100700403883c0b18121011081a24109a2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 365672482 1250 365671232 365671247
    0xf0307260609150a030c0e0a05071b0204020715090303050414010903020a0206130e09160b0702030a02121002040e190e1b0303040e0405010e0c010e030a0206180a0321021507 76
    0x482e50001c0c044031005c40041d1005c54000701404034030001c4002450284ca40806440015000ea0140201c0145415106d203e1000c643c08503901901d016a43d505946000400c1c82559104070040314640305004040540c9604402d00036401074420820184030010824200d6280503001400360b800301e600d03040107080407805001c2040125030000021640d418205070054000c070303022a151b812102440d142c0040480400010301716101e0b445081c82e0090340841e5583c8400c06007e441842e11000c9803030384201c01c00c201e0306003820586041d520340d03903112007501c0d00e0001580c3c0b0a101c649880011200030400c1c1c401c03c4980340304c0b24014502c0c040200040008070182808032909400300f04804a0702032480c914140c041c07407203140005402c12003e0016420320513582d89881c10828030000c81e5056550004801c3c4503240c040358100e555400da52400184602010f07001c0b500400144400400e001403040d20701b482c034501000c0241c0c03940d00020120f80740c0b040f03559918690420325012407041c501c91500e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 365673732 1250 365672482 365672521
    0x605040519030203031219060f051207180f1b0503040f0503070203061e06010807091a09270a0b030d0f1107030c0f0b030103050d0c080f0307260609 65
    0x10103001c15140d40100c2e0031035010403052515840083d043c0013111200c510f0a01017a03000381c0c01008034909040700d07a0382007002882018410030361504d6016a54000744062801440750644a0420120413010130000c0c001e11036810741110b03c1d204402842c0304441440c00740030041551303024034550b9165a88c5500f00880300c0c0c203588606c424080000141c8042007014050041481c40c01e5000801c00440408584010003d41c100f003600c800f4071139080c1d0001200341c203850b040560f00800713400c04e0318030051600403103220701e5022123104e03103a60a00c101135618100300001380c0039168650f41c81040c0031083e42d124603022509580504180c9110621507201401050304a2a01007020b4021086031407a00040340c2060301d0380c120100c010804d107522152b8180c0180b0b11264200e04642c51603e035151a080e12001c00d00a101d17a001c0c0110402254408460312000307820380264070390a003200001e020200700d240740f24a111507024240000a41c440c59940302d2840100f16400c60307039404d8142c0c10000074605 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 365674982 1250 365673732 365673769
    0x6030a090305070803040c0504060b09012f101a0a031113060323191a1005030d0203030708013006060b0d140a0e1c050415021f02030106050405 63
    0x3c00080e011000450189000b8070000c00a58100f00411007110555880240005000c02203c019640c114480e030040c0c3c168001054250b400010290130f03246a01c08138003010780240341c0310b444d80c50742e40c0d0702c11130711040c2803494003000c2071006003070104140749404083c0c00c50200ba1540ea55a10300702c0e00101d9001c0420002040465483d600c0d1042240c29508544040035501d6080080c1001000603a110311020f94007004412115181e4080c42c040c0300006441c403641d600001800c0004c41c00c80340b0004e20019084078189004040025103039002503818000042c4004000101c0696007892540080911955400950300003005038151281400040301c170203840744000279050304688050181001d440070302160843c0b0b9400c0003005880028156100030707140101e8810352a84c00103460140c0ca0925800c40c54010300f80c02c00795440c2c040e03a401613101c00002c0c103a4102c0c4a81c00714101d141d41b1100b00201881d00c4040b6110401c0c2d0209000b0100052000d01c410805498a80146407401c031842 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 365676232 1250 365674982 365674987
    0x4060b09010602010e010b1c0803090c210105010b190f12320f011814130506093c01020307092c04060c170414010f060506030a090305 59
    0x10000c111444802d900000243c0d54440c0e40c6440f503182030040c03141d200d1007110801402501101c0b020360602c0c681d9006441c00801100041561170200001e4900e014000c0c144400c5050382145c9250014a054801d0f03900c0d4241000001d0b030440b04000d68440203007115104820245500302200d0f4507455001042c01c22050444c215460301d01d911170001c04110b4243c81c606200303441072052900e04028030102c80c40c200c02104221160040301040d5054030303444000002d8540c042080d070406407007070070b10b201302110200051080d148c001e002d0012116101c2d01c241c890030f1b551034010f241c40e030391015084070980c880001c2e01c007400310000312a80901800c901780f81640d5180030804908a0700100d481c400420103899060081c1d20b8402045030b10070b502c1000c904601c000e40520800501800351004148645078060f91503054055214401c0c0c0403a140c0c241501c0740b40c2428005004644024064100d501c0c180c41d00c240c4440c180640b405480c400f509140c515203d0400402c02811642d00a0301000002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 365677482 1250 365676232 365676251
    0x1b030913020d1d06070e060310140315090705120a0c090e030f071407080d020a060b121f0b060909060d260711060301052206080d05071a010612050406 66
    0x70042c20342080e0f40544001e104501c2d01d0300d8040d1094000e0403500b0300c661824000c1080315004c3c4600881aa080c01c0740d164040030100300030a1500940c0c1c0764058120b206101080b610440000344071040354070844060b01c10603c244181034451a2101015000d034152034000e003c0c0c02907681010606100d40c00899117004c0001078810101e40080d03604441c000400320044a50b86c40030410100640704400c0503161558041e5000b030751f07a1102c034200425107a140c201c64215580c5240b201e40b200b03031001085c1c07160030002401c01c4450500341020700c0c00092815600a4550401d001a16082400902884c6a42d01c58004110b4403504028003107624000b1b018104141b00b05031101c00c03402482100d003c43d2501c0300ea15003c04d50510110b18180603d0081c0010440b0340c1d01c1c1c0722062040440c11803042d1403140c41d44d110310043c22081e0040007a500c0f03581c4100d013080364000001c2074000c1c01201040003600c014401c6181d048820b104110009101d030202221355080d0b54045900a4418200003420955 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 365678732 1250 365677482 365677511
    0x1504050c1606020c070b090102070e0703020f070602030f0f13141204080d080105030312062806180e0c1c0216080d0c080106051903020d0f021b030913020d 68
    0x1481e2400b220003d4010480c2c16110304100103a00160106121450600d4032010000390b41e0b400d50f12411800c40ea41002203525980a5030480d4044c24011002a5070340000e814800c01950068851100320305d40131000036280d0102d42e50b00d900070703d104021a6a144020b485076501d980d4841c000660501441c2080d0003c0060000103100400c2040c0103400e406d08841030141038010141e0180303010760001c020a90800014040c0a54003403021100803c0340c4440d071001d80300082410a10704821003244401040d41d503000201116600c1c03441c900050f0a40e22010035140e91a000e0316400f1b030800c41445507140f8500c180300c1140c602d044181005090100b8903078020071000c800b42064801d01d000044100605105009a055041242c1011130040d45020701c010094460030700380c0c2c2c910201e003154607800c0307600c00e404540104214400521011224451210080d4080941c40304400b24107091403041e00400b0042e103107424001040340f0481c4005000010203580b00340d801c410019503850254200343d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 365679982 1250 365678732 365678767
    0x1202150706090b012309070c05010f2f030103022103190807020303070c11130f0506040b030d09090207021503040f0308150d021201060b0f070213051504050c 69
    0x180185008103480c042410003c265200c1030308000b40448070820703450b45544a0400c48030045400f900c01c605655504041120710604100c1d008009500344058100c1e80c5400da086400e0011000b6040c00c00312003200200303000c0d41040510940641c40610040001d423403c6080740b07000030581041d50b1400c8516807006030850b408484581c46804101080344a805d5214074201c1d0301c000c26000940c80d500b0128006002c103039140000824000340903000302c045864440eaa101070040c07610091004207416200340024210889409014620b081500c403120315000408803501c1c0100d8940c00c056031709010b510300103035100c48400e0703030002c0d83c2c1d8440460340c210640083d8800c0b03000380c2000000401501e0002d10104028140820329903148548401c15514868001d0003a0f5048030018001040c03000c0b1140500840e6004130303a086000b00c2c058860401d0300c401410b5003442281c2a9205200ea421004201c0f03000342c81c0d1407004060707180c000c11141010783c401c60708541d0b14a106030900703100f016011000d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 365681232 1250 365679982 365679997
    0x19110f130204060905040506030303060409231b03010203010e010608150603090604060b0301021305130612050d030507080c030a020a02010e0601120524040206030a14070f0e120304120215 82
    0x1035600080400c02c6590250b8814090030003203405110505100700043e68a000103490b10b031140d1b580700e0940381042500042c944030240c104059094810204100c82d0f25880c5407501d12014408186e80014285010f1003124140c41c519044101164280740d000c880780c0c080105022174000c48035a155507140ea914020b58482c074074490042016151031f25044040d41d848150340742c003a07030050000020b9000803003584801e0399402c0e10b11030070b494210040c0c00d0180c0b049a00c2018941500d017002001d200000c110101c400c8143d4030b0602c103a40342c0510444800404407810f403e00a0103202185201e040f540080440c140d640c40041500b010b07180d40a4240031081c1c0c4005e000036a40785050b0104401484026400040c5281d20030016810448184c44044000c000174443c140000006440040c90390001200130b134141009122441c1514000e0308440d00d0282c01000314404441840c1545800d0401c1083d40d00f0760700c0514201440c29084e0340c001c1040c4c02c002c9a004168500d07041d4800b070b0000c050601d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 365682482 1250 365681232 365681269
    0x90904030810080a08030601020d0e09070c020a031401050103050610030507270c080a0c0201050c0703051608160201091707090c050405130219230307050408060f040507050319110f 79
    0x2682007c00000e441d05035030799561002d10a05200280c2a683d500720034941c412254200700445151910008982c502c59810003414204c7c60b030f80320359981005600240c140c82c4194200d4505031540c07801e00e0407100c52440002e0559110142c02c0c000701c0803800302c4100c440020b084001081090014140a481c18034540400140990003001000e01441c01136105803c03050008001a06008034120541c0c400c2d800d02a0500c0000119022a5192801c4059017690042941921103501e8038000261410310701c07060780050100a00401c2800c4240092010b8604d4640113000d03407441d204d004000f500201602e2401e10009110025058440070710403240b640084000681d2168200304c0d00b0362072001c0b220b046040182c218221268022030088a150791040d00c14046d03126a00c0003421152480380d07030012203403409408107001e4800c4c1407100701400f807441740e02030762522038450007419592141c001d107220400383e007001008082004003001c03540307501c0c0140844044030700b44404540803042d40c2070700e42d89 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 365683732 1250 365682482 365682487
    0x4030309030e1e0f0a080a081e0a0c020d0311010e0f16050a140d080f0d0621020f03160609080609060415020309070f080709060b090904030810080a08 66
    0x4042d070180001e03484500071900c02a01c000403000c0c5008001c2e20000d6207002d40c07444100e0034038030356502c080080141461801c0355a00d8000c0c0c6425015600412400741c00d4850300403410282030403030303000d0303a104500d01e0b643c528900e0881d4003044070340b1003426020750611641c4540140407640030300566212403400402000c0c00c3c03503220001450f1118640c12020b010714460014002c0d0380d100004c450443d100d840d80c00c40c419480400007603000100381d50050207424001907410700311548101a204c20110300750200f008030740d90400d4001a41c00303030725900c481c13403900030540c0700514200d4485407092354040c08644100140c448844081c009076003104c00411441c60f000c11180c0e0b42000241d610010110107070810f802e240d070b9942c20980c1c0100f200b032011500800058075080742000648000c05c0700009130714800340d5400c142e5803107100c240030ba200c00c0c2d0f00389440400d1a042c807008498440e0406440980c3c00d42d1507440454370400050202c0f074a03000e2010000400b0300341040a000c3c0540a0641c5a9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 365684982 1250 365683732 365683751
    0x312051510210902030a0b1e01140f0d0b070302070f0203190b01090e060105130f0c031a0a030b150102030403080c030909011d010e070309050718050708090c210303040303 75
    0x9602d1486481c2038012142081809001a180401c660440c0c07544012089181c0c0c03160500c50442000c0c8043d0041e8042c03614000003850718016050310b28628081c1c3e00c1450602e400f030103100c00b4040c500c401902d00b124038000b0900c564801e43c000c080003401014401c0d00c1c44003660000341404a01040e940030150a4402d90040c00320000009004008011040140c0508825900d031a0881449058801d01100101c090355440d10780120242d4003602c541080051444800a002058210b0110005000e41025110103082c140a8001500d030008000942d95650100d841c034042e664071501c0c0d04501041c44000001f80c844400382807116204800345440d55404001d02c500c100b41644691500d4000a407003004121045007544d0645682042c940344a1780c45500c2036010704142e0300010043e00c900c401c005501d420101440500050b20402070005032510101107075042c509842c121015000f210b0410200d01d02015400348500c1c2180e101c0300e074113440c0105581183c008540944c0441d40b19070085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 365686232 1250 365684982 365685017
    0x40906020d061e03030e27010320010206060f010504080706080103200105090424030507090c03060503150a0f0603060c0e151e0c06070203180d0312051510 68
    0x1c1015010f0030741c1074240c038507600c01d451a41009074400a024050094031481c015115101541d41021490b007890340c1500401c44403895204c402d200507651410764550ba1107008031200d08080748084141d00801c580c1d1180810850305480d221072181c140442040005503041c810700c181e1000346030a40b1602620b44c55800d007166820400d0b413420004030110101c1c150540e8200c81510361143c020348000810b103042c907500230140b407c015001c0900b6017440000104009000a50409568901c681030142511100c400c0e826076407c2d02030107605410600700c40d481004503900581d40000c805c040810710ba204103003414122080780c0c009903034040d280d40400c0f03c02c0d81c0041d040701c00194181c50307a40c070026106150b0500390084003120841005a01c22a5051125240540d00d08020f035606840f024140303020301030368a5002c0d1003841e00e02440c1c0140d50003d407524100243c0c0d5190982ca0700c14180b6030707003403030740e4001d190041004460388140590024240c030b800605454051320b9444c0c4011080b008000d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 365687482 1250 365686232 365686241
    0x170601170606090a090f08031f0510020d210c0f0f0c0209060d0305220608100b030408090d0c0b04210f080a0c0501050a05061507230c040906020d 64
    0x1145020341c405000d0100301d840c0d180300ea0307502c000f01c2c200000340d030807003481d0500e00c44d5208003003e06140004024065440c200301148505a035968140070000c9583c2e0091001114034209900c000d44c1002035041280da001700612003008045050822407000900c00c48021143c034152110002409054000d4940b40c000e442c240c045801400c0030960300e0381e01d0b4001420401d00400d4140210640350781c100030140190203403407400c00c91540c401c1c90999414400e40100400e4443d01c1d001034401c10100d0001c00304866210191483d83c001c69241d40d90340e44901e0481e50003e400c290304000d07451050380c04141c403c81c080e00039000d90480709603510300d0091200200c4145840708082904440c0c1843c00281c403003400400c03800d90104000340c8074180050152001c0100c1c0c1d8014245500b448204a03d100c0650300251044000b1150202007420a07420045907010710742d001002541c0300c0034480c400c2e90b28070003c048002c0140c01240c1d087d04001d00400c1c01d03038845c000e01301d81a540100b0150b4448546004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 365688732 1250 365687482 365687519
    0x70507140109060201050f01090c0e0d0b041703010315020a2001060f0906080307020d060209060408070f0b03090307030c11150405090916090216020a031101030b04020406021b0a170601 81
    0xd0100e030505900484c7c40c050107200d110380c1541d55981c0f2240d51405120300034001003000b021041403040b45e003001d00300424215000c5803007143c5141100b080000c002c0c25241600d8111034000268446001070030002c0d401114a402405031034000440e102000ca050b03c0d03028a09000080340d140c0c0b40c044480590750040d0046d102c59801e0010900000c6800016a480580c0465032200c00640500317000000f840340d020380641040c0009401b040d281c60000300c070400ca482e50800e440c5d00070707514030b070081181c0416190450107030410006040030900c6078a1842096024000c1c4411000d0841c000071003400d513440703403240100008242000765180004080707030310960000181c80740409070050142c41261601482c3c106550128100504406603002d2002496014144140d03040c0c40f8200400c12011f075481c3c06000900707000f161007807803c1038029601100c41c26001880158059072441d0700081c40100600d8002c000c0020014001c00ea160244815040d0b42010746101c0d418200030700002c07441d80700d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 365689982 1250 365688732 365688737
    0x31c0f0e040c0c08030c040b1303030207060f21141602190b07110c0d03030504050606011806030e010915050609130809060922150503010b0303070f0807050714010906 73
    0xb2507442c081504000d411404035840b14019560350790b0400342021038000c03a04003c1c0b03244d60100780303100540410304031401502c1c0250202c4d0110f0b40d640e602120fa140486080c04001086c13020346523140441d51205840020f981d03031003c50801d0f901d600c0d88007104011240d1085440c0310840c007101064041c070a654800011010029580ca06903c40610904c03000e0082c004103c03103034400002a030018030030740003403000c01485001e141e100e604004010308010344080c7c03024010400424600c0d0b000b01245060705101b11384203590b251410300b007a4028480b40c901c8400f295240c01008001072900301c000300003410814400142418a8000c2c4040000001d0408108080402c020b00c0030681c0c0d4401d039181c07034a088510b82d985904520105005801c6481c0b0156910b40303040110a0f1156150000c449403000007202c00d2034180c2d100e08040c241c642c4201d105805030020020000880c000880601c107c900030030459103010203590701da0345803a00310380c0901c41d000e45d011100c4015680c80510900209100c0c0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 365691232 1250 365689982 365689991
    0x3120c080606070b1b0a0f0f0804020a09020906070827090403170408040504090605150613050d2a05090a09021f110312042d11031c0f0e04 61
    0x71404182d4600c1140000343c003200d03090b40002c040280d40c0049603516078031080403a40b2581c81d000c01900c205100620704e4003143c555240300d036205100d10055072040703400610300d03a4400d181c210135000030751001111a410020030000304000c10207103002030100841851596030030704985800f5610104107161024821841a002d020120758070019035800404e268240a1480d100c0f03107041e0340548103643c0600c0d0468100031400701800000c1d40300620a600b45440c1440c000c0e01c580400c1800e00c00c20300d80103040c0c0c51205003030040313003001d1032009089032103500c0c80c440d442c080c0e40000c01c3c04555a4034036440300030311600078010b038240307007450540041c142c02c002c0c0007039182e039800900d8002143c0d030403481c58003544081040c00c0784103404003422031a211050b2030780e803640000101d0286a0468043c0d8644c19000340141400305000354110f0404140c20350b0403c211089d80d5415041d90480c9001d9a040c8246011001d0140383c007000314801040980b10144d42d80c0c042030000d40350000d421062403099181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 365692482 1250 365691232 365691241
    0x7120605060613090209010903300e0112020d06030f1401111204020906030a0c120209010b1e0a020f010f0501061101050907052205040b0f2212020f060403120c08 71
    0x1000b0b03c030401d0384d8201e0400340c0c44101d858012203c03035003e507001074103000d1020b01c4145800002c9042c103111411004c03604811400e511300664030603c8084606000418a0300740310045111a03002c1c24034980c4201020941c0da5990b19000c0c01d040d410780e01036420803d601640c00b1001001d1186602c0c000300c03121501d06108072060b511419641c024400783c052900d00000a450741d03805c0c054240e59650140320b1707541941d112884c0104100c50014201d00030b080e0400081490001e00d0180e51815110a00302000c400d200004509a45c10100c0c5c07500951042c00703080c1000000c00c0c0510b000095020f40c00007540e62504030700801d0034a00710900350302c0344d1400060203000a808a0600c090341d4082d188000c09e0b50106d0044210000c11040400466141006100400910700303009406500b4018809455844900038503000e4110b9145001c1e42160707032070500c400280b0824000c407080c045070054070700740381c1080005410400126030460005540d010340720044070081c4144116011685409800c5151 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 365693732 1250 365692482 365692507
    0x209011e08090706020a0c09020f0915041802090901060309022706100f14130e09030405010e1008011802040e07030b04060b070803010e0a090c0602010212150d150b03071206050606 79
    0x312303014800c0c002c1d40000d11110803200041c100c07a00b00402034101c003400011010b0f852900d4000340110311042815070000d918281480c000d441080600500b400002e0746481400e40081c0035051040742c000104001c8489100c1404040307144d400c40c0325900942500d0100108203510350a400c8840070701404179810380d030442d0300c00310b40e034560910012603d50742d0b04283c40b2007100324065408070685031940c02c10080303030560200103042116000c4c3ca540307081c510b00d9000c00100c000d200ba846000164120010801020031004042025403001da00600d800e0303d0740094580d0040450f41c00d00400c2d00c076a030310312145c20715114440042180400b40707424100c607a6180f2000d8070042c411418407a603003c020075440c40341d03540088017080d402a000c481c143d94400f4068017075000745003800080790b4404d00041c0580010740c0045c072034240c0103008802030541507070380b071202d241e0144100c1021640e410480201e5141001150301034100040030074480a580c1c80c02d14184c6200506141c02040c0034040c007a02400c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 365694982 1250 365693732 365693753
    0x2120f0a2307080c0c12030d4205060c0d03020c0c060301120c150903290903131502060106120f0f021206030606060306040209011e08090706020a 64
    0x18158035201ca415080032500c10740008207507158907918600060700b030007004501d40003465450204800c0e00c1c0c600010500f000089031842e2a15504d54100b00680180f504043d488103101001040071400000c80680d18440542e075124181c0c4406075103c200c0f06607520b180340000005220445070549400340c0070300c0d526121082104c0c50001d0503000720349043c50340c1c0300f4880300b11420005494552031390780d01c804a074000300000c803080e120120a8180800c2c025161001040886580d0b110051064910794658400c96081031150f6a40e10800b81043c0a1404144242c0c0c0070b000e0a01c025516501c0d44c1c02c2d18a818006030f8420a510312004540540c3c0703a4011440c94111451400d00c1d094032031100c15600050078090407a4800c0f189080d820b16481c031002e40c042c3c950320740344c00030b07542d4550f0360301c014180d5400301568100d40c821000d1000a17005c0c034098000b0841c02c541031500000310060350a1100e1080580046600460802d0040107081d80c3d080241a000742501d1005252001300d5072036440009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 365696232 1250 365694982 365694997
    0xf03011401020105241c06052e14060d0906090b22050d050a021c0807030b06031521030f0304140721060b120717010b060412020301060b0309060103020102120f 70
    0x43d544000705c00007404503c010000155049641401070380b801900414810403070211407141e4540d4045581030031290300c00d00608ad2082c0c000c2c5264114210fa0800c240c85e08400400c00c2c001d900e0b42d01c8070000036141c0c090721580d18031980680320386040c0500c9214a09450382d50002e11400c0c0d0f600c41901107100010000c0c16460700341450350303031800300390003c0342446000e508204000180d0781c0c1500149520504840c403030f1402e0b07034082200c0c1415104000841c44140c40320760740d0180d8094072415602e0071982d00c40d0400e00b50321000c48140c0c562140f15085400841c4e40c440303628008000c010510085800d503442a0703403828090029030381000303401c450080300a201204004402c00700c0d002048031a600c00254444003c05401e000d9800c0030b001652501d103070051903003007090100780301c840716014005c82181d144002c000364106420030b8488101103484520607039242d03481d00000a13803031140300d0056000d0a44100508090360441c00060310300580000030300b2109504000c0000c505400f0019208003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 365697482 1250 365696232 365696239
    0x6060d1703152706010801061d06090d0503090f03010204081e032802011a0a1403031207180509130609060b150717070c0b0d020f0301140102010524 65
    0x100c1e10342080100040310303005403581e00480c0c0c0014140320010f0740b24881540c42c2e00c00150081c070740d54038001110b41c00070030f100300004200000050032034288842c0d01c961600c00c0151000303042c00058030003d8034103101da0f50705841503080041c608549003400000f0991401058001b545010b141840d0150340e4446075500b0140240c20800c00c01c003c4809000301e07030032940c8202a68a1002c0070550705940b4031202004980507601c0c000500703160800020701c0b040d81c91030041c03424803114585540f03540c46c0d03a84030390181e0b8503000400184545040940d40036024400580d20703002070041015925801c00110740000340306040a4080000c3e20301e4522603022920380c40040030a1202d16840c1c11170140c88604110b5900090040c1142007901c0003001920019009504204a04c200840799080602c1016806080540c101809019180f03049006004041c210540103103403c0e41054810201c0d002a0400c810500c0041611040f640e424000c494110024a8400b08940a040006000ba41007000228007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 365698732 1250 365697482 365697487
    0x2102040f120c080d0819150510050c10090203120c0d03020702030c0a060806010207090e0c100504090903051c0209010e040b04020c01020c010204030b07091d060d080c0109030206060d17 81
    0x40050102d241401860f0502c03c59081540810b005480108201c0d001501003900c01009100b94005005a10004845500000845003001c0c284400c0960310344080f800c0c00303810400440c501c0c0b410000203500e0400f5030b1001509062500c101424004034900c04a12090180882e9400203c081352201030440d003402e00627907a03019440403a0030800b90f86907095000c20a0b40300060303c590040040c5104100c03da0a07103003d65280c42e00e0604596465a0800e4150300040c4582e0301410a4601070740c950103203080817070429650308100d1003952100001140000c8002c1885010f0b14509903002e12501617940003541031000400009118402c1049a507120b19240e918000c1e00b038443d541140e944c0f20740c1c10000c1d9514003491036818040d42c0144411244081d800002071461881901f01e807040d104010015001d020300c04801c540881c5002d0017099000040c01500c1d400101c600380100840d040050003c621410b05090180c14003c0051145008410a0f184400015a2215121441c2e103404544c0358 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 365699982 1250 365698732 365698769
    0x6060306010905032e0204060203073c0b0c0a2c040603200105070206030703051b0703020a050d1b020409060603020414010311010c0201050304111306062102040f 71
    0x3968440b480c1e220a8140c02500160124140c90b85c04082c1c155000800500b402c007540a100b00481c8580c0c45244010b030400c1c800700c3e0020ba00240f03050081d500f038100f000000d1001500d070090b0640018034030159010f08501100030032181121296001c0f500c0402e107410041070b00c070003070240b1442c0d00900702c040003001b80e20841c1c5400341c20354610024000d0400c104031070302d03490165030070402c0100c1c1d00341020620750103980c0340d8411405c940f45a82c0c01340c000d901f591940c0406070302912015022266242d5042102440841d1800213410418000e9000f06206c0d001428110706214004109004100706c0102007080e0748c805550040c0c040c2c0e4140d40000b400c00450074000002c4c07400307420082d4020b041c9001815001700c01c1d80e0b051f040e02e00650741e04902d9607407a0015250700c07058000089c04200144009004034450b03060300201d410340642070b460038010840b4003404444507071f0810703c0401c810f42d50f152a180c100000082032440103680c114505420075040410030100740c80340d000101c041d0002d55 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 365701232 1250 365699982 365699987
    0x7170106080403022a01020c03010c1715030109062f1912050406020a27181b05180a030b010e06030a1a010302010f030b0f04020d021b010e0d14030606030601 69
    0x460740c40c03e1514605c400301403002034400f003030100e410590300521031900720100034981846112609041a01c5100070401046e940d007042807001810104c001920003043c034007644081c01000383e441c0c420a00025205c070066041049030700c484e0709144020320345d1484480c0308000075046a141055010300c0703131000c041818048400c4e5090074022422181010213100800005402074801d40280d6210f864030500c40044c403c070110181c01550f49c4915040b001000300d51a954070076040f450304070b00f002c0b840c81e4a04032031941d0745400c5a140c000080c40082c04035041702c01c05000780b0715104100c40140489155071501000c800060294441c0200d4101c0031400a40e8200000006558000d5039680124840506a00300c0c01c024803040e40450018038060700068864811911180c80050030020718540c6003080c0030007500061400c0c040c060782040030142c0c01c240c108800b03c900c161200040303801540c40800c03a041c10b8403d56010280000960040010301d010b5064035032050701030351501c3e282c0d582c05004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 365702482 1250 365701232 365701243
    0x6090c090402130b0325080a11090405040f050c0d0b160e0a0b0d0c081303080a1508010b12010504031d030c090a020c07060e01090509040804081507080717010608040302 74
    0x80302e00850b150000c0c21407044d03000b45110f42c0403581044a0f140d048000e400719403100b01c68140000b1815000102c3d4003041e54030400c1b40c1e00b804400706040800d003901103421a03406036415610300c001301410004215003000000314030b2005942c440c20940280d078481c02840c0c4050a45422003000100c2c03407621510904403002a00c00041c0200d03420b035a11140b810303150307010600024041e41416036041406e40625607150080c503002c60000c2044140351400c80710403030007a204403821034031a0250f00c0c000c010020050041d01400000107110788104040141040c4882240480f0781d040c0020400840e800180144101c110340302c1251440004800203402d04a20b50286948500754406000e903181990340501a10790ba40c0d4100c3c0c6160741c60713807400d0703e0701314054040f81c0c000380e0400024011030820070300641e0064410140c0740d040c02e03210144d0390b0503d0700000010004056000410180300d80c00030020344c121440c0e00b04422014041a52000198814003548007440240070102e020503108100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 365703732 1250 365702482 365702497
    0x12040b160f140c0901150815040f0c03050f0601080619050d0f14060613020d0608010228030204030512030414060405070609080f1e071a0301090e0606090c090402 71
    0x9541c050207446180001c246030b0000300d111a144518296003816052041c55a07041c0c1302079010520b218481c10000712100000200410342d10640c2104414040e21140544030800000302ca001c02c2842611100401315000244404403982c542c1050280716600403004640084e001c1c0c1f220005a5440700301100302e24200c0e40469001040c0340d081e2003d01010f0507495240303601c0760020318a160002d500150b41c42005983c180d5200300c90300d210b000701e9035166000b0304484540c8507011039082da40da6030329030880e080180400e6580000c1d489181c04250011581501da030707280d041c01c41c1001c0c01c503100c5039a02d56803160304c0e076407014000000c40d0030700405642c1d13038569050031000c4664030318117840c0050719910907100e0b14010546500c0d000c101030b231020900088442d50880281403001f0451391144104c0e0780d041c03550b14540600503001c00c1554425019203424040912511b580f949070114030070403100340710410000c60300030b80309004a40d505c51031229001000d40482c41e13103034041480054001d208040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 365704982 1250 365703732 365703743
    0x1b0c0816081902030327120304080d1104030f060216020d12030f180f0305091e100311070201180902040e0105100215041203060f06020105090c0312040b16 68
    0x48100c01c012071400245140c100c45203203007400c03454004007640d0f40e000a4550103001c0c1310415084500c03841040264031007214040440340c103650481d407010410350054030705a400500c005010b0302007046600441220011307540d9070620309441c503201c0c0c11511407103940c004c0c042900010b09502000b4001d00494034150001e111056444003403408a1101442c8881c20b030104c0cac02c000031442014200e00c2100081003600c040030701c40001c1c0c4d03501c03a021f00e031400d582101889000d01641c0600d4035650202c8101c520051801103082a84038204400c20008005000806003041c000210203054501540c007115820b00f0250080d088100c5165040354503908118403042c40410005480400c0201032130496a003510703c48403c0001c103404a813595030000c45004000c0010340840d000404c070f8114110001c04503e4005111511900c0c0754449040613031221006079104c0c401e0003038800081c0302c50311526600f18000c0502d4010240e002440d405030348030380c41103000c000c01c8014a50000002e40c404403503101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 365706232 1250 365704982 365705017
    0x2060f24090115031407050906070606080607050301171207030807030b100309150e03040308070501091b0510020f0601060c0602120a051909030903080a05070501050f010512011b0c08 80
    0x402c102524a4001c0105400181c24038160700042c10340103041a010380345030380d2540c0c0f40000d0a000e101d1580c0c42b2280c2101e10680d10000014202800c1c815a0302a00c9182e507950754a500d0250310003200030341c500381064207800c40b50204000301001303421a40001d41c9801c12180c1c07540e95000580040000d224a0303500400c0d1110444690f82d031551240441034424601d91942a02a105403c00c80c6e641c50343e6464158001c2000340042034008015010b154411800818007111a690b20f108010310760102142c080d1401005004034502403049602d8040980300503c020400c1c800201da4461040c4152000e0080e42031070314040c404140c041303440818040341c80c02c8150801c41070315002880304032610107035030301044501010141c550151122071905070369040d0b025811915818030a6105c04076580c00d202c8104095000100e0a0041c1c3d8456801008014244c2d03242400380407200b842d4401d05141c0340d02d803030660100e803501e2842e1003030310108a282460f0303012460f103087e02440c4540500c82041d00c408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 365707482 1250 365706232 365706239
    0x50715140103051c081e04080d0e010906061409150a03060e150709030302030f03060a080a030c03030b010f080408090d051b040b0405090d0c05010b040204061d0102060f240901 77
    0x120040500400c1c000b5145020000f0300498075a0010703918500808103110004c0546d002c50b0b405950003c0c0510445032910002801700340844d8141c030070328845c1c0d0351124040d07002d01030a0b00c144001040d0880001020f03440c86d000242e02440005d0031068030780c1c0345086414150b292800440080c5a001c04204103402013008090f549241caa04071042202c0c540d40090b43c0d542c81102000100e9030706400450400c004201290456000240aa43c114071910700009056104000c102080b6002c1d440c1c0859100d802d083c010207a84c10146024140410207000d04a450380c0000f685500940000c1d580b0303120310680000801540c00c0c0c102c0902244500101501c001280800e40510040211010000110610107102c1510b204403a035400b40d0f0004860000001e0049a400b60094410701c0001048180302d40050201d80254000000003400442c1d001c40c0905009200b00c0e00c0082400141321503d440445201242d6000300303112a042200c0700d10050064441140c0c13110014010f02c4403019686 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 365708732 1250 365707482 365707493
    0xe01020d0c030209040b030c0102100c0e06040e040606061803030e031c17011a030703020d09060606020705120307080306010f1b0f0203060a0608101a040f050115030b01050715140103 80
    0x100c0813095125070f2502080300414039002a82011510068000c0d2450b00410318114006001600e8088240000d49421381c505036601801480074010000707007400c081c2403d09008003202e080c1d42055080c013032101c400c003030880c00c509030200459a00d45442c1c2507440c42c20000c6030818410020b2080301c0e030001ca41070a101da0700f2140038114204141c104038126aa2103030002c011410071f02c03132115904000c0011078107587c4a0b400030040150002d0010810321415a41c18041b9507181e841540180c00c141401d0219281c80c120705e0807107418084c010350425032075071140e48241c440079200d07034180a802019914600d010307020f211032850303641d141c1585246081c24121210302c03200400300c0c468004c60340080c6034000c0e07510071401661501d20003084c481c400c3d039440100414900c0b5214090110300c0729924004e40d11801080440c201c401c03004501949841e410b01e1928030b00c0c248100615042080c030a1691342e00c40140c2d803d07140c0000da031602600d10002e03920300808120541b04909a43c003000030041c0107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 365709982 1250 365708732 365708737
    0x302063c2b09080a0f0314060f06070215190216151106090a03030e0a05070e0601020a0b090c0a290913020307030e06152101020c1006050a06210e01020d0c0302 70
    0xd80301d464400c0c400d01403500c120121141c1500c81d01c8190720301400714812782811401e203040000081e240914100c00e03a00010404811a2041004010700003042d06090000d040d1808000b6001e0000307010802044c5006002c20036940030305c241ca04415000c0c0d0802d6445001603a0b40702903454196100c606007804520b4172080101000d81c0801d013804091038421100041122440e90040c018003446c0d41001c0c40880c9400024080c18110302c20408403c000c9200300824900641d00e1100501840c40c0031010300c00318801541c4116400e11407406c0d000b210559102c119004580c0b0040c0ca01c4e40c801180f40080c45030901580c00c0085c3c5840841002a19038055222501d0f0b040540d045500541d100345035074000c060b0b0504030a8020800f5210148030204081007180e124416400140c20281e000d4031b041e1501f51050301054040c4c0d103070f0000300228140100b0f0b52000d044107141607032030306049582241c40d0060740040c40000681d9150560081d540c294107450884031800014081d951000a000f4082d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 365711232 1250 365709982 365709997
    0x40b04091109120601230d12122313051020030108061b040f09020f070210080f0702150606070f05010c05120c03010503120307090302063c2b0908 64
    0x12086d0303400496443c030f0220282410b200c0200207000d40c900302e0f5076400d10344465003810001c3c460000342240710024540104030b01200783c0500c081d2035100300d2444041c46132004d01800b030108034469504021070310100d080341c41c581c0d2500c0042803500300403107004035001d66110400340d503180210010903180c1021401c1400ba00c10010301c0614048201781c950098440e5100300914010841c9042122075180d802521200300c1727041d24182001510340211384a415000001c100017108602049044100c03001a560003030590b20042c05c05250b10101113542c894060306103446940046481800c001c45503240c540183e0703010000b40400f8442c2c0401801c540c11406101d180c202d440000940e2020804050304e048032070080060070909040050481c459002030110300400000040100150311402c0042683c5000c4449403403d100c0847d1003442445400d10810913420840401c070311008042c03d00341c0c0c8010007002540c0c0480104484c0e0350351038105410030903005c2d40c00c0804003c180101140580010f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 365712482 1250 365711232 365711249
    0x60801080c040e0303220501020a09060f0206061507081b010204050102010b030f0606091306020c0a020f0301090327050d0c06030b100504030b06011b0f050c06040b04091109120601 79
    0x41040207082109480195003a28043d900a000285a55a02150305651556243c0c500c01e01169503481c3d141c05c0e0b901030004540455020038081003401d42c052403645284415101800c103c0c1410400200d40d00c0da02140d2410b440404520721003800070900c21500d2002c40445d0360407204001201c514082d4105201e61170244d40f0f0802e0100d0b0a040209007404001c4007000680503680c5e990042041a003400f501c0e0b440389036403100d800c0001403214401441c0c511140130003002c0300125481042030052031105981d002c2d0741001403001c00280c1200741c07401c021062841031040382402050a0505055507440940d210b0001ca4041c1d080c084aa00c01109132440e640d014010303103164100f8004c0c2e007840c1c0a800c4000410800041000c03400303c01c2043e400c903205140202c452954040f00d103e188504960560344100841003950802100b041a00e940c1c043c19101c2c03d0030f141c44e00110340b81c6400745209009850f51500311549041490f0300071504201030003016060f520410302c91842d43e461302402002c94 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 365713732 1250 365712482 365712493
    0x30d0201150b040f150201090c120b0109060302060d0504031812020406150c060b030321100608010b09010c1a070207030c060516140c060d1a0411071202030f030106080108 75
    0x81c0020600c0882d4180e07204820304141c50b41c50460480c02c605c4401d0804421556074502840000319030b0360554004001002c00d00b0640c18980c14400f43c00401070748100c400d14940b003002c00068a4541c00d540d141d80c3d001070000340c9946e071810181d480e01d0281020b001e06142d0220041142d070f80c3c02e0a030b203c0340c0d4000e42d0100071681e01c1e0751151071000c41e42514100490941c2555400040b800e4100c003218102c09400d40781001c8580d8041e0b02c0c0c4001000983c44506101d0301000382c1044501401d000070a00c91500d0b4038154504514400750340300e015401030400c101c2801801c02d1100030003403403000017400d50402c0000c0c40c00610094035010740e40412200748100b084002462440740c4140c0d5058081c0c0d80201ca4511a140e80703100001100f403110f0700090042c07011814107a540c6001904001e40300040218030b44000d60204451640f103e14810301c07031442e00014582c4a1b120304e080d035610503404170001a51000d03546041c0c2c5140604d015043e2007080000010440c0c9034803440f524101c820b00f004492 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 365714982 1250 365713732 365713739
    0x1d0d120c03020606090609010b0d0f050f0a180201081b13030b06030715090e041a0103060f06050109030b01170a060905032106090c0d060506040803030f0708090304091109030d020115 80
    0x101790081560b11550000c001001030000c14409801042440455034001900c500030302206800d071402141e82401e00003140042090a000e81c1c083c5216503a0f10488180301100a68000303083c0e407401509242d40130368402c45008045203c0341c2224940c0381080144958a5560300e4200c0b4000012201103019015501d40082c071180c401c40520280242502ea2140d002c1c14501e807908051401041a40c21180c995860b09146a172503410602a50007000d01149814040c455002580e0700b541c0f00c0750400240c5001003000c1000200e503a819104007501070ba080c401040107107490442e01c010302404552801d41d00c3ca0420400100a10703400c5101c0125107010509400e01e2410100304503105034015100500003031503500c0406c02441c00c0030658900003281c130703104c802003103d035007007a045554141c2c400411700420450b814900c9610825070324002c40c2078039007100c01035242c0c05140304a58040b512a006040d035604100c0c00da6041c494068201c1c0c80d50100100001e003e4079000c0c0945103265103000021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 365716232 1250 365714982 365714989
    0x207030e09090a0b040602071a0105041b0c021009050603190f09030e0405060109080f060406051513050a110d0207110334030609080301060216061d0d120c03020606 72
    0x19071151440c2d0003d41a2485162910151464010411200181c1c20440c080008a01d203107000300341d21384801151101d604010600003102e2100c0e580151501a01100b6517509a111582d86131080e0305407000701c00c4480100301640c0002c1301d0f8120691104d03000c000c01403543e0300d4000c9118040e1040000740401d031101c1036100c088a4542d00e01500007401c0f039200c40350506003034202a411002c189403901c2c91035036501403941080059403801b0500e40049051200340040c50140c95040070401c40700029183c40c07540002c1d40504203600e04a507207a120000203c041c0030f16400b044400c0103811980340d84d883d400a9940c0258032028003110180f08944000003142400030744050514030701e91055400c1400701444008130442020b0000782004500c1c00400000e01074040c2144940c4075981301516035040402c06030a111100d41844038a80c4055010070a49501004c1c1c105284440c0c41601e03944ca299801013000c41c0d21502e009000d000c5d0148800300c00507070110300201c01d41d000343d00351a220b880300c4081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 365717482 1250 365716232 365716249
    0x3030105031213030503220b07082205280509060906101803030c030f030522050a0503210c070804170c18070f0e0d120c1e03110105100e0903090901090207030e 70
    0x140c60040f0600c00c2084041d4080a64900301e4018607002c02020707512330000d104107007480c81c40c10000c80d140c51880b9800030fa1813040c00261400702d580c0d1005142005c04100402c0c40106860312800905c001c001320940a1207402c6689000e0304203c07801c25489082c080d0004110b00e13000c400051044040071051380c1300c1e01c01c25024110612121441480300c049540203140c1000050790180580d000c21400204108000c2c00400d41c200c0d000d680e061382d00e90f456981c200c00140240300362001000000c00007000003084405841c0b070030500040107410a42e031a440c0c4201d4042e0729412403003120b4054080d003042c903c610701c982c07801c2e5520074502c10718040448000d0060442580c20481000d50140051101d1108071940000d5140890322881d241d00c2d6070400080720041080c80011342e030004000c0c5a0721400050000354004000c0c0040e0514080007075207050184142d200d031607002c10104a1948050040307900034800149113011550719000b0740c0c002940f14110440200355426071400050030038514 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 365718732 1250 365717482 365717497
    0xf130c27140c0912150105040c0203031302090406090822060306060504030b2a0705100e0606150c0d0203030f060d03020307151104030302030901020f03030105031213030503220b 78
    0x504112030b46a40801412a401c0301c0301040d80144400303140d032204401040000d40b8400c001c04400c0302c0d945800305000440b60042c0300c51086400c03c00400554106400c00b0811080e0305441f00d0300a80c1c0c403401c080c4024444098003e024400001e61900d429207407031041d42051841e49043c001055442c981075044a40303910440f00400c50a00042000ca900070700c2081d4811340c1d5031a800d24000d5030100c5800706a0a100c0c0b0145078100100b120400c1c04010040c27401610141c51041101100c13442038980da0790300060a10b8800d8169060581d110164802610642d00d1044200d030521400200c003c2c0d200d4004441c11002c141c1000d0000e4810318003081080b80303032601500074601e011510345581c22001e81c0c98402d01c403019160003090984125480003040194040e5020b140c4074120100020704200d48046800031075030040c07005000301c0c1e07808503605100095101e405a540c580400230b22103100c0d04c80d0300c00742550002041c445008000c0c0c42c01202502c0c0201c02450340c854441e20410281c1c0503a52 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 365719982 1250 365718732 365718761
    0x20409050a1d0106150c05010b061b0d0905150d0605090a1d0606010906120e07030c0603150b040b090418030206040c0b0414010e0d02090403020c04140408030f130c27 73
    0x8480305d42c4980a000c0b0030700301074000c00c004182c0e0203089000c00c4c1540c1c0149003200210100e1190000f8000c0e01f406054400602d074688400742e140381c100001c0351014042001e00a0718000070303000c0b00420103940584020500581102064a4603d00d40001415045004600350b0034100b1002c200c96400b14000384120016100e4500c0316042440403143e6512117003000c0c02650b90368540424050701001900300440c4070389030300d0300420300303040e0f004080c1c400f404070000c418045c82c8014000044c84070261025254800e03045915406010700245c05041080300340d0301000300c542c10100505074007081003803082d8050b0f10ba2100c040eaa944c280741551007107204010326544200680c50342588940e01ca903640c0c0d040108220266400c80d00000d01061081d01d0460159114411652680c2414061002e185114290840040c60151500c0c519484020070028101e10030f003002554960b0070181d1a41000e030400110719055031203400703c0305410301d10340c900d0a07a03050840641f45040700c0b9016241c038034403201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 365721232 1250 365719982 365720009
    0x209040609091a220807200f0616060906020403120206070e100c06050f062d06030403031503150f05090d140c1911030c1e04020409050a1d0106 63
    0xc4400030703103e10142c0800440c12404071000902c003403c2415413241d5006402c120380e5800e140c41c0003951501d03004a0500c6000c01544030a105a0351642820b00585007a500259140e41f80d41c81e034069111035000c014002440c114060342804442d81c00b1b4000d99109908212105908807070590760303604100c440d9800164180c03491081818095030141203020b075420003050406480d5900415a0700849150b82d0750f000d00c400300041ca00d031070b440038203841c20250f400c81d031144e0391030345018038030302800d1110382c040c1c5070005c0440d080603c41d6004070007503100e060b040b02011762241340050001ca09803694148043c1803030019881c91546100d0540140c104200a0401d100d1080098820200004d0b80000c420000d01405500580034021149104409800e1b9444480070f89071002c0e005c1d03034840b07400d40654429003051050fa180c8610b5440c2034103001d02e4801e046003401002a01070f11664100d147c0f5941003006220480c1c19039003011094076002c4010f09100900ca00d40182200d400303108804003007005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 365722482 1250 365721232 365721263
    0x2010f1107210c0204020d02071a09070e090f01060609031514191401060c031b05030a0516171b010b0306070c0602071e0209160e1201020c060a020904060909 69
    0x4620701d4042d848801e0900d24140800c81e00040e040383c0007000c03000003291700002c04c071040281d80852006041800040e010090800885441e620303541406002008000c01d004618003003020084448003041240c000e10907035855410007002c5e00c520340320448034451044500100940c1782e00803180410f010780326005080ea11070002c81c03014280d00c441c00c2c2e822030b650b1700103107060409400500d0180c05d860300d81c0d44040c0114540200030403d44080907600a44c18151680040c0010088031040c2c00b1601d000c035118a6201000c0315004400440107201400e400340703d050000c9203801170500b519a901c5940f20500d10141da60382038071404001c19501d9005100000d82540c09641e9803c212030107a640142454015551800001c8021199a00e080c0303020040e0421440c00c01341c21a80024610815180c3c80840d40c2c018128041c075421315841001114405850a4400d505440c100f4021038101c540c68284040000d00960000c3e036454001c505043d4045004105c50003102040d036400107802030341285 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 365723732 1250 365722482 365722523
    0x303050d0b01050702041401140906030a0f0201090f15030b120a150204030219170313050d06090510051005010302070807020f04060e0f0a05060109050906090405010b0a030302010f1107 81
    0x1c0803050600c00d043c054100541c5035881110305000b02e6045010441d41410f4002920781000111382e4403070f00000040100ca9140480c128404a80c0100400e00c0c02203e0b200585e0b08070b80d26001541e071101c2c50034000031070469802c43c01c0c9021809440422600154030284070040303c900c1801c480c0355102d100960300140e003021240c2010081d00d0f00044c1060b440f0382c00540c0048402031380c00c03c5001c41d402c06001540200003845200c0c01104001d500d4540c1190a0483d11540337803044610070504076081da418054290002e403000340d480010384401c4507c0d03142d0800200310036650b0250040a513000460740354002d10031201403513009200307a81002d05a50800008540c65840385030050385850000401415110440e802402007c10b50140c52070848075100c21a200184450304004403404100711544038068502e81010b000d0300c40503500d0740d0345e007081d9025060304000e607a000480d803200081890340c11340c40002505220f500500c04912032002c40d9115004482c0043c000108800c407540e44c807031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 365724982 1250 365723732 365723741
    0x30708090304080a050c09220b04020d02090f15040507050d09170406050d0b150f0a180605130f0b0f0a0e0a090b090f040519050111040b040f08070303050d 68
    0xd2000112031801e6101c01c0418189030f581c402c200d5856209140140d6103103452030441343e0008000190b44504c000d02202048104054000541280d0080c40428203544850401034074168026080c40070302c2c140040c01d10456241141e0100d00b004254054050030700d007900900c0d00486013682c54505000e90591705500030040b4002c100d4a5210500d132895401010b140684001c0c483c64039100e4035000c0e6090f1403000c0d504c0c81d0103ca4400c040712615860280e508005881c400c0703100601c010384a030050076040e140d45801c83c0051010408420002401c250300000810744404d2040540c0741c0c280d03039821040000300103070080c1040324505016044004064101a002c000b1181c50a110b0045800001c1021f407010340d0060074045460b88840f08a6041030300c1c205800108221010b1024030300354a59076100d0402024003140c480e81c1500000500c542504040d43c80061000c4940da190b55a0031444640c0d03200384500318144421503030006441d08081035007421640c0540701c0c1445c0c91074140080c1c0041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 365726232 1250 365724982 365724991
    0xb0f0108240414061216030f0212010e030306010f020102070b0103171c060302100c120e0f0402040b0903010b010f0503061009090c020a0203100b0a0e07020c18062103030708 76
    0x1c0c04244580225915801500b29054124010003424100031041c00104288802401007580c482c007100300c03000800803000c00031a07803c00b0f0904c035013041f18400900608030200c5211903039030a248403864160004001540219001d03200c030b62402101e0311081e400d038061004040c0c41c1815103401080810036a008555022203005d0301385280104003401c00181007115011030f00310641d0f600040c001c509002c4400a520740e200e0a11041d5900c40390313550b41d000100003482b8810040c800842200030f460700f40c05800322000090042d91a00d444504d901e03500d07004886614465824540c07118660b50040c0043c211030221a59041d1441e90390109004ca4210000380c00020000d100c000018003149034840c4400c080255400307449807040307600406140070075003e8042c61042c034114201c06690394240440e41128180c1003c03022aa4502e6000c0e411302142401c41608000c10b292003d01a6010b207091a10a01c0115841c001d40348154808210000c5510011a04ca50040010607020381c040c40005511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 365727482 1250 365726232 365726281
    0x402040e0f03030106030e0c01140d090302120703020303060a0b0f1b0a140c011e020d1103120403080a050a051513110a0302040e06030309030c09090118080a030b0f0108 74
    0x80704504081c2524603807003640144000782e562000e808031038606100440f80b4000c246082e442e038603d82d100350310452040031040e0440c41e07034442c620020035000784412465104a8000b0544440e00750501075103d601c201e0f2980c1c4942000707030000c610b880080f8161074050346d151f030b481d80c18581000b86088210702c00300610742944c0300d54a041d00000e20003080c260850080c0f04c018007034401c1100005489941128800c1c00c1d001031640c54040c45075400115a10005500d29180c0c1c00c20030032145e018251304c00c25100e029039494407020230040c183c0083c1c01501030035107210204000e41c0c420009408403002622101c201100550001e0403d161603003240022006007280000d040d00d074aa00c41215600c5086004040703a00810100440b840d003000403544002c040d400740d840c00043e1000241c440307a40b0403445200d825a0700229000307110075803201020517081c0009607208925801d0018050308400c81603400a03050030300780440c0f42004480c1d0569034a0686407640c0f551251180c902c0040e210070740d00500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 365728732 1250 365727482 365727493
    0x112080405130e06010938190f0b0301080f0708060f18010e0609100e1908040e04060b1f0905130f11040e090a0f1506050d0606060e0a030b0402040e 65
    0xb10a41d091044c507000303020a80380061520f007501c0b0031568201c41801c0302032000c50000c0180401c006484030000040b01c0464400812208030003103640e02e0600354000d0704000e2450308c2c0200b44400168011030607980c402c0c085641d40e941c081c100b15600c020600504c0c40da500813030f000c941756000e0300c840d0540101745010440d03000700c0c400c4003060860b00181c81e5903005178041c0f024444240c4050102d014000e83c0302c081841031800c413030130442c0d85000c80d2000c0303008598110100301c140643da000356405010304040c0e9a400c0d0a03d4140030010b0301505e981184140110503030701c0001d201260b040107501c1c0c0c403034a41c0c1e12041d140004022403112012070500940e900c40c00d0920005150384589a101130011005546841c10500e40301c0c03460704c0040c00c4010b03503407004001001040101c1000100303140c0c401d40701360500a000d030010018040710780c016500840045002c204211560f0071403003c0c0c2e81f440e90f41c0740d68100c00e0b00400041308941d00c8003404120341d200104025080c1600405200c4030600b00322107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 365729982 1250 365728732 365728751
    0x1140f041215020a0e09150315060616080408070902180d0c0f030c080d050c15070c0f0302010c110105010f0e040503042c01050105090901060818010203150306011208040513 76
    0x1003c2c3e9004050950008400c01c85c5060030307140140b211508003007414440c8000c0031030540460b640c2c000303215440190035411000070b11a60b440307804944241442c0c118078080c00d401450301c41c100703800500801c030072030285103400304882e075691003902c5242448041c1c40c0003c4281c0d0781402600d52030041d0680e1070105509000c1a00c0e12915150b0000b1442502584006031402c1c2c0003c0c244041140500100841000001442c90001400780d0260030203600c40c3c1d00a449800e410b0b01c600195010003071002d89041c2545041c541c040d48401541c004644919421055286555003214024001e50b1204034003c0c100b80a658941ca0b510b0381d10034452001c5074a0a6140c07107001c10505a8800f2b032840d01110154130b0801000c0000b00c0c240117000c00c0c00c12a0034000f02100242017600e05001c0c00d4100000200010341c0c400d01401141c0c0e40c01102e2008560700d090409044d03400035000341c2054000d100e0304000013000c2c911013544401d6107801c0590b0504103820300040040c10500b0700030501c2d031a84c4410323069 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 365731232 1250 365729982 365730023
    0x1216020607080403080a06032415050a03140f1207260a03090302120f090111060105090f130f08130f0503070e130c14010305010b13091d03130501140f0412 68
    0x124034101c200040c0c2441c4034001e00c9c000c0688041c5854805140c1003084204030326101c0800500035240d01c0b035000203150080d10320b90f5152100ca10740c071800b02d115240c1c43c0716456402c8002400e1442c011440901c6c160307051003084c141c6102c00e0b0b486007803080080000404541c800d5110801d501d12034815510b41c2c00c10300c241d0140781c1d0410382090402c8440041c0d581065a0005101d202250340e030b03800350045601d404c00064210600900402c500925880040c5150700d0368404d501c0c1080c0c0c840154000000300d800e0134140381d040b40d490344801d1101c2500c0454615040b104820031541c0080050607600e00b03000002e15001c80190040040b001c84101107000514109811400b0300b0360025200300b9030b00d22000040a940047e400004000c0f800c0044000c0409035107010000d8518190f000300344180030900f02101c144d1000d201c02d15500011454806140024121100310b0390240d803000b20003108104000031920440c42c402078102c10420040000e022200a007802c0785000752600c04c11542d0b4520b02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 365732482 1250 365731232 365731253
    0xa050919050303060102070f0e040221010203070801080613020d2604080303190203130b0405070b0d0f11030601021515180703110408070911070501021216020607080403080a0603 78
    0x2207030076400110402c5165641048000010310b80c0c260350741b4200d49008804180d4040140c4080d010754011407014003840c0c0c400f6018480707420307010000c40d070b00e1602071030040000c44280a10781040c0036280128881c02010621f46104640040c031000c82c00c0603940d01c4040d550311f0600540c0384001640741d0701440c0181c04c2c02030801800c51401440d500e1030b20010442c03003101d0000441c0d45152040c0280901c450703084e031000601d180c0c801c1e01400b580c1c80e181802880c080c0c45900034042c0c030304000380d110400035036900480c15001060105101c607482e44101441a07000c2103441c140180d0201e0000f0f9442803c1c5542c2c01d82000050b003440808101000214803130203940482c0318a40b160715011700c00700c0d590511424004c0c0c0050300242d401c150034018180d403118024803510007400e03180c1134030b0100041c0c54012544202d5220008642c1c5901c05d00c90001501c1d021a80c0c02c04d4008180c013005031880c0041601840350305a580d40b0b0400d56129035003540c29500107010b0040103699800080005a544200b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 365733732 1250 365732482 365732533
    0x1a1c0218010b03040303060806220c0504061508060a0509061309060f0902011719020a02070b070c06090e090606040e1005010f05033f0f070b0411030a05060a0509 71
    0xb80c1558a04d01401c010381514159403010080f640200108400d840c04011450356014501108010451581c20300d9003a805040d048258001d140100010340201c480fa01c10b8020304481d2185032482d0f44010400003041230510419400408480004001e46044100c11030700c0541d001000610030f405854030300480b26019582c2c64503940e2454a03905660300000184541d0480400d655078504d01a030780b40420f5102e014000441a03000b06091103164001e0102d4405001351013017250726030021f8103242080e8021445004081b501c580c40c042031110404803914400c800f5100204030700e03110202071100402c07020055690342c1c0074030170021382d0088185c0103881c028200181d921b51013908220400d820600c071075101031040030306450740d032400745003200a80814045030a4211001c0310807880c41a07880c840c0c0046003007480c0300041ca41007000031204949008a0003000d030212210407035014103651b103070701c50300c051700e1544240c0015944403640d40045501074210380548081c0f050078805408801c0c4a8403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 365734982 1250 365733732 365733749
    0x10b03030921010c0e0a050d0302120901033b16050d020a0b0d0c0206060303090a140109031203050f0a0e0327040905070e0604020306100c0201092301031a1c021801 72
    0x1c4861b16190100030f021742000c131503804003c03505a402941d0f450440c07045944c1c4000100c0c0d8411560f00940c44102010804548081c076030460000481c07007001e0410480528030b40342208a060904006805c800401c0c450300790049141c14003040001c3c6694040003240c1c0b01940c241d001c0380c03030303042c8102821380340c1040580414980b0b40301001a0404034018001ca0007540103102003141959807195070380072238071102d01101c2c5259514004a0340801a81c0015140d00c03c0e50b081c400441da4552700c264450304899103203410036101da01c00c64040c6c5103405a604d0703903980103000d1000c051040d1a54405010001503600c503040c90702501003002e5070307661001566141c200403002c104001d40045410784c070002c115811440c42c130b400400520700002d50303482c560412281300c0d10581164083c8102c0c0c8050700010080c04080038041a828642202c103a0003d4002402c010200680c48810b041d440c844030320041c000d18960074180191259082400d40503640721201c0c80b02140320440c030b4000c01d4040c01c00e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 365736232 1250 365734982 365734997
    0x40804051e0a090b220609111809070c0b100302030d0c150603170f070b10150c030801060c020d020402040b03040b090f060c0d09020a080f010e010b03030921010c 71
    0x508015110b0300395401404900d0030b080340c200c000d5407507101d10550120181d941805001e5500c08030401480c5030340145117001e2900c1c910a400c1d20700c0130040c02142c209462a0700100d01d1250600070110415190780b800b040408801200203081d0854103580040b6029070420041ea0341c1c0c000918180c81402800046480c500481080c441c030860100c030001c1d4440c0d02480414990307500d40700c14186191802e4122500403e8103d554030b100b0003180c00681e000b0261038a14240b000c5400640b002074071038038040004021407050414000d0b143d4000454168075092102ea103040000d80c6d858114a1081380d00014100f0041c006031f1f41d910250000e4400c0011413a00c9180901e068854030381c014000291940c000100044025030020304940d1107006190040c0e1207401203800c1c1d0020707240490f402984001d41c84c0c4003264070800041e5011680d5602e900074007070203030030001150803150002c0c042605a0001c0091025500f418120510f00468000c2042600500c0c4a0004d08403160701807000b000401d01d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 365737482 1250 365736232 365736289
    0x6090806071b060e013b011112091501090506010f0e0a05100e0901030602040503070b0c070b0f0c0118020922110d0510060302040b04110d0911030a031709011404080304080405 77
    0x6105091b0403030460001c005440d4262031000080c06688198900d00c0c07050000541502030a0000e0842d840d2041440701c1c0039619010407030003811003200c0d524006550152458505ca104504a40310840090405000c03141454144044464001d080c481844500e903806021502c5115a01d03001710b009017001a15130b8105420141885c00c075500c665002c01060200030290000441c21204440d030070f1a040f681e40029280c09000d83c020249a110503501c0c00045920f58103014502c90701691084410044558032260301e4034a16400d009109502515400c00100060003507a08039405940140300311168159a9203462400310399000ea20041a21214104110f00301809500030060040302c0500208035034003099001c43c052524007045a94841d55410103000300d80c8800000740c1005030036600c000c00141000740c5004010600000f58410035400281c2070300061140c0351003d40c025580c0c4c9865103c4c1d45618000382c001410a44086801708000101c4d0b0343c800004d00024844185010030300980c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 365738732 1250 365737482 365737571
    0x20304090b09060603011502100e0606031002041202040207080706150312140a0f0e0a0603150815071412041a0a0509071a090a06090806071b060e01 65
    0x41c03049008101000034082e150703880e00d06490554554021141c510b03c041c0008070300d0004200800e1079480e1800724081d0400001040740340c0f05440960407140c07803400340c0c00b0034070480c4103a01c10b01400100140e102e00c0107103419002400e60138091182c142c14400d2949070002121002500503d040301d400c0002c0007000381350140e04a010500c3c0c00c20b41c0a658810000b00d455100d03000190017003001105c0400d1107940a4a0b0301030091a000d080c11101589907140607001b000c905100700c49002c0e00510020341e603a130010350503400c181001c252034666200c00d1000e603600e418040484207204020710010148034000118544600d001c5d030320114030751034000c0311248090005020300b0801401c190400581a4001404104641306d80090101d441c0c0c014610704c0c220300904e0002940101707180e000184240e80078801100f076801010583e086074032580d105480c03500c0800304071071501d0701020956010a1a41c0d000400d40c08035140040b0300ac81c400c0c0344420a9603220041e5050b00c0d11310001c80c401450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 365739982 1250 365738732 365738741
    0x503071e02010f1e1103070c06090f0b0906181503040302011a040510050111010e0708061b0a0f05090a03050d18080d0801150e090408090f0a0303050304060b0411070302030409 77
    0x1c0ea0a01454072010103890741c40c5104d14424a00a005542540342c0c810f100420031034454640041c3d820070300c0c94585030000c080c0c84480c42060941000b85e14040380c04071180045600201004005500e0300c015882d0300d01d014018031600075489a040c03064403420303240141c011842980700782d00000e03080511129072416100050700b45070143e031030b05041144020025801406070b8000342080b1601c100c40c0e540040c00b42a607904450284e01070f51000165a620018071140650708101c0c01c2c8503480c4000e0310a680b00d01a003c141400120003428464000340160000c1014110140901c85010b4036901e40914207a4031306640400150a1441800b4804192036402c018010000c0601000304400348001c15400341030280350700840b1290600c082030350040d084c125007108050148a56840c240c00c2c07100c480d40040524500929050061250900d481104030702501d9143d280c0c14150f85440c0c50303460090120200d403039040fa030380d0500d07071104010307040207441c0051190b8021590b481c01c1c40380500aaa = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 365741232 1250 365739982 365740007
    0xc030203010e040f0203031b010509070504020708040b090406091e1406061209030c060c04090615080136021804050618070207030206040b071e030e06070503071e0201 73
    0x1481800144440c041000c1202c0e0031030b821000d031a0310b00025000003401c6200300802c01850a0584c40c140d10b00020640055105210610070780e0702346541c0e20140800e901c130705000103201c0241008207000f07501805001d00341032500a40001340d21600d40c0754240171500c00d160030484010706000d16222051042c0a102040505142c50088606192022900034002c2170072080400140b803001510303403071042099802a40c0304100315206414080b080c0c090552040c041d44020900313015007c00c500c010040300745801e40c0700b6540d840e004d80ca804100080311403440c030080103110303a05405802400e00065a42d50038209074200590f02c68141420080c003010b080c044030701490a0204100c0e0507599003064102c0031941c461000003036a0b4404040341010340b1f6800095000c5004240400c0821128014003400d43c4148100c82c80369901010000c500c00c0305050040c0021841c2d080581c1c41d08059000d4143c031403088045074140301c110f6a403401c211149e103207190b11707584024230102c080d503920030001c4044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 365742482 1250 365741232 365741237
    0x90f090b130605090105040b04110301090e12040521101506021b03030d021b030304120e011d040c090803160506010b13121119030309060e061b010204030c03060b040c 73
    0x90f103010049040308805101c0c02e4400c03540e52120030300c561141c1d0090801e42c4003000c07220381c0c1d0f5a100d09140c40181060b90080a4500c6802961031805c1c00c05000c07a0103035540100000c00001101c07403200f40a4075010080000c50042c0340e0b02c1d1300e94020300c2c05215034a120309104440d00c5400c2420080c40d003441070308000d01c036000d003154062464070040100c0da120000c201c009603407914840102d01061514a8076000700e0b00c400010401805003414558401e22191ba035000110707a5030302d00445400417042d0503104400800284020709141561041c0041b120a00703106030115910341009085d600182003032030070504074600c45420060140202da01500340101c415003801e4590981041251160082003140700c4072100110074084000602078540a000707040152150b49110140b00c852560310044001c80c29900012031603500902c0d01c50440840a0044c90801050a000c018200010011015555400c00c070220109000a074142c1c040d6000311f00210740701c10540207000885504d413014108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 365743732 1250 365742482 365742491
    0x3060702160918120210050a050708060904020a15171008070b09040f020412120206090a0f06060b0a0203070506220b0403140318010e0c1f090f090b13 66
    0x2003801d58819580709403841c1210000c0e0381200c20f04201c8851900a9010b8a0100d1000300d40c60076560015401303030300b40c415140500c001e4986000180565000740c4261001c07601c11030005071241400004550300c54001060010810b50b2680494140450f1045410000b41c030f890110603c19150002c0039000030301d1044200d0700030300d021529a1944028020f00d4140040003e84038110b40e141d8000903014202c0b00411907070b03565142d20001e51049a00011181c14030300f03800313000416001040382e030301c600b07002d5000c7c0900d8003c3d036544d00340d40c4040040031913665603164400b24608400d84080e050820480d0010766948030b03282400b520b4400d008002552422400307920200724a07a10032a48000c40d804410092140c0302d07451300740c41c469805040400d00010200400500d0310304080030110100d40000200030741010350080c2911400790344c2d11560090003031105009152001c0b80c11064168151800900003500c07101101640c460755449003c006854500040b40e0740780900303408480c0c139200c050410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 365744982 1250 365743732 365743753
    0x5040302011d1503090a0c06030e0c03061612020f04091e180311030c0d03020d0c0216030b0402060f0a0903030e1c0308070c020402120703050c0313020d02130c030b03060702 76
    0xc4183d01140c0000c16000780110100300d2007142000b071422055805200b051040b41c850000400810440da814022403103040034000da141070100d02d19000d003074101c146001f5400c80c20701c00e07510307003c0601d1071071690b580c00c00c419045040c1810103040902103113500840e80d14042da4440810315408034050195500d4101d012440003c6d200415070190352500703040b0301341500c105240c0c1c00c601540c4600b034400d000e10000c0c110700b00d51550041c10300510a1008200d03401103d0401c981e03410001c45d0b241c00303c2403110800c0c008516000d80c46903016100501651030300704a2044030007690000d01340c0c4008214480030a10030176030420f031110100101650005000c451186844659242110000e001d01100802286e06548208265200c40e07401410540d520b1641003400c18091408907080e10002c0d180601140480ca10281182d00516424104011038905602041003c101d50b000880e40414081c0074050401228040c03602880308540300025410164014182020070040c2003000319001282c01c00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 365746232 1250 365744982 365744989
    0x406111614270709090b010503040f0c0503030d0203150607021309060e0313090e0c01051b010b0d06140c1911030403050105011e0902280306030206030705040302011d 73
    0x5048904003850030340000c280101107001d80c401001e940b0409809603038840074446002940030b001d0f1160365159210035940391000f03001c903403000300c15600040082020a001c203a0202c14100c0c07e42c0948401c0d0075907652040000d113164401c00c6200d440580100c100404400121006504181d098070658039180c0307141d00041050001c60002910255a09461424480b050b806041c55480d03180440342d8891004400091150252151441213801c1603003c038150840070860b0040c003081a189d19003499021081d20031440d4802000310a65980c0340810411903940310b03000e10302c80c0e0040d41c0006542e0300e2400491000c03940100450036002c020020700101e07100c0300301d495a00004620b400d02e55001c420354114214821340d0b001400941c2800300104030408080c0390b000c070604009248503500c1340d840301e0380c0059005200c84201c071003090b0401005080202c2ca00301c0d207078150302d24001036525220781c00140325070815107401000800c0400c0600c01c6580000400e11078620001074445100f2141000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 365747482 1250 365746232 365746273
    0x150e071409060307080a0e030c0307050120070308090f1b01030e0d0909022503020f0607090501080f0601050705150709051c0210050c030c160e09060105010302091c0602040611 77
    0x1008104000c030780010314030051b241c0c88143d180e500c10090340e50780d640040306150780f0b42041009492951a0a414000c40104400401148005011442c1c01c0400b191420740312128018086a51030082c0040684002001c0c41103852100d405049800b207040c1200004040b106411007e401d160700046011035580e810100340780c11502c8100000d65940350340044102c001d240501d04041003400072000074205900416105d100c0e503070007001c4481c550303503228003100e1000b5103101d00c90202d0410008034050011007295590700c2101810000e103401540c1d80c99070300d8a005007003d80c1c01d02c500301d000d000c0016030240c8000000c0c07901311445800903041d4040c5000c800000d440091081740980603001d070f589c0c0207000360f4601c41d01d11029291203610340b01000d41c81d4400f1000a407451503030500003007400d101d1a00300c50b0003034484170000c0103541c0c205401500298061804140d2089200c10502c450f900c03001494003903184940c1e03004d608d4030320f061006866200072568102203500100c80381c8240c03045080b407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 365748732 1250 365747482 365747491
    0xd1e0503150f040b0301110403121b0f0f0b100801051005130c140c01050f011205060a2703030209100507030f0804060213031103120412030e0301150e0714090603 71
    0x881c0c602c042c940e40001001000800c00d251303003550030038121620130390031078010b44100c038021010220f2810720050100c400c80540b10001c000381018642c82c1c80480c03001c02102e031110380b080003a00c8280e500380d115a003c914049030045504e800c200d0080c01a40c1003801030b9900120202c5503030f00c1c00d900700400202441c00c40c0034810042982d40c203000747d40d01c1c8034086c290784810003203c000381d0f50f20491241d503000e03103401c940342c2812911000001580c00e415818483c0f40a8000003c0d0800e45c45612000c0083c01d0360301c55003080000108030407140d400c0103524541907507109441c01641c40c18408140440d4501008501c2d0034003030140410f0021903001040c1041c1d403030640c5004c00280d0303a01c0c40c10800902a2051074082c904d039800d40401000800c3d280507040300411030444096415800702414140306d0350141000482c000d0b441800024069078402090050050002c2810600003c5821842481d0b80c0600d285081000502114507000b00d804003480301811092441c21140e1030229505110242 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 365749982 1250 365748732 365748739
    0x303041a040504060303020d110303040c050d020406170120030705040b0a0309050703060606021605060405120a0f0302061b070819050c07080106050a0806060306060409140d1e050315 80
    0x400800802001400701d40c0503020007001003044503181d081c025038070a0715110a0003c5112003960864000002003070320310070350f808045d10b082c0609180c00d2001e07006103544100d0300551241c0000c10190106071010400741c00540c000550407403c3d504101c84c400001c44450707452102001401402503201c2c5c1210182c0b0f203840d201c0ea941301c99101c0120002c0412200c0500300f400740038404410081d0941225045415683c00c0f02c00d6154032111550300c001c4c213031280310b5218104201c10403003401c0c818260550803080e407040e1080d9a070346440302000d9052542040380160081410415451000c041c6000e50140e11a6a982811151360b1880300783d01c2541c0c2c00e440d840b45031004401045c0e2160084801d84c081701c3c02642c40d15a51101c1c1140030340103d004441c418038400c0404600c80d1000a405882400001c00400380e41e1200d01c04c0c40014007040e0403d0310344c2e410210710a0b10301c400400c1781100d020110340c0c5000c5440001d00c0d942001c200e400b01403000300b2604006001440d0450021000c10000c200e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 365751232 1250 365749982 365750009
    0x201050304050f2a0405060f2202071b0e10210501090b0604050702030c150a060f060504060f09031a1914100509040224040b0d0504061a030304 63
    0x5060542c0f814607000710720303c000e11800c0b074400240603003044807a0752110495000040c090910040109860f000c4070300b036030005000300003a22039140c1414007181c14483c003444140050302441c90b0f18103903403003540d0965010780036005c1004144201c0103448002e02c3c42c80603801c101d0070035406181008403140b06030740b444a0401c98000a2001340e6240380c800c142c0c000000c012400c01d031724142481c010300b1200a40b0883c9003800244005001100300d503004101580a071882100c1c04d4000f601030000940300001c15541c40c0400f0680040468020b000f82100e138480c56241c6181280041c100a12200034031304001c035003982000001d55651080030020310040c40004540c0d1095502c0403414000c0c1092007070141005030398002908042141405039144d101c850001d540c0b2042803180d07084090750000d422a9400c0c0f4078642144600300380c0c0007805005003269203001d50340c8403000240c0c0c100700c991800c042d680d02d00340001c103e590320809040201a40c80c0806800800c1f001a4403801f83d4891020303802c5c4807 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 365752482 1250 365751232 365751241
    0x10b190306051309060b0f10031d0d0203030919150e250e160818030412150b0f030d0e01020313150206091207060c3b0d0b0402010503 59
    0x190700080041e24018050354050f45400d8a100c02408015100b51600340c50100240718a0a1104c01c0d00100714020300901405003c40d0000c03001400d240e036002103104c1041040b8590b44001b40014810b03501070303a0041d074032030501080355803c2002208003403c0c42c0003d160003500082e0044040102559140700c00501865030040c80381c100303014068020030001d010410500742c1030000304a4030607180c2c040c0700c1050aa0350110b507030b454160088140340102d010040041c04907418040b03e031900f00303001c009890400e83e644081d101d4030070380007604a5581c1c0c204480c000c0295264480c0d41d609182c200e40c0c0c00324219103400840d48484100c0640410400841101c091070390080040f2500440c590004c2290547d80740c0e0207202001c80c517098030006008580c0031890003000022481d406505001c08a894000c640e40d4000040640b14011018004040b8040050b6854603104c40000012010f401c007007140d90361040c0049507010b06260380301700640350208001c9065034040f59481075081c01e01d20399076200e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 365753732 1250 365752482 365752487
    0x30c0b0415060801060f1a0909041401050c04150c030e012708010c030b010203250201090305030a0801080d020106080303060409051203040305090108060a0b0904200c0715020105010b19 81
    0xe0080601c000c500748036002440341070560011040713401c100340740d25005480303980c00120098407400400004205114083d800d2411620a0341c11911400801518103042440682900d2088603041111800403034100300010003121a0000d4400c03d00d08000c26080c1d50b600a84204104a5028100200341c0e0300d4002418280c3c2002c46000007019801010640e52000b03940030b030044950101c000790610340082c440354000400d031198405403607003601c01c2c401d898416220440000c3d20a90420481c10300c0000407481c24002002d00c8034072a62600794546c148007441d40b0b04409141440116803410742d04001d022804019aa081603040701c020a4103941401c00074904418000051541600007092004141d0000300800082c2e5081e00c1e4000c8542d074060400400f84100d00c10b5031101a020420010a4a49540880380c0d03070701e5420301c242c04450b00c41103105040e08030660b026900d5000410a025410a400500190402c148001d00080d810072006411500480500c1c520201200030300c00030060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 365754982 1250 365753732 365753753
    0x4060611031903111b07060e0a090c0c061803022a0f1519030e03031b070218190e010509030703180902120414070338011719030c0b04 59
    0x542d009030080e102d9048890342100d5038003844001701c40d841520380002d083d83c001c001c80004520024013140826181c429a200076180d80a150710070090114401d07000107445100d20024140201802c070300804580ca8060310380b840b013140b18601511460382d5640c1e24160802d40e5a10848240d803e152a19907803000303e501462444001c400b0044089610019800c080313201c1c0003100e00c6d9990511044d0807400c1c1094803440b0995840c0107202c140320444500c6076040c0010403030035201400d80c041c180d40768001e00304100030030f903a00b40c3c10b83c8805012038290081d80c002e2840e0354082d84000c01490030b007000c400b5035a1180780b5008052102010380081c6220161890000815140009654501c20741407041d004601c00c55040700c02d10242c1400c00300141c8005513410580e5405200801d031039a0001d6544440c8010411102d404004090882c84814a480d11300b8020030000207446040901802c0c40c3c2c0c2411a00f505464211920b07000e500c0110742c5c41800340c00c6040d0840c48401c0152568109140290f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 365756232 1250 365754982 365755001
    0x20a0602030a0b0a090608060705090f131b0912240c05030610020c0a06050c0c0a0315051f150504080303040311071d0c1809070c0204060611031903 65
    0x164030220801125510b0740d084000300c1c62003202c0c034005141e200d55800e81154460300074004d540e8445000245200d00580c01058110402007003254043ca12000154203405450341401100342c6800314068488032000d41c0d91b816402c0c60402e420154140301080c005e41c0740341c110180c210721519290380c91280560804e070000c001901000d1040d5503052001402a6100b0b580e40f90181c030a000081c0f000070320108000b01b01d2080140511485071030480101d40a4200c040680024001d08020f42d800b60f9414002000075803180740c001c0120401450884115600103085026048181d41c00f010038580c1312442d0019500c905041001b4940790003401c8559004a8014070040d1000200384014960014804004d5145100850709899207031140c00540b0206410310144107000d440201380c210041102074600140311008407c03680d820900000d000030010381701100401c1c988000b04040d03060a0161700040c00c01414044204a5075140280d0b030f1381310304440e060500c054000d554040794402e07045010038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 365757482 1250 365756232 365756243
    0x206090d0f0f0b1006020d0806060c0a1a011d0f0a0f0501031a0c09060702120a050604081e090603060f011413060318080412030c0803161d090a0903020a 67
    0x8004481c80c100005041c100c0d403c0e00c0c48001800000ca00c51141c0301c184090751066400f6101c050032011040d0b61042001d40300310750254042c0240b829410b0100886003829000d0400a0020100701c50030084014040e000400d9031200d602820800001d0244a160000c0d03d29440203510754800491200510b5001c01504004e800c00c8000010b0050000f02e1088440c425040b44003d600d802e08030b208148640d85849811502c10310020b005407a000022890507501d174004d0f100c04c0101c0e07a480c10300380002118110742c404c0700420300c00000d401212651703d03425014442546400640d030001035050100520703041c42900300c241d0203005a4490303020800e50b0351403c82001d0311074103044504607030010140a5031000a150603400c6401254070300014694980101c5035074a01420030000090300f0340d0f118130560610030035281c18000102450001c620038013805130809135200301d0203801042c036072880518413008480c40c81c000c82d1a40d903021400e03421500e00040040c01020034a8160b042c8110140050701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 365758732 1250 365757482 365757503
    0xa03060305010504080405041b020c10021204090c0f02061302090405010902040908310b070507080f0c1513090e0c04110703020c060a02060f22050106030209130b040206090d 76
    0x400c40c01c0005007060b100102e03000e01181d2070270b07244800030703c01070114900141d01404091405061000d070554154001d441030b15005c2e10b5040112140b50f005034041c00103e9590099442182d40c4030a80f50b9411215101820813400c002d1840704501d070b003902010384581e0092000c1001c00c08250b200303802c00c0380d0140083c000d074201410100481e8003c00440e004010708a081114002075007442d400101c4103944c3c00c280700c00d080c80307004c4500b9001203008490700e1060319800705d1540720401c003035140c0c80c40d014000d199800b9220306000013503180408195280d034007070200d540f412800311108400d48400c1107000504c100007911880c640000c1d10000b582043c40c0681403000e840001004021303041c0179400301e1300c020313803000c040c803207e441901201c1006801000114000320007015581d900490504aa400d8112101c1c0540701d0007020700c001140c1c00e80d5184000c104506040815541c041200c41a01007210301940f036500c403840005000034460700c40064000070741c0e81d8034902500038075001100d044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 365759982 1250 365758732 365758741
    0x503130f050c01030e07030b150303040f030b0402040c09270615120c050910180e0705031017120906070c03081803010510030308090705130c091203050306060a030603050105 76
    0x5840b11400b5049500003410f02440c42900c40740052840d0031a0b5205803150301507034401031800c00e80803243c80d41c142c1c1804200800030b50720010751410009907014204100c40383c28a44104403c0700c01e6800c481041c019440c030204040342007002418200d101c600741d00c126001d03c03810258010702058004044a02c18209100340482d48135414200c000c905400170885842e013074409031045d02401402c5c2c1d5211180d2002042c040d84101300e03045003c1180c003620080191180c142485000c030172039010700043d50100c100042c50f031200c2c11700700080200070f01c207601e642ea46030303c1291100c142088040f40b402c40040c0d003124944500048880c07107a0420300d4900043d8591600e903045501034040c440c00d1078142c240844051070103124032406111407011600d459441c555003900d181000410030580742c0118200025a5180d19940c0380c000d03603003140001205e840d5480c000d07094614640103804030103d4500518006500481103036080790303044400940741c070000401100a840c803600014015420b100920 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 365761232 1250 365759982 365759993
    0x102301060e0d0c12031d06030403120f0c030b09060906060901031508010906021306091d15120c12070b0f1308070905070806040212151503132906010503130f 69
    0x145505c0c400d995001c100c401d03602145240c0c204410403154000c2080001c00c000a01500d800341036408030301e102041c010607840082f070843d580851140086a155000541c007868858056584103000b100d0109090404101044c8103005400c1141d05141d91007400d421311b01c001c0e100e08001060510024000c01c8005e1420744041c1d0000b601900f034030b445003180481d845020300100c3d0143d51400d01d4100c1e03400c0408150b2036103150054941d01c01c4046000e041c0d80262140044902000b0400000f024a5100b841c14400b0122045038503c265420482c03003070000c0010001191004140110003948401060710380004000c010b40c4003081c03d1044440000d01e03082d240d000603208024545801c099a65014107100c1680304010031a50046030b032400050640c48003015000c030141c000340caa050f402009070b603d414140e205503440c1142107078100d4031004124001c8081e00e09440b6060024105511541c40ba101040003e03190505200300440042e40d140700804000c410f80341c000030f61218102090406 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 365762482 1250 365761232 365761259
    0x50307080d26060d02040207050a06050603070b04060c0f1a01090e0105061c1401021b030d0501050d02100309020f04060b0a020d05040617060a030c08102301060e0d0c 73
    0x6600114020403510a00b00c000403444003002a60081d2501e4503030b651100304070b00d500d01346104aa005038284040d07030104804000d00e505081c410313030300000ca5081440402d45000c1040c0e000b00151103040109001183d03000c0083c00b86030750b20882c0c8801142e003c0c0307050a052156140241c50b42e01c01000000303500041500f04000050701d0b13000030001920f07408140040070000340030090203008000451000a022189200a4400300c1d00005090454002031452001c003210318900244e480032901c4030300a1198451240180400c840c06080e541c020f40c0440c1080140841000600d5541c0c82e000c0d0a540f01c41201c251030748001401045080c0d2200000d40c000d8008405c4000144103070380a0720001c501a07022a01610103a4407104854426521b0360080000014010340e0840208480000001d92440308000074202c40805000944482d00c10501102c03a00361042401c000414440401c541c404500c890640b2207620341110342554030320100d250700c015420000c02400c00f0180010311079404004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 365763732 1250 365762482 365762503
    0xb04060b0301050705190905090115020c03010504020f0d03030e1906140108070b0903070801020c0106030317100312030e160f050105030c030f25180509070207090b040605030708 78
    0x404000090046041c03500b200c034111009004140704004041c07000d801160f00044c0d140862030302090300d41c0c17224041184400d0030b1b440008586610843d500160f6014090014405001e070003c1240b8a0a90005001c001c3d41c0064035005e90340d00c04601040c54401d07081491450043c0c6d049900e240341601c00c4030f6940d181d854041d20028031b0b251f000c45001269041190480d00f003030b4010300b41035042040f807803400d40c05050503d81c94032990900243c520b01c2030020b4401410500e000103007080c41d45c1030181c80d030006085001800c9030900e080004071202c00d040f120503290004007240805407199425001404001c80d000490311402e201a1032020000342c11000381c404040316285034a640300010b40d800e000a0301c06014071842030001980c81900c00c0000c41d48059100d0848a14402403450743c0748881c403a116140c0010203201800b00c48401400e02500200002e44400c0510b20380f0000080d11600b0038000e00c1c00b180c1e290100111555141c1d0000ca001e4132000301654502d554525825554112241 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 365764982 1250 365763732 365763743
    0x1120212011406040f140a0f06241412040c150e01020c09040503090604060e030106060e09130201030605031203060909070e04080d060906080a0204060f1a160b040b04 73
    0x1028803038002810b0040d4000c28003800c022101c19140c0804003c0a000c449000201c0150346091045220040329a2a80510061040042c82c5801400c001058408541041e08500c242c0c14042d029074811402c601841c545624010500140b6404452220f01c155403440020840d1001404207021138015918122000000c1c1c407009549032030419240c44402482407400f40c1c001c120b890324139041c002441075016215005891408411030300141c2079800079007101c0b0029400c6581c00761241070900c503440c090000b90620b83c03200605440002c07142c840080600c03405003c200640cd003164001d80048010308801400e94900b8602140c040242c3d80044071924851410384001c200c121070045452001d50b0703030344085000c0d20382d103070780714004140e1002d004a04c210342e440000041e02c403076078411040a858544040c101d40d6406004110580e0400c0d0454100010405030420030110502064104104030f84941e44e12020030502441c3e00404811001d003106270389034200000c1000d64042144503c1c401c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 365766232 1250 365764982 365764999
    0x200d0f05011d060d020607030f090e2404110d1505090c0702060315040c0807020d0207061b031103120712020a0e040f02072a08030310030201110f06011202 68
    0x2240206440c030a1240200c81c44020040c00b0684551200b41c0350700c28000340034070407020681d03400714040d9401540183c0000d048680e2035401c4a074400340841c01000f820b803c101250800f4941031030491501d444d0031810f640058210940c64480390802498100400e500e180c070343c05080c0f0044040c000700d800e0000a401c4040c000b040700d1a00010144c00344c44101041070a00980750700340011a4400b520420f070b821240029080190741d503003d40d80101c0c00c00d60761300101c7c2c1098000a864552946543c0c4299004180140300300c56001820480100154505080008207408c06031071083d84918090120700000582c10031107180c0c050500e00954075903036140030711506c0c110348400b02c0c0a00744a00e40007401c5540000c5003031400da00a1105440d80316001840d04065940d15015207014015202034023086a81040c5200403d1541d03a0081178400051855131a105103002005c02d040e0100074148001d0381112104144100900b1041113203d0040b202156111030350039510074001c40040b44900c420 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 365767482 1250 365766232 365766251
    0x90f0c050708071101090f080a0c06080603150c1b0c030c03151501090810060501080a0c081b0c06090a050118021e1302220e1012030201200d 62
    0x10030885921a8014107040d0030b010740e941da0100000c00000c0c410f41003002c1c0c00360101d5500e00c0c60800a00403c082d0300100000e86480ca41a2403140d4194000401c0c003103104c0420046440209000403401d0b1401b009031032a45e60560310060301c0c02414400b0b11148100c0d486108214400100b900c040c2c2d40440480300d001d00c540c030805aa4050894816a14072003030f41c0865002000340b410104001014103102c1102500c4140780c80c41c0200080da500741e0192140c1042107907581000c1030036040300d058401407040b41518003002d00b0110018000000402c04112200895501c2c1c005071641d8401c01c80603103c07242001045583d40da4a1355009072425445c210041410840b1400d1800c070103513001d4055941c03901c0500c07042c00b0003081c201c2c003640c03c6401400c0240d401d0016200801c840842120b00c00000f44100c4400d2012184a42010200c0e0440c01c080c032003074071294100641102c0703005105042c083d010b40307030890160034070110744a684140c44040c80480700e1450040c0a411807490420020580c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 365768732 1250 365767482 365767487
    0x6040b07081b1c111f1a0616140102090a0e1807030b1611010e01140604060602030f0c1606080619141002120417060903041d150a090f0c 60
    0xc0f014080745402e144810302c10b10081c0200503e0103a02da01d4400d889500c15000d13200c0480100c400c4810f04115551011420301d121800101491200203070360702410020000c0381148010759503c0050700d00400c2c5940c3c0190b060342501210000e103000b8000c2e01206503644048400c0c1602a86c02c150604a2021504450040069941d0440b07800c241148046d480c0c1109034407184001c401070000b0440c041c00c414100c020f00740a000203071079001c1c0000904007801c540340c450845d4044d2090344120708100d01000015400416102d5510b2000c1c0100d41d1130035400001307444d04284071890744411922110000c0d520b600700090510a200c103440420201c00d190303151606c084064003840d440840811091035841c144a12501e4140c803242c0101c600b500f00999900d904d0380c2050b800581c1e0082c006d1441c09a26009100c007070b800c005214000e504103401c0500c02c03007100030040f0144820350070702c4c00050401400417a50700032181018100d495000d84500c140409442141c5410b40c107076081c4942140c00d0751 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 365769982 1250 365768732 365768743
    0x309080a05030d09030e09010611070803090a060302090604080601060804061d06040b10030b0c030604111e13090f0504030201060503210c010b0303040b04061d13050606040b07081b 79
    0x1540407020710324000c0d41100050062a80c030000350308202c0026113100c0140c54100d101406400e080c0c40f00451441c2c1c8040c0c482c03822a06400400c60354005112004440d1150758594003a10114280980c031080070401240701c9015607403080300f00c0c2c4074041c000174045412001c0503000d80e020304000d004203400300c185041604800550042c1d207074004800030f030200d084071208981000441c802800e805a40383c851140d03000094906110600c0000203010551503d0310800980402440010f03040c03468008101e003030101642c500c00c0003104002600107240203407580c5440900302c51380d0200180425801048014241220114055860f1550110700c501d4002101c6410941072420b0100b02080c2d84101c4101c1d41004a45a045640307034911003040f6034040c0040e00240410200c019202d5281c4000241000101050040d09150305a2001041d40715030641621400c407181e0046800e0300c6142c00700c0c83c00d118039408460b40c92008580f44e810441d0160041440350764010200300c1c6c07040d24104854a64 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 365771232 1250 365769982 365770003
    0x2060a030c080f061f120f05090c09100b090406171f020c0d030207050304090606020604030210290a0306060b18030d020a0f0f080301060801030b1003080d0b0d02120a030908 76
    0x9414501800040c06100c0c10041c2d402c1450b2800d0711100885031b000d0010b4407210a21103011540740d80030032505901c2006551002c00c8100e941d16003038140300b45200503005240c090020340140028010a15844681003007000b00007440100000b00c00f0401101d403a40c0c0302c1c203041a2034a07041400c035502c2d880540240d42603400d807a0098900aa01684250000c3d40003a10072905c9000900c000919420148124002803603070b07070050a60303450149002400c200071615090f150514040194601c0700300303644196554440d040156000000510024100132425840207103403a0070590042046c0f48458003415424200a4201c0a0390300c00c003041645840c0010b0344e100040c0e21110030070000c40d410045101c0c0b9180154000082044a030f12903000301c0e030090308110089004400100f0400030100c0d00194819800542c421400c0d05580d565115403142080060740d0607103903d8255500d0352005940c01065034024055216455010001511285241002d41c08030b00d10305000226908045040505c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 365772482 1250 365771232 365771239
    0x305010e06241b030c0d1103071110051207030b100201091703040f0b1501080a090f120302120a0608070f030305040b030712050906060f0d0b0103081602060a030c080f06 74
    0x1d0314440049070700858030780749031040b200d10200440c3c001440208405183e08001d490720946104001e0041d02c0282200f0256a20401040001c0361340c0d100d4000c00c8400880b40f2510003040c81d04110f03200d02804c200b500f18502e034241070000d441e40661189282e8901510401012808440241e00b21460b40c1005001c41036103060700c042c00200100116803082c8075040c001e0030b00e1059112490340103000c5903854006074000c6000111036822200903640512580310600900d4007079900c8200c3c0000300000142405d121b08038482d40076009170107030741d04540030030403005175454901c5074040034000300e04c04ca4a55002d500030100301000440c0075142a26016240c070b41c0391034901034490280394001407012003082100350300b03030324552564050355005800b540e00409050034040204100c910034001c14a20582e070f60401d0600140407040f0590442c5d404c69140b6480d4002000703105250841820000e40c00f03c00000d500040c03d0300750b0712008254020356904400c9981d50040501443c1c4d00780da046a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 365773732 1250 365772482 365772529
    0x8070809030711040f06030b0921040308091e150403021908071203030213090e010f020a1d03250e010621051009020c0f0f060708160516030305010e06 66
    0x8906190300175030650301c3d4811000885655a1b01d41c690442400e0340c040a4a4210070340c403415940a0340300b10352407400c86c4405689041e1640d982d40303803540b158802507070003101c0d0140855144141c000b000d2240d04000341c000c074070490508a070090b0640c824001203109500320603020805902500c45001603a501900816019050120112649210100c21400c06030200404c05041c29002030b004014280b9078404a9034403a801c4496080d505070762a0310710011700c103001b0f1104440d0b0005100f090381c3c0f880e4680d92544400400424203001c6945928070002d10380c10401a54100c2070f01440e000c41c1c01c2440700843d541d88903d021600d0310300b6042c840c1025540c07041104400d000a030303c2541c0000d0040c200b0b200c4165211010802e036004004100480d800c4000e40b040700d2641030180c001e940c400f0720082c000a181007007000e40240d01c0600040c5d209504c0c01c04c4444500d02400c1201c0903c0d08481d00305000050500e0000c2c080d10090140790000040c1c1000700304242008122690311804003400c040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 365774982 1250 365773732 365773763
    0x501020d2312010612140105120a120810060f08040206030a0b040e0c04150509010b0a02070b03190605030a0f0605090a15090620040302060d1b080708090307 69
    0x154040c484200d448229003211a801540c070040000038080c000e294090a19190324110010700340c9a800d0780c801c440e450420407034020041e40700440505482d801c80d05092201e0f20f101a41e85401203142c4018900d224a045114407179802138940c6100c0e0039100302050609854a00491b07040c00781e00241008580d408012800614001d0003540c2c5c4a6031010700091410030080018084c4c1d40140030800032900306001030703107083c00c6c5406000140c808114940c41c01c549028041042c07140c0511032100250004150b0340c0c0780500c01c6c00030300018070f1055109500da0809008824002640c5150141c0040c40e20348001458100407542020b0503412250740801c482d116142e0314054680200726006501070b0741c10140003c0c00010003824290960500007850740001c0c0f41600450740300145100d4040025038564080841100440d015240d050b121039450b03107102210340d03001c1c007512404080502500300300018600d5001003018031401440e0340c2d0070055254007642944a1250400180c80c3c21111900e80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 365776232 1250 365774982 365774987
    0x5100305210d0c090602010f06180b060702060403060f050f04030e0f1c15140105030703060b0303040302060412020f01030c02030702120a050d05040e0105031603020907090801060f03020312040501020d 88
    0x600141004807101c0b840d25032982800c40840d84002400c0010403961402441250740c2441000958194901d04200d85820f2a20110681001c0503003044d0080d1500e0003826152619400d072115561b02070103680e1030b60f840c2c0c6088800340620304c1c50740c2c1205140c40002640040450701c03030f078042d40c0c040e150748107001080404d1041e0900011200390f0040e01071000e0000340503007000d028041c140601e03802140300300780840060075180e030241c402c8070880b1a071005002c603542c0464201c1c02c4941c8220300241c4400c02c4800300f802e41c000c035440a50700ca1000308000070008410f4248042c52032080f601172142201040042d42258170140c80d441c01603005010590050600000714010b040006080742c80c82c8600f03907140c3d0716042a44001100013680424200480406d82c15101c0c050101200038241380380b045070814030407040903c4068411110f8401107240c050241804034050040c1800074001c0f42d44030000e8800c06005803004070700038801d29044203014002c5c40d007601c0c10b80704d0581c050960b0400c8107008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 365777482 1250 365776232 365776273
    0x172d0723010e030417010608010b210c0d030e030f2a06120405030403020907321306090812090609040e031c0902011b050718020c030f0d05100305 64
    0xd104103640e039002c001d000d29010805080204812403c028914600da10002d003520b0266110488030ba04100c1c00001d00d50310041d040c103400c0d8890000310300002d9480482d920b04550042d0b09904801e000d60500b080c1a40980748000c048420307012a00d03c80003c02c0070b56545c0c804441c4044113403025404036500364112125100d40c004004100d1418614001640090180305039021103070340d480098204114102055040c0d03001880e0700342410f0248480242d0130300ca010300703402c2d07105010f00102420b14180704001921452510700c2d40494640307440f1000601364035542c1c00703000c00c98072400003000c4c1c07131550360070444541c5131000d0145801c002d103140612014003401041481540010300190402800d2026514080c0a0710040428541e003030b40005001041c050790910908691442d142000c80c40c0080c641c0b084641c01310055004501145401d0000e01841c4a001401d0000188130f10140e905e10002d0044e50171380740c038100080e4440142a00c060b203420b20004003983c0040c20b940040003d8000c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 365778732 1250 365777482 365777543
    0x30d0e03010633140f030421020601060201060f0302011d0301090213090b060103051e1b04060210060f0806010603020f16030c06050a0b03120304172d07 67
    0x224015440759107074900f03240c416600442c0e50350340c002e9a82d41c0c0030110a8080c041c41c0d00c1d041844502c4c690740820700b00c9201d01c0114405005000001c10100441d40701070b003903090700c0e10001558060028070000d49644e000e01c2810019070034450b0205191042071290f4007166416140d0b02a4107c11008010707411001c03030a4980d255588400b103d001d038a440014411206405000040400940c9801482c4100240802d81003600d41420400030200100d10100100c50008003c0b48598642c03c900e5450140d03e00c1c03440c2c440701c000c20300144040c0c002454202c82d505855003400443e0300c1c1e01d030741c24a640c0644140b88a650240004002c81400303940184130304202c00280d54a44282c00000110300044031008030001a0107007611820300501d8030425030800140207050012134061400030b40d440d142201552010b044c0040031808002a1594020314202c01c58a01c0d0b0319400d4401050703010415005080e0a007111224401d03134116844e00c100d03001da030341c481c030030f903a00c000700315021001202030b010f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 365779982 1250 365778732 365778739
    0x40f05160c171603090806070813050f0d0c0c0e0705070b071404060c020102150c09040c1806090312050a02030a110307060908131e06032703020c011d030d0e 69
    0x346102d400c014408000c0100003520035021549a01d185002000b00c64168000203050f040b1200380044150300610082c1c200c920399001c4003845882d4240b2509188960900302e00601c00c02d2083c2300303100d030414111171925001d038000720740842c3d0310901000301034422103124000800c10802100014811342909810088901c1d000c2c03c034801a090080300750380300340c01070004181d16090f22400c640e41001000310803c02500c140342c05081840c400c800b07600500380c03407900c00e607102c80c48020b0880c410382034034640d040c6807a82c50381c03466030f60140944503a86c43c1c001507030242d0354031610010f803d009030300700c036240e01866008525008850904503415040101d1420035070008100d81404510540150b03c0c14074024000b0640e915420400b6183d058003544c005141445080b440e119070608144d00300040740c255041c00f03e401c0304000501c00040020200808140700003244d01030034141c0c00100c5031500070003a00c03a80b0011007030186141405004451840e4180c0c0702110001c102441444505075000c0e01a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 365781232 1250 365779982 365780003
    0x80606011b0f06021b0d2012120103050c100f08040f02060d14070207140d02040216151103062206180902031e0a14030f0d0902040f05160c 61
    0x82d515000210301003541510003d40103e4004102d00da0301ca5202c07650015000200304050240101078a480e041d2540c1c0924503803051300c209003505091002c0801c200205155a80d100d01502450b5007001007804190350034400d1580448413810b1910840700c4d2014940c4520b803403003445040445600d0380081c411a103003e030b660f08103801601c409000d0186441029804543c021503002c0901421000a002d5001c56000c1d1504006041000c2e1210b2aa040309a8000c0c0071180e241c00810040e200d459007140d00400005164000e0041c0c10240c00140252070500341310804288002c2043d500082e14965401251400c40d441c4110700340034604d250300da81c641d0200e00259100310204140f82c00c100f00c40041c0e034444c0802c00451900384446001d0a9124540c80b540d0024000455941c40003018010146c101c0005800150f520820585070460756240700c440c0c0c2c82c507980f401400134250b0031104030300403804c0c02d01e003e4120038140209441103000803400851a68070700c0003143ca000301c2d02c0003540c007000c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 365782482 1250 365781232 365781287
    0xb0102030403150b0f0f01090603050a091e05070b120106110a050319020f0312060d05010e0607030209011205090606100909060e0106090f15030207080c250f08060601 73
    0x4061280f50351881c100b0340001c02c00c0f84c00c8107206141c9005804039105a503110321604403a83c00c80340120036202e991400059956507034040390010090028050000441410240f00d012003030001c0d0348240340318030b05032a07400d80d8459248106000340021a540e40d948030005005803032240c0585d4400704658000c81c0e50b1502e840e1505410b540c4021076070803c804a00c81450281c40d0100315243c500c0346c5c031000451070b003205031a8240041c18041c1800d44142443e44280c03080c8a0250400c07403094071940c050b03400b00d0400340c1d0003a000b0350143d0541d078082407000000000d102c11070301c5068400c00021020b08002d94841003080f104d1a420708200d414844074990215410180c3c0c440c02c0060065034042000f154100030000c0d0100040d50f00a8105000d500303024805071400558603509500c06060268480e040351070a4031072401001c51914541c800c010007003480c0200da01440040740101c946881d031250700c03a09000d40103103140c05080c90b180e00c0f8401191065200d1856400540345140041118140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 365783732 1250 365782482 365782493
    0x160c0510060306050907080309030a030f050c060f0a0b06090d08031305010510090b030703030c0b060a080102270109081203041a04060506010e0a06020c040f060f03030918060b0d0b0102030403 84
    0xd80d00250f0304143c0d10010484000300400650020b01404401107080a0511001a58485404000404001203d82c41c45411400750042d26848a0520180c40e101d1034516186240400d0403100d0342c041c00d007091100d0005003448001c0f01c600c000e02400410000110340c40b20155030b40050075020f50300454260f40c8c00403460038400c2a020703200804a0013681c4c1e181c01c00c14802e4444a6032240e00c00e81000500b0170000c1d410140351820b8a61020805189507141c034001602400c26a11043c42540001440d01c0e0301c0420300c0a42c1016010080482e5800101600440d100c03412402010003591005c043c0711700070b110141c05598480d22554420b07141c01070700480445030900607581182c0440e21841401425038129015005103078040d40d518070143d14000c0000d40e103c2104851900031650303031880c1c00101102d90010030142c400d10320031543d007580c0c1e8940107105900902c6030480a15007114000761011260090b002117a4118044506000c018100b100c010000400107c0c190300c001c1100000044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 365784982 1250 365783732 365783741
    0x403020643020a05040204080d030908071401140c13060c050c060f03010603061508070c06060e090c19080c120705040612050c0102070806070f0e0d230105160c0510 72
    0x4190034080c078041c1c04a10600840d2981c54200364802c0c0c1c01813005000707003500050a40401c1c11180340100b00d00d00e07141042c070f420744038040b40030380001e4028100090741c9105400110262581543c441d00a94421411109500450f9480b40401003062401c1210911503647c140340750f07000300258ac901113071740e10003c0c0050f400400d205010180100041104940621815008150340c0e04803020240e400a802081c0002c020000800d0100c43e004100900c0350f5540104042c045408200340070f4100140d00316954000111081e01c00e081c0080d80c030100c004445019000c941c19070002382290b103207080400c4600f6040300c00c0a2500e1140b510006815074503801000001c2000f042118540421424042c0c10940600c0005042d940003a81c02c1000400c0041c2c0907601c008289050310310f940d03c408086440038245e01c28142c0c010f880c01501014003000c0f111480e01d5401d5800104c00010030090401d0030ba4600300e80c629094406c500c2031890050040404040492088098a034410001c00005d411038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 365786232 1250 365784982 365785087
    0x70c15020703090609090603020901090c11072d140d1a0f040c0902070b07030f020f0c0f060711070312031404111302040b030c0d0204030b040f020f010504030206 71
    0x90303800b8000c0007002d80109403a03000e0aa046d1090098a0a540102e12000c106101c0c2c80c1086a03181c00c076800c5144183c204804085800c1c09072260070350b880d07254585071041550000e0100d00300f40c0e105089002403510b03150841e0074001d0722201c045c601d0f00030816400500c15080d03c640b07400340195040b000000240c0d91044945500c0d890050801e410a0300f002a0180c01002c09144104080000b168041080c142c0c0301e035544c5404a0b403034480c0340250020380541d40044d80c884070003084240d1090000300c3c4404071214640c040710b5141d0f980030b40403030304821211030480c043c1e000b440701400440c02000319001d01800070308010800150005c3c00300302000b800c54040c1c0e600702e2122802c0203d8985072544032050100e0180c203606040c01c1035000d003220310001e02441001480083c0c0d034103800c07102c3d405036002507410480310360661500342840c142d6480001d174120722554240f20075101035805881920f06494002d01198102200000d03038000f02803040e8100c0034600e541e2804c0c111204012101000107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 365787482 1250 365786232 365786237
    0x6020c030c07080105040314030702150c091008041a0c0a0806060909010308030702070f08101a04091a0112030c0201030c23070303060801020403050309150904060b03070206150108070c15020703 85
    0x2d51801e03090060801c0211100281c4023441041805003640e40010a800803035480180b00020f40c44525aa140c144182c80c0703030b2034110b030388402248c0840d908160103611030f0340210000c580950310917180642003c42190382c04c4080005000320306490f8824a03041d544031501401c0c803454183c030840024480d080c264011030701c04400000b0440045d0b81441171000500b0426031540485040400c40d0340c88400d0f5038482580d07569101c508810045403c11210b02c040f001900030810314010303040c10030390322120440f0742201242c418000540845030280460100b5050b82e1401401c50031540110003800205044404000005415418003041300105400d03042c509144640c0c0c4680710324000d0152041580300c90941e03481403104001195010080341c40c800d1049035102001e441e03d140088150041d00340203604070385404400b04188040e0b81c01503005015903000c80300d11365148500c0354500f9502880d06030008124002265116000728441400c1501c142400741149841c04100c1007241c001c035030285d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 365788732 1250 365787482 365787491
    0x15020403060c030b0301050103030f11031902061e06060a0507050a0c15030c031407030924090b01080a02010c02040e070e0f0a110313030f0504080d0c1205130306020c030c070801 78
    0x102c0e0341c0500c101200c40c00250003c1c0425851a01d01508280c0b072555008240400192841c51481d4280115507407822240058a90704505513402595003000700d42c42d41c1000c1c00000d400c0741042d00c2c0c00205110344d030014100b5140032121030040b1680d400c6440100d4013480303a00c071418005002c2001c142d000e01444508400c0300981c00200600b60382000400341c0a0500d0b00d2071041900888140180e404000e60402242c071100300d02d8000ca9107103405400c01d044012050103560340c0a00c0340c01070741c10301e4043c0c0540c8080d41d0f2034407210b640f1031002003402404191511200302c01070a250300103040700c110450641d90625580e080a03001d010046614014003240d8008010102103540300d91484000c07081150b0b8258540b103040c4a01307440c69000c1c00f0742484000901c4010513445402280e010b0800d40c42074942c002c11001d00a4030800e9403410854070440010b840d2444a48140c090b070702c80422030101b400c2c041d840d40d1034030402548446584021800200121140d0440030401c00d001411035800000f0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 365789982 1250 365788732 365788751
    0x6070201140c0c0a0609022d030615030a02040f0f02040e09060a0c1409030a02270c130e060604090914060705120103020f01121a0111011104030f1502040306 69
    0x301550740103202064141051201c3c500c4600300148801c1c0c0140e21440000d112001030000680c10000700501c040e000d800c3c1d00340c0041311460b21944600e6002c05801311b80c2c490b192800c1010f0355500c40e81c265509980080380500152920b600b0026400c0072451000400400307440d0350400383d038415002241400c45030030510410650070000158400360100c4100b02e20418500010020405005070707210600b0045030940050b5020b100608140c0d500403e0340f00000e03a1103000e200702c03103034a011900a2001c0040042c03a075800c14011126041344005500d00143c0c2000224620b00b00d01905090300712100f40400f0440300400e218501e10700740686000c10160541000540c0391410003442079040200902c13903001201205e0000f01c0c1525030484004500181d402d00403a10400c04200f00160b050400300d81e05000846809803140c1e414007039940903920584000e0f120701380c4507540588901171270f040000b04049813402d12010700300740c400c0c1c41005103040c0003120801640c01a400940d6400d54406592 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 365791232 1250 365789982 365790011
    0xd050408070b0a14030a02040b12090c15030c0d0612060204080d050f1b0f0d18140307030b060102030c07030302010b010314060a1406070c0e01050108010512030f0a05070506070201 79
    0x900410b440380005150030350000000b0002d0740910301c0c02d81190310100101d001000740780c040e10054001181307a00e40b2a0f0103030f000d12007424801d48200c403042c060080343c9002c0341015400140140b02c541031701c80ca15102c20150450950008800e1000142d580c50301107a400c00800f035088110340900400b507125400e0110290409540307800e020b041c403c0800c42c004c0c00c43e41c018282c420100e8400c100b110560100314202c1d00b0a07884940c08580c03070249180d980307008c030341181d024034114a551464005558564200522011510400702c0c0d0592040c0c3c400c0000072044584554130040600c1a20f06103008075040d6032a284441d04201e025035154110701c2c0703140d41d047c1700305455030510300c428000c00e041c108042142320007140960404000c09422101c400c1c0c445108850816078401900c40091f41e440a296180c02828095a4001b44214000080750714082112424010807000610300c1d150b0386220b1641c25074400c08003d4284a0180030031008190305002c42407266826400200d100f00401008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 365792482 1250 365791232 365791243
    0x307060606090f180204030503130305070605120c030709050616052109010809071703030f0108030c1b0a0302060a180f082e05180f0309150901110d050408 68
    0x828104030100004000c180e1882d0b038040c04444c4100213594480480481c50380107031140345c10142241c80000f0300c0b0714440101d4060a02101d0150781030b1021039031220700c00c81d041c4c03042340740015143d0950008034a02d854048000e54001c40503003006030031603036984040750203a00a091142040312202140000f8007406000c01444442144c0d666402244014044502401009440b504000280001413030728142001000040c207044640c1c4034140714501c4040d5960b520890700d0054250441000082241000082d01c1900745450003500345a080245029518524980601c2c0c2c032030355640c0c3c0000581c451200528041805988243e0004c0d441a41c944100880b6401400c1c01d03041c0d00300401c0300d1000811a10040505c20040c0500c909408d91100c00715101019205006450807060004282c2220700d40c00450090806440400c8801c814054480c021482c1c0303160000c0b50071904807032602d40d038030082018540c141020004c0c4000e600350a0314205080c1c40c60008180002002d00109404000c0e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 365793732 1250 365792482 365792489
    0x20c0d020303040303051b0301030f0c09050c0a0315030f021c0f060c0305060a0510050c0a0606080307020a0909020a0303080a0f0509010506131b050f04121506080303040308150f03070803070606 85
    0x14031f0303804a0480c0400b500a1005200140040801018010070444003075109001071210080074032440c100801c3c4401203901c454140c1e40070914011284405800400b6039808403508005e02e010110340325000d10075030701c0742e0540e90041400c0d08403105000641d102c05061050703004010015004801e5000a01140c801400b428030480703000008121654070303040c800c60340f00054a841600c50400025544c42c1c12803d2000910141c24000007040d04070000000d420102e000f2200380b80c0304d581c1ea40118003164400d40010350081c20702c107001c0c07000c40d0040021940111a42070f000907000824504601151820703101910aa511141403042c03601c3e090218001c20341d9514020020946a2080300b0300c0c4011540c010350a008002c01c00d0311030852100269001041d0081c501c10012100746040c0c01420b00c2108440f4806162034404a084440001500d10030b42d0305443d42202615460041c1101340b261a5101d82d001301d091440e40340c11349080c02081e00501c800e500564a0300b0017446e203401500e41541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 365794982 1250 365793732 365793751
    0x7050109080d0f0b0f0f0307080a1407060f090909030522090e010c0507060b03160f0501140a0e010c06020c030d06050913020901030f0503131806080c22020c0d02030304030305 77
    0x195484d0a903640d40240c0c1240100310395241e44021000c0110341400740f01e03408031000e4001c0e026480d0a008902403080500c080e2002030b56190380d1292010b45100c4d0645000b9030008100e071005001c408440d90006a150740030b400d200342400c00e8066000020b10400302111803081c02e24204111514a82c001d0900c0528040001d110031040b58000802d00d0003200030142c1043d8a412605240740c80c24005080603440b854000c200d02e1b034a840208030f280d48544a00d0780050380e01d001c1c0b02840707044036041d40c0e4506159a00c1c0c40260402100464206810b400107441142d03003000b500c03c448208100401c0158000c0d00b000c903c051500c401c1140b00d10004054542c0b03640080120b8005070743e6014580d049d0b0b9880041070310703254224101036145004071040000325662003e0003140e041900c04440b0683c1c4841541845102d1b268082141c494400382c0380c4c60f8000c8205000e640440540d0902044850403035070005080a0001822a11707081840e40c0000258100006210a065160140646c82070b500c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 365796232 1250 365794982 365794991
    0x100816350c0313240c0c050601051507060209130614010909060e010605160c1d100810180c090501051f02030316020f0f1e1203071407050109080d0f 65
    0x840f460190a900d2140041003030001d41c03000707001544ca810b95103010300c03001182000000c3c0c109001518000710b001080d101c500c640710001a0914101485013100d880109090b418607080d9503804029401003140c0662041d6810b4050740401c1440c41158000c060030b900002080f005040007409162880e0041480a41441001c0c07084040141d046030450b9041d103405030f0341d4040b180030b4aa00180e00c1c24001c2a0090b410b40c00102c014058203141411400c0b110414065100e44102d45010507440c4542442c41c0c001640f01c1d0800b010560101c07800b40310601d0051515001030f0317180740d52000c05030002e41e0300a0742d40c4014480da0500d030800e045100c000d0b8400c40c0002d0350031880651f4a020007081c0003c819020240e03c0861803081c0031210241c0b03c0c0e0012101046102c840c01510341d00122001c01910f2660301d100c41c40580c0000381c0800303a03601c020006103141c841d0755007194582240c040c15244143c08005010000701300744941d801443c02400240c1c1c40702601401c190070707105000303907118401d400d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 365797482 1250 365796232 365796241
    0xf08010603080405060309070306090516060f0e09061305011706090a0305032202040515120102120f0606040312031a0126090f150a0b100816350c03 65
    0x4141164203072681201c01e541c887d6103802d01c481c900050350300000d103918100314460f005c210300054010780103882c40403203a11590700c03a04100d071641c2c00e10f02c2d6200042e10140f0b980c02c5030b0801c00400c0e5040780300600002110700c040700001054400c02e900ca440c200202c2c07111030b034003e00b0070303c44960407025040182100e00d07040c0c1c0b030003440c42c040500300a000d041e220a024100c5000500440510780c4c0c090000c2c4000d150050310000d8000882640b1741c042e1200c42040c4110704010f04c01c903910071080700031840e5603071035103819180841e4009010340e401c80c000b048003002080442c48003078040182590041001c20076502d8007500741840b020124103100781c002001194a49401d0b0030703807101411850310101c82d900c6600075881d190000e01225141e00810f540c415070809003030205072140580c5007003808221000c0040c41110000100007000140210020401481d00c0300c4c13903507106510620f400c90185044642c0080318540300202e414060101c0315001c0300254a0718140c561103080000c034681180307003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 365798732 1250 365797482 365797493
    0x10c09030201020a0b0a1d060f0a2304050a050f070f08070f0e0a1506030605090606030c030403360e091c0302071a0a05040209090307050d0c0224040f08010603 70
    0x54180c0040c40d121784caa002800c211500d070712030a00a6041419000c40d10390a2070304a40360542660413843c4580d0310b200045030348001c1c1c05651012040d008204402c80c200003000c00c3c041001620884403800381c401c0f48000304004129906101e00c501002d032480500d00707107095130b080c5a107612442280d04040e40070045808181807050854035000c41c800c82d107540d21510030005000380800003030100c5c4841e00104040394541d21403c00d03602d0580d500900d51b00c5400401c9894001140c0307150080204000081c0024840c0c143c0ca0684418080c4440ea1940c00001004242c00d2441c0200410580d0080810401c4035074107007160805811000341c0184070040b808415480c5c0340303080d500c0074103800042c04001c20825141441d1100c10821034000c1070300744000b03000c015100588041c0c1c0700c0c0d00ba0340c000c83c0e44508040308030740c9400d5002c0002c3c08618049101612a03104000041c0d80c0a95115aa0900f001404007608500d80f0505003441d5582c1c10300c498540e0b030f47c406800609042e072614209100041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 365799982 1250 365798732 365798743
    0x5150331120c060905031c020f040b2a010f11070f020f0d060f05070f091503180609030f020d0c0812040816050313150806040b01030b0303130305010c0903020102 71
    0x141c2100d07200071112111101078441a04040c0024141c1d89412aa84c090182c04806400065403000f404a009101d21902100b42c0c0a80301004616940401080150201890050810048034091440990314010844204180b00d040740502d59445461056110825200d034108621102e9170250500502d03840743c030300f5000031060090040e0394a25600c02c05036030304143c1c1c50050b030b400b080a000faa0344848510010b4074080d43d1030008030300040041c90284e80902d900f01d054a000140180d82c164070034000710060729210350f040084045924204d000b18081d0302a400d400d901030380f140a9a100c40d02c00007403501d83c160502c3c0c020031954030000800100321804580000e41200c440311040d46a6041410300b0348550140507d0424660942404014005c000b902c8020b180000b40003036650354410b481d2445252003141c07000180c8040c00500e941c903240e0b1201035041c00600d000180c1d44507402c0401e185600c41441c1c890369144481040040040c00d024800310400e1600c0d01004452a5a0020359103a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 365801232 1250 365799982 365800081
    0x14010519030908090d050a02150403121202090d0501230702150c12090a03030c020318010c06150f05090604060b030601050307020f03070b1806060f040b010504051503 73
    0x5448107801030902c0f044500303841c060b02c1c0c010303d440e4425400345032141e82d80d208440228001c1d205074501c038071f0103e1403400742c07012030303402034080e500462888000b104c1642440ca003213054590300707200003426510f6941000000038403c0000040d02c0e20301400b1506d085250913241a0200310701c1d020041183e601091605a000c078100c9101e0150322800c821061500130248483c02030a464010407203043c0002550208440c0207440030441c5450521701283c40788204080000c101550b031044e245607502c03824140030001e00a00c0c00245d0009104a00c403070002403070b4070040b0ba980d2010350911144c905152042d0304600d04842c20058103203001e80c40c00b510b000c005d15040c1440008000145018002c1c049500004203920580707a840341c04c1d2800c150f00020a0700c3e042c8185004010442209200003262800341d0310040c164003031201d202d020400600380d4a0400d5040050038040000d007921501d4009000010705031482d0f481e0325080c403070000700d103021610101c01c0d440c1c034110112080c04d5807650748211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 365802482 1250 365801232 365801237
    0x30c0f061612020616032a02150a020c07080304030c0b03090f030309010c03050901201305030601080c030114040c030609021518041506091403070f08060114010519 72
    0xd82019000441c4070001030400600b010190100c1d402d101c6502059480c481d1100340705000440c1c9409404500300c8180c02a100d10b0804d60109115191150000507403a40751035104585d84035110b05621038900409603003501900ba008200c18520761802d1110f0380c080c09640000314100b030310315220581038001e1845042042d40d400404906c0c004002d204d1035080c0d01c20b54003226900d09007110100d001b003c4801e100e00000e450709001c6895080d06000e01c043d8044007503400350309101048015010b9a0003001c4468060719034150000c1e15407010302405000740b82040180032036601c13034400d140c2900c03821549015144002810003000074500b451700301c1520340007400081d6494040c804110a41109840240041c0e0082076442c10501510340307141c8420300035a02440020841c202100040c0e40500440300442c58240c800d1000c5ca150b1601c0c0f0410180c02001c55207021381c1c80c1507030000d4078142d4000000e80d0700000010b01c0306005080802150f000e007031070443d1030801c083c484100702000c0390008004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 365803732 1250 365802482 365802487
    0x703140609060f030d09030c0b0405010c02011103040f060e090c090603070e0d1a0406150501350414010606020309010509060a0306090e0307050c04052a04081515030c0f06 75
    0xd80343c6078907400d5581e0f03400240440d0400c40c6040805002c1441c40c0c401204c0c50300c60184040f036000051b030140c03000c903003041e100e107615801c442e0300554140c1d504000e00c440610041c000002e450b02800700c103400070041511388a1680c8008400d1102d814001030400741440002c20100c03120b0f880700c80c00c50b54480000c0c40c01c90125005240090160741d101b00c0007902043c081d540794002d140814501c24044c0344140020001e03403100420a0700d10350224480c0f240403c02d0700120001504a012a03280200c3c41c195961003010a4250082e00c0314000743c0e001e0f5402d030001004d08421407400d2007000c001d00740038001981001960400204940b08560342c082c0035001c0410100d1b00e481c0250040d2018251014052004e0100792003103603501c0e000a00c0c20360380c520510034420700c1c900742032156a010301da401018a41d02d4240100242c070244196060449100c410000000c00c00014003007640c01d600300b184c41c0c00c0c0702d041c8141c04600d0043d00d01032843c480e03005200e03208216a20351801a20070481a1182034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 365804982 1250 365803732 365803741
    0x70903081b06010b0c300f0910030209011101090b0a0905012009101404030615120b0403110309030d111204080a0605073011120603060703140609 64
    0x1040080050701d2110340b03204420020541034460001307091030400ca8130842d9055106a500b4262a86101d01500030701c003102007000c0b01e043d1040000b00b04035125150030903d003251003408109000da4000e03102000035404501d80c14a5a4021445060808404001d108211194841c0742c01000040c0c05183e2056903948203004102e4207400036100140540395810403a11400700c031058690002801c1c03449501c0748040c2014907802070310081e0300b00c665002d03110704090940c0d42c4da40003070980301015155074003a880f00054045c0d00304d00c16140c0703034031803804d611260801e403030084d0070511500c1410110341c1042c8107500d0309440005004141c3e21080c07601c00c02146060000345c3c01c003000c924600345000000a03000c62140710000c1c181d5102c0744952401c004e140c1c1c904504a529071a800c52904042040440e801d20b910398080c0344014082843c500050488521500c04219a2003a1801c4075140032680400005280500c08280c1c804c0590905010420a040d1b02105152008058500c035010400108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 365806232 1250 365804982 365805007
    0xc031b07060605090f0a0c11070902070302070819051501051e040b1203031005010503060a090506060f0313020a090b13090f0503121503120909070c0605010909050c04020307090308 79
    0x4002058041d104c0789481c20800400c4640a00888450030074a040812045940384100f01654604156001510101e03081c038030188041d6001c0ca009508620440c0c0c40810011400d01c0300c0b000b0070031003110001800845181490401d018400c0c0c9100700f00b10320004109503256809800c0324032105511002a05091400060041c180b140303030940c008520a651825507007000009500806801f01890b00c400e554400444040c40f040312780c10740200301014100507482c082d8001c80d4000b08001c00c2d007800e10b40240704402e81900215488a982928045000c2c203500380154000003800340102d0074084007000c0404950301808002d440c1002960f00c2e83d141043c4600c0600c007005555124060707a03034401005c0d4000d07070b9a500c261042d02e481200480c140591749400540c41e01202040280e890034014020100110a0700081201c000d202070405028005052440f801d806041542c000107034001241c01c1c07051500000c0c6050300e0007a413041080c40141e83e0054100c008582d4030050903550399582d02e128 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 365807482 1250 365806232 365806241
    0x60b072004090b1618080706050703030e010903032406090b0729071805010807050c0a0f03030c09050108150d020613030c1a070b06090901181203050c031b0706 70
    0x940f43d5038845090101888400c1c000c880301034000d070754180c1110443e890300054406140304104996201c05000c2202c90f0280d4013402c440790003800d001400c2d45044400500703484c0000e500320f00080d030328101300c00e48540024120f0a102d5a104074050a14100701020b01041c0d414060305000050103d03894080002c06559420350340179500714800c40c0152451a013088580540b1420042419020000000c00d0340c2c1400303408545059482201e29110b40790241e8080d80400500d200c1400707511400070200301000c0d070160189100f580c0014504041030801040303d070158110a0400c080002840710108030034985401c0005c2c1200c0e0003000521f2480080c00c03521030703450320101c0a00c00c20b00000030701c00c000c5c244004540302034451030409045a42d074594144648800148a8040d141c082052030074080c0c1d0035940202d15000014055210300682513421211600442d0800524069100c4840d8580556070300402814813003820760411018120005000c102404a2140003158040034404603400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 365808732 1250 365807482 365807501
    0xc0106030807152016062406080903070f060509031213050601050919110c07091a010c031706180f0f0708071704080d05010b0d060b072004 61
    0x400d0794490b030520f0301c0c0389074080e84828624040d281c5075040d21005001040e5452144101024610b00030740c00500390382c0080c00805c2900e0890b528420320128115401c04503000442c109048000a032501600420f98600100031000c16001440b90000180b40001584107040e032010000c5031b039648411140b4514003504210102c01130042052001c55032089030812403c80c0182c043d5004c9a07201e0b01070012909041c0c0d0f145410300300461500110b500143d12144c1c28400c0d05564900e003200c00b40120345011102e0700703c01241039a6000d07409480516800102c1d54900a0a01d0582801d45403000b5182414040071805281c561800090181d44c6266941c00307805401c900944c0c841c20614854109000d040b00e820740d905180f50007061040f0302561080e4400d8886503999888800140c1402083e00b901500c21203904005000d84024460940a01d40c00b8060700d0b002a40c880340c1c40c000138425201d85501c1400c058008005d810b001c030700000540600e400307c40050b03210010320392003c81c000b481c03c0e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 365809982 1250 365808732 365808743
    0x602071836030306050609010e1011120406030608150106050a050705100e0d0c020a060e130e0c01081803030106110c0405040809040b03030412030c020625021e030d050c010603 77
    0xa5088041c01e28560411090310300030382c0c0c2040794a441c0c0040c001e140c822812224007040c040c21034080b16181c4003182c0f680c0c1c0b09251400307003050341720404668940781901900c0392404d8070101d001d01102c0d5040c0716040061020741d00411072440d08291260b100d9006008210801000050101328140900212510143d0000403191038178103e21400004000c40c1170110520300444450700071441c0709403a0000701540080140d0080e510701801030b214403143d61629600030ad0a18088105c03601203109000b038564030303900074202d0340c1d0641d0b00040541c68014500c071a030401c400710810306031000105481c1540d6107818811a02982071600500c0c2201450b0702c607a0040c1490100010010410054425984156002c0c003a01220508041c0c8a0149010701d00341080b0441510010a21802d41d4480b200e002818151520344010482000c2c000c1d02c0c0001000e03141e090128030110b003001003012003001d40083d0b00072210001000041d1701c0c0c00b1000f11410030844086540d0722060000e6001400070f40c1e014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 365811232 1250 365809982 365810051
    0x160605061c030305071e0e010305061302190207081b040b12011d1e1b0604120b0f0f040b06191502160e01030314130b0301060c020a06020718 62
    0x140ba00401608088a0420018002d0400690412400981d0550300c02e0503864090014648800450041200400241c2c0c082a0342c83c0460398885144004c280a1081c4881d120b42c41c5022070000e850710308203a02140c103942c06049200000c1d20070550b14102548202c40205e1440c0c600b00001d120b51814280469482d4178041c007000c0501c54054040390300c804103006655036801103031401100f0203e6504640301580158602c0c40e03220800c2d02c4c2c0c8041c0f240b0014180c5042585880c0f50109206102034112800000a028409088031340e020880d44a01440e00030501c91506903503210f41e088024050500071507041000c140764011502058018100103400e1500c18022204000e544030305480b8a007410b20310540c0e011031a02192104241604c2e0191943c520505081450940316072102d0001c0340d102d0328401d004611051104000c600030310713442e030760341ca400c41c3e140c010004281c0c0c186d48051700f590b0141004000440a0148048940d4030f5280001407410300c211040d044076418411050701c64890 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 365812482 1250 365811232 365811289
    0xc0414041d060609010e070906030e07030c1206110403020d0b1b16020f090f0f091204030c1d0708180f070602070f090204060c08090d020907110f0316060506 69
    0x980d191083c8811580d60300181d03600c81c00000310707400540f001400103074030b19414402c6a000381c205029007035221003102e01059680d2a00c10400d1426008000c2c20400b11074030700240b0059000d24041040c0322400c1514103451640003c11600100d5001402618030400152440c1c1c43c1c13032171a140d4050480c100c1c40e40c400c440d0106524880121000b02d102e41e4030000d5510042c18003404ea0761042d5812907220000351120102c032030b28140300400d00b01c4144101c015104181071302c1805400214407581c0049807483c10502c0c4941c1910400054000c40046202001101d65005801541056800c0320703080c071030000e08020704d0500f0300c031401003d290f01c0745031b4000440540c000750020840340440b40d0b1015068461904034240d10a0b445581c000851200c00c50000c1000304000300482d01c0d0080040011241d0fa60100e1400602158a8004502c0702c0001e1904403106208a00e030710714080010351701d02400884174206e1800145005085a551140000c1180d02ca1340341c41c00b441250000c43c00c144842 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 365813732 1250 365812482 365812541
    0x90a060801110c101d030a050a0f0f0f030f0b0301021201090b0303070c06051c14160f0c0b090304170a0c05010e0d03082a1b03030c041404 61
    0x20a2056900a40c641640051440369040c01d035210459100050302412011014050140125591000000c1100590114500700800c010103007a807458582540320114114090091841e08200348103104100c0307000210f2940c80040b4148046031802d0014107803500d50150402807100d210016007562000404034000044050814100d840d070100a2003040340084c00c1c1074980c0107480c070041010020020a00c40389009401420708410501c91020985885a9080d0140c0d000000c0b8640f0f41004142407142c0c58114000c034852000b81ea09100f152414100d0b00100311140d9001e015026030b0030200800c0d0615400d004072001085a41081c00e104075080b81d040380c5544030f080d411981c0342401580028154090f40d01403554950091040c42085036685040e80c0b02100244030b46580403112040501c400921200c0200b901e21507010640c81d8186108234441c071000c0301c01d030292140d00c00e104228446030b08100312800e560b071037118981c0d150160004a0040c09481c0280c03c0d8000b808000e80740c0180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 365814982 1250 365813732 365813741
    0x8071205101e05040b040e0d03050402130513020f042d061212080604090c03080a03090203120903060a140121020402030408030a0507110319090b1603080121020d030e090a 75
    0x50f4111800c115074440182000101c03031543d081c1c2c00c005d41007030a102e03d0242c025404907038040d001034061203121103040301e1030303040310806c54901c07110a0001c2c000801b03504020840716040b00d8280c0b800c0007405801c4c054041110340703408481c21551040700c0420000003481c2c0208008000324000003007036031000d1a16480c000500c2c10070310005040c050001c0d80c146020b010b100021074200e092001c41d40e0039a01c1c0c01c030340c90b480310090400340b6032920800c0300161400c10039061102c0c0c0c8811015205c09100003003508140d0007030702c00000c00c1d042ca856001074003008103099044603501640724000d24010107a80440510107030000e2340c4a8404400c2109004c0340100441c490210680300b00155074604000f03442600080c2c64100959200b801507a0380b44e91414030303026440209041c4041c510b031343d035240390500340d00c04000d0500d4002c01008140c10503030000d00d014054018a024001011100140c84000e03812290010340b0a107803c9428030203050050b5075051000c030307020700010f0b01c500c2d10140e60005003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 365816232 1250 365814982 365814989
    0x12020c210a1202030903161503020318060901060918021e010c0b1306060501020a0f02120304050901170114070e061b010213080c040204030b0c030703060b070b1608071205101e 77
    0x7c0c05008460000402c40600320f00c1a00c1607407490488100903140100c0c02500010162014a11000045044407034200403451003030300000008540715041018440a41d0a020350410318001e1030441c0c40300503503540341d900c5900340c84400b040559403001401203a10f180d980001070301c04070b074401c140014000100b455140300350042005114960351100120707039854490002800410040040d007005181404400000d580700c4000c40e810a61103c00003581003c080e0300c1120103503551513003084003401c01c1c054840c00d03410b0103101c1d4185281868028080c0702c401400d003480703440d000031640d900c5070004801549000741d120086403100d160f6151012108114040c1c44040d01c00d0110061080c07a041c0215800c2c1da502c15042c0f0200c2c2c40300001501580c001034000018151208004592018030401400712140140d11030406428840340200c4d28010f00300084c410007a140f01001083c68110114540d4000b030580006070359503820284103040701040c1c01c43c01d1814214a010000c032000b040191055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 365817482 1250 365816232 365816239
    0x11d030c0d1a040b091915200d020414060901050a08040606090e03030603010f0203011217090303120123010c1b030c0801090b0a0207020319031407060912020c210a12020309 76
    0x14074454a80110f504141349000303041002111041107180c22a030000722030715142e103540b01e0048c2c1c01d5800540094000c1c01001170300c181c2c0410104080880800300846058080d1441841c5c801c080000a00501c00d8400000074050b031000400e0400581c0e600c028002d01103000304100aa0b00014803036202c0c0e206861181c400c3d82403041001c1000c0d001e10840703040f10307020028003c1201fa141d0301c003e500c003a01d050245508905015000d01c5440c1800185510401902c400306e039581041c0303088090340d1515540c9030711174071050740d03111899811403c0303400d010b50000d60080d01419031568080c2055565000100002c568901c0050b11050540100001c0d6200d07122620322a41e81c03484e080100e014800700039503d03600c06060301008849840300c0b03c01007406490129500710f078203001001703181e01c0680d00322101941c9210840602c0b01c60a042102025148068240780008400003a1410110150100300b5002d40d500d88041202c02c12882620543c04404483c1406030b1100203501c0e600403a0f4282d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 365818732 1250 365817482 365817493
    0x50703170708060d0201170126150103060228020606010e0d050d030c2a0c0603050f180f011103010e0f040b0106051c0207060506011d030c0d1a040b09 66
    0x91100310904141c851801c0356103005140c1d03105420090f12101101059041c040040ba00c5600b00c40d0b000c940b140070300b01c0a81d8844a8442d0000300c14007010042c040e526880e04054900010030001440035411203800c84000743c0c841e403801031021080140c440c0d80170040480c01c02c5000406401060700d900c2544240c032950011280740c000d014111124103801000ca800002010f0328a0b4020340c000340c645174151800c008520074548069103c0300e441140300b1403010070704030710108020613550400003030f01040c6003e10690419070041255103002900004010f02c12848111001d07004100b0a03040102c024000d0111104800082640340c0c0280182142030100400107111071004000d01ea00403940304030110f049130f182c90811109034200d05015021002c0030700d008110b034109070000c1c0c1a0b06011700e00c005514185800054803201c01c0341d101c1c0000000d64002c0341c1d06075901088034040c00d06c05545201c0c548405203031108409810458030054850800140400d04c6107440f44c491040792101c00b10380 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 365819982 1250 365818732 365818757
    0xe01091509170714090c070f03091811071211070f0305070b0306010c11030a0f03080906060f01020d0e0a050414040302012435010c143103080703050703 67
    0x540f101071501510f150105581035080c0d160401500a503800480484000e00b4500c0c85d079901302000311480320907000200301c3d580034030211607840f4051819000c181c000300840c0101c50300000040c0600c20000d44074030440c4c50350b10000c60040340c074201100e030684103890100d0340301d026170890000c29000a47e80d034410300c1c07808140d24542104030307402101c050b107500c4248950780e911401d0b103c401c01081500341c0114a0907078001012081c421444510030344401d80c083c82c00e5010b152400f20010400c03071180901c0c81013100303666000720340d003154a138861410008600760500468101d2103950302007074101e49030034002c020b4117210f2002d050280f4400e900038032003181c807244007483c885c420b11035210014030074081c100f20003c0300d02c0940e6900b5124220380010354140301c01c03a8503e4080c0080000c120b0b51a0440d011001d94001580002c01101c0a0710030f0070499520820112480c40741c500f90b4403520701582c011410300301440403e00955012134a1a51003c070303445d00400300d81240101314080cc2e103e24101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 365821232 1250 365819982 365820029
    0xd09080f06010509091c260402090604021806041e0902070b01050904150905030901090e0915090a0516050a0b0304050a060f0b120d0906020a0c060e01091509 69
    0x10304a0102140040510780d00745402c00a95100c0984800050f2142c000800007500b11690401084010382d1644003c00c52181c8900e140c0310903c07440c003400c1d1b03890302c010000180d548050702038102c072060b00e005840340c11076150100a02d02509209a10103408100040c10994071444500d0740100f49130300c908060360354500b41059029100c002801600d0840c01070000b1300382120010351160156041c880c540d110300381e03a10101c644100b001d0b5016003000803808038558100040500400103814011118a0401e0505441c1e1407000107001924154201149a0503000c0100018070358020040e1b65625000205081440c031041c82000e010f5654000000b5282070a0425a84a56040400b40458902560702c0e03000900e0381e035800d00002030344d816001303c0c40d40340d20410000070302509000300109040b110001d84201c44640c01102154004041000024a640c04504c11211541480102c0101510058540c0c010319005130900304c0c8031082840413268468030f41c0e411248803d070340400c43c95074545403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 365822482 1250 365821232 365821243
    0x12050c0c160e040206070204091a010503060112110910050307090207060f0c051204150e0a02040e01020c03192c0a06020d0e19080d0207031a0708010b0306030109050304080d0908 78
    0x400044428140000d805820010000c0509520023000010342200320f03625440c840c0180c1c4c82d41250a0806801031020b03050420095014005c0d21019030202080c91faa042901c3c07a100d205a802020280e0100c1c2c041004509100044c1800409840b0116240c004003c000d420500382070345d00c00d0501803005401c02e0710303100e911420780d103550716586040403819140a40c110080d000700d40321030140c28059211a481e106986030030100b04040c1c10324100500420003591040d100c00040342e4030400602c440d08200004450880040e9403034000b8084007024103036400000290508c110b0400020014450320b40030403c2030404104580c081e00700e507290700040740e0300c07582e40e003188010072550403400340c2c3c1d45005241203c4088030b03000c0003800c3d50303120465681003c450704128005a4003c41c018410041d204107060b0043c0c042202c2d0121074a0040c400424806041c17003550092200000031521640717080d0085242180c01004490b0745640d1190074640d11030324403142e04001802e41802203101b41d00840d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 365823732 1250 365822482 365822489
    0x70606061736010906241701020f0a0309030f172403030714060f060a050402030a020d06030c08070915330203070c0518010b030712050c0c16 62
    0x4908465a0b80c80010018401c010a08440d081c00442029280c45404118450800d002903001050220061921800f610594819409007149a81d1b10400d021600342001c000c0b14660501c0a008200d2920158024031491001d540e804500140401c110364154110003000341c030903525101c80b034150000494000009090180c240c0d045d05000c58070b204034241d20342c1c0d4242c454488500d014450b82c80007a146502403101168241c1d000e5105c01032222003840a168807007110b0360f443c0601d1401c030f000100c54a0b12405182e101d2540032012520b048402d43c1910041d0700072000130041a6201d0810494501441c8a0003205101d41e100100d143c01c698091003941a4101300e900d01214103142e90000d0f000003400d130850991031100b071440c0e11400c2d2407508040c0b00003250080d6590f4100d908020181e01c4064101502405100300004103210821f24124112090221180d80765112043704482040410744031400b420b05100c14084084415002002c40e59140700484152844003404056030450520 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 365824982 1250 365823732 365823767
    0x60f04051512010b0a0905011a0f25020402220b090307050f1c030e040b0f0906040c05191d010e030a080304050709050a0c03060501030608030f0c030d1107060606 71
    0x240000e1490811445240201d40c0c200b00120700c200d80c14000c602d021215600c140f00058031000100030f17840c100d18942c0c084204a1150518140c000a006602e9108002410201012160034000015a5800c1c203030301c26a4020000c0d56903446200e11003d641c4860712441c80c1400d1a11030009992030080d0403180c0c03901015024003405454201045101e0460f60302c03694000c1844c100d08032017032120500404015100b0b4682d0b110862815051004032490124070900482024103040003a540ea940c41c59401441120007040142e0300e044220b45601a8182620315038142c804842e5945070030150941c001c1180b080c1d9115001000d40044411407411205140c054001015250115001400455000b40a4000c4a600b5030340da008090440300210340340341c2055590843c1c035450540c18002c05001b4042441c09010786030421944036168800d8500718442c0d50f40001d244001c00c0300034001d59010f4500d8000c1080b481001d40c074034004542c4030305002c07180c2c2441c000307010601a028510807a40000c010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 365826232 1250 365824982 365825011
    0x51f08091b040207080706090c03060b03060403170601120c030f20191e03090b1f050103091109070906140f0406081f0f06020d030615030b1c030305060f0405 69
    0x107007408003d6001c0641aa0030300c4040202c1c1001c202c1500441c00414421078000da48a4907504049049680c83c4812920030703000303c0700f40070121307502a800040041414032100c1d460f80f2001c00607904802d1413100340400e03c1c1042045a5195010744c0298043c21030b1103401c1c49804500010f051040c5450310101882c0c150920100047c08814480c42e100007003070f030409403003802d010039040c880e2112211445002030388507054a020066440308460b00320f24525a40c019650340702000349000307141c901406040558460550044c494070014602d641c0740041c01460b09410039000041c119807150080d5404154011402c00300719201c40204e0f42c4074084040c1c07550500341482c0044034110000f9058180d000b03901040380580384101018038000b0906404c81100305490440e0182c03c00d0000302100c01403619000b000c1000901d088941e105c1e009003894002240c00c500720005924000303510b80c0610051901129504050301a802140200700480300180c0060300002000250b85085654003c0c1100f103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 365827338 1106 365826232 365826283
    0x9150b031204081b01030c0f080c0906120916140f04060312021c0216031407180501050418020f010c0606080d0503040210020c01050415020304051f0809 67
    0x30700301880b851010907c090319100c02c41201e8000e110910001500991500e011100040001801551924400c0c8060101c000049803030003401d20606084c20720b200c0307603103a0100c1125119140c00701410450824854030019822a8540007602c0e03220106c0080c80c1110b001002c21403607802030140e03501e09107400e203101c001d92200c5825034002512049840c2e0340400d4010940b90401c101e80307500c1da80e00074054601501395000715840615502076500300c2101d604a18101c98045800f400082d940d440740c4480352000680095110740790184450300d95000e40000061940100d40000b0480d94a81150f07080201c00302c0c5201c000780c0000200f208515080b444070000e40001d100404c0100f5003080041c000384135500500e0380112441e060360f46a544200201d030058030020309550881c014030443c0c3d40214012094400c00300361007c0000b09030640002c1c2c205181e00008039803150f11410f = true := by decide +kernel

theorem cover : BRFrame.Cov 365647482 365827338 := by
  have h0 := BRFrame.cov_init 365647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 365647482 ≤ n) (h2 : n < 365827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
