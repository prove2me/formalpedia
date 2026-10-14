-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2299
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:24.912051+00:00
-- url     : https://prove2.me/submissions/a49dd955-3f6c-44b6-810e-b3a38c274abc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 413309352 ≤ n < 413489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 413310602 1250 413309352 413309381
    0x1d010f02090607110d1407210c0e070903061b1d0603060d1e110405060a0303140d020d090602040303021501120b0402061207120b01170114150a02030319 67
    0x301403103511007a4182103041c40590700f208880010201007181b407200c4402c4c56400c0409400d16a01e0300d60703581502e10800d84624000300300940b404000808502c513000884101c01c4000c503150340d60850503125110309074006469281003904086090032031403101101e401c1c0c02d855100b900050440000c0c200381d901f10700e15810050403c08204240307803c013030b0040841e11030550342c1c0c2c0f145000034891002c0104071904032030380c1100035404d081d80c0c03415014166103c40306807111091b041c9152802031084104440d50a2030400005020040f1010342d0102c4000402c042814084100b42d898500c1c001e40c4148000c0d00140140e43d142ca4150402084060491b541c0400d801c14601c4c068440000c4800041c00c01c80e407000040211071512481c082890744514a1b90700c80c4644011560441d9003918081e404035030401c07200200055035540104039050540700444410303403482100d400401d84113180040002c2041c04040b030140005075000001f148a004d4000709031411002c6070b90400141d62074000030018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 413311852 1250 413310602 413310607
    0x906050f040902150a02070608010b0c0604060b0102030403050a140d170a050a02091806121f0207030203040302030a06021804061d04030509120703140d020615131d010f020906 77
    0x52850305401c00d81d8030600060003240348106605141c4a545e0101c1c0c0d410740583c108441c10850b032900200c0e440d005140c145051441e0500b801c3c403194454078001c000602e2903903a07514075540c60340b00300156030240d5441801c88a410285007042a132016100b01c03501aa0f2240c44243c0388414400d00c03058041c04030b0740b889003070030b6100d02c010710020b04030080100102503800c1c410319070160b4400c6e006000c00440c0c4a5021038a05040e414818100f544110700b03181584048048440520424590310103000c030303a240183c8401e014074089045d441070b80d202070f60512031600301c1010300421387c0c01800031040c003c03100d844a204d00130512040e540a0311070f0800041007003010b800489c010a1040c0d9001d8030a01d0182c0c941200c20001508601d21a081c000c0e080d40080014410000c40940004100440c880100340c800d19101c6e00a590743c0006120034100340403403103184042d0301d07400045440a001c000050205996042c002c0200e4180340001004c1982440c0c0e0b0044025014803c5030000400544660b2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 413313102 1250 413311852 413311879
    0x100513020703032003090f0d0f0c021f080901051608010e0402010309020301020c010603022805010f02100516020c010e010806041a040204031a01170606150c060a02040906090605 78
    0x20025008818280c0078103407075074510382160307202880c054036442000f901030b6120704088211901c0d0100424040d441580402a0f00c110345401c42d1661512034001d14003411806c40c80d1010465107589016050303150f40c15010004100b0390052006440b8120041c000c100554441c8030010001c048804040013003842c020051003020317450300076035500500604021480000582c0031900b2a030207104000c00303996652500788118a800b81107000744030740141c10100c00204141c01c40d12100741500c5890b0501108100c030582070341c0244002030310341206038410010303890140032003000385601400803401401410341c6a2003d601503103060021007810b94442e081542c80c0000d0000074190074461030700091500084500e16030b1180000c0002c3e510644813080c12030140c000301940404e06800c90440c66118030368040b0501d10000e81e080d401700c0c003151121b04200e0041034807a0381c4d21901a42e1207150181208210b03100c07482c0c0d001070048440d061420865990340b10f034100c040f21494060582d0121000301400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 413314352 1250 413313102 413313139
    0x140a2607030909111c020d151d090f010e06070e090712020c070905010801020a140a0e0f0f1f0f050f09042d0902180c0a1107120c08061005 61
    0x1d809500101112440c1000860001942d05d2201d4107100300a600000d401e031602e2680e001d00013032045c0603000810845d041c050b0076500c0c00b4090f0113000e0b01c83e08440000c7d40400080013440c3d100c81038100201300305807203069038030b449450444414020600040048105007407442c4c3c104c0c40f501c2681d446c1d40360300101c2400c4030065030100c0c4400d465846070150119141c0304c035110319402002c0b01000160b0301c040c0450050548980358040180400c014440c8444080c1c02401c00c00004034201c1d40c0140e6020684001075501b580101c03aa43c000d00c0d0001e015502ca68181d003ca01c0702d02c00ca44403c0b0107482100000c075040c3c40364440e8010011810300003148079040a070800400c614000c481a0740344100845104c500c4002d45210004040d00e80708100154140b0b51840d071404010901c1c1c8800720715040c01d070300ea0306204102c9107200300520a400c20621031001e1140c14068504510100c10031107040c101116143c7ca54054000f860140b0320104000617106100701c000c4a81c09442c1841c00c03e801c003102c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 413315602 1250 413314352 413314361
    0xf0105070624060801080705011b060b0409170d0e01022a070317180301150605090d051b0a051f0c11040204030602072f0607140a2607030909 62
    0x10b0b001e6181c40580400c4440e04645046000340541d50f540100c2c85d0b1400b035080346018916403100c0d05020f511405140241201e840f5501c01580003540810304006810105008004540c0098200c0b40d4003000704a40406200003060030307084421041c0440b000c0c00f240787e800c0344a50010b00f10204208102044d08e40f240c801c40000540c61401031300d102e5562038480300100c01c1d501d60410600000001c126034407000b42c0071440c1c0d007400243d008004c80d10040030755031000b0645019800134004003041c060040e40d1542c02c103049907907000b0280c1c0c0d021040383c428540c5000e1100752051061100c51004143e5003001d00050000b24410328030345025034199181078510716240c11041d0380d8540189100401510b8500040000398402d80d00180c0c0c2d0710141c00c5c0039210740582001c00d402c60718136480d609413100c090f00d01c040701d0842c00c440107980d540d500d1030140c00b84980c40880941c1800340350389030070502c03528124011014005001001640110094402e014403414030001c0228440040c1804000580c2d0310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 413316852 1250 413315602 413315621
    0x80d030e1005040303150b0403080f03091603030305010f0b0702030c061b060106020a0b07030b130c0504050d0605090c1005030a0911030609071509060c12022104140f01050706 77
    0x75240c99005010460041d6001140c043d400b00361241040d206119020340010300401006030a1400d140c1141c0ea810120301c607040c007100c41c2800100c08248080740034043c1c00f941104a80c010b03c100d40c2e40f460040c0c0540801d100f10b0327015401e1008c0000303264149904a884083d4024042c0840e07003960380070003100d40c005161340001c0407c0c8071094481c15008001c0a07020709040e400074040d4a846151146400700010704c803104050500c0c40e580000d8940b18490031140780c8401000c5110101440207d600d40615408240e103c03013410b1612003400a60740c0480d01030320000c010b941980c00b0110900c18984040401d450001d2801c0000900107826540032180c51880740c14014120001c5500107450400c050310200000d402095080002c40100501404a0a003d0810f004580e00d000c034040d080103400403028107640c0c0c4c9480303400c0b440791003448030003250341d9904000f95003101c92410781a2260018019000f0381b802440040349145030031040f030f110401059481d00c0c134100c01c0f503440c003018081010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 413318102 1250 413316852 413316881
    0x309060a0306172118090703110a050417120409090809040603060c030b040e07053d0810050a0b070609020909010209040b060906030c0a0c15091b080d03 67
    0x24000c50100360014000300c190742103400520344004c0181000c13142e490f031051039059424003044510095071045084038003ca504445141056582c504180c000d803c900020070030310503000030100c511a4200002e4030544216400700c04450780c02c5018140d0b81c1d9502c01110030040b00a00003007001d214a60080c086142c42100010308080c1c111000c00e054500b84c1d007048922039110041c00c08000c0d4584034030740400383c0031a403d110f103074241c001690722186140034890240d183e01c24a100034911800003650336603d1080707003503680b0048178007100400724070041c1e280c00508a00c0109200c1000c0340b10400c10703103200400c103c160614203406e040d0554020502110030544038160540540c0d03c880d02d1900c1000da20f000541e8036000b03038042104907410244442c2c4242c4d4140420a00c640300c171b1042d00c4d44100003d844640e00c188980041c2c44480308540000c100901e00310380301ca480b45060300400b03c803e1050701d080070350305806407009a081000d400b500b401c50f40507049285015100b6003000e860084c810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 413319352 1250 413318102 413318111
    0xd0c030812060108060301050106091a04031a0106090f3203100621050616091203020312010b0a0c0b0a0603020a0f0501110a0f060504080d020304140708030c0309060a03 74
    0xd03a611100d0380c0215044442407034014080120550300210250307031061040340200f00641c1005c001030440141401107210102400c84040984c900800071a00590741158103a0364040040306079501d141c4003400780000051004200242a40305560b11400785c0d0401e84500c400f07210329544110319000100e54081c0c850340b2441c034242c11034030280004488021020804a07100382030052102171915070100e0480b0142d8051081c01c00700b07102068041d0041c3c080c0d01c0d1188074143d03d04044032102d001c0d40012490791000c040e07070400c0503000001400e40c1e1680046002040e83d0790b00450401d802102c80d103034082450281c0100000ea070251b005c941c03043d9008400220b4036126008612a9800c503007003501c01e00c1404800740942d42c1c10401c810601c00d240401414440c03402d40d62041c08680350407004081548400102d4100034a103000c0e1903000000c2542151649824241400d0001c0584e50340c003541e0041010104040c24088100d40c0002911002580340c180400184662640700004c40e02c2015603c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 413320602 1250 413319352 413319359
    0x150e01140a031a01020a1113060302101e03050411010807031104180516090b070501090204020a18060f1d0d02030a03050408010605010503010e0a051807260105090303060d0c 76
    0x1908060728410300a40e42c0003403481c064204001d041074031a40d186065600c80c0c01a0380000e5900035000c0c82201c400d4030100310014060480d0b8000c3c01d09034000a5011180300301400155501111220b00f00e06514643c07280802c2142041d8100c4034156805400d034904489c1c0b1000650050401607007111083c60002009140c01c820000c00f0340082d00000310b0a12401044007903140e07240210703604510702002d4010404206e06010301407440510501190120100e002810320000707600140c003440e005081559100c400780401130480144114014142c2003000000c20160712880b00445c1d0740049450f006c0456105640001000208901d001d503c107400c06507401c01030700c0038003401407607a02c01e440d43d0f500d81e420403c0050944855030442c0d4100481880100f14020310807001030b40007540030b40c0014450f140c08070716150b1440003d04084c442d00c60b079100020303d803010044080702541205544114807422a00881c02c0e100c0075118413513181d0092010a94170314100008044807403054804030806030f038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 413321852 1250 413320602 413320637
    0x20a0203060106090f0b0306060714030408010203131a0105010806040b041808040e0c070312050705090d08090310050c0301030209060a0806011508060d02011d0604030b040b040201030e07150e01 85
    0x10260000780000342440420820f00740e61708488406440000034440c21450200082003950040c0c40000c0e024101810350071060650600841d806062200b009560782e00e0700c0580c42c0902891218201c500c40c0748035030141c6000142c86035075816100143d41c4c0702101c1d1200000c11020303103000c100141e0f0040d9102c00c80016043c01c0c0300041d02140c4a81c0c807058649242c4505007009900003401500854000c0240c03000081d03000340d0003c0703400003102000800d9201c1c010210340c580100308000d50171a0410308007500f030081440203090aa41e044044035a4420740070314980c103440060750400950070051005000510b05010b045074007180241c1120451542c440b0300b949044002c0e070208042010030280d14030303019480300c6825400700042e904401c2c0a0356960000b0301002c003400b00f6541e01c80100e0810740b11907641204a40c02941c202182400c182841d04003800c650400303850480c0400c0c90100c8403131071a40045140f100b01ca062950040c82102c85003000c0c1c80f40c00c001000c182c10402d88100307100c40c045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 413323102 1250 413321852 413321863
    0x80c0d021206030106050a120303051008011806060906060e0f03120a05250203030307210c020f1b0913110a08010b0a0b041a070206070f03020a0b0123010807020a0203 73
    0x404500c8500391402c00b2801c0c942101c90700e4100600410000e2018001d081d0040c840041c87c96152030009001d80d0388000a8585034040d801c804619420001c001d583c495888046481d000d0055408005065035032807144100c50b5184220008a04294840b100626120503041d40050015080d6003051900340d9218609a0281d0321902c080b5101244500300c4984480c2075400b501c2c012520b650781c41402e500040d0390f9002c014507440400114007550890744405000c0c10f0300000044205215003a01310001940354031440600072040c0c400c4281c2c00102c001c0010a0940d0048041c010210a445021007038030048082c00f420347d410040c5017002e20041e102c02d14460020103070b02000194120110040000b0440e180c1d1005000d071409210a10035030045042030030101c418046515900c80b11440400c0450042140140440380c0848a5100f45500400c007101c100f4814000c4000507a2181e000900e259455042c0081c80314200c8003d0b0100d5001703c07203054014240d401147c0b500407441d0300103071070078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 413324352 1250 413323102 413323117
    0x80903010b0d2a2d03050708030a081609060807030908030103150b100e040b12010f1506030c0e0f0409060606202a0d05070906060e030a12080c0d02 65
    0x7281c05641035040c005070b041d0202c10700c0b0b40800f0f2444015151480b40c2e980c1c0c030340d04030041a01c5104003110007440200c4800c500000c59102c0c050b40c1680d43d1f0360b604181c1342c1c0c21504028001c10104800900c0e100f4010a0060b0444c10035280e5414080c10441c080b03800001c0100810207140d600d4914601241c80540914002c510910700400b00b49007400c03a55081c3d404220442d8065008a00c1c40c0c204c1d10341110304000d0b2628159000a0095030745030000d0035070384125502e04590b500c1c004440b41da880803504461800c2000032038240b00c15039200300c120210350b2072001940005002d00c00040e101c1c46c00142503803141d08024000310b5580c40c0c0e0748800c01100c5682c0c3c46000072408600e068500c2e0310406005080c4a00c8050213407945141c0e000b0780c20003440c0f0540c0500326038038881e03007500007903600c0340184424142c2050444d44120349603e844c030700806031402000003044400030020400e140000740461129848445000000715a0200b900c00d5400540303900507501e000e10441072034264600c0503043e0b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 413325602 1250 413324352 413324363
    0x31605032506110306130507020109080f030403080601090f0911042303010c0504080703020402070218010801050f0109050c0d15090c120e071a130f081014090703080903010b0d 77
    0x3801c41450b00608940300320315a1a00c201c000d108101a964545a100300104951701020400c2d903500c0c08201d004002c4104001d01c40c903404107401c21b0008690001d10f01c1075110381c5904149880d00001075502c1b01c06445108010182c1d00301c20701420005803c0416418080445141000d48490110340d41c2c0c00b44809408201403c10b203c580940b40900482c880b0f5140e070b0400f40e14160070030780c05607200c150a01004e030065400254020441d08c80002440e02203200b00e84000d032658560488030f000c0c0030141c800089800b803034000403920341070b42d2151038041c03460346000038580505404458040e15240007500640002c890001800c80040d000d020490851603072060140d1003401c004504590720041601e0155001140510810607607140c0c04100d4000902c0c05a119001286160b00642141d000b0034030701e990030240007801c51400104a0001909500180107200c0b16240c1d91240e0141100e0440071540320b06070410200394030400601140f14080e0002c5803240c411408512881c0070140c04490 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 413326852 1250 413325602 413325667
    0x22407051606020c0d05030d060f0906050609011b031419030f0225110301021201061b0308060d030908010e030712030b060a031a210c1203160503 64
    0x420006001011181d4149040321000c9030820380029501c00001082c240990b100e407003c001400030420583d407207201c10040038490075032204c0500150069500c03c0350103050902c000810289450819100c00340410b07900c0c5402030603120030200c1d2a40b60888103605000c04045006c44101d074940092143c0c1c41d210700c4080d452041d100300101140c2207041a1070b102803061110301615188a090781c4811034640e0b0f50080307007400380e040100d00030b002d02c7c000c1c50b1305601c00518600141a0145800d040350803549408407a00d90708080348500180030600100020a00760000e20a4a4403082030b025481c080d00d404858191584526800c40e42d54503108120380d840803541400b049444c505103004400a40b0313003844000700c40ea0206001d80030307c1c480720043c9031302e485040301907058902500c0c8440300001c01c84000350b02081c00c040b00c141c0742050103d046000302142c08816007001948520101c0d4400010f500d070400d0b00c00f19101c002000182207650713020030010b5184822000020102c16096a01c40d05c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 413328102 1250 413326852 413326867
    0x60403080106020d05040e04030806130204030f0c090e070902030a110309161a03010b160602120402090a0612020d0201030605030d090503011a0d030c030207080703061d0312130224 79
    0x24903004d9002254420404200824001b1a020f40c0300a134000354141414842038840c000091031400e4082c0d502d0011510102e0000107100002ca54403000c13500440174101034586440010007526450081441240d01040c410030582829a0003180e100c40749100000384080d821980010650058030012500e81c8101c071503001040c5825840c40040c0030403010050340052140300c035144c81c00148151080580042140c40c44501c1034180c500201c1d41c040421584d40901e020300c00072006059409900841a0900281c80d4501511541040e20315080f8018030b024015401c01403a2559900b04a0400d5124500090a0741f400c1107514040360503900c0718102241000141070031540700d40e5403032032080d030b00c00f1b0101004c0d110502d80e00e402682500e8402c101c000141416845c0c401a540055000c0c890740707200200f030060580c01304803004200103528102c030131400720403640d134025941402c014000132808036100040715a101504a44094200c081c0c03c03043c0103401d000848818000c411460f80043e203107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 413329352 1250 413328102 413328107
    0x30605060d08070f110a032906030706230a030e10020903030708030604060f060c1104410703090512030f0f0919030305150a03030e040c020705120a020112021204020918060403080106 80
    0x80d40040002041d140b80c504140000e0b2f03101050320642e2b0038484000f079011686482c0b80060300940070061a665a01c0c4101c0c0b100800400030041611010300030a05200305000450007242c0e95604014000c1d81890300f40d851b022101d5001400d1194030658a000005e44a844001c0ca0b400070005030b1110701c1d80c0151400d01c0583e0318501d0b901d13a0b100c1d0740340615220071950200e8120b04010706240c0818403c091b00d940c81600751110000344900714900000300008076615401c80d0121a00c200f003607400310400d0101190700c5003c01d486045850074103c0020f41c10010f4202c07100c2c7c2c000d1846d4221000d90908681d0b15117010307007104003500001d4a075010000200340c92210368031813000c2545c49100040c82d6440c02041c9901061405204680f10724203105007520812004000c6d100c001c040c2800c050500444d142e03240c02c0f00c00100d01003042107000107001070381d40c42a9048a01080c00754105c660319075082241c1050b006040e100d2500b44d008180c0543c00040003410b1084d4481c5d10b8612855040c604003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 413330602 1250 413329352 413329403
    0x6090203061806030307060209040209030f060105030706090f0b0307170c0702090105180c030601030b03011e0507140a0c080d180b01080304050f09100509040309030605060d08070f110a03 82
    0x41400001920900c6803a44000040f206c881c0c0e00300500603140e02c1c1c0c002c00100a442800e020962501c42c00015820002000c81d403d030403260200d0484505540e900000e903a600703114460720f01042005501040008000001158800b400b0700d0b2035010005404c0307036410510301c1035a03400b00302040807810b0011418040071031409010211480380d00b1000c000710083c00c04500402142440e900840441c03001d034000c0d04042c64540c4010000c0c00f8905944991243c440d6411404021190400c0c000c108024010b81000d440c000041d2605464007840f250140c42d036144142044500040402400c0301009240c498000042001204002c00c450079080800c8503c006801032502c941003080100020f81c0c40b5115041d6036481500d0302101952060b41e804000351030380c0d000c9504826100208020158440480c000341e80c0f1480003046240c07205d405001d1410102400245045001c000840208170710944c6444912302c0b1300110382c0d210503404086092450a648101c0c0c0580c44114030807544800200c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 413331852 1250 413330602 413330629
    0x50307030606090b07020f0a08011d1002120f091c020a02010e030c210102070c030b09100c140c010b0307060c15050609010b070f050307230c01020706120f0609020306 73
    0x5100f0049803c02001589034407171034100a12948983d00185403a0711112200340040031200e000b0420040307402c101208800300044a0461030184140d038019400251007900c4003110080800a8180d031090001c1c1c010f564064050000c030721070080b00d161100b00034070510313150345500c0d805803070560018030014140000c1d4800c031504c030703401164240d5400d444508120038158850042500d4071002c00c41118024030500402a040da907410700c02005014048540c18040c3c40014225403d008100c142c03030044504882c1c4c0d003000608110203201440840070b0240c6109008400001038030b03080d0300c001918100c600d50102001c580d41c03525000c280110000320302c80301204d20a0500452070500001003003100f050091007001540824150140000c0c1c82d400d040860b8020304990740c4140a040541d080120005074944410b95110b180354401d4010510010061068008141040c14600241c41c404070007162110b01650380c14443e0380a540c5401980004d003000700c00181c0c0e0303091034000d01420500149 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 413333102 1250 413331852 413331857
    0x80603060408090402070c170703020901090c0f0305070512010e0105040c020615060f0c03042303030a120b01030b030a2108040323120a0e011b050417120a050307030606 74
    0x40802010581e844100c0c2c0103c0303c102c400598943c5107140158a964142e00680c18020041c5080005000001a14030569008540c40c2040e81c2c0e035515020182d0f40d401554000140e060200d28041e180241c01c103c0e0400b07003505046082c00804d100b80365003031401f40d01c000c2e0491161001000141420700c600e207035401f11031003e0580ca241c459103103200307400705480aa000ba0340018070b203032034a40c006090314942d054110071380355196070b1401c811032007240c0012100032131440c50702c0a445600d80081103a0b034181a6849003444241103140060041401e648028141038031340240110070b66040c0094032000d441202110400c00c0d1515011710585d04004502c800d0021036400d1001083e0000c100380e4112203000406400340b15429016501400381c20803041d4122800e01c24011451800e802004803508480020062141c0354240b00d04201189014500414002c000600002803d51b4503081c8000482048410019000c11040507176440391030750a00148022007801110f90707060203041d00500951 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 413334352 1250 413333102 413333113
    0x9230312010e040302120f09030706050403052a0406030803100f0506030a09030311032406040501050d0908090d1208070f2c03030d090c120804060f020c090a0903080603 74
    0x1525500c00e014041c003074400c1d40d2120074002010544204001c0d26104200782c00c1c03580798034803040640010b03040410114400d00810101141c0180724009507011260010000c0c805403600611802d4042071140756540a071404c5056076802e61035038043c9100442c45401110380c0e03031816240c007501c052000c0e000800c12200c000410022135070b45106036500410000800940e07102245000d50045c40d45003e02c942000b000b01c100925601c041a0000c43c0c0c8003100c80b10030441d0411010480f44d441140517030760100701c040c8005100d0001c55404664440d20405200f45000300701000202c2195401200300c509901612461130b103250700503112078011116003401003955801c0358024121085500c11410105040c208042c03401c05204a442c40015018041c0da41d02c1090482e10405400c10074425120f084030042c0024405912208519250b0b40140e0b0490400c1d04000040f2441e86240908a046210310f8a0000386540e40004c07440c05213074009400240c45c0135518002c2c040e0b4000401242c42500007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 413335602 1250 413334352 413334367
    0x706060f06090b0d1b0905030f010c080c0a1211041701050f0c030411090f1021120c0b0c04060e030a020f040e0304170609071a09060702040f092303 65
    0x48642c1d4020703561180d07009a12032196000000042c10740184260b4000b8410000851030b642112102068070b0040d010703030704841005648142a0b44c2004031800000c0c0020002449189880c0044c04981209143c40c462948401c4811000c0e210241241a00c000d40014104130001d400d0000e8044151507400a10032450198500d9040050080c03d070901c150700000068200102c8900114991000500784013141c18052143d181100080340c0b9a940c2c48800d2070301040d440d224480c502c0309204140117030b090720103942c1e448056402c00703100707000e00380b203000c400f01c100150644c602180704400c5084515140c514001008114810001060307000c1c1d080305c171800000d600d40c4901192100c00c00c0d2000b0440380041c111103851480346900c00302c0088561599000950320101302c0c1c9004400c220201c1d200c450b00c0d10b1118034031442c007410f0300520700750400584100307081070805011114001080081c0c0c0c0d860211260068440108007258a0f01c030207140c004142141060b03549030b01e212200114200a403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 413336852 1250 413335602 413335607
    0x230108040b130c05060a0c030801120804050d06020f07050a11090c0d0c300c110607030b01020c1011060f0108070608040618051b06031902030a0b1002030706060f06 72
    0x1c000d00310740d8078000021405000d0002040541c001418080c0145a072001c040707400400304156400300f01d0001c6c65140001800350400b20b401c0650780e4114070b00e907281c10320740001c0020700c2010700c0c4115149038080c4103040b414154074026046280c011405410f450000d880d05d4000017035602d01042c4a2a860700038840240781207800c0d81d040300883e01d00001c40d41c002e2501a902d45120601d2031107400d0034508040c0d44403c0b0100401c0b03091101d40c0c400d000884204d9002e07104003401440452190b400302c0c0c0081d170706502c03940100c000d82c0410300590781440030010210750400400c406900c08150380b001303001200b8008010031075000320044400001035040140f10ba17202c0505d80705400c10842ca0501140910040d68440741c02200d8001c109004044a8a03142c3d4036580540d101000300300c1c240b03003c032844d414003004070380c403a0400d445280644445507034900000d400240140d91a1a81c1c2c4610f50030360780341c000000c0e00d01c881c1c40c0c00641c0c03030302c4062070080191401500100408007000c00c08100154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 413338102 1250 413336852 413336873
    0x70b0a0e060d1b050909010f0303140a09050a030605040b0f06010203090f061b070303021902060316020c0904050325020f06030408160809040b060315190f23010804 72
    0x30800c440c00c1d552848a145614060702025031009082c0c035110049480c3c0a400c00014001c1ea2030640b584001030f81d94002140c140102d43c4000f40201c0c08514044005c0741c409002801c09800c80d05003041c03010386541c04542e1403480c0d03400481e03860b5990814881800000160154403585a1000f100149000c0c40002d403240101c4544900034504041d07440300c0759940710180e40314520320500c42c00307005144004030f968a550620003540036000d000a50340d00c02d08003101d100041a00508424910344070500104040c084040491085004030900025a9510006d446001e81e0007880216121202804500c440300030102403803290000700040a401030715503c0983c418020206c40f115100d41e9075092111844c8650b074031180b102240c01c1c800c00200031701507003d440032010a0314100301c80300100c8244a900e03c0700380c0d00c86c00c008440e020861210301d13203000038400c4150801c07186032207559907145460f040ca030340341c00c45507165110088003407030b0950388988001070000c2440c0146c00c45c1042c5c0c8810a80d0f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 413339352 1250 413338102 413338127
    0x402010c081e0f1b150c28110f07032a120309090f0203061c020f0a06080121030915180b09012007050103050a09020d05030408070b0a 59
    0x1440c0032038485000c840010081044100240500f5552103101e006116079503c40c0c81022420340410340f11922480707000408140d004e0b520029028291038605020026030415410004442e01441a5003200c103450981c1c0700b000700c10743d25114440452130302c807079081030780070b59443d40036a0080d07101300042043d1402c0240c540a141c411038510014803004941f2584080d00306041c41c4002c166004100360740540a541122000d043c10002803045403042001c1c0c0c4400d41d0520740c007005200b81d843c3c190001900c1c81d21360328802860070820016100114103019441c2d440a00807402600c01000009250b5400140428030391580c0345035449a66409030000d8803030300a0382c200c201340f9451501654060014070404150810754407824907036908000400740d006284c55800a40524101c1210b0520102c0220002501c20042c083d01c0d402e20300110003e00c001020051240e4031948040d0150326003020480d0800d028001a5580c0d509107803040f0708d480f9036617100301d42c9003000300809148170743e1280e41003004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 413340602 1250 413339352 413339363
    0x60d0f1104030f02130e1b0d140f0f030702060a031509180303050f0f0f070e0405041401200d0b0604030b07020a02011409150904140f0105010e09090c190906180509060402010c 77
    0x80551804140f000884408c018100d407150440d0815080000540d0482040300d00e0840d08c1e0604d951a070103480c3d0246030300094000c0024040003071058040d411520401d461403850f90340c10b80e561030103041664401080d00e201340341020400010306906000b031030750107501114201007600b030001d2518418000107102b1000d450701c80000c111514840d00c09808180f40081091001313040a05001d1983c201c1c0304c805800c00e6191184030010710419140c150110002c038040141001c0c10b0000134405004d9017400590300410401002c00062409500e0500624059008044805540c400540004820115420020018001c00c4403a0b40d034519400d5403903032540c284540320301d220f002103406403c00c0e1660981917802d0380304010030441d400c000d66048480c01d0303079068007021152050156820055810409903040302920010134146407032409490600e0645a0800540c0c807503146085541981141c1404420740180c100c1d210083d01825800c04490000382c0914145940040c010b0080c1e804010300c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 413341852 1250 413340602 413340643
    0x5041107060b18090303010f140a09110c01020c010212070c0507180b0409050109031404030302120f210105130218010c03030204170a150b060d0f1104030f02130e 71
    0x1a64540d030303c0f80c4012011101c41c1141a04000c200e040d16500240281e90444860040024140c5000d2490134400403028217098802820180c2100151101c00040500391038204000c1e481e002c02407008042d0031941800060712241e0701050420f24480250160b0704002a601d00340300450004200316046440100f070711a02880200c0b10f140c050692245013030381c01441c01800c10300b8000f06412441041c0d1080c0c1c1d0340d00c9010b122082d050f656009a001c0640160f11044d0b034018100d406200400e0350030f0842001d14205032580c080c5170098804040700b010341005010042140d410308064180001c0f543c04819420312190000700a40503501000f80c1d4100030081c03072000145401703941224060712820b18415400600c0d81600795852610341401c8580300319940c1001808611031207480101c0c0c10050078a841c040002841382c000d00340840094804903a1101d088100010303a800034002180b00d065900da80f0005c3d4010044169002d039001101e080c01d0540503003040c040401d41c49002c002d410301125 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 413343102 1250 413341852 413341871
    0xb0a091508032a2103060a050102030c10051909050d030b06070816060b060d09020f06160f240507020115050907120b0406080a14070f05040e030d0c0e0a0504110706 72
    0x28034210026180044540041241504c400c800c1401140724100940d90b0304000d6030382e040120380e0f0384211481030300d050704403141c4e4504e40d1a098003c0354000b80c00840119100141c54401000c58040d01002c0b2038503408680501c045640501450080034400c882c80c50500c1201e80365051148180300d00b51402d0414500b40100b0040264880041240081d03e00e64036601d11040303100080288000982c45003044621000113031030440122180d0354030b28028803182520640d91003d002c1c1c1c0701c980440d00401031203000116445214455000780b2240c450104250401810103801c4420801106407401c400346001d004a450340010070381c11800304e1500100305001420982d00230024199000c2d4003d081c624005081d18000801b00a400e0103203490385607400a05148aa54151601c241e01b6840500e81042003189003542c0101d25980041041e01c1c646000c0d40000f2044a16412486000c01c00c506108038441c2443c4030408007801050314100b011503d01102d041150284200041446840c2c0d494178 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 413344352 1250 413343102 413343187
    0x180c0a0509121006060e0d020a03020111100f050f090307031710031502130b030f0f041505041b0605040b030a020702120304030b040605070f0c02040e010b0a09150803 73
    0x15249040b40000341ca01c56003007004074a01074080e42c8211000035400c40892016480d00c04507101c503041c0c1c000c1c9a100c0003440c2d50300564854002c1c191700c0b03600e4022141d401141034844d00071402000d0340340200003250b1420310075403010020040c1100d4050340c02448010002500a9000c86a0300c03140319008426940c1c2c3c060507040b4507016000102111403002a81020100c1c0d41c000d0916801c1001101c0c8440d40c07074400d541c013540004c0311079100d41208076000c40c0364900d081060682150080c0340f15240314000c0c2d00ca540c01c1d01d1090b6002c4650110301c40d41d50380601440d041020140000d07280040c9428604400c00801d07000151403a080c1e280c0c001032807001c540d2441c086403010100c6000b641d031500d5a1781842c24080100300da047d00c40c10304080006442d14446c0384454080d55140d05c0303003540d090300c940901c002010840e41c5a58190f5884c02d107000950307259560320000300030701c50020880d00d1000703181a94902c2d43c0e0788019600e5205004032640041801d038440c009550609021403140c0e03444480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 413345602 1250 413344352 413344369
    0x9060901110f0a0305090f0103090b070804030318080d0f0b0d3020060618060316181d2a040c0905010f081b0a0306080d020c180c0a0509 60
    0x2c007002c0c0c0b103503a140070101034022003d000f1100c41210240c150340c8002d00150103580c41d80c90020000e202020001d01514091402e494015001c0d103000074644000c1c54119000e201c5125003611454000b1400b48042041c0303001e900d4441d011082c0900842c00720001198507160100310040c4020380d1011489103240c0e040000c0d41000c8540841c11154141040015000c165401624200944135100350a80514001041c1e400b0303074000f405c030122001103104c1540780007a0140c06150701d0300884581c05954031a011840380a000e1520204d0b04d40c030103180803542110300c030380005600104c400e0f400040601002c20304010b513140020050b41040c1129100400301e80040f03807925031140c40c10b0052000039034051206000d4403020788075800c00d01d01c1a02d05a41101c01207030b04102c801016211428041d8022018180183d102e04011401640b01c1c01400d04104604c0d181174016032122840090344d281980081c00f443c13460810540190802110a512520841e01610284075001031402c0319511031920 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 413346852 1250 413345602 413345623
    0x11040b180402130305120c0c060a0e03060f0a061e0e062103130b090a0302011b080d09020f010903151d06090a0302010c02010c09030f0609080c0a0213020906090111 72
    0x10455032240c030200b02c1c0c10290f142e40400d07600c038031400d00015102280b0000b218400007032500200f03840c004410401c03140b42e1001b0000010042c055002c002e43c1d40b4200b0100e0700403c040403080503070303181000360141102d645900491a0031212070144d065445050380b19015100383c1407003000c8658034680030541d41815a51200822032001c04011141c440100107800c004c0c903505055003505542c1c1103003600038016401a6030b44030400120400066000d04070f007540c0784070170700460014400e090f1210506a0455400c0c0c944194490031520304515050007421000142400c1070b00c43e081c00c54807506941c42a6000d80b8090a07a504402a4154840e062188088680300300b100e205141c110310079504c8240d440d904802643c280748100345454010f000b420030700e01d0555a00708601e4590b4903114146101d41c082176421039511640700380800c810000501032030b003050000349982c0000d0310501c02003002c004036421040744107001ea580342d40d0740d0307104480340c01c0300c00d19292030b05121455180e82440350550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 413348102 1250 413346852 413346859
    0x140a05040f0f050304150c030806132306040f06061b230d03050106030c0f0810090e0f07050406180213050613080f030307020d1b080409050a0c0311040b18 68
    0x5041410083d0004c01001554040068228004185d107825107111079554070003001718010400241480c10003a11039544040c0700c40d804140e8188400c850708861050745680411900014100203060906000720046012141402c200c181d2400400800c0442541d0080952810051550702440704805031802403801e461a000618442425000d56403410800a100800d080500019000303010348030300322201416481d500d03e00301006008840340c90740205900c1074038070b981d14041074054140c41000002126500100001502c1d08440d5143c0709065201a100d1424000c00740503142007080b0030900d500c04041c01580b2602600c010740c10100d100e4020a8002c1404104d105203102440300020440e02c0320400c0e501e40e400c03240221926840126039280140e40710010071060310f4072031030400981d01b0581030250f40b40b4102c0d94072441d8a5001d40d00c20b00425868205102c12041540310341041d16005040410650320b9000c0054a14081d904c40c05005000100700c48448001c1180031030801f400c000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 413349352 1250 413348102 413348123
    0x40f05092a0414030a080a050c01022101051e030703030e010c0203120405210604030c0f0c08010203160203031b09010309061821020721020405160e0301140a05040f 72
    0x211000c680a810500c940540320b5840103d0b0000c904010070808122070700010181d2620b00c2c1140256200c0d84420154231056608100e42d80340b070040808291a1140c01d1181030f4100c3d45000204001007003024401c035927440302581d60030100c0e5400507200c0100c0e58107050540c03034030407078500607107010354010400ba425008081000ca09105002c000f441a110211403c140f0031081080341d800c4a00000f054083c65031006011802003030241c1c080c09a039074402c80e540301069805a450551030072281e44500c0c003982d004411300c00011000d00c1e604000026500c021800d520f002d0148003200d100e15401030403100703070000e0381c00c505034440e40110215903000402404034642c0050012009481d4150661746420061106507042d203016007240d0704140c403980203010301e50800400010004000d503d0300b40c4550ba2107612030040c0c480b8003c05200300d4680c3c0c14114043c42c000d07406403807580b0703950134a886645415240309001035186013080e00880d41c010001019034851900708005410810b0182c00d10060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 413350602 1250 413349352 413349421
    0x91401140a320403060f060b040b0a02010501090c020c130b061b0c030304032004270201020c100c031b02030102040e0103030906230702030c09011d0c040f0509 70
    0x340b054500d00240049820310200109030145600c1c074103000d0350303060074001c02c8208040340b12604820700e018441c40340010380c556507041c5001075510a5200f01c21058002c921080a01d40a100d01401440c0307006042c0000780c0360450083d11000100c10307a42c843c03c5811010528020b03c0d9000c26251800544a06d56a00d40e142d000c5058181d960707017200940c412040e004140d41800300c182e404136540802285446408140081d07910303034001008503049a42c81107441c8883c2c1940e01c110b40c8030382c40c030810000d0054585c00024200409100890301035010141100c14981e40320060b01e981d60740501c2d044e0b01000c061130150054916941c00694150700204002c111028031440083c1261310030348600f0078280d6209025124145501c5500b83c844000c203100c003004da00d00200502810f84002c2c1510601600302002800301d441c05c2c0c01c09001016044080120100c074500386980041d40b07110028102450b002200c0300c0c1c0750141c01041c3c000c2402d0004104034128882025146000454490609154 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 413351852 1250 413350602 413350607
    0x5070909050c0405040e032b0e010504031e141b0a0c03050304151128140f0d03020c0c1203042414120403031505041a090f07091401140a 60
    0xd0b0140c2482503140104501c8911000011158029001030080c00750070408c1d0030003140701212078002e45515444212000b490754080c81090302c154460b031a41031402c0f8407141d26013804958081450b01703210303940341c80c20b48101e40c0300207070351000312150074a0540c1e4480004040c2424280d10000b400e400c0f00c108040b04202e4044050f0040e651700080c10300c556201c41200300d82c0406d0b41407010311a5041880200510090240f41d065201350b512490750054515540c0c804c0072882240c41c0100710b8004050040c4000e0003448000d80700c001c0e5140540c1030183c603032001d64070f81c01e070f03640441c0c40b90520f010a0701c0206014401d5400602c4400c2105120815813030741c00c0c40380718100040c240000c44040c507062202080c0e03802d8402d40c05c484c00c0c0e1154650758640d070a4004041c1000004004c07a200304001030300751b030380e8003848007074450603801610405a540300b0b00c1030110001c3c01000420310000200f08107540e0240552742101c0c003210244001020f10701c01661401c1c240103404150580000e4031600300e58 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 413353102 1250 413351852 413351857
    0xc031e090306091c030f1407120b0f060f03070912080304030801050d05031c0e0109030504031104110d110702041b0f050c070b030405100207051e060705030a05070909050c 75
    0x4001d60954030aa41d0300e41c552038482d5506080e503502c0403d00070075009928401d0380710601c6440c51120000782d40700d0b032a41e80d42071210100d035103400180056412451515050161202000f8260340f044820304031203002540324062031001151b07034400440080d20705031007040d415008001e070101e141c2d48802142090050f0307a01c1200d0036030109000800000d02401c003110703840a00c40e08080a1801c1c400c1038203a1a1022203846130750041300b51540f01c4840c03d0f40d4203100c0c1c6103005100e6110181e4407451460f100080c0d00c010641c842c81146081c1251645400c02d20171105908403840002840304001d8034091114000c1820194116161201c401b00304089800520403840d1643c0b6400e00400d60b0010440d85c52054155540302c4d40c0001c2c8080150101a10155402a100c3c0e803c0c0d60a264a40d40c500c02240c000c001e0549641d80203c0c00036103c10040d80280340780600c00300240682e440c0c00d006c06403a41c80040c00448500e80d840b400600a01e10038020540170f05800c003002e01c0715082014904a00d034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 413354352 1250 413353102 413353117
    0x80d051305011406010507080c0a050609010618020910080c040e01090506010806030c240f0a27080604020f0d0b040305180306040c050f0607060e0105041202010504050606060c031e 79
    0x81d032a00041c1941814074020580c8503030b5051b5030303c0c1d25090003a61038140079049505c442c2500d21800c3d43d2b90001a42c1446120310899186000103201441d103e0500820491051040400791042002100d2a141c00a000e16103c0c03180c1481c0d00c45480d0070549488034856035014140d4994008000308500584c3d4000c00d0140c039003640c603400d0f1522000c08150301e900d0510300045d80046d4200000f20079079800684285c0d1441001200e5040004088030321540342d120100c0b510000e03901410181904944449088420040c0c2c0c1554103c1401d02c01090b90b245406403020703215507402c5124140503501c9200603682e16078007000d1074085081c28a00a440c0d5000001c050180c11080d8402c0c540c02e05000a11511440c0c112041c0142c0520300300a0005c1e103812001e141e03800c072800700110300100340540511814985000d000203181e1400f814a114200c03411214801164148410700000c94000241180c110300100e0f8000e550780e035426107113440d51147c1194003040c003202040b0566140c14440290205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 413355602 1250 413354352 413354363
    0x9071713020432190504050d031b0206010b0f04030f1103010f0b1806030c030304121a04080d0c0e1903060b060403030903060911041802011d1c080d0513 67
    0xc00c2c1c450402100710419108404895209002c001000402e6604095401c00c040c881c0403515012458804d00680354204e038241d0f41ea620030408011120362612480c11080e08000e100074005c0c0205000a445900611811001000110707048100da01444c040b100151740c80022000c1d00c2c509498054075120391004040d2182d480c000e214100580c041c025940004401845c080380101d40700545400e03108054100b980502c00c484070300c2602d8401b0002000580768103090898070b0035552802c0c042c55500b410122540285060904c030001e01454113885001c210000089080100480b0444100c20000005030344445403880b00443c0721940001103040d00e02404052001d00221014840d140c4602d2100500103401d1275810030104120394069128284984944010101c041d800a03055071441a141c40d010b0081030410030856230400302044a03994494002514688202c00042d40f40740080100da550b84640c00c100001c001611040300c1d900b010255003004541052034075200301c4074142004448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 413356852 1250 413355602 413355611
    0x1506020f1615030504082a060606160b040f08030c0d0e010204150513120308091b011b030306080601060302041d190e010b03010501030819031109090717130204 70
    0x141041002000e5041d2480d903042c40140700d4104400320010079006200352001c0b002803240e1050001a101c19004481418000c4903601d0f1010034100d0402c040030300502d1183e032041104105841410a01d00b1920340c0041c00741205541ea820038401c4a0700c03900000f46031240010070800c0f6010400b01400c0403145140041048454011600e401c034400e90103202220310310440b14503105403103007005007503030011075100c207081c02c3e62059105488440c00f803044000c80c01c0c075410010640c0e020001044810042c1031051a05140ca400107407a504045050b08580b101da4903d200c14503020381c121100401c004401c1b185079683d1440010b00940043c000c001008809009a118030802c44c413900d40100580341280e80102c0c07071100103c000b01440008007146d5500e40501041654080c440c2d5402180110701d02942c2d2550351280c06607c40c0c0804142050600c0e0105080400a03030500b034420840064500c02c0701a15a030906584040c0016001c056610406040000010b0304c249500301440c0300703071070900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 413358102 1250 413356852 413356873
    0x10213050307051509010c05010903170703050613020c340602060c27091509090106080a020f040e0a1203050c280e031605090903031603020d1506020f 66
    0x42c1c4440051265943c4541e514420007603807a141d42c01400e194205040c0401d4210b03c503039a043c256034000701b041c0d010030212280c4801c2d11080b403402d16840100c5181c108900c0c5014000912420a00c190040c845d40c1c0c00725802000c04d00820442441c0e4444000d400504800030b03060505c100c07592641c8400054020701700144403400011030600480301480c0460414541e140c2c03016401c40070114801c2c0214194005081945840046a000b05002e00f91080d03910114800c2c00a00030b80686165890380c5406010012014003261444003554121950303501c1500c1040020040d00c5000d44100c694003440141a0801c03100b6a207030300070581151070a004503036840740c400e07145000b6101c20301c00080c1c026103420055092030718014001b4130700e4205604884074840106e403500c135440c1c8018407042d030494018405071800ca402c0c039900c020b041d8001e510314601820344a901941a08406050640200703d00e0700401080c1c005240e4000c04800410300035946400096966000c08140e42050180d42c0b000d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 413359352 1250 413358102 413358109
    0x714070b0a0206150a0506070501020901020c060c12030a060e1006031a10180e07050901020f03040b07030c0501020d18060e0a050c210102040605070308090601060e0f041d01021305 79
    0x66810421603005007149a8401d8545201e000101381c1c0304ea4004600d00d0049071650b90341c0701a2864500807400180c4030319840c4006440d08002c0403140c1d202c0c660600c405c0f41e07240d00004640010100c11290640c03203448030582800541669004041d00e0017110b810840d20030140711a54003280c1c00c80d03405208803040100c9400c8040000800c0542250010303803a1a038450290211082101c4800410300316955a00110990310030251180e0303000401c0002c1e08501d96034108280315950020308040c5241038a0108100140c0c880d0f80001020710000301c0903041402429410344a51400b0304600b445030707410200f203022946010401c22101a0314020760f501c00c4600c0041d4510040c0c3d440300080030079040c01030821000f0103050920b907078144425101c002480400f8009480181429110a0b031522070610f8040c0c128200140181841e030b00500040041c00e90122240b13505c42c5040c1c881000390890400840c001d0103800e41103509d003541e03131201040c0d003020545c01050b1034402003040354011074580040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 413360602 1250 413359352 413359357
    0xc02010206010b0412030507050f0d02070503160f060e0604090606031409010b010f1209060603050304090522060f090609030801080c01090501020a29070207080c01050a1b0501110714070b 82
    0xaa0810b00380303142d14035000034051f90042c09002e01800c11202283c0c00f000c0007910b0600103450400050f0025901005542000c00000c006210403200c0c50b0078050074402841e80007002c510401d4108259042000c00710380381c0000f114041c00c03003e030090283c4c1d521044090f010705907031400c20040350325001c00a0f0300b9200c103100d0300705080d00507941c02c00e200144440441d0381c0f450011032021f40d5551041c000000880301c0c41004025882000515126031800400c0350403a074005186192001101c0d240903110b511011128100035403044000551540003030341074004001e402e00060040749000c18007c1455002031400c0d048500c0b880403152034008080045808841c0e07881641d000d40c2c0042072240000f01030310310142d0750200c505a80240403840442d22081500140c801e01c001da0000181806141424131000d0707003410080c02c06900e002c1046400408241c0c3d005440148410481015000c200c4207400540b4801d1a04101c11388a14560800326504503a545d0034941ca80704180001907502c104205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 413361852 1250 413360602 413360609
    0x315090d09050d060506220e1009020a120501110315041d03041802091c0606080a0f03080405070812090f030c0d15021e091c0b0a1a0406060c02010206010b04 69
    0x3281500a043d5511840507003006054103a105c255075000c0d800c007044001d00380c004031846200100b84541d51304225802c0000c01103121200318100800540584c03580503003801241c0300000a8002c201d003506116004040030459040a46000014000d081d4101020006603c0d4104c404004c3c5281280032549060421004c00041e82c00c28801048a901174905030b0035a01d0b80d1240152801d81c0c2c040004800e108125580010360711440141002d00c01c41d4400e030000341c4070142c000c0242e0030203611407100c1e491074450010100312070000020104032050203081e00900b6860200c80c640b40c1543c0c1c0019003030b00302c0c84007035005181d8001503040c1494001880180504080c000050701c0c10607460303003550f2a510010411405408008002d03400f4200c10030110303c2058014099210359410302001000a03a40314080d01400c00720703010b0390104e44040f030ba040d00040e42c003e0000b0b103854215108000072a02c034400039846032604000260154100c254020003030301c00d178251022aa00d604800c40e10740600d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413363102 1250 413361852 413361859
    0x906070c0c17010213150801090507080c0c0c0307080d02121c090804120309090b100e011b0503040e0403020d050403050a12090b030411120307020603160e0315090d0905 74
    0x14401c0005030002c80041041c00503001c00940743c08020200304482039001d5100300c07103c103049000b007203a07194850451405014000000e00a13410142801010010302400c0e40040c08000614000614810041400310440c00740984120950742da5035280c90b129245800c6000d40504030341c000c200c0e500d5000b110694624540f164a541d15254259001420403043c11620b4113010030000c9003007030380440c002100f03510a94480c03a00d42d08100d081d40a860011541c1e81c000d2010401c40c054443d0400385050394000c003031804e040c59111180740303420719400d1040054000d010009020a2081c5003c950612940c000e800300c90070900c441c04111002d110700c4c4800790854120481c50800115109104510f1f00301c17500c0c0103040301d500d882c00c03801c980d0302c00c0d10225800d004460101201e07041c101c440d510307110800e9000d0341c00c21640d030f00410b40c10311008000c1c0121024004a030312149000d403030101a0744001904890f001c1040026041c00c180c0d080c1c130546154402e00100d0594144140220b0342900c0015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 413364352 1250 413363102 413363123
    0xe0c0901021c02150906071202090112092d06050603070602070909030e0a060c02100905130203060d1a0a05061f030216120216050406030206090618030a06050906070c 73
    0x1a50b03000b0241005200c110114000c503480c0c0e05054800400c2240a8054017000e4021810136003400340007900c6403640d19401d80d00501c03405923183c1e0008018019080002c1001c03814030054645412161b2030000e22880c5124204041e042031a0142d5450385000e104101c1009151510402c141c1d44c0d10940c891000140d01c0200107021a244582060016901c64205250714002420000f400c4980f99001040003072038040c00071082d032610031500c80d120300140c182406a40e0a06e03001c520821001000807510903000404500e4070348a00106647e0540c0041a049100d284d8045060542d1826580c60a0040c20300700854024070b440100340c650900e0050700741c6484446600300750040d400054440240248203203840022a50644844140c4030881d40075180202c01c3d030104802c000072541242d0b002e20300c1c080c02440140c40c4c1101f00c40c601c843c100c7c1c406440d206d009815401045890010369098082d502d100d204201198100c14002c036000c006032545552019400c945005040e040980100b000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 413365602 1250 413364352 413364373
    0xd120509070501120603061b02151005150f0d050f0f13020405040f0c030602130b040b1e0f040e040b281a0a0f0915030f02010e060d0c090e0c090102 65
    0x18000c10361030791301600010511903600c0e2581c8003201c1617040c03408000741d044d10302c1c000c040740d061040c11100e02c8180036480541c18005055280f0919500405000d00e44c1941141c04011403241680d4981402d19a01681d506480d0020005403000f564580c081006034400b00320141d0348601528403c5901170b580702c009944035020403020388000340064862a00801c03401010a03000b00204000d1030113914090303a01c400442c0010104030440d800000540d100340018020604d1643c100d4443d5412041503080f100c050740c5c80714002d441040c0003a00d100b03400080004a10080c0f0900902ca10f01401c801d131100e90302c6400d13525000701c08602c01074008407415048505114503034002410a54400b1280201c00803010119020307003100d8004082070a600c400810404041740070b151128a0015041c0b0b60003480c0d640c9101c2c00e9000e00a000f03060003034070b01108030340e0f403280741c2683e4100c044030109200c1188400340141079031101d8000c0408840007040000c14134a00c4600700c54803602c060303000f002019407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 413366852 1250 413365602 413365607
    0x703020708070b0703090209010909020f060d0b0a1401030606080c0712030b03250b04030f0803061504031101320304050c030f150601081e070e030f0d120509070501 72
    0x684007110324000074012840820284910948107480c00e44000440c106107004011604105a01812003103007403000c2480140c840c00420041050103841d00c6442d00ca090050328060404201c0c61504029826070010362100c041001c00d1022100380c13400c01910b034031b640c01240c152400f05d03048060b00070100a41000150919840496141613140024070302000000003800c002401c0a40451180d00ca03483c0a038410304035210400030090400803c2c90304e45941d540020b8a420000060801c0c4400f01c0020303150b468a00c1007800012030180f115660701d8491400c284006254003101c0d00040c6602081404040c01c2d6420040341010f400f0b00c0e0400d005044c40c0c44019a100520484003805440548001a2810810011000d015801405041070102045021940028041e9040040d43c0301030061028038030284050756541c8014842c05951480c2741507800402c141c3c1c080e50980b02e5554200d5800702e0100d4141018075295452910066540d8010026a03100f5600d10f4081d070020403040100d0360 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 413368102 1250 413366852 413366857
    0x70f0314070806010f1703092d09010308070311011509020a12020c01061d04030903170c0a050705150c060c031b0a030212070216050105130803040b04050a120b070302 73
    0x80c88022281d800e40c5030003102e0306240081e03000100f81d403140c501c20f2084041420207401d20194100041d410002004001651400700c404020742c8800401256021107080c0b0340c880c034491101805020040d6035903c3d09140d59840208154002680001500d480e810180508980300d17040d5043c0c000040c1c103103402000254040e01d21401031000c040201c880a01b900c2c000b910100e40100000a81d0a250070070345230015100801ca4210b0152980c1040000303a00000c41c02c059a4000010f82414030700c1030381c03003681441540007a890074414442028200030700090030344103403103017074070440030251100341c2d9019503005040030b8216641020300061410300514001c1d6922454031a4400c01e8801c90020b800e00b00d5122003140c0300065000100031035140035600301550004c503903200030800c031a00001c510381032013028011141042000207a52221241a408a0000c0c2103510180ca5469981d00c04c0c841c003943c003500c44e00f4080c030707104100007505050703140034030607080d40100f151101696800c10880007075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 413369352 1250 413368102 413368133
    0x50618010e070b04030b06150f0711031c0f02030702090a0b040603080c10152402120a03060e0601080c0a05030a14040b040b090303070e0603100504140414070f03 71
    0xd40d62141158519003081052900078456100f903195104d046090403100d03c400200910b0080c19010741c0c0c0d04040b1340942c01c840c1400c07414201c0c1c58580542d0700c2d26490008044038080d03894800ca070040d002c01c1d824580e06462040709500d41250b4124601000e0340c9a024080c8080d40c000a03070703000501c5c4114a60082540d90340000c00000312542c49590380d0426402c0040417010607488580213603a03002062162064610350040315005840c07400008048241421160001502202d00c50ba02418001c001d81107052101810f05515401b030322500900800d031a115645001114902180483d4001c5d12498002ca624100c898034000b2114003e41e0141c5c0003404410106a4810002342140700c1e2270000c0d8040c3d0b208000720840b5084c1800c2914003140080e00c03204258100b0000e02c12825007080c88240200001c0d19042d46941d44e02d61005a1205030b92700c0142c0003810003407903103e0001420101c9105501c0740f120050a00d00300344005985800900407010001c01d164020302c0070800300040308844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 413370602 1250 413369352 413369401
    0x30623093c0a080a0f02012a0c0606090b0328030f0c020604090b090a0b0102032205031002220608011a0c07080615041a0d050703120c060c0201090506 66
    0x540441424030707280b082c038419100034101107207104065500901032040850584000d0222001c4281490300780701f0040701c0300c2d80c50000442843c40c0c00d402451941e0707040e41c03c1001000507580c1c48107290060403c00301d045101c1d00800315411002c80301c18028100c0c000c3e421200032030841e2542d80035900f6500070740c00e0728180044540340744010b0351403070010805451144004581001c0603024030074050405080003406a0811584d8102c41e44e0000c140c03914800b242d17044081207841c000000d4a030b061140c206607054003030040d801010349015001041000d0301c0c0c41c40a0010a6107060100c40f0451500410000130756030401000403103200d0030f00c0c0c2c0c0b444c01202c0f00f00385443c089004842c9040310a03800304010b90400d10820030001c2d581c2110758003c9505540902103050b051940603460790b032001c0c0c100c0c41002c4609104051100400045001e03640c400685e00f410600c0140140082241e400210384103410f03c0f41d500141c0d071060040c9d10303041c0c2c0e001c2c0041c040d41c4c80ba004440c03891103a42814480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 413371852 1250 413370602 413370703
    0x304090207031206060219230a050a0209060105270418030c020906041109090406021303050105310f21050309010c0509030706030209030703062309 65
    0x40062161005140c40742c4030b510b805a600ca9410911025180a40d002c4401c4d90000e5900e12044a55000c4650007944d0140018090040f161711081080d41246514519842558444c07420440d000034208042802106d0402103990361200454603849240d20345240b00688002d0010281d4042d03074a6400741d0002000440d0250411014200203411280143c00260146e1808419406d000012703a401c000140e500f40030004801043e0705403842004c205501030420040094144420355040c0ca9494002c0259440e0365941ca04202e070282406443d890a20282a6007904c210278402d421550060700504800104240035145c044601d900300c41c081e00c5043c884c004e5041d000c0602d96000482410070f80390b458072824406d00706070860b0707855000c038000c0c0401001251240e54000a43c4030445805240141c1c4d90031489002c61308016a5501c000c2c0050b0410300c01e101d203440291804200e02c1c0c2c0c48402108a903840450b06030b9103102006180070b003160341c8021005624181c502d00f0407038060011a420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 413373102 1250 413371852 413371859
    0x803070819021504080d0e0303090d0c1103250f12020103230709170a052e050a051906052b080a0f120c080f09010b0d0501060602011127030304 63
    0x80d8003c104480803111040c00280944107100340e0710071000e090120100440c1189411032845945818023200c420500940810707407800c0000302d201c2070100350806426541030280c60b20034068810013807151043d50742c04658001c6860500076151104840350107070350a042076000c0c7c0041d4000c080041c05084000b14007a03402ca0f07000200310310b003070185031030782d4401a24038505035500d20100c0000f03045103220b030080d04110010075000038148049800d1030b5400322040c510b0064842c075501040620182260a0004004c02000b040e80100c0c030803415150f0600c81c00c020588a00e08030703545801850350011450b0f5034501243d81c0303c52103514120404240f01d0014460342c507241c51300e403c0382c0a9600011221240c4241290f07205406115480882c6401c1c008088445c1c0d020b04107080007032083c4024a0f440000510040d401d400207106440041e140d04507242c02e60510b0360180c6014028100558240501c850b082c000e1801201d0b500361804c500140403202225031004400c80318074a07598944410302020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 413374352 1250 413373102 413373133
    0x3060915041515080706091d010501031e1802090a090b0c03100504061e1505030703020f09090403020c031c020304050f0d12050c011b12330f080307081902 68
    0x303c0140035010001c240c0949031440c002c2128806422103030002c200e031000b0f01c520b07074007904120341501d009003400300ba541e07a0f41005941651200411000d200d04103401280321100f208400c44006001740c403002e06542d621100182034940068000301101081d000144429034000040c0d900071201030060b01d0a5980c0302c2c001000d84000e030301308100c4014940801c0c010b4041703d02045c0c00078040c9007294003100c0d01c031b0000074101d4000141441c00341a000030728948446905401c880c0d04400081081c1d60790b0a00d400c000b5501d82c3e00c0c004042c003d10484800c1d1000303280e400c1b4202c01c1c0d8031150340150b01d4507081005000410320f542d88181d400c00300c000d450000103251001d020740c4040d500d50740d00d034850751580b60a50944022000c1c0d40c0d8020600010400f2140c1e20401e85101c1da010404040340b0021180e41002c000421203100c152000014000c1c042030b02403150007a001c9420780080d91001c0d5441341c042a0301c9201e0801d0040214800b008141d000c11080c5113481502841401a00c0c402040450003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 413375602 1250 413374352 413374391
    0x50411030a03170a0902060a0309020604030605040b0a0b091003080c010608070b18060405010801060e0d211214180c03070605211b0c0f120405030609150415 69
    0xb1408280d041180344144000150403036800401c0c95428800e0718401d40200c1d02c54810404820109a26200724105546440301110000c0d5400041003110745841d04001c103000106a410a5400c0d040170755401300741c41c107201240e0113010300800c43d101c81d034134603558000603078000340e6491640d54849030002010801400382400405010a400b591400c802d07001c01e170035413a4001900c0c40340d10284000d100a076404006107054500b40c0c145a4031110580300000c03100b5260020061114245103508000c01c01880c092015454550f140c1182914800e0000425100c1000383c5078050b10341e01002500c02500602903206d0440400c06603001149500d020a040c14815000440400c80000348040300c3e42103099000580a501c0303104400608204202500508907160101d8511501145522003484184039608040109800301c50456050302d5072544c0a03001403240600c030340242400141c940320b02041078007101001c4420410320703131b98564680341018018121074202580e0780e118024600c80c02c244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 413376852 1250 413375602 413375623
    0x30112030309150e1005010b0f0307180f05040e03040308090d02011106101503020901020a0213020913050f06031b0103180203030703020106030b0601180b0703030b130606090911030a05041103 84
    0x2004104c040d441030515181084200b90303480d100f40f501004203e100f4002086d600b2880303210006030303034075203400c00121100780349096400c000d445012030000d10f002d80c070f01e0701104943e01030f41c0600c002002c48030066100e0203103110141c40c440040021909a24100d903144020b148141040c00c6030929090303005180007003c8135440040720350b410003070014101d10343c8095042d03000d0f450309500d42440740380003d44448016070000d0080d01c0001d54103c9500907a010b48840143c0a081c003018401e00841d458054201600c4c0c5c07101400c01c5002042643c203010401c07550760982e0480d44c0b150b80d080d0000440041114040c5c881800880e0003094005070b8050004241e042c2c069400411000c1c2181000204d010010b41240d06224800e50b914180c007083d001420110381810500c10b860b442d0311304054025142080102e0350180120410345148201d66100d1002c1e62413a44ea071342481d82e120300302481212040c2c0c0804071190428000038884000d5600415482031140f034000031804181c0c00464641002d054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 413378102 1250 413376852 413376893
    0xc04081509010f2304020627040c030908120603120307020615030c01090b0c0c0918010c0c0206030103150b041a010311030c1c0612030e010e0a050303030112030309 72
    0x18410481c0c0c09002d0090704503100402045011015003c00028400d0a029940f20034840b6002600307568504054800600601051441011070000480c0703501e8118691300b44210710b0000e602c4516413092180072603441c1c0c80322003d498120041d0301102000d400400322a85440f80400f925946080e40d4055400f030f401d190010081400d140315110040140440424020307400030707420340c03d5a1783c8900488202c4540301e03005555812444501c0d410110404507440c0c20941d0781c0180516400e854004d05019510000200480c403075100c01199081054030000c0e6100c002403006101081500c880300000324070100e0001007000c40d03840450241c0319151040c002c10314112280c82c03d5542c16000704440a038a04030300a1031482c1c10344c4820707454010364100802041c3c250355040402a0182c1c071840207058013810712007000b902880d00600c0c422900503824002000ca41801040c2d082c04072a80003950802406507003944c1c01d00703484003010340740e0343c40547c00c0640700c142c1040407400c103802e40c02d0200da886 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 413379352 1250 413378102 413378143
    0x1401110d1a0a090c02240618090c120a02090a0614010801051818030d060f081b0103020904020904060f030201020118030c121e0306090518150c0408 65
    0x20a15a41110700c4214480e8241c5110304198685030340e0300207a00c0980310591000038100400240480c41c101204400d0f410760030202e031040450740d0031061103a1007080c0031202c456003004400901000c50a040c5c4550b1040e521042c000c1d0898584002190b0b402c3c4540c400b1103c00706035039000500003241c195941c00b04199211018401e0601c07880c1d50b100110b6007800d003e1015458180450100a4160000750316082507101040d45d400008200c1e9031501d2000d03046a884001d40c10004004241c548030f40c0606c3d40e298040004e040c3c201261400e030701420141c2c5009403002e4500194003948c880d1514541c019800c0107400b00e1581c8512a01000d0000700200941c180d0075803002a00316031401007100c40964a03404020000fa5101600c5e9003195800300b88043d1401d06448144e86c43d588003140c1880d120100709041207a16455403100c82100c2100300103000c15190030289004003030140c003104440fa0802080392a84140d400300441d007184d13074a145945000d0361645442e04100c06c51001c4a003000d0348 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 413380602 1250 413379352 413379367
    0x51e0f0a0b0f0613021b4803030f1909080c01080a0b0409030c11010905061905070f0501021e030c070314040b0f0a17160806010201090212070e0c0f16140111 69
    0x10840c10700010304110350750340c1c1041035040b60f5621f0802400c03401c18010408126481e60039661074a101d28040140449458a080740207802e2680c114507100c10864000070b405400c0303144a14641403ca0300da07035010300548000e1000440d80e040004040c441c43c45c2e15103105006e941c5607803040c010400d019940345507448480749081c4840c912644140c0b0f0400203403110610556480508a40500201744210440e0305140281603905004500c405001c040e903515a8405003d819002045603980100c00414150401d01c03804c05180019560307412501c42c240400d400290055060150303800910480a060581da1200900c2a61110f0051650104003160001c01c00c1e421031200e43c24084000403800031842e141c0b0581d4201040139802008100024010038250b90003075020b00403050700640900072120b812450aaa201c0003486000116030040700000c0541354601c0903526840c042c444100e203016116540219282010101526040640040104200024404e141c00c03524841c04030303501c6002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 413381852 1250 413380602 413380657
    0x15031c030609060e0721050a06080d210e0a0210022a0d1104091403090f011d0d0515010807092403060c0507051e0f0a0b0f061302 57
    0x25a100070b003014140a0280042c081151030340d40d00100a107808840034044007451402c03164206207615034207281c8028132071821150381007482500c04810403116406601d0404645450b000c0c010040d80d0a400100f00494569607003116001032106002c0300e5089059070001078540c1181041c3c078025900000070444c5541c0c1910b0304281580084158190545208000ca4104a01c803500286412000001c00c00103644580c07094403034982206441190004900c04155a42e01128100d813007803c040c84e2800e0550b100b06800ca0048801c0c005140d000091031061110b1495502c0c001c8805016450003040c564400b41d00445c02007031a00020078085140117031a0044860391b2100b180049003a00980d000000e00b4001c01d811244e221100250f0103141042c02c44642c054144000d02600802c250000b07504160102c1040b1081c4010a442150029a0125542d0280b0200040090740e401e0001600340b41c024030001d074003040140400c01c03e00908036607501264466210324040701e01c000c0c2c66840c51413 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 413383102 1250 413381852 413381861
    0x13051005070807090f030b0c0c03030703060501020609030a120203070c050307110901050f221503080301030203010b0f0307090f0f0203040302060f16021b03150103080409150b0901050315031c03 85
    0x43c1c50308013440000d04003070a40600324854000988918802e2020400c0e08060788112840c2414a009a82c0c8a050580000b00030340000d119040c014400c01c0041060580b010040314850486034a45092000141441c10042c2d0401090b944c248000e1800300c01c0031070414001480c000d807003100e59624000700304041244062041e001640210000d5140200781d4958040c0e42100c6540381080490705002002000041d200c29400b1035034207c0403e100104000e4244041c1d81628070890090000c3c0c81050b0501c400307500303005001c9038950300114041160251075440b08440b207401c800d0200c0c508105232521400d03a84155400c400590100d4200301d03a908600c1d08490b0046800b21000d001031003141c00007941c0c0c0e01d4451400310b4400e20b0441c41c103c83e80d420040310b240c00b4800520880b40c2e6030340742010801c54200e482041c11300b90400303008075007009103040280700ba13841aa0110b0305000c1c00c2c80044500340c0000702100c54844c416000140039580410030040061020900e0410140001c0001800e40c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 413384352 1250 413383102 413383111
    0x106090204050d0b0604110408011e0b01050f1c0908030106020f0615040e070302100e1203041a031306110306040f020c0c01110a080c0a060605010206090c09130510050708 75
    0x1600c140010301c2181c0d0f07400c604550b4680c01400b911419210344001500038641c62030b40403009440007800290b04070040d004851100c4041c29442208400f000d48042079602058906000030701c10800c00b42203000340b8000d0084100390007810102c0262120b8040b0840c1c05408060311000c0001c001000f0b2681d0401104e070819144001030700d1141001e001c00210540041a40d0384140d403101e01d0310103d10f800300400c100540d0020800b0f040c0701102c10b805413891503000d0407140107208010307149901b04000000c44c0c007107441d403551036608541448a401d002d40c00c0035101b80c4110382924003c1010403250300601c0001154407440a03600d041c254100422600e08903a05440c00340148800c09403200040340001c00c1040a0a01d6215280601212824059a290001d2195001060000c4800707000640280141d2150302c042216079100c900585c0d030344004a81d03204190b4030408008809040030111340350000a101e4520114003aa41d66950500071540d0100c40402d03a5034081210340350b0303c1001c0c00c1d0030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 413385602 1250 413384352 413384369
    0x7120609090c150e0405060411071101080105150a0f0c050109060f0c0c0b0f0c1b07030210140315010201021e092106070f0909051e01090c051608040308040e01080106 73
    0xf000c8440348040c10b881d85005525100f0350391500002d15a0715141c0000304201034009030070303a596006103080000c20340a4400c0c01d0025800b04008640b50038080c20410760113103d40d080038207081d07411b5403c40b150040c0c4009a000c000c201c4162200154090040203012407051b030380400c010704800c1040c41110035016000301004400002c000100f202440c1d425000031a5100c44603040e6203205d1480c07418130070040c1c11341251007110b05c601c1240401091020682c0e10803202d6240c4484c01c864122000c00d800f01c04000010410800305202d0b41d17100c42400c0940703806000250074000140700c890828501442c030700d1044400003030036500c40e2400700c00081110010518040129550380ca03069540d02000b8184414000301c6074503413600d2030040c4184001821340103c1401030340b030301c10301155414030000104103004450400104100116004644050b4059900e181c00c144854041c0b04217054010000e132217204c030810000c40864070b4080200046c0c18191001c00317072540b402030168215106603002414 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 413386852 1250 413385602 413385629
    0x207063e031608090a08070b09071d0a0b210106180c02071a04030206030a090210030c141b03041707080d091202060d0509010b0102010e150a0507120609090c 69
    0x1c442042400d10040009180382000079030313a41c00c80061078540c5c0c6040c00707024105e002c1350300800c1180781c1e20382622642c0342805580b901a981d10440c801116841030316007007880b648001985402441d4448501064000c160717014004610124400d42c14140b6560030540c0d4545606000c13425a4102c040c8903000341c100f040080c590702c0d440084d15050140252103085158100854140800b0800d4a015640060090b071340c0f0705050301075500401000320224011300703040c42103050181c001d1040d040d41d000691a44003a80307000d020500641d030f000b4403400546c0c0010328072444440c002080504060940080d04144a0080000b860300c0c0590303a80c041c074500e50000324a40a4940e00810701c20845900c0b0901d01400215840000e40314000e10904081092a000070000360544c150081e0366048001e070020442d5941002d0019100c401c3d076440c40d01240080401f02e000d0301003030340c01207901590702c0c036107000714200800d008425107500f584020002e54840c0380001c01d00c08044410001480c00e240e0420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 413388102 1250 413386852 413386861
    0xd11031e0703060510181b0c050703020603090a060207060c02071502031206010314070207180932060405060906010b0a1b020109080a241e0207063e03 66
    0x41d561103036400010030094950010665820320307001c42001800000d0b000c0c504001d030f100d03426001000c810000c42c8031014a03e0440304c0e1940a00c80c90707000160020302400482c0d05540900c803030f80e400a405844c0900ca00070140021030007a02c05010310310320030080403421000d0000c0c02890264150400f020541140d40050503403a000011140031406840082d001941c0c1c19005900600358416001c4400e0405c00030001d4551b404141c4070241c440240707000301c1c0182e140c00103208840d80441c001b07280307107603810002c2c0e030340d10300b00c1404234458a00f604042000c00c06040c2140c1401026030307044442340e04c18018804a20400c0c0a202d0152507a80340342401c15110000083c8201210f25403030014034008402007065910035007003500580b4003003044918180540c03804c01080707080c6034804103a035038204a040540381d4082c0101401003a0803034410342c40300714403040c00000398003488003220019615000c150b03007030b502d68402842681c02d0311903403100f1203141c2d1103012658160382001da400355010000c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 413389352 1250 413388102 413388163
    0x5190905010b0310060c030507020a0b03100902090a060315031223131202131b030e0109030221040f0603020307030b030708060c0a140403051c020703020609090a0207020d1103 77
    0xa60440f80c0c189030080070403c031410180c0c8c051103000e8010b50851030a030b0003c2105204540214001d1030417000c0242c603e580c8042d031000304d000d035012080e4030244840042100c1882030300030030304030405811003000403a625036524044490404070a03011410032030400c58452031051441d4111114598800d00e00804504295882291401900450b0003240c1c0711005545440c00c4550403004031041c100a81550501805c000744610300f08000080d0078001e1101c0d01c000103000703041c0e06039071580040c041c800008000007003441f50034829543c01c03501840005000c20425018100914182e28016a01c7c24108002401e03508036020590180c1d0010b10100206540083d040741c0c0410b4082e42240c036481e15000c11101c000e08200083c04000000c6400f10a200c40071448410512a240d64044540384807a4240c2c2c1741ca0b84c510019500c610207010b0501c603420030811490344101003480062800109a0014028626001003503c42c2d108806000d0b03ca4101000108000413822081307064888801000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 413390602 1250 413389352 413389381
    0x9090b0a050d0809030f1f090c060e0114030a0204061428120905031b0d020304120f021309060c0302070f0807032109030e010306050d020d080405190905010b03 70
    0x403940107540d000d428009204000056134086000142078030b00310841d2202c40c0c0d5940b50398205082d009034084200000d0a1418460341309071030350014148849a10b013910a98032031848140c0d1a05002a4614114207404090300841c4900049880143c0781c1d414490f0050a910340c03149550700c9944100901800b441e4604401c0080c0103c202d06480c801a401e9000c0780c0100108405140e0799082c50303a04000c000c0040003505214600c4210030700c0f0090042c04075592240540d0306040507800401081c000f1aa0750555803c400f40620022071342c81c0c00b59400f01d0205440309e40c1541600341d030b501c0103008011450246200914007450203504000d11074860745840400e184004041500024038a0105401504032050107000303003072080d081200c980081d40207010081d00480000b000c000100100d0340c005d20800068070070141034103001003420f03403d1007602c1925000c1503410580500c40085e00359110340094102620304901c610049240283d5441501c006070050000c0f00014010811035503001d045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 413391852 1250 413390602 413390609
    0x30807021003020d06060503160810030f022d030106141e0a080a080c010c03091728030204050406050f090606030a0e0303070504140904030807030b03030418050709090b0a 75
    0x907458100491610168002d1003410b1401c0c181c203060031070000c1c0d1550424080d600c42c05e16640341c15000c0f51030303c2d011659185d00300c43c00301c08024001c00c1400455440841250b03000d2010b042254600c10080d103c03015032008030003031485d8005290702c8040904003070040340014143d800141c200041c8010005448a80044503032040001c160000b6007999100385244001f442000b043d20030300d80003802d000c4c025500142c2141182d41c00c00700f508803018443d11070362090036003051486c11182000c0c0d03000301240e0301219a09510402d8079020070201013602c40d00b0061411182c03030051b511803800003808295445580558442d88a040c1300d8180ca85402101c580d000c001110000c1d600d40e1841e26003030040029039210315180c0700100070400d01380d80000040c030a0705c4020310b03c41910300c696010040d418400f224000c0000d41d0280c0850b450900940000d101c01c0b10090a60381490b490b4040380350400705440d00440d6440c0ca4906009945e80c006070144083d10014009003c0d402e960300204800c48034511 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 413393102 1250 413391852 413391859
    0x50409020c01020f070c06140c0c2701080c0a0e06090606070f06060e0a0f02030702280203100212090304030c06120204120c03060c030c12050c040e011e0f03080702 72
    0x50070001c00d102075048800d24548442c0f4181c8502540c1070090b5000028043c1c0c0c004600000c800c503011341030034400c0e00c0040440170020000d0b8521031050103941e039500ca800c4103405401c01854040300005203002406041108010205100c0d560100300511031310390f1106d21540150f105100c0745480d420441544200e050b1002c40d50f40d8102d20704040c5001c0b0310310740500044e160138800300c0d000e078507111164040c145803801445000076043ca0242240b200384c85150140c0d00400003000203000100102a0800e60300d48510030b40c1c0502d030007003410403070011030b90325040350300203811203e081c66846c059030812040c4000354245815030741c0c3c00000d00d440b4064503040c0507000d5800440114a40c0446000d000b440b0001a400422841d0141683c0024007048883c00d041100c181d40f2940f00740f20341d0401580c00d680c0c800c4032002c4079910300020320380070300501c0c02d1a10030040414450b003404400e60085c8103281031440350302104189804100ba070b41e0441307041c0e004000c0f0104041844d40090f41d4403a90100c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 413394352 1250 413393102 413393107
    0xf0b2101290d230309011e0c02040902061b031314010215191802010305060603060f040b0a090e0703030e0306070504170a02031609060506033d030b041101090605040902 74
    0x5003010703000f403190f076500c0d48402089402c249919500c0840540960b481c2a00c65400c0c0410003d204d0f400341800c84c0841c000981411002c102524040d085080307501d0014081624011541719056100c4450000040c40e41c0d01c0000d01001520709900107200803c428890700c540b500220340000d4441d4100d40900c44481c81071004642d5081050303080091140710484104440240d400d000401c5124080003640800d00d403e002401a08100c1d04880c81108010099007800c40820200802440c50f5292503030452411780c000b15044a030751181e1003417050000c00400da2a86580303802808000303101422406500716005120704550860150390076500c8264100e940c1e403182001892400640600196151203511034002c94070b411206540240e800303480092041c00e4450007480800d01c01510b155400c80d10040c0d265940c0f00d0104881402e91b800101c07030402180c03e41c200d00030850301507041600d064110609220821107800510880c034030f4207090516859241800142041c065032183c0030440740c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 413395602 1250 413394352 413394379
    0xe19050415052e0f0207081506010210060602120a0c0b1e160c0204050601180e07020d0801151803060f0f0608010b0306011514040306050a11120a0f0b210129 69
    0x6d001c1ca9003d0002c03502100c2e12900340840c0d8000014041c0c0ba41409030103501d290070030110542c0180c1c0c081e10b00d60f03001003440080d20150107407160f1080300d4082c100700d011800c0400181241c829540100d480d4440e042c8802c000b410000d14005001c0c00c10310008250340180204103401858003010300790103d600142035611400140c030b09690311040400c142c2c12100001c0340c0741c1d60700e0038014000c0049600b15400d10003156000d03200c44d075081c02403905100700c1c0303018818a14410445607500d6001703940b0504146590380d4802081d220450300e000b0b5060307164142c25000030440e100340801000090000c1c002043d90401203510b070241800f07079582a042d0b0702540700040340200600380d201501100f005a4441e542d0400c134005083c283e813101003140c10162014501d0724414242c0340c0b914008040b03410591941001d920092007500c00b0f002c5c111391104032911140d510000c10005910289103407174904503511070142e00b10746600d00e8070303042080c0d41d0071807422100351300c6c3c040b03101040c0648081010080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 413396852 1250 413395602 413395607
    0x307170306121e061612020f09060403050d08220b0a0b03030711120d120203090705040f0f0b01090b120c0706062904060e19050415052e0f 61
    0x480e000c400c0d058450f9003410407250416040d481e590044120a54040342c56980e107072454940c0703c4a844002400074103c4101c40e2030998010001850075640c0e191400034290041b844d0b035005940140e0b00398111404442d0441d8014208a6000c00f03403011039400e80340201e0200c0c482c850760190103800c154034000000c0e50441c10340d000c200b1852006089985601162a00503400c14070988030a001e11403514101d40008000511100b0700445603d403200c0300c1100f0070b00b05000390401072071003000e0b01c0349040010362500c0f10300c00d4801c001c50544e008200340040c039503100196407940881c9810044078440c200040a490000e83d2180c500d44085811580c981800408003401003800c050300d80d3b0f142c200005074522100b0b00c80c0c982c80810900540240c1c1c0b49c40c00c0c10a0324051303881510013140c02d01025946038904103068401c408a22000041203540f64008202103906000e40110303415401c0c01d0034031051a22100c860002102d41e41c40e00c40400c0f40100d4002d00040c9090800b0600000c50300f0301c1035030750 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 413398102 1250 413396852 413396869
    0x5010e0112030207260c180c03090c1c061a0a0b1317010516050a080403030b0d1b1a1635040614031003081b030c070303110307170306 59
    0xb010590540007091711035420300400b010b001c42035990700c50100a02c0250600302990300d061010030105014565502c121420350f0b50004001c1050350182e0303200c001c140d941d01c1c0c80c98256085600c0d4034840c000345070f03e045000c0310302e4103207601440fa48002041c6000c0d5aa048050180c940400c0d0280c0c6a101030016403c210400f81c02040c2030b03900d0780d100c0080c805015402148110342030f924010002c4055501074a030340c81903031803070030000e480c4e0000140480e0094100b01c9400401800386040c62001e52188054660499151881c00c441d2031800c01c5401840e4140d00d070700a01c2c13420a146044011419424000e19035030000303180e1011014038102e40d2444e0f0024006c1120b05e6030005038134808503d080e801e01d901c940a00030118401c412020523140c00c14055034801c111503281c0910160443d01d43c0c010365003011440103030541d01c1a9401034003030000c5c40134244002896000301411811485e01034240c00c1400100b15507644140451008542040b602d004d020019803c410303070301e03118400401d0186 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 413399352 1250 413398102 413398109
    0xc0206071d0d060f15030809010216060c0204180807031d030c0109140102030403050a030c060f050103051e0c04090303060e0f0c0318070b0301030317010e0c04140406090603080307020d020105010e0112030207 91
    0x21783c95000000c14008008020314040c0c00907420380350ac82c003031403a00d80c0135421280121000122031144843c01818294000354012108103010749102c0a01c3da1000c400d0780c0104d030300700d0004008a5400c0312110480e890110120303011000b52a1078103902c00028480b00d0288200d00340d101c0340001d01070b0564000c1c400c40340916046400d0360300310a4030b07041c050194000700208581c1d00c1e2500410020118141c460a0b059903404809044036080c0d000e68102841e4045a520b01180501641404240d40d10b2182c04a0079100b9100400d1051501c3c00125110400920881e81c3c602c040081250b84403401d0700312540b00c103200420310b0b4951106c64040f072400c42c05401848081c4d80000000c818140c12000500c1034040500e40e07012503a0300ca00e1021804c02094840c032001103020300007807124600070040b080c4c80c0b000103440010915550300c2148162407481d40141c0d035280000080c451902d60500c004030b44d844a90000f4429035141100c80c24502e001480b88000c0100c2031009a02010710030b0203000000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 413400602 1250 413399352 413399381
    0x3050a0b061207080702010903270b040f030c050d030519110d030b0418030906030207020409060212011e1d13050106060909060e0c0d09050a05010c0206071d0d060f 72
    0x214186402d02e0020784500380c0e0103030081580c0e040000c8285105015030016190f1541e1040d10300300f03044040e00c641c01c01c1c06009800d50804402e012a501c010a0003810041c000148180c0600d480e40c10041171001d00d540100e801058811510360120303400c442158298150400100210905150100e441c5860f02c91000440c2c082d1362040441710350715422840e1b9141080b5000c0040707102448900100c00030001e0028042481144100522802a4040d042d1540058008036600c3d0a60341d035201240d1200c811039030122900c0005004050115450f008032412240165a00300d050440d1080107858100704031103603940000009503c0c41e00d80d85c00c613081542c003400a101854880e44003600303210080c0988200301d17250140c00141903461f41300b558000d03440210454503080c0003440e104040c2803580c005403054490b41d40500d000500900c24a020398106138054040c42c28481401482840c01031000000519070f0a1452016079400e000d26400c5030f4003c40c001064201005160301070444020600c48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 413401852 1250 413400602 413400607
    0x2011b0503180f1302030903040803040b0c0c01090315200c010903080604091e02040e06010e040309171e0c030a0f0b01080609030706020702010201090b0703090209090106060f03050a0b06 82
    0x10040000094061500807102111402c1c0210040c0008255154100d5500a850840040310340600354011a082007200c0203032480c0584990160703181d0f23801503000d51200c180020f01030310041783c103000003210708000b40f0340788041d10306e90388070311503058290742e10040d4040c0d9484002035541901942e01c0008a484c0c00e405803070b01d901c079449078000e080e0031105034041503146001035030134a42403040780f00c60381d0f00c80d000c0700d4803000c15030000b101030b0304043d82280c00560b0f8014010708403104000450003426113104c02400c0d0b140038540140354224680c001c410360320b10070000e054100408220344208103c15a0b0592040060804091401c101c40390a150580601d217817880911115540c0001180d0040b040e42e03a40366602c50807d030740e0703c004850405613604203011841c001440d5400401c6807e00510000c9442c0071141c45503501f1032030640303121002c01da59071042d00c11800c100046079480200400200029403034030b0301c09001d419800d280c0e4802c150780c61002400c1940c1592180100300405054180c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 413403102 1250 413401852 413401907
    0xd050c07021e01030507020d0210110409140a0b01170106030203061f030617070806041202030c1b31110c010911130b0f0607111e130b15070201 63
    0x101a00c00402083c0028101030000c1c160a00016509600040d150f00400c911a911494040240400642c80c130384900100b2002600c100300b070107a040440c0c501100b8203250304011640e481103400d545d00c01c505010481e80d0329040392a19010700350441d0051b0501596075075511000508000354004072070b00741c17003100c24000c040a5040d0b001e0750503200c4001b07080380036040c0207550940d40d02a0344501c0110b50320001c0000d0000309042c5841c03a0143d29401100d00b403c46140041d4100400c10f00d0070b42c0d00d03644c00074040c041840c2c10103c86140b0400f9800300a00c042800c4000a42401d2407456081002c1c3c90f245440701f1030003c2400c48158200d40b6008100b101c4a600d002d01081d07a4203141c1d41d00c070b04080c08414250028600c9000c0c0d020b040200940b0208030a00113000d8682c002c41004d8410009100c1c0020013030b201c0a44550fa08a2031422a1040200d00c400b0402410110742c3c1130580c00c0d00d84400100540c0307602030b800c403264051445403030700c0702006d10040b5070036040c500711182c0c06000d414103c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 413404352 1250 413403102 413403139
    0xc07080d021b01020c1e0a1205130602060628090c0c0204091203060806070e0d2d0212031c0b240301030209250e01020708030c0601030c080708030d050c0702 69
    0x2011054414010303943c00030301c84451040c90021006051b0300e02d1b00028502c5000a240e4401041c001c159818002d06207815036501341e52000e582c0d4030010158001d20200070240c40c0400c0d01809280440103101c0c1400d40e417000d960345c2d807031407801285036a540e07818400000a01514030682c41a600400901400e112417900509401c5140c08007404607080035408500e0079004900b0351320840341ca0741c80c0300421701d08404004e0380a40400b015543d441e96084502c6450320803624200c0b10090703000720710000b0328061051100d10f102103040c0d4001600280024030307240c40e15a014124508420402040c5510001c00050101f520245408129683c0c45018480d95181751301450489000729104c401c103a80f52036440b9503441800811001096240c00f03e94919400341c04080346200061040f210407a4440d04100c2c074580c4113828a07003807a88000010000c1001000424004e802900d0290500d10300d0305455036960b00030800314045494440f000213500c0009001941c0c821034004000740e44580700704402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 413405602 1250 413404352 413404357
    0x60d02031204030303020c070807030201020a20040518120c0d2f0607030615080a0218150702091b07030c030e150d05070206060609040b0a090e030a080f0c07080d021b0102 75
    0xba06103230040900c0044c24540100741c000859806030080d0960003d69a07a14503030315030015030b00d04148440b80549880d92920702c40d00d849510701015100b014142d00e00083e1a0280c9a082e004454004000c4c1c10f54101000c07584440c1c8088500344082d116529039600c41c07890400d071401500c44120301c2120141c010340010240e00a81040d02c041060701c2c3c0390000c0100006090800c07501080444000c1502c1d030905500410302102084641c038005542400001c445200c05944107201c1c3c3d00c0401c068080d4905070322080c0e00441d211103090600e40c0c45a03101842d600407a0340241c20b024400c0311050626004400c0c09451900050a095a003441e64501c24502d800c255141303403c903440c0c44009800d284c0001a00e40c0102001401142008110803c100140c03010031415a00880740980029499807603003d9080c401010601540d254104810010011031004061803000d203540c0e03050000004d1403004591103140c00a401e29660081c0100d40c501034072400e0001c1041200e4070781c0d0085603c0041d0702 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 413406852 1250 413405602 413405617
    0x15150d0f0f0504030807021507110a02040c021b0a03050a02010c051606050a1d0f21070e061f14070204091e060f0228030b09011403060a02070b060d0203120403030302 73
    0xa50703850a446e5490100c4e0b580e21032045461180281c0340c0418002806880e004a003004440b048403012500c030380c00f140c25111081c42d00e1002d80d0180c00542c41201402c8031102c8100c10036075039801058030316141c0d56a9042008030203070500c4914116032060140070310004001e4086007446030142a070380c0b00000c1a66004410000002d035030300121207640c2105805503182010014203804112041c1d804001070222141c1502024071058480910802c07030a00c0041c000f0215000d5120b07180c9000030078860480380002141420f8102a9909151590440d80110300400000040c0713481d1841440450000e20340800042e040e03c102e04102c0f441050090070b00c040c00c42c0309076000c3c4809800c858024080e4000c041c0c40b04541240c280c40c0207682e8900c003160342c00300b8640c2c2ca004604254900d0100701074090a8001007101c0700c6448a4240d01d013420032205400c9040136004601d0300c04540c8403003101800180446101d94548900502999001c01c8450b9081c58105140d0703942d41d07030700d15029009500200703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 413408102 1250 413406852 413406857
    0x801090f050105030c090a1d0102071a090304170102070c090902030114060a1806120f051903050904050901062615070228170306010815150d0f0f050403 67
    0x100c030140300c440d050040381e0480c0c0300034000301241d42000c400c001b5050f00044c90140382555900b01c550b1415030921800014a00c02d01c00164ad8841904040012086020a90050403100c0c000e201040c14000102c400302c5050002c1c02c200c0b170691030040c6001e0b22503048050414042d1b8800895140010340c4000c9480d4800c5008008c00d1240b1480719509010031500c040d40301c0c0c1414410840282d9015400c0403880c0c01c07480c0000c1d5640c5a48031041917658407501903440007c4c40106800b0003004010340042d40e04000c0c6800312242040c0e5008060f07104032501103004940301c402042e0030f11000d401c22070282c01c1c2c54042482c10b81d80709402e00e42e0440a101c11034828420030001c10b0070034000c111494014074031035003d4100c0d2841c0c550038200c01a4405100c54a4031460541800428000c0400d501107100c0c1d003100340c1c0c0e41e05100c0d00041c54074001400210720340100e034910018682d10801110315644c00b0781c030019114100c0e030444400400b182090403c0c001d04001c50015103205603400148282e200b42c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 413409352 1250 413408102 413408111
    0x210705011e0e01050405030307110f0106080a120315030611090a090203091002040513180b0c03040309141f0e0d06060504050106020307110f0a03151b300905030a080109 74
    0x1061480c00d8a40c10b80380a007147d0801c2010400880c031490b225103880c01c103102107039460780302c440d685404c6a45c16803106140742c200d092800108442e5500c4500c044280f4079090021400170740350900c00000d21302c0018405903903001242c05e95005c1409139071210800a1103014071940c0d0300a401d01030750089400800c14010200d98410b62aa0f81c801d44058680182c012103c0d00d03401c00d9090700411101c01e8504c590042031021030001a007902905210300b07500000f4a48906092402400d80b8001d5002200c100b083d03806d2002e801c1c0ca6500c4014a0b45200201408030f010b9a41390a8170b4035a0138000040d04900c100366003000348011070f0824000c4420581c4d04201d181c0e0707183c1c0226240d01032810014400030540441c2d078881c2c6020742006d000b012004000800d03540e90fa580e03450240381903003d04212903864003e01d100b190211a03021100e03203c2810702c1c03003044441411600c0303158140c01040351404250180c4c0808036401e54849054550f0003404c83e641c0b1241c1180183c51010300748101e400c6107040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 413410602 1250 413409352 413409371
    0x6060a05060a050301090f330905040510050c040f030f02100507030507081c0912030c090b1b0a0c030302280827032e0509210705011e 59
    0x150407114581500c2d0380f01d505503428240e5620203807103041c40036908a83c840c141200b400400d080c4a69508200d092081061260800c1c0b40c0e02c00121a40041d41c00c0b40f40200308004280041040101d008220000162036a0b461010540078040e540060001c854041c0340807003044400d442c5280510b008903104271200603240400c4642e44075149008000403403c2c010800003c420b040a040502e8100c0f529003901e0340105e9400003164410001600e000040c42a00702070182c061107021b0507000140740c0154041e00301008123055209104090854220302c072503012140409000c412a403d40c44000c22401c203a59040027542c036040c064108901402010008014510468190074203e6110040500b00ba424001e075445a0440a09a60450035400c40b1402c01d40e40500c014a03903d20040100c0400320b491440a032100078050301d00200c614541801d01200040000384100c03020200b807143c190500c186043d40540d4054600000e0196007050008440301e203d28141b03501040007241c040094140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 413411852 1250 413410602 413410609
    0xc050d0e030c0a24020304150b01021b12010608160807090e0a0b0606070f2108060618010c0f030306060305090316060209010e0312040503010b030a03170414030c06060a05 75
    0x1800442402d56103c1c00c03200d400035482070504500102104d90881d40c038201c030709180040c0d91003118125429000c0902041581e0610710510382c411400384018107140d007041a807148000d160212851003094500c0100004003003d42010010b40045402d90703200224150802c581009940030301c0f40c0303034084d00802060006540c13050396400841d1000800040c03480d908c405043c3ca102800064008104100b0503002c9884070b040401190b1048041040f90f9404200c68082e0392105413103181004495018010b01d41d031000103490000c001052040c441361104401078a20100f00c220042515804502003400d0580680c422403c803125501c0904c290364405403816181d02c141015a03095582044031540851010b60181c4039104040c1000b880350040e980c0068680356410203c0d000d4138200040c18886804c0a00600c50035200990051002011a59025064103407200d00c14216045c4a40081d0600201882001c075003004d00041e65038030080720440903110034088540c07074003496084400107070509 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 413413102 1250 413411852 413411857
    0x42c04050703060c03060806040302070f06021902091e0901051f0503150705160807150e030f071a07081008070b09040b030c0405160305060a030804090f0f0c050d0e03 73
    0x551140150405508560300c1030004c10405030180101581d0b80e02c0802e0440c4104013450089010740c00800716140f80641c503410156a54001c4400c5401c07280c50700801c4160b010100090300c0d412600c100082d07940d14124001c0640103250300311903140c10001e1006000065000074050095591542e54110305c0c90301d0701c03a10450724480d9541643c402c20000a1050100c1142c503004856441e00b2440d16265603007410509200c2c810070344005400281038001c1010f18030044815480b0754a090040c80303121003205469000c3d0b44425212140f00054000400c00003c2511100c40070410f14542c0b20300f0034210060495900700c43d204114151004042046040051020300315144207038142e00d0308820f4010b00015280340c4601d00d415100b44850307404243d030741e406a1403081a504440c0c2003035494611000342030710005072013903004200240c000c0c004034640c102290181c594400010403450345540c0602e005100b1000f1001d41240307881482d0b210aa4803174000c00d00d41c014802e0902c400441407003655100d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 413414352 1250 413413102 413413111
    0x10090b0618100c02130c02011406060a270f0e07020f061609051806091308030708060607141b011704030e0d050303070201060f150c0212030c0102042c 66
    0x1003440c005581d4880c0707005203425601070941d150050070040d440d804a0004d940c50303408801e02d40d84500c41d44034425424400d03070360410a082007012a600709100483e00a110b1418500104640c000400202da185d190107007024001c00b810714080c0c40d42d00c0740b4010b0300e00c8040c020f41c5017000305207002c20324403403000550180000510700500380e00d07105c0320100c41c45038024008a0040c030449000000b201d0751213000d5400451a20041c1000070f241c41c03c20070129080c010301580740d410055a003d00461f0941b8290399104c01d940c144400c50b519000300042440c007841800920032844880c00700d2011001142955000e0895040c5030141c040c09401501d1030080c01e03542e24940d009040000d404648140c03035402045030042c0c01842030301e03050b464203815540100c42440c003503916044104011401409007600402042009004501441c2070080240d00400f001a124000b08100400c400206000715000042e030007008550301c41e0b4074041c117030b102d1b01c1c2c0c450700729944d41007a0b40901001c4100030340d05204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 413415602 1250 413414352 413414377
    0xa02040c031a060a030f0203090304090c170106212d02040305060a02070206070210020705090a1e09171c0b03030a080c0307090509010611070b0c030f0d020c0610090b06 74
    0x11440b18001d0100c181c01541101c0300300b6880341314000401001d80f008500494541003d542e4560034461041c00303031100701e040c920410800c04c501c8003040078070101700b5055400901d0038141603280f241203001080c041c0380c101480b0300e14121802188101311022840011200500300e51042031f03610611049000f2031001400c076400040c001052607105034000e0140030303c0144564200807898000c59241e540300c0e00711101680c8241c1040c0510701d0000317112170f03210034074280a05c60030745940f00b400d4802c22016110070407142c58480050400c4400f99010b0800401901c0c0306454a000014407049900000d10315a02d03d864001c4250940c20044100e900c0d040b255100c40041343c0350003e070700c10181c2c0002e00050822446100100381c55032906c442c58003e226030780d5801c040816400030b050400c0c1869004000740f4408100c881e000071004401d0381ea02d000e4030103038151654500c91400019200c1c0d10102d01190241c03c0030018070100c0c5060076000d69039208001c0080546100070320050740705880c5111178 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 413416852 1250 413415602 413415641
    0x605030907090b0a1215020301230405070c0303050403020c060d020915070507031b09050f0f15011d0105041e03030f0c020a230904050f0c090105060a03020307050c0f0a02040c03 78
    0x10303d04490484c05c01740ca00c03640d100da01c0214108404000c9800070303007107402d401c01240d1000c002556280c0580020f600100e03820402400d2098000c1c0c080307001c0b110002c043c5501c5400140c02e050090010740e8420f8005459665503608d61428132000b03510035810070384110004440900c8501500003a01c90040d0300c0001043c005080d034840000c00e400b84d402601d4144040940400d801c6042e028060150f585070510414505001d82a1a5020070061070340307080000c2d2611680f0143c2c1c2c002214907021448809612074002c6080c0102c4843c850354004080e503039001d182403104200442c040400301c078040c1e1344161184c031800800311442c3e020010040c0d07110300d8480c810300032f1810780039441907903181c0d00e070304241c20768442030110b020722904940076034283d0041c0c9038040040c40b05000d50407151b072040700c03680d4241d8104000154140a08680a4101540400041d8400c2d008004860000106008440191407501080c960340e00300031400700e009500304072045518a000340250a04007900d00003028 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 413418102 1250 413416852 413416859
    0xd0f17160305060604080f0109020108150f0f06130305210a080615070f0f03080a020c0a1b0302090c0c100b03030d0e1f0b0a06090612180c0605030907090b0a 69
    0x20041c11000d090320750702c1302007084002118442005844030030000603001245500745800054240d6100605580c0300507085020100c0c180e4994080181d07008040760b162041c030081e4004503007039003c1e020401000c940e004001000740000000c130754080c015103014118000080c1d03d01140e690058010000100d140724011490518112520b4070140078140101ca04000160325a0380d0140f20581c0150794080020003900d0505a00460107907100d035541c0c0d019840c0416940100c0d66503503082c1c0e405401c07541c140403668110740e407030141900159001855240e55060103030104180d41d22072062054244a200c003800340720702060080c0310f86400020042e40c14482a001d5a20107040100e00802031800391030600300300c8010040300c490005008801c0003c003142c40d0340520600c9502900458140481c58100300256a4003400c13402103160b012802140c003260219080302d019020000052203146610700101e041a0700002444c032448180701215111640c078103001003183c0c9010b9940ea00241c05507400d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 413419352 1250 413418102 413418107
    0x40e060f0403120515010e030304081209040f11030910050105010804140a12200109120c0c0906060c060f270c080609010b10030c0503010302090c0c0d0f1716 69
    0x2650240c000d0903c20500c12a072145107080f1903003180c400c0b1402d480c03010f0001041d68012001101044c0030f41c015444e09050408542d130311070402c03541068040e07002a86e0038542d183c60700f00050040c20600c1c20301104944802010454104440f40b0076140304603c8040d08404c61800b0352812200180c4400d0101d0b262625074403031034103040d40c41c50780c070b4401c200700100001c110082440c881c4015682c1c0703114039104d10f540032403411300c0c603845a81c00381c0c1442e0700000810a801848251080c01e81000120b0071152301d4108443d5199900c5121004e02d444070004110707070851944101c082c0b09034802c115002543d0070190882e485001d02440f182803686400f909a280010700c2d05503503005445240070295a010011720b8801d0850f071003011a51918000b00103410505621320420b07003203080a0001c00d5a40800400c1c9010510010744507c01c8440442c50240c410030450b081001b1050035100d88032504400601003004100840c00081c400b41e41c4039031615440c0b05203074041c00304000e24264880517a00308 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 413420602 1250 413419352 413419381
    0x4020d0506270403260709080d09030c05101103041d01051e0105030a02040314100c0921060b060d14070e010e0910151d0a082a041514040e06 62
    0xc5da0401d41813098018040494582c1a0b110f0b0075256602403d11b4244603806081400710480d6a05104031540c0902c002181c03c1c034881c0a45030261413130a8040302400c1c0460700c1e80c15129030388245020005010a5081c00518240c540c08001e0303501c1040c2d640d880040c030010160000c0b0a042005040c0103402c81d5621a400a50700000c0030100503013456229212440024260801c4142c2b9a01c0405074695082c4035004860f2036440d42e0800204482c50102403841c0c160038034035541102101c1781803040801901c0e900890030348074041c1c102d5807201c14807030580005007840710385c000201c1c0c0094009201d603881440c0300c9860190680d55041c417113a081052042400020b401c0b880000c209a502042c40300b00c104e12500204001d9176440540010320a00d15071050200d1810360003142688018401d02c0c1d40002d5484201b14814050004403508031010040300d42080501070b445070408101040c403a8550001b40d00b0740340003e8045213403184407400c2000b101c080f40840342d070700d80112000501031000c0710750 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 413421852 1250 413420602 413420627
    0x1080d0507081204080915030604050604020717030601180b1e09030a0b06031002030408131a04031212230901020429070b070507060b03070b18060904020d0506270403 73
    0x94003402c03d507052000071542c0840f5104070014000100c2000078920b2b0a008141d080785007a00c0071460200d1035107582002440b07400c0d51242d41e80c400004940c55921800025002034000548003c00c0d60b00c1c1c1d4007810940d132042c11400048014010101c9050880b04211950450001c0c001d00c7c00003d20341e07505028200c000d14407035240c025119041108141400150b22079440b90503060395407400e044c07030089a00691341214400a40041040d0382d401e1450049806581d00700c40708049103002c00000300d071100f08541002034094280000600c80c01510b84101700c140348150341c0041c1581c4c0e007070f01a608038000d0b48607540381e12800c1a0154075100d1002c03c2d41c56109540303680c10b403600c1d00c152079170200000255043d20001c0c0001605d002441383c00d10490300040c0040340076000e10b42c6803200078003841c0990030480000b039480e0101c91000e80d482e0012215050740103001507440c2d00d0a403c159008150403200c650194030307048200001d50340644400c50402031111020040c41d1245c2c0c0301100e03140034164 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 413423102 1250 413421852 413421863
    0x111091507060905070f0803030105030a03080603010e12091002010b091810060b03010306060b090120070503160609051207180b041b020d140301030615030209090601080d0507081204 80
    0x24000c203a0070300402c80f1941c0118020483d051400d41405020219603100c400e1a400601c0148000d81c2d0202e07030140e2072909468a2540d54560000007401403040b1000c540c62441480c0e0341d00070041d210805030105100c05c40d02d200003400c480710107909031014125490b13480b0303890f074001560702884100135004400c0030b03c04940301e00701d1130755001c030031142d044c0c01c80400070b5800b000410400101d4010840039243d03e241041c2400b41d0300001800e105032140611040600315105200d50000c1004007100401c0010b0481e005401844070801280f4018000c100005484540c089010b05290180c0740f505081e00b801080441c1c60080c112544108c00c0740403102180e00c68a200045640c0c1d4060410000c0d4402d1802c0410300c003d00003c0c0c9030030101d11000782031044518040d820b01c0a0070f01680c0c1107c0d000040410020441008064414010303000250300a01031000e014100800085890503100f86c4811906480312401064845000e10480107100c00c204001d0300c2c1e0140105414075400c00e03c01d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 413424352 1250 413423102 413423107
    0xf0604060c0b09120d0b100903051e0f0102070303090b06010f080703091104020324010918020702040905030a0809010c0e0a0311040b040c050a0306090218091e010e04021201110915 79
    0x2034003042d04c1c5a0015000d14925070312100a1116483c2c2201501100350b494281a0300d55403075642e80075101e00f51080220b0380601d03480c05030024080b00303028112010182100865039412145030203002001d103400150b07150b400ca000080c540354011913004090342ca0039106c1c0306182d520140210080c00d43d00c0d03411605c42c0c41000d14000640c07558006503015100c1d10708032222541076141c10303074510b0344828036050421039010006c011801102c19098151a850030000d60f45180300c0c00442c01411040750001c0039880005210b85565078410304840c040c01c5847e00901c01402e60303510072030703403203101e081034681c00240c2442c1040064201035240c8400e4070702410200d0714a040d40000390440386a510140041180091503841883e450b20860016140443c0218101510902540c542c18150b101290152035031002240441c48015003440541d0428a0000c1039907840c2c2c40c1a0702503043c1507078128041c14940600c1e40361101c06000700e0780c1e403082014840d410301d00f82c00700300244050020811055850304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 413425602 1250 413424352 413424373
    0x2b030b030f030a0831060e070e33040b0f1c05060c030402010215180f0102040f1e03060c02120c0307030e041b030c0909020c010209010e01020706050909150d060b0f0604060c0b09 78
    0x1d020b03841c01041200800351192074044a6068105804504070592100801500ac080e03103120b00300360701540d41a40d00054900d50b441c00b0a02c2c030244501c3c9558400c0d880d05100c9072558003001521440c91140c3e043d16103076159034491800502059500a01580008984008007404003003880d40c8014080486500039080801160500205c0c80032104281d4001605200e1107120401f49001061942082200c10a900c8000c0c04112000d0100401280c0c45800c0500d100344200300b000086074444a140d540e481d042e403202c607942d600c41c003421400300d2161100303803400b0324061240807110308a48004d4009001203090840c014450b4103131060900c0341102c004100b59050307101901d0030020100005948100c04000908058268103103a41198080f40301801155071010540e0380b40c3d241078a07040e810ba25000601025104900590340c1c200c07000c1404079060103003582000e2600751043d51a0f2892500080c02d01100340303d42d010709004102c500c03035900d002844585445a1000509041c1e80c0c0d203004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 413426852 1250 413425602 413425631
    0x80f0a060e1602010b0102070506031323070503010f06061209051014061507080703050a05091f080a050c04180902210c032b030b030f030a083106 64
    0x82d14102503089032a000d01c000150244500394400001340001c0c0b41103413810002814034440208813602611010303036503508101110400a400c50041e403400c2a041e050f032040245d43e002e003403003558440c1d0301389090070030a4840d610a0178195862a0307900303800c4040e0840a24050300942074115182e01c20920340c5c1440e0b481c60301c44d4140903206022030b0302007810500200250030050403c41e000241040128100140a080403070b1003641c0e060810713684030f00d80c004065031207001e50420560042c0482c1102c9101915a8141843c0d519a5403a0103207242c481c50098802c550b01100d5000311030701f04010074411010003203e04220750000f0036001c107009000f980032420489e00034603030740030100d0210500f1505440500c40c030010010264010850842444100802c681c5481841800c0040341080c000300140f19401c401c8964401030120f92a440200d15001d17a6640915031002c0050844008100717100d29407141002c0b44c2180090032000da85c9134050f80b44600050940c01c980c03845e62618144a09007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 413428102 1250 413426852 413426879
    0x2c03070509010603061d07350a06030506090a080405040b130e03040302010f0e030601090507120518010c09050a0303031812050d0c0507031706130e2506080f0a06 71
    0x106560114045140010f80d04103070340840e000f0740700ca089101c20411f989900415040226008502d40400415150840a0300076107040148110003000d80030411b00d64882c0e040141101d101f001214100d07501c0d1094182c550790b90100c01801c900081104014510b02600b102d403034400001e00028000a5003485082200c007401d40e205100d82010070104107568200040c22808025400c1ca010b10120b200000380d1100d10501907044401d03507850103d00080e11424100380708a038030321000c001e2030606641c50703004481700d4a0054400e40c2000707912810baa100d140002d00700d80300609803042c05130560b601a0080c1202c500120795601d80000248040360b91003805031140314450300c842c0e079a06485016101036844401e104000d0100c10442000001d501c40880b040c10b11101110010503101d807000103e130007003043e640309121800c00208061b001c4012861012003070f5020f0141d00b40c45001000c4100310b082900c5007001244410700020400d0f444a08c4072030740060500b600041d841c0c1c850140c2c40004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 413429352 1250 413428102 413428109
    0x909010f0213090e03040e130f0203030c1605010c0f061808070b0f0112020f01141b0715020601030b1302010219110a2922030b0f072c0307050901 64
    0x90103000420007010b0030511402001e040510f0180d8a02400c0c1f2003610180c20000c0d00d4a800b22000031a000c040c0080c2855001c905503000341a00e070388080e0f05c003415031340d207030030350344000c0c007030300c00c1100000c0703542c014280040c00380e80c4285011034240044d1901e0004248011101c0c20b800031000c0782c080010b058800804555200d201d002d001414500c448641c00703a0141c1040d000c0b074040c0001e030805079442e002812a41c2809103040344142000b5490303a5101d00a07681400c03080100668540c00c1d051001c50080152211180d003c070340c0400300281203036240003c0c48007901414002d4040341500700300403074a81e42640180122503100040300749408422195140944600c1c03024080a40a880c1c101130203001054003c0d50302d0100c05445036403c1c460f50301c007100303c50a0900000d0100d100c003010078000071310b80220174240c0b10096485c2050002c03008100c40c60000d0301c03191400292003070b000f014540c441c105041e00002d108181000c942240c030141c1d080a50b410700c142440000c0c50b503a1030b000140038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 413430602 1250 413429352 413429377
    0x3080402120a03023d02090414010f050f0d0b1b0c0304060908011a010503190905011112070903050c21070b1e030402101b060906050411030604050c0909010f02 70
    0x1411500d194024000007105d00808514450649030b55014080ca400c46101316841c40d00182e6809540f8001002800c1c01c0ca0407c40200d0040000529200107460000448200703070344261003094070b6009c00001c5010040c0003801da150301130100381034a00c410030007141c0e1005650f52501e03204030f884201c4e2071170304142d0000c00040c05006052102c49000c2c00f440c47c1c8501640c02d54010402c070fa000191017400010a100240060302200c041c2c604055040803900315002002004403e07202c1c80161215881500c02402809090001c40c00c0c0911034450340003101c0c0c02001904240d180e220421910f035019101c030303050030364130f0f1120404010340c1803007031f080105941079585030355903008144c034003108120140820302050180200030150300d5003071414558184c1440c244c03907104e0f030000c010590080d1090303003e8501890003100304100041e69000c180510300541c1000340580200c0e0801d44d5408007201c2c024500e8100d00c174a40014140300d4031140c3c0201550b0000700c2c01c0c004400b03099080740c0058400030f04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 413431852 1250 413430602 413430613
    0x50f0a0905071d070905011b112407030215010f030816120906023a0302040b03010b130509070c140f1605040f06080a080c0709090303020318010605010c03080402120a0302 75
    0x38080d001801740740100401e0038221209040300c0009204000c1d80c04005c0c121200e044510200b65444440e1005010b28401d024140d040c00c410b120030041d00481c1080b0054801d0035400420004c0c05035500d030403507844812003410305055a40e9039034a60030400356010402e003400030201c006900d05180c01280c6009540e1140101e1038110020700d01044251800101e20301240c0a00002011045500184c641845014a8003c0b156800c44c001e120300c1d4002c0c1046000031001040700c0c1203040040c50780301616079801003410741311001c10560800666040c1c01040c07583d460a00050328280300100b41c1c80ca00d40a03134000f410441802814072001b6a40406408400d150134440c41c90b0500c07400051800e890300c20800c142c18082d281ea0380d1140c43c80b020b010001c011500201d4401c040101e10058110640705120f04030707440c50003501075002603c04a00815030040d0005441c03805115010445505030764610b20305a041d00e00351840e600181c426a0003042c0664a8504118108070800304544694000c01c1d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 413433102 1250 413431852 413431861
    0xa2304021606113609010303120507020c13150e07020c0102011a0f0114040f12060b09041101050f0904090b0402032505011202090901180b04050f0a0905071d 69
    0x3c694000080801208090200544100380c1001e081800103034100300007501100d0040c00c6144448840f03203281d002081c180007008040d80b14041d070034001e5001307006102c00d40f104903040c1d0301d845041c90142d412081e42e006298a9000ca500000c0e10440c824442807a241d4903a01001e0079080300f103d00c200982e2003c3c80800295a09118000700d446400c1a003540c5442414002102c2050046070a4108016480c16442c1d0708034040c00c407401000e00c2c44245521940c0c0c0d0b40e04000020281200703a460a1410303a2503603031403d015414510403036000d000403002c602864015190b41d000446c40031800e5400f0701040810b6100c900c1400d2560380a4a01d06000d445d0500c101440c0041440440c0718000020070802000c071802c03c144d00544000b400c2c10104403a800361090000d000b0880f80c580c3c002480390002500791840d011840034044980303410b00681c181c083c10b2200b5203900b52084400391811200080c0f80700c8180d4801c0045c20301c035809650344150f4035000c841c594020719242041700e40c0f0038020310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 413434352 1250 413433102 413433113
    0x220b0901022a0f120a03020604030807300b0303030a05180f0304050607080705190605150f150c060a021305040b01050a030b040b030f1b030303060a23040216 69
    0x80141d07118040351000344040540c03007100400b01910558010407869142151070703610281180441030900c01211240c03640c0d800c009603680810748080d4042a95440410507070f03031141000e03040c0252013070503000a07204603800b0b10014001044c40d000006580b01302001c1d03656000d100950040c00c02500200381c505002c190414a800102d0303140c642544640091b85141c04040140c80c102d40040b43c07003548485050501d00010720a4890051541c060807070000e0381c40440c862080d2406005260400142ea40c500f00005152340301109507511011004007070981d403500c142e15809100120004904200742c0c030911900d0044142c880f0300507a6004210b17a1407440c20700130342c0340040c882101c041c880103005000280c4288101808c000c109070303c51130450310315162500032910784480503044440f0078200c40c07042c07902e540522404070b0842d4485078a11059140020960b030055000400d44101580741c00c40300d000034056001100034aa0880c0c00303030142030380d65201800c9000ea504803041c0070103501386410b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 413435602 1250 413434352 413434363
    0x52a040f0f0e1504030f03060308160302060604021819030c080604030f02120702040906060f0b090a0504091101050310091d0f0d0504171e0307020306160f05220b090102 74
    0xa02c1c1d20f038400aa14940c10700050750081e0840e405050030b081c00c12019108502500e40c0342c0001e02070384c03000a10034000c09860f4112058081c000d40c244d5203143c49680400c003d078811038237400200304500c03541c4101c40c81c4c00700720000701070203c0d03030604113290303a80d658680f01c19003981c032220b10b03a00184108014150040b510001d044c600380702820500c40c8103131802c58940070b0340c000a40999524145181000203d40c45500589002d84021282c00d5941c500200c040d88080102c0340203002590001469090500803100c0d0594030440000c06861064011070b440d810080c00c560a4645d0408001000385052003003040e1403010010344070b443c00b0080c4400b0714001030700c5030844483d4003020700880e03269400400d03213060f660f20078140c42a400024400758a0102c0800030102280b414103e1400404400801040028030a40981788980c5e6031041c4008200424490311011602d10400c81c00b986201d01d00400318984910483e03007505130a2407581e121402d55420420110800182240e46585c04104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 413436852 1250 413435602 413435621
    0xa05010f0224010323030d050c270f03121206130612020405091515030124050306060108090a032003031006031505030a020603061c05060703050f04052a040f0f 70
    0xc11740b844583ca502c480d68a210b2511502d08581d5500003140202c0240c0040f15000440c020721180d000210010ba003a0070300207610b0702c030f1040c042110b03060824140812130150924032210603070305042d130440500c9012100140345c0b070781c4034407030502043c40090b652051001501040180c1c5ca014052441804220360300a0851090b0351b02030b0035001140324020750002c1d48a4030411003d0041c0c02c404020a024059050504068150403030301502411144091901141d80440c102c42440e200c800041d00c1c0000c05940d11000c9410844103600407170b0280c82e6036000a521320020405103070781401d07070504503002543d001041c030301c19030010000d56074107011307100c00e900e11a091000c4130740c50400005e03034035070020300c00034010940071002030f5407030fa030714050001e00301c20113030740d0118103030140c41d1050710382c00125801c101080c54640465000201512564810382e40580144403902c2d908042c00c201c220040d842a140c42c9a500b0341c40103d40704c50003000d66105005202040e544070388100d1000395184200c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 413438102 1250 413436852 413436893
    0xc17070809060f010806041b08100b0a090b0108010b13090e031902060c070f11060f07050d050f400302040605030f060f0c070602040b0703030c030b0a05010f02240103 73
    0x2c3c014030a25101041e05a082607101398090844010001010075080a0b940134498502501c10070003007a10305a00460030b503540c102d80c02c0d80c0c400d880740009000c40e8901144140060307480001481144c20301c4000340042c40d020095664600d80d14010f450581d2603080003c40a90400b06010010018070340101401b40344a0002d0304040c504910500b20b1401401c0c0c0150442c007404119205011001105103542500a454142d0715010000805400d51185208942d1441041210039040d4400c1d020ba40c06185100450352030300384c40b2102e072001d0106a1a54001c0e10b038465100c00030321840b448070b5804a614001f04055201d02d140100800c540040c0d004034007d4004854030b0700d103040046030b0709a00041012a201c2c1c0380c0c96450503282c1900508000400c811720000e8040b443d44190000b81070014400d41e0b050012044c00390044094500000344681c01074800402030140d58001c071440e0209402a1045581402e55104446d100d684840305040380f01031600010300c180603e1044c03005160042c103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 413439352 1250 413438102 413438131
    0x212130308130f0501060e070801080c06072414060301060b04080604020402030403170c04090b01180314030d0504060902010e120604020f012105100504140a0c1707080906 75
    0xd4602518058000b4100034441c41c0b200102c2041060b1104190740031900036001300149500c60018441c41d4005950345001314607403c0000420460008407840d84100c09030071941003d035156158126403260107100c101101600303000d5075104441e4419080d24030913491820900341098403c1c142141c146400950150004000500c140200018966000360703040e81d0041e5617a4032404d003213560550480748510703510b002d5404e104a0038009405442956442d40c01040084003100c01500da42401190204984481c001c082010409000d10012150841e10946c1d1030180340c0c0288000300c80c011a800c0320420795074015401956840213613001c03100002c2c0d40d129401540790050750340c3e4000c0204001e21400e55546a01c426034030440c0c120a07038800d01c804901a1310703103a099000280030100d0300c2d00c00b00c0d6490000020549080d010702804030b50400748405180e15120750410180181c00408000c0c04080442070800d1600b11800718800c10a6560b600060b0400c100c105040a401400340300190160 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 413440602 1250 413439352 413439391
    0x7030308060f03010b1005070b0a05090d0f0e031207060509160902090319140d050415110102070c0608070311120a05041104061401090807082d100212 66
    0x2008141d04100121101d08800301c1c0903001a024020f12103074650000c0c14001c0300780c0c1881c1c01201418029100d0080000300382e8072140040c1c22254105c540b600c55a00410942c243c5c03034000c100d8503401101030300d8501105221140460700c0c00c2101da4501c100079100144601c00e20030309104050300304d108100a40035152813801c2583c2c4080085c090521110350014402e0000c0d5410400d1010010395000d007540c1a0b83c05041c05469040c60440103101350082240c6580035900c44d40440301039400700c0035000c1c21040c005034101c1d92101464100006990308000310b0f80486c0750215400010321160340d07020800e10703000f50024282e07910100b003000110001c1c08000030044809640682c420440f0100003a00e580303904100c01007482a40c100c40c2c100d0701c3d21401051071400704514040710182a29400882d0355a400002d560340d0300303031140c81615003001581e04c25a00c02207410207814000c9601d07001b591480c0500701c50a0030f014a03210000383c0d500090b620801c000d40c0007182d600c071222510080740c0181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 413441852 1250 413440602 413440607
    0x227130b15040603050f0a151b1404090906140f0c0f09030c0603040506010602070909230a0b090309040b030a02090f060607080406030203010f080c132301080a0303110c0d12020d05090a020111070303 87
    0xc1000c100020700001c80040400c02c0d207400240c0f0001d1900010501104dc03c6080140c02003908034003e002c6d24160900050603526040c2506014810103a40b051402c88034006c11080c03174020344900d81c1c1c14002c0821090196581e075000c0c40c0201c0c05180641600c0d45402e42c082d2600e0046d9000030302050402c0380c14808030f0200b1011100055064000281e0410360b150310343e05016288030001c06041e007080c00d022030940c000000d04420709003030301d040040000c0c2904240c0e072a0b0a10100940c41212080080c07550121103106a80240018042508200070342d0b9691038240c109411800002e58044010045c00d5411485100102010009030a181c100702002c80c1455500d41c1004d010147c03a120240c010903107005000440c0d0700c03180c903001c1c250f5868038001c6488004035041540002d003411101c16056690504503419030f00040018268400c07042801d032841c0350344503081c0c00515424440c20702c5001c8176010740343c031440f030f11307006400c016180d48005028001c2c0c1c664680015440b0f400240002034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 413443102 1250 413441852 413441891
    0x100203040902030417071b0519090b0d0203100b010816050711061603020601030b0f25170a050f0c0a090b070f0227130b15040603050f0a15 61
    0x300d070030001503a030b5900c0e4201340f40c426944080c0d80c21502c10000d002800e2207002c00c6110b9101750790214014259540c0d40030044200c2c2d00040c10404944034035420050002594400d6100800140c40200001c0c080d8001070306200402d005000d03226102e580040d2207690140701a5171100c80302001780006950000c00520343c2c011840020f00000c842c140c41c1e000365481d541541c8804880c0a00c0e0b43e030040c024603000791206003c0c4000c8a00d18449000704250b0281c44803d244035084003000d4180b000e4003080d51007447c1c122444903000303010701b2540716035024418151507481a1080440864035050103110a807c0200040403410703450010300002650b81e0740310110404584d15440da10340c8441d0703107003040ac000e41c00351603000394007403c90040700b642000c080d1084400700c2800e000508080e03032502c40800e804010020001d01c540041c0e400100f072502d510b5450740103840301420020704103031071303a41d40e40c906040091401c0d1700380d01809441c81048104070300902d400c9541501030118200c9400c0c0c81c503502b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 413444352 1250 413443102 413443109
    0xc040603080a08090c031002070b01090204062106091803021c2c0301050403020d11070e04080a17270316120c08030f1005060a020a03270b0309060610020304 69
    0x1c42e030100800d4000760f080003c0108185d00400b9994108070300e041d848001e40c80b1510845d40b6402d0180001003c40780c44c42035030700701c84485d20380b000042c50302d15250a106d1040b80d04102078a55481001c2440c0f8800c4c030441c261030410307010f003140c0c2c0f140500700030780b03040da2090522281400b01050b12031842c1d0310070101180200300805800301683c08481c0c99156064030a480d40d010741c0782100300710901d6030010f80c00102d0780341ca4a80d610342c640c0d08c02c07283c0d80714602406007940d801f03008400b04000034040c2d80140325842c2149007150b8004c440c0c103090036150178161955001500c180c140ca040104a100c40140d80000680055103800c00b001104403011035204c0b8040e108030010507032406024007540d0700180540e0b01c050340907580d28094030482400d420070398000c040c01d07002c4079012500b401c1210031182844150b8000713103202409a0740440c0d100c52001c0d61405a40d0250326280e80e000620f8401030003400c1101c10298036458001403080c60720314000c00c1780f0b03c40c1c2080504401c3c0c60742c01204031b5054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 413445602 1250 413444352 413444357
    0x90c05090603070806090a020a05032a0a1e1a16111203040f0e010f03030206060915181504060509010b0a0c0210080604060603060501210f090c080c040603080a 70
    0x103941c07650006428450103074032000e0343c0c0c041c1000f00440b5003000315880824a100b100c015050a450f038060656810083e00890314090400294001e10034005a001c60300303420051141c220a511007080780c0b5a805916000e20711142c140300c0600507401c0261142d44410050300380c1c5c03130810780d0304500c41c01e031401aa0405000000c1a903184021900c2e0300c8010100000b109040325038944d640c09241c45480c1e40361150050202444002080d4002c080d2000f10032240c144d4001c0610303440e0001045110702d40a0004032100700e1580158100b41c03100030340b070308400000d600c2452007071600880a5044a494600c41c600c80c618002c400d01060b5100c081d1030741511004034007a62503c90f1030740c003583d039103041c2c00c2c01a500c059410740c0c2020a680c030007001c1d40b1502c82540d05100c41541c50001303900f43c0d1f9050144d180481e80390100c1d1418120903010782d03550040321041c04251002d080e10700c001101d0600405544500114009100c3e40ca0100305144060006840422080c1c0ca541c0f03510f600c9025401080b404c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 413446852 1250 413445602 413445619
    0xa050d140d1d06071a040803090106060e0a030b070207080f0304170307030c030c0311010501030609060b0d021e0d1b05120a0f0303020304110901380d1e060b0a08010504090c05 77
    0x1c2c00303420b50003c4c0407511240c0c10380c141800c02d03051680054200319407030789c0c0c0c560802001041c440e105004213091090082e09652109d030550b6110041306000400003411031041800c0005d50290800200c1c4048443c0406140c0e2541040002c1103080048800380d0100e50007004080c000130380c04602001c400340c0500e403012041c0c1103840e045030411050031080d101582086c2c004428081c065004041851003501e0400a492814042c043c2250804d03101a50000510b01c8444d4400c040d90003c4d41c16060041c010030380c92005581d918034041000540200d01495042d0900140c20007070060411019a04010000400b0302e5480c80030403030b520740c801400c06401002040400014000e031402075400201600519030711003409240b5642541d10b00c8103081c16054410200003882d101001412589083d200e10305007207012803101421060200d5460b414070300d05070001684161003480086d010140000703540350703030740b4000070441141030300268404d42c907249044000481004041c0d04490061f81c0c20030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 413448102 1250 413446852 413446867
    0x914060316080c070818040b09040b0f0703090b100f06080c04091d1c12020c060a0b010215040b0417040806160221070212010b0913020a050d140d1d06 66
    0x5460b0141420060105c40080340d4103414440988000c82e450509a8040045814101c10070466010507034024221308116004a01500c400071f2000b41c0c083c0c0a0b060100d07020085665102d000e401c00c44200781401d2040900340310b2105c6070302e6050024202890038040a01741404490918403c6e03200312082c055445000702000681d206c00300d90b42e40b41e880191807000035504d0011b07401800c41107808002072600120090356071420300c00c0c0d0300302585481c0101580e90f0b6501b200702c0105001c003106070640c480e000c1c00c0d044030703001801080e110354401e0b0030304041402d2034500350304900e0141c0d41706035200000384814099001e0006030385a01c0403403c9030504040003100c00680c02c0150f41c0060154801080e1441e01c581e092244c010180e2070301c00d4030a100c07100c1055418508807500c0815040d400240500450b10788005241a0f00702c1d240000c01485c00a6a500b0005081c40c108020403608450704400c3d80c0c82e50041070001081082036420503801c40310810528851348000502e180f0302c10a40800c040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 413449352 1250 413448102 413448121
    0x302030c0a08040c0504050108010b03060702010612060b0619091e030f0318031b030c0e01080c060d060504020a080a0c090305060705071b030528080f09060d0c091406031608 76
    0x60380146170181c8100001e584030304805d40a0100d40007502c6c00f920549010801080c414442e071400c4400102c0c41080200b81a03a0742c1c405072900d14081640002c09200202d0b443d08001d80b1140081110744030f00032070b14a842400280841c5090403904001094403042011442d140b425040b216071624091990f942c1c2d10600004414040d0005841d44410582404520000200c03450580303000340800c110055880b010b401c03810304e09008250a41e04013030130340380c2d6a080c810042c2011920310301c0d0200b0203e46510109003241c218002c600006802036003481582d12142c0701d0380014420b00e04e0400f00050039521096a10100030381414200000001e9010074004040c0c0c1849200748400c4c0003038900d42d0741c2d04041d0b65941189040031425002c0040f141c1c150010034200014159100303d02904101c806440840150403000240303802403400c000039031140d007182c440c10741006103503210701085a051070044580d0b00040b5690034004c10080040c058004070402c2d1042e0204039520b0300b00c1065a481010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 413450602 1250 413449352 413449373
    0x1020706090b0f09030a0f05012f0901110f0102070605070e040506030a020f210c031213050d0204090812010305060a200901091206020c010c0807170621060906070302030c0a0804 78
    0x3e009481d10390101f03020420103401511014401d00c040d45084065401d260480030b036480381340880040200b1103c040c1b94015072214542ca00f022080e100003c46001d415800d81c0d20207401202c04990710010080c00ca604800580a11074041d40d0801480c54a81c0210b5583c2c0718800c030117842041d041458641c00d0761484107907a90b2545507403a019243c4005003540742e58111f40c029044c402e001c0c040000d00442d4a54044d18140d50108003420b0201d4944030501c0030070b61b00c0140698200380c5032030003c1c01240d4148010305c07c84c00072803900782d01ca41c51410b020f030a100010b450110b1850620040750241c4108100c503004c411000070600d03036641903400068685a1040e4422240340d901403c07144107101c21036001c6d00c14200d0400c0280102c002644040300c055204903283c1010030b0040300e00c4180c480040d05144c0d400b143c054104640b102c204030344500321640000601d500380c1d00c05c0b810041924814460141c010249040c294154204444041c115010703a0040340c0820036007500040500086901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 413451852 1250 413450602 413450623
    0x380409080c03070609061b08010e0415060e04030e03010b030c090a061d2a0301060309050709050c1c0504020901050d03020a0f060b030d080603061612060f0501020706090b0f0903 78
    0x7100da40e01c036286030000c050001c0010940e9410304d46101d081f010042034101000302c1d40700343da0361b080d81d81c20082e585c0d85000c400390041c0e480640b41e016a00314400b191007070b0005400165100280f918003864010981d50604039098000c3e41402041e000c01c0d2000140800300300c004680c201c15603a02c82d07502c18000e0105601c2403208000d40503070043c1d2700f42045d448500503c05141c001c03a45400541c085500c2c1f100c144d1700b2141c250b2003000100105480390340710800399440780d016904038542d541100801d480b0255003c900d0840c000034a10482c1540e04415482407440010510040c50940c0000d0135030078052007003070300924215440c60101072003800600482d9602100c900601e1a86003410b03c0200300005c0740754024490b144012000500450b0028401c00e00200101b07940e6849428015040c45080c60340421b003d46030004a44074003031802485c000e42121600740381c2071032601000900d4900d05501480030f11800d054184007075440481110f40c41e0300c0d84000c1030340e51520140880d14060703607001d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 413453102 1250 413451852 413451877
    0x1060c03180b031b030603030a121407050a0f0e0a1401090f091506081605160c030501021305010f05090904030504030b10080618031b07030c06020138040908 69
    0x81c0425001c1420014500031009804440400c40c00140c0d4880e5901c8140c1c1c0d603036450381c4140040c101c168420700c071340316003c0140d0780c010800500783da1a1420001c401d03585040403c40c0414807950742d503071000c41155980e809103851030202003540e010500c0080743e0301405807200d0500a00482590245609c103004040340c091805402d550365030000c3c01070108481410b00d0381c1031001c6c00501d26108050403400b5083c5240d00c0d500c01c00820328281d500303070310910010341a8581e0884440100d100031340795400642c001c10000d030342c0d02e00c078849012040000d81c08c4181170128141ca004106a48401a03e009070029a0030003141d488600303050700c41d030199620080a450700201004403820405241108440019040300d59079102c1c01c00f480d1407014010350301091944140040c3c624854290b0400703c403210309400780c03140c0e542c694640c110305d00c10387d07004240941e440b404d0a8001500b0004000c0d0303803000e5450328031102508010540004031011a00b00c2c131640d166035064003408048000c41300780d10303c001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 413454352 1250 413453102 413453147
    0x3040e0903070606060503061c061517010615020703060905011806020c0c03070501050f0d0209040504200102030915030603010b061b12030f010314030903010f0615021501060c03 78
    0x40062580c0d9600914044500a050604c00034100d4024800c1d00d0103407800801c40e0004008501d030b1007030010030f00c40040da1290345804d1510b035240d5890000001605414104170443c10210860f00e003074a001e40c3c05040751218401c203503a859680460190141c0342c1c0315002141c04845c0c1d0510f217014120f03072407aa81642d280c8108100402c0314076402441001c00140603501e45036911403c060320750419104440c00318501300025140c00d0705c26002040700e41c080341c40041c140400c401c0468203d0b0011901100d030b05c0f40e04c0c4903181d500c0c01d52800d02c4140381001d100561409071741e1004500f21031203420700c040141e40040701181440d40c0031b4121090790f0701c0140685840e07040703c840041c40c605550000614034000c00340c190b82e0404d04070045130b00c10480075400783e032a6481c2d0355400d100c41c0c103d050f60031754a00090002040c2c65a0a024018511800900104459090240102600400d003104405540c00388003254984401280b81c02d045449505001c24001c600e4102a2085444001008a610100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 413455602 1250 413454352 413454361
    0xc090a0e040f1a060102100c020c10170408040513020301030312020c150f16020a0812060622090c08100501030e07030204112d1e04030b04030e130207110d0503040e 72
    0x12140c084c0c403a2030309a080714040e070844c08912045904550000c0c0060f000482c0c0036000b4100100c02c0701c1c1480585c60002a55400400000b610b00c1040e581214446000070b000c000620700068400040240c1c24411851545140c1d406008039010a100c0342d813190300400c2441c0d6052051010101e2600ba9181c200307130078030340b242c86000400b40403622404503141ca200d404080ca4400103940e40040d51040c0402e282162500c904038140100900803907012a00b04011600c131610304420996502c00e4810700d0400b9801c050040040d204407010f40420400010204240445000c00800c201d8000b803c0000f08140d41c000b00c1ca0030507203031350000381d00181094416560106240000c0c28015403513403030302c001e10b2054020029020320050720f42002c040f0070f000c000c4113900c43c803100e4000b6402d060f82ca10315284c3c0c0c80d0755901c481c507801c070b805a0100380501495080e5040c00740c0c00c0e48510030445001c529020300c9581e400e01004030030342a01c1c003800026160200300182007080718050104507001c01e041e80340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 413456852 1250 413455602 413455643
    0xa140403140a0213060b0f1815040305010f0b1c0c05041103060907020706051e1603081005041808090d1e170f030105090403120204060f080c090a0e040f 67
    0xb00102c100d0044201003003d900e0510681708280a895000fa44a450501151450166a080326080241c660400b10b1011440d548070311302c06002c1242034554944031491824407a003100c06214121311071074142000201d199030b079501924800c141000452004981d44c0c1000d170006c11158002c140c01030b2800005c0078401c135049002c3c41c800c1070219035a01a60740c1e07010049031180680d101d540d0102e402408851000c50901075903213000032a03096001c1c02d00021014420f955508072070b081d4042840c03802401502c44c2c025240102400050b68140301c00310202113820b18900310154041d090007408201c25141d580c415080d20465900207070361040c00c00b201441628003030b5040e1030071150045a1041040c3d68546141070702c4080065040c0c2d030341560302e050140610501c00500850810541d151034410660003880548050f184030313a6002c070703210170140300500804000380240c2008001031118040b660350b40003088054030194038081d061600ca0b45842c654692003a000104102d021205d55800c801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 413458102 1250 413456852 413456863
    0x3010c0c050610030506070809010b0904140f07180b0102010603021f02060a051302010311091f020f07030203030f1b010c021506100215060310150306140106050a14040314 75
    0x18090350a555a6403a450456102c183d103a2000400c01d800000026494901607001203907c900e404c0004500c9070000d0700015520042210200c40240403a105000400401c011036014034031250010007007507003064210204e0550318803039540d5858507a004810164400e4103c5402141d0107080c15400c40440d1014840e602035400ca00302c018481c6c200028a0310a55008041c06915040200008100c0c1c5400440c0944500c00245034208400c02c80500315450f891140c0c00c02464000c1d014182201c4104020f0504454151220b000c0e4003120090001d6a404800c031081140c005600d1690b54522095442c580198801140341552030420964070301d580208503501e204100f0040c20400780d540340100203141414143c5840140d10101e4211100380040c40c5054001c4c500508035080c0702d01405442c41a071f849648190048081640700304104401406501c2078000028500c000f2903041640041c060302038412841c00300140b160740c00e10703c42a0241120003a40c0c000d9103000680411401c4a42d556 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 413459352 1250 413458102 413458127
    0x180f09052104030c03080304030c1a06120703023a050715031413031101061715041e11040203040b07090b0a12020702270f1b0406030f060503010c 64
    0xc9041c950228030080381104030b400b83c80d8060108822a400c580300c0c00c000b6000248114180000040304401040c2025055045203010300906041ca180000a001a5405c81c040c070102c075038051442480141c0c0d85030122203907000051000d00f01d1100d0403800e212081060188541002c4121a054060180c0418210260390800f600ba0150181448040301103504103c400c601c518000b0010610302c00940d42e00c07403d014040e1803c01c44070750103c9005421202c03164010343c2c10740c80b5030f05694a2030300e050000e05900f11000040c1c41e001d00c0c19441d07681251203240c5a40c004042da070f0390450f0420443c86406048410b000d4021908c0b03107001d250111518000b620341e0004100359080001e502c00c10300381122402113042d41d0308200b1002c10100307a030194005d40740490b4003042d100e102c41c0380c65010804c11507200304981e00149031400c0510708603941501c0504007030344d0310316110551003251040328100c6045441c0d07032500003000c5548811000c0107004030340017140d1550a0009c040130b030660000d5004c052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 413460602 1250 413459352 413459383
    0x120703050603060712020d0609180b130308060d210e090604090c0b0d110d0912020714130f110406020723040b0a03050d0503041a070207180f0905 64
    0x1141c981c1c07020140d0700c100c101c0c0d828000843da10354402030756a00380c0180c003c20320410008110b40b17440310300507400d40f01801101e00c02d1704842d001e180c0c10700040c46500741d0002100f90300d40ca01178440307407001422408010640b034051985207030b110b401c02a2a80c0c45403503040180d5103000c00c0c4000c030036008200350319060750541305c0e107101e002041d0b242ca0644140034036142d00c045940c2034032345858000d500580010005501c0155a0407090525020601c010501c5a010b514001000706151805220800c29150786608641c0480000d0202e180c40216800008c503085a01401001c0c4150342080908104621710312843e0a1114014030561002c9c041c4c404d5030070b9078090700c015030345545141d512010481c59800368001440658000c6040c15440f450048401030a0105440d8594407964940f81e03244003c400040c00002c00c010a020010828850302c2280006400c4103040c40c2c00d000355154030314003071000d1614080314543d40c0c030000c0d948110b1038088410b10a0281c682c80d0704040c3c0e00e903030141c040d2144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 413461852 1250 413460602 413460611
    0x40602130810060e33042003070305011a07060207020609030a05010c11030c030d0f06150c020103051503060a0b06190504090f02031009021815130b0408120304050111120703 76
    0x14819036080ca18101700c160341c000030518021070801c1000b008440240b164001d903a4502c1c0750006200b80c0d240c99070803202804500c0c2d590501007801011104160b019004600d1007441040f100b0081c0e100b2030b041250406005a180c0c2500e0000481600c01c02181d40d17407611861001c4000c010042d040103442042076200c0d01440076848403a1516071260030701d6024641c000708201c1c03641490300d0788282003000c43c40701c00113404e03502e41400100211104140d100031400c44039100046607414002c496000c0c00240d105044180584042581c40d4406800d40b100b46464003e20708840d01c50b04241c4541180c440e18018a0350004a0060b1207a4018002c50a40382e08286103002d40103858021030f030169040300f4104803020701d0100320304025040003044a00c02000308034010030707664403000c03004501c0071030184581e51400380c460100c241b050303640c2c498603a0603001c0c00200a28400801ca0311011402150070a540e507640d4505580105050b541d002e031a414081880d002e01e4400303046591040f082518101b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 413463102 1250 413461852 413461861
    0xf0905101a010203041a0f04062c0d022e0c02040b03010212010b210f0718080c010c0c080102040b1201080f0a0303020a054e040602130810060e 63
    0x1044071103a090346409a80100001c20009005104242c1900c4020421908110190b12203000b40c2d80f16a1080002440141000c20300307228080c1e48900519001c0d82d003504140f15a00441c0e980034a01030f0280c0308202c200003081058403030180e082511040320440c04400003500b4805066800880e40503401149040f081c202282014822141c0e04240c0000158990703285c035007156007541c48540385d031079100e41008882d04210040c0c8501b9000383d1400b1031134012032030032850041151118001c1503514520b44034003088240c038041203503580b0310001e10300100741d001d143c00c006582813802e070701c49000c42d0302c00500040d080e02d80202404d43c80100c00c1d440561a640c980c226507403121403d4111001d40c10200d25100080d000f603005041c481c1e06400c1c0035007030507945043e6000fa40300010040e0710107812038200002c103e02c0314100e0460358a4802c0c2903145008039450400729004c0091005105650000321403200e00300c12001d040090402070300f1a0000e4611a4007200170b8402c610607000a4000b200200c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 413464352 1250 413463102 413463131
    0x3020d1421010f0b040e0114010c06050f04150207030906050a02031c090b0f1009051e250908070b090d0f0804181b08061c03051215011202030702010f090510 69
    0x11000c40b42e90805d80c116503408d003201252409a8042c1180c140025109600001151406250b20804080c6a07024089c6401e00700040c0300a840141000060710411038000081c0c0c01400001c25607496160181d194200c0b0f6400341c0c614440c0310681c1c1c0340c2044422103260032101035081408058410400c0200e5925544201441d01c5002e0300e941c3c00010f1003040601c2101d00c1076005079401201245040c298010a101c1e00070380440a60b03c1ea607016240e415030301c48071a1584c1c0a02c4540b0035a103050101c3d80d00d40f655850300e5a4031401482d115040c0081c1860860b51503901070300741c003500001143d0000da01440c21b10580d500c03500c00c2541c0d4802081c16034072036000b00e101740c492461300010307050030480380000c04aa4005001741260707408100001c02030240c1140401d984480c610a440740796607001c108140000710080104424469180c503240101d90346d81c44031224480556005015860b51200c000c00d82c09020140d80181425142a25070414404c00186c1e507040c950746c0a00801442000203441c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 413465602 1250 413464352 413464357
    0xf02090f04090f030f051b010207110603010501170c0f1306020f06131515060f12110708030901061509060e0316050f030106050315010f080a03020d1421010f0b 70
    0x580165403d0380c452020900860720b40d80149140c4c81c14601e4410b030070b1031081c401e403800f41c00d06100c2c3c0c0d40407510340100098526000030320703042120207e045600d0440002c00319115980c019510700d034140b0108111088400aa0380102001c8101130b03201e215a0045000080340e038403c0c1d1006101c0d801158007008404140c2c80d00440f0301c041a500070014945441590342c288450309030900b5504c2903100c40100148600d40d01400043d51a031400c000c45030780050586240f6480e50794610715101c05414554100000c841c881d42c2e000c0071807926a0f85140e84540100425801034600418088013000348944c800480d83c140c5400b910b9074801e042e41d120074941e88019a6880790081401e83e181845945010700f400304d46410000d00101e41251502c012901340703400e0041101a0500881c0140458008650000c01410207440201800004c81c2c80003903840104002940910152090381d0100325804000c0301c6807113074068100c1c0005440c01c00d0519118000344502c08200f2500e90011810741001400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 413466852 1250 413465602 413465621
    0x806063f071707060806060705010f0b15090325033809060414070503031204060605060f030c07020a05032b0203040b0d020307030204121a0105010302090105030f10090f02090f04 78
    0x1c2020704e0070084c1c2982c5528010388200d034807000a009080014400740a40011b5003503c80300419a0030010040c4003c4201202500381a18418022003409490000380c076110006900b40c1228885100000148102d070207400c05410344016131940340001010480c409565043c090048540c503014140005103400c05859400d4a0340015000c01d001c0f4945511000c0c0420360f450648801d07a60b41e00020780381d03502211a804c506d1586c00100814011148034001c01000c00381e4450380303061800d60031004a44001172090034100e401040040664030341030350590180c01c0140480b180c0ca10028001501c0c508200000c0890b00c10103416140c1d59880441501e0031241508005800d00d8001901280a504020b01480416a0074000001c004813040744840c45940100c80c20513200c03008503211041c2d0b1360305800c0b107818103004002442032070b644841141d604c500407030740408454880d020943d0211049030301c20305c0302da810040e5080350070a40350300404070a013003280c8107060b00040e00b0500080d22041c08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 413468102 1250 413466852 413466899
    0x14010909020907030218010f09180f0b010507170c030f0c030c0c0307060f120b0604030c08010c0206150d031101112203050618120f03060f04060806063f07 68
    0x340d6108031b55015215603d80c000d03407401e00682e820b03101c200400031481180311102403203468060100c0c0303c400740d1140109100d401e10344985840465192131204040412002107030b61800204030b88202c1061051725040c040b0f9000c501e07131710084406001d5a81d040840035144c00c4c0103200c0c01c1c04080c900003500f407085a100361907444132580106c40c1510259903841c01c0d81401380d2140e0b07000f01aa40c40d40d000f8800f0394498000902c0301800d20100314215a4481541406c0d50711070340078811240e9940081600c501030803500524280c283e49022506603a903500d180140d50709001c8696501e4450b00c0c040d1840306080628000d06511010412000050900c4007900c02e41005000c01c0c0f0a542d010b4072103014100110499801e400200f400300c2e2107512034001c0c00e0303015002000340601072074a407030b401e9540c00d0201c50500101d410026501e880c1c2601501440c4a008000400784080301c0c47e10250384050f45000742001c050405030719034080c600015000305518011180085210340554400315008003529 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 413469352 1250 413468102 413468137
    0x80915060607062403170310150c0b0708150105070b0708040c1503020406030509010203040203100507030b060408011409190b270c011425020103140109090209070302 73
    0x18802942d200c01d100b540c00703079100d94080c070240e8003c12405a0740c4650004070451140756040518141c20b08262404c0040b00400500046601c800d01240664401001002488401d000b003540e64070b10304a00140002080010000300580003007449124145500101c0312a81c0c140004590707a2041080c000c1c02e0b00c0e070001c0414202c500c203550071940244100030b0f900200f81c41b100d00f10211350070000c3c6880001e40004052141c16414014250042c000000035425400c15500203901c4940c440c01d10251103036503100240300203100e90403101d0034200140c001a90f860711064020301030f0041b078446100c44a00d903804a0001a0002011043d5002e400c1c40792601c44003582e103919800c2d030013400880c810000303075a254100a4021900000011800008040752045040003404920601903111800300e01800034109511256545074910428581041c05508040c8016002811403002605103c00c4440003c0740345000da510020031203000321005e40e440d07550b003a01141a0300c6441c07010074405508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 413470602 1250 413469352 413469361
    0xc1e0f0801140303071401020304050709050f0402010f03060f1701061a070809180c0a17060105040605090301150314070504090804050904020409060c1809200307020c04060312080915 80
    0x40358103885400b500107003541c2c60b001150300c60781202541c5900c4c00080765400814001000420800c2400030158102c05204a140c584507425126100900290600030301500c1d00315981d200c0d501c44170142c0303611800000181d4a1300c81070703850450003110705d5040e9882d058001c211210300c1c80c80840b03c5100d4034a424a00652503035007140e2074212800081d0060304800c3e1801c03001031548034084c440c200c070400d500d407102c140800061440034007905103035204008005210030750f40d024080f035040d0350860a040b5540d2032000f0100b401441054030b050007520583d0710200400000038032500258070008219112603032150100002c5071285207005280302c800b04010445400c4c1909500e5203e0f0005000282d09011340d1140026120104400c5001804001101c4906004903201303801800203035804100c01c142c2c60540e0060300080140924403030001000080b0b80781e1003080700481c01c503c080c0042c4081e036900d00d8005c4544440483c00c40c0420181000504003071800201901c2c100000000920162217 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 413471852 1250 413470602 413470619
    0x2030f061b07050312040b160f121a280806060d020108040201020a1406090106090216060e10020403051e01020c0703060b2e0f05040f0e1003060c1e0f0801 68
    0x102d08030784500060016250008507481c1d17071841035024070f496480d24507150498100036580002c00105100b080d0403520009503000650340c090b0504a140003460a800081e0504580102c08425a000a142039100b40d040f100c0d1441d40a40703240303400f0000490781c82c2c090a6803206002c540d012b400c600440981405581700398642c6401031b0041c0140c0740040c5268450765600950640c0d00c3c280b81c1e10010070310240c68400d11440c00280012001181011416800d40d26608108a0040d0401d81c54915600050303105200e82c5c2e0219a400c50304540d82d07556490a0381d02c52009100d00d4500300741d005601041c803101802201c0c80f088200303002d00461410b6030707684001410a8600d80e900060341d81c1c4841c2c1280110030100700f89140750940d0310318801400e10020b142c06e0a08000004020040c041008001c0c030200440b810713150703d013045098541e54a160402072440c164406080e880c00c268240c00b550390003282240b50174102c103100c10186912820140d402d0b0410040c00360020301c006004200e94034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 413473102 1250 413471852 413471857
    0x3070c0f030b3103090e1b09040507111b0a0e06061c0f0e060a06141c0203280c0501050c03120604090204051906051005041707030c080a02030f061b 65
    0x2034044210068030108140b8655164034440012000b00f1031080050103840070186e11140d2189245000900452500ca07102001c1d014007801a8020f50312003000c0782a03503002c0c4810070104641c490441d401c103014030440c0c4030b000504136560750140e55208000305000b110000202d110b44805443e8525085070841040040c10360302000c1c0003010790300c0740c020074050014003540c0d95280140d0014885030600200c2c50003100c3c0030741d0150801c942040b003440059142c1c0c441f03d00e2451000084200d40d030380e4900101e418144c000104284080043c040349203904103090b401c1e0403a80c05010f0b1a11502e88800054441d0702c51041500b01942c006e011103800303000e021403400c0e440701d0041d1011401c041140e001c20203649042d0350301502102e14241da1071224542d4410903000b06800ca400c020200414000544540300341c2c041c8484020119200b48035010040141c44010356210750400d24455a0f410255164500d645c0c0c100d100f8051010100b0070b4003000141c65028211b030242c4c8241f42610010702c1c103002e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 413474352 1250 413473102 413473141
    0x7030503061306180c031107020102121e040306230403080a0c090b0714060a0b0604060e0616050102091201061a13031202010c120903020606060d060f0803070c0f030b 73
    0x1502d40c640400e04400c1000442a51540e0134000310b031551101d000079064440c1c00d401d203180301d00240201343c003503a800964400010000c0425136030321082164501c1039000c0940e41800c0981000400204114440c1d2203100c07202c00781040a00354042201000040c01e0701a50050b000898020108481540e603a02000310000582008090030380d884641c2c1c01c0c0c1e40c018400545050080340401c801c00003040c00078540c03009003060100701c1e602066000070310a00490241d10108400c5880300ea046488000403591504c4a000408984c032101b071400070b02139030081d0b0803603001d82440030290407600d1050140c0003d5840380010310414040c80d401c07640c900d40200b82203c2d4503641003080000400c04000c1005c00001003035001240081d01c02c00083c150280c8422444c850b10702d441410404246d02003030441c0c00c588101c4015645003540c00b062009410660030070150172009090020b00a1000801000060b02c45c102c204c00040d07480c03000002503040c0784006000e50044200059084110040c0f59188 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 413475602 1250 413474352 413474389
    0x91302090d0203060906070323010303081306020d0506040605040e03040e062e09050105040303080f060102010b060c03090a21060c0504030f030e041d0d0e0a05180a0f020703050306 79
    0x105100c0e4002911345007003924654101d41021003441482d50303050252070302d261020705180b00d1950300c41c0c001416027031051001030304015002001c506415204003c004000360019000d41d00d4004000b000f82c01041c064551501c154601640095a400d103801802d5913822a10301842c1000e140c41c03070100e080395004109980c00748240900165041d0004004000c901c07112110a02c1043c00340c2c0003901000c40d40d0089414400d05010400001c0c0e800083c1030350045d0300000030115929000010303400340c94180c1d155a030204000c91813001d5984000b01038220704104451810020390741e14040c14039000820794024106d802e560601000c0344154004006004051406502c2c2c04d913242c680c10500c1c0029441240040c5401448000a103424090102c02264003166540a80e0402940c00e60303803d00c1c000c0381c0c814410000c6444d00150785408400c4000c04d00540044452045008107250382c01c011500d0b060b8403842c0c5200c0914811591080d90001a45600c5040c95511150100229481c000b0301d0200d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 413476852 1250 413475602 413475619
    0x120609060f04152706230d0f08030903090405100b0a05030714032502010e0d1101020c030301080715030b060a080c19021b150f030415050705041a09130209 68
    0x41d02c00c1d41c06600e030b04d00c400342c451200e01c0c0018a03200805a58180d4400d5080340004440284038100b00d8034403a10301013003102c403d044c400c01460140d02440c40b0043c0508290804410084003003000320040401f81c6007290304010744e580c0c128480c520498640682d514405040c00000c40e01c1d40203100231500030135142429004e15500007a0f00160b0340c0300b203c4c0c0907089504424403225a06c1e80d600600049a4039000a04c0109814142d490791010300c1003041e02082850803031489415401e5045a031408000820b69030b4039a100d05200d0b941b642c962155541c0c0030100d400050000e44a8440c01c440c3d00b9004244a1824202c034004989100003d05240f6004d00100300f60f06906030382e0862010003400c1600034001c2d02c245540802600d00c120014076028000381c1c4400340d012079102044071868000000102d403a9100d605002d0020040074680e049554508818401500c0d00300340904103c4508802c000c80740d00300c030880d4400700d000f0441c0345608641c203800b50382c1c80c00165030060300c40d401018100e0803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 413478102 1250 413476852 413476859
    0x50c07050106032405160e18040b090609030a0e15160501090b06030a0816030201140405060105031b03030d091509081903090506150f10020102120609060f0415 70
    0x2400c46115a0049031090121564084d5000700442d80c603214280c0b0950030440b40c5481503218a01000c50080003042000c03146c41594030340e03249144002560a201c00c032542d80d203040d141c4044800c405455900a6210b0980091301103d4000212145041282d03250074082031588240005030064030b005607040107050081110540e03c0c04680c02c0705074000d000124151a85040c075142c000740281059009400c513010300d00c04030b11080211210b1280d080c8004030719181c01c1c1000c0380107001841034070800012810a020500800246c098180c800c11000c1c0d80340e482c002520f0f044d1000781c13181525003580003402003680c144803503404107400c0740c0649041c2c071000c400030400300c0c00c1302d240b5803044420b850301007092504140041c5040d140480b080c18100041d081d40d0b03c0c0e80344d640800400c1e24207600d0707424182c40700c56281c000d031920036080040e0202c1e40c0c842070032002a0103900400c046111500d8150b000660030f1402c8810240200d40246c4001041041201408040c2000d07202c0441c25405012000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 413479352 1250 413478102 413478113
    0xe01020705100f0e010906090b030402210604030f050307090b09040e120a02100902010e120f061305010506090403080703022203110a140a052e02060702151603050c07 73
    0x140002c0c4070b40e030303181c1c080001e4481c00a0f001420540d480c90400c1109003003802243d4010001c0307000d8447c00840030b5105c1e6103a02c00140d980c1000520365020000c19504032601040008003d801144291641000300208032811141d0340030403219180010203540c01007000c010628010142c1d910050004030700c6000078203e0030302d41083c10800700c5040c200000e038119015410300a0071130300d6100e000d05120110807500020102c03610400c03041c1c466400182036486400301001390110088505d0300366555072601151030071f4450b4850303005413065400c040010302546401e21100c0d00c6103a042e110320700c13151110b01e011002034200400d940ca18000e01c10034080c2920f1480703d680700452084c05c488001030383c0e4005210722190b582d031009529184a010290559584510560664000340c1d114010b280f00c4803010814800c0f41c4500c061107245501c07080450540c04284580b0a23a0140c089174401d00310003036140000380c01200c3d200c40865042080e0500b11381309130002034000312440d0f10f02e8281042529035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 413480602 1250 413479352 413479369
    0x506040f150e0c1021021c2d020309121305220c02061311130207200102030901120914060703060305191a07050d020d0509010b09160e01020705 63
    0x1401a80d41c402084084107107420702c1e420a042c01507140130098401c0001c110f48030800e141203172203100c40e00460302c041c0d80d8218101104030320500301402c0c0005808c10400c45082c400b4580090540141c0c180540008100c46c000c8030701810f0310800502c0a20042e6284596540240c0481c107903208608800103003d40c4d80d04d200041c80110200726241000100c4c3e007110484038440c003648155040b03d010031030b00c00700d2500c03480400394000c460121041da61200040503141c1541010301d2a0f8400302e140304c18071040402402170000c0040e07104244040100c01680d580c000c1610150014185169110240c00341e0340120030703207034400c2403940da20348580780c0d0300d90030164100e4054000903a00c0d0390410610104000c1012500c1c06100401020086038880351500e0081400031a00c54003404040b0302c01d5441070044071014581440c04545400251040d0005020123a844030303800e40c20a0502161483c28500d25070066102100c0b4003034140c100b21090322002940307817155042d40100b9400080c5c0741c075410b07031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 413481852 1250 413480602 413480621
    0x20c070f0503060a231314010518060c04051e0d03051c0603150519020406020a020112050f04151e06030204150503060c0d0b0607050c030d0305040506040f15 69
    0x201098285400e1524005000b041d42c04c1d110305144110340711001000b1060280c60b00e0491a01050b130b00e40401d0701c20f010080e18000c055020650344007140c04010340c0124019100c038020401a00404041287c4e82c01094408031011042007108000c9440c2c803490606000d4001d40004c1903140d44100001d032000f0a0031402e5002c81c80c0024030321a0420540c2d00c0e52440401e4007003c010480c01c546400d170340b03048029000e07031009941e0004104220f01a50310500d602e08280815561941c5a4400a44801082c007040f030100e440f001c4803410210f034500800e4842e0351000281c0f030a590791512115010807901030044100e41e03480d81030200c100c50400e0301e42c98002139044081641459481404210b540c013603442c80403010b1811043c0a5940c0c00300e65203402104c1d14144680700d61081c10584010700c40d6041450b485a0006803c2003000b101058601710318000300c060750000d0b180782c0c0b4140d05940007160024000d0700100000b500190404110660450203142d848100850303142d01c2d401112101c4a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 413483102 1250 413481852 413481869
    0x1b050601050d050a050a2603010e04150902100e030111190302072414010501031e02090a0b130608090604080f211906050d030905040c0c020312030f011406070b0a020c07 74
    0xc0000d080f47c0000855120441e02c0805924a1517240c1540c81d410070030040c000404504203801041500a0140c01c04140e2640081c03910158615101c00601060107103c2014065402c00340294003c218540a481c41c1d03a50030610304a1203100c683e0200c000b9400440119010212807524030a249032080c158115000e01210001e803400103d50340c08807418050780002c2c1010b0400d404401825a2107140c100d600110180240e100d4000e800041e0904100b9040f03601907080c0822a86020390310b03841004120350380c0e62a401541d481d080305180c1c82e410704841c090962601080f01c504a104010b0060641c1d00c540c070070281202d00c9180601e0185041070703c510f0030582060300450150806803080d00018001200c8580c60354000e0b54018050074414401c00e8481e41e500c1d1940301c2004d010700c42c42c0c03c2d850b40c01019540c2303800d101417441340d258005840301010030980500100c1c100b1603040c554200400000d0006084c0305984d80da0006442c80101400c8034150240440c031524581000b24601070881032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 413484352 1250 413483102 413483123
    0xc060a090e0c1309020f070b06030705030d02031b19150204050904060b0118210f0611180603010e04150b030f0a1502090a032018071b050601050d050a050a 68
    0x184084000f0654039000020900c0c81000b21601e07410b40281141c060795840000801c82d41d50740c800007803c000305c3d5401280c05003e003070070510b500d541c0400240356a604210080f0092015043d80ea5643c2094070a58814440100340740c101240c0203403428a117910300d442000d8941074580c0c01141d003c080c02d0b14204e51071a10b4002c12162981c000000301145c403102d100f60074205241489822603a0802180140c07000502038440040c41100c04040040f0f83e00040284090400800183c00c9a40080d0307050310000c540740d1040076036290040450741200c0c00011990701035100c03500d50164840b40084c1c0d018403070340c0e83c3d01004001d480912541c0000c0c003449020700806d00700c5040014010f0701403486038503a070b0b20400003040c0555407450a481501d4000e519030410b001d90180645000e90300588075071b4084030143d01d1500e001071008070a48168001e40d10608040d0700b2015868040100140061a5400c110f00512250800f410851140d03801801101c800f00d0140e21601d041402540f4203850840a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 413485602 1250 413484352 413484367
    0x20702040c05071a0c04051e0a030b0402090a0501120305090d0c060f0e060304080a1110050108071701180314040e16090501020712080306010509180402030c010f020c060a090e0c 78
    0x41103481303003418081144410318501240d03a00ca1622440c012144509100c0041020110780c41252598544000e02403015440d2030b402c000705201d01c01c4808a10600450000891459003401900e040f034610005000c0000440c3d503042d600b81d0040b4580ba0f07040726043d901c031004200c1e07039030000d0010040f50704c40c61008210054000c00d00c3c2c04240700240140f20030003c0c800080c00320f0b8202e5490141c0c5207003150440c104c2c2c01d06142011200e95a10601038100381c004611464045064002c50f024030021100ca00f101400907426101000424600e42e010801c554000c02c0c0540350145004480354002481c20340c80f0f002c0214011030a0754010a09001d1030b40001c1c4440c0c22030801c9002d8a003d0004281d07141c0f41010610301c00220300b8005000520100100300c940e40100140d034041c0d00c000b41304070010701c030010781a00d0450b005c44050788a8031920340741907025402139030105185000c660107000a111503009000096004018000800c5100a4002040d005801403540101802c000103940c5200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 413486852 1250 413485602 413485613
    0x40f050a050106031a150f2113230705030d0e0f06090a0326070605060f04050c12180304060906090b131401020c0a0f0905090d0e13020702040c0507 65
    0x1d050308040c0a051500c0d0b4020f200c05484021131160000448004034070800c0031040d804140200e01074010f0b402d0340803a08641e50300c0b41c05006002c0341e640503014206d03542d51110000240c0040407003d8000d05002c241d040c04a4291350f01c604407540f4600072286155603031000b007440c000340e04115000003480c0381c00d136081a15155441c0080b200c801c40c0c0075410003c00000140d401a0a0702c0001c0c0940f203d6a401e10400130a1102003100d212030101441d00c6985c2418a200034000c11070303010348281481c10b07010240d4034083c4280703130280d6107217081c40e82440d09202c9444c5001034090100d08503a9040c0da50165680402c0000b000030703041c580c7e90340e0446450004040d20344030305500303c0c0c40f08840601040004042c0c3c02c0410703040b2004c840a00c0d04981ca6100140d0a203c19000046d421181c00301012412104448a20045511401301001580d03541071499444400c01006c0d00002010344983c40101d1030712440d450890700000d40c00510700304481c0e002030100c990301c00084020540100382d4034180403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 413488102 1250 413486852 413486861
    0xb03060a14010e010602120d0b03030403301d13050901230403080f04080706090b0916080303060409290106080f1302010513030b01180c05040b090d080702040f050a 72
    0x1a5810503d10107504140300a9110105244440b440360804100c10000f500190440707082618080c2c00d8a03a11b0743c0300c1c20012081e02840b6000c03210249484000307400340940c2066200b01c4844e5543e0381502c440d2282c100e0203080301201540354400035280c02407a16000c244615070241280800019045a0b050040c10103044e440703007502d0240c00340c2c1e4204808281c004100a5001002002600d41c0340c0e5285000400c900a08401600051502c6208801c10070030503003c5014940900440d03880d050580c224200381034560017590219007090005c5500f0742000c1e0407000c2224450301e110100360044400e001c2d43d1141d8100b05c4500c90f941079004000b00354101440c990001030810500c2186d2030070395600f1540d2900d4200c002d04008000500404e10726000a0b03000207580c0c0718000000550b50707641c02d0215803054008144000f40303422690b50300103004600300c50441c3c01c076141c9181000419020400c0010a00710240c03803142d0108622801a42c42c2d1107580700c007214040e0300151500300110188100d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 413489208 1106 413488102 413488109
    0x504050402120109060c0e0312190e0d0309030201030507080408120405330f010e010e04020409021f0306050a081f020d06030c29040308090102010b03060a1401 70
    0x1940c01c070126000c09a41c51f1085414038104041e1102188282c10760b90441c104080140d00c140180c202c080542c2c81d00b8260000c0700030318003007101510f10100c202e00007900d00c48244119a014410380d40c100360141342c0010289055a51038511307209250600303011a50746400142001001c002041001c2c40d4101c489601310983d00b5000700c5601132490410b4259291000145044035080849049a02903104141280d180c03c2c0071301c642040280040e41c016854480490240c0c49010700000041000d00d01d49076040311842c00102110401c0c0c02c050b226884050040150040c0040d0f03110b0300c591030031240d08603403065510000080c07081154281c0c80354145070000061040d0040a00111003003808010010380c86040c10b40e062031034884c0c542c1d048400902003032010644d480c4c0075021050041c0000038030300354600f00081c540360088a0391003101d5143e9080c0c0c045091885000f9004 = true := by decide +kernel

theorem cover : BRFrame.Cov 413309352 413489208 := by
  have h0 := BRFrame.cov_init 413309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 413309352 ≤ n) (h2 : n < 413489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
