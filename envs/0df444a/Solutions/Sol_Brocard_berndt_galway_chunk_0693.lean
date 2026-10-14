-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0693
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:11:20.352715+00:00
-- url     : https://prove2.me/submissions/84a4fc7d-440e-4495-850a-ad7630f2afbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 124460431 ≤ n < 124640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 124461681 1250 124460431 124460437
    0x9090f04080a0c050705040c020f010e060f040609110d060507030b0307060207031e050a0803090607080c03010b1602090106180504060602060f07020a0803010b09091b040b09010e041802090705040506 87
    0xb000a002d0040d858008021003041480701411028005000085c1c450348041d40c3d9150b04441c1068035400d1040401150b40300044141c4110b01006d02964252160744031040102807081c4182c5555241c00350021460303c82201c0460341c9840345d440041e013417400040041c00c880c030f503103440e40c0b20350003440040040d940d0000e680801c0d04d411011281d0116030000d0f4061a0010100d8001c115000e01c0144009008400000d10b101c0c2008101b070f40da16507a0014200d840d00012034005d81190028070042c0260007580c00603080d101001e890b600d00301035454001581c03640d4240d10500000c0c9103c9140c503480007103001e48000805094400384a642e04014003c0c0d250315005000902e64100c62000410b42c130700c204508114070380c000e42d03055902e50710340b881c0702d042d0741c03110080d18043d00076440882d143c1408158845009507010003810f050a0501c0d0702200d040d0b00200b84541000b4200300b40c0f180300e50711841030b001c422110124201b4107440354414010b20700c4c4014403220a210041c08100096107500081b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 124462931 1250 124461681 124461697
    0xf010b0a110705030706052124040209090405061009090206070308040804180501060912050703120e03030313061107050c060a030f18110321090307050d030509090f0408 74
    0x300d41003807406406024038091081d40095418803c0200004800790040c0050041d00f60050380d4000900061058030070b811810740e41c8400140ca080d0b41d490200e81c0388103107071307403076030f070001d0000d481d080d84c02c00064071424040d1401d0b6141d410039424440700e40b1000e0f01c81d5004090419040c8a60705041e000038001d0b000b102005814071211b85c0014041084040807640038083c8900780f40c0d190003d818189004040c00d01816000c03a51000002c60060301681c5190101940301000307007903e908541d60b412608084c0001e0909008000903142c10380e650500146104200c110010040c498580c00d1140c10b6400c1109442a959400c000540102d0004101c40c94502c6094801c1369640b014103000b1001040c506e803058020b14030f42041c50300250300c0c0b170028214680c000c0c44081001e4140f4001c0540360b900410311000110307441c080181c0d50000c1c04002c0c0c14030b05e030000c0640e880c003075072080400c90540c10354500300d000901c00202540d8a14044108a4110000c5140d0018a2a1035540d1124600c19540c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 124464181 1250 124462931 124462937
    0xe0f0c0d020907030b06030412030b0d0b04200409031e03020306030d050304030e1f08180309091905040b0a14011a07020d061113090b0306011206020702030a030908060f010b0a 77
    0x183e105030203900400407a010240000d6528509810810340040c2c41e800408002800c2c2081100c03a4540040c09520680d040059000300b9202c03640c03602041e6071184003002d892090390030302004a50b01d0784107012409009840c0d82c404011100040080b44007500851740c149403052007030204035100014101408015800e0903a503d443e50700b41910310f0440700d04410b500c5803800011051301075800e8200b00960513207440340300d4152030745d031600c0300d107851885a0f080345507006112011840c0b401e05125030708114103401101c80d60390f0300d0b0030074001c1d2502100d0549800d5615400e00010400780c2c0301d0980340e585c1c00144150036504059a200b242ca00c482000c0d50849004182d54041d9603c8404041c9401e50007041080190358034144214181c00c413122894490b41d6800c000200f41c42140102022500003d0140405a003091200c81020841a00a882c01b6509021680c01070b1010810a000c0300d00a0701c5200c034541c0343c404c815240100040c18203003030320302e520b004001072001c01d000e541154181781 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 124465431 1250 124464181 124464199
    0x607090e07030b04061413090302250e0f09060c040509060f040b1206090d0903051e070308030a091103161419120209070f050d050a0f09060e0f0c0d02 66
    0x140100d01502107294801d501514068000510000c00c03401381d800304c1000d503a80c55000903c450407074211906404003501581100c10300d00080d42c1801c0d032003030742c0b006004be01501c0c1035201d82d41911145012507070822a00851000c0c441c0c00c040c100103160384800bc501681d413505040101040009402500e43d9000d100c1039120001c00c3c0c0e07284c1d00601c140748009070003c0090b90040c86910368540058035800700ca401540c400401252003015400240d0350403c0c014031007850740c0d1113a550080d5040300010001e021b85a00071000070091070046019006000c00803500e1851410a94210201c022405100381d001c003030607004604e44654806e0481d005c80b0303464401d01c110a400b0074440d00c5500c61010081d0740d141008641c00400624044a00e4000c7d28021400c0c0d41d83c10003900c400c01e580c02070b03c010690900401901241303039040590720070210038001c507140c01030009031030541b148000101d482c184c1b103410108540204100d03641520402c0c20013000d40c0b00380480071488003c2140b802a0181c0120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 124466681 1250 124465431 124465441
    0x60f0609090b011101020c1c031109061e0a0905030d09081905030f070507030605061014030a0b0d0f1205040501050f070212030301060c0506010608070f0c0f0206030702030703020601080607090e 85
    0x40c8880001400c488000b0f5648540f0354204036101c613030032003108c1e49407a8440079428000b48280b090082140c0502d8903d89400c03004801c01280b50403034005103c40282e14400700a85800031000b034500030705262500c080b41030030842014180002e001c051010820828020010400c00040e83c01e144600c80148403035403403060800c02c0c114070960010310780030307400090440104540041d450044a001d20000c002c540c071090104000ea42d82a0100b50004942c01c0e40d070550441c00b4001960094085540051300d4085071010554150130050161402c0c0c0749440f0104c18815001e070700c1c0620340381c2450114034103820540060154000d8111800d0b10f5a000324414045484151422603080c00c0c8a080781e8407581d4400000b850009283d4003240d0600075100005185070081754818060081c03501c8074030713450203204012902c0c4d81a4a07402c1e180404d85c40d2000b00544c1300c01d801107014680c194050742e41e5072045e0401902d00b07001a401104113a04c6101040700c81ca5100e4103802c00d6400d001074502c025254 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 124467931 1250 124466681 124466687
    0x6160c1a03132112150506070b07030623010e01030501051e061209160603020f0301090905010906060605091206010513050c0d060b18040209090406150305010f0203010801060f0609090b01 82
    0x211034818400c900246503500755542d0010041400006032913018000111081c000328a03940c194460107070400418400000004d145024a03a84003072280b4000858542d110700031001c80344400035000303040c0382062103188103580c0003107000010102030a0a00041d4548008683c0c0c4406461241240030303091410080e43e0340d900c0c8121900d940078000340d400b8605000d80c8031900c079040120101e5003405c403480c1c00104240240251401e103500200041d0030342e03103410b120360050940f00c0750490f031035540e8444000c001a614440c1c000074008994900e5100c49041d070030700c40e804030420400c02159018200400041d9500c01c0b014580480b4241f011030b098650440d8500b00d4000d05428500c168140700340401d4010104002e0701d4203803042c03400103d0010031281880200d00c12416030fa500840d1290000307001c00e2554200d0361040c03900c4d2200391502c598a8845a08684032001554030701500080100100d5600b40160009000c5103800041e00b1482d160003c0c1200c400c0d80b0500030309036140c3c10381c0e6007141c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 124469181 1250 124467931 124467953
    0xc1602060c010b1f081f060f0903021201090606081f020703170705031b03090604170d020d02130501020304051323040302010c23090d020402070206160c1a0313 70
    0x800540302c200000e4641030711203a1024845032a4000070a030b140003034090500c640030400407003400c0481482c0c4505101c01150120003c0c2c88d5501030140040700000141c0750f520480380b0341416040001b03540c0000d841c111080d201e1591103210590f11500c2c4200c620070380805500704103c103c40c0010ba03902c140d8602079035605019000240c8003c90b000400014582020055200344008074480e0400300710415145121b001c1690100740d1603100200250008146039041d03a03040302e61200003410322080c90b2600040ea4061450140c0c00c41c1c000c5880c400f00394a094807403000d0712003400518142030401021400d010440b00c4240885900c0702c07110b01030511040510408003200d91003010040c680f82c01d02a002c1d02443c000344000075181c41c000e11240e180000040c41d000110204d462400402d8001c0141540c0640c0c400d0b41c0c095070801950005940340e4005104102408802401441060900e040034031102d51116280c41107030780745100119543c0742281c3c1d00c05084860398000c0d00045c1420b0f92410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 124470431 1250 124469181 124469201
    0x914010e2403011706070216031103120c07030302010e010603080f181f022509020c15010f050907020604020109030213020c060403031b020a05031209030d020d0b090c1602060c01 78
    0x20400000100b080140c046005500c146080105e803d50b403030340c4408a9491300801c540c000e030319162160a00c00170300000a92a40301c17000038219503180406490b1140160711900a60382141e102c0441041016020f006001030000d0800003041011701d15201d218440c41000000017004100148910650341e20f1840d603007054101030105e06180d401401003078001e040714250180503202d0000140010003128403440c01441c011150040b0766850721050b040650461400d80c012070080050020f007900d91124030307a00030702c0b4040245030780c00c0c5040b051180d508006811902150041000c00c00940d07042200081203d42c182d50410070280200c000ca00240206100400e060040c5028001450707415000640080f91100382c058040c1002ca070140e9440c0381c1721a0080c03a07a00180300700303a5400c801100090740000a00c054a25000c000c0820904a0f8000200c081400e0344e59040324080381030000140e0f03841801d030316606151941c001120520412880da00078828100041e07c0c0c0c0c070300c00003900412600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 124471681 1250 124470431 124470499
    0xc1c05100501170601052511040501050f011e020703170a27050d0204110a1e020c010e102102030106020c060403020105120702030d020c03030103110301020307050711061e0a0914010e 80
    0x140c1149230502c0010500c06015203d6130900002055510b0702d041d0075515010140c440c54007811a68010f03424052a000340a002c0d802840c1c800400b081500030010341d150b10101b8416551010303c100a000011f5807600764070508007080203401340c0c2d40d40c103104009540c000c4901001020b51440050003412548090f141c04000210301d9000407900301d000580c0706191301c130b2481c540f135144150480e5640c0318000e0650002e51055a1101182803032340c1104005401d0380350080505a1182030000c01c48050542002c21540c0000104a02681800400154681160818601807858000034103601581100103200c01481c004103422030300030021280268070f00e2006545900440e1005c94894009204c1500c1c005003000361100c1c145010b108581c480c40058403035600380109a12103142c0900c07081d0b01260485810400364404010100c1884141c1034404006503a4003002c00e00180070010a501403880154030004004041c0c0e00240c00006c509025920310090701003900c8134600e4048146583d02c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 124472931 1250 124471681 124471747
    0x73606080c040e0607020d05030c0d02120702010e010c1403090c1002070819030507140703050a060603060c0c020108010b0d06090e0a051b0312030c1c0510050117060105 74
    0x4410110301d40c401150111020032007903041e104a603441d0381c0102c803500d0042c1c200b00034950f03269000703601440d007015078050302c1420720940400020480c3e10011418845401d05002c01c01210740c24040c94482d02d803201c0c000e005649041c0d001070100510450a8040c0c0c00011002400e01340007045074a80d2074000801c1c00d00b10105500000c1d403107500f640102003143c011b10100c17000b890b030f601c105612020741c03656541d0f00e4036265440d00d1000c844a04c92444aa02860f070002002c1102048040501d5000d03180c0080e485145141c004111040c200e040c4092082d868003000c0980c0c0c00840d41411152910110707a56444180a1400101025000411554542820f91300000000a80290151310036004c031081407154040c003000f810b080d50816645503000034014240d1400007c0a950071808039200a030030003080c40c200550040703400040140301c6a0315804c0100c3c0c17440c0032210b000102028248200c1e0310001d204a20265a40100800e042c0a0009503246081c2d02031480401400da0703092028031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 124474181 1250 124472931 124472939
    0x10501031b0f0b030606070201020307151401053c09090105180a080403030309020a032010030b01080406090203030c06010f0501080601210c0e1008011502073606 71
    0x240544401d00c088407405068000400c03030704200c40c218015148002001030031903880c00c0421481e540044402c03411030200f44246800212802d03541c01c0303205950000440c041c1c1c80005581d00c1c204050b404103120b004020f8400c11842000081c10007002d0800e0302811050061490290984071240c200941115982d0104011010103501c41c2d40030320011541070182540c034031a405da44218044019214003001c000800009010f944a01030040c0b0281041c804165a03031a9041600500c0c100c964401c0790400b0700113414a82a007400398034400904080214a40741c1300020b2108000601c0207107055034540c441415036400f0000d0714080c40103941100d12a6840d09826412202075200c1d5901003582032021a500c2d6004d8050004078101003440410000e008000e81800341829004460500c070003052101d6140d11400c84c0d2201284507911000d015500d08840c080c0445180c4541c001103401206e0140003920700c1c8903402c40c07115040c0c1000045010345501c1c10711000304280c0c50500d03492418030001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 124475431 1250 124474181 124474193
    0x3120f0a11280209100e0115031104080c03010f0501140603040203010902031c03060b0a0503160c060c0e03100204270e0a03091805090c060a0c021008041e05060f0a09020301050103 79
    0x1160140f0a50b07000180e40c4801301c0d200741c203074024040d00e010807034a03100510049074402d84c00c036a0004180f41c042001c0c600e186114003140d1154100304c81c2d98001e02010701841c1401d000340c0700101d0140c0d404011943c90800302a1542c4134003120948204d0002002c00c055503025049140c25540040c01d6503990100c50020f0041c0c01c1d1009410000709003040800102c12211006a8030042d0803a1a00340c0703540d50304811032841000c1031500b18103100444c1010f9020403842d1007152024906034071f41a00c001e001801301480d203040500c40c66440c80c01040b05001d03149003000035840003907100d03900c0c40402d071400036448003a01580010012504c1601d0001051590040f10701c8210340040d94000113040031811031f84180c0b54100d070700c299640e01004c4001c0c020f003400300040c140070700c2600d8109101d034070310342c0000c1e900d443c02400e64001449100910060001449100360100f0461003918445051543d0f800e44035800203264940c1c0d00460f200080d00301955421103103511f0f60080c020070083d03841303203492 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 124476681 1250 124475431 124475503
    0x70f0f050d05130c0801061a09041d03040807080c0312090102030d05090714060307081803040f03120e06040807060315091506030e071208091f0201020903120f0a11 72
    0x15100441014800982017006100385810b540b0034111804c80308117004d180c40c2c0f8075403094048540003a1f82e001d840c5025200c0502d004203090542c0c02966589181403207041c909041608841c99980041280cc411a0760000b040c0d86c07202a0309106649a89500005038203600a04011980303035800c2204100409001050400540d01c2843d4000340d845643c030180456400101d411001182038440491100b0b1800303407007981c1032214401100d241540303801e003001c01c41d0210742c400c950b503600c010340c1090080d81049000301300c0e620568460f4109460220700c569980c60a205000074155105000d03181c014101104201034070700d00e01f05001002c0385c2d15005103080041d118800000b45820312145800c080440d2140031245c07101c01d001c001d2201078a03100c103650301040e02c55510480c152a100b48104005000c0e003107801468000589509107201494107041201c0002c3c0f030034500822400e550721915005486182c41c049c03801007030b558045040f103450a100702e081c0315203002c1007040444a10682100b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 124477931 1250 124476681 124476683
    0x1306020c0109090212061201020c0111040e011d0103080c010209040c260910050a0212040506040c050a0f090203100302030f07061115040f05010b090f0f0f070f0f050d0513 75
    0xc40b4841e80e038804404040740540c00e085250124100c000c11a00d10700100b4071b40c0d145032513000051030500c04424236821556698a01000c660300410304010400074031048500401c80945042c000c4090001180254601400010300043d030109481c031081d042581038613401d110151003001050020742c0b02038800a4616a001c2c5500035503c003035880e16080c1c940450081d0f40d444000c01030020061410406818010300c440600c1d035003484007400e10b510071540b09010f6030141015010034205428004244565030300514087c42b03030b41d1820012000804030007011a140c01200503103a459803041d00c0e0344030703a60b43e102070b600d4403030101c1040d41c581c0c011841130110f8225031191240210044030142d02c405006000c0c0c040c40c0700c80b500040114090100004025116000008004100d440007030035510b000d40340607064511010030492040004100c1030341040306844da0b444145801c002c010104844413491508120820011210690080040d5044d04410001c01d03c520700d40550050080401904 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 124479181 1250 124477931 124477937
    0x90c060724020c01240b0c01020d0f020a08010e10030303050402011806020105091b030d05070c09020706060608090610060509270703060b040609090902120616020c0a05010207050904081306020c01 86
    0xc0d801c00042805c4520030810300355003003811300c40c0e442c01215149070703000404120001d5400b040340028000080c482c031010025440340068851686410041005405070011001c40d405200bd000198105800200480c2e901d03140c0414148d44a20049500343d030019903161020501c20310108040c2d40642007144a0381c20a030890310344007601c030f83c0f0241d0f1500b030810702078054002c03861002031544500f004200071801340728041c10301540c0b00701c0c2c441240d11020003594019681c01081c410207a00000450304444104001c0c801800d11207607465801700780d07100311424484001401c02007038840041c02c1034203410b40c9450351000c0d2403040085254007011200d65002038a070a402082d01104401518103450042e0382c0c0c14911810640404010500741c00180d92004c9404100c1c20100001c118461140da1104000a00c040704460080d1510703d100c81e50601c1450250030521050b64005150310484030111a034441c030703032a5400d02c0702c03851140710341e14080032034642d41c04902075400003001d101c41102a1303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 124480431 1250 124479181 124479191
    0x1103101b020316060209030f300306030d0c0204110406030e0d090e0a0203070c020a090f0b040501120206090a05041407020d051602041d06070e09090105090c060724020c01 75
    0x214100e071030307200f1034040440b083c05a1108901003a1254081d000c4003002070101d501001010300300314a0289101140c0c1914500c03840616010200d01144000c0400b060390028114141400002c0c1c0742ca800311108420000100403e4040d559680c128040003151043c178070780c0c0d4640384c010080180c429000c81c400300c0d124060ba01c0740300d6807140106104880c040c54468a59460703140b40d12010f5400038240f5410048401039900c0580c0c1c818146000a0150b401c00042a4800008070019920031041041c070592400004009444020f50410034969046030f20682c0c4003002d000007030320110309800141c0c2061500b142d1344642c00d001203a06000c0c0340701c0c1d02110903103078003c42e049503d40301d40e101107078000d01c0c2150781c0401420580c1102e080c0d00c1084505030300d01d244802d212460120100e41220004180c28a6400103003418050182c12001b40c40080c001c80c40c04901d826507620003a0354a40c051107000444205008401c0c208c01c9840030f201e0707801c1082498500303080010790020b00f180707405940780c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 124481681 1250 124480431 124480481
    0x1701080102041a19080903091509010e0f01020d0c060e030c03070b100614071a0a0501090b0906100e120607050703031406091f090524011701030f110310 67
    0x2180646008507165104c070152459903900888002401400301903aa02c41400352030383c0c035600c0502d40070781080341201c1c0342d807910300803000100480a00700c080d070b00403c02c0210039522039038041007200c1d0f85100c0d070070300c0740390300031070f031920340003d01000501040d140070100762078842400100041207214000d50307640c0026210341800c00b6901c20035118080100b41c942a51450038008040034200340f5004861402000720100c1000e941c4010869072500581d0b990401846107038401d10030044500d5007961400310a1801c41d000c00c0c582c00b80c908034007043c44080443d461503686d600300c410381c0700340d544802d076130040c1400074029105400200b812404a03040500146180c0844201b1503c03c2000600f5107165481d40c01a0358420300c01100000580c044045011138055114010f0034011860300004c03254006001003a800210b940d951814100104140324401100c0c0c00e81d0388030305480c0c200d52540c10403130140c500481c10b04019100e40303405010300c6003440390368002e650140410750204000d81d5010211 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 124482931 1250 124481681 124481729
    0x1051e01140f04020c0601030201120218130608100504020a0e040209040b04020a080f07081002040515090102010204180b04050a0606170a06030507030b07030e0703020604050f01170108010204 84
    0x14011490051042500410010003100d241544001000c0c10030014101d03520b01043c10b036889000c4600383c80d80400300410440d64804a103180341209000f0450918444103121584440340f500030074420141154034211202e003517440b1600602005080755808101d8468500183c813045074140d200b54070295000803a4000c0c03140207440b4982c0107004252030741c0d640e80c544850b06005001030381c0103080b848011500709001c001c8032154034560f00c010040107240120b658030781000340c002034041c0350050104010320384401c403440d0081c0a605100a456140f1000101d009004640c0100d801304402c80d1601d0349100154455101d2620540d0144120f039103849922060721050f2142e030b0f000942a004036003200d07134089844c0d50032500840c0301040c8240c0c6c03130b02e410340b51170120381041d1043d02c004821b001015405115401c00d52401c00c001d80219440e5400055041c0100e20429000321070141c2080310580c841c440b4614404110181d4007010b50310303808828000d4000c1d019aa0b00102c00101c1e5081e030f022 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 124484181 1250 124482931 124482961
    0x3031902010b0f01080f15090a1a030a030c171c0204030210020601050109140a05030312071704020109090c030e0604080c28020630070e01080f04060b010e030a0807050105 75
    0x301070311501d100c0e41b40d68050802141d030003032034000b0701c14990030704d01015640d6030280c50050b40d4100011403450410110301450f1740076102030034401e51184000d100002d03000003500c10303c0f039000080081803062000d0300d074004e8440c8844811503410b9103045401c6d000c0666000c0c0080e28000d40300c41070004407941007603030340e541c003801203c1c0418041801003220420010a03850780c01c1e809412004080c1c4c0d00c101103442c0d034000341d400d41d0281c01c2d071008004a01d0345c441d10f03016500305000360200b19030410303030000b03040f0f0715040c0a070004c0301da1a6104a070460340260820001c6483e940300300c400038502820038480503082104440c140d27002c0c81c0441e4582010f014800c0703840780403008000c00902169800c011060344000545010001960aa50201000b000c01c155002200d01000e0220346000080280415802202541841050420701c071021304e030700b2980c0b1350083e80171000003225100100140c40ca142e41c90005541441003501641c1044500703000b0f085158070030002848151940e0a80040c008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 124485431 1250 124484181 124484209
    0x301032118050f1203030109091103030f1608040e070903030909060b090d02150f04050f04050103151a060c010e0d090b191b0501150801020309030703180503031902010b 74
    0x8099101c00b44007925280c090020b03000c8000b0300c0040b840310130351015411a003099000c10001980e9507036060600c06214880c203520700c4102d01561070100350400714a943c0c000c0e52400036003240c0c00d940e0f4404022108040305e000d00018506a206490801801414290280811000202180c00c0043d4001003800751406aa260b1014282007269610a00480144070b5000740d83c00040320f0701c215150890b02c8014071014200081065649003400c0c18005200c0045074298095480e150040004c120700c0407100c184140c07003840210b2988007000394510380c081c6d814102644002c0010f401104d6180541c080c05000c0c80c41003d80368901050042551404010d1007142c2c44000100305460300c2c040700007030520b003501086c1003a1180d2800c02900b203e40c14542031046803e03a648030112408490f0000c1c03400e00a100308402581707145440081181c490042c2c4d10010300f88030b80c11003500c0c80402510034030303005031001404a9460315070702112a03207051418040c103405035180a0758242981407001a85c9120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 124486681 1250 124485431 124485467
    0xd1104060917101103041202030a050a0c170d0b0405011401091703040e0406092616030302071202060610050405060417030702040603080331030e130203010321 70
    0x51490059080020210620804154003c40354075208070400740c8030340c80d000100c810042d40c40349401e24254550140c1d0b4500482958401d014001107603a000e0100e43c4582c0841c50b01800c031140910b085440e00e03a40d8419002018008120002800b10380e5000179503515044a0511041e66a0a1501d5144002140181c00903444442c10301003d0004040c00415110781400c80c0d1030586d8450002034450f000b500c04445654440c0070a209000809030108003d807492140707502034a810041140703a91007143e03a151111458607503c034080c540a5419500c0702c50f04141b5030300002c1c40c1008002e444203002c0f14002c1c4206440042d465980d486501500d0541e440640700a00d0038ac100340c0015101e4209080c0b078000e600c02001014016101d60040310003c6200d02d02d042d27142d081000f0344039611001e80034440691000c5144d00707241c480800d1031a210240d058180b84d5821003c0001041c850703d42100000b124500000000003000103866074011402c450701242c42d41414a1401101c402e02040108460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 124487931 1250 124486681 124486697
    0x2030a1a09060904411501170109240c11150a18030f020105010b07051e071e0603060611060a0522031206091103041e0c0b0d110406 58
    0x103908060003025003060144130f9109002800c00c0b4100c00c2eaa40c400c000500d600740100300307030b01721400101c0c1d44460080e24030003400c030524901c13031507a604482c14810130107802c1d44100c140f0203400d000e520111009400c4810406091006e08c02c00380b03481c085844103514689000c2c41c0c02c4490b40306400c000504040718014040a49405611840c0c514000c0d181c20800350b0340d81c0078030202c0408000c1030714050b0b101e501d419440c110010f80107400c4500581c490b00c00d4110410805000a801140350050788050184c201640052001142d2030041143c020349aa140020182803065880300e0081089030441c0c3c1e014840d02d074582e001240c4420032041e0b02c028075845180498420340550304080c1d401114500040c2034808000c200c03603406005d84506501007034042d1000301d40b4001502812019040b401c034117201d150000a0707200914400140080c1000300b208000c80011200c7c079801103074054004c20552030715a102d41c2d82001950107045040c1c0382502e0141c44407907810204095908490071510f810072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 124489181 1250 124487931 124487941
    0x60102030703120605060309010c0e030105010810090602130b0418090308190f0203191401120b07030b0315060f240a050f04080d0f0801081b0d060c0302030a1a09 71
    0x70320343c070681c10800318541c54100c04a110749800010390b1080d01030400200e0758503003002c405002c0c40c4114a406010b81d04140060100c0362001030394420400c04a40c000460b0251805d05800a00420700c103101140f41d201000101092403030050029078110721f03100c00300d0282420a06d01100c0710003034020003040b10140022003842100ca808034218002c2507011a031210303240d40c3c0d0700403684100c41100d030855040c042c4010f06c0c022442010100c808031140c0500310b5051840803460101911001045401d52304000380c100340c460b4000c800c0703030000601180c026400160400009510031148075000380d200e001e50010a141c0040c0070f492100d0244520004440c1e1721b0b01e01e9a10f07522255510082c42010082c05407980c440b24010002800b85001928149181c814000e09144019542c40104150b450061207441400b081e404030141801c046580d403d030203000403c00701098603070050103080c60002d42e05080c980540045101ea10411000c002d1501c0313260003890b01e003c20840701354102d1300c0380001038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 124490431 1250 124489181 124489187
    0x301320d1b03060509010c03020403151805060f011a2a07050a0305010207060c0f090905070c0506040b0f13080f09060403080301030302030403150504030c020906040213062303060102030703 83
    0x1080c081c000c64441248601d419140015055940e000319400c0b03075a0b404008440310203202c0c02002c0005480c09614062a50302e07101c0110581c55031402e42103658400c06a5110690000c0c519465440b80a5a1081c50401d65003035117044240300d0b40c8807007078407060003420400c48541116002d41e00da501c1c1c8c02500020038014041e41c0158101c06030740e88504031002c103a690b1100c0405000f1403180d80050307900c1c41680341140a540000e46284180000c2040003180305810011403c19507600220003d0715544111048402e51401200500b003400350a05110030f02c41c0f0880124400d20500c60390010075203481852002c00c41d880c80020300060410700c0354450341c6941d24010014120010204e60400340c4036201c44d80d03103501c20790048026130b000003410020030101d0341c1000c0b014a1565070810035031600b524003030200c00d100000288980c4194002654654465060310194000401c950b100d40d0340750440980074110048161044414541c0320745140c0c402c3d041264460001a400307542008165a816 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 124491681 1250 124490431 124490449
    0xe0a1203030c0e0415080c0f0607060203092803030b190e090307080406120507051201050105090d05030a030b010e0603072c1003060501080906060307060509060903070308030132 78
    0x1030001c01840c0036000c07070b41da61580100d5520454402241c10240d1070704031034a07e0080c1524141c4d02841806804c003c0a03541c3c4016a5034860b01b042015a41c0d5544502003802c2c4031280052001000e40d607a440c2450110314001c10059512a031001c0180700e1200c0200401183c1d0540700209421060720180b2014a07000c0c15a80c001e030400d002c0380c1c00c000c056601c80040390050307040000041e1246402040389a4140170b000d810981e9824420301d001c2c00800031502d07820701402424140540040e51401039111406400c0e6015005029a900c514980d00001c1c00b0300880c140490000e03200300b8106201e40b800c08102da000f4200c5888100040c0c64034020284400207803244450b60100070074940b0f010384c907101401e04959005640000d00d142c14500058001a00030704a00c485a000804000701c0c2c1c0c0700060000e054503403900305280c5070380d0f401c5c00140c40d07031041c040d40903018007038094001700700141e840c0614144d829200c80c00070840980c50203a0349000c1c0103801c2c03030304003108503034801614208402c003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 124492931 1250 124491681 124491701
    0x503100506130b150a030c0f030605010c030c02030c0d050607090806090307170706061e060e030d2f0d170411090406240f050307030506010b09040914010504030e0a120303 75
    0x10b51309a4102c448040b90503402c42c007885008070b6151402070308110381c00340007440781200c2c604007000101d003881c00007000f02200c19401418082000721540079594100315200c1c04050080020003070401501c1d104e91114819500340000c509244004561400d0200306079108188400056082204507150680103101c2081508460034080090a003c40d44901800c00604081104496070204202c1040c221012552220041019407088100d80d50b8022451001e82c04151400c0c08040f07540c0050b41741c2584180100325034003a21030100a00d0700c034010607259648421903c503c0b80d4400020102010030707008030b40c024802c0c0b11001c042030341840e1100c1da0540060007031200081c240003000b50101c01d0b0b03000310111310804c540454200240c0c02800c19036005800150050301c070305172565079200d98134141030003515400c207004500ca032a141c0380c0758041020150095900000f0901d100107290091605a07030503030014550b07200b02552030a014035003408071004084504024002c586040303008040c0c25031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 124494181 1250 124492931 124492939
    0x40302011d210a1106070803070e03160303030504050105070816110c1c050c1f03050a0b06041d1312030c0c0615050111010605030a080708090d03030203010503100506130b 75
    0xe602c8450002000442c200c04522070020126064103040c04112044071540c4039210300001c000000c0050881d070240c03a00320f540740c01c04400c01c2400b00000390800c014407600011942c800c050020a05625400090091340610000c200503200e6810490750035100b1a005188030180c0510650382600c103500d84540032605100b925909810350000500c8a20b0501c1c0e074110751580c803c40242401020b018800c0c09a00840d00f2001c1011031200503d81f403202c000e29407042c1030703070b6900140f28000380f40c200c0b034403201009009680e210f484026039000900035403200058102100c00240c01900f460704204120b580040c04401d00700c0111100710040c008601c11141000740c0d0040d02000119507000b62040201c501c0c40c075500f010f00300340004010250070410158680e05200080100d40c0300418a41c03d4030f034104c103e080e9209170506000503030b0310840e18401d410440710780200080c19419401703103050315011011744200910030200141508c0c000d50329187d110041d0440940122266030002401102c058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 124495431 1250 124494181 124494199
    0x113309031c0609060b070b0702060601020c040905030c030706020c06070207050901090906020d0614030d0203161704081b0a080105150103020d0f020d02030f06100c0305070c09020c070302090c040302011d 89
    0x20f40c003000b600c0b9554000104040041241002c02c02030054680c1d0260142c401813196140600c0001e5a51003c85422400b555950402909001080c0110381c588030170314044a60301c90080c500f40d4020352098061914074041c050105208602c007103030200c11554020500c84090f428060550014101c88404480c1d03e035003080780920542e0035002d47c0c00106403407200e813140c0c081d600090505220748540e00341c00f113400030050001111907610754030381e40c00e8101c2e6504407d001314461b0034100340f00703d400c400c1092090f1140542e4030042c000310364071800c000b42d4028090681d10262207090322030684180391300e03034260507548046501c2640900500300c0d45134000700740e405054101800300c2c0c0c45603c0e9a0401500041000803400c17003140041d81196007690700c0c2041c4450042c00510401c2c020f68002e0411200141030410b12010000b020041c04191204540d6040f08004c01030340c85a881c401280a111107200080c86c00003542c040d64112501a1203421140250440310407190300e50b8403030316902c14411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 124496681 1250 124495431 124495439
    0x60919031d0a15080406050604140f0406090219050a090905031902010b04020408061e06030a110103060e0108030d1103061c08040305060c180402160204050403113309031c06 76
    0x80d000e0040c2c80f4040b034548920a007001d003480070a41e44000c003040d0041d41846402405a541c0001855010003800b8048030075880300e103088c00180000b402c01a50000310341d0032800315100d0180140040301e10442c0c4200e50169201075003000c0c0c0e4010000035105030018424030000c29800d04550640b5000c0e880001080d442d95000078089811030380090f11a94003400420200b940d081c01044072446581c1035100c414940440080e584074841f010081c0004000051244940d01a8101c0c00160995658400031581c603803200c246e690300204841e0074480e0400030040203503c61402141c0c0100000740088502c401c20413800e010642d495036044031040c00c108400004541d09214190240780c000011903074500742800c40d01c20b4014210000d5102d10701c10000704884003182d0802c0205240d040d10082059552400c081c1d842c048003031043c0010340103000d20b03943c1e2401e1140c458284854050310208101810f11600c4c181407070708403004142c580c401c0003007091519400c811a40c070390100e0300000c680d039078507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 124497931 1250 124496681 124496699
    0xb061801091a0a0306120c0308160b07050304050606040c0f180f0f0315141302061207051b01151205160801020d0b030a2102030c01020c060919031d0a 66
    0x4408080142c4030000310300d02d0010b941c1400f50200801040c1010481510b0f10b444a440711107044c44001c144c640d0000d40f407201420407090142c5020780140005829141410025200d036100320350407a92801420001801483d0a01c5a8040104141d48070784103288505000d60b290311814518183d4103c04042c000740c18079802c190301c0d01401c0c1c6d01c0c6134003003544e1440c076155218101400174080e100d4141840ca03038145d68420f407850340c0201382598200344075601d800800c05921401000d0030380c02c0c81000c104001c03650400b000b003840400c5401c4030205514221070880c01c036075141882c0540941c0f41842085110801d912000c2011b0003001030300c1d80c003c44910820101c4010740d00800d0340e0b940129498070a004a4424050342c2841900070b054022000d070f9907060038010389043c00c0252042e0f1540ca065042c400c000f0781e0106507102c0c2c0210740e01e01c0981883d59840c03000316030301c10080c8074480303120080c4045040e41640b2554181c0f21440340e40700880740c40b0000d4502e0200190401020300c000110005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 124499181 1250 124497931 124497959
    0x1a13080403060617030712030915051006120b0303072009070206010504060f050f12032502030c03030a021203040218041b06050903031b031e04080706030b06180109 72
    0x8814040001c4840c13900102c062151904680c10400307400501c00800424071460381c9100c0305101e0300e80080e5071001440c10007900d4910540001d213042ca01000c00000c281003a021a040d03440035103601d0300880c0688a000191014120150380540051043d003001480705260310840d807100e80000d040c0304101d030000c10342080e1304480000c016886080100036508003031003004090040b00b52612038280c20000461511002941c0c0103001c1d011100302e040b500e02050081e42c0c2c3e04500ca40d01d04c06407107120f00f806442020350101c20ba209000d844256850762800008071500010a40c0103003017081c4204428107442c0d08000c1050341c020128400c5016500d085c111201d01c160b01c034503010269032106c181c1c605600310080e00840c0078440104403600307407660008159140361000703d2004076030368a40e08000b81940250841076580d1000d520001103600d00c00005001900c600c5003c03104402d0b0f540e81c0c200c054400c60001c15800c5102001150740f01b8010940c64400d4003018181850180d56581c44404004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 124500431 1250 124499181 124499183
    0x70308060402041d01143109060501080703060b06030615030a0608030307260103171e0a02010b100513091a0904210c150c090f0308030103030f03091a13080403 70
    0x8032900520000b081c0d8005014044c605440c42c16036035000300307c0c1140b01c0b00b50320000f0185402000528002244540200e030800b41c0c002c03403e10031035940d90318840e42c504403808110b482905000d01000d0904002e0252445008010500d6014031207998404d419640007405080304207444c0e04000ca40c3c4031b4108010f5005104513075800d00c2c0380198400c82d10050790b0802c54180341d501e005c80100082801c11011451140620b40c1840d45d52074176107440403480c1c808a004403406070300401e5086c0b00a8040d40f2916070340c1403c6d6014484008029012070f264410b0810700c0d56071a4200c8414001d02442d50b1140202d40b1003040701d104211943c07000a030703035a10304031070444a100c03e8107460107000d0a41c01c44480c0c0010a401c04c111700107140d80d5045215803914591844003070360f41c00212003592160a8242c0201407001c8400b540035148c0c140200f031548240003e0700031864014034101e010340310b03100301c10220360001c07010781600d45081850302e40da03030000d0103401c040e50142d694400400c00000041c0015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 124501681 1250 124500431 124500479
    0x50409050c030106080609040201020a020402031801060312080903040e0a0f0e0a0c0f050a1d153318010f0e1c0605091f05100b0708030906061507030806040204 70
    0x780d0325140d4010885c00006104a01583c40d036801d110040c1d0300000c8201d8055411a000358882e0390302d1141c0c09103800044104061907081c08000070512050b07402080d0039140d00d0b1340e128800c1d940c429140c2c1d602e02c10307031040c1114101020300140007a81264070210040808003000f00b0004d01a00440e860185040d0050382c145012050401c05484c4500c2c0e448028402030300c1c404111840c1c401030b904604110800b0100c840e041d0400200e00201144d10321a182000500b0043c1d81c002440b40e040811002c0d41c2d54051021141c0e040e146101c8604043d0b81400c0907070003211010740040c00c01100d02e64121406041801012400e04034641e071180141c8184002d0220610310341456800c3c5230041d00c1c1c020304892016001810014115640c03030f043c0c8003002141200c045401d0700c0f400d850550495181d07110704c505050101d621700c03c20800d00021801128000c007103130295200e110800941483d1900043c440000812000c400240217250307090348080028801030520b65101c080c0001c0d034820b01144446 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 124502931 1250 124501681 124501687
    0x21908040b030c1305010e01020a03081308071b0914040201110c04020c0a050709020708030105101202070326060306220203100e10020903100207020301020702030f0f0c0103050f010605030601050409050c 89
    0x81103c0c0b01030304401413400f442e21f0183d14500c000040c0d165040c41401500300a92180090400500e44001c0da080390b03488165696a0302d00c50500c1200d1810308203454502800072070001481446600507102c00300da216808030b4468840e98015030341c020071005554910b01071041d5242c4582d17611303c003420188001e0000752218401510305603003000c050b500980d003024814490b610105100c03074103484c156001600c030b009180d0000d2000352240c088140d0780c000d94500006020f800c055010312001c00903a03014440a0507602d010701c0c044c10308001108c2254142e07115000141120303060002c420304402180c842c000c4c00480e107402080c1402c1e1244040d100140d2541c1c0003000c41c80003000014018030f0710740421824207409400290300d40c0065000c4010081d00441c2c90f1095550030b41c100d070b05a81c2d00400306c1d40100c5038400c456484180d000540d14543c061321801c40e00650182c068203100e03628540382072a4903800d041054810b41c1014005a04100060001007503001251145a0007011a0b86c000380c1c0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 124504181 1250 124502931 124502947
    0x20705031e0d050c030c0304060512010510021b01031d0307120f050906030736060c0302070e040c0e040302030d0f1107020d110301090b06030c060a021908040b030c 72
    0x714200315154041c901c1003056003254407448010502012035a1540750041c0d54114405066195014254503d4000d000018000540d65040402404030b507410201092080ea6110200640904006003076800740c0c0108010b0381122105d1000403903014014100010b080590b81141c0e140154048440100c99000103118814003d03940120460b00b00c852400d0000e164803900010010701035192a240030328008800700d8105030280f00d1501c512000d55001050488000d41c0803041c00824000c024450b4a11500208516120310341c20340b02c49415400030800907141411041c036540d0010f0098410010400001c541240001039080c00759029500030b644a03100c3d8011181210b146241c01001071389400c0c2104030006d040020f4403009901201c005a44003800d05100b02481d05901000e90725510b015900e008105030780140f01d004074030039400c440c0000426424400a80b040041e20805030340301510040503030320740b10215680c0c82e208555041c245940c444801d0403541065414034810030020904203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 124505431 1250 124504181 124504183
    0x6050603130c0f0303210e0d030c120f0f050c0a0c0b0907051017010f030b070f02010e100606090f0308091c060f0b01170c03070e0a0509040308040b0c0414040e10050702070503 77
    0x205085100e030002c20207c0a6106c1466850110459540c2070503129040340101d240544280e000e4009140e4041c006011007041050041800b0341d281c1240c68502400310b40c2e0610000c058440100c0d0640701e103800d50450740c42d0f0510750200140700c180544076884000c2030f20b80320642d15520000c069260110360402600208242d103c1c160460500c1f040707001070400100d1515030096400508900300b20204c06000b1780224050810b00b41008168401c3c0800850210310603030001e4112500c540d140815076443d080342d40507200c079910000c0c2c14400b05005101d15032401da034480309503800719440113001407440d90380d040694250000300030780342da51600098503558001c1c85c4c0011420710b0014400162514805841c0c031804050544020005c500c1d0b100a01c648846800e040501001131070315038503160503c1c004160789001c03141180e40400d0030010030000c60100040e181a1800080303d190002c031150103100c000d0541c1c006030a0603110740710060503455404d20410b809500c1941c00b8011542c1004281 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 124506681 1250 124505431 124505477
    0x40510030203100e0f181c0816110a030302091306080c090708040201080a1a12100c020d0527040f0b03010b0f090402060a0c080412120306050603130c0f0303 69
    0x4100c654044e0b00030058040300021050340e0080e00707015090504200c0110042c82c01c5810005540703004442420240f1444e0040f030030601c5501742c1c07051001c1c44100848110b030005800c60078003805034406007d0310b000a0094015044806000d000c801c50405199054800d4810aa0007140c00f0707000340303295420718100400661b5101c8040d00302a191810a540000c0c84060300415080f5100c1e43d03640016101040801400e10450004200340404e100c60b0311900c3d2039000e04606400e495262520b06001c0358008199003018140b285c450345d0500c0800040351410b0101d440000d00b440240c10821200d9507600c0c0706400404c058a0b07000202c00c101e400c180350031070310b50451151103082d120f160305038181d1760503440315409a4181c58854813601d101ca02603900445c02d0f4801040c0034008500401e2401703814083c02c0301d0501558002426101a0340144c0132149a0300940c1d1b0031410400000348942c0e40e907080703d0b070a544520b0b400700d502659404c121840b488540c104900042001d01c00045145903080a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 124507931 1250 124506681 124506689
    0xc030501050f0c0313050304050d0302010204080f0d0801030305030601020a06020703030509210d0b03100612050d03150909020102100c17100518041e2306010807090b0604051003020310 81
    0x1603800d40341083c1c08080140c0c0001445800d1040e98104d1500170000b0900548009140180040c46001c40310314019010390802d0182a1192260684100c08440005100d0b0900072030b6071107520242e400d5031000c840c04e41c4010215030540c402c2d00412030000700c041c8001e00ea114000c0c0c0e00011141812007407030303003000400010914016840e00b95451450072643c22030740115400c0c0d07000250f100b2504042400d006c245448007060600d40700d0005240c0480703109218480b449602a108100178170f60040e0b00721002441048004102081c084c000762807680d1044074942d005004854048070039809035400d95000700030740c0c400182100707d6201e00d40003030f114127a040ba28501c000d1126508080c04207070751a00c00881400551840d001050521800c4114112643c01d102520b507005a0036003800da107180f11921140504a054400c0b52104010118099059490030307000b0304101480e190f080c03006041d00c5610035078400005c1000160f5569002904444000142c0340962030307244c0301040c0721901800e540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 124509181 1250 124507931 124507951
    0x30903150c141e0309071d0c0304020906030f0d0302090a08010e1228030504021c03170603120c0703020f061306050d0207200301050703060e0115050c0a0c03050105 72
    0x206040d9140c1c0c00a0303820401e05032091030281c450803001c40800082e90039110f030350141d03200001802031141001c1241d00698036111508511600c2000540342c4a140c1143c20b903c400c8020300105005141c810392050f00580028200c40207840070b400054205a0f4a500c0368000c26400154102a0700303000d910301c0c0003001c07900002c000c1c1c151105456900e0300c0c6900e070b002011000c0040c40300103400c1d0301d040c40c192800010000070f04995031001e01030300805c0c00340c4084c0d2203540c00e40b20303940c0024004400c0909003a41350b070b10411400400080c200c0c1ca01c2c0040d01e0300b07904d8010802221007c0f1003003005410240d02040090124500d035005012401503003800c0c1a00a1804100c030041c034110b120000c40c100c1e2064a8000e5490540f00c4010009004400c0001d101e40f91800f040c004807070301d40c0504030044004a00030000703030708c5291054084030414401c0c5802c0201c2e44c1c004104012400b06140400712150900d945001450420300341000c4d030041b01242d0000100c0300074010300009102c3c40d035111003192 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 124510431 1250 124509181 124509191
    0x308010803070b0c030703090c0306060503071703120a0e0a1a060105070308071101090b0a09021302040f0b090f0301051017030f03011707030b0a0905010506040216030804050c06040303090315 84
    0x40c8560724800c8000740300e18078141300000482d025902c681c0c4015081d82d005103807020015224a081000340281d482030074468804d4080c08203034071345c038410700c0c03041000e180005510b0110704804190000354010502c8100e070380d940444016420040c81107030800c0344260031401c0d26001d0305072012681e070030140ca0b00e0b0420500344501c000080d00701d115a42c0126246c01c05c2411010309101181c05040d1007003000304448103c0c014001d00805581042c0c8107a84226006e00ba50400e290b80f40080340110b10820100c424444030800000c00024010b050000d405400030700c03d9103060002c2400c2d11429195201c0301180d003081003080c5903503210f4034868101000e010354640a03103c4180540d81c08107014041d54811100d04071420b1140403c2580025641700e00c1c080810728010301e5a000411120703106440039400e140c00030303030706103000c4c401c331003e10b110107643c81d04200d0162411070710b082000b441107a01c3d00c00c0080c149450703a0341030040d2000350320035500c64400a00310f1410099164850a80e001094241 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 124511681 1250 124510431 124510433
    0x9022103070203070b0a050306010c110d030806091302030304050f0a0b0408070302120106050901031202010914070501090f050d080309150a09110108040b04031d06031816060516020a0b03070309030801080307 91
    0x1f01d82104e410810034078056010080a050206086c05400c4109602c403800c81039207000c040d003260505100e030310101d40b130000558504c40007420035914010029071503007003040280110301d41640035010007130000d0071a0610365103e14030300090340d1290b000400c1d10b60100408108602c0c00350b0211103140a14002446054580741c0400c3c180712043c08001c21a45044901c088660f200350f00408009821041071041256440e00e281d884840d640a224005001b0f11000703d400e00c4c808a01d03104540e4060507416000c00641c039100429080500010360500611201e886080040c22026005050901000800405528004400c40c03084000c0505010300b0004000100310304d259038a0380160581000b103900c0414180c000d0301e4918148510f5404070000c003d02450f089048910301400c07143c1d2040f248416042c02d1801d982601c103120f22800030b68200320300054594818404d80304548047c0141c1d52a9444400f4003403a170b0000c95000001954071110307030f42450780c0656098014458103002d1441d219813 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 124512931 1250 124511681 124511687
    0x70209180604060c120c090806070201110d0c031815050105040c0c0222090c0305010c0212190513090906110a020a11030a0b090f0f060709060309022103070203070b0a 73
    0x4014409030840b80d81d0b0481042c014085c10800c01681c5da1800e080100c01081d0a01521034810350003a044140b181c5000605031900510507812079030711148006040099400601c40a056000603500c10036071101190050a0340d000340c013921075440703514800d0b4402c00118810f01200c00c142d002c588101d040c804905845c2d5004010341070030310740581d0b202d4140066103000141c202181c050854144c0d1403e1043c0c003e2040054107032040e40c1c41b41e07000b072211143d039060883e03440a6058100e040d00c0000c000d81d60f4401013085100e000c0801608000e41080484004060758840d1948000340300780c2c07500c469400300b205510501072104002041981450b0410394001c4d520101c02c0d40c028585014260406000d95040003a105016070000900388240f40180d0300980380c0d00214030f50b24152080400c90120031801003001c074480c03c40c640c1c0d011001d510f4420114040c00680f0310507600030100721400308018041811003071a4a0001c070007565104070501c145490002641e001082408041c40007254403a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 124514181 1250 124512931 124512943
    0x11040f0302010c061d030c01050a0c091214010c0f0e01170c18030319020706020a0209060d061415010f0206010b0403060b1f0903030e090f040308130f050307020918 72
    0x14081c038083e409a441440c000b0020024102c007401c1d011402c41c41400207490000050000e501c0c004c0080c0050381b104d07962141602e101030040c2000c10301900301801160400e0b030200311210300410003540a10101d50a0700e0031180060315841c002080c480d107000382c40d0340085090a5410b003c1c80c00070240a0700510b10840500090034845180000141040707918079098600010610005c003600e070340700140c14a00e0108a420800c1c40003502400c0c1000862078004a482c42c810b41d0042c0400340d1544d10002048000c0712030341404c442c3c40e680c0308400b41d05e001680301524070030960031b41030385449041040090880b2040c41800f10440d80700d880140400300d00741c07090390112944641c000c11014002d000184030a07128040c80f20791140d81e194a03444e00340c7c0c40141c100c1100e00a8880c90420f030303550b03010303c003540408030380700080302901301d001c14000380c40340b030103075a00c4254102d800055442584e1160002c65a00c3c80c16102940041411015172800c0b82c00c1c0c0e078000343c0083d541030060700d02c58031a07902c1e50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 124515431 1250 124514181 124514183
    0x50a021f08060405090708011104170609030f09060c010c022b09050616020d080702100f02060f09340801050105130e01020d0203010b120f0c090415050a030b0a11040f03 74
    0x1034544020515000c403c000503800340030701800900849c082e41b851301c49550424401c10000400210010581e85004160680281c22400141d890200c46c0da9103a04503034404002c90360040c40400041982d01401e20070381d868900a80e002d010b640c4400ea03100300540d10300c801e0300007209004014a1508a800c2440d0408494054076215141e007100d2100901e00740c103c0c54060f4000121040b4141080400300041c00c40320320894410081d5170104038100d0b5911000074900c40903030300c110302194408001d401604c2e8882c0300e0004660103200c004440c0012414880b844c043d0820341100c03160840b0003c00d600300045d0036050001c200541c907040018060301e0701d0b1b83d030801420b6a5203841ca88440d0080d011240c500101c000190740d01d5940301602c60856000c070440804000c103074800b0070082400000101d0041c4661a85582031100c424204002810310946c0b80142c46018000050750751202005070b00110301030301c0c809605181c4140c400d07040d100034182c042d00c0d48904000500600c0610900c0c2000d0b2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 124516681 1250 124515431 124515439
    0xa0b0a02010e010b040e4c0c03090b010e19060816080c10050a050c0703030c060b030a0308061210050a0203071e020706030c0e040f0501080d08010e060402160807050a021f0806 77
    0x81c0c2d441004074102c04004d005070b1fa14040c03002d5209100081d88071813044d07003020840c0c100070390b0410314022001c035403e10708010704045910b40104a04105200b81381d81052610015260002c144600c1390704540c100d0f8032000043c0c11592171900d80c1c440101d0101d00525180d0007610711703034514200003048060700c15910302c2401000302c1d00e0501c4170303c03680c1960350150403c0212142c00e40c80303050141c18010882003c03100745082289185041c10301140c0d030b01c00c80d82c0c15141e079000c0380c031207a08004410415241940c0e5030300c2444200b500300800c03405924002e106001005a4038281030000802028203a0300c55180e05a0495030804803d034000381000803502e00d46000100700680810440d51318038680c03c40740e4061b040400d50000800d00d641301c14120b6404204450740080103180541c0c10540900c220352408a07480d00040b500cac1001c2e00140340314007814108059104240d943c0100c1604021415645544500201c0e4118140740d0400040340c4809100c05814914510700104882e900030b2080e401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 124517931 1250 124516681 124516723
    0x70210150f0f0e0106110f010501030302031c0c0c03050a02100f0209030d0504270605030607030c020c03010e070e040f08070b0a0513021c051908090a05040207080d0207020a0b0a02010e010b040e 85
    0x6d14002e00c285408151020024811940d490800a59942110180803121110990a00382d90041486440500b28040d08d51103126807a07a20b0175140740d08001e0504065001d2115262147c1e81e480c4105603d5101801005849200304410f16240c80d100c040d0b01e0061000420080c4a1003000022920081e015110200d8ac085245280c0c40058007844c3e00c0300fa054030a0505000c1c040303405804c20700e1408403d50881b181e00301c01070105400c1c1e80517032025001c00d0700056418000c070100300840c2030380316009030343d0b0f00800c403510303581c441065002c03201c1503a0302d50f0000240000900c4601556400540700300315080822910f0b00060307081d01108040c2c0c0c0c03030b09030300701020010007505000d60307035600e00c080034100c00200c5141020419548a101401d04c5400700845c0850b403807600b803090b13601241c3c0164106052145d07400f0440029840320000740d84c40303407203410700240f00017600001b030800d03200b203034000b003010140707155400e0a665280c0c0030544101d0400413680050040001d22484d280c1e40700c400881 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 124519181 1250 124517931 124517957
    0x50402030111041d0a05010513110c03041e05010c0803241309060b0d030206180c0d080702040c0e03030307030b0105120a060512060c0405040203070210150f0f0e0106 73
    0x20040ca00b0030320422000d280420001408524010120f4140350503000a0311244d40e0502480110350090107800e911100c1e0503080414600e46500142c49c01407070220751840d000c001d001442c90740c0c015a0003c0c042c19400d4481d001380e1003014016000810081c00c000700d0168159403407000e02c0c00003c10020000840100d00764580d11030a0054003101c402406031046114207141ca07101502d8104400d49074a41480e4141e507890602e44852000d1980540c0901816150382240d400703464507a13203070800e00780b01d0400c854401d951142c0c406604a482054201c3e81ca031028410300094801080002091000343c20552038070b91008003c03a0b038400e03c0ea10380052a8801c4600691311070258400080c6d0706c3c1258410400c1c605100c1d801344081e9002110948040420f80090765a1540121341e045903030301007404200600d0074603030099078001301c4600659490111151100c4121780b40e40b1143c03420703100d0f8500204034a0782c00c040110042c04240d910303201ca007801d01c184c4040404061194004100c20f6000900b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 124520431 1250 124519181 124519183
    0xa08150409060c03150503030414190803031014010302090d03050306030304090203010315050906070507031407050607081501020c031504060e0a0818090105011710320604030b040605040203 83
    0x20241c1503004a0412000a080718028014030364200d241c1200c2416540200311850000140c40894640d07614003108124040306005e05521544051003049040003000725a0b4442800518071a00c2c8050286640e20b1408910440a071000b0040c81c0c1458810042d41455807913a01181001e1609402c00740d6170b90b103440011910758401c981c09800e101388080008404c100740d1a4007010703a0880700c00288115150548440d407210402e540d500c0108104001500010b0f000381c01e07a03109491100919820a10701d900d5440c2080001c6a468000543e11001c0224180a0b1003c0d483c1c40780c820310042203a29031050110307aa41c1780007050901070300c01010000d41000000d0300b103c51800d0496094540500d00c0d0310709507410350040c120410340c90312014264441e60806002c0d807412207205950b00105150308541102170414042d02c0c807200002c0e250340c0410983c0403102c2914440c0d047c2001d40024081400401d4103002130308040d42e208007000c000801c0410b141c2014103412542081c8002010b4a03148002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 124521681 1250 124520431 124520441
    0x30809121009030324051809030706020a050c010e06010b07110409020a06050a0801060311030105130902030601080a020a081b060c01090209100303030b1f030c020a140a02150a081504 80
    0x40d0340441d061641c1001011350640044a06a00350010f0200c1d0341c03000303c0b0750f00c1e000c81240a0680c11054806030b0703900403c200c0769025008414101500c0c074260250b1103d2040c2e034010030a45001ca100003c2c0000031050074425086d5010f4130901600d8254101030403000340d07200d6800b0281044e040590940b219554a92200342c0c4158000c01d9440344542e80c0d40041c00c1c43c0c1090920b14013103002c09000155881c01b902400c2c599000903c15545140c1c04c0c0020882024006284210025551114900180c07801c11003103020b8110f40004140f959414810050840082d40140415820124032290440f100300ca0b4a002c408040390b6a94072480045003040c0100003103140654015041c0c0d091284076845599401d003600c0c066542804041c50303420034800747d0354414200740b100640075038030b5200b8584a13510010b5a60494419690f400b883c548130b409030480904107182c840e40150000d00c0c00c500d4200031071503c14024601c0c90307050444540c8081c014000040c00c0f0100c61802065450340380d0340d82c0d804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 124522931 1250 124521681 124521703
    0x50c120406031401080607020a0b070509040908030a0e011401050d14030406050307080c0703120b010c1a0a1506020706080a14090606030124170f06160e0a03080912 72
    0x40580c64603500d6a0082c090701c00709501068000316000040b50000b0007050701d62240e28250024400f403404e42d0b9132203010040c000d001204004060002150943c0c4078042c03060310b04d01402420b501d9080112408003181c000301c001040c82d070b1608021840501644644c1030448504648880c0e45405a05010f041486407008603001030100040126026404c0340c05180a10b2181d95410760390354070f030405490300f482400300c0a0081860340f000304520681a4101d0500701506150101d40c10103aa603842c4d448481c0d020a09040c19a08030800040200b01c0c41020058508400381c2e040203490003c010303440310030600491007040181c0f00002c240019503080240344270004d424098807850420308846d2558426a00103109508000b5980e2800e0718460341c030300b081150508030380c111a1401038100e90307001c403800d0200078070b0159124405142400b806114415a603a0503103074192951034078001d040e460340010840c452000c2e80c0042c004107a07030700b0039624550300070343d014100d403152815400d26001076101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 124524181 1250 124522931 124522963
    0xf1203110313030e06030c072a090207050111040b0301090e0a02100c15060b1611090c0a030b090f130609051e010e06060d1b03120509030d080412050c 66
    0x30a002100003544428510b0600941e5183e04c03101c000001c11020703210035100408001406d11441010901d148058a0081417680031a40c140b0703600700c4c0309840d01a85501180381183d000c04c52105000d001c0c003541d002e28104420356440e09090103a1011980810300407901c15540c0d480421466003002c01021031121380040100550401c1c1c03120007403601c080304008507581800c20b507001c44000c03254000c4209907030410740d115080c1b411040081842d4541780d00203407842145a8100003850700d42c06038840c0038104a0005070750301d00c5c103080b014007a0390001181e24000e94402040103000547e2075030035600500f00e0102004c0070b001d94281400545113044010346070b4040d204010070645414800c288504808000a011a007401c008240d1a558101c8031541c010440e900a0f000240000219600c041c80c4034880d82d81c4252039469030a816400307482628003090340007480c03a10518042001102c1c0c182540b0701031000707160603507030106032010000100c02484004500c1015411052241500c0900198 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 124525431 1250 124524181 124524187
    0x140312010909110405040804090b010234060903050a080a0e10020120040f1e03061811030f151009050405010b10020601080303060618030d02070806070306030f120311 73
    0x1e00024010310700a403040301d0544031000e9140f940d0a02c0e000b42440f894201034501e050a02d0b10b03a003071020341446a0024118000c000f080480c0c0c4c0b1940441140d8110a052000d203024032042d072600c1701e1240d6401c46803d101c400841000040c00c00a41180010340c0004080d450707200c01002921211410018035038448500003000d0340301a8154840301c09c28564400061074203807400a0110140302d01d005c2c80001500c40c00c024402c5500c1645e1111028080100c1805500d541e0b449030002c44141011a4424001c000c2d10030b410301058040c80c0c40d040c02d00300e02601c1c0c0a0303104001195900181d000940e107050a51001440104000390107200a08055000b881986010f1901b18001e28020452078441c4510050030840b00e440010502d05170307400d4600551840c0c40740c0c400c110075038020640501c2501500030000034513440c18842d8a202d112070750002e2102c9820a5540303428004010000d070300705441e00303600700b011034030107412811400e810103020792009482e8172040380a00401074044007865000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 124526681 1250 124525431 124525439
    0x406031d0114151e060a0513170d11100902040209030a0506010504110405010804030305040f020d0f052b110f06010605071103060103080a05030a061809050601050406030305040314031201 82
    0x94846140b04280301c1c4828500c04204000300100180c07800e94070842c0c0100d4201c95142c42c03c0c950b00a00f0b480e010b03030920908240c4599030540b032340901e039046a6080c00340c40050001c5c00400b08000078909000741010032000b00040f8410b07130b8403032007007134600301160702d49402c0425500c0da5030443d00106805801c0e00d403125042c0c10407540e9203800703100c1c42e8002c618020901700b02c00502c1e003c1d501030b070318140d5030f02d4030035100c40d1402c030090b10000d0004c2c1c41040d10841c03140300507610f1001400b0311912481e08180080740c5814101c0c03d01e4040c0c41a030303c0503000c038600420511100d03000c0f11421404d03400d0007898540300c601d001c0d01d0200b1150030f00d40e540c450080040742c0c01c1c0d040301c06069281d100e0510000c001c8410000d054940380d083c48000c1400c1401e0203141e441d14000e00c050b41c1d10039042c0317800040c00c1d80d8400000880036102c1d00807810556440e1504030600900b84005405880140c40034800d0030302e0350b41c2c010b2440c0300b10b202c003030280c0e5aa0780405080c24000c2c403c94219000c0643c0c516007030750712 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 124527931 1250 124526681 124526711
    0xb090117011404031704030e1f020c0f1c14010614121501122402071209050a05040f1407080a0e01090b0406020a09150314090c1e03120d0f050c030c0406031d01 70
    0xca009c1c1d8002600c11003407041c00700d2425002d00600010040d210704011501c02090300109105a10212021350801003d826070020074803c980003003003002c001841e20841d40c400d10002201c034800105558000d00360303000003681607202c1d160440384a010071803540781003070038500084200b10550850680000429a03040c68ac550003418070340b4007410018501c0c4100000c00d48041e6018483c0742c0c2c000342816803c00a518141e81328980e14000e6a80c0810442140007004041e81400c03110200810030328000d10011b400d0510500388500c1060001300304070b101030384801c800064020402000950001003051915110b01282c0d4000c117002008100500000000500900401c4a41e10201c5d250300e40006c602d8040001c0000c04240c1c054108144200710200d003040b00d4910090a50b014031401e5500c1891000c2d400003030195504081c0d0008074841c0240492041c0e070b00160203034016034814014001001a03c4040302e0844015040c00540d0551862a85152000c40701540c413955107048a54000c40301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 124529181 1250 124527931 124527979
    0x40b150402070c0f080304030c0e070908030a0903200d080d0912020309090a181502090a14090106090605030c0304050a0b0906100f270b090117011404031704030e 71
    0x6080c404002003071745a030341039940c0c0c0c007407848094264447e0320b10404c0225000c3d062940c01440070b2620000094030b07030500924550011350f003000020f9100c1300c200284003034403a001c0b2902c0d002404000c48201100002a00506042d034081d100b03200000d0b40c1a004820b560040c80510342c0302408000046018801030f40f40c1d041808d0701401048984000350a1900e144900f62075000a07010400200e942600c424080154116540715169400c000c6085a580d03503800c0d46000b000f4200002c00349042d00400d1103000d190682c030030020711200c0e8200b44210b50300107041ea5030080c030f400d01054032540c0d10300b8034030b01e801c40b0424003400d0034491106100003110041a0350b481801144031080e14079030790b0400307084000c41c0d80c8200c2d4a20b040804500044e10002400c07100031411441e00842c8070106040020070181e420380c400002c802d016480050030300d1003801038040e844507100300c50081e07207081d840140070002503420b00340800f5a800001030415003c4c05000c0c1d03001c031029050345407100c611502650b0000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 124530431 1250 124529181 124529189
    0x1805100908010b031507080a090c0b0a020111070201020d0534030e031605130e1b0a0803090105090f040f0c0807020c0306040507060503060d050115090f0e06040b150402070c 76
    0x2500f000035124030382c00c000440c900b04003062402e13003000303903945082114808000b400d00c41505807074a14840100e11150f26480141240e110a00da030745081c0e0002900715aa0111090302c55081400b800c000340c6e8000c11513051800d01800c1241d5204600012120b01c03e08030b45200c550000000040c1c0040f025030b400110320148261a414000c503507010400d50b03202483c1c00081240b03104ca0380c05000c98103182c00c1c0141441c0e04400d01091000c05401c9403400d04a8030051070b4041480030020b4800f61504000060062100c0d10203146442e8210300020002d2055040755800303400c001c1d0a840c4c7c0c0c0c1d01c8030b43c011b5162040824003001404111440100021000e8841c0030043c880c070010f0014910300401c0250040398800c000b40f415a02d45017003568a9000141055030000059800c0c0780410000c0c0181800c1c1258249079042960420640c10101c407052500b0b248040d1402c004800e000c4000220184c0080d000141070320030742c1d12902035a0003108641d01c89500036001003070000810081001c144244c2d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 124531681 1250 124530431 124530433
    0x170a0210060509190c0e030a080901091a0f130308031f0f06020a0609032d0909020405030d0e03070909080c060109090206041215020f0c0705060a0504061805100908 72
    0x1281c0c0e11020800300007415500013154405840400b2120706043e4001c0b83c8417416420155030300d8840d5800a410300790805015604c4090009040c0310b1581d010751250003422524808075122000c07030700725880a00804011030405100003801b08240140c29641200a5038400c884540d00c1c585000308889007051040b201881e0a400400495842c90403044030058030f403e94010001c002c120786a08020f001d4810043e0f091101c00416524205d0340c8000210304000b00d10446402c0da0311400004200034002c1c1d210500283c030601c028800ca86e408a1280c049100c2882c1440325058424006400c00f51103074090442540740607020010042204098591465400169801aa40c95000c20241e404030032000f98031a404010602c081c070291000c0249080c0544110905004551141d400f00c2e48080041a070845000ca400121000c081100384041d00c0b0070b03a041400e20040c00c001900354000c41c0500014070900c0520f0201000329444500020301c2c1c0100003003030765000c4a030080c014078120f009071591 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 124532931 1250 124531681 124531691
    0x120f0c090e0c1e190504050705030708130f2604060c0b16141c020f04050405060d24090c0e0702060a020403020a060f0e03010504050615011d0d170a0210 67
    0x503140942ca42c450001c03c04418403902d85070001040602200d24800c0d8080741001c0401040c1500c5074070070184584803907140c41e5641e0400c035030b014028450041c800c000e92190800b80f0b0340010442600341140c80d9006240c0450640f11420355803031890400c4c003445410401043c00620320b580200d0508900380520460b04003516249a04a6090507110030ba00c0460040c40da640d4000801d40018150034820f0b403501c6000310070903a000000e07644a1b00d1004030300100400d062040740740c24880c59401c40400c4400c209401010381d00e60152100c6403c44101842c043d00401e07218100c05e8000d0010325034800b2002e141961104e0011588920a40c0c1a00044c4548000103000302407034401c0320306880e0010140a06c452401c142125412030306030099042081c0400069a192424000c0c2801544241d0161845240903440d0f0703003011800c6440c0c5d504114114100c41090000090b0701000103d090314040384008003820180d210007144158101a000c000800b0500340340e0205a807451085403201c00d04c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 124534181 1250 124532931 124532953
    0x901090801050c0f07081c050609010506070203060c09010c0b04080d0608061b070204020405120a0201020c01210e030f0304080c010b0a03031d040b03030d0204260601120f0c090e 78
    0x100302c650858409442e102c0400446500c08120b0b4060980184548a0a8503003116102000601c184a00040d5070342c81d2940c1c140105e601d82060320302d014040030340d0101e0402c1040d80001e070b40c031030001d416007a1140e00018214901d0344503454050095410000300b640380c0c201403030f01c0c1200350320080304a10b0907480d003000030031400c1c0d01180345070046c480508000910100174405048542c0101812a4041d03400c000c002203544403800f0380b4aa580c00c6c040903000d40001d0380006810000b180d451b1358100901114141400301150940b40000360304580009400412201c000785540704840c11341040300f41c01b0041200b04030554006100490030903000344901c018001c1448030400c0e1038040140030560340d094815102030100c0e1030700c020311001040402c5003100c8202083c00c50b409508440b44064000030140940741903c1100064803904034030b0342c401c14514000f0305486440600461819011282c6071794140000400710555903500010340010841e0b403604078500900c131034202c0c4181c901075210482 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 124535431 1250 124534181 124534183
    0xb03030a0e03070e07020a15020d180c0803090a0b031017100608060403080c090112020d0f060b0301260a02030105070305010e090604080a030e010f090302010b210c060f0d090809010908 81
    0x21740221080c1c1c00a015a40341c50b5100c05506c2922088846016428000181c5952060040039000c070450001c102042a282c140001d0600326504250081d030b108104d110010344502034004116003081c0314590f01c83e11101014014801c0940c440e08244030703080c0c0c0d03494002c071020811503405131050f4001c01c040c99961030800e03118002280c002d00880d00c0e850000c1c0450340c1c4200101055041494403150f450342c68401c0f1402c03a007150888030701469039a280d0120f660039510880010b0300c4096511030039503251403055940154200c0711190392420500e6040e0f5104010029003809541c0203000740190b140031392004008042c01d1040c1c4480d002c215021401010021611034019900102018078201c0034050a8020300705000d90144199611600350120554030320868024900c01d07800400e16001c02d0080003843c650840080e022000141071040410000080f05010040190b6045882c0d40c03805254803014007070441c40803406400d103004c560070002100d004100150090701c41c070815a840c0d442072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 124536681 1250 124535431 124535459
    0x11b0509190b0304020609010c02090903180904050a240203011d0703020a02070303081306060f0608160e010c0807060903170705160b060d0c08031c11120a0b03030a0e0307 75
    0x410101c2c5400c002090142c100a0010707c4245418101207155040d56404900c05c0c200840d0010030b107400106040d00403050b80112143c001404481461003400e080c1c403860345031214041d0040c824480300f0b02407200c0034401145444846c607a075000719100e40e511020500700ca0064284122282842000560517501a1003501c0003042d2039402084c1190031540c06407103900c03010f010780044d0a00300360403d0000e10325000381c8028165407a06045200c2c68040301a001c428080d00001c4d41361950100056070700d6108400201e16102441e081500c001c09080095044c0308060f13010745003d08210321242815000a4a201b041ca4030560720304090781e4598040b00d01d8010a82c8041e1640071640c00000071980c01c0014a8100000610324802c540352941c1e602a503240030741c0550f00c0d03504041030410b208030340708030108000e80300c1d09030511180d4100440c5c1407281c490000302070484a04000410080071003580300080340d59025049a40d51240f11a0103000941d0b2610f4244c480d01c070391040443c0400c411400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 124537931 1250 124536681 124536689
    0x90405071112091528030216061505030607050a030c090f080d020601050f0a0603020304050f1e060f07052713021b0304060e01050714070f0501230904020705011b050919 74
    0x20000f032852120000d100305505d040742c00e004243d000e120601c031081d00d02c411880e00e503104200004070b2105094243c04001101d0388018400d8000404018800e900217007198918200380c0380c0014112143d590030340700280241c01c4180c4000340080301040444001460380d680d40c82c25001c480702c3c0e0781c0e108100010100c0c03c0107030640018892070200301090107900070316000392107101620308071241c0b14025131820304094040d080710281441740f26000b034800c2c0042c5400546260440c0720515062402900d503106440d4081c8003142a6041e0480c01000518541c1180500510b10380500740000c50a0000e50045846a240c2c0541d20326100040c1100000300c8044a00703d4648640c801d0200c401907503141c21002c410703900c0744440710440303141160900c1190064031104803411442814040010031400e409410032601212411082003810301b0f101c251046041c080750050783d5584145011405080c0758050646480070b0011040c6005402002501e400c0c0e0007074a1007035080b440440002d1220180b446 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 124539181 1250 124537931 124537957
    0x11e08030f090d0204090b070809030307091a0c1e010c03270c030b01030b0f06090402010e0f0a0f0e070f140304110414070201051801110904050711120915 68
    0x204072141041030141045030002407803125004556004901590000b410450706070000340d04001015400c240d07030340e401c03140c034074025820740c6003020003c0c041e58000d019130000c180002c42e800000c0381d6008100c0b442c050b10305066941c004000301a1f45c801e020f0400004c1a9075013000b1307140400320f12a00c20107244024905020502e0304129007102001e00d1510000e40e204000681d000c07003c035181c2400c0710300843c03190003000450701c2e103100c03200300440d005842688142e000c4400e0002507039100f085180b000c0822100c04800301440c4d400204000c002d54401307032111000c2c2d41e0015800741044e010901c18241d5480f84006940b4000d02280c1049820115090007403081c0085404203003103407200e10605601400000c4c103000482000780b000c0f201129040010f07034451040000040d0b901e2000450240d000c03000b400780107501c2804950f00e00800300c08a000d80e50711800507980c2c6100313050b42c505207081c85080e100300b001d02c0e0801c2440765011402641c020150240d000c908690400200c484d86001c0c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 124540431 1250 124539181 124539187
    0x3091a03011a0f07050f06010b0712031d0a0b19060602070e100b030f1503031c051906080a030f080c0a030c0201060509070e04050f01060509010c0507120803011e0803 73
    0x10401c42040e6076012491422090910804404a6110008184c40342c0600020001541980d0495162910580242009040501c00074001909424484004820300d040104003040107626500955000032079140032032080700503c3e01031180c04444a4013400c1d95942508643e00408200d8080e43c03454411240140d000180c204012184c041449403c184802c0c03092102564944451031075400c25698004a00042da040c8821852001c2c00718501400a41c05581044480c1110341d001d82e040d02c00501c00181c031a40000d2044802041e0a00c079400148400c210385925103c0e07040e91410241821004289855003001c0740d40d000704202c1d4814030b0902c4c072031807400703c0041c2c080300600b0b02d09144505664072345d90302045036920140000d20541c803566421005a1080c0c04000580300701500a10a60503c86d005200031680042190705004003804c0000b968821340c0380c400c0c907000080d44811081d14042030705004200a810081d4100d07807600000b0034503030f00043da15003103d010742d202c1d90280d94010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 124541681 1250 124540431 124540439
    0x318090e1203061f0504082415090a0f0e06042901080615011707020d090b070b01050105030c0f0a0e04050a05061311130b190207030b0f0411060c010903091a0301 71
    0x203c418640c4844485c82c02c2401d169443c1035007403030055030780d00090800b4429404410350512500c0d100d030f0b0080c0b401440284558200e00442d0300d441c07024021540383c588030f9041051861756500407c03c621001c0d13044034428a414140894440592128920100480f10a46000d44940150503060342c5060300a04195194450340625407501c42c00c80c1414407094040c4000340d00151600103106500079006440440d104490040c8504021703003100300000c0c4180304100c00304201921150658030207081032a680c0e16004102090350007003c4c00880d1000001400c040616030040209494420a65007030015480313515034101950400c8480c950000345c05902c2e03032501200d54000491322490f45550320b00c1c1600b50174000d1540400c5030840302a4620020720a0001a840364100000565520203000d100d42543d4403001c013480c1c0606000318010b1808081001c0c8a00c015840e03e07010802001c02d603a079202000c2513806004107410580108001980015501141e15840c0d6105440900c00c0d51643e030038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 124542931 1250 124541681 124541719
    0x5011707050418020402071202120a02060f060a0302030703030c11040903050702100504080d0e12030c060a0f0f05070c12020c010e0108091509030304140309011b0318090e120306 78
    0x11801e0a5a42c103404618403c0140c1c6592008011550007400f0058400c0c074a090040d01e0a061290f00c01c0d4809020000d1000407503010429a40240c034101d4190301584803d000a011203aa580001e0b605025a500010400d504000e004207994410350100026503584010003046903c2c40201501041c0104602801880d0004542050014906006060640711442d0500c0c00e0015215200880c1c5c2e0072100c8103191500d1402c0000c14801d05c0001d6190120211502d40c03606009001407c2c1e440e11089415003110690304128020b4001030400c000d5490416001450140351300c0e011b03942c910780e030b00b12441311034400725240010341c40c180c580740c000102100c011030b0b10000c0100101036034012807601c01c1d100c15441d01c165004c3d1007010003c6480c0c0c145401e055200020ba80180c260303d1348204030018440c1d8000784402070000c5200c03408504002070b810182c40c950080320700c420350760700c00101c00305241c40070f17500c01c440b120b01c84c10803590b20b0348011039010314911065035101d44c8546141520281204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 124544181 1250 124542931 124542941
    0x1080601030f020c0703031d0d0b040f05010f0c030b010f080711280212070f06030e0c040509031e121503030412110916091503060302130e01050117070504 68
    0xa4103140001e51041c2041c69041260856226101542c2100c90200305055001c404104404060208018152a00c0b0002910416a0380000342000084030006051125845020201a800a000740801410b0401c0000100f40785052500800d183c410808a1940700e4044000c0002242d100e00e01c5a899105050303625221091500049200e61402c0c60004456142504400300c07198032102e025000620420420b14181e40350803d10b0f9014400c2000b90745c944281c4e07402140e00074200000e0401e090004103003460452801c0a070054102414029100380c00001003807007401304182401303003604000e0808010702c0b44030805080da00600340414400c2c4680550302591314001400c482c50155103402468500b41c4000090f5000c0103803060724191800c1c101d0f82c4a42c0240f40d030f051000c40815600c00034018841e60300070b04117943c1c0440500d044032400303075210390061074000340440305070902c8c0a40a0040c01e5400c0c2d0280f8035500300341c0009600c0b1214000c1128150389000540141d41c20720b024040242 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 124545431 1250 124544181 124544191
    0x3080a020903070819060e03030f040b1e09151509010b0c0309030d0504290a0e041113030c061b170d06030b06100536030618011b0c020108 61
    0x8014254005444441000904000b004c5c84a950240340c4607030604104803407a00c0d21600032a04100104029000c04c08109940251301c155440540d46410705176600309407034815903440300e150007414420f51410002d900da20441890100c00c10342d0342c4440ca52003448017191801500500700d10f0043c4040d9500c40c014101c0d081d4903808076070508a82c0740c0007e00d44a0b155030203001044001806200e054000f41744078030444170095180135150302600e036a80c6039120b084070680801c084809103d10541d41c6400540812001500c402c1d11200240f0500006121620044982d00c29613400051881c1c091202040641c41c0008544a8645151a003e0003c0a00d0294040e4418208806500e01407144580c0014500840010b4075030329100c0700b0700c0075410b800d16030002030110510580d905605c0b000011505c0c40b408480c404102d040410030b00400800c0e206d9500e40c1405003c040080780081d01c0724104144901900031300140c560100e40c060000a090703030140001d40c100f45100c0141d4050f0f00c2030340d003003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 124546681 1250 124545431 124545433
    0xe0603100e0a0803091c110c0d020a060e03070e0a020904061a090907120c03020a02060907030206030a0207030302070f080c0d0908060a05090c0406060206090c04020301050f0405040f05030c011b02010903080a020903 94
    0x304150403208211b07003800c1c2541004610768483c450300d210000c00120034003c0c010342d255085854207400280400c0d10911074202000105000d80e211510305002d01801020304403d07084c2681000300702a0701a4001d4800d0038012858a1000250800b45000c08801d81d40f4254400345401800c4050040c0004000c00741000d01152100c16040307a2124400c0401d18100c56034016201d0340c240070002e04010001e0302d209030300d51111101780003503a1030704100e90704800130742c0300160703110000c1c078043c1c3c082e0152a0025110321003c4030b240c820700c02400002c10140d50040b041e20a8110f89250554000495000e1501d0941c010000603108805035030006405c941c484084920581c0500002000e131102e0b5002440141c002a050043c0034800b003180c0c8012000071032303080d8150740c10b20021030381c0c5005800da9181708a44480114080c001000b803000a540d8112058982c4d030010350842078023034025025501c0e4031841c03956100c03030a0391041c8224000d65030b246d503c140c0a500ca0028400c06034010042403030381 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 124547931 1250 124546681 124546693
    0xf04090c080d080703060e190209010c05010504060e0f03041a0d0612033f0203060613140f010c050303040f080f0706050603010501050d020a030312090c0e0603100e0a080309 76
    0x103940d0204106403000440ea0f0310394040e803411120003000d4801d250300c00ba001000300e905101c14810703000300d400110b0851140050300c503860100121840c25407440090203652810b4244018442107400034036150341d10b07108541c100010b061031180d4038400c910804d201c18191135108a015002040103140302c4080d003030b0201c4c2054442c070f0701d070f803c040188a04402040c19100e1300d091141030110b503080040c4460405c0c4010078444001300515845a030030034200300360700100180c0d0344e94945042c3d40c40c4000f80514100c2c142c3d180d5600e003007010344d1071300d20b98842c0c6020800e0201c2584200407800001c1d5201d4061400e60700c0c1c69032050078040d10b0b41340446500d0390502c0031141d0360450502500d81e03139000b2200403c442c01c2a0040c54215941a0403a42c06140a50700d0700c1c0c00340c0c581c000044110380d45171500908420000030180000c0c200e038117004104044070f0600041e00ba43c2c0c5804607028123021400d8440e03108518000d94100d40c40c0d101e50400c80d400000c0c0040100e0ac141c0040d6900040c034400780c41c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 124549181 1250 124547931 124547939
    0xd03030504060b1201020a03050a050105030a0201120e1603060501050d020609090a0f021809010e010e190906110702040c030531050a05240c040902030c0903101d010603020f04090c 79
    0x341c01e51315070300540c07580e035011034000c04459050045540040001400700700550500e070119860b445d04040103410301c4484000b400c00020789038030012962501906030b9070040c0c8100845061903c00d48000e0b41c142d07040c10008103042c9000e0f018903903103540c0100068a84015034051060140c001085a00d4841e9146e5104d02c03030100c20300092154941f46400392405054180800c41000b4045e08900c0041448a00612010000c800010b41215140302c1280a02081013a000b02a0032000030042c045414030403c10074201e00e0001400d001072084a0601141440101c100c1c01c940c0b045070100480300c5424060320f0019100b07607000d0111940f140000d01da80103180c42c2d480c43c01c540c43e10700b110f10364000700d201007058400c1e03503024a66000380b22200810381444080422a4041e0703000f10031760582d000000c42c0c41860007408a42042e000501507605250703043d42c0d03010041c10143e0801081300c0e01c100190100c8101842000242c950090840e4075048000041c48002c143d400c02c1100c82c1401170070049 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 124550431 1250 124549181 124549189
    0x318150e1807180815040602090d1401020409050f1b0d06090204080601080d020307080a1b12030c0f090605031512070b071a04110d0512040b0c010b0105090d03030504060b 75
    0x148501c0e503d481d04400030090100d85400007419510051a0b81c01100c0c20040206206490796006900b0410150f240d400c0040003031310400c9500700040c091002c584545000d08010b4006c1c1c03044a00254042000c0c2d904c44805d6074a801080720780b5483c0b2848484040001295040a00005207001034000707002c3e92540c0588080340d1081e04989100d43c01032004118600c0d00300030014400341d0764401740d41072102c159940007070390080c5041c07503092015491500c802400c4c5040701280c0c09401070220203100740718500107801096460000000250244d4103120518010308108003100c03201e68030146103a076031103a000c0040318405120b9600030100920f814240d9000c02411001c1c24180044903030320501480c2043c3c134291101c002c82072903d000c40800c00480c542000c40403080109a0741000007c10a02c1d0043c01d2080c0040040c41002e80402c2c041108004040035011081d400002048030030100001511180220781100350b020303030a01e01c1d400019100c0d4000d1038210744500000703d06d540c03102e4001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 124551681 1250 124550431 124550479
    0xf0304030602090406082b0e101d0906100302030c19080108070e190209011e020c030f010e060105010c0305070203061e1e01121104180318150e 63
    0x1e076003040c0c0100c1e00c1495480c00e441400c00074401c6000400c5400100c0d00c0c0c000d07513500c21007021803851180110130380a00d401002c01d1080304400401d5170401550320840a840800c01e4000a4012001e99101010346e080035109030b4060100200407041d4958401070440c041d5000500d07046e000b4109110300c1800b07225000d030b1120700345c3e29a00c40d5070a640c18020014038200b4960b01c485401490719080c4a501d00c0d0507290b1044545140c0300242c2ea4034454401a0b07034103a244c0c80244400e07900c4805400c1040d602141e44070701c0e0182202034038280c18103d0400c1d4240e6032100c0c0c00180c1d9401041c0100403541c01240d2410080e40309040c80c900304019900002d05001c01160480a030005002480c807480c0c5e07500416540c080a0380c013641004a02e102c241c00c041d18814011013036508020101c100500201c0c200041c200d1000500500c029206c074001f001003441d000340c0c01c40c0270404550f011107010344c0b4641c2d1101541c00c000c9980c0308601143c04c00b26070010011101d1034100034941c00075620040d0050b09 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 124552931 1250 124551681 124551683
    0xf07060503040515161d0a080d030f0920190605040609120b1501090909080d0e0303090a080906040306020a030e0c03010606022a030f0d0e0108190507020f030403 71
    0x42980301d00d010f082290418200702040000c0711100804c204040d081044103600351240ca180050001e0507292004540c080c0050300254001e0f00020005400b0130300040b641c140300c0ca983c0e0f0030f000b160004d00800080d1481c1d903900a02410300c60b104e441c074003d041d0405072204c0c0b000405903443c0886500c800d0301003520a40241000910010301841082c0d00300b07901d0002000a4100c0c20b2a4258944800090031130242c80d030b040300240c0c0101c0e402c0c142e1040c46203102412401e00108400c4440c0e1400ba8913a034024140400540c0c00c201503200e000c180841034038402c0c40d02ca4050620b03142e00d540d442c40399a01841d84664417020501c40400410f840344060305e19405c1c10f880c0040e0200b01c0301c1000d454002d044001c41d119a0500b1000d1048560100b103400c622100c014a200d904114075000c00803c9480180b055054481c4848520018000160304280d81465445280800c1198401112904c5080310052038100840760021a40306481c0e000c1c03540181c581c815a50500b540200c51350940d4031940c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 124554181 1250 124552931 124552937
    0x209041101080c040b0307030506010908120301050310150b030603010906060e09121309050405070b07240501030308340c060608030901020721080304031e140f0c0f0706 74
    0x110011865070080310998002c5408921a41000d241041545d0b0602c00100200105074458012071116402082c124014007045000c1e6008005c61144000c02a00244200d901c00e00c100c201c04078140d00941710b60507504031040080d2a5281c14a40ca1a100398005402141c0543d69081da02007c20750f980300b60006406144280003480c00d07c1240341d071412600744500d0124600400c400180807800c110100c08950030401c010800d551182481410900d0b40e9104400400300050030104000b079040302c0d071402d402100884c425403010b98107000c0859109020007004900034401103556050584a05882c282104408152116142d803a100e195441500d2040c003142040303a040f0100156405a000a020080000c0d800c100010300000d42e500e10342d124081040324107080c1d809001441e20498003070035401040440d540d05003407400500300402d00c02ca4815036030141078641070551046c0d40842e241c1d159001081c0c10044440e80e1103410354840d180300101e0307100d5800c1c07a006100c0140030401c000c0550b62 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 124555431 1250 124554181 124554203
    0x51036060311010806010207380c0d020a0c050f040b0a06050301080c010203071a06150f0315060307080103061505041410080a080d0c0e04050405010b0f060a081f03020904 75
    0x31400702d4994451425440c1808900c80070440581d074006400c0007143d02d420030f0b01c24a4140e411a0701e401b07180500820b05850845e0b2050760000b42100010f042043c0a0700031100034140c0c40408036215222b80000425018000c01c003044240380071888a001e01800034400a03914a003000003c11221a662180c0013282012004101d00d403000d0080c0410040b082c00030f586000d80c1680c1c0c40340ca01d4a000714465002c00010045203064a500e9134043c1c1c51030807000c0040e941c0d1041c108071290303900100e54094000070310a2403402d0a0600409580c01070007036888580c1c090742190b81b21005801d00200e04910312209540c00034542c3d9550080c1141a004c406c4520018244041c455140342e1310342e04180d0b40c40d80402c0840e00001c08060458014141451002172508200c0c3d804843c4a001c1e8801030ba401401d190500c800d000c0194000d600b25201150910901e000d01d1007840241e00500e60040045110f0b00001406560400740c201401a0603542c4c0c1a070f10351700e0b40d00081512105842c02c0d2400031801c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 124556681 1250 124555431 124555433
    0xa06020d0f0c3219020309210607050415110c040204090f06120203120c0c0a0608160e0d140721111e190e01090903120510360603 57
    0x3251107003038826110080c0103180360f1207401240b0510464400c884d0104020780c1016100d482401504c0c49010021300491068510722501104010b01e0380035164107014540200e1211030103039080302c086980402c0603070a903104444041c0c2e400b00f01500a40c086000d40c0031808420390760780c4014070203044513074070008180a80300021800c030369054016500742d8604150700405658002800941c810803d0111603031032090780c118608100301c0034100307a0800d8420f0b00103d10b0a4100440b140b00d02681828071000b0069100200d80c0d102c68864842d800c60560810803010408c2600c40c0ea408451001c01c0b82c0100d40d88000408007590442c00d02640010000d070020104070442c10442a40302040f2045403403c0e0b10300483d610b445030000c4090b07200d090788407030a06004246c108010000c04428820301c1c0300d50ba460410f400139012441c403ca000502c449042d10b18560303140709250160010341c008003840e03414010f850090a44c40d204404200d59100e502c41e00f0780c05064904c0c440d51141c4030000c500c00c2c0c69 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 124557931 1250 124556681 124556717
    0xb0d0506040b0102070b0d02131202030c04060312140c0601081c020c060405040203040f0b0c0c070e0c0405010c051006060906080106050313021905060309010b0a05010c050a06020d0f0c 81
    0x54001072186040c4514140e0580e8000784034401d0b180803008032540c0d10111810f0000070311981000900380440c00b5000a860403900c0070310301d980781c001d805940c002c000813000c0200301d03207003800002d0800e52140310544d080c611895404841200c00c5520f503227000c0b65074680d2481c2c24001d92001c00294001041140b42000145c802c20360056a8001042001c1110000070264000d5006280c005c581c040b0001c1c1c140502c5200b1104a01d400082c024102d041402d65050700d81e021401c100e000d40b00d01140060101150f090300340c8140e940f40303c0c403400c2504290045a51020594042d1568498041840d0b0b81c2c04c003d205490043c099600c8020700d00346007031400780440d401607210f0420703c5000d004100c1d4003c0d0340f02501d035040b94101e03403207411201c40395030002a0400c11340145812003404410800712017130550061484507002c41c0c00b0800d1554503401140d80d03405c1d04400070501d4000400c040300189954028118590982801091492440500030211000c052920700060b49840560504140c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 124559181 1250 124557931 124557941
    0x120309072d0e04030e060a090e0114180a0605210115060203070f020109081906110915090f15270109030803040602071e06050109021603030e0703020a0b0d 68
    0x21032090707207020751052400402081030948079904511482d4400603040510075404c928031000e0061106031a01405030b4000d0040c5481c0c081c100c44c1c1d080392000803030f40140468051041c00740c010480140800c200340c9010865101406222080391204c9020032103960b0841c40ca6250828014007415464030135010f2425200754091b141c400d80090030003401090380c080215a24190400c4c444a40e0b4007003440121040d01c100d03402800a805039410b0000314446114851403510b0141c041842150202c200a940d14801c1c41c0d0b00a500001c0e000314405142c50042c064110800014200440c81d030b1040041074200b109003194141d40c43c0001606021200311150350f841c0340851107141c0c2c000012003800a8140d03035650101070601d960200c0001c041160580441e07050b1580001e141c02000d1041d16854404114080112995802c0400126414585109644400c079204840720566081b5403800c2c0d00030416100c400744980140c580110158480d045c040c2c0090101c01c500c00d507260b080004003800c4071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 124560431 1250 124559181 124559219
    0x6050609040308040b060d060c0201020d0e0105010605041809050114040201021e060703020c010b0316060906020a0c0315141602071406030a0506130915140609010e070212030907 78
    0x40d003480900012961207008150b010b5407003d4040d0031600c940c03002888461007010000c000e64100000d1100003a41900039001c2258801424414000b9075000603003612024010240011000c0c44100b103240c9031000c820702184441c810014034220705840e00307400c0d039016942d89175032501c0e01c1003407000b1135130704011190424810b0b401d80c80d003004100650381d4840d9806005402019000300b4a40e1090f8400c2d840401c903003c004084880c00c2407680620001e9810611444020450101c0300041460011909409043d03001d015501380c0742c2550382e11034070000840c40c2c1180b1740b0342e1000f161021840001c41c2c06c1c000d4080341d5000c0e18840d15520024940002c5030444484071004001000c0141c41c1c4c3c8065a0304102c2e40700001c960307130380c501c07000c5485001c9500e119000d840c1000038403001e2185a50041c210082190700c10310881ca130500c20155200825900d5903004000c1c0780040100341d1f007011055800c81882d03c15281c41070690030960030290001e47c2c05542a4020702d004002e59070500c803841941e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 124561681 1250 124560431 124560439
    0xf08030306120a030e041e090b04051e030f0f07061a1c03020303150d080a0306030b01150203120417070510360206070803190f0b0303070f0f060204060507060506 71
    0x2c00c885030340003017140c841c0091150140383c072108058030100c0c08021101180a40700307410003400c03a403410100038088040d6029500c0f0300400301e40c6035041c10303180d5512400b002034400031443c000041404a41c154070029082400207030074840c500c0000c1484c007078100141c1041c0c852038980c090074020072803d400c0c9400c5800c40011050301170340000c0d03004030569a1081030311411a10030340e40341c000f14142450020f00200028130001e209607003a030f0194040c2c0f00b40c0c0c3c061039080203181c0c0c8a911210600c1042c000711b40250b070092105a00d89118024000e610a105407818600c400e105442203145800c040400c8996800113888640400903920030b046966024002c12000c02d507102e407803d00c154524107001d0303402c0c038504040c40c01503440e542c007103850076a4420313403480d0399140202d14408043c07102e000e40b8045030b040070740e160265107880c0034480b84000c009018500e080c1d801d42d03980400355064001200d015124a0b16180890074601c050b0004154607103030b4279507a1055140c68400c6440c01801b030751013 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 124562931 1250 124561681 124561693
    0x7090807081b030a020603010315050105101407140303070906170c030613020c120d1404150c090b13060206010b070c0e07020a0c0305070f05040908120c040f0803030612 74
    0x12441c800264182c0b0071001880000008001c1030200e401d005940c200a50000350003c000410000104004919400c51040070840e50340c8803400c0001586885c1c50045c00262034074003080d4000c540c44010400b4505c60110034482c103410412071810b58008881d01e10120f006250304214240d00101c3d01c3c1a2031800104191283ca0100c00300c5082d40000742c825409241440b0f10b00ba0b1b080f001d176048405000030310044580b503542c14118076013558400005070052030b080180380c070a12090041c0007406142d10440c8000101e84c450380c42e8000300f128101c48000c008005c00d00241d0465070302c004008043c2c0f413010000b009400d01401900e0084103a01c80360140b1000c1200e00045404100e000f4152020780f01d6880d4292907001c0128502003020710702805101006900204018000400724210303990100b01e04400c036540c0081000301c4035190700150900204101c0340804816264059a1080d4a034410034241602d409189064051b150410403959000105105417854281d800342c9507041d0b000f0050007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 124564181 1250 124562931 124562939
    0x90603090f0106170f012901020a08070b0402040e0f0c09060109030b0f090c15090108040303090206181e01050702090603070e04120e0d11010309170c060103060b01050304020120031c020307090807 86
    0x5588a41d03074000044007050159011f1242c0e10903c0b540500030380040c11aa1185510b09001110f1031083d20101e12891501000400203040800c00c940010300e072401903d1929100002e20050010061a485c100f080410010001a20041d401070240e10540d41c0101c4603e03080c06440c0c075201c04800454031801080010440c03035400340d0219000f80c4000e203880c9020351502e05c1c064016101d00702d4002d502c1000071030a000c0c0722030713903c2d0340c4070f000201110103040143d80c00007145a02c1080d2101640054010031809015003884000d160704010007504072500c0554809846207011003e032070440d107094000b058140c5140e4428104450074034200c032812130703c80307140d903420509900c01100355060644801034181480403488415200c01003c010f02c554580c0e043c95601e072101000d01007150118a0500c1482d069403160b41a240300d158117840d48144c00b041e0171454501d1520100e41801d85200410000d00540075011361404c984092500141c0c403400d00340c5000d0101c020a400020b0141c1c00000208 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 124565431 1250 124564181 124564211
    0x9191b08070e070507060b040e0a0302010605090121080c0f10050903040f03201f120e28150b0f0306150d05071a03040b010f0605090603090f0106170f01 67
    0x307030422010308240c1e45d140d6175850800c014081c0d081410703074401e00d040086d10302d580010a220424502c00d50007040350356114001c1100444007070003018411180744110b02207100c000f00c007880b200f90140d41c94070704000d07061000034906601003c154000d87c001c0c100a01040b4050b02413960481580300196050030305003458008050203034440a0980d100104829580500b00144001402070160145444240d0b12130040c002001c034151140028800824283c4103840602c581c5491071010300c064810000b02e004140d20700000841d91440c2e107081490b808000032070040a40c10707041c1c1700f10700c08240c1c1020b002c100249282c0311407403140030b90003110402c82210200204155409422900c8000740030007400d0070341c502101a0040c5409920307a1075945854960040a0b40c855440ac1c5201c60700d80c1c0c0c1310301044100324404c1c4a4100491024001e070f60701032400c3c0001d0750f0701c400c041c001c650f100c3d00d280103040d0950f00035511000b01000c492503003448944040c04500c042a02c402d0003480400d020703d17804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 124566681 1250 124565431 124565459
    0xc06070c020306131113020a09090603020307120203070f0807030c0905161407081b0708030c060403030b04020706050a0c0e0303130b03180d1d01090e040b09191b0807 73
    0x844513409991000c4040100910718046030080242003139400420200c0070000942c01070b55800701048110000140e1071401e4003644094942c06009808400e01c0c2604111001e03004020403a4903010320360740854140070303482c50907004003040e100501c101303450750920390904500ca400c00c10038641054108103640000034a40518086245003c009800741d60280b105107008240d002002c0030000a0580ca2080c1c0400d641d0680818000a903a805903580040584d640b01d000700280340d82e0000c1002402190103a8441d0ba54181c1c05840503141503081da40308000c80724120340c0c504110795509a00081c0340e80c060b0420454030740c2500114500000c440480c2c4101c54030b8401c61084690002c001100c4074030b816501c070300030203209080f2002c080c00c0e154082e180400600f11141200c420891801c0f40390301c507424440c22224030350400f4074070b52150b03112105094401401c4240d103100711f0a40c40030898951404c403000500504a441361410052150440c001c0d06a00c41c0c503c6502c041e10a00031107101400ca = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 124567931 1250 124566681 124566691
    0xa11150405061c020913020415021507230a0203030712050606040e27070303170c03060603040f05070609091401141c06140109050907080c010c03020109060c050c06070c020306 77
    0xc0c00f111480201c015001a1040f00c2525401c100c00031041ca07000105600984241d0340c01c0440c00c91500364042041340e40303245135100070003400480b030082520715000784017007a070502462a80b00280304d40000003d040380d12025480005034070000401552a40c0111082d0248a50315028492410101c00244040c091405842124070030311011501d01541c690700b0000200900002251b0315403e00101519a2a680300507800328032040384ca00000410074004521034514900f169003552104820300401e50002001121400e00480419002c0340080003000d00401459980201250074915064241c6590314400c0c1e0100c01648018040304110094140b25000250f940200300140c11468440e46a5201c0d4080c1c80b0910305010b8000d80c00c20543d01d00d05841d400001403007141c5500c50040c1d5141603e209031241c41d0050f0003540c7c665840b900c5410181406480045400070603500c403101122040c0030080049040050030501103071051029650200860500540a144540110ba147c03140181 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 124569181 1250 124567931 124567957
    0x40825060f050d0f06030b090c0a030b04050a020a0308090109060320090604030606062d02150a0609050f0115020d0206070503062b151107060f0e0a1115040506 70
    0x620201d160711420984842c0f070040341d01401980c41021020008140300e0205450703241411000858900300014101ca5001000c0c02d001541d61a50700d03101800040508201d42078096801520017582c2c07040c01d8140950b00039031070b4903615164080003400c42c040940c002003d240c108001c06600c07491390412146500100c101e0703299200390380400680948245c3e040207040626101011518680c0b00b06042055802d80d07607900200071050082559044000d04001e006900a000d01c582c49602007007003a802040380d40f000f0402d02d0302c40c440f980644000b00d4223003820050090041002d2203040f500403a10f04401c2c00a08007104130300c20025148c44004024205002000010035540e1311105007200c007118002c4122101401c4000e1081100400d03140d041c0c40102d0300da24140c000c0d0203a03215854030703512200403e074074000e15550f824000e03001014050031201d40c5c4030340c0804080700034001280354610444402c0c010b02c1014041044c501004d20420011101c10b201c103100c00c0d20f4181c11240030030b40c2d1030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 124570431 1250 124569181 124569197
    0x105030c030a1112031306031109100309111201240b0f031905010306020a030605030d051b0114041b06030510050607050c03010c0e0a0b0705030f03090114010b04082506 74
    0x4004500d1a01c00843d00906600c00090003460586d00030418000381e42c40703564284000c00a5101d1810b16010300c2880d07940c0032000410345098075000b030340002c0038244120b21016201007000f0008a50508046a900340c69444600d042c10311440040992944400e44c0380c614007050422040500754081e400d101e000d4242c002010980310b0301c0f494074a486405480c503061006684a283c25006034010290b0207011909154010665203404a22190f5190103980d8003400c140700b00394019131038042c10341d42440d95565070040c2d28240402c0c42049100301d001c1d01c0c0d1600301c95a000f00b1000720720107984c8403a04151811b018030103c0803081d400c03203086541c216104c645416030740c20850306200e0000006a4103619024900c0c841c00d41080c0300342244401110b102e03001740e40d511500840c2c2d110300c1d440101150010482c0074032a27802c86001c0c41d004584000001820a4032030144004480300f0717041f2a001030804075040118410801002c1c07400d08a107800c0f4450021020380001d0034080034040c14081c00102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 124571681 1250 124570431 124570463
    0x3020304031b030209180c040e25031a0f0a020909010e09010e010c12060b0708030406090807141b01030b01080c0f090d14150705030a0b0604120c0e0105030c030a 71
    0x21002c4001540e0010f01110700c034281070116103442e00001007195528011321010148510b0030f482a078180036440406414062410075106501120182c1d1642000e520013902102060b07403c1018102844041c940405504000d000445100e10013400e40000500403c0f480e0a90340321300f90b040e4119000e03403c1110107500c1d401c400034050070070504060720a40c40c10551800c22a8081c505d52214030180d002001031586548441c402c61141c8000640000c40c00c00119000441c240d0008030480d00442442e0306010f4165a160240b204151248403694085981da102c8a400410f4481780d1000900301008960380c10400680080001040200c20300030228007409500055401c5509a41009080e0f500b08051071401e00e204544e0001c884101c1e1149a07400001c0202141c50540109903d0310b610b811030f50740c1240f203805007070031001060b0003017000e00000601407270b040c0c0c191500d60320840711702103027604001c070001501c0c005902140c805e81c0801e403411459140820000f00407900f002c0707221456810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 124572931 1250 124571681 124571723
    0x807060c030512070305010303090803121b0708030a1a040b0906010f020102040f0b0415090b0f0f04090f050f060f1e0d0b010e090607050403080a030213180e0c0d0302030403 76
    0x60840103c448180142000442603040d4030160607603200c4e854810340c00d03454012059903801035400748044a0f400c00e000c43c07520424000018a20003406040b03038035005050f42c41030f960750001e0302c1215030203880314040c0e402c450f06450180700d01d240a0301d0070800c000e503000010f00301520191045041c40302c10401214458400c0d01210003621800140110850703803101046a1540300303100e550b616100300031040c40e0b0701d48504a4102200c400b4038001e0b0401c084009001003030ba00000900c034101d0700401002681042070b0207901c0102256050000f009d280032003001c2614a402086284100103000361850980d032603607840c843e10001107104000c40c554a40107e420401c1c14000030303128104040001030400c1c8881080c1e803013148070400b9541162106179042d10b10740680d010003071210505020400e850b1348641c2c040c0c400405200c032907000d02542c518030358100c05411200d0b64080f584038601000d600303600f04600f50089606554282407016103840c000d48a00072400020000c4000d4507070b02c0380d8501c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 124574181 1250 124572931 124572937
    0x10b0d150b090907030312060f1502010f110307030c020106270e0a1b090603020a030602030403030b120c0f0f18100b0a0f14090a090e01090c03060204031b0807060c0305 74
    0x507140d0b034458105242c01a668031502c1c88101e0004000100d40d440b04ca13428024071044030741c10b048502c01503040c0f0a55400480b4103910032002c40d0b60b0b401848d01015160701604203d102071308100c03541c90608002c004c0c29241180c011405684c10820104484c0752005032545000d10bc00807101140404001035101910740300032000c0382e5210700040703142805440e0103c01e0b030703810f00c80f45286003060769081400305407030580c44080c2d40804031030800c1000c00c60640042d5406072123031500082409010000035400a030300c01c03015456521400a464040c00c02c403070720600400b8125011ba080703009400001d440e10300810424505d45d100354011540343c400d03c2c1940e4000e0300303d51307514907120061560020440034028010320001030001512903580305110007121450a005070400c4445401c040c8506c01802019000c40300340d40d640d040000c042001d0340949406148201000740c0e40d00d1441c103012043c403e00202c0d81c0d485003240b540801903040b001941c2000c0f10b062707052005150042d81001e49080c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 124575431 1250 124574181 124574201
    0x20d0f12090501060501080609070801030201140c0604030c0c1e120c03080a120c0305060904120e03030406080405060106140403061a150307030609020f1e0d0c02030318010b0d15 78
    0x10741840056001c0207019002481034600a0b40d07000c1c0c0700c1e5680030400240640a0300c0d440045a031075001030015520800e4120780d4183d000030030619007100c20414500e009021a03040c0c0014009610f85000c00219518000051155111081981e100b4503660150000f15104000c9c01210445140c420031410385101002036411219464540c0442c00300605240400d0034400c801616107460302d804103001384182402200040c00f8031144c0c8e90307181c1d11800003e200c413200c00c007440211713465403002c1d690810040c80585110760302c0c8082410685407540c582401a0824018040d185040840c08103508040d00c0813079030403502c0440e422103222500d00031a2030000701d0390b0b0851460b0810035012216080210301400080d98108400755030740185a00300c1c00f03001d45405000d86d04005a28a82c4480000c0908000d40980740501c1c206c1602c0d00003049840e040c0c903860140c0c00200800c8002172035903920903183d0340324100a0001c1c08846000901c851420344008040000c0c014040d4102d00003540709080310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 124576681 1250 124575431 124575467
    0x3070905070f0f020a080904020903122109070806160509060d140a0c091a0415080601110703080304060e0f2a0109081506061204032d020d0f 62
    0x1c0c104410000c014800300324808010a03a140403040420f1310010344011503c0d0400c03011130810300c082007044042c0d80301403a07065040c41a2640d4241c00d4010200600307092035a40e002030001900722400352010b07840140b200340a60002d0900b00308030400415065445101d40d4a083c50100324140107503440d0040900300303a008100400e0042e80b05045d5072107030701414802c044042d9180c1c0e410b400c04040d0b4500c580340d00c00040440e04d040107180741a00081c1c00c805903009900c5d0810303440c2e0085e04040d55002000d400060902d0003413107144c0d42c020200600f90076403940580091802c40d284c841e1540b2003d41b00802269a58031042d08080c0d0600200d02c10b15511010740da0240701c00801080030030f40200702201c000003640500500f540c055084103007100d01040150000881410039200542c00c0140807c8c0c100a081007480340f54441c0d41183c80c400c51183d280e40013040c112011180707105030251031f00e803125112410710449583c0c001490000b0101989425418002032000072110030051484510203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 124577931 1250 124576681 124576691
    0x1509020f0706050f0a0608011e1806050a15050303070803060105090d08030a060e0a09020a0e0912070c0828060915061409070201020405090c03130804170111130b0306030709 76
    0x444c00107041d260340507480c1400144600340d00e4403101802c03908490f100e807040c07184804240005e40d1854000100f0441032600070300c1007051540390b100079528121013004801d1360b0b45514058813004480840701808040e00114144000d95807407004603c405402281401000714540115540300ca0700d8034801a4030018064490030a10302d18000b5002c00d002d410306450850b00014000c40603445030100d41600184600941440c01d01c00d40c0750400d02402c10490b0780a00200340d590b098401c0002c015003441038445458491374030282c41d090501c07040480c110440d103001d122100014000b031742e00006400c0100040d00b0900c9213401d5000c0d0907510030b030f1840b4604100b8002445004007403411640101a01c0010790742d40d40e0366080707080340b142d03005090780500b503480800e024100302005941c0c0480c1040030010310003040c1e242d000c5a0b4001d030340080c8000445c41c005800700c03076081c0034034035a80b1000d40c0e1071410030712001d49031a80401c260141c01302030304003c8002141d6980070041c00f401003440744c80402c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 124579181 1250 124577931 124577941
    0xb0403110301061e05091812040e060405040b0f06220207061802100503100f03141605150a2609060c0309060a020901050702031203060109091509020f070605 69
    0x44800040c1140300e01c25440c2c5403000411450060074540c0c5410000141c00700d0b10705003010802d1000c3c001c2c0410302c0082241c00301e1254040f00300711311800e9101c003c5d103041c0c88500e809014110340c48003c0c811030145007440705000c00658400d42e600e400610514030803407e640d0b00780200720b034a2444160b04183e5080d0175075200c0a259503034014100140955020701c1007044524050006040004009400c10600580010824802e41c09540c000e8105c0c03a0100307076155940096040b00140b0781041d07402119074590004400801c000c1200107444103076680400500c1c00380001e02d10186005003040044000404030900c610481040880344070701200e03401f8111015800100c0c3c00022a020076152050401007040744090b5029648036010410046c86284e4a18031a800030703400c580d0203a8140201441040d0060368103000244e0706070b0103501c2c00364607403074210001011080c6a501c0062080c0c6030400414500080c00308600030b4584401026907540a881c0016002c1d12400070040d1400f860002441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 124580431 1250 124579181 124579193
    0x170a06021819140414040b040318030309151803060f0b0604080105040308090609060720030705010c0201060b0a090b0703091d0910050f150120030c120703020703060b06040b0403 78
    0xc10354080f00e040808020010040c0300c11190200d12001500325248001400a00381c0d01285038490301c240f070061048251804501d080c0c140035001100450440b260603c000000c4103e9000b40d44168503204001692600c4440f08920040c040a0001a20390030880b003c514250404101c01e0006050590f4480d039170701040780200000d60742280010000000f00e103482000080c0d450044021001401040d215824162a05032801002c40801e622661450001c00800c0c405080782034016000441c0403c0c256030001d013121700e1500a0300b400101030100c41840741d844488407040d181c619900d10f548440c10f0400343c5030740c0c0907a4807011400d03104030100c10f0205060011103000748100c40807200400004048041901d00c02c07141901d2904800340001c004180c41c0140d1245444181080100c01400500840c00700485400f0a14168000110014410810411048440c240e12241030a141e40c81d6070007901c402c8980b00240c245902c899400003103076158421900184030a444040d40d0750780d00d190132 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 124581681 1250 124580431 124580479
    0x41b030809040c020a0201050412030309080a0804050d050a050720040905070e010509011202241303030912030504051035090604020f010f05070606060e0307170a060218 74
    0x1042c01141009203984805000061a0748041d074161549410182802c0f2101c028980c4034400360704050b11380304c034a07001c2208130006051804140e500d04038189407900b00346284c181209505400c102040018810300f9034410141d411840e449801000700c3d86882d08403c4006003117048195000c1e20301130807002000b20008114044491859000c030f141e03030707a0300100103041c1c4091041c0310000807482c60050041c80d00b00080001600302403c10f4024840d0050342800c0c81d0040707a11810246280241801410f40103004000140548050046149201d55006000340194451223004010f00018250414003d50141100c1c6124040781c0c205030380c43c2c03d003800c21500c0e04400d034072a540391038000c24682c0c0c402140980c49941c002d49403140910410004540c01c0c800650030800704032051203c50300103451400782d000200a039a60f2201c034400b000c02014108145640041d000d103000354100c5052041c04180e2942860300048016141e0711034080300d11004c82103018150f84144980d40080d4101218205 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 124582931 1250 124581681 124581697
    0x1608010507020d03050103050705010e18150a050d020612060121060f1e0315060b07050708060c0a02070e0c07060509071806030203030909060d05030409020a030b1e09041b0308 77
    0x80740c25120f0b50360001e070b08941d07080c08003504035000a0410b00c25540a10300400381b042000d415001050b035003c66005400c0001e40340304500003000403044075103241409401000c0c040454842e03000c08070a50008005110300c04520074007440300000191560301032401c003c80014400c010310f054880d9416040300811190045030351039009542e0106036001072002900502484e84804902c0e40c0c2151070b002c1d03110101c4040741c5120303034030381802141145040c40a401298406c0000301002814820040c3c01d05a00030b00b0026102c1c0c0500c01ca0407a1540001c00780c044900201907590729488074101540580301d42d40340501181c2c208414041c45040000d481c004648170720140402c2c4030076100140041c5c40c19844065495481402402408d2031b0040800750803c80040421605e680c40c1d68070349045030402da21944400d64040740001c811501800380c07a031b05420032140030443c008410f08070400c0610b48500140034031034074000501000403018008808400e00a00c030a0060f603a0f18260800e5400114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 124584181 1250 124582931 124582933
    0xd14010c05030601051e0c030a081e04050a0308040f0606030308100509070e010e0402040f060207140609090a020a1710051801120201050c16030f05060702210a02160801050702 77
    0x404000c0301482a41a01e008002c140e5503989402150380c0c03160300c401b0072549a070510b01010485110b88040401c000c0036902c982d41c5440702103240140700c00700440341c0c21524907040c1ca654800c02000990100b006c0e1119a81400c20b00c10a444900b04841e40345085580104a035191003008824103411403181842050512001c8031815110130901945410940f0b003440072500d070305441c0040d9809442c0208003603d010b040142420f81d9400b030840c400d0311940c0908096045640c0904c407902d89252030032118601900c65510345000da1000c41c4004000134901c6400503400b15803004010700c90580c101c000c0144c006400b800b82000ea1503005641014410107108096405442c800350803000394060480b0791650344843c01e80d0040c0c005454513480340702c40c1c1c1c009000d400302030001581d04d441000f0186009003240c80c2050712070b01d005886c004000d07144100755840015003a14104e0494060080741110074180358440b0140b49099252a20400901569002202010401801c154041c512403500c1c2d034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 124585431 1250 124584181 124584191
    0x207050d020f03180d121808010213050108130c060503071704020f120a0c090b1005090901090e030705011b08010e09060609151201060602160b1210050d1401 69
    0x108050ba62420241c949100680040c44a92400301c44401c04203a102c4015040d0b40340240203039151406652207144907404a414030360301843c00f10b0038040d450094814180214a86415a0440e0650342d640340700d1941000540f10000d402500d40c00c0e40f024100d90310020750680700d80c0300c0401400940080703c00c00001042d000d05880081030254000340542c0e000350134007a6010b4a201840b001a910034284040c03440360400c81800202c51801010090400810004440000b00300b085108440e11a0080070004284014102d0395201d91750380d41195844000000d200251194050030b50244400240a5520340341d40046003111140400640700c17000d41d41e03442940e8a465082003400015103400729154000b80000e1581e080124501c4e0700304004404100100c400b020008406403454164102d03965140c0d43c04000b8990104808400303140340760864440075080c024401c4250007452000c9424031061808906582e8000644002a00300034040800d502d460707042030030002213130351000c501c55860a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 124586681 1250 124585431 124585453
    0x3030a0e15041a0702010203070c12051c020c0d060b1203030f060402121914010816060305010528080a0b04050723040e0f07081f151e050a09020705 65
    0x91084078141d0380d04191038800719049140412998000d44c1089040d440704009420224602c003045a0040103245890707074a800041c60541c0c06c07c003001540782e1855400e401d8844c04070307030045071000b5942002e407121040508a41840d8020301f4231000700f0398000c050403002c5190414003100641c0b04162580c4003941c513480d0307282400120700c0f0b1518025903100031900851541440d55100200402012002043c288420704440450302002c1c0e00c040800e030702c00001001035a003040c5184009081b541000c200642c50b12021603031012420007034048441e207644042242d00b030300740ca40c0c00203003644030106c0346d51408601e402413540c0c1041c2c42c15140c80c803401000003181e00071010701401c05840c030205103012011200502000e0400c0c0104400240140c00c4100001030b001c120240080441c00000c10208483d1042040441d0410405510650070128506900080c01c5604422650908581900c1c0b80201c050300e00d1480c41c6401540e805840e00900242242094025110090068007519200050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 124587931 1250 124586681 124586719
    0xc0803090c0906120d080406020408120a080609060102190f0c060903031409030316050a0506070509010905010c020315090319020d030c0f09090b010302070f080406030608241503030a0e 81
    0x307464211102e17400080c080800302d10611005800520a00300542002c2d181c40040b0700744a040c2010304800304011420000140c0d01c0261280c00407403d96002c03010782400d0000075120045041a2101c2c51b04820120040254004140048070340010034203034110340303400e030080042e091032000f0b030700040d202c003640c04420340f2000841d0034281c0d00030015464400c43c410f80303254181400030180d03140e0154074800c0300410010310030584070300e24596035141e48a418500140c080000d80d0403107410020900117607001600c00181601164080c0e66107040141d4448007842d02e144503183e941c80c40c0d00941d00d0030070705031500069000080c16083e241400071540e415070440e50070ac1d88a121100040c4820300401081c0400d0340810402c981c185000740c41e00c421034484130200210380b5801c96840713500240030030100354588990340c042d2030207178040c0c4040d82c4134070003000c5000d083e25071807485140c1d50380c04244035045580d07800e5141440682500e8030743c1405c0c14040c000501c680c600da4082c02d001c2c6226000340324 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 124589181 1250 124587931 124587949
    0x11401060519080403030b040f0b040501150504050904290106020706030509031606022b05060a060f03020a02010b090405010f0e0d020d0c060621060b0306070903020405070c0803090c0906 82
    0x80444541d4120a200c4901155401e00213401036007070654666031310170305032070f6400b404060203040c000208035a02400c060000f00c580c140c2c010322a01c111105003038519070380042110101c48045990001544450a000440800a55040000040c03241503c04145804030040d4101c85041d026a51741c550303034000c180c00382d44d802c441c108042e4008105440c801da290422406040e1700800300181800005001629081c841e1104805507841131840c0c8504007071280a15644444280c9501e01500d00d0b052000d4401d0b240c081b84030301855000303d042c500c024800d40c0000d01d50740d40180000e00c507050504040b4000c00c0500403282c00ea40c2842083d1440f84800254a01402c1d5140e00400a034542d0300700803111150035042c104ca807541c94840018110382c1c20391024100601c88001c2e01180045490010116038181c00c0321030080e0803072801c100038942c1210b1080e044a40548004c201c139695104101ca100420200040942d440401888043c41000404801c0004103490700704290b00e401c001c101d9401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 124590431 1250 124589181 124589197
    0x80f010608070c061d16080307110105070807060c03021b010c02030a12291306030804051201020d050901050919020d1209030c030503090a0603020c0604060209060903010e0114010605 80
    0x203501480400e04961003101090183c034003a00d80010200c19105141c80c221111139021a41980084141c001c0d20294200d460b0007007016000075850701d402e61b40e0b42c034140480040c4c082d05119010a103c01404440300c1140d081c0340d40010200290311141d07002030001e4002c409441d6120202c1c4900d8144028144074100c1215541e400560500f041ca10080302c0148043e51655059034668200c41118110041000361429800c942c43d001c135014002807010368400146007081a41c00c3c040c0c10004030f00900c041714140e49054440100c1112885c20580c0684a1820f001c11581e10b00700402c81b00460651203140920f00b100700382d4030b40001c00314503117103100540b0401940c000700d001d800c032002403100380000c1c0d001e600900301002075542d00c1d02d41c0c0e20070050070f62080d5140e03000051a584180b4100d101e104c050f03d00d90804504041410001682d142030040009201aa00040b07101030769503007000380d600c9408001c0080c0181004144094080e010203000784004015130350000c117816001e10155a040c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 124591681 1250 124590431 124590437
    0x804090f1113050f0a030501110301060320030a0902180406150603140c030a110c060403120e0a11010201150906050a05030c1f050d1a0a080304150302030408090904030f080f0106 78
    0x10760a05007003081c504c0703060a041d64046103030640040058801e020701180c04c201e420b1a02c0d100c1d85020000350540340d00b07051045941c00806100b2441280d20019242c00c901c0c460000075505040388081440351070842c02e221819100b5408100c100141a000480380c0401e01c50484410755a402069040d034084003004820000d01100180b035612a11003e0740c1c0c008100c810205544450072840c0c0010f40c080c805c56881900001c04200600d074100b4003a0400700c0030002d04212101c811002d070350b00d035800309030010b0038107181010001e110fa10035000042c0e0340115000d016107403683c44004100a109074842e183c0550210400002c02340b03800f01d852003031004080c001c005012000d1100000c4000a5020142030040c2480302400c1d407504c92041c600c80031000040d044c40f00d01c645c820403420940d26405142c40754000c002c1400049442d9074103841044440c2000740c2c9949940c904151030340220070009811070b150f502080b05040d80b10070384142da0f40c013030b4442180319142c0100c0792906200c02d00070b24002c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 124592931 1250 124591681 124591717
    0xc030507020a1b0308040b0307021b1503040303060e01080a05010b100c12031107030c03112b020709020c0c130b1f030e01060e060112060e0c0a05070804090f11 70
    0x102d21032503241c80940b48003046403143c0d01e0312980e03544055003060b000303142090004020072883d103070108052044243c030301c0e5815844200310f20000b0181c4100c01c1d0910851840400410101402500002d0181c4a007014403c0c1c42d43e1100181d580d90141e140741500c09608000050f151401c260072403480740d406030398400451000715141e0100c442c84d2029140c1c00c060303540040309620307000b41340a08000c610a030f9945440714402e0500500c842050090384040340c2206071750146003e20a006502560200405064070340a1400f05909010700c5e980700b6010f071400007407403440041021420707142200045448000b0072910700905011034011100483d04032402c82108801c10185090707095081d00d8603d40850301c601040c1020782034603060ba011235280501182404002c2d0303084140f00a054801a0f400c0280614080f920701010f680540b114412044c001100001c25215008580040b07410284c219a2942c0d074a044000a00c007401c0c43c240c005181071844507c0101d45002c446141143d07140d41d040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 124594181 1250 124592931 124592933
    0x30711010c1e1202011a091501170106050d0501090c0c0204050a1808030f010b040f0905060d021201090b0702030a0e04150f0b04050a050609032d0f07030b130b0f0402010201200d0c030507020a 84
    0x1044032382c07540d8054144400101c841c49a80c80d0b606046010348038581d00d0303945401800c485802a0703841038200a680d00d04020f02d501d40143d0181d2004c9031290100e40204542d204c13303140c80014680da1465082c8001d81e50801028022080e0041d0b00401c0c007a1201205680e80741031440c403500540c010482c82c5c8113885010460310031660040b94102c04020f20100700109203500080c034040100c03031115003e946520450f000d003c03c91011340c0d88904640003851405c11241001401052805503261056a58089403088205030821001c054480b029440448544481540e007044d00144900303445250303c148080703541d050000c1550b201c4400034008168020a880b092002445000c0e40303403145a41d084807690004104004030700343c005440001c3d01c140c40c21820b1465032202c1c001c2401da051002d00006800281c03030401c01e80c0e800414410748103c142c880c0d00c0100c3c050100e0703040c20344c5111005580040b41107080b038010035500111f00740401140008600c00c0e01502c0080f56000702582010242034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 124595431 1250 124594181 124594201
    0x5070903030c11060c0a0302010c050a0504120f050d05130b0906072010110709202503090509060114040902070c03050a081209030711010c1e1202011a09 67
    0x81050b5200701580c501d520000008158a900070070ba011060754024001c0c04289502131088030544101450600d16000c840c24000d0094441c52050144e40d4041038900c20a001d450ac1d42100c0960344802030b11110f03050200c00408542003a61801401b2240b2030001900406001c1283c4a107003002d0301c0c031414540b42d6120450b4105103404104c104030148485201d03a540c4603500150f90380c0d0b20303460302c0140d50102100f0310300c3c0c6505034214010461030115201c3d2921200354141008244ca05c0110b039a4140100030441901e80c5003207004500d003600c402c2d0004241e0000a9802964000d440e024500e5a0380801122803100c0030340806c6482300208028011189640c00800c4802c0c010010651243d40e070355103852400c8040181903620240118043c54010308660b603642c2c03c154081e00540c145041900c41207101c07014100c3c82418000b0503404842003088500c1184a048008a401c5d400d06501c0c0c01c00b040095030142e070340c00040d40f904440c003c442c0c1c000407102914130000b0b00700703440560b00c2c20800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 124596681 1250 124595431 124595447
    0x203060f040201111015270b010207030b010b03060411070b040201180b03151908030904050a140a050105030d05070506061302040b030c040303031d031c0b03010e1c030507090303 78
    0x30b03810055401e5140c0041041005881030600744802c00042caa038480c4c2007111044001e40103101441940103050310200802a80c2d50248134400d0030010340e83d007181c001030349803d4440d03000918001da40d000001d16803a40318061441504151401d03c0f40084010043c035281c403d0070001009140003801150255224100100040000c00c108210550721107400c800c40f50421940b2480031a0b0031544900103003000403900f01c031600c40902400712241041051f80e224000d00319068043c0e591000014048000d5410485030700c0781208641255090105254020300024010340d8080d200b600c2422151030702c284120780c10f054001010740401d4895808010a101070201c021007419020700c0701040000600c6c000b98003c40d8260a074540d81c902d145005000e40303c0c4010040003003e0049884403a80f6030100488811400c1d400301c1d1a441800d0401000003404005102c6416618280a2902007080003e0656141818503100b01080038040307811000d44a080720101e000401c243d0003000000d0045800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 124597931 1250 124596681 124596683
    0x91e100e1c031e050c010e061501021c03020a030b0a090b0f09010f05010c0602070804080a14070b0d09020a1509051206040804060c30110d0807050d020c060406020301080f01090203060f04 82
    0x20b1071620210450060a5651f00d403100b0f069900a00f05011131b4060068000c0d09203007085c00603120911005483c80404941e0f090503505058001400f6400144a603210000d482402000358110310348903084200100b2051080e1405071100c100f0410480c9007015481d412140b21a800038001c41c01e25004448980b181d00c01114243e0702070082e00c0002c1d40403000742000d0b25100000748900512400c1c04100704039941064855501306d100148045c0f01150119070b1482060000403404000fa0310114503084110f60107800d40c10303503001403a1016940858040300300e500858084000085654a06444500c107940c002c000a030100420000741d8028800344442c24062103195210040c1c422a00b0b000d0f5001030a04000c100001b400301c00c6c51604908080c0b000110080102003241721206c024001020140500e01031000c007148580c0141d51720b8044a0240440e601501e203181006c0c0b400401070340013805050001c1c0a10045504541d07014414a04603e0300240101180e48854103d01808100948 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 124599181 1250 124597931 124597937
    0x2010207171309050609180a14010501090e070510030b0a030f0b01051002010b0a0303081b1803070803030c0301061808030c06040302010606030b06091e100e1c031e 72
    0x108000c51032621002440704440765841d59200c40d00c04402c1c6889006400154050f4905400d2140f2070700c501050551003924401c180c2500302c0b13003c62852400aa5a070010303c43c101c450705980641034190844c904880e48498240300e4003021540d0180c4940c0c56000b0701d600541d01c0100d0b882c1107403007900702c0580300394082d09986499840703446000400101010513110b07400c0c6000100b10343c0c1011844210040351601c000c2110a9140c0000344a07141c071840064200510540031035015000c03480303a13108080f070400174645d03101584401c95003001c070207251903442401090000602814040101e03481101c0d0003406a00d90703804c1242c10b40d050210200b4003882c4103030142d00400e10f4541000101a1f81034403038001d00052405140c020300392001c94021504150601000e54416111036060355084541200d00020043c0d19019200f00301c1d501e03c0c1d00e2503004501261903c5041e03084804070711a444261551300980f80004000c4410364011603000380064501481442c1c20008052050100e03c410b02d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 124600431 1250 124599181 124599187
    0x30207120201020408061008060609270601030c0b0703020709050a0605041a1207061403061201050f04031e05091c020a06050d0b032805010603050303100e060a0315020a020102 77
    0x1403112041000c640e48003a01503076000505008000d010048540d222041000311200c6074146128188c481102500c600e0003103002c0000b140159850049a89821083d204900903840030301c201c5c59518182803000341c1d1201700b207000c08110b01c01c8601c122030300b0341d800d90020f19526107811581001004000c050f00200e555035500802c00e55646d02410481c2c0b540d1064a04141264204120502c6001100c100150344250030400010b41c12511440f100c080403691162240d8503a800700d10103900c120309812965280404112284100320314181c02640241d40d004881c2403100d9646007440d00400325880451014400b640301450078000f828084d2004042c803028081c0240d01145038051141c200d8008103102048504c1d00c01054452030001d010114014081d9040c140c0f89e03900784030700d0071007601040e0020013108000d114003500301c03000031540441182d90320b01e82200c400a105915024150019042c500841c00380e18008120b1000c0d260020001c03050220702c10030000c020b500074040c400942d5028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 124601681 1250 124600431 124600433
    0x30f0c0405030d0f020105060415061d0d0f03112107050307060e070501140301030209060d051207060207060b100806060a090e0114010e03060c040302130b040e011b0903150c030207 79
    0x43c040850941e00d251604004a0f0b01c0c1d00000e429140300a00c0340740601e142c50100503050003004034101c1102c503107060070380040d000110a000801850781c0140d07001985942d00a0400462030150f09a103402551101201e170030080d20300d0b031a015581a24031300c000450030318044d40b944820060543c00d00c11400c481c6484206d6036001c0c1510318140c0300c5441504041d900b0002541c12600300500c0c01003140340301e881e56041d94002000b586014007060300440144260104102c0104282442d00c002c50120940b500e4480c6003c038041d502c40f00048807141d040040856540c200350242551804881d140e4500981c0e40805200068000d5911507080107141c0710009440aa0700c0b007201e01030041c030b0307041c0c400000c18440050302e04120144290b00a602880802424041100c00d0b05c1c1a84e0341101c00980c0c1148558185026102e01c1c03000c0c81d405858040c800c02c44aa0541c44120010000400311440340480b02041d5140010317403002030552500640c003a002280c041d8042d03500b1030f0780d03402c005003000c00d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 124602931 1250 124601681 124601683
    0x2030a020c0f06010602060105030a051207060212010306060f12050318010210060803030f010b090a0303031a10030504060b010305090c0d0c080a05150f01060f0806040b130c1d06030f0c040503 84
    0x544080b490043d085000140318165043c4100d40c090300069005040100b01c0d03560307007a40ca1160b07175294481000080f66200170070030303c1c2c1c04a8a520810003125915940c60781041402400c25120304d04e8041c807940784c0025900101c1e44400d00c4c11790031101550408030048494006502440107060450244e1100c1000f0148144030300c2014000c0f00c001103403640380c80a1030840c21801a0405000500d080c012410307640c0d50f298495007601d5041c45d000c1001080700c00440b04030846001095401050f44481401141d41503204502c00c074000d030014008488200019000c684060740c1c0101c03560030a0600788120700700190310312113203445500d0410031150394055070350038a803030a0340848846d0400008031010300552800b03141c0044844002c030741e141d49014005480b445030710300050244001180000e600d82d8860380411441c03100a040e4440c1b807404201c44000401500c140040407604051520005d0400c60b2240c06034110040c00d014910303141c00981e0ba0300120b00605103080d420301004042680c2e18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 124604181 1250 124602931 124602943
    0x90b0105010c061506020114060a05100f0201060807060c03180f0b0705070e0a14070e0607120509030607050903071d06240d020d060501050a122007051b01050c0303010902030a020c 79
    0x348543c0000b4902c04aa48c9030725040c08090711113842408003000078401e07581c404500c40380a1980d410300c140054421807084c0d002d00310a9100c0101070146c1000000c16942180c1c0b07140c0700a100750344070480365102000ca400e100c00c0c280220b10440710080d20038407200c06030400400c2c0c500d00810481d14019030741d494141d081c2508a45854840c1d4481d503d4030100c1d600903110345c0e0862441d00b401e002c11600d00e0040b03107030390250038000707400c00f0824900310401038000c0d0125425800702800b41e810f10300d02090040d00ca640203d000324024480d05400080751075001030386502041400d00401041d8403960104050742c50f5883c0c203071809081003900c1a14030200c1d100142170510000c10056183d494140070a001c803401607010341e042c0081007005524080c1c0c8a01d010505c003551180014040f40c0c60043c40c0c2420060a184255030100052140180600000c0030b0800c4078680c1095124500000300450302400b40454020b03890303000f80010302c40c42115030043d56222031801001070400414000b02840e02d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 124605431 1250 124604181 124604189
    0xd09080d0906180b130e010e04030206040f0c08160e010b0405010903060b01270906060c0b0a0c0e06040305030c070b07080d0506060904140612190230100f090b0105010c0615 76
    0x26217120040103103113900a0450300400200204030480d16181c1c8000c0c1d140c600060004049074003400100e002c10442038041c001a04a420440d0402c41d42c01c2034260709a00c05000740681c00743d060000103503045240c0300b103c043d144103039201984140356649240151000078070444c144105042c1c942924101d103010010024070b9078250303105052034204140c04680c50b90708180100009040341002203501b003101d654002194007400500000308100c100da456102c54501c40d403021000500005004000002d420500352810550318550b40c2d800d81e140c0c5503c82d89000a040c00300c14000d80d0410703003d41e882603500c0760000c4c044e1417070450400005000c071003604034094521240c800034414181080302803015010700da84011706c03004040b02e803000d030990388543c0001d1241002d50319800d0409159048429039811100e0800005054028225150403008921025480c0350180425158944c2d010320101c1e40d40103101040c069080c000112041a0407a80c280c0e04075031207000d4030020110420071a0020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 124606681 1250 124605431 124605457
    0x6030a0e030f0423011407050a0203060106050d0501080a12050a0327060b03010543030507111c030b0d0212010c0e0409020f04090317090d09080d0906180b 68
    0x241c3c3c20052203290504c0c3d0280b42007030b12000341d03c1d800103030b0f6041092880b00c0340719041d5450321501586881d0380340c20680380c8002d4060265400000e4140c0c0c102c00a0600d140448805008030707238868181540d61011a40080e2542400c01c0d000d00301d0b240644002c058030781c420300d00410222a00d601441401c1c403001c1c10803649010107480301d000c0c440039100f0f168400740d044009200e9424020400075000401d0307550001c0d002d5400c403000c22000c00d645601030300d2010020200e0090326038085d02034020501255a440410003080c881c0e070182c180071a90b64178450b600c400c0c2481303480d101078040b00104500d01c070180d0002881a00b400159489441a000c01c580f608004034400740104402001c00f0b9006004601580c10305240700c0060f03880448061a4440c10344000031031600504048918400070280303440000c00000c1800300c613080c082541c40320852a038684503405545d41d061182c0da0010031144000080d101d1000348001e61080408114440702c0c81008024188c403000220745960002101042d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 124607931 1250 124606681 124606687
    0x7081206010c140d1103030610140403020405040b010306110f0304120c0f05060405070501180b03040204060b030c070c050d020d0f020102120f04050907020304050d0b0402040f06080609120c070506030a0e030f 91
    0x10740f55011707665006400d010000b450450a21001080c0d1301009134020009001500c40e0302d004c1e034903081c0142c0b0029900244144001d00345801c0140d004032081c0001e840b814200110300c00007503c8031080b61000100000100d141da5900d480d06508014604018410000c4e14002c40d0085041c90045002f5036018901074042828149091072506c41258002414410003c200f42d41c0b01d900c0400c0081291040100183c4c2c0741d803580300140080c21b5603000062110386c044140040d0340300c05409031030760911a40c0f0007848252580200002064105030095010040001017000584451080540d1510600481d6071410850040c2d111070307041a1003580042201140410061620b8030070b194100c900c5002440c506070400b0041740b0355610300440941458803a001103021500ca61b8440d50351003041c0d040400c5030340d4032081c280b5101c0b5800e80380c48005204003207000070700c007401c0811501d003000c80030010090b1724600418003805400007401c592847d641c0e11f8400e03490810510041005440d00600559 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 124609181 1250 124607931 124607953
    0x1302030a0e0c011119050115150809010203253510050a031407050a0b1809090d0e031002030f070909050403081801020d1e0e010207081206010c14 64
    0x101d860b00c0d88020078100311030403801c000c000300c020a046140c1103680881c8400c02007141492405800e0f8140007101e02c02c108240001c5840700342c00140c00b41c4009a440451a407142c80c03e41c1e082c0c0c08190f070100c041440c410180034080c4c480500d620414000c500b01182c4240217480c2e01c2c038504030380c00c50a5041c0450940c0b01c81000c218850300ca58410320003403040307010724282070125600149500000b001100c2d1001082e2403c41d04100000080c04010500d40700c0d1500c170146009960010790b070500d02c94048072201422841c00c12801c5100b20240001841140d040440890304a040517581c1c40e00340c01050031400d0024414001107100c3c000031101c1c00c1070760401140c010403541b000e5104260141c0b8041c00d000000380d2084429810261486900c27442444001c0d2960080c8185000403030303103516200c1e4560500d0401602c0e00d4105402d0103041014030308840700603083c0d100706000240540e41c208040c0d440c1e09020a00c00750003207410705d41500f43d0201c0380d4950804100f59115080d0541c0300044501c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 124610431 1250 124609181 124609183
    0xd200301140903070602071704181a240702041107050613080d090201210b040c090e061302040f080f010507090e070c0203121201080f06091009021302030a0e 69
    0x842180a5030480240780c5000180241c032400303500d10003405a900042c115050189a5480c44078286c20048080c1d035031640c03410108035151900e05020001c909020000311076101c0c00700008103a09002d007128107085620003200000c0718204840441075a0284008005600c81d440740031070300144400d0541e519080303410300a11700540106841032005086401d078000815050030ba40ea0310f0701071600403034004090301c0140c5040b4501140c001c40c2207a20f41101c9503010350780d00040c841e09401e032401c020740032040c941201c42c0f5015006584010071100041000307401e007400e244c07503081d5802c0001401c003500c0d104109420031003079000000e10b0b8850618034842d000d00f8030415800409604014500b43c2c5440171007039000d0001049170702840003180d41201036440500c07040716040001c0011607603e03076403010507042540f801c2c000c0f11070754400e11040f820300d50400170b540350041e40c10f6802018070030b1601d00c8600140c6034600040782c0000d005802880054041e0016500078240220041209540c4070146 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 124611681 1250 124610431 124610441
    0x90c020f070b070c0311030325170a020d050c0703120f08150f040203090109060c0f0806150306060a0309020301060e0f1609061b02091e07020606010516020d200301 72
    0xc80e4003003a0800c1103900013071007010744108881e8412141d102d00069603002a0850081030800241517121240c07441e0082049000c00d201d440c85140100440c0c20f83c00034042c0503003d14903003d405139012102803c400b900800180c212646030304100c81e0a541c4941c0c502240a020402e420013060038000c078502800e411000c00c40d8000500c0c42c503440201c4c402000644442c0d07e00752315034002c0c0c4d40003010a8102c1002c0d0010100140c0105003800b01c0598006e00074000c01c00c20b158500014101c4004c40c0041c6000500001a180820001030851b1541420026542d20907910b8000f41556146c2e0340d401603d0a024050080c000180c428915207052801304144400080018400100e40e900400b43e0a802140c10810740d0200c2c0740180020b03000030110341980a80c0035000c4d6100c3c000c0410000e00c00d070b80b40d028810030300801c40b002c2031503140c1d10700603039507038500b5200240071801c1444030aa001050145c05100f0714002841414150055190b8010b808900045a5480b41c2052041400c9080034011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 124612931 1250 124611681 124611689
    0x120207030b07030b030d080405151005040b0411220305240703090506071202090a0b03061206130b0c22080106060e21010e0d02060a1a0907030c020304090c020f07 71
    0x424405204c1c0200002e40340c0306080c1001c418068004041418058200038001324503a5199200c9414188005c1061000c0050b00c9051b00c03550074805489160304050080d162014001d01040d0b0a104201c0001c111150000c1021080c13503411040c0003008c10000c000500e07440d008951054525500c82d14030000040008145030180341c01c00f00d6500015000045c0c440e0310004901d4120020341e2010036482c044c3c4103030060a54801c503880d9000c1843c0e03208400442c0a07080403034030706903507403200460a03841c1d0000300c8001014124400c941d0300420780c18030b022581300500c031105501d0703c1c2d00800c0c24203190803900803207800c80a01307507030522407880c09100e200040d0407076003085a600b4080030002000e0044000401e012540e503c40340000c5210250400700341259203c040c4d600441c0f070f00c44001d40d10b501c11900d00030014200b05e0f0100700b50441c0e840d43e20001001810303c51040e07403a8102607028002c000e000741d00f18801000002620403641c49102d04504131580900241001004ca642c503045640d08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 124614181 1250 124612931 124612937
    0xe0d0e0a120201050a180b04030b090105070c05030d1a040501080606101e14160f03120605010e0d020d0b090a0314040b0a18030c09020d050a0e0c040b0d120207030b07 73
    0x80000d80c2c1c008085d102c60325458a0040e58842410840f80e00740c6035250300c103c01015000c01c02104101000201a2048400304000c0081e03030b465400481b91440d425101401c590002c0216280511554000c0c00034410010006413640750b0020114041710300c00d9100c20f010742c025805110171483e0600c00e40d01c2984007480e02c0c0f03244000e0507544a00c0039603d2100c0c0301c107001d001c01d6140290302000c800e46822100500c49540d60300207508142886003500d002c03c600003885805034405544040c401c0c00140c0c0c5040c0d403a402403409580c20310001c8155180700340d80c0305250702825800034103500200343c03140800b0300150860203003e28000d05120008074481001000a102c04d01800c070031350b000d03590f0020051400c0304030000010716502c140ca0142d000074210b60a0b016000c1071800035500145214400301d0b50802640e0345481e245421584031104000d0960845a8000600c2c90701e0b4210500140d4010540b5400b004a59a1a017007001400741c3d400140e000004204113204c9850209580003076541 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 124615431 1250 124614181 124614209
    0x501021b0105030114030c060706060806010902040803030109020f160c140102070e0f04081b06070e0d0b040809150403061a01020f10050411031608100b0f040903030e0d0e0a 76
    0x11002074400d010501560030003050319070174021641c1c0c040105801049000d000f5541d28030041c10210090300c3d05024818007031080b0000000c1d020134030303c00c980486044038044c5045074240800e007000b0354441c42c0c0101c002c4c2d00500c41f0366030300b01e6400340e810b0316148503202c4440e41c01d02d0003105504130380022000038150741105500b0043c0760b2011072400e03403204504c01030040329a1030b4038040b03c8034000d08980314082102005d40b012030b01d10004006024079141e807244443c841e0500d0810103826406440100101c1c1d4034400b140019100c2c1c806031549060040400c1c441e481031032401e0b00329401c181c0c000e03100e90743c64482d1511500312030f041062a0f00001c0c4003903c0c41800c0401125a508610280907003c19035410004083c80a206c14013690110700405881402c0e1040c2d1041130501d072940524030f4103024039600120700048610402500c2132010b00404040702c2c0c0801080024110410242c00b4103844044100711241c0a0081c000e44984a40f903402100e4010b0040c4900862b807904003020b240c0d420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 124616681 1250 124615431 124615483
    0x60e04060f0e040317090601031a0c0a03091502070c17060702060c0703020712050c0a060806011409030703020a0f0812030415090201030b0604080304080c030304120807050c19050102 80
    0x180c1c140106444020341c540301c05454510f800c0310b100480d650051807031070880041c090180300c0805c4c014102c078064158400039038504070300f40c07403000c1040d295035030210410004008050300a0b041800b8171400340300045230540700072007480c040c0e80c003200c022508008140350038061400000c403420800c50042004021618002c003008c1e640b104003811082510b01c01141480402d8403c00c00e0001074140180d074401e41241c54070b48240c0c2c0d0350001c000303203118003c0341c403020581c00e06c01c0c05018840c210580d22561100c540660282c986d5012101f0f16425006418012000d40c882c00401c01c010245d004100d5900c42c5014549403d02062200d0400e00c0f0408106000c081000c2c0d00d40010030a040d140002040c600520040e8010481141980c1e00500c0210303001845107000310140042725900780503075110403920700415841c1c3c816409044250485500408041780400000e40361080c400cac02120f1440c0c0e07500000846407141c00c1c1c20140c022141c048140000d5a05201085001c280b15240e00440009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 124617931 1250 124616681 124616699
    0x1080102040806011508010501141e0a03050a14010b090102070306050f0601020d05030708040b0a0e0a050f070623030c0c0303040f030f0807080a0507020111030c03040201030c0f020703030f0c05100501060e0406 92
    0x412300c5043d040003a0300902e52409400741c81201d6507900300b000e01000b9455040300035006600400303d8900880c0c5440001080068980030b20f25440801c201c10300650723800c2c20b00700d1101d43c00410a0364110b124071880440001c400d80f150a0246011403045812454500e000a2410318102514001c00c60700307000384260f00d03070410756583e040395002001d17480039580d0115200082400031081042c1e031140e10109014007201283c03560b142c03c600d01c1174584d036503110303001915001000d50405211318002c1d00b0109a1507031000240da004400f0b840c0040c170340342659110034070b181c0003a501614003c98941c400010142c01c0041382e200c6c003015091400940c030704294084d00d590b000038003200355580c40d1000540494801c2d4000d510100d0010403007516030505a00789402e81e041110100d000c00c1c41c01d82e088010f18040d54000d034524802e0780c02410300c40d0442d40c04544c0020304402c2101480000d030b610b140029000d000c05010441400e1001415601d460001051540e005d141c0034081c0b03140103c00c1c000100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 124619181 1250 124617931 124617947
    0xb06060a0806060313050307030c030305060406120f051603140105070801082104081002040e1003151a0a03060207030e040606090b130b04030b040302071e050108060f09010801020408060115 83
    0x50b0840c1e0380c2c2e4407a80e07411500c2c105140b11410051075130100049603400c15030082000c500300c50081d03a0411250303487e042400100c52050190b2810b07400f50030a039100041c801c2e004060154410410744282045070804440e040002d50022190800c8070603590074802d40900c52258411494a840c4102d54901001d240c0c44114510382d00c0000c1c680e442c2034042d403840c0c0d402181c0040c07a00c1000c481181c507903100640000d4200380214040d140700302000ca90841740820701c840a40b60403440c2d1a07951107090134541c1c000c1010b81e2240203c2909004181e1041c0d482c40016001140910405655403016240003062444240c141a2085142000c00d0043d2781c0d020031603a00b03481c00e608540f41e44080f490260800f2007520392110700007010001d0088200000344440c94000c900c25002c40c1d00c1240c45010703451450080c90500109407a801004200d15031050484640264000e06000d40760266400446c032142c60076081880303942c2d000102084400401c00606004001c2c80510440c0c500c010880180441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 124620431 1250 124619181 124619191
    0x2210a060c082e2409050607031709100c030504020306060d050d0f110303010815070201050705070b060d020d05011d030f220f060e040b09191a0301090f0b06060a08 72
    0x1c0c0c180030f009541c03890204501c0541501e0701c070a886820a040c8500ca4240c08070b944200040b1176040005103800c0c440151031120342d05495240c80f510402c0010301c14100b006000500c1840b41d86000d407004200d030b02c2403490010300c1c2c0d60042441c1c605401414680040a04914080c0401804580118034089000b096841d49890002000d00b5a1901142c0481c09001d0418150100000000705001c0018510741c010740400d680410f1582c0b40070081c0e080390341c22901003000c00e0041180c98002400c0c03150050340081c00514444181005d600480d04200386140216805c0c0e44d61900c03d40c0007240c00402840340c00942d0002c40ca00342e03190072010468060822816000354a1902c01d03940a0707180b80844000e41207061040c0740180d030b6103800a0042c0d04031401c070f5000724504070850010341090010349102d4440104420031703080c12081c04c41e0050800b040400100e802510314840b9a40c0c0a000ea20340703883c0146184000c00d24182000b4641c540b01070000341c030070307001001014001500052410303804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 124621681 1250 124620431 124620481
    0x15031b03140d0e1011071707060504060801030609020d06150810020405010c020d060605030a0812070c08120c0f04030c03020a050609030d030c090509010602030c06010602032502210a060c08 83
    0xa0402528207560a500c4c003040c04915020b2004082182c24000d01d411f405614071030200e826142e070740c85007030701d5030b2180d40034039400649060010b00215000e5040784141d9480600003e0314644203031200030441d910052001d2030118596001c00c1404810044c41140e24001c1c64110325143c50300002030101d21040600900440800c488082070102507403050009003400345c01c0e0b0342d0b00303251403420749201d512010100440240404c08200c0461140a1030003945622191103403611050040071015000024501c080c00582001000740300c040d40300c043d1000314030941e0381e51480c0d070039407041104a000b2038004600a04040c855080f103580c2c0040c22001c3c03030300c050400140603105c200f000c8403041070a402041c2c0003411880001122940000180440034946d0b00b601c07503690700d40408a03141d00c0303070365407080203002d50201191106205819030201c440c402403440e956402c070b941280542d1120001c0c6000c207604a24034510500413680a88440d5000c0c070300c2c11055525080c041c15405010074810404c01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 124622931 1250 124621681 124621699
    0x80304050d020a090e06101d0f04060b030321161b05070b0f03010302030f060910020c0c04090b06130209060403030e0409200118080d0315031b03140d0e 67
    0x15034490f5008500a00304209082c0480d130320b10109a5681d02d02a504543c0b03843c039903100055003611131410014942c050000140d0300740c030f507054051015031010b0025540e2981c0d42c203503800301c1e0360708000600f451070b010760780c0901c0b4018540300004408001002c424030340303503141d0100f4242c81c2e00c01d46444001c0c0001c03c604032a4030031420a145030016030340040c0040c540c0007840b00301854150340918122072085080314108840910b42c15103600c0c5c01e54010360307281e0181c0c1015075100c51540142c0419583d180880b101e8031114800a4295504000f05540e54802c1100307202c41c80c180034054890080400c035081d45030421110102e9454400ea03c80642008040d4803a581c0b03a58076a0055200c030380d0040d0100c03038443c07200c0010442e412285106280480c0c3c241c441c0401d40301e084094001180c80400103400c412239004016000760042101c01030380d00c4901e03000400090719814442c805080d0441c0201c1296007145030030b10040e143d02000246991050507440010303948102ca000740d450302a114030903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 124624181 1250 124622931 124622933
    0x6081c05070f06050126030712050901110709050103110306090703240212071b0503030a05090703050d020304060e0a050607030f03060b0a1218030f0804020a03081801020d0207080304050d 82
    0x100b55a05420040000e4102030000402280410192840d240403006c0d0311880e0b011241140da507442411002014520074900c100c01d5203000b9806490b0155040c1801c0d00511803031505a41072003210781141603602d9031180107000b4405440c03000c5503002000d50042002d82400f032034199451a07244001030480010140340f00340010644002030014516000170b54490a0107c1c850013840c0044500c5000140d01d1a04410100c00006101c219140c11002031803954940200100151600421004071403040b8000040061010003400c4420312003540695221424904010180060b460070648a0f600690040c080d60b070b50b05003201c2e43c00c0d80c141481c1204500101d0294003400035540503404220002c1100c0300034981207800600c0300b5051907400c02c46040541000d0961511625001d000a0000f620f038462183c02254900d401ca070005141c2003110740e9a64480b0f000e80d12403607951001c2285400507900729601007004040703810b030741d0002d064201e080608065070b90056119643c0701e06a0045064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 124625431 1250 124624181 124624193
    0x306050705040e070e030c03010b0f042304050330011401020a14031e1305100201141302030606030a11040906020c03120403110604020303030f150901080f0106081c0507 74
    0x1d0007000c02191510103403900c040060002c01031244106c0c004e00030003070047d45610301807250319160180109108440400f41040c0b200030260a13003804085085501080c0b040d011826400384998030902c002e41c0d40f020a00c048045088145500a04414418910035042c40654603024113568641c0003003284941d061004074909800206c0141c0802400001828240e02c04001230910301841815580d00b1820320300081260702c20001c82c890002c400040900c0a0324003640d09100200461001040071490380d201009010820b86410502a00003052a001c600301444040c0d170041c42207000e8503c40c1200d03201c01034041d541c1c03003e2501c13483e61041c8200030084280e05580c01141d00f00c046903110201e944035002400802c2e03e060740072900d070f9800f00342d820500080142c4601d5014028600b0f5840b94403c030a20000c1c080d00b5941d4811213030000c8856500c0350940740d070080201400810000c0700820400c1c1c00c50b411a00841010b8000c0740c903802003002c540040500c60700003860110394030320081c1000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 124626681 1250 124625431 124625437
    0x30c0d03030b09070306170c0303040306110d050f0708060603040c1401120f060509010b1318060302060c010507080c0a0207030f020303040e0f04062904090804050d030c05060a150306050705 83
    0x6940041c07403001340320045905a04c030f103080d00c00f11a01d1860b08092043d0b41e5954048185543e83c3c0b5a008100900000d116a000203d03100801d56299003071164000100f41501c004441ca00646140c1c002005140380e40440003941140080c0e40d206d1071030900d0b455042401c6504e0042c1901c1c00c10b03541040025034820000d18081d03451035541002801389000e0131380041c200911a0901c00d2100070000301c0d40d000307004100d03242962180d01d5240068608000708804070307040c5442510803030341c803580000983c40382c80042c6010100140005114540700c0383c064454003024160000b1170606000c8040111b40000f80071058a070821482402203c184c4002841c0d80300700d8000c0508540b208051103c206c40c00f405d22402180f10b03660501100b00000800c2036504010242600b140c81d044400e440c9606007603010039401401059003500d050344031804a4034817400803400b200060b1024804105200c002d000036038000961076018070015010080030f92400106020280426035101c021600442c000d03011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 124627931 1250 124626681 124626701
    0x114120c0405040c0809010b01171503030706180614060a050d02031606020a030f0201021315021005070c03080c04030f0201050d0609150321140904181410020702030c0d0303 76
    0x30a1040413039400001740a1002034031580780300c1d8200414001150b0040350200100d610800b42c9802c00e9441e00020036000d00c0c3c081c86e241e0103003c00c000003c0400c003103000341094070385281010301e030462045c54a10102c2d68000d07203210650640205004055450b6901e01e400c03a5003c44001c600c414032400060706080c2505082080401103003000540240c02086000955001e61221020b401c10490180e00303034484c4078400701c00b00d4080d02092040c1445520f042007038110b05e2044620040800c1e407041c0031940c2c26200c280101d4901c120010030141d01100e81540700c210020018289490359680c00201048076100905115021407a209204480c1c1d01490041601040602010380c1219585400d40da05000c2515140188a170705940d405080c10580c6d070380501ca40c2c1d0b443e41c11603203110028007034100326041603101c0e0711249200110240700f0782c0c101455005020b58000c3e410700318042c1c2d14040c8802e09408030680144250b00160b0f80129440070b00e181c0c00e40351034001c10700901c0d08034011300e02e490ba = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 124629181 1250 124627931 124627939
    0x90402091302180a06140a030c020a0c030308010f080a08030a110f030103080915180907090f090203090d080408030c0706060321090801110f07031817010b0114120c0405 74
    0x72140f400142500361206140004d4421184060311414201c4540549440c004c50450b810080c400c211417007030307201100501c1544117590142c80035656824102040342c1c02507000620210051000441c1949900001e1018038000c100402442d44c5004542c00014200308440e507030350f0f0040404800b40c40803601102e81680c080e0717560350384a1409203025080001c0d500c0c0141e034102d64070749644032800700700c552080503030111080b5400d10004204407203c004103502c040001c03000c0c0001d0115075034003094014200912000d40c6034500188103d20700282c118001c030030400c000e003d10001c00c6012040b650044410640b150f6100c816041c640060480342e0320042c040300305000c00841c0b10b1020229888aa00241c2e1801c100c950b588031072034241c502208800034030710010424002240400401002c0380d502c2810012018048030307a460300304144e554016018010784034100c82d201c15080c40f89489290302401c0034a1b40c080c0001b000095405a58584112801c0c00c00110348101a200150380091000070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 124630431 1250 124629181 124629187
    0x30703050d0905060906180f0616050d0f09090c05040e0a02030609010b1c1d0106080a260d020a0c0501061806050a0308030403180503070e090d080c090402091302 71
    0x450041e556900c100c1c0071100003500410003207614504402140c54001c0c0017041e103400d0081620208100845500c0040c0d030007020001c04201c141c65040261400e80000d01c03410480700b03900d0510030304029848070801c00300544001e10704801c5410110750000d550710080300164110080034196098400e0b50070450004100108011005125800075440784105451580b00303640d03641c00303404950040c400641c8804400100c4c09400300b078141c1c443d00080c01540b001c000203c04e0b0044e0a030854000b60411000d42d00142240d206108100c92a42c10389452648000940c03403070b01d0020007440c0901ca203d000100c2d000a5480c1000d03108040e5110040d8111380204030a6a0b20701036003003002c4180c0340300200c85003048030004040c40d0410b070f07540031a500320741414034668655500f2100a0107498000070780d01c120110206058400700700300d0002c1c151901000486082c4040c40717525241d52000701c0f4080000a00c00c00030322244010036a0051001618090b032240d4034180000c00a11810514000039072000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 124631681 1250 124630431 124630433
    0x203072904120e010c0312090305250302120a0206130f060f05070329011b05010e03070308090a031e0203090301020c010c03050f15060a03020405030a0c0f050105090d0b0c09030703 79
    0x410500c1c190b0b444542c40d41e807032101c1214010343c0c480b2241c0801402046400302001000c0d081c47d000000d03098864507140d45056903440001081d08000300450200c8034809418004268041054100c62455403420a00346044200020b6a40d180100080d4241078901d101da0704021000c0c1183c0d000c680d00c418184000c450901a10005020841d05100000e0412040090545510940503501c083c4000f044004071b403000d00540d9524056543d00d113415400f14002000b245082c410702140c07028017009103a481c0c0342d030705004180a0001c0c11045d400e8000c01d80300310000b034211a00c07400c140d4250004651740d8200540c160305500940081c00c2e059400080c9440010506511010700c03101320703803410080d50f150003610440f01d100446102c88514042e84c035000032850040040d100d02156841c000d807826480e8404242002140c600803202d62003090000d1180350311a46181016000a20300603042115840000710b49190041001e8403110000010540122290741200c0ca802006000c5403482666 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 124632931 1250 124631681 124631693
    0x3051b060909070e090703060303020c12030405060a0306050114040806041209150206040b01080c03060c070c03020406090506090f0915041b0e0f0a05010b0405090907180c02010e0d0203072904 84
    0x41858400c2403024006081d0302d01130303c03988049e01e0b0141c0c01464814030302c03414401e8203001d1800454451200b800002403650b076540082030008070560300031a2580c41c003400500f0054000300d500c2000b43c401c0c8400c0c00aa04000b904582c000d411520b001040031060300140c80300045504498614421031100088040e00010701600491140034180c140c0c0e0780c0c07180e01c1611070f141c0b4440f0b2a81070f007102d0085a031100c20b101c00303420304a006816201e4150380e2580001c085841c55441001400d4a910400c919440c0895205511000d099410030241c81e010201544850000070103807400b030380303d10210307040c88846041c00803c15081c002c03001c00c5d0307602e030144440c6401007100d4200e0b5201075000025440c01c0385003e251304032001140740c541401c0c00d020810000a5005100038402c0c031a09000203200080c3e201004482d81c05040000781c800c606010090030344d040b00c2075803102c40e030294461090140e030003c21035000d2034200003003042d01c01c1c00d11401118220a020551588d404100c244020320003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 124634181 1250 124632931 124632947
    0x1813030e04020327061b0a11060a0f1803090605070602040513020903061005100309050102130915060203040f050603041e050c010908060709060e040b0d060902010201110403051b06090907 82
    0x40885001640c00400e107440c6030742d2501100c06c4d8400e0001c0fa0405003e0480000150074030003040c0c01e20980038124555000d162000840d4146440303600c802c40011a03c1d00c0c0e00c110070311071151000d01071041c40251000b41ca0034540384121010004009500400d0094640c1a54040c05009141866102841c01c3c0703007000c0d4000000340d900c640a904003144044450311010012100c0c080c1c1090044e40503064258000c042d0003d085c0d6995408202c48140c03000d03502d5013440509000c810000340e0100500f00c1400e01c852380d4200b4820740d4400c12092125203030001d0320504866044030381c1c035681c0d550307803800d00c0d690105000b445006451801e0f42c242080008901400350100030790b50300103400d0b96020a2603565109581c0d03100828804901400101c0c0b00b13003100d601c06c50740600007144002c00707c0081041c480190074140c643c940d4030501c40c170841d079080c010502d10340c1d8480701d00c5080ca41191103241d103c0c040c2d0701141c03a880c0040c218005450303d40f041136a40c045da0081060b2810300c1d180c040581061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 124635431 1250 124634181 124634221
    0x3010e0612070e040602130302040c0804030f030209010504180603080403080c0606011b11030c030a080d18051c0306380309071a070204090302070609051813030e040203 74
    0x3403250960607881d20307002031003504035522050b8410300c944980d21804000d61203c0650140402c0091010000d031326640540d05408195582e06000d0345410b05008040e21283c000d55001c15004000c0107070366a9101051342d003518801003141c214a450b4611a4004158035400240f65010101d000010701c41d11001030f0840841e0381c420340d6629a1010011910040c28103d10400a00c900081d0307004965a24000d140200015045400d242c60041c0024a01140b5060480c0c42e40d02c006892082402140911f600c1303103001400304001d100d070541d500b64807802c2c65051841401c40300c4520141051181d000300c070042c500b0b940501c42d500d039158642004103402d60001403211060071074104a01030290708036031288040c000903003009401c100d403c07030789401425001000e00c8418042c61000d43c3d554803690007082d104c0d4005050491805902400d801c040f6804584688010124018070016041c5103e9201c80c1c60002401e01d0680c915090740c0700080b40d0030054005101200b046891141400559848 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 124636681 1250 124635431 124635439
    0x70c08030d0b03070f060c050a0b01090c0e04060509070804051203011502010c0f050921030c0307052e050c070c2306030115050901110d02070e1e06010509010207030803010e06 77
    0xd84002c1040c15921040d80c892a0103419842d0300401107540304081140e2110b00c030341d00ba103d50038101e445035582020207070422080d0399030703c2d031101c840f1640044054152000c10744091011520b4000020784080e4000c00680603c80c41000040820800380090a0210503440c03001d82c0f2561500c8840608290415510000d9071a10102c000c4441c040c00310702a2070a0340e5a182403032700749403c6c244049400a4100201c0142084002594144040c00a0014411640c00030354440c00542441c92138a105160495080c1c901c80b042d03140c44c080f40c80d4502c41c0284c2c1c80d1001160503103074912682902c0c802c20101520f15007850102050b2006090550a42101650000f54940c0201401c010440c0300c02e100d0810384526050000001c00c2c001c1000e02481c0c441414540280c2d0b03210041c0c1818140b594141c02e00580015034280035032070308102c07500d40144005001c240401811203008049400240c4801c3c14800702050b8000c80760b10800c0800095030384000384e9616541d540810200003041030360100d1003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 124637931 1250 124636681 124636691
    0x1407031d3c0606040c02070803040b0d0c110d030506010c0f030815040b0109051201060b030a02040e07050313020405060604150504091107122f0303060112150308030903070c08030d 79
    0x203001c0c400079a180e5840d03050809058140c40351401c02000301512410281035010318030f030001d20711400340041c0000344800e03c150703990b034040b15000000701e50142e000345040c841c1c3e441002680700b000068491b0303001ccc91418009402d40702e541c0142d41213401504020300c0c600070a040c4004055000c40e2540c010600b010062850001981c02c01090341c11100e035050020b80082000c1109107020206498080040000040c80c0f9884081c9111a648110341c8081c0c000e80010b405c100d4000040c2000382e100c011403900509501f0140740329407151803480d0000c2c0c422a2600c0110300f4940e1000115802418050a007014100744544080c0503504a40300341c0300802c3ca000c040e030450550240031541025404110101c11501091702600c00c2c14104007002c0c0400c103022401e40540d034001c3c1e0b41060a01d401c40c010b42e26458104001000011007100d002c4445081800030201403d02105003001d60340d0180500307880307544082206141d406000800703800601d00142c0040c030300102000409025038450780c00d01c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 124639181 1250 124637931 124638013
    0x1003031d09070e090a05071b14070b0a090503031206061309020c0d090b0c0d080a09061401051e030d05090315101805010e06010c03021e030406030e011407031d 70
    0x170841ea01201c0c41e0000c285001100b01610210260401e070b1203100d41d444a103a4000d50540c1071500310150092032000b000007605009558001209a001340707001c50085250284d50b03250114020005084940034480100d10111a8803444036804090018004110744800003081038503502d01c200c80124020030b0924002142030302d00d0300c084844900e061401000c031101040421194154002c2c44a40a86d603100044400101d8500400048880921410300c4950403e000c01409050810f0b0034401301d08054524240c80c1c0f00480d141c6410034480c00c01d29110344949010a0800d05661203403803c0075030007410883c2c90200c199003041500d80139107400300790f80c0c4603422200c2101d000303006030360b098a82c0700b00140316076108005c0751029500c039105503840001d01d0449281c200d2a1010784041a410101c0c3c00c1c0040b44c2e141c030503803040c419a500203004440503000d0018603454040c120801f00b40d21031400f01d00100c00d003130107900701e04900c0d0304940c0e6200d60300314840194402e105510302420441c10ec441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 124640287 1106 124639181 124639201
    0x1101082206050f0106020607090302010f050412082a0a02090c091e01080a060b09101403010305010c02060601081611100c020f10051003031d09070e09 66
    0x4100b6041040d44024034040580050085601240170000c0065001d8214803c407074080c28812410708840702c04a890b403040307030005004407035414565070070040440000c101242c840082035002840903011100d100e8400c0070039041d1039004c20348000c0549071080c080d0340c101009140492038103859002107a044040c1540c00c9074962030f442401252540c020400ca6441803101104100c458203051120303000d80513000c00907005240300790303014004034024010408100300d0380d01106d8880d80c5d2072a004d40a0500e20b01400010701840d00031074119402409039a00804046804400000001d5000c8030f03d4600500340f000c2510070010b0800c4040e02c0e41c032507240f0f800b115601801840c801141b00515144550100750b610603d44410808081c4903100c03044203890781850320070341e01c10a15018064505040c0e07202503208580c2c00500442c16000701d050481c0d02800eaa00c0c8850303a031442c00b42 = true := by decide +kernel

theorem cover : BRFrame.Cov 124460431 124640287 := by
  have h0 := BRFrame.cov_init 124460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 124460431 ≤ n) (h2 : n < 124640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
