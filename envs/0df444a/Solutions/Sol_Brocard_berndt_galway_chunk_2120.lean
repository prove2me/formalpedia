-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:54.091802+00:00
-- url     : https://prove2.me/submissions/2d21f834-cdf7-45d4-b57e-8fdf2e5632ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 381115107 ≤ n < 381294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 381116357 1250 381115107 381115123
    0x1003050907050d03120c02010f0204061d0a060c060b0d0c0b03180712020103021804180203010e212b021210060f230403080301050a0b2706090409060606020d02 70
    0x12038a6201d81c2d541c80c5d85198400c01e509170a6000114204509044070340403130740103400880219130620741c2c91002c8208450a0044050180c0307200310001c0c14540041c204090f00b42000740700701c0c1c03a8505e040302a2151011410344a5006039680b10003920b03204429115002190f0059600d44a412440081400055180b003169030102170b55020701901c1d00114061760004d051001c0c040c0742994046210744607482400340c4440c8a000c02c6a1030441031040500b0754201824002c0c0c01d600c941030601d0240740b20445020f4465064507a2543e800d009541722500601020b0b0184095480c20a082d03556403042d00108000002c0710300301403881d42c400b00059021201c0d030240c200041c50340c0000102c2c40e40190384640740240b0950500601e44080ca60030105c0b640a07400c102c070341150220042042e03080c024010005131200031000d9044c0103103001004e0441a282c000303a008070752003481542560f21508210f960681c0090f100b8002e8200d603040c000c3c040c000320b20a2000611800c840071050358400300740aa = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 381117607 1250 381116357 381116363
    0x100c08150f01110a1b05040b030a170313080c010b0f190e10050306090a110913060f020d09140d141207050408070305010c091719060b1003050907050d 66
    0x1d29040d141c00112001c441d00c4042c039140b40701da25916070200d814200900c41460840549405c240d0412040c4400c0d603a00c5600b05020f544140d0814000030350038103000312150500c04507503849640b04003040d258130300c800b4805400210001a100c48100b010342022544c1304003941c00302201729608042c0060078054408811403208002c800340030480038a0500380c1c0001e250032040e81c201d521400040d042220613600102240e018900b03500412519003a44650060b08940b943c540e0b2408094441f5070344840c03003000f08002d075240c01510250780e0b194107844003400d00d40b0b0200181d40c0749144c028103210014069500600c12500801d1640c1d11502c810b480c002401d2044d034bc148034034180c9051000038007510800c1446800e002c040381c030800800140c0003d500400c004507c07003000070b82c00f40801085800251f240e0b17072461018504400009201c807103c480075850000d18070428203007140201503644c0d400b40e20110246001c40c40705c0e0f060300018010000d500684004c03a65400030800f5441c0c5a020007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 381118857 1250 381117607 381117619
    0xd060b1303170a081b30070e0a270504030305090601050a05062a06040f121e0f180f03020406050306060108040b0c04030b04060606110106230111100c0815 68
    0xa503064074500003005c41d10390359881740c0e0614070310080501c661301d410444051000c0e141d45040040c510381c800d550381c1203015414940da0101f0440089802411a4010107030700d15040700032a2803a0415032422504c1d4252400c1c10442801c140c6802405044142d40102c1c00f4803800e800400d09240001d1b07800100d500c0107112910341244c112000a1a4465071400070002c540086030068005090255912880c418070001e614501d0320314000e9948425101c401e4100103084a4a1a9040303900701044450049410325141210019400b1a01c03c800c120a070b0311003070351104000801a007551107035800c0d03d108646c280149500c8405042d07a9080c126007107800100444045401f01c0c02e84180590403401c0b40540e289000d850751103001e5060800e540c2200c6080d034502c0300700b050070351111005202a407110000c3c0961303403034440d00301f80c1184d280310000c0340008100100d501980c0202ca018940206070400d840c4011000034021008100c007280380c5002c60142c0c00001c1d80c582032284141d00c5030b40c0040c24 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 381120107 1250 381118857 381118861
    0xc071b051c0501021303050d080f0609040311030c010f060f050612221208071d030601170102090409080406020706180b1e0706050115020f060109020d060b1303170a08 73
    0x1800c501c80040c01e016074880d5801c000c5800c42c04108070301c66000c0d601a100a054030400e881004210100081001114000203400d000841d601c3e00c1c8500c2d0041e0701841e043e80000c030721a001505600c40c01035000360f1b640c40c1c240504c00c00d4000e07030014000c80300442c100c41c181540c2c036818001c0134070841c0080c0e001400e0400014a03212403468540e11498504640e4201181042d0703540241002c042101c038011076420f40c2004481da030b1140129502001001503005000010030100e513850606000721400e1a40d452459903035400c00b541983c5503094028814030410300c40d41040d03016640300e4025480140103080000c21158040c25004080d96048103c1c0185249411070101c0d85410444003580c1401c00300e4040000090b030b40c5c0c040c181480c014100011154544614501002280c01081081d5003100c0d080c011444070103d04e583c1154881100507a650412b10300f40001002036401c40c1a5000e000305102d040e14141c0e05503041501d100303100784000c402c41e410000025008118455002508100c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 381121357 1250 381120107 381120139
    0xc09150e0a11030615040806250309050a0b1b0a2001090c060806060409020408100e0c030a030c0c080f060a0c05090604140d080315090f100302060307050d02030c071b05 74
    0x1d111148201d2900c00d071820952111070b850b04141040e2040e27080e00c03646140024988400048800d04680d085c2020059119560b0329642c4560464401801c3c1c40e000100003050100000800450907840d04001d641c1c0721108070300079214440842c0e50310000c007241308082e020681c052092207002d03034204448111461900c881107030b0b030520051115820070300030b110020b20964580081c0010f00001c0015000c8103407003180f89006c030380a0002140180d44003c105200584011130303148082905031600ca0140c64540c01d014000000c1c550043c4103510031089815810344020840c603015080c00c00c4107009450314004126418040d82c00540e501c0441040301300103c4119104a00390000b01400d01401003009442d141d41c00d42040300c241c0d20450241020303228900e00a0402c0c1e90202c03401c4009405800d15901400c040303205800000d0081000201080000b4090821303115651405002075640b40340c03200c9000043d41200c8000c965400380d0601980340c1c1c00e1070304072080c00e031480036041d1098003005035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 381122607 1250 381121357 381121369
    0x9110f062205030d0309020306061e04020c03040e0405030909010b0f0a0f0201380a03050705151b011e1a0112021e090109120305160c09150e0a110306 66
    0x100c02414880c40081d000906500c040c0016204280d00c4d4800142d402030034018142803410081101d84070709411140d4070380007601030401c00b03290070040d00d0050700c40f00c2c060100b518600c181c3d0000c0c5550300000e0108001c0010000c002c00302440d050b100c410300c40c4d90780d440040941c010b981340455010300c00d0001c010b81c1071044200440c0d01c08240300104121a10340140300c00301c840d404103010b414035a4034102d102038000304030080e0806020380d000941c0b9455a15400c0d2201d2840c05168459202401001d40c50a0b518081d11109505244005819041102c400d8000c04174032500c0c084d04d05010341154610703059031080340742003210008a1001e400341e0b500112010b00c400d8180314401a82404400258a40c00c011425442014036045179201718140000d40707502280d91152403040014000b074000031781d111050b11340c500e08801500808003d907103040c0c80c88107041e401c51a020b51520f4940241403115035000f50403501e0400c2948600d40754001a82c0a5038078140300503c01400030808540301d0700b0300c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 381123857 1250 381122607 381122647
    0x501091a0904111215010905011b08090a091e1811150406050301090e01090305071106070f05060403030507021b12010f050f0403020f031912060306050a09110f06 71
    0x40001038070520143c002c080c00d03007008011000e0582c46100b0002c82c3c1c0340850080000701c03400d0800d41c0f0042e203410002801d410004881211003503680b28041f04002e800400d90344000d000411100034180c648200303000a000300c0014401400e0a1852807071201414443c1c0348211a0a03900071780140130a0329061400d0340741c080031a0b048540c0314072810f4280d5880c40600080d100c0d0b9543c641d07032940350110400581c0c441c08204405c0d03034501880900001c1c4c201d402c075002c01d42d00089240c41c110744d0400060a43c081c80b07101030043c1003800540010058085002d0780b06074826101003141d03031034502c0f08030307a251002022190b0909010003461900d2a081302d0301e65603011007074004030703458076103080c44021b032807003516800140c4c50480c0510003056010b0001c40c80d2046108021402d24103034514007460060031315010401e0098980301000d000e49203402031400382d90400c03014800341c10300e507030008001c00c0d40032801d40d814101c2400c0c51070382d4500714000c182d05110040c0050f040c8800003042000038011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 381125107 1250 381123857 381123859
    0x20a020a060f091709060307110a211d090a0e0309180103030908160b0a120509032709010e0c0408060702060402040608060702101a03010f02030108070501091a09 71
    0x344100100001e1228061820b203140798410100e00d00c0c00310300d0a883d2003010f501d030046000105100d20212a140e2005603a03200c40340e0701e0020442d0020010880c24a0449103001c0c0040090b05040e09500200310141e030001e4585659010940c0c004844a0380003070a21620581e02c9403901c404204005010f402951060b00c00f081903d180401490000e40d0b0264824a45881c141e4844010410b141d0090320354001406441301801d500b081d003401c0c41c07070540b4590103480c5602d0004182502c403207203e004500041840c22070100140d0400e40c41d07042c0c0c1e81d081550129924918540c403001c41c4090071107200c25049010f40000516400c0c60a51400c0c988000c00d80d0403007440901000502503001c0007001d02030100d6030080c116a0405005000642c0c010340c101d030045502c00000d01c04115170004841c088041c3d01c450009246075228800100d5804481c50243e02d90b00707002d106180d03102980c0c002c504a401c4481100d41071503a0b02c006446a40c10b0b4841d00c600d100034980c4ea00b540c00702c1d0320010702034100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 381126357 1250 381125107 381125113
    0x30e03100f060e1807030f1103010c021c03090203060408160506010e06040c031a0d150e0309040e12030a020304061b030e2b050d1103091f0902060d020a02 68
    0x16228100c12a84101d06a9031910b40390601000340106900c01903401540c403040000d03146909600710b950300c130b0340d0784001460504596990070900800041c6202d000800600a01103940e2a440003990381804640300c460500c980418803400b04d000f403203442660f03039016018001d80d98842e110040181c104403101c1d000031141d4410b8400280301403112501074410003281743c03060b0038158241310440e51006a200706162030900c0c0c00000318051b84001c0d806d10f00c100c5170307148817040914289908500c00416084014200361880340c0d42030011015220782c20b020b840030000c0c840c408040996404160412445483e402c03c0070407041c010175001907500c01c8c0a0800810103854041502ca03009080010080000c0e80d201d100e03254050062018200c000b0f5545500707010b800224903030400410040e1021010b00c040001d088516100580041c44c030710b0b1a40ba90a9240e144c141d85003611803103070001c26003880b0354a041058840d0124800c01081540140005081444850401d4000d5120900190a501c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 381127607 1250 381126357 381126373
    0x1c0b0702011d0a03200a03180b1303560f0f280203010512010903050406050a180b040303022a0103020a0e0d030e0414010b070f170403030201050f0a18030e03 69
    0x30704200c1440100d21a070364240040c40c610000b90f01501e050b809c112940007040112a03007076507145900b803017071b039410a92000010414428000c40e001d5000d4003001c2402c00c4595040740c1d81c0340c2c032240242c101011940c1c08040e64650002b003100034400c4640c066142c10b031002060205259044490784000b0a9010480419482e41207040f03014042c4002c081154000005016a04010141c99078140d04040203000c1c01c0040e075409041801203014003020001c0c041350a0780c3c0076100c1c21403035682c0000c50307a8800005860f2051103c0e1030b44103010913405482801c40c02095012821f0f9606405610300c45842a103500d00c0c001103020b94001008041007200f540c6045c40507513141c01230b034480030303200b13494140c1c8410400061002351108581090246001400100900360320310048804895103c104135071104540d25201007106003a5038000441d03240444c001c010140c056001038003070101040c44481030f80d181251041a40d1312488142d00805441c03008500090207186148040080181568042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 381128857 1250 381127607 381127667
    0x20a0611030c120a03110a0c0305210a06060f020609191a09100f060f052e02030307080123100504150504050405070203030601080408091c0b0702011d0a03 68
    0x8258076042400000b100050300c84c65942d014841c042410180d044128101840ca60700a081c0180b00301c80642480000070344800d02406404545a140d1850401c030041030820000c42c60092426026010214481c0820511f103103000240e01031040c00b06d403000308045421802050350004e241401192036080c480d007201c025458600405200724201c80c000c120b8150307000545003e0b10002a010700da80740c50103106014a04000395000709581e0140c841802c15207024858420b0000d1050b45901806a42d29603041001d60100041d170103450255906d040c5a62a4006101c22000b80c0c0c0805e900004c121258801a0401000801b44418070741070450410303135075000050001c82d075a80b40000280d0001010300c410714262181c5a0810711510045085152004c00038008010141c001380c0040b0000c00d00c0000c0c1d5490103969002d12200940c06100340c98146004803600e41c0903075401d000f65082c00c00c40000b00100d504810f80301200e10006181c2d45025480c00c1d90604150503d880407482c8000c0b200e202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 381130107 1250 381128857 381128863
    0xd151e06090902010e15120c04080307030f0e032a0a1e03060f060b0f28030204091d1b04091a040b0703020412110f0a031101020d0309020a0611030c 65
    0x6110324140490510385034400107005c100900c01d0240300b1116100d01c07040360716100c020b81310032100c10086184951107503581210603005980c444142c5e8400002c12100301941b021a20002095a444a005400300301080540720702c840014204c2140b001c01c01400c49005000c2940c0d610340c800340200c40102d807209000ca80820b001c0c08180d0000f0080041041040164800ca8017035940410b41002a03600b402807902d03607440380e000745888405004c00c0e4040d246440354a603040300b080e032540801083c00b120b5405006500544500e10070781d4a08085440840c1081012145000c4240090001204030185081085001e0302d4200e800a565103000030000d1081039040380110342c2031100403c03a2600340341c507003503008004000404240c01800b041110203145916160429440000220a030a145011814040780c00140740d41c085000c2c8000820b20280c400c4052401000781d007668281c4001e0034003681501c061403402900104111b4040003103070700c240d512100401d00107096030301e46401c1210b100d00d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 381131357 1250 381130107 381130109
    0x812090f10050907060804140313051002030307140c01020d061701060f1413140414010612030c02061602060a0201140612101a03070311040b0d151e06 66
    0x4503841000031000502042209500c0d22440300d00500c40707440d1030a001a01d52101d4800c00c01030128070b001040c10003204540700e01010740c958003200e45810174a00c4028480c10a4403030a4000d84c810494486c10500c00b00840f0300c00c00f5503841d00c1c94a540008502e42041d40b010101e483d032550700340883c0c0c00c0001140039100c01045400402407a2a03140841242100e4641d40150310791026080100308020030b60700c101110007421501d04082231400f400d41d1014010741c02407000480400000c000c2080000440d8112461012008010203a100c104036048007504080c090082174000400400511b000c00082c00c0368004659120400035071030340801c0c00c58100d080301e40c000d40d459005c00c034110740302130604a5000f02e00300c9407402100d0311039020340e46840b08a00950b5803a6183d1a581d014002c0041f852000503074040c0496004c181d0301e0500031801484c00d00f80134031581c2402c00b5903016240036450003030401d13088260002c000f00314816200003407619104034000002e80540c025507056080c4a6a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 381132607 1250 381131357 381131371
    0x210c0b0a03320a05071e02030a0810183303060506060a050f1b07060207090b030c030d0f0311030f09010e0a050717030403080406170903120c070812 65
    0x1045200d86600241800d8202e00c804003240d0114100c40c088101400c070381c080e00301e9060407001038181c8907403030700710755444080e441c60a0701c00c01c00900c4031099500000a206155156448071025210700720156600d036103070f1040014400f0500d074010030a0110383d1200750b4006c01161070000720382d141031202400c519000000c1e5004042d800082040c0081802050b0b408481200c190b498040c4100c0c1c0035003140208401c0c0c049046002c106071035005d4050400b07100d00d080880c1242c4074180d03603440c025540ca0300d60180d5803140c0d081145515050400040031900300b4002000740600c17a82c121401c13140300070000c44c500101610350780126150040180298016583c19544032041c2c07520440306403d4450b2418201c56a9201034000e02c081600400c1103001d9800380160441d0803044420715a00d140602d030000750034903d0001d000100c180c0c102d45100100300d043c40c203040507660348070086030312030090107441041e0000b1003000a03e00c50b03900c4020301c41c2d45d2040c1c1c0302504051044070034110308007040310740b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 381133857 1250 381132607 381132611
    0x1030203150105030607140928060c1104230421020a0b0c03090705060c010203160906020709110f1201050405130206180f03030703032301210c0b0a03 66
    0x1401941401d0040790184030600d8280304655240c58003117035481400070020001c1081c0329498514150750341c400ca505a0f00b004202580103488882c40184200851603140fa00c150003c2001514500450103a41295084400e64054900c40d80038880034103420641003d008201c4900711020b2144800d00b2030180f4059240425052040850441d0501e800c010030f80c1075500414055001800490311568449601c0b042d0b90b40300d0701d0b03202141f458590150000e983c007510104100c40d800c04154099441440c450780902260031940b082941c07640f00c14028540141c000d034206011306400c9800170301d0001c0005071090310b01811143c0320111500440300701c08050405000401c107510b05030140582141d0111a802c14400c1a940001c4c56841041c05402081d14a03504289503a40e850701c01d16000300021703054070755031105071030002c2c000c05e030490114803180e075008030083c03e41c402074600f14103070303281003429044101c2c04680c0c1d420300a08914086500318110070300440c00d0303440c0c10b018024424081d100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 381135107 1250 381133857 381133859
    0x61205070614040b0d0b0316030b04020a0b0a020d1115040803070f020106140103090203010213151707091202030c0a060f020601140108013b16030606020607051315020601 75
    0x910428446030310b4100d007501030005215818003a011940e03244c2400c0400681c4200b202d0105c0e00388142d000100034802420b000000c20300c0010050940711701d00c222030b0307410416100e5030300c5440d5006060b003880041c3c1c4480c0300158517500a82a441e240c0e412101200c2c04d414152188000b0000704071003c6070500804001d0081141c1c2080442c140b0030490700092088904140c1e00c0441c030388088601904260f01c030b280c0300003907403829411101e5048080202c1034419456240c80f5410580c04042140010081e001c003c0003003510032002d40c003880003580d41d1100d43c3d19061802441c11000301c0145e07403500440d42855042e80d03800000f10000c0081d519002c841d070000c1c420190401c42c0590003400300e40f441c40341504450303074440d54041c1524580d10b8a40798202c80c54a10f100e000755410300e20104910a103181245006c510340f1014412210a40141c002c03100315503045090342d9080c441c4c0380159004801003100c15004102400c1000644048600303020f82d50a8030f120019520a0300701c2c0540c01c2040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 381136357 1250 381135107 381135119
    0x4080a030c030603020f0d0c0e010605070201120204050901050904030516050f010b0906091605222105073b01031109010311010c06020f071a06032e06120507 69
    0x480c5122403282c10100400c03490764001c01d040c117481032a0580724640c000014410004040381040141c581407082003001d40e11f4560251a5900600090b80800c1c0d0300c507504002854640210340c140c40003e42802c80c40d907c0c14003813242c03003a005042101413020034094544d021400c0c25042840314007600050402da0a001611421640c103000c2d114002d50064042042e04d40310020055081901000e804004a100c0c41c2c0480345d5001d001036400706030480b643c00080034103118074401d003a07482003804c81c10f0580d0a03020340404100085001081d40e00404000c101c24804181c20303001038103001180401410619072038a494010121000100c03081401c01841401980c2030200d821110075220300b80c071541142c5620011285281519040015409440042044580560b00200600503107284c0301d400707034501081c500420301c00c1241005070b400002107480c034002800c04000542010b42e0030f04003400199103a800000ca04001f031150351103910028441105040c4c0e210b01c1c60180000c0c0c080d6906001d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 381137607 1250 381136357 381136361
    0x30f0509070303200a120f020d0504140f030c04090b040501050702010221130c080c0108061512040f0c030507090c0905090c0c0a08040b0921060112050c0904080a03 72
    0xa00400919405100c003480080d82090f480c21995011410303001c490304c0410f0f100380ca04005900d00030010422038130118225078201c0d086000104198003503d07681885c003030b011a03090103544208840304000b056501c42d01e0800b103c2e810a422805000ea61919403201c9c003007810f845800c2d104448489491007080244442880780c141c02194078070080d8980100030040c921005440d20100141c031502001158030040444803030a91564454131002d6659aa0100c982c6c98064103651280810702c0100000d4a0b4908101d406d1040c48200ca000f5080c4612000e801c9280000200205c1d0702c10f00e040840720103c0e0f40003e140e4010351181005104990400c1d00340c01c203980c40f08004030240402034809114955800c0b002540c8602c0901c1c0b0b958441d10303800040c0385403415030358010701401d000050102e18542034100601040200340d0350116400d4584c0c144690387d81c4807101244042d00b11000501a1150080822507154050000c440c002c4020f20005255008140c80c2102d82e140e00040340c00a498041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 381138857 1250 381137607 381137611
    0x91113050d08040b0c0f2406090709060e0a030c0806040c0e04120e0d0b0a0c11031306140c01061d0915010b0f1213030311251110030f05 60
    0x76141c15031440666640e140a03030085010f40c0f8000180440d481e85030503010042e00200540700c0c030884855100c03c00c55945030300c02da040580c0b01522844001042800c284940a00520356a42c440c450640303040c401f103c001c4c070000b001543c800b050714800004548001d8004000d012160080e0042c7d040a14000b0a49103e50303220030801240c1c00200b0001c1021100d0740303011004181022018041d560300001c1080f07090240040c5001c420344140840011250301194051040392500d20381044900702c5d043d40c0e4011110030503207080c80310f002440b4840c464800031080052007440241410f840711030b580d0a42d1680e030060022a0b0151001c4040307105610f20b89a0400200c10107013440e4030545031a44000f80050003444070a5100240b03401c440002e580803220120102c00290f01039003401802d0807007169481c8816030000e0b080039070b02002d84640f0700844400034a20000c201503c0011642550900d184a40660385420113a403500720315141d0b20b2811402d60301a5500051085442401c14125440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 381140107 1250 381138857 381138859
    0xc0e07020a03050f070204111801030506030a020a091508060403050901020d030624260a051e070e010504170a060c050a0c0204091412030403030c0c0209010e070909111305 75
    0x150700c1e00401c1e0040111a45070283c3d008003541c0706054008100034020040100e0290100054401c20380404104210031024099a042c80141c80f894205581e0300c2040348061741c1f019241800f006800c416a100301c050440d80011440302a036100700e0785003400006c0703c00390f01060001441d20700c4da42c1d040c0041c0341000c0031810208103180c00e0444042442d82e4000046113400400d50143c03110a014144c3c0b4801034103144403035110340000426613858410103071196240e42c0d0074400818680941c003000281c2034084ea190042c01681c0380d03903086603000c804d1381c0c0a0f03050100410001c907240f00385070300d401800036074503008089410b4a0310304541240e81d0f880c0700d481000014812100d01513030140d41141586d40489010900181c2070410a8440044c0d2086001d98498110701d0342c4501d2100c0e0146204500a80b4104200d001d90041500c0c25040440000d50001c0c030039005100031081110307120340003c018a08240082d0700d811804044038503455062400c0500411480c121180c119141c4c4040c00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 381141357 1250 381140107 381140113
    0x170a1107080a0318032f0f0106090f020304051c0e0901060306210506010506130e090a140a030906080901020c15090d18090b1302070b0f0105100806012304030c0e0702 73
    0x154a00900540e814140070391a4991141d000e800d06c0c81204a00c0400c0c0c0340c11054601070b14a03c54454024942449000c3c011070400c12040303441c41652003640d11843e081406031440d660996140b03607001034040d08481c140f02800e0100f00745600e81d0440c1d54003a041c0c9031000180c0505040035001003030700a105c80752484100c03d04a0002400110380b003411038005403510f640326490244d140004a010343c00880385518404100200c08400042483e440c5003e02000010550401600364603103440b01006800b14010030010070903903200d203284541c0100e80000050512103401225030801c22a400141c09110000c024022801018004040000741604200410302c070442c030a860030000500c5009000e6a86444410b1180c4450b59103440b081302c005021542c0e142c00d440c200c002c100007a9000b00e04020864004102800e001040c11124002a115244a07a441e080111001a65a05240c20004d82d165442030001400e00203080510f106450961840341003090103800390300300a0142d02158 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 381142607 1250 381141357 381141401
    0xf14090309011e09030803090106050f0a030506060d020604030f1202060c2109010908030a06061205090604020d050f1e0c01020106180903030209121501060f170a1107080a03 76
    0xa80c02841055003801d81d0981c0e000e01c0f00600e00b007038840e000d269001800b010000010046405010b61202040c1c4800b160520b403150135146c02d00c40101e4450000030a15031141012803001d24000c00c281c800c051001785031610749500e940c1c44100e04000800101c94482050403c400d000340c0610020768003103000301c41d45041001c8503200030601000140c440c4124401c941c08500f440f5020740001c0c02d0f454104200b02da69061008411004151034403528000884a44112448150500502d40240d902c0c000a144ca80c0755a001c00c100441020350848440c415410990100001844401103020440565a03208500030441034203000e110001c180c110f92404105109104d244100c0c80340503002100005450303101480e06500030703c03501d80c0c200d0340500c030045541c86d1038800040c0f50380101c901044a50059a86170b0381030743c440004c2c2011001141200c80710001d168610b04859030300c0040c500003c10310b140e00340860200c962103250140c441d1080010385182040d05401550084600300805003141c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 381143857 1250 381142607 381142609
    0x61112031003140a0206030414150408030f07201608011518020c2b030b060a0516020907110d020c031002180307090c030b03030423010903060f14090309 67
    0x1405a400002c00320014502407840030b980410282d02c4c543c0e400382000ea62070409003010408481d50041c104c000b80700364000401000c411409036801654803801c464255212071090f0010f80070000c05580400000c8070700c0042144a209045c2c0301140c8100107000040c0040d98141c1c2000300a41022800e68141552070303a803c00c002d0302c11801c45c0c0200d08000c5032404a000404003900c10142c4100d098420080a80800e140b81190401046e086800301d01c2c2000c1032100540c01d0358094000194005c805008074110180a50000c0581c002c1d90000900103c2d460ba0004a9040302910044c000507091000254060350803c00345200e20000e0004040100c03080000a5407030b10196100c0c41043d0300824550550b540050903402c11a90007015501c00980300c00500700200000c55240002070308207000c1d800242000300c115015912480e4150100340c0d2444900e00710007070442045070422150510000201c1c98510803801038028a520100320008200c26181ea001006091080c00350020420700d100c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 381145107 1250 381143857 381143881
    0x30d021b0f0111030a0201231b0a0504090204080105040c050607080306040b0609100309050c0a0503060609041a07020f010b1503041103010e120408070f0503070e0a021306111203 78
    0x48000c003101d140c40c0700a11040100ca801040c07640031000c600c00411100034240d01900b001161030590185c02c0e0000000524078103640e40d094520501c8254081c00c801c0b45c80c4044e4009090a81c01c60800500d02540c03040380804a80c496408803006035911b034144800c2144401101e00100022950030382065a1500d580350644000f4003094401d9694420b120f107144c69000c05d4440b0190010400040000411005009058048811981030081c130764810030920b401a40c0c0c0042d40e00143c02030445645503c00d00c03540c2d207030241c81070710340502e0740403c149050b2810307420074414400c0380c5c040c0c10030032445004036003505d2440c07000d9880780198100b510365500d034100c2903960107908600d0014201c1d04180100740102815001102c0a010340411141144840d00042044070b8030384040380c5d8030607500c0d841c081c0011040d02500c0e038507401005040110340c00c0000e40ca5046005148014502811010096240100f40d80320b840491140c000981c0d00705402d00c02c04a4201041d04010302e50f292003949040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 381146357 1250 381145107 381145153
    0x715110303150a050a1508010f120b0402060d05041b0b03010b2d16020306060303160f03022e0c030b030d0c06020d05040b0f18033a0605030d02 63
    0x34038042c000403844030a54510300244020103016182540150301c515151200100e903220310340118144500000744400c80c5170480c1e084921180250820400761f594444240d24003620031b0360301280601603e1080000b6101d9a230003244141701004c08419098078442c903926195100c50701c4504140010008004844204e4100708198030b181c01024640c240304040011811000c03a4440c1030203c1c0c548a2091820368080e40c06000b10102e0311035684220030959644a03d0310005810f1091000380c2002038180300c07805a15512a0050745e04555140c0ad80b90300c01c00c081002c3c0506031030031503142075080d1580e00c1204591401d615040c480310701d00f0004655907520b00c02510341044086442d410034404c1c0d0f2f50666100311844401405141080c2c2441540d0030000e5a6111030108140040703034400300101e01140704c1c00d0561020f5402c206101c4150b1641000b0025145040b09001c0041c8809540092240424001003c4001035082c00e2a0a152030000d1401b051020b66002243d40a0410000d020003c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 381147607 1250 381146357 381146371
    0x21305040209130515150a1a070212070810020d06080f06270102042c0f0a0b0f040e0607020c010504240207083304080a0804140f0715110303 62
    0x30f0b04004140340c81440d14a19107000c45104171036105010340345901d4030003404030040888452620b00d8807010000c140840702c0041c45c40c1503208014600050412616480c510511003040c2d814160340d44102904101041c0b88100032650b00144140880b0514407603038026000210040a00039003204009554840142c010104450b07400010100da05104035103104040b04c510003503403180c1da03c0a00750200c503000d0709402e445508642000c004000c05c0c9980342d100702001030442006488804034480141281c42c00f664000a101014406a440740e00418844824510046c07500307140400b4000c1c101300c042100d2604212003040100003801000c144007900d0381802001a41c0d504104000313902d0b03e00d1682c49036946000344402c8240c50900c0031401d10f20310601b55000e00f4607c102810301d40c000d034000c440051800c50306108021001c0d10880c460342d4401c2c400d01a030450900c91080300d03031500c0c48102d05014154050302c0709001000d02c41001032111f000301d04081d404103022003040c54682c0001401c0c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 381148857 1250 381147607 381147631
    0x1403040519050313060513080d0f0507021305010b0705160b0d150815010608060603010b071407090e0a020310050705040e09030904110903060619060f11010c0507021305040209 77
    0x15018018244104d500c140a02c0d4a82003415686650203071a5400440d0740d0a43c160a4050000d0602c40104281c160090240e03103242c41021804000c0d03034650400201a608a0492880814040402e20803580a010040700d596250207481c9000c1e480c0000e802681908141480406c009031074400c1d007584c45913181d40c6404100e0f207400c00001c0d03c0703014440c0e01409091144600307142600280c4285207040c0e603020b40d2021100c0d5102c40c2800766500c402e02c59201d207001d08000d154007242501d0061a0f001c203a881c1500c034166911001c05e8255041e2203501a070383e40081206004500c4c0800403c44014101d000034071403403401079005810350040e44545250741c04c3d244002040c91300140f0443c2c6070400014810450b60603100e8401e02c00703802c400c015a008e0b10402012910701d1800e11781441c501c00c020f00c062560a41089030440d044806002e2500501891480c0c1d400104003c0c02400c1c8400701a40d9010749901107030040040d40c0c01d2190140250a25090922015072280607100e07038444c50000d80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 381150107 1250 381148857 381148903
    0x60303020d0c060b13020306120c03030a26011e051503040204090203120a020a12020c09181006080d020d110a080307170406060f092d02040b03100614030405 69
    0x840c01c050014400c480f6806104200b40c030115064030b501560040400b5201c404640201c007086a4ad0394012a004940c11380c000e00101d0b104e1440340c00d02255161642c4141c58010102043c400c401c00d8080c1c2010a50f003c40055661004000201c07420041070200d800c050218244940e4503c035200c0984081e010f41d440c0d02d01101591020000f030b020b100e10f20048a43d44148070a0000d4403105940f1040721003e19844150031224400940300e4565580140803403820380700c1c1c1020b100030341c1c402d00842078280510034482440d00014896440140891400313003000c6103080781c0c02414410078200140c28480490b07180c001c004e20000f0404030f81d683c0218165900d40f03078210f05a642184008000c0400b4a21004001c01c100450308032508442d102480450526203561b900812b48281e81549010200740790b50441c15400003042d00e40036400745c0c1d5001803629407201e51180465000321440481803509031401c03c003031303a8030065952030013044c62401030441c20140d680680300c0246c000d210698100440c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 381151357 1250 381150107 381150113
    0x10050903120a0f0608120403021e0616021203070b0f0c031e09030d0914060c0c03090108042108070207060f080a02030402041409010605030f0c030606090a06030b0c0715060303020d0c 80
    0x4c0203501401c5404d007192164442c2d140407000544c040d000c100e001700203030021205170350103944940c2001c1e480180401c1c100781c42094078000680701c1c008285d0b8001e8000700e603040300c40c0c002c3c0003d000d4240103800051840c600784807503c00c2608064007090a0020410800125203030b9900610704c2918a01c41d2030040d40c5480e18842d142d40039000707a140c1030510b810100020840030303031f1007808042900c7e03054a400784e4904448014034010a9803d2000d508100301c0302d0080e41c8207154050b8400c1c4152409602624440030700000504104e1b100d202013000c650900900b1501000780710010201c5141c00303240b100c542c0d4401813281030040c1c4044d44064000c00031404560f90394000c025000545900c0d80124580940e1213070184c645445101d000340100018941083c4010481c1000c202d0081d0042c100c1d0303214102880740325840100482d42c90b955036440030000444212959003daa02603400c81c1d00c0303000600340349581c40715194504d07580318506081000001c1d00840d0850452a19003422007100300c0d181 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 381152607 1250 381151357 381151361
    0x70b0907050301022b0c05040b0d0e0105040f02091006020a08160501110307030f05150d03020316050705090105030d0801050603070e0406030b0109140106050d0218100210050903120a0f 81
    0xa0070071981075001041206802ca0003000f000841481d0310070286984400c55100c2c0d04a03102502d00d0f0001610800c070a00c144402400240304d05400c003c00069020f5515240300d08503542034070704980c001c030441804400e52600c0009103805c142684001c00c0c60710b00e4402c029580b0b0b00340100003070400402184c001480342c40503103600e60580d0401d001f88030f08502400030b401558030403034001c4042443c0101c8481104078520403d48100d00c800001c1020000c0c120405c03c0d040d5690704103e0451004102c4400e4840920001503920385c0328100400038503003040d041104800c81604564007a0f0712103042c2d1200c0300e03032040c805070440300c0984d50584e5a03140c02008540041040700da03070b50024200b50001080100010100d0f04841c0061010012001020321b1512640403e200f41000200140001c400304100c40d80101810506800c0d28100303c0c4090001c500c450b00781c580d0755800b50b04050180000e01209018191340402200091454000c1c031401b0b80209110180c1510151a40c1323081c000045041c0e9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 381153857 1250 381152607 381152609
    0xb010f0e040c030905060405060f0112050309120a1e0b010905040206090f0f041508060a0207050607260c0c1506030a0305090d080301080f0d0207050108010b0c120c0d02150408070b0907 81
    0x103401d90348103247c5400d0565880ca410341d54400184400c0000064403071384050041490340c2e01c031000d5440c2c5500e0b001080a401c0c034110404042c1d003d02d00054000131170709003110080d14080900a002d68401d410920722010b4147d00005100d800c02e0104001030342c4c4e0394221451141c00f107030159000b41008011a0003a800007883c0b41e0003510704151101510242c070381c50021203071840204d41c81c0343e5031754140d04283d00070180300030116403105020178811070068401080384000d083e003008641941b94038280203150140c030a1110341600082d081d401140500440091900065004609040450200780e03908441c14001e004c000d0049840c40f600c3d41c0e840191100260424843e5849586400301a80c959441075142005031103261304034804140007081460441d03105866214083c1e00c0d202000d9855445040200658011a032248180c1c403440805041e41264480051100006c4803802a00d45665969a40c00d640048400c1000041042d400c9602c0c0c2d80d440006881592034009081d4600005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 381155107 1250 381153857 381153863
    0x606040908090d0f080c0a020a0b0708030c0a0318082505061501180303030b030d0306030317091005010303210b0319020310050403120f18020411160804090b010f0e040c0309 76
    0x100060f00d5514200014549610308d00880700c0100c0c039a55988281c0007803081200c020030201040c8001010100d00d000a440c2040650034045882030941007c07078042d5805682c2201d4007007000c5940312600e2004540360030002c20143c03a0102038203244d00e13681e5440c44010201b1500c3e8104540a00059114241800e092081d21f164202c4880d160320380600500200c0041c58040d1185060395111103101e0300440c8222601612804041c0e4a114030300140d040340180148a00e01c144561110602d00910070580214025038600f080c0170141c07019460304a00c2c0d91044100b55040c0a1401c140390f40126460741546081e0003003040050642c03000c0783c180028001803e00c01490007040105043e0402e80d4151780d080d450300104031410000e56080100e888210301c4070300c0019200701c004014140790b0f00095180c807000340481d0400c8400000b89070304c0f14481200303c4580802007800c200c1400c2074005c032101214242050f4460b01d130213000040c0450b82c0d49407020300c00c68413032854002c000d0099000c00e03140d9130 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 381156357 1250 381155107 381155123
    0x709020901030b1f17040b0106030b0109150e04061a040b03040c050d0b0a0b01170f06061c0204031a06100302180414100510051608160c03050606040908090d0f 70
    0x10701800410031304500c03040e4800705000c01c111341c00d450303c81c030305c5a03100e164030260340556a408c1038412401001071964550601c5800e20300400e0842080c8448107500c096a0b8928031804028030900c0280d0f070303440e03001240c441e0a03640049070120102080d0340558100c501c3e00b0b0b44907511420098403a080c6036000306c2e0130400146a507014001d070016850310900b20544180300c3d0002c42c000444414130a00030340d0703a160100002180d0203003008074515070800402801c15043c903a0440b0360001c002c1545014030310644e40005d0420401c10303000b003620110300f01941c940802d46801e41c04140d041105c0d07181042019400503081c150990318024070003031030101400403c0900d101407a0300303410f08015980d003158100700f500c0005040c90904512400440d15560302420308002700b240780c4001c0e104040c11a00c050090148580f07002e0700c2c03100403400b40c2c007484e00f124113545103041c11410880c02901c5240228108243d00d80403401c080110341c07040030103030f42c043c014003514100094840d1407104014100a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 381157607 1250 381156357 381156379
    0x307030803101a041409010506031810020c0d090803191101060306050114040509070b0d11091c150501080307152c070608091506120d0309060e0607020709020901030b 73
    0xf0042d00d02510965100f041c40041803005001006851082481103d6020004000040e1810590746480d010105040d0480b540003034202c0d810810384e001544109102e600c080006410640c0c004040801402c909024500d00b06043c030300540419207032003502e4180f003174640c0e480e04040000d6202000440d0030110800c080e503100c840c10000000401030b901c2c800c0d401d28010540c001008a503d000301c49200300020301e0074880120740c102511032540326a65121040c48031850030703164020808184c0c400d0941c0442a80c0b0680f404001c098041104141202c0c0341400502ca506d030000115481150030103020300b038140b6498000000781c1504031038000350540c08800904d50711881c07203c1d6100120003a090f00c4046490f080104e40000d412101d0072a15440045100d03d40c49105240c1034004030b0103050703a180712200001c401d1405092824020009a9540b070440074024940700c1c01c82d0b46420100641160304001c18002c0d0750b6241c80c0980700003907034000383c050f0143c0c6c02548440e41002000e0b24800c60a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 381158857 1250 381157607 381157649
    0xa03050115050f010f0206010911070204090506161803080327010b0a050102010b030c09090102040e090a1203110a080901241505040f18060b160201030614030703080310 74
    0x15016202d11406081000303048840ca43c05511001c461510b160b004103080e80ca0b002102c005041c4203d824078005004100a1015851b640a0b8000e0540580010002030405c81e0800002540c2641070004000030318400300300102c0301c03254440460740c00564003901d907261000c012900070400446040418041d01c100c045582e81034110001e8107204560145046035140c005909859032020706030780c560841c1e0850002e914009004030342182811000504041c0c07116030108140500341d13038040d0700d035011104030f60400c0002c05c54502c1c06d103040d140c103008c200240c1c1c0002e201e50144414507420300c030810000480184095120080600300c41c2071081094014440351070482441c0d004241144851988c2003004034065421039040300c4024000b0000c042c5890b1100c060070360301490300b0890f1a02e4010005d03402006101904100e01111274a0780c074040c8034400501251220340c014003a0005040c0c81c040c050f5004520542200e4008682540d281d4403030402d40751041441e040480d1603a00c2517031107605 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 381160107 1250 381158857 381158891
    0x9030118050a02030609010c1704060608070806150d11010f0228020909010621050f01090303050f0f040b160e0603010b03040b010902030c04090c0507060e2107050712020a030501 78
    0x2c168000d809540e6580c070381503045401d98510128107408204969001003a9005c0b080400c2e5015000c1c6000040c80d80d218402c40d820004142d03c2552140d1001c070511210390050841c0d20750300003003260600f1284245942c3ca540009010300c9590503c14443d00e89141c0c640240182003080341003840c142c408400c040320381001104008400e90150420034002500150144100011f6805c03501d9034040c0a0704074880355042c62040b81d001c032028021b6190184009209005080c0c00074803e0328086101c1c54080c0744c00150040040844032aa03c010003800b01049144075900d8104d0b080c00c3c403820012140c00c0c41550007002141d04c00b5006580013000241c0c101c1c03054027450180b07200d103103041250b13641c840070503081e800182c1c1d003840828410401003055160a5205292102050408500301100c41c1c80f100e089426500e64038201e038111b075080e0001940400c02c10003404c2d01c0c03541d1543c1043e0180c3c40da983d40e07038154010146040004072090040d540ca48020714025a801030080c02070f16454001c0c085 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 381161357 1250 381160107 381160123
    0x120c0305150319020d150c0309141b0603130209090604122a140604060c030c0c0c15020c030d030207030e2706011b0605090c010809120903011805 64
    0x41c900030001001e00c5103103070102c1d40e022445441c18a6002d0706034284c081040f03809140d0021102590700b0f4061000602c1c8034000d007041348600fa02c0004106040e0309181c04000c03d41401c00e040313604013141d070010000c902c0303604074500e19042d06d600391a0b44d40c11310f81011140c24090042d50111505040000c0e042c000140da612492060307800b045007180910040c0c4281c2b0800760b04100c12030003102858250784100c00c1d45592140180b0b0394030880040140c0d000d081c0b00081d2000e0341c0041c1c681c0010881150140200c100500e50343c90035100310440394513007165807030407401851050340078040f00d088072503c01c101280c00b0700380c02801d17900300c1e00a884000c2c0c02940000004c07408180b60094840c41c5181080c08003103e660080d2048a008102e0071845503901c00c0244170b038dc10f01200c0c0f907020444c543c82c02401d140940c45480300180608282c5201d03440d00b8101c101c0c00741041903d0301005594000800d10120810040c21859283c442d4000000d01400c400c520400c0612484180c903818400d002480b20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 381162607 1250 381161357 381161371
    0xc09420406140a05030a08031b070605070e10050906091e040203071112090d030e040e06010906140405011406030408070b0a0225020a0618050301060e070207080d0c080901120c0305 79
    0x2920b5640c5009058480c010341c0005880054140700041850580d009c0c6d40040a20140f203d5250410560302c0000f11101076960500040d00400d0303404890610b00b00300c0794444680d091a50800020900152052040b01207440c06520104480404180c1328010304040c100001c006644a02e800580203161600c102034900c450f22800b684109842c1c141d00c212440c114000d000c4000002054405540381d420403180b56800c181d80b02c0070250001c0060004030302801203518049502c511704010322a2000b41e80019034030a5103410010841c80140741c03214280603406890b110f8403543c07142020f030000d016581002d00402546410041ca06000364000c01070f01120200401c804400d2030300c06082000752940094005401b09010710002c0d010300540c0707407001900c0c01c01c1151642c454004c03c0c03e45511381d11a102e03201035803040c08050b82e01403240704d0281c180e120080c040c002e80010000c01c04040420090060100010340c0039507644205034001c50000c0c094801d004d4003c211100034001c2100721602 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 381163857 1250 381162607 381162619
    0x501110316030209030606010c14010c0302090a0e10152d030f0213050f040e15060103050601021207030e01050c030c07082415010c0c080c0942040614 66
    0x2954a03002c0d02c00c1d2070503503001500808440d1740c0e5100560781d00038810300c1941c09201c1d60f52080f4401800740251316a12185503000340e20740d02038105000481c1c0680d0008504610a01c0800c40c03400e0b80e200700c64084940316a15991a0300c080402900d55074088800340302e401588480c5484046242120064100c50542d820002e15462040000c00c9006580703000030a2491180c0412813032921030607400303c452001700001a03410b8440591841c01006d8004410f0400d0318004001c3d0644e0540701c0d09034045021300180c14140020710340a0003501c030b00701d402800c0c0900110030031080d0748280151070b4000c4100d000c50f90f0340d040c0004410b40c0d44040c0d1140c03030498032030740c030f10300c10a080001141c030094244655068010313150a9200f02100342001c23440f5040000100d005c01c0454149a00c42c4000d283e280064401070549a041c82421032004103000c0700c00d41980c0c0c1c52061494011603d03004040043e54950000c003082507010402480488403943c813509001001c100c14202c0030001081410840302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 381165107 1250 381163857 381163891
    0x13172203031e08090a02120708010221060a0302030a0b100b031f08030406050d0203090a0812100602011e0e0a02060d0b0103060909050309210d0503070f09030b160c05011103 76
    0x40320340400c111070301000c90304080401401410405042c3c14524150400c1d18423403503c4501980c2240c200450b4541d840610034031400304c0304051045542c0242040e5600d02c81d680c25600420340d01c10005100810300d42078800000c440176500d050a0000d48030040e800c56507401c008034a40d04650000c0200202d840600740d001510080c000201c8003264025100d03107013000d106e02c1024000303400040480819024803440c9500003180e900c014104034134403e005010906184900032490300c040d03082441560b2500e928038110701c80c00d014401d44260985004190000c02e80442801c242098800039048480410241c003454283e8010310342c80803080c1e03001c01c051661112000165515039602a16030303003003000b01100506144232075810b00d901510a429120311400c43d5a807074980f4114032940043c1000c418820902da00c6140015102624a01900fa850640e2135151541c2e102401c284c2c02c43c0e2400e480b030160b8900800c43c0c514402d410200801841e031031a540c41c3c9007940103d4480d11b03500c404030a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 381166357 1250 381165107 381165167
    0x90105130e0703111207141210020c010c0f03050c040e0c0903010c0518011b03081f090207021c350c0105010f08060705160c0302090a141317220303 65
    0x44840403502514050843e950a0002307000603013035143c20b440c410380182c004401706c0d920503000401c81c2c0740c0b0f920300000d04012894801400b07006214054030070503042c01c091090781400e40d829102030340e02c04000341065880c2e421102d0198490003032600d406509040a07400388a4000020305080482e041d5420010300100004580b800080f03100b012804c8008400e030008640700e03060f0140c0c06034066810054251807501720a603140d9095204503145900007881c9811800c2200b02c041c101401102080c0280c1420b0742d5950300c0549131503090307280000c401c5c5103000c0401250880e03400c9489480d200d5039110000038003a8081e00e024010703600140d80790040002c0e4110700081e4282300e61030310303595503040032404040c1c0c100241150a043e0381200303031070320084050b1b565241e94034083d21040c8400070b4511203100b00410140c0d4024a5041e24135136181c00100442e0720003800d0002400c2a800386a561200480e20030420003003041c08841104244c00080300309074101c000c684032200001242c0d841d52405072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 381167607 1250 381166357 381166363
    0x311010f051209070b070b0417030112020d1b0b0405040c02120412030e09071106010602120405040207080424110a020f0d030207182306090105130e07031112 69
    0x320303140050401c11510030180c080d03024094001c1d0034007080e228003a44d10014070103140c0200c181654003079100700074001040141070781e103500354281900190031589001010908084a400041c1c0260350025408042045a050710705210000b8442220001d0302c4402c003601d15005401981c2c000c43c50503c0800010b400000c0c82443c91695580441c500f605104104500d009000c13800c6081c01583d000403c4d0070f40d508400c8500c151070726541c22034080b4131804514500714060b8011402e54100c52407900e4003500603011641a29010fa80150b1340d49844c0c600481a44a5540b00049012000b81c0c002d52900c0d0021aa003030003803d0f650b4815421990b08900d03a00d0319021070000351300046111a22440741081526000e4403030003401503807400d035918a10b41c4031441600c0081c810340c0b555520f20142c41c501e035455501c52074400402c03131141ca18115011945524041c062184076140100710305031140d5950704910b00c04c0b8034070015180610b42d2460014078030307039090801c10300c40d008241540e08108400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 381168857 1250 381167607 381167627
    0x1050a06180501031e030309060c0f0225210203070308090a0902031018140703050108070b030103080f03041b0f0e010e070806130b04140a0c050c0c0f060c0610031101 73
    0x100c0410415022480c3c07520700c1e1713000000c0049041c10784038105480403c500344101e04044c2c400392121141c4076444400242032102c2e000d00e03041000381d0103500700a170310030102100301545c080d00c0442400340002c8415042407640da0700029414418944080100404000502595141079401d68400c5460702d01d60416400100d500d403d40c81602d0341d0811500c0049441341d5490401e045000400f00780440c440c000440c030845032100484c0e1504010000540c04100c00c2d130041103500011030842d41142c8d41e00d1000d209000342c08a9001c07012000c80d0600031004e206082401c0301c261040c4c81039a031750ba08408c3c520940c1c480c02039020364200c000a00c408082180234851031095580368800d6a40804001c55100d02450010006549000010040d140c0380b00c0c03010008036840c4924803030700d0450b5004007a00c4585410408202c0240002c445814000480d90119503003140c0c3c80e100c02c040c590100700e15000311020f41c0b069104500c1404144030607010050b0503a4010003100e01118a4a801540c8507140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 381170107 1250 381168857 381168863
    0x4090c14041203120906230c0906040e0705041203120605010306030b070f0504050a0902030f070201090f0809041b031a0102210913050c21070e04020c0f01050a0618050103 75
    0x1c5508040000b134400c00a0540f1607000380300010b404034150325180c04990030341b400c84e001c0340040700400e403060042e440b400358000341c00c204103482c0100d0a400f04060303008a2007585400e54800d404202100c0c0581c0039074018200807103181c034402d8200d081c024400500812910b034400c1c90000c002c2019407080c040d1a007034a401c805022410740300c03244112000c007482100c40c82002001d01c0003040581c0c4040d950030092252500c05a01c03414035252400c1e0100003c2c06d0201968074001c42800060340c9801c03100c0c20650800d81281c0c80c0d41d5000041000f400e4840180c002104000e501204010f800da401a1111002041c8091540e4221001079a03543c000481518400c214a0810407486070008002c103144c550160482940042089920080c1c1d40107451890302c1760710106240795007051541c6e4500000e00100441e41e07060034150406084007643c42400d902642c2c0005030401d083c2800c100e0f018070010440001c001a203020380d0400c00400d913900074240c120b0714000041c0180d2906014050680e90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 381171357 1250 381170107 381170129
    0xf0506070816050406050a12240e100e0a090b0403080720060a09020a0801060324020405060a1412090f1203150103090515010b130503030c0c09061504090c1404 70
    0x1007450806c0e2a207400c4a841b650821980030f1060082c034125004001468a103d100380920000150004240902c00d800c00c0c3c600314540010402e1032180c000d00b120031a00d01c002c06c0d4404e500d0300104000513091030304001d0800c4501c48188030401d43e014015030301c40c000a542e084125a02054100031141c1c1003400505160f00000101c0d044007a507074407c1d0320441c0300908240b28140d98807601800e40b040342e03100b95081540c02210718a01c84040000b564400d41d44442140b03494180703000100d041c05810031900810603000500040003000c03c085555040000030f104103546444a401c603501e440009400b809030003420302c140c819944140541c2d0040c100f018031a107400c001c51004500030304035048207407000d00c5400c85140c0c1244c007040080b0b010703046001c0740581c0c9aa000741005084c12180d48401c0c0264000c212403507202001140042c11000201d031a0070b002d44a036000100c2c1248003150f14144640b00080001c3c5416055100c050941a01d4469010990780f804080e40e280c0102c5c4101034a0700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 381172607 1250 381171357 381171359
    0x80702060907091107060905060a230c1c1505130605010e0d020103060f06020d1d1305040c080d02160603090201140c01111602040e240c070f05060708160504 69
    0x8180c54010040c00413684e1507603410420180c40f0070f4155a04454140c8868004d8014464441030310700a0543c5000f0602507880540c89200031144040b03001420011565004a038002030303200d140c80c0b40c032046001294144040201003c3c9010002590301c90340d4411915001100940c4c2e5580c01000d04894058507600440e17400a41072210012203810120304040d030fa540b0102d02c1d10340800105024101d2076000b40030380c1e110700f0005050010b448001096280b40ba65014071982e0f91001e6034520440a0800400c05071114640007002000503000307540c55015803003046140a41c00500100d800300700300140d2107404e07981e48065003110302c240700c0039000400500c0741311070940c00c000081002c00e5805000140c0640d1000d241c52241c0c2140351000310018480c3c40c87d4055143c14001d1080044600c0017400c0b0a80900c0b284030744901034505199420142c5200145444107508207941c030a0790400c8009204220074a41036480d00001c84800020a80210100d00522030400320325a1324400c54030f80f44e10306 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 381173857 1250 381172607 381172619
    0x901031d0c120c03070303110c01090e1614180112050c03061203070f24060f1401020313060519020a030e040203060d02101d15040302040b13050412080702060907 71
    0x4000740810641d035210f160001e00d00307078904011003070055000f95150001a6400c516130780c10a100c41540604010400c0c0050000700c501000b000c2c1c003e61a2440c00f00141d000c00402e5821520303201c01c2d2051084041280036280190222142d0001001d9032038503401000030b80e000341121000da6140d21026020301c0012041d0030040c460304c1180a103941103c0c1842020b945900c45658000001c5540c4002c1107250b480040340070000100b08561107005101e16410f0402200c01005c0c0c43c1b03c0c4481d0f40500ba030740d03d60380364000e0080760401d4a5140206c1500e40e260007000d010f60b40032048400c0300d0310803040c52078030302c030700c00709126a01c1039040d510781c8450000c0d401000301940003d41591340c08414103d01400580d12071414696030076054031030080d0041400390f1010500b0700c50446d40d00901880100403034403009002100c0650313504440c0060809007000100345604442c181c02d0005910300010711040c4519045035803804185590b60b424684c0d40c0d485e040340c54500582e6290030319030111a0038004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 381175107 1250 381173857 381173869
    0x406091406061c0e03040911070f110d08040801020a0e0d03052a0d030c02060a060509162a020f0f090a050c0c0d090807060203120a0506040902040c050901031d0c 71
    0x814000084004881c0380c3e007480c03100807600b54001c5010990b000003410018100240603401403402e100142e68200003040d00d891182941c02c0000610b05004201d0040e000e6950341513480e00c0680101d01d5649807910b03403110794003c1d4061444500880e0111484052616040d84840c0d030059150392014103020321413140d1100d0b55a0044c1e0861032407580f00a03101c0c050802c0117503480707503146940c0201e1170038030600010382082d41c05880c5405c0141045410300c59a15021140e680000d0510549200f1017001c4204461a1100c074410019030000440500c26a0001c0240c8000f098021251149005c40240400401c06500402c00d60020624800105000700540c80603034080a0341d090349107007021002134107003011003c000032030215030200300034001d80c542084440c4c054400b42c0000c0d4a0913000303002d4044115030040019015607100c200180303450f01c0702e4004402c3c1c0c42c1d01034800c2c45062401c0b6000b9225801040d01507002a10301010400d0301074000084d040307485009006071200280b90b40031300c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 381176357 1250 381175107 381175117
    0xc02071413020d0209010e10050a2001050c040f090b0901030809030c040204290322030c0f1202210d02160f0b01050102150403120e0c031506040609140606 68
    0x207070003800d0064200c42060240000c1200700d074520740041c1d444a1000000d001c0800114001c1c0c01500711448601d45144c04c002100e4100c5520b082500f42c00c00c0340e0240d14241300c02d20b8152a010350805060001460081c0003400c01c2d21a5115180c1c0d11507141c0115031300712131801c812140d11281c2c00d00108041003911b8000c3c080390501500b92a91204124081350581c0d206501c180c41d109010094214041d05010011801d0410030094903e10b0900e61a805410014030390711703110075001c2280d500101070044803202e050715031000a500207000b66083c000070051448039590f0241c003441180b80d00341c02e0032020410b03105a03c9030050341000d07030160408000b0f41241c071a540841c072004000c0c0012074002455001c20a2240e00c000b0443d6040000084c1000881c00840c40488019428000084d40144141803a44072001001038a410042d20040c80c003407104507081d4060144540d1800002c0c4110012071044000b506c00b803144564a02c1c0d2181214002e000a0340c0400c40c0320045010f83ca4100000d00e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 381177607 1250 381176357 381176359
    0xc020a0b071a0106080603011d0a0201140d060909021c050a0b0c0d02040308090301060506070c090b010504090921210209030c13020d180f06090203011503140c040c020714 75
    0x100d0b40203407415901d00449402e8000d03c01103041d10080120520f000d001d03440c440d0550322042c40601c00b050711015a40c02e89010000e041c40702500e030990b60410f0032005e0740e906a01a43c4103011490341d8200d001c0062000850503030265030400d000c070300204092100305007080c0e4040010001402103440d596049400074007076040c055420400072a4840380d03070020700003070342c00b0300c2805079242800030400d403c4135441c0d030066000c0c00040c080316012a449401c01c0007180d0700351201141c040e201a00480761842990040d800703080c03501d8140c40c1400ba0150410340342007141c0d24140c0402007000300c1541c07990540841c06500d552641807151814202e034000e480d91010240440f2044079900000030300c003100324600031000b140c0c00710305081c21f14003500880748404040d00c1c095240304410340f0b40000b0f1800840000d410a501c1e49103810440d1000d41c818072101c2000080c072130840c0e0303c81c035060451940d0302d42e029216105608404003185401d22601c1000c649940081000c2490f01100348034800d8000005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 381178857 1250 381177607 381177623
    0x70e100504080a080309010608070b0f0c032b0507020304050f01110a05240705070f0f02030a02120a03030b12072105030301030809130b090106051303021804050d0c020a0b07 76
    0x1c2c1000108500701c0154400c05100b5124a171880351242103d02d6988030501c90b5100b014100300010703204044a901c1001ea100c050780ea001400089031852241e070410b1290f62060044925002d008484403250b0f113440b49405001d1601c84072002c07039881c041c1e40281d9501c10010480b1064640c09940400014044402030744c001070815101c60b030a00305084a0484010040ba021b805903414002d10140e01891505201d03080480f1a2174030484d00101a100926035000401f1290655400b000034100b150344c000d202040990920852540740c5421079400c070007190a002003030b400f0b4a405481c0322200c00781e404c0104801d902c0c0c07152250b00c904081d079003c4803010303a62080c480420001d00086000e140200025940e0fa02103000b0300010000308401c80002c20b207008402c100c181d40c0d035070b101c5044030046e140651312065100e500321009002913100030350001040c8500c100c1c41500b640c1c1c0300c3c03060340214256100d513590600255405221850000d5010050355000e120084c00e031000f0f025100e00810750 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 381180107 1250 381178857 381178859
    0x1e0303020d12090609030c230631121214040803070c060906050411011b0305030705090303040f0e0f252f0d050f0d02070318150314070e100504 63
    0x6030604172070f5031990a8000030021a4988248092010010715040300d00e511100549040d2071110303104c1c440507162050305d800c0b69004000c0e011784d002c0c1940f00c480f00036566082890591400c132001c03c45070508000400d69569070031301381440601c1040c0320010070941000d03803a03546035103800f0076510007040074061100c20b0a41d000403c005101f0b66810301d2140300002007908141c10708007a0007429495131410040c42c0c1403211440141c20a00036003040d4141062900c03178891440c192041e00540a240fa014800030a0019508025091480888980116154554569001020904000f21040c0140200c942071204809201c66125143c1e540c0601e0403242040c144800c290401030b10f09900c640f5150015012081c140b401d1017035140c010080d05001c0d14000d286003040316a4061046c8801c8000d50100704a01071601641e00900111404001040c802d510307529407524240360b44042c00c000a28124415580a52942a1a0040b41c650b1540400901c0d200c040150303000c0e516075950108035040c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 381181357 1250 381180107 381180113
    0x3090b04060903020310111206040608030d060f0803030603071a0906031306140709050108180a0506010608100b09040902040605060c010608010b0402311508011e0303020d1209 77
    0x2014001814072541e03500c448034658010945441c03884d51828240d03605c1c0ca4020240c0480600c11901c50500c1012940103d54610000a006080944c4080303040d00000440d0240700000d54082c1e0709440070304110707103005134580402b15a240001c0300d10b0394241d444036106000500c04410100b00a402120450b8079003024040800c0c90398000b03955400c01e101c180202c500400080d8007608542d80c00c59040301c40705240480000b01a1000d901c030362818440074a02050700b4030380020121900c201c00b9400c0310000c442502c1d080d0744d610400d20411001a00c9040419400740005000004070761101005d00e040c016a41c0c20000104007a500890f4815580c4600203203640f80c5d0400b6000016200d800010210300c0c000510f4250b81d008028144114810441482850003030501c980d080706001c03661000720190303035107803010025840d008580c0c01500f259051482d654490540c80c182c07000383c0b00300c800b00701000400761020901130000a000d03800030541c0b110002e125003580a080d80c007518002c2239441c0c0a072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 381182607 1250 381181357 381181379
    0x5011406120a2019030923070302060a0504060f17041707051002190c05061b0c0f1b1807030f0b19060e09090a060c0306030b090703030206310309 64
    0x2c1c0c1840381d45010602c0f694800800c81d80545113003c504060203c40990781d07511607107248241525003803911003c0071641040303081020310080c550250001ea6030b000c00e107030046c0080c0c119104610000d0381684a40c40280e110716003861a5144184006d01c50380c0b6140d6403144991004801c44448941c1881000081201007081e42c02c4920794400050399084088003450902a0850000e020b00903020f415000040000922070b42c4601b01d2039400800c401c12050b80fa60368071486482512034410622000608031b00407842d2104003481c1001a280c010180d0140300700810350050902e284142e02c070001e071440c0e0003078010040380703080d0020000300310756200001280805140c0c00c0740c0081443d140d080c014903030040041d1551200407600d549092509500c4070380d44088082c402010305844401e4411204e02981284025583c0020094454540b800c12669582e9840c442030340148a80004502c09049903488100076814105401c94214080c1c40103455210b4542c40031010440368020000321103d0b01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 381183857 1250 381182607 381182651
    0x6020613141006090e0708070e0a02040f14010f0c03051b07091103090f01060f12020402160b0f06061314061909061403070c150608100b010305011406120a 68
    0x2c4100003042d80c01e2a06000845005a80c40e5840340c1c00780806000c2104d00003045401c40d110582624442c0d501c42c91008040d020325848542c0c003a00012000c0f81030450492640c071400b02c20780c1c0300b40090002031021203511542c41c4014001c6241080081c840ca459940d403141c0c0d601d815400c0321a100c4d6200c40d00e404075665100380c1c40315504d001c011f00041e040103210740d41350240c1c040000d0140c5420304441114034000d0380308000c81e041a0242000440d01e440e0150f0b44001c0321041001007500303050800818200003243e07111a045040d4001500c0f130b241010a4500c0490307840004980700782002001d0b82c55070241121079900007001e00010750242c1d0b10040e22003154400307581c3c0400c0d09140080c00303030048410302e82d049160841842080700300381d40807004240c0d080d04a81c20b01c5c0ca01d48240c040000034a03d9410407285409801400c05048042d9040740d0000704081c0e80400c044da91350507540c0050500074640d1640100200704c19003203024246961134010903a9100052201c1424032211100d481e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 381185107 1250 381183857 381183883
    0x412080c010b03190c05090601021c0e100305040209060d0b06060d0213030f0b160f0e040b030d03021b0303060310050403170405060709090c09051203071a010306150602061314 77
    0x30011041c4c10440128000e200501055070f030f05219051900020b5160b80c4150220415162808441c2044c40d200c0c2c040002240300181181114855400d0018054541103600380e005a00380404a0010704000442006080d00031500ca00c190b1134400411680303502c0710541c0100c071a005e0001c05c450607219100303440210311406019442c480145496180c0540061941110b01880308041891980100ba8074070000710614080103840041d07000140100051707005182c25204071170010304991382550041040c00407240d591440e020051441954a100407104290150080d20140b4245400d581019801501c00d042a1018041822800c20103000c102d41c20b03900d6030710020602180c9500100541c004d0704035050140544008200041d000c0c039490321460740a451003010440d0701d40c0041c82510050361388080340b5003400484040c1e41d400002d0a02003681e0092500104031901d1040c2d02500c8221030464010b420540c1c0c9080d013941008060340c0040e0348900190070000091f000600c244408050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 381186357 1250 381185107 381185143
    0x20306010801170c0405100305010e101503030512040f0203030a020c190e070c0c1d0a14040c0b0d150602060f060108072003190c12050412080c010b03 66
    0xa02a0001484004103030f000014034202028038003820440811a8442220300780c5011480e0340390030043d500507a54580c806800c079442c0501b00e65810601054440c10f0704402541800000c1ca88107060507400300c07902c00103012643c200010075a201d8521501540709001305141e04504550b0740100f41940d1141c1540303070040c0c00c1103001c0081c6141403a0581c05036850301d50046142170800e1f8001422509c00f603d0741c0c003070100c0450f1000030081d100700c0000240c4030742d042240c4000184007201082182c182e94813107034030341484024210200a0411a442070303400802006210f490720400d02e0301503002346c580c0b0100c0c54540c0414140005078600c1035000b040c0700e90007400c440c0350110440032241d2001e00f03c181000101d10601234650b5006182038101800b071607401c24a540b0350420300341b561240040030200b0006550214896680040c1c4011181e4041e280010301c803c3c1d000c030119080d00c101d014aa0002002c0780c290700125151202904403849104000954144c0040000b0303e03001400b03646c41c102c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 381187607 1250 381186357 381186361
    0x1090204060303110d09150c0212010f140f0903041811040b030105040e011109040b180711060f0f19090525141503061f050a08091603080a030b040509010203 69
    0x50410448441e805c151494844452802c003a210212500300b555844100940c648a0750155500c3d0500507008000700d000070461000c59031690030151001b41c1825a810403104c000424410007041c15a21400805015511346401c046145040509a010080f030366a51402c4000390003900300c00070070207480d0030324845840e0762400c010002620340d84c0b9004410303a410001307144018119001513480c0701c0400c40d8041421030504000c254100c21400c460030f203294074003007440340403031300f0071342032600c0740d80400a40c1c846649081c1081d24140c01600c054544e40d2550000403008500043e00b202039424480340401d01306603d840d09440c002c0060a4900001303035030680f0803c000e8040e00600020a0b40d42c120800c070090404c0014074441e16100d80583c00900040050150b684920362201a0a4407031041352001e0002900106140c200300324420218051101141010000143c1520300050321141c3c3e5030403900315654000d41c1e0304040300d042e06050312042e20300300c82da41d54050f86c0d11462120300010384034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 381188857 1250 381187607 381187637
    0x6190c0602070b1503030702090a110d0510140102070608010e04061d07140102010c08060616020d08030a05010e09030a030c090801090503250f0f02061b0d090510091701090204060303 80
    0x813260b000c50742da100c1c0c0c1c401c222640068036848116903000f054410000354880e8580f544c08141c0c840c5802020002e842d00c0300b000494429030312008207450025802ea01c1d442410b00c016651440c2c80d009030404241a0001040203900b07408041e60f02c02c1c4500e00100d80400480b0344505018030000720700c0815080b00c4014051110303014684007003004248001c0c4a0b0310015031000c3c10101001d08064001c0400045888031340c00e4a40e000e20a89a0151420310301003000e0508281e00d070030940d8200400d90400000181025226001074041e55441001d1440c1610265090f00113094039607e500034800405400110118280304208406010f100074540c0c40032469813600002a66030f080010303021400e41c00e10089583c41e00510700103540302c911280d8945182c000202c040c000c4144048680391014000300c0e2805000c54801000c6000d074880c460300741e46440c00c10008202c060a0080000c00019041100007001e100b0324484800200002a10b0304158000c40e0954146400c00c0e00450103220a02041d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 381190107 1250 381188857 381188881
    0x309010207080c150c3c070f0c0f030c0902030406060503070f05030f0f0d050c1519050601030921030b06280513120503090a27050606190c0602070b 65
    0x48500717411044c52505040e10140c1d050144141c0752442c2071200c0391810018803412040c0041e41800c1d40802c9615090240b52140301991080022108240c80b01c0c4000340b0902240702000c16079501400712034645003481c0141c00250030003082502d0740364442e8000909910b05000d16000b811114204044582c142018145054551165090560301c80f0805d080c2d04a008586540104420314045a07605500200249001e02131524084000181c4c818800042506907420101810090f018004c1307030b4036880154102d8850400c090807101c95201c00040d07213240c0e11186c00400d01c1509002910310403440200316030350040160040d52612808030201d40102d40b0384151120f1005180a600c0c000f1001a50001c040103407061041c044090a000801c11070180151041c01d030f00901680c2206075104081c03d60384040b00700314070000030a0100d01c4841481070145a1103100060491440d0020401f03d80f9200755080543c0005c1002503070640d00000d4450009060460080b00f032405181060741010030707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 381191357 1250 381190107 381190111
    0x80910020f1b0d030c14150106030e030c07050402090d0f080901170106020a0609080d0207050109030e06130e06010912050604050c0a060f0f050c1002040e01090e0a080309010207080c15 81
    0x3202c40300312407a11506503180e2041403042da9051610a0000300289000c491102c90819800018002c02c4503210100c142008000e049401c2070341d040c005990180450b54a038442c5114020498000f02c000344424200b9400a04564901910200d0988015101c00440c02c1c3c5015007240c42400c0041c548002d907a104164a0505044140c003d0f419454110003955582c200500180004d49030001e41050040c2103090300c0030414041406d655444842c41c041d4002d0003102c1c001c0300803804800c900d035100d0400b00159400c140040c010988600d0034210a04c0d541140105410b041003d140c2e00825010200a40400c407548204010051400e040c5001401c110304180218041c240c41030b401c2041c80c1d400701d6020b454240c141002a00510900811500380c40744030503094141c403c00c24544034840c84c60b40148200c50156180401c640d032078100e88000d445110407802e1840d8014040040400c000e14000e5401c50f0048000618050f1140d4603080c180d0049020380040350003400210000c03a40c01e0070055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 381192607 1250 381191357 381191383
    0x103111b0a1406090d08040f120f020d030b13090606120c0f0b09060d23130314090a030213090c0324090c090e0c03030315120a030206040b04080910020f 67
    0x1c8158074084e9003031a40c41e070620700c1880c01c20203441c0125081c45144441030000d150031120641c5200000f400117000c0c6e1890f6045c1c000184204450045428864401c0d42c010b000000c28050041d00c1c51034400002d07144d103801c00d60322180d44103800071b000340044030542c01c854030409140c14054901003030a012100b0360b501a481001081003014140e60722141210a8581c000d0300004284501400d80c00c1401d031503841040c040d607421414050320710b43d007028142c3e26a00c6a0b8030304840701440102c00100e070240740103664003e01040301c01c0c001468a103151240c04441d1140014040c15281c84030381544801d5442503407500714900291013400780105503c1204c040c85101030201d0056651124200390702e510030346038896902d1202f14a000d1060010760b0351b400c0000c04503500c030b0524080000b5814401034045e4482c04001c11031014096003c540d00140b680c1580240c203450780d075512102030f0400c00030706c01c8650281c1041050000d544690340321000309510741c002c0c00608403842c201807070082480304074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 381193857 1250 381192607 381192613
    0xd15090b09040807110d080309190f0b04240b040506100c150204170c0a0608010305210708160c0501051c020c150108010b010f030c0e0103111b0a14 65
    0xe500280c03901018030341c00940c0b01a4140c0e0b02c26450401d81d540a000fa966076901400f20f101c003a09004502e030207140038024000035201c598070100401001180d000074010015142c0c2c001031001b0461843c680703a4002e0254042000c406000b5070b1810f03605000500c8440d20a5841c0c41202440c14184249517026100303540700c2580e41d01c0020040c05100c1c20250061000030700380300380306081c240780e01075034000d20000c54003021040c1c00446540e15641c102900c1400f8640c0427000083e0144580c9240341240d402c140686458024400c01d00448903d5150700301009000300003040001d017000c0020852950610318500b0b184602d4a026072003410310781d104904102080c800f0005d0038900011415101550311401031f640d09200c0111810042213098100c3c1401852000140601e8103400c046e000301000d80e1210106007090b603050301210450402d440009040d4801c5140309c1d40294480e070002c0c840d02121604240305828a008c0700348801c20f00c20140d8000700c0c1d4a07010480c1d51150072001d4a42c030409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 381195107 1250 381193857 381193871
    0x3081e0613020f131706041e110d0515010602030f09040e10061d06100f0e0a0e0108030909090d020d051b060a0204030201020c03010c021c020f01020d1509 68
    0x1850096440584000d1141c07851105800c580c01c419411102107441c008652925030900c2d02c1c00c6428401c03584102424442804800c80303018002060b024880c650058105c0a109401c031408040007411020440744042000c1003241d0940c2d9441c0c1c000212881103005040300b4500070108400514107030f008006660007440550740380556181a28480642507400250b01c0f81c09850691520071070301180c484a500e802c202081025403000c00001102e0000a51803081c1c0300c036018808210b02e4144000001105219040010b5202d26407454841c0c2e0001c003c1c032170054481e804440d500c4400c0e0b01280c090ba000084040d41e0342092440980d0005d002030140585000440029449822551400c2c00f00302000503414595100380c0b81c9140740b80701c0d55040340d00c40d01d041c003581402944240400d80c050300c503404500703100d803405000d07020440300700e5400b82c01c40740c0785260040701610784a41c0b80c03801e40c02540c0e40d00030401424170280000000c00300010821110080e031100c043c020580105489508041c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 381196357 1250 381195107 381195151
    0x31c0e0114030606130b032a04051c140f07090e03121b07080408010b011403091e0102070b150a0e040512090109050414010603060902090a1202010e0a0b070308 70
    0x10540c0d074002000c0c0c03415aa140b00d0015170700c4c804512501b0503042c400700030087c009032141d000e906601080c102009040e660140e588229064066481401c1c1e000100802e08001400507410b0034400c81d20401110b1034804412a1030703420003040080d40020b41e0b0124078104141441e074020100c1002544001c2c51801600710f400507543e5000070f06640810640d54540c25003041d0100440720210b800001c502c0d1103a13105e4040300e018004503001103001882c1245c8280650350910122400343c2e41c5031000b000c4c911580c060300340e4801c10001000b100b80d5401d10000005c00c15489001d403040280d50b8216581c07440403410004100202c0d0000807280191108120005000042007402c0030b201c0c4034a41c2d200c00170080100c0e0141035582105030003030704290401c6d28108415a01a040c0e80454500748030094890200c2402c9014048030241d201d078100c4800c10604000401d010142030040c90014070509240010803034010301340c0e120352200e0310009086030034598408110380c0c0100300e02d01d10311108030000d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 381197607 1250 381196357 381196397
    0x1b0c020603042006030a0f0c09140103090c0b071104060806070c030c0f1502090f0105093102030108060106030b03031206010f0c051e1c140315031c0e01 67
    0x1040100030700000072a204482012070100d81c108003000313206564134a00700c0007a00207050140c058440c80c5080905c000440c5d030007141c030082554042e403401c41c10f20a80c01c0c01140503280803003041e5150b944810000c550000442c0040003890701450b50034404000c42c005110803110302c0d81c00410303250400801d009a0300d0303000904900c515010b1410400c0314006041803003c500c0e01c403030010504200200705104500c61900540040801110090420607400b0015102842495196540075030000c00d200310000c811440c0e191029880c06e51000c1040011042c075040764420380095070554421001008413a9060003200742071032041d809542858041c08510b6904c2c280604424184402200d01404280c0300d210707600f46c200d1f004000c8400303040c040b0b10b10703001c882d0751146020014058940c80250412115005c5603ca01040d079516649840000240341150030140c0203544402603003035410305a0ba800c02400c0400100407802c0000091000e1002e040c41e1100c3c600c0030b040c0b1409000c0244805805 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 381198857 1250 381197607 381197611
    0xc0923010504051e031e010509210c0c030a0605101d0109020306280f091a060702120a05070e0a2c15090c2803020103110403080d1b0c020603 62
    0x40e40c940c0b51102103c2e080c5031107284c0721805a174045c841c11000c0b092246001040c0510080401c0c001c0206450728a8450703103520030094483d51a2501801052621005000620800d04480191a248520300340000c4c1000d105520079034815403030b003060121285c0840003101c010140b1510720380c200c1d40e9406a000483c841407040748541e40d404000103203203803a111603444010360148220f01086c00d03000c0c15104000081d000324101204d5800d03020400400502c140c002048070318990085144401c41008020391000307004907000701d44401e4035001c038803041102c03800c650b2049003c2c2000504000803101c0740b880040c4208025405c0ca084000c0c0c1420a4410a6000b1946803105050003819030301d0f5883e061084092030703001c25180302003060316000420031104020007107075107c000300316113050601f10001004a407078a52041040810042d0700903401400815540b0001e1414240d881d110390409405c540d015002007500c03403202c440103481080b60f280000d006420b107903d40c410b003600807603424000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 381200107 1250 381198857 381198859
    0x11060a020c0f0406170d3b031f05011406070f030e0111032a01020c060f04020109030c0602030903120301080a03140f0c160e0c07060f0f0c092301050405 67
    0x32282c1450540b10790300420017821092080b0f03103503c690607816139a11900030803054001112085210004406001c06601151032840d40e0039140c200e017140342104031440c0c81100d500d403044a651310492003100c050f002c401c240709640022958500b80720b1000072001c42242030310501c001c010540000d41240303003d00540c0c1e050b00e041c040b01c003c0d030310068440c0090b541b00c90069201c08258100704041c0c1c2c002c1c14600c1c10381411018912091100c40600b40e004501c80c3c4040c07a00000006000780c3c8080b402158440d0051400004c1d642e0b41c0e88882070150126007140005810010781c28855042c2081515400c101403e9082d1456240815050311007442020003000c01140d0410020608480025520101c0750780410340d0303651020605441d5510b8051483d1010300035180c00026101c00f01c00c03000c43c0f2640c0c202104178a0010709649200042c600b003400074001c0c50b45d400410783c540c2c0c024891030307541c1d8030152a001d6400e0705014402602c00280e200f0075490702c01c0129043c1e0b2590744201a0303000c641b8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 381201357 1250 381200107 381200119
    0x10060e010e100f0c0c12050709050c19051603032406021b030111120105120105060906010822050f1b0a03060903111005040c060203030f1603140c0711060a020c 70
    0x6000b600490380350704e004001510383e8901e00c0c0082440341c2d0303e040107840644a01c04a404070b541e640720f400c05588007240c80d864114000c1c082d0f8816a00343c03020f0240c607106545080c0e441c00f2110411320721504c0150500740d0000c0e80c1c0d0020380650070243d1701901c030a144e54922420341185820300095680c08000c080702d2408501074913011241c0c0302504020b0015210001480d298009110511000c4600740700303d5206040034070780000260b006226890090002421141282e540c0034010344407030748050a08680c10400641c40f5159041014000d581c451050000c0c10354403455040141c640100c07003150701488009120202d0090352012000c200700c07540a5008105441c02c3e04040c1c0b1120b5400c0140e19103802028600301d06207600358881c0707100c1d078422810b002e021500c0b48422039680c0030031284800c0455040d4042900590701d4040b5071091003031403901140240401a0b4011010700503150364501c00d0001c2011404c0020320700c1c45080c1880c00f5203411341480c03000c0d02c1c02950340070380c07004442c0603036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 381202607 1250 381201357 381201377
    0x10e090307050c1923030106050109150e18090c0111070501021e030c030301140319080d0e03131413050c0a030c0203090907020a03030c0224090703020910060e010e10 73
    0x1201d40da80300070017031440040c40e09102440455040e00340c0d60460456102c1d511b4040041040d40c0070300301e9035083d118103188420b00307080700350410b46200e2a09201d803540080c01b80429850b0004500d005032203100f011002d00183c903101d5002401c0185071074609280394000d0301c0e051105903030000c0d86100c44517440c2044220102000803031030441c030810b5000002400000004140505200584041d00360300340c0880e441201c8001803802c20880b00c038401018411b00300304401840c4a1500800c13010f850810613039280c00d075103d882403d042011b50110004c0e9507465142142c600d400e5111101d0600d456206003d24034041c203071101c6600c103214040c010302d0358030a0b184020754403c01c280c5114000c0505200c0c040d080c03a81d00070f980d41021290440009040c410402d070001e10108821801544a104240464154000e07140c40c64800906441c0030707101d8940d0000150340c80f4200c06000702411065001050300b4900000d240144414425051100c81a0820f926403207103d41c41d2007840c19498003c48117 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 381203857 1250 381202607 381202639
    0x90603031c020d2306041a01030b0301270303050108010905060403050a0e030d092619030e06070803010e151c0204090c0609080d08010503100c02030f03010e010e090307050c 76
    0xf4003403681c114481d0751034801c0c143c03801310a407507240c0c0d43c04001124241d502d694010400c0159a0000c0003a4100566080301c031300c19502942085102c0103000380086200071005109041140144441c454a208042c414809042d014841d05001d001a4002480f51044940301c0e65980c4c40c000d80002c0c1003117000030b104407406100c5c0121280d88003005007603500710961203000a106a0b00d902804180da400544881311254181d071040a440e02040060710b03030a810802081c1540a03a02c4042d0180060160340f9036144c0d850200030103405118410060701c035410942038130002d0900810400503007a00c0032030503680c0e65030764040340080d203ca003609074a240218400314004d840405801084041001030101d01c030303a00400054166580341003114007440d4004011141d403102032086a4040e000f0031000c4030341040c2074016580c07200d800e004403407402081e02d2400350282e00980c444004901003000500141c500d0003055034000010b64011414030b002034071116260001d090f03095104100102c4500c000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 381205107 1250 381203857 381203861
    0x210f0e0a0c0e1e04062702010c030e04110301260604030903060f020403080a1e0f080115030b03030a09050102071a160c0b07030305090d17010e1012050f0c090603031c 73
    0x100040301212007402c1034a01710001c0c092101c00e80001c8803c020b008800c035075101d4440c8803c1398059592000801090f102070b20480d01040010f60450b491b144c2d010241140400194024071b80c0340b41c0b02070070741034000002019030701e001014501a0404000d0001003039004110300300350b075040000055004003c55943c0003c0c41030b5480200034032408070340000442d80092040801c0e5032903101c0401000520385040b2146880d11341c00e07101080e100d10051007c50202c8200c818801d0705800d0014030800181c00203403658028040d10000507041c0c55080c080307540e060150708000c10f10042080d01c1707228150600e224501402c140d610034051034860600070710095051410003400d00c009031075610802805c004018010803512003025210350901074180c81d21810464803074000c2580c41013907590a04444044010f0003500c410ba400071200c60100340407a114000c0000d01b485032004001c51100101c90509013820894014420380c0751108001044e10b0220031261520589038010400628034601100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 381206357 1250 381205107 381205141
    0xc03010e0601200604020108010905130314130b0c2803030903031509150503060618040302150f09012409020a03060b0c030901021009051507210f0e0a0c0e 68
    0x241065070b00560803011030040b801d036001758000e031780300d60190383ca0b401e08401342c4e00241c9103000000181050700d00481e10031480007a1000d40e60381114501015200b120b0060b0001d03030040c0140600c0003441d00e0480368108110001c0c19945015582403021001c9c0041a10340d51b2030b006828036444150071030400d4425403060300307181c840d5041040402c2e11204600000d01b2009401c0a00c049000f1001c0352900e0001520f41c803420000380440b5041400400461081c00d02030b1044040d4800c0160104010b810340c41d0851150640e200004407900d00501c9030f5080d91a41e502200c0744814484162000c500e29850010030307210750090245e40c0341c8007480c0880c01050381d079014040094003c2a85002d00e40044002c241e0190268201c0303c0d41d00030030409104a61014600070140d602c0303c4001811032020341840382d880002800c0c80c201009141c8540c0c0f1010804812100e031751170382d070581010303908085d104510308404880018110503406c8d40c0c44100180080c01040400d50516000405003030643d10000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 381207607 1250 381206357 381206387
    0xa171b030c0c060c0d0f020c030301060c050703080408032703100c090e010306020711010807051c1e0507031109090a05060609130b03070506190c02120a050a02030709050c03010e0601 80
    0xf61203807800c0c9042003003940002d03054003c51403c00d20700094000040c002e50f503c1f482000c015600d180d1809100361958070500000721881d0046000c000041000040580001d05860000e50340e00d0100c0307228504031000c880c1208000010070403400069440000c0c070700400d294072040c0007a0140440c64155918036817940803001e0740a08000120400c07500c6d40182003203a1084118030021101c203001902e000108868031400a80c003803000c10036072281c000580a030305034200c0c40011000c000c03044403200c0701140c6d40d5561041e5155824810030f035a161284070700c0040340c001e803241404d5680340080d0106001400c0138500381e440d04003194441e0303111821105c192100400203d00c200c0710024501c050680c6041d01c81c0300e4002e04400260508000c0100c2e4440786d214030703030840511107540b82070701c040c4a10003043e45c00a200309040b5241f25420441d14174018040d40040400c04203920400d8508002c540002c0d4140c4d003003105000c60112540c05803415100f011646110075912400101d6403080414904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 381208857 1250 381207607 381207613
    0x50702031b0c03060f061e0d1a180d0203070b09010e07060816020c0d020915061b1e0601060c080706090b16110309130b060f0a171b030c0c 61
    0x1181d003081000802c00d4451505030182c0d01c042d500d00160001181044800c1900300300010010040101c90600808a0b484000c01024101c2c0e032a031261a40080c4403040c41060000a0382031041c85460b0007442000100500d00824206129005c02912802110303c010002551031011071217042080d04a50450502c2030100c940c030a0391204001d08105007900c503442c20b106050300c8c0c103030f0261011404240c2c1c0c0d0300281c054082c0107074507404e1080c1340000410240e882c0301e82d054802116510000200204c11440d8060310b00001e998051505000f02e07000310f0071a810740741d07409040f0f040012645604503581410014038030f000d24104440705204000004001c1c81c078003048241081a85a4418000c440d048161980303241c021230240d031040001e0288040ba40c0c814800712020303291007400e12344d480201c0071000c10071075810000301c5c00540020303001c0e41181030301003802c0c0360040d0f002c02c120089492101d0740400c1400d0907107140b600d00000d02101c1402140010001d550344080000316202100f00b0382c11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 381210107 1250 381208857 381208897
    0x190c050105160b131208010f061413090609060914010306020f211005010c051b01020708010e06040615030f02040b0f0612040c0519150c1406041109071205070203 71
    0x58403022402032408840442c16100170001d142c0c0310388104c60603030340c14060f0803100900b0300b48150749898800c00f042c5102102040700764540003440c503410004140030100800c85a051543c0b200903500039410101005103884440d200c040c09035801a41100c1d0000310040e580c12100c66807242611400d00300b09648070112540034200c00c50342130254030170702a5490071503200362035034011140b000a1540c090f1140d4006000c07072080a81c10660301c00e0b0020140115108250381e410b9540c25607002800c40d0b411a0803c4c030801060000c107008010380184940d100824550650385c1d1980c828040410181c000c0350f640c01c920201c1c1c1c9404511070194000241610f480e005070b01064070345013004071011242c0c0f00f68441700003401e0401c022000807418000131842d906a040200c07040c40b1101890040c0e040004800000d2b000c2074410b118410742a0380d0350003900c0c56240c0381c10308000b08032140380164001c0318050200305c545544028044d006082811000c6400d48407400c0482c918000e661040c0c84030a080c2d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 381211357 1250 381210107 381210121
    0x21c020a0b0411091006023403030c12050306060f071a1302040e1207110a030204141602070501082403100e010b180610051c050405190c050105160b 65
    0x40390300d2419007121104619a600c007556010700d0750030f204110240e03201c103600e0030488442405070044403050308000004980000d400d03002e048c6440d8802c0d00440c3e0104503140178000a1034101e0100282428028070394104200841e00c184031344011b5a07a0703220045060800c104e04488160140c100b01c0b205024181803034802001e255001381000c0b4852440d01445181800d40480c07001d1a40350140e075942d052561603140e0a44075801d82d9051507205c01445070210040e40c483c4203908009120b440514a1490500481d896a10646c00c212040d58018071040085170b030f00000b25940302101c6c4203101803002544000d100410480d01006034103009910710070300032451302c4c5d00107500303a400030000340f00b5240300c0418080d21000d00c0d420412038281c04000910b0f80e00308000110460321603840d0441c6485035840480c980400026001c0401c26150701c284024801e08104c490310241003102c003082c0784000c0d80c1d02c004d2086464481c0c141071002c00706240110f2200160302400382034001065a4080c90030803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 381212607 1250 381211357 381211373
    0x4060e01110a1e0503011205190b27030301030305090319030201021c09080d1e05100510020f1005070c0204020711090c0a120518011401090606050a021c020a0b04 71
    0x20b8080c0080c21507101c1800c0404004041d03d107800341074031514916402e08007000d900c45c0c1da11000f030b512807003070300204442c02e1080c10420b85220302829032041c250909841c0b141098264489034101c4194200000c0342c040b801000300e0b41142d5040c24100c1e5100e8250b030101b07040c015107110f5104181c44014850b0245a0103400800b00740414210700000d42040c51468803c80c0c2c0b502d0360142c0344440070300c101c04000010f64011016600c1186c5005403003048005c0c9401542c40454000601c84082641000035040c5200920205c80d441e0024120050296008a61382c3c0c2c01c8403420f044042d1500c01045103940200f034064141600130f0300556441c507490400ba0724544030315411500070080c1e000061f100c0d103c5881070300d444212950310b01071805504010030000d400041c0080b44462a05950100008024402c8001e8556031054450007581b5180060382142d032668481404c1c450200b100c0070540360701041010400124442d111206013039000202d103807203143c45008158000601c00d1109200c000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 381213857 1250 381212607 381212617
    0x60304050d0806030118020d030c140304060f05030f072d02160909020d060b060f04031103100203012904170307061a2d030106060f020c0301090b070804060e0111 71
    0x15140c00540743c8881013031500320386040007404980541c1e407008500618001e652172008034042c0c40c1c4082c65081940341d6001681e290001c80c3c0b041e6000160030008039801c00e5200daa01c80203400d115055140c03d034032720300c0204401003070300c020400105c2c0320b880c105494501e60308241c0000648440c44284010300179645d044d190340c03584050115800001003400031405040c0080394090070550700d028481d070782e20000e40506840d80b54400c505100b2002d44805c08005000114065508421044100c070145400c04060915001e40b10780100018041e00c030070510b200f10100c0f044241c0e0b10313000001841c805158020749e003003150b50000c8070100750008000003002d0143d440c02140304200280200b5003d089207040c0200503904860018000000c2a85000b5910b188a0403230000002800901c1c0c00642191200d80050001c90401004440055030400c041e403918a8281d0081100040d035032259004500010316a01c104a040030001e801c004483d0044616500c1040080c0182d00011203032200383d8102d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 381215107 1250 381213857 381213883
    0x2070806181203072a021302030f130c051005070f06051f0311090702031b030d0605060412080309070314150702011a12150c250312091106030405 64
    0x18002e8090303024840340040720b0156200b625401600500c26000380d540103400a605607000002030519400350310340b20b1400300005003c100c0140d4a14050442018002003c0c11030741505040d500800b00092070300b2000015507108440301051140c5001c0d04480740c0c46514401070010400311106030401203290040b6006000b5a03016400c00d00c4da140e59040456014031001d840f58915000c40d10032400d01c0017080b80c001050344103403498103080c9181d0643c40f243c0c615518404d03a00c0002d41c100c0e1310300c440c49a07a024080c00c9800e82e14051500038000c0419494601c0501946000400320b6181c6804000100c020741d0302c2030343c0801c0c0c00691960243c44598001c95000c0d41c5c9c0c00325002500661062160703500b0a407035140440704080c8001c5c10312003400701c080509211403140c90400c0c0d45c40595400741503c00d50f8441d11655451480b07202400449215500f109075580f803424110380043d070080f141c0c0b0010171000d00300107408869424011800d80c8510a1990403580020500050102c04a038100d1101c80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 381216357 1250 381215107 381215113
    0xc0803270a0201091a0301050f0f0d0b090d14031b160f05010c0e0306040b060406091a040b0f090c0906043308060d060218040c0507050c0612010504020a0207080618 72
    0x2542c1c5e4404107076402615110b018501003040140310510740694001ea29800c0500368103400f07189000030443d40480701e001034a82c005000208481e6410800c14001c1e400c0c030528180407020f108424034203c5000151031000200120f0711485a8911002e041c0c0760540c3c2c28214500d81e600150408070010214844240e80c107500b402030410a2074004c6800a40d404009030060841d9a569241d8031600e01e80a003099511546541e80014215490700030640300801045808602e4041c0600300421150403421481c02400c0301515030b0030940d82d0b482000d5004183e05d91041da2000504000b6100d481642c0181c0740c4280c5104449850340e0041c4c034000c6405600089a00d00d4840c001415155840111402d60703000b003a001c260320025441c0d80151800100a4581281031408080050b05440400c2d40020018001050308018400d080020412401098417a540b034286c0100ba804040f40050007001c1c02241c0020381d051005100b00514002004c02c08151741c640d05110300ca60341d074036580114000240c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 381217607 1250 381216357 381216359
    0x111040b070b0a09120e04090501020c010606090f0e24041505040e0f030f070f0b07020c15160303021b01062301080c07060c020f0a0506010f080d0c0803270a020109 72
    0x2c14407400e410503401184174613060000803001c440c5140313128899500a40c4554020000030400d00107071440000207000415014140380b001412001c5940c0b00f038040400551342088800e5500c203a180c0c010945900c500d00c25202640345022420000301c04a0300300c1d1a040e07070450154400e0400a0a85030101c5060109800701100c89554041d40c070708a0449402c200600e0041120a200070810148074000c816240d140c0b540301d04c00e84040031100e92004d6080207107010583c0c075080124102d0403103441507040c2004022094881000000c60000f020306034001001c00130614428000e91280e548007000340070103511130b00d025042e144940400607207403402081000040d03001d4000b40344100f1004691038100300e420340b2800301030704003400c0005c2540608540c0941c107043c144481c0c0102c50140000b40100d51400c0740303072a01c4c009290f000d1102070b00546151b8004a5000842882c401d03040380303080d904c0792190401c05540110116400000030704007030060005142c003090340c1d1f56050007600c50396221 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 381218857 1250 381217607 381217621
    0x1030b01150c150203130803010e090d02070e0105010c2f01180b0304110d02060703030c0909050c090d11030f07150801050d0605090c13020310080d0507140111040b070b 74
    0x32848a0b100240302054140f144042500542e02a6500c9804403160316860b442c0b41c0c94400c0030342d01c2030300050200e12050b01044a075030300400031a40070302860f20092600d107182400392000c462040c0101810071240300a814144a8004689020307050303488200b015510071a42011480c44030031090300c0c081210905007110765422248500200c1e0140840d56213946e03150360300d03100c180d0070b81d0300b084da07002c2c0303112150001607200c40d40034202a074440d8800050200800c40007408094003603100540c09401c0504200e203a19003901030706c0c1d0504007516106500400c9103012540351034042107454041c440c3c203d5500d020400000d4000840707240082d04050010643c2d400c4940234424003c242d0001366403203030701c4001a8554405907100d45102c0665842814003400510618a020300788545c00d0703004424050340304003c155074002461644020090041922000b03403540c0100100170300f50b01041f01c10340303404103020741124103100085185d15070340f16140c400314015504091000c1c0e40f06002d00d0009101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 381220107 1250 381218857 381218867
    0x31202280503070f110f030a02031305060703091e091a04050c0a09031403091908060601090503120c070b0d09050f0a0809040e160306270210030908070b01030b0115 72
    0x79034540d0b669682c0813410200d06540205130490182a51320950100100f8140c2c2840540401e01103507025540c0c0d0304840300800c19241e56a049036205010800000002039001410b2a00b00e9440c1d52100d02564070b01403815039810401d510030b0032101d041c50540d2128040c1034104528290044a0802c103035207400ba03c0d01c8a5000341303040040414030081c41030011424014006000140c0c07481101d02e090480e8001c502d01c1c01d500e0040b24551295124184403002e0140401c0740c0c091400e18040c1411403422000944e502000e9880031a01c12000880d50b141700c03418004031018003201410941d403044056420001004002816170340c0d4000c00400e50b206490200d40000780c50b1b0006100d0b4100042030040100401240525018510408800f03a0300343c5c40147c9172900460280c4000100000084400000c11310ba090743d20b0742405550940d80c0041c0c0d1340c01c20b03642540b0402d1500256160b03851400110038400c09a01600c4144200000420001346038241c40c140c070700c403400440b404ac0c035070481615 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 381221357 1250 381220107 381220111
    0x720070f090c0318022e050301030c06030516110307050102070f110904080712090e04030908100b220b090901060f150f210903110c0a1d04031202280503 67
    0x380032100c12500c05454091b00d03400284481e500710400000d03000ca8503030700b0030801c0403402c030116070080010810321124a481c0c10040041e800c0038081071401041007000b141d0b03601004000d200b5035201c02900c0300000c01c2a14600355001c0700071552501141840d42054910a904680650100c07034254601d00b011030030540034651081c2e109003000c0503030351001c441c81281c00041c82088190080014a9045415424002d40c003e03110704400906083d1203d083c64076086402a82500f084010700c8140c4402c0e08901d0503100d2034030740806041403074041d0310180c0200714030258410010802c0c400840010360203042110703602c0340440e18043e6115a00c8540c40c40000780300e0301255500c04006280ba001c0c111540312082c40ca04032401c5a145007070008101d0b45803600030f1b00014006036009500d5501008004003041d4216203140c415440c104100c3c1ca80704500041d4074516000101003020940104000302208003805400d648480d40002a0420050b0407070442100140060701c0c2e100c510b005404881c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 381222607 1250 381221357 381221381
    0x1113060303080114010e041d0106060302030c041e150810120f0f06060512030d18050a02100c06110304060b04091110050c0303010b030709080c03060720070f090c03 72
    0x821603840d204c40004018802c40045040c450301c4810b10000b0b41e1140301d100d102d40f13000e1254089000401c003465084a02e00c0d0032070380074141304000b0b001c02022250705039000c4651320083d0a03060111025607050340c80c21544110034440b4540c160507031a030f401c000724600c00c079000e40317500d40001c1d55524200d4003c1102a000340415400c031840d100030811042c00641d81c10b028142c003040c0b03503559501241040d403030300e000d0b4600e07900007040c802c0e500f4110f40a1240c041c44403200c1008076223074a803034642c0c658186503030092040f120322003011400d50041c40905181038001c0010041c60b282084d103515140d00450382202c10501d081103400d450300d80b900c1131059540d0804101f5030340c40403100c10720200011141001c0700740103086c0410301429038100020740c040c04914030100e07103e0500500203031114100f43c010312034035040a0080307142a1000a8265400b00040c5001e409600d803a4910400c10165001c82c03141034060b4403001320301480005a108112520b09030b0400c20140681011401c40d00c0c481c07501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 381223857 1250 381222607 381222617
    0x3050d0906050f07081c0209031608060f190213061202070f0605070509040e01020702120604320d03060305300306060906130602060a060b0316030f091113060303 71
    0x83d800c001280780151504502c80c0601500c2c0a00c02e55110050010500450342d43d25000a6410000d007004d00c15881c00c0c826000c0c0c641c6105040c51015900c440f40100f440b2007260205000402426055040a14003060060210b580ea15800901c0e081500c20f03000e000c0100b490103944822a64040c401c03680c031240c010704500340e10f1040e07a691401600c130113408501005001d220b0703400e440c1c0c0da0748a0440394040c0c1c0b400040c1d031f80c03549205102003540719030450411034012000b0000440c40b040395060b003205d421050908159004005807454281910040006105060000c0a2180c0581c081016170f405141143c580d9070b181d048140304800240d42944a80800401c2c0742c00302030b548009503400c2100244400e0410f0100780c003288031904115a05c82e0b51003901ea03410801c041e014465560040b088e05401c0c800c07142040640c0f40d00b440058a0f0f4826182e100c206038218501c60740c841c0310340035014401880541c206041ca0810301043c007065922440c11068100c0190f0900d20a0004480d85a211 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 381225107 1250 381223857 381223867
    0x60f070c0f0b07050d05040806070e060d1406120105070c1104230a0e0304050f01030b18040503250206190e03030c03221a070f0f0b0703051503070b0d150f03050d090605 74
    0x4a40c0000e1031003070150400cd05104003030200100d4001c0702e280d9040f81c041052585801c07001c00641d04509812070115924040502040ca507006494082042d002a080301c0d03142484c5d40800e000300400c90054030041c8004014029031804444018002c115040c0e0a0104030f480c4108607849100c0c0d4460702e5407104a900110083d03500a0f04234042c494001040c0201e80d00b040e600703c2c18018411281150345400001d5100901ca2481c1c1070340c0300101c640e0220800427102580072642034820307589041000380c1c0e1004444d031004d104d440107aa8400c030160a0302d40f07034904080400d6907a00b058160780075a00e9101c41804101d10810040c40899862800b2000700029800250707145500080d0150307041d4a5606d01c0d42e011800c0c10303443d00041d80c0715105859281c949040c00500303ca01c05403482100409441c074401750b60b03400240c610141e4800416540d9600361980c4540c0080c0091119880031070030b12400011195030910004040313038010b40503901c0b40d4a501d141100e40301d90500035100407a00c00e03c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 381226357 1250 381225107 381225121
    0x905040c03060812070b0108011401090f020702030a03020309040605010507050d080606130303050a090909230139080405121303020402030907061b02060f070c0f0b07050d05040806 79
    0x803a0200802605002403015115180d090a1800031010b034003048a0000d40302c01084042e40c2003d0060241c00000c1000c00310000140c0c5030701f10184180b01401d502c4250506060700d40358120741205500a084950b260254034019443e90440244284107910300703e070002c2c00d540200304075852a58007201070700760b00c8100401175900300c1004c3c10315034101c1c0303050000c031000c50000600c00025500917141d05469000c010001007a0030081e40100043c1828032000c80000b03801e40c1a90031034100da140d43c0c0c01200f012091100d005043c403510103003158080d41014603214a01c40d842c000144250040642c1c11580b21000b50f0b081c40f01913400a20589c02040c8544500707075410041d0250280c003840b840302d0729a40f500000c00740d800c15204113049800c040010425a034204166054401501c1d0240c1481803454001440b40d02941740f070066281d00000d0124100070100c820803000c1c2510600c0d180301c0d84c1d20341d403285211b50400f500452385d5118408400100c203000302c055404480c4100e00070045a6142c0d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 381227607 1250 381226357 381226361
    0x30c021c051207050c0109031a1b04030b060a05030c01020a0f1104020301060203090f100f03020304020d0602040f060f020106150f1107080a020103110903070b0f070605040b0702010e010606090504 86
    0x504808880410305000c000400c00e0202d81c002c0003481d01e0381522680107007015800d002450034141d0500161180c1040058900c0b1120000c0c0d80c400141c006a030b54528941ca128103000c002008048000054044200701300b070060240030f900c1c1a81c0321100d40c0c1c0c070346c0305055a8960f0aa1042c0c00f43e8058448440064002c080c00da1940d8480e404048000c142e05c80400e050340c2007a0050b00150300701065039915801c200c14084c00c02c40044500c44010030105c0b1020701540300211640041640020008081d900d03089945000320b54021402c55546a45002135030038416240501400150303945581d0b480c461050049500f551090782c01c0001450004609541081801c1c201f8018041c071802815544036041c4100c8009283c0c040c06840e0721102c52000404031941400b1900031210240701d0030380c080d240060280c05594105046a41e20405a0310b20941e03401a944014601c0d400c2404020800c40c02103a0300b070090816400070700800c19001d40e0f4a007a200d0034004c03c0001002040108410b140035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 381228857 1250 381227607 381227629
    0x901032406080303040c09180206030a110c070914011208160f0b0a050709050303040f0e1b0d02070308060603040510020d14090c014a030a030e030613030c02 69
    0x100d000260071581d68102c1e60a43e0012103040c2c401495510f000c228009a6001e408450700c020070107031031041c07003e50002d407050001600c80c00341d50b82d8804510034109a80c804441c0055000d20489152640d513540d010045c0c207069100c0c3d00700c4da1450000146030010a0310350034045600c045c0c2281001e283e04012101d60030320b048150382d504118103025000c038192091a5005038003414003c00c0314903114101030300d480c84692240340644c1c41000208041640402c0766800e48511903040b005540f1b50710485070681080d0544084241e4001411004903d0503600801d8018400c0d1100c444c42da0702d030341c00c10003180800c44003e0316982003514030843d029280c3d4010040d0307100c01d800000d45405121400b00f00e2031402c980d00403a90f84124002c1d0307120368008828003118014a64100040340b004250000b203202c3c038200e8400c40707840c1040188180f0038907030351804501d20094111104040305050040480003d0200305000e8001c0c280880c2c840306070031081c1e4440540548800c00342603103035803d100542d00740e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 381230107 1250 381228857 381228923
    0x2070204020d020d0b030606030a030206010e1e09010b011806020c010305041b0605070b0c041d0901061701020306120c0612060d02090106050a0206010801092103060b0a020714090103 80
    0x1c00c100c0d00000054a00c05884c03000c40700310000035403407074030800d00d4940386000d4040c81c480c4c0e008401000010794001a15415950320504140240d115040314145024000c1030640489a0b0f140401c00034080540c003919560409a903102240c00702c0c09a003d500e044140603140040e0000410032165500a03040746802910804d80c0e40d6800d2200c0c880008901d03c00d401c1000090000904001440508034021340c00c003d6811000e49881e00d4450502d02e03d2014101d80b40008401e0b80000351080b9080d4001402040d00341c5600c600d031110985110300070350080b11003500c100c01c0448080e03481007002a1f002010704001c0d0200d1300d804138010060400050040042d588909842400d10050301c0d0200f4450007040b503616100d03100d007030080f0301a080050503040310301980c1c134100103040411a1403007254020481c5120703000911034402c0d02280644003981049480c158009200c9070840d500103921030896a1a0030307504540d901c01e03410400c200300c2c00c0c403002d0305a0310042403039024001d040606200100d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 381231357 1250 381230107 381230111
    0x17060d1b150c052529031e090111041802040506040306140c03070c02090405010f050f060411040f3003031b02010513080c160f08120403080d02070204 66
    0x141e550400c03034400310801100000100c8882040041100410002c00300030344401140c1344c444005900d03c451500c1e030744101070a5555082c4510090300a0041280f0350305a0b05031029520300c0d154841445010910314205504940d1000266070045c061049195241d45500040d00e01460601c52f0801a00010406151a40c0c20840086c0302d076600e800800c0114031030a4041a03060155015005088000700303c0260a8001c104202000341e0004103002040d9040780c503184a81c480d4101640104aa4101002614509800c0c4444107440d40c4200d41300781011034042c07100d00d0503020321070054025071003400000c00c400c220502000c494070300c1c1d520065402c1c40303400884407002c5600030b00581c0d1000342600801ea075180c04e6000d40c100d0300c01c0e0b502c0383c41542c0020300150510102c601c0081c50000b00141c83c0d40707008641050004814004107000403544064600c0490301c1e4044010180141e120360741c030ba4454441c58800c030f0b680d190141d40071250030080d104c0c10f050306480c1580c080d520180d803c0768069 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 381232607 1250 381231357 381231359
    0xe01020d09031b173004150c020d0f14031e07020d051902040c0305040b060f03030c39030a06050403032019020304050a051306051c0317060d1b 63
    0xc0c8461804d0004061003001032500d03062100c140369054003901d8410040d14418502107102100b500c0440701101c06a2034209201800c030901150b0708140040004d601041c4c064507082445203118403c0c100900034220322002810854420f40d1700e1046001510f80492840458664510034001a08905001410090743c81ca60380d500e0b141000c10000300b21070440b40c21250fa9066003410710884036000828181040380c0d08190300c4440c40007000600e03091151341419122801920301340151640354070076004a441c844440841100050341810108100c0441c84c2c1d8404408082140c003d442d11402401400c0000420b884010141500410540c14075486040004e003081002a0403035940c4c44681109489080300601d0303d000f086204100360840d80103000922090b61603402c004d040b034008940c604007004106000c40094001640096448042d90b00d00050900c554140f1403e201e119680701c01100006210380c4540c440e00b40d0740b454100345084014400511540306290000703042c042109402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 381233857 1250 381232607 381232619
    0xb042a03230405060f090d1710150f111b1302070c0b0a08071e0e0301060510031b0c1707050a0510151202060a0e011808010c0e01020d09031b 62
    0x28442650101e901d58061300401006010b40740001c2e0b0000c524001070006440302c04001045003211645041144401c64080303000c0010041900004040c00d8a001c01c5190285d00040c041c2d2041c00c20b81c030082458a02c681007076000c0880e0200b62009207079101c0c41c410b6200810310282c01c44c2c0307000e1400016420044d01020aa1039140f0390018055003c01c19918034581800528000010344006c05015044e004840c0031200c00e03008a49101562030000301000900740040e0260102c0e900c41c980016881041c5031a0b40e9064000c03002c24055000e41e1142001c07901001c503015402e280009c7c01c0c4103252510219500078600042007418000c000310b42c00c51503291685414032038107140f041d03c00d40d0740c2c3c001c066580a0385100340000380605e680b84025244e050b0045006481082c03103010401c0311881c1050004c6e03000f4900030078648030460380c0c400380c65120509603000b004e04004100104002000c1d9441d5584001000880744100303503245510320307107140c0c0d40c07039400c180104111482e481200004103036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 381235107 1250 381233857 381233921
    0x405041d0703061113030606090b0f01021209061c050601140a0c0f02040b06160303060504060602190c0f060302090a23100527090f0112080c01020706020a030b042a03 73
    0x511f015840025a95107041d0b14142100c1050724498003400080280400341c1e80c0100b00d80f91902140c00a0b56902c011110015030940702d902c91252018000302e8010003004010b81c00144500c50070388484551a0340001d4000c154001c0c6540071002550090b81e01000900319121602454806800400d41219140014400e40c204064483c00080507080d143c040c1681401440002c7c0002c0d03074108181410b00400940742c245818040e014030b00e44941d9602084418411350000b8815146030020705912407400502a5000c162740030701c204814600441c225500654000f440c0121600750f0312008d0b00441404640d82e24264981c05101c8180700040040b012250b1076900c00b09401000602c15005a003000360004001e009854403500380300040c4410206481d620551079042440b2035107410129440324060300c0342c078000500c9076002113012640b80d50160000f8004c120101c4051204402c540c2c800c603e0f4bc200c4a0365806c40c5143d00840c11440d500a03071109a0200140b42c03900d045807118003003018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 381236357 1250 381235107 381235109
    0xa06050406050421020a020603060a0e0f1b1c0c1202030705130906080a0209040f080712110f070504090204020d180c0e1e061210020405041d0703061113 67
    0x81c0107600d40c41080700300040c420280c0c20307980300082403010003141d08030000d6035101d10340c1c0000d00410000010451a5a51043d440001d2450000c9502d051901c5000000362100c00d0724082107010001c885079000380320020980e1600c2c1d00366038032100c801201410f0440039081c845080428010300d580140b000c8101d0b40001c41c8180746603120581d4070400b01e1503100d40307030300140d01079001c1c00d01d0000140245280499000540b50b01241c20100e1522113051080080750b01090003084502c0c0003600000300810a640028000d50503281c4034150030203580a243c5807200c000d00d009654008942c18000d074509070f8003001c1e05c140060001800c02e03054411000484461200380114401880803c4003003018503480c0c1006066480f2484400b0700301000d0300400301607003d02c002c0c040446500000c4081d22403051b5602c1c0d2464007070071540c601110044039802903003d80201e90296040020100d82842060700c020a25644140104030076071868030f40400030450b42c0303003006484004101d4501c0007255121018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 381237607 1250 381236357 381236363
    0x818120a0e090f0604020f0c0d020d030507031a090c04090204030804210b01030206090105120406090c060c052d0f010e01050601030b030c151c0e0d09030b0c0c0a060504 74
    0x180d60310484880944240450608903100784001e40810203095520700da06070304070300305680260b119050300d007200d5014085d21000c0500c0c1d00c02c100c0407407001c40d4001006008900366840c00c10540d114101c0440507180c2d54042030b80726032030705180300580381171882099503c101515100c134101034581030704101360f038410341c41524200c1e4003180900c0080100398941100b007401c00741c0c107140000c1c16a02c258005c007051201911032440032814070b10990040c0c0072500105489900242c040c03800d4509100100006102942e0f24401d802001c90b8260080c11009001c0741c0041c028981648404912404038210050100b510740c1c88801250b0610340030043c4c1c1c484400d0301d41c000318003203046120580c02c40e04010200740c100b50809410490f25103000c120007102800964400350141021890294684603000028805029291401001100580c072022802d2812020f49a403109043e40456000c001404040c100044a5012850344003006004003d940a200d081e103180d002c090710349004440c412a000d0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 381238857 1250 381237607 381237643
    0x3090f010905150d06080102030f0103030c020301020f030103060212010602030906160204091202060f070c021c0c0e0c040e010801050405071e0b030c1207111009080c030703020706080c0a0c030818 86
    0x501921301c0070b40100f40152040354021400d41ca8400d582050305072041c4000f90901c00d00001c05400d41d1000c1d012074000d41e94041a0942e03a50392450581c0080d4010400440c0c8003040a0001c26824808001c0720780760100106860309110b000ba200c18030f8125a60b804030790060b590340301ca00000e039010400400c07481c100c0d0003600b410325021000c0300d91709400070711200400802024440041e0340341e07190100220300b96a00c0b4100242c440c68000680c044980012039000251030800c002d1864100c024230695911801d003035050b0b640c0302ea16609850050b5401080703500f10b44001d21550500751100429130030035403401c1014559400e40c49025500c01c1d0751100d806080090740d4000c1340400e058054001c8460b14212084641e8824420b468800b0401900c4900d0323100d140c41d0b41030000c182c003a140008895029241c0d40c2c1051301d4040e541d10000e20680000c00c3c20400001c0768180403505a645498046d1208002113500717a408981c2d442000786006020000203002020f650300800c9840d046a10b18a21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 381240107 1250 381238857 381238867
    0x1b0604061d031e071403060103081c050103210201050c0d090f060903050d0b090f1927060506060309060c07140604060c08101a0903070e07050d0506090903090f01090515 74
    0x9420010182c02c01071140003c010486006d8800065a40c1126040321405864a50794844400c0c07a1008101304e0000900341000841401004400380b59103c1141500100052001409a00340c0d007084602d0790786210240684848001540c100400c0380d41304030000584a225540d0311400c403081458250300191380815590500300052045140b054005c50342d20150745171071000e140d08207400422040c00d858281050525005898102500703c0800c805620791003d400703d13050203d5004117806969143c00c15011440600741401101d02420035031018201a07230b10350490b40c05a500091048a101038030342e0500600700e2042c0240750103180725a40200b28079404030402421420050700c44001c49880003010800170002200b4142c1c8841d01c0d0012544444280c1c00003420040c9a40c060050729110030704005510394810300400651080820030803d84c5c40b1a001c0c072130f2900301180c02c0d010b0f0780d0040040c88080c0c94100003160543c0c605241c400b00258032880800d00840720308144c1007068801090b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 381241357 1250 381240107 381240163
    0x70602071e120f0c090f0b0a23040b15180406080a0b0402011b05010f0e1c030510050a0303020607030c020a0c06180906080703030e0d050c0d0303020c19051b0604061d03 74
    0x101c1c1f84150b4103c40284106090410340010074400b90034050080e00c0c15426855651290b030004968050004d21040c030f07518a42999000f10341c0b182411640308030780361000d001103280c980b0409058807507100c0182500f120950340c8400199021b0401c6e810700050520120440a44071032441c60148520000301c0d07042402210181501e40000c811400703a042a10264101b101003448a0040c2d211441c01040c01e8072517080d404042c598607013000b0381158a40c040407041c150005800d40c02485156010846059100d808076141d00351080024410400c40504004283c0b188090841c82220708204914455031444d030340707044500d181d01c11000382d000498204141508000c0c81c030f9065070152003000030480c460b6200b40e191800255598418201a98008207061103a815030726501900000c0b0340c1c41c104062051032903044a2038080f1114403900040c4c13240c064410110207100c8c08081e101500b040d04018065920040a00600c02440a6a4500e0103207503020003152800d03804844541516a208070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 381242607 1250 381241357 381241361
    0xb0403120314060f0111060c0307090807030206030a0b01050c0706090503150c120c070503030703141807090f15090603020f030f071e080d02070602071e120f0c090f 72
    0x404094241490801160086125044803a901c00b030201e9150b611010b1030310046c2c0c0c10118084a0600c50702ca40d2081040d82c0c010303000118001d440c25201c08400564607003a8036900c06040c00003c0d00000184080754414109801c0b07100b00b100c050500c0781c102070700b03d081d00b031500b40d550307000c4400a040c0420400280c00c09100b00b00c000c500000b821046407900e546004040c3c42400704186020545600280c01d44d8060303016150b0240d88501035942c2d81c140200d00601174040da00c507036011844c000012a020001d0102c8904d00e030103c41e400340c05050302d00704150700240020b0078403482d042d880740c1c606000701103294507101c05001c40d050005034950550050041100320050483c4c000d070f01903070b62502418030000f130040842d003980007442003030440f07012488d03823030501907010b41c5840c0b24840d04128031980229101e420303116258203c0f02c040350785822049018204110440c4200342c0244140400301c1d1031003100e00c18500a6800c0c210040c00d907074481603186126400301c3c050342c2d543e913200c2c8032071000343c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 381243857 1250 381242607 381242633
    0x80a111c0c0507020d112409180402011e020c0a0320030c0102030d0504030c06020403080717031515130e071d0616060b040614130606080402060c030c070b0403 70
    0x80e10b015420000580d02040d140200000083c007101201c14102499580d81141c03154070b40041c5a52503900d20b01c100c10001c580c2c00140e01c85104a901c080701400c0310612074002c41c40740d601691140704101c01c10506180e0500044590000c60040d180001c1c17040e262484003c008512505200040f00c050340004200510009580392080e007020245603047ea0b8004140c50907031180c2c410014240c1c403686000d85150802a00080299002107000001c1c09070043c060310595004500510802c58242e00881041c0320845000d8100841841100040e02b1701c0c20540540200702c1e00820301c0d0024217800d2400081243d0b1002002c0403041c41003000407540000803c01c9000e1250ba13010004c50014002049406013001c06056501140c101409003c05508200750a0710040c208010141c1c9800e80c80207105a40480140105541e14001900f000c0922445044819136034540040b9200c65003003110315070000c400490719100c20f1051181051042c0444001055041000e9595625501d4401030799a22 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 381245107 1250 381243857 381243881
    0xf0207080d08010608150d03051c090206180d23160b030604020325020d141603031e05010f03060c0509010c021212120105030c0d030f080a111c 63
    0x115004200405812000242c1500c04600381181c01d07503540313011141c58034481e1401787d5100d941e60714080d080c1a0400010070104200b4040380710000c602c0d0024a05450104c0342c004c3d00480b04124000250941030740c4802800f0703009124120101e803a0303d6030f1003100e407149500c44402070380c00c01f02c00846d03104101e026152011603034080742151030045540c0e03240c04000c10342800745800000046014250151007421003c49a07c40402d1140c41c4800a54079030318103c410000c038080e0014413003030035403803401c0e54642d66420f42100414142a902200908000c06e4540d13082c88140c810b48840501c1c901805000c1c5c04030400305d20000e0f00c1c41c10403509840380300782d03a031041c00010080c10100c4d07640f085841b24415015540c46121100760001c00d131034225403441c91080384001262008501c800940320f10304a403003c0f0b0454070828414801c00205500540c0024007090202c0042055070707010381c9084e644440803c00015201d40c18054000d034541c0700300b10240b07009013024000c0e600900e441c800e42c102505 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 381246357 1250 381245107 381245113
    0x180b070806030a0c090b0d12031a03010e1f06030203190209060108040519032c041d030403060504240902031b030309061804060f17011109040e1c0f020708 68
    0x240e0f07610f40b02c10042003805020302150f1203a0b501c0c40c00380c441c850840019036101004218510407583c0050080070380911441995400700c0080c0d5807407505002c3e00050034551009000c0c641c1c0f00e092000c02003030229400d60010b545588002025950a00000722000315403030442c203444500b441000182e86004040301e043c041c0c48018040032680000b2080301d0040c0d100c48442218409040544801964070080c00d4140f41034101e91007042204044407512210546082c41f501c805504201d4071404031101000c559401030104001068440c1c12094109001d0700c032403082420070104075403800310300c480e880e402151103680341300450404010018950a410581061050072440000e8481c41041034442c4074010101d8010343c0c80350020342040c541d0390010806c20038030b40d03620f484140d0b50100344520704111180100451800e130041c045e00905405081d0f40740e14040c0400200001080c10902c061190312a1030403c1c0c0c0100800c40d2184ca40e40c843d510364141e0f298144000901d089001e0b085031050760 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 381247607 1250 381246357 381246373
    0x50c0d03091203020901141b060f0c190909090c1d01050306010618080f0a030f020606033a030b131b080405120f040303030b041a09070201180b07080603 67
    0xc2c80200e20190b4500c1c149400350391003da480c01260900c000079000410390a00140e0045201002600c070040c6407030301020340d0b074256502e004148000c1401c50303400b02071840c02c0102d99030883d0b0311120242c4109260a210490316256030721042182d1036610700312074005001005111031540c1c1a004c140300b0301281084d03080c40d070405011940f5100180700d0350090040f00c56410381d00302c517108581c202802e6214100d44180601e420403076a03880510f08280e02003488000c1d0603020600c0070031103c0c4180d030050001e00c0d01300210441c4041c0040c91409400020b80c108881005c90a5100c0c2440c0085440b69004251004048100204ca0390700440e0160100d10746920010035040c40040ca081690290902450700d55450404905052001c4001655603d001800d0441d09104601030810303203010396420480490b6480030701c0100c6100c0c10700c2c0300c40540c0301e145540040c6401e400b01503100e8018400400c004101c60301103034080442d03034821585031781d085003000700c0603500c080100e80c003403400c4009003815 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 381248857 1250 381247607 381247613
    0x504050603010c0903020103050a18050106030b06030607021203131a040c0506040f050405060f0a0b0c071d0402043309111303060b0616050f060903090102070e09011b050c0d0309 78
    0x84d108902c00207040c151030790001115400e50360312202c000c0c0300d440803511035540c0344e1402300d00030409070004540105a07075011030054140001c0c400e00c83c11030381d001446d030b03646605803503151034000a0a420a003283c0702c200030300040526045041c0c5100f45502c550150901c0d140c001c3e001c2101e030308200d00602c814403007000640500c4003c03800b2a20203850015190311804041601c1e0850280102d82182d400e01d400203098104c1e4004104900e10101914407040d21a8a503850030300805420f82448207000001c140545040d500168210080c0d880c03a00b03a0201e4203000921081d15503001990324410040100a107007803034041d460342103680044540c94074401e0743c08006c54081902014040d16a6901900390239110315080304e20b00e210340c00b48030042116034504156501d035408031840c2c1c18011603010607201800081511046407058014ac0041030826032400c0588400900f103203030f15902e0391040c0f00c034118140400600307040d0503a00c442c2d440071460400b5262507070501546c0c4c10507107401545008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 381250107 1250 381248857 381248867
    0x90c1c090b0402131b030506130207120e06093001150612060602031902070b0f09131a011107030803091e1903032c01060812130302270a02040504050603010c 69
    0x10f040d05c0341070024160b15a40003090104c0582e81b450742545100280060501400702c2803d10000305540d28080b41c141014240032042c022501c5540c0c00500006509084940c00c05148480385060f90350b40300f0700c544042c1d80c90f09440840907011003031042c80c1d100303000b5141e00030360400c1d800100320014061280351800013966072084561844480d03400c1c1c075000031007034800e014500007044600465625608240d10a0499501900d05207100e103006503080041c07a81540030b2080c01c0308802103051110f000716001502c080c20100c4007444140606c0d00c01100044181010318000d0746424006d0041e0340500040c1814101800190a81035100c2c9841100480344107a44604042e8076140128482c0c41c1c2c2d030a0102c00180d2000c6034041070400711160604e64205502c16400c44c1d500d0021900c800541340c41100d03051140b04070550812321002030900240c240301740706940741d01c1d003100c0090a49031100e44600c50301c0f409540391110142c0000b020040c5243c0343c003480b908090304030004c1140c19200b21010b41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 381251357 1250 381250107 381250151
    0x904031218031e092d090f1a09040b0a020d151805011a090409080c0f10050c0f040e090c060c10050c0a051903020c07031103011406090c1c090b040213 66
    0x5080c60800c05c203800d0030f0101d0130f030000501c4514403d010201c80c0314a00c0028000d40e2421103c1401c0c1402c240000b417504240c1c180c000c0f5000300c0b100c002034031009000c2c40a98001c40303007111140d803202281d200d8a00c440c0c036854018001c0140000180d015081c82009032401a03120582041002d0348212141d140d03c01100d5010b44200d03000505100c581c070b050000d174002d0104000d1a4041c4a40c400b070b25080101d80704025007020a810070071517507410048003090145545522910006000034040e01c2c3d14440e0ba40c0d0050103000c12200100c40000c0043c2d241e600c0009034201c0d0b034102100c1c0d1340e20364519000306900070030000382c02c505000c0c0000c40203002d800703a0310030382007203201540d0b8841505020b40e048400701c1040d50250f0f520030351a0300b41820215000000721b40130390310b40b05005c0c0310101244040f90181000528501140e1241425124541c004413070301c01c0c813801007131004804281c0b98481d00144a210f0b448581807898030340100285c541040b84240045c0d41000480380c0d4541c0d20400c845 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 381252607 1250 381251357 381251399
    0x90f1e0f06050d030503040302120c07060311120408071704060f05160b0c2110030305070c12140c010311190903050a080c0d020c0904031218031e09 65
    0x2030321603080400800038001591000e500581d60441d007205140d840801181f00b24082c0c1c0844505541082582509101e003a240c0c500b107400208050000a1180d0004e4251980352019035041203465059512101e6082d9012038141000251f0356041000c40401c4034810b03110034071410b041a1030218007618086442c038441040180002e81c5001200070344244000c1c1c190465072405940c5440c040b010724680c4442148650210305807050054810081001d038400c11851149007480c52940d84d099403143c01070442195000c0c0e410402007215914420b40a94550050b803000100c04483c03402d41d8203241700ca041a50402d130404114440000c00740b07080b00e42001c030a02801315071406042d82228221405e8200512500901e00044184540341024109044000040e11481d180b00c035800c0c0d070380e001007807c201d40100754a000100480e010f56000c01503c0081d5001041881d100c00700050103280c005000c60104503850340740542000d210f0440d040600c21400e014105c4d0b1304054007407201c4400e40c1040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 381253857 1250 381252607 381252611
    0x1f0b010504050409081314010905030c060708071403130f140904111203130f051c1b03020d0b040501060b04080307080c030f040906030b07091d0a0b0d0606090f1e 71
    0x500405c6500000c50b0700c0c3d50a105049150f46071204a81030303010a1096100d0300050503c6400f190502d40854150021480204a02c3c904a51a69200d980e6001040c059452011a109503103000c50180001c03d59200404040204c49d030400e09481104100b5801481d0401c400d0202e881d01510f40c46003154000340c201003000e44080d000300001d0710303035426a040754040d800040b50300241d02011000ca44140c0d54414943c2a40c036441c3c40a000c800381d640e800b54000100d8810756900401c211044500c1608070741003101080d10784a401007245c90030002d1088621500b600c0c104814000e0a109100180031208611740c036080c60010362559901815101811042d400603c0b000c4c01d040030400c41d5a000500c80341603889580d1420034000a041e244015203030650304030001042644540c44100c01d035500701d804100c2d18813400041540301000101088204e9a41d01c59079049230380c4690404250030f02c68600400c0880c01c00d640300c0b0507500209500c3d55154102124030354015900c05604148401003000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 381255107 1250 381253857 381253871
    0x506100c06061503050108070b0702030d0f031808120f01050f060c24010906151205040224090a0803040b030610030605090106030e150105090112020d05010c021f0b0105040504 77
    0x4410000c05543c2d00410005510f80c4401c14403c0e0160042030403255600d0581c0c040d10382d01c3d15220640e100e1240002c1d49500710f00070704040385014044141d91000b10703150006030326191400d0746c1003060140e107090340d000724081021102450820390299008400e051840e800d17500d07000c00320340d0032451004100d00c03402000c91400000d0b5003c001c21282c988500140301c2c05c000d000010000381540a0060456480c18041c01040d942041c0406550300350700755403140081911403096400505018004990200c05100e410201d233401d945290700c01180c00b559643d581844070108a840161903101d151240c00a1200704003406282d03003502da21042c02e54001111040c40c4208900804250300711a50006090001003610f5506034401c40e407540c560000c07551400011002800d42c0700f8248549984194244010b002203410040999003440c8090700040d4903030a0780c1d40c1d15080d078004000c000b00590011803581c80780b050458481100300a1000304025411001c400203000348920b00919020f10303201c4007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 381256357 1250 381255107 381255113
    0xe15070c080f04061e08060d0f14151006080108030d020a02160b0a0e090f04080f1c0b01140403200604120b04020a092306030a050f0705130506100c 65
    0x881d10502d0814241a58031521a000505160030309600060641c412807141500d80c2c3c0508900c1e8000c4400515148581d2003680d0303520654407480c0411122245049501c01e250340080104090501e665203001c2c0c030340d14103541402e120707000a074410400c01071000e004011005c80032040380c0300710707081c0c090240e82d504804205901e8180c54001103c07052013100c0c0300040100b8080007070008840c09981c0c000c00a500641005901c0300300751160f022445044011070000788005006054014a84030564249401100052002d900c10000b0380c4c0a5601c0380080d507184c0d07a11a01920140c02d0406c04141854203584a1059110500003a40703440810300108034000c3c0c0c3e0b0001a01c1c010320721008840d0001072580350a58294500b51022405604454004034419501c0d0203890140c5240c2c100182c61908443e00c00c007a4420040c06e0290540a003048074004650b0910005038000d0420000782401071a0205002044030170b403204030085841e101c2404456900c8101440b030f000c065142880010409003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 381257607 1250 381256357 381256373
    0xf070f06060515030109110316030507021608030c010501080a030c11010c3f020a080906040302060a05070b090105071e020f102315060c01060e040f05010e15070c 71
    0x14001607440381e14500c00fa980c618400000714181c0e802407805124a544152407200035020554408541038a900d1799070f680b00d44a94400c5500003002d00c100ca00300b4001201030741c0454003a80040485800004022072140c070240215801041c0001c01410600d09039100109108141c4c4070042082540750074441451384116540700407207800c4545240c81c00e1031400000b54007022281180764009407480d103189402e4822507803d01880c0300e50050508046569161902e80e41304192042c1d00100c180004005a103600020f80048001629265070720689030618003004080103140d10001d83c1000c041005103907014900c50900d85070445804030f04051854180c0c182024280e0a400c42d12501c0038000030351240b90801c0680c06004100b00207802d111201a0151950403981c010182c0c40d241c01010240c2000350003801104070380000001c00c3c0d40c462043d00c07882d41003a2803e503001846070104c5400d04c5001e100e00d542e25030814004220f20b00e150750801d4000c8400038100020b10418400400a2100300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 381258857 1250 381257607 381257609
    0x8060d11100302040302010809071511010603081801270e0603030c1b010e03150112030c05061005090a150b03090c040603080d0e0d1d01110a06200f070f0606 69
    0x40480700d40c1264554010001c1d00b15100070390028210102282c4a5040422071406071908980e401201100d140410388804401903140da84d607650300c07030000000ca04484050140d08001c45040000c2040340400148000c5002c0420380c061080c03003008009a9898298060486000744c4880409903540c0001a00314003520b41d000340305011309032007000d44e107004000c0703507605030826203440000010480905540f500e2120003902100c10303040060050780000404840c00741c0c8a441d000020509995860703003010010b9801e64202c070a100020b009500e01070b40c0d040e5100c0d800d450100203034088004a41101d9a461045400b070035400004122184030603c810b144406000d082803080d150340c0e280200301e692100005810141c5032113040d040039040810110002240f80d50b652a4034040702c080629900e004d070004a0510400350b80c444400c0c0c2c420b02c01c98180c81d0142000040c1490400c1c40c0051121100c502e844000703808110060442500b070094406040e0803a1070210910f00c0e03894a40001d00312 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 381260107 1250 381258857 381258859
    0x8060c09091302090a0920060d63060504140106030b060306090105060a14031614030c010801120305030414060f04050c0301060b03010302011809020a02010902010e090708060d11 78
    0x182808000301440c036900032401661042440c10003005e01d0300804101600145000c40c0c0c00b24080003203a2501c590798100405c500c44000003010400f84ac03150212502c0c400445440c2c0c10360f0400f41e200006864443c8541d01c000c50380034004100840305810b9101d82e1402107005004643e564042003d20408180980c08810311030b00030404181c903030404200d441021160740f4883e1140f000010b4076180306000c0d0350f02444020702030304400c0f428885056006000038020940520503059115055200700700300301c00502e140e2006041c24042041854103110051344100d050181e40e100400c0140c0c20744008004c0d982c4c061420307a40302c2d15a450800c59035244031100003428890f00050061050070314100d1405940f01e54121007010142d2800d0500340c1e501440b035041032400c00d100400155003d8152080400c5107034413400241902d401d80c1100b240c211102c03800040c0e41d100240d004650b00a140c006034201c046030050200d1901c0c00c80200010b1000780f075140101d584490100400a85110074081400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 381261357 1250 381260107 381260119
    0x206100e0424023f0c0a030b040906090201020c010f05040b0708130803030f0108071212030e010614120c03060c0c070806070804060506010518010e010903021201050106020708060c09091302 83
    0x58a00603a160842d000c043d000c040a504021198241c1c0d450145801640640010103419a05c00042502c02d81011a040080c140c40d480305040c0d541d0390b481481c08186c410072000583c14102e000091420701d12070610b5040c0b14003408075403503640c0c2110030ba4044410021031195a0402c500d80402c15001d0520f80700c0d2003120042011130311003804000b85229440c030104e402a01e030b0340d03541100c0e9100781910034010341c07548006100300460f00c1c280e40f075544042c1034200800c03420342522030242160326681c0012441407034119800d4042c80c080394003e9403c103422000b0013091200c0f0000039100e41010b81158282e800004d41600011018070103140140103e209690042c038080c44080c08501e0106c80848440d441d100000f1044c0d80900207640c1d602e0605910030145944d98001921a994203100540c140100000300100581d00c0d296080499440440003141c0f6525052000e031901325990458815a0406800c00c01140541820342d0000c0904490000954880708085412031403001b002941003a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 381262607 1250 381261357 381261367
    0x60c01090503091f09060305040309210302060a140114150a111204030b0f18121201050d02031005040809060307020a0c060e01051b0c18070206100e042402 68
    0x1c004070103081104819515046900142413100406000007a6888086a080e0b1028085c0c40c0c4a03500482e800752107801c24a0710b00b525028070202d144160500c05011102070070010080690510980b50091580c00040c4000641d0f011980c00340388050040f4241c0b0035609001241e5603403015041405105000501503a0708010f00b00144400d400a034070792003a200f42180d0681103601c03001201e00302c23908101050a03135182c81140d241007400242500401c0f039618001d00c1d000083c20300c8002030440b602e06030265110b1404171010419441688481e110b2070011000754003607100030550440c0d59031514000900fa694a160041260145500d40c54102402004028180d50002000b0324080e025402003141180d403401f049841c239803000c3d02940052014402540c103203d2991000311492250300550325030301c00c01c0020400705c4c0869081102c10146074800e00900319010b0103030540002d81c2c1001c243c24242080c00c0801700000262000b440c0340d40c00c3c94054082060720b03010402000c418401075560b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 381263857 1250 381262607 381262613
    0xf03090708072309060409021005040608060906030706050d060f12020111120d1a030313050a0806040f02010e04140405100605030a02030c0d0f0f0c09050a0209090103060b060c0109 79
    0x15440c980184003a038810032a0214048a034141c010002c500340c000d0510181d9001014070441010180140350800c1d1180301d02001131b074900c804140c40c10f001ea0340d0303e501c0d5442d02c800203009040140006001c0c2e00c0990900910352004101c10b0181c44580c00c0403075a03244505e0702e460060103643e01c003000c200340801020034602841429040035038000d980754190390919003412038032202548449110400e08000d85000700b44903070004845103444516015000c40c4080201c0d0031680000c69429003032400c0e410034070a41c6440130b1214007070112100101300602d010741d2044100e14040383d0190501c40040c0c040f20081c0e0ba01c2d00700020b0071740414107105040c101480e266590b0715890218a01180c03d00d1400700c7c0600307000034100500b580082c000c05520081005110030040540b00560319017880102c0c0344049000700300c0a6412920601240c58200d10304001d16084a001901083d681170040081c2c50450b83e0b9004298103403500050001340401c51280044d032144940e240c00c90455007030201c6403042c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 381265107 1250 381263857 381263863
    0x220315230a0f1b020703030f030f0608061819061503120e030c03120f0c030903070303050a0201060501050702011e02030d090605010302100503100b0a0903081215060319050c0f0309 79
    0xe03119082018080c20000420440f0702c00340200c244030041e840541c1c01c10210b4421040d00c0d5804842e820002440c100c280450000e8440d02e402c040050b03800f502c18411401d0391221a8955a41c2c681e01800915000c842801040400c0c2d010180c05640c503010440d030140390038601798000310351004000c1d414900207040a400c0c5450104050302c00d0090b9259400c25040106500100300003458070145012092001d01c25107030000441a40b04e40b1046c000d1400c0c0c0e8804001e00340265000e40c0700c0c0381d112540554000d0a5440075001181080000d003e4400140d0300316403130350031401ca80244902e880b085010100c1c40c6016690324b01003071b01c1c1080010010300085030b1000e8184c81c0250740040020b4540354054409100586180c2000b500ba11010000c50350903502825040d5020710b041c120890740ca4448100300d070002d2500d50600e888500034801c00e1075098000070103414041d40d00300e05601d07100c00d00002c6009440208074407291200c000419013200d641c00c4800c8000309000720341c1c8071700b001540306039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 381266357 1250 381265107 381265121
    0x1206060c06050901150303030e0f1e12040b040501032307091a0906070b04240f0e010603030f03020c030708031017010e03040504230a02220315230a 65
    0x41481c601000300c0c0f1041818010ba15100002c40d1070142d2407869a03604800030804401824814003580020388840142400b00b064900402c4200802d881c0742c00844d00d00300800030031025030700c1c5030400080020444500543d03089500900b00089c10520040040725032125802c85004c1c0c181680c010884990740114589007916100951191403071018419480c0c24460070244541c00442404010000b0b0540ca141d2540944244900c00c64148071160a44010000490701c80c1c10359200c02414042520714820082040d690200921a8030318580b00900483c1d140e9500704205600040d00251030071081040310307200d540c40304805070b49207001c0740711aa40c0d10b80c0f40182c0402c3c6003144040c3d014208140100d01c0c45e20440006180303080d103000108030013000751072000d0800342c03011080c4800f03000b0006ca00f02d1103020ba6070030150b80c03040b401041211485040e8007030320051249801c1031000c40c0a41320010082e4242443c0000c40c20950071700c1e00480c561603021852006007030b2003009220310264005007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 381267607 1250 381266357 381266363
    0x3030e0f030109061d1216022106040b04060c030b0a06051803070b2d041404060510020a020a1203080c2b0b01080f010b07020f060c070305011a0604031707031206060c 73
    0x6500c0c1d1904082d661211f00c69000c4543c440145244040c0245c40c11089990003921081440c0400001e000c41c824140002141c1c1641d003031840d03104220512016008448107056580360810103c2805c10010303a0f5441140601c0f010000082900201c00144410349552000c00030201d91080f41e55007480e043c29806801e20007403000402d00314160382e103007503045420706050041c2201e040c0740c00c00e0003c4029080fa0320b8140d52041d100d850000d8680c4606a40440e2140c29501070529800240144071070003e550b80000f856103134002020000c00d82c40302c151070300003031030410300c03580e0380540d50081d032410792041005000f002071802d981120400ca075200000c4080203032204813950307440044900c00c3c40400d10903000084000c1000a00524101140c2c904800b001000b143c18190303444c29540c5450741d2500211516990744802c0690700c2c20070040302628440840390a0f10b8282180d41709280550421005240c490001c581c0d01e0405000d88107101d890100b25400700017403542c603040140304e00d110700710035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 381268857 1250 381267607 381267613
    0x30708150d150c1e030e15010311031218010e0301091e050c0a03020f0607020415260105060105041e050d030f121a06070812040b010e07080103030e0f030109061d 71
    0x41040c2c60180c0d0341d440010b8144600f804c01040f0440c819805004080c49140c0c3c00d000b002c025100c5e10540f1444540a140500190040004140c0515181200b10800d1400c1c50a003885000c400c40300c0551480c40d00c5c202841c0c00070442140c0d00120b4050000c510b4000c00e030140410020f02c0c40c60800c04669203880c010022101040307455001d008548601d8000a900b20540c030300300d4042410420018100d5038400744c800521480a00c00617945003280c4c1c0c014070400c2caa21103298800106000008010800d520020001ea0800030000380181c42288a841c0c03580d18124100c03000038184c044108002e00c4050507003600e0030200c0c170f0000c04182c000c92521020641e601e0360880d00f40110b1066486445140d00140040d030311040802c1003e420108048a21020401c5000c00710482481c00318082d51040e90000b88035418050043c200c000000d200004000040d001000400d0744109030301ca217107400b610440c1d031003011400070030b02400d5501c034041c02d031a05040404140340841c141c2003910340a0f500507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 381270107 1250 381268857 381268871
    0x60516080618190507120e0c06090d14120a031409070b160f050604110118050603060f19030311070e0c030c071205030f100b030708150d15 61
    0x5a030000c809495164110241d000e01079082100704240303e030005807a109581c192071042d4200c6080d00c07801c540e000c0c0001c03100252003a40e440c032070103120314039500000603000702c0c1c2d00030b030108000380a11040c0074800e80003102007505000e0b44802c10010304e444142034603000c06c0c44020182ca550311031030400300003e140041508000c2005d41c400d42c013441915014001c8076181ca011060180c0101440c01282220881c00764005294211240f00c0b861061001d080702d0b10f0642084041c440000c40e450b03061012852103155611040254041600d40880794181c1365115400807a10003801c80712001e40182002c40710424450040c0a84001c407446aa550503050b04c003c0412902d58240b0b04c21004c1920700500883d4480c914040650b80c003041229006041c00d0741a00e90451100c0901c14107404100c000060040003150800340d10340c0180c1e444046a1a1854000700788520301c001040070701003102c80c0010a611a01c60b021165100c80001d0294400010500303110710003002c581c129880d11403800f61 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 381271357 1250 381270107 381270151
    0x20c19211104020c0604110f100201140105040504030207030f0c180b040b01020111040e0c0d0c09080d050a0503150406051e0306090a050c0d030207030c17010c080c160203030f070605 80
    0x212688502c400c07005c0c102a0b15155603c02211861030729265001c0140056965161544550f02500000aa0001c00c41141800d0103410002040c2c012a00a40c2030608120100c0d400140c004200c950101000f032507011941003d07403481c4540d410412000018008003900c030300c26a00304108a0740d04840c200070765540d0f0f80069088850816040c04244410f0008020a940000200c2e074001e83d1140302902d084d298409010444039403241003000300300b6a08051121000410804d130b050f0f5003c1c281a89482c07185c0d1300c0502039000041008a170812842d40ca4130740c039141c5420090042c20701400003640c2d0340d002000120007494401c441406071113581c000401401d000151441600d030000301500c403940d2602c06106003461065400c0d419403180070302c0080010b0b25044050f000b4010281402c0300400714400c51829202694000010001c0c400140002c0b0315410f030803038180191642c140400709110740301080c01c41c06a60040504804040740b41c1c0700344401c5400c045e1181c120b44500034000f2609803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 381272607 1250 381271357 381271361
    0x90a090b0a0207020a15020303040c0f03080f031305010606050a0f0503360f0c090a02070b0a0b1c050a0c0f0303020709050a02040305160503010507030b01020c19211104 74
    0x154080c164858800108401d070788258000c080a5002420a10200780c40f6032010f00c844100c0c403100030060f400082003001b4458404805005413070400a614800c03451a1140002801240c03066030100d40d000004ca600002080c4000d0359075a408002800115602c0d1006040c0ea040ba04808000c9010125440d0b070f500e11039012644900c101d50103840210303000b001c83c81701034121213561600744035100071200e00c115004c01a40d1040501c540041400c024480c09002208074040d100740941130050051a0000318000f0718158004171005002401185010000b0807521004512006514120501d041440400704040208600485001140701d03030740ca50034130002002c2d10010380160003110b818441c559950f081550040c60341c013405814161603499a80c00c0c01088400a141c040c1b09650820103400d0078091154030070528201080300a600b02e0010707484049201c0307030718171070480d00249040315020708031094007074682818580e083c8421400f288012183c0d40c40240d440b8103101b100c03080c0d10315041c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 381273857 1250 381272607 381272621
    0x5130209180105070306080703060e0102130b030403090e040b0a05090309130609110403080a0f0519020d0f09080a0b061f051c05010b160606030204020a021e1c110106090911090a 78
    0x21030003e101e0203285858ad0300080440303010400440d5001c100d0640c152299022041c00380200c0c03a09140c0d0b81c2442c0c50040c200040300e5001681c102c04403400c00001c80d156106e003651202e51800c011401e65929140d07181140704060001d6441529104d0242000304d41d64000c0e01580c072080b604020341041d0008042403400303248001840d840d41008000c01c4140305800394440b41c0c0c06414200e003808020303c0310342d290203801d502520041e406603030450281c41d4450001107007001c9030f00704051361904102003540c650207200c00140a400c4154042085919023002e41100c40025580c021501c80f07641c02d000b001c60303000740c1c3e00101c80400584180340c140180e2107010b04846034001210700e80491406c0c00f09090003000d0003515040e0340d40000001584550005100c020075039805084c0811180e820380c49500103142901c216070f4046164007400c100c184001a1040300c590a161409042e207400c0d00d4054280303500004000303801c00741040c04110711541c0d001035968044a4200640d40c030312140f10112004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 381275107 1250 381273857 381273869
    0x50c06060a03170c12040b09040b1e0114090303030106020f0d0302040e0f06040207021801230303090f1c080a1d1011030c060f0103051c0503070305130209180105070306 74
    0x310f041103000601200003c20b100d201c10819600c24038001c00d1403542c1d40d0410350100d6158040042c503d0301c1c5103468070680403450350440f5080c640006030041c4420403011100420b040c000e20407286900780c1009410b680a600009048035a290307103691009480d140d03440300c9625540f01c0c03034000304d07603c50203030080e1001d40707d08503504074160f034400c4c4080c081064040c01c1a90015801c00104e80503031a07803500c1503e000310441e1004210351408441c64500d03042d40c3d005000d42202c0700242c5e1135550303002c0112210b01c542203d0103075500c00954002407640130714050411041d200526036404020381c07800582072044445e01d03081c01b00110b102c5a44a6a081c000105a005004080c0a407c5900178101c149074078400038100d900b00520b01d01c00d07600d0003005660f5028001c038050010000c100c401c2101d100c0f03a806100e88031600013070342000070381540005490300040c143c4650000b001c40500d91004100d043e00249440c00d207040c4861070403800e80b103001c513805940d402c2400040d903990003401040110b4107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 381276357 1250 381275107 381275123
    0x40303021903120c0c050a110a0815010b091203070b04021302090f010c0309150210180c0320130e060f1306020711092706010e0a180210050c06060a03 66
    0x34103d6650001c020b0f5080c800f0510050081c0d00c0040b0310100a4a0380c103510442100103030301030070000c000b6100c040d64005800ea030f101c0800d40340070f2804180c1c0c3d181160024a035040d22003000c000001d04230600710001c100e0070312001c5400701c1846000c0320f40500a0b070007a90800b03213910300610918180d2041c0a200341d0002c441686d04042e5503c900500c500950080c0b8140e00c115444203d4401e03003068034007003180164441d440c003100c1e288447c40381014241103558002c1a0044a5603202644080c510008c0c0184080190318900d004130125103000080004000303051034482104200700418902004220320f01c2104009001355502c24641400b5001c440708449000070244e48d440d01070741c4800c1c0e00721188100310030001d070143c03112401a80138504002024040407042e5241c010b00b40040b280741d08095124800400c0340101c3c0803080303a080007400202280d0300309a41f8900c24055010b140094001c440140c610100d107074058050305074a046101591201d13200d8008103d001e400d2800b0180c6162 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 381277607 1250 381276357 381276377
    0x516050103090c061b021c1103010e0c0904051c12050609040222091e0203150f04030c0318031415090c01032a120b03030703090501030b0301060902030903040303021903 74
    0xd800349201c2e65020105c03020995941038103a010901100e90400c3c0c1070100341000543c4010451050100701301c0780d8059008003c504030342c20002d50769441010007207001e41e0051001c0740905c0404c0c00b0600380c028500e000c1002810800200418400401c0c43d06210545484085a2585454088140520740007040046e00c540180c0001300e41705006810340460a40d82c4080c0702c001013481c02d40c4254440441c1c075800581e075580c018141003205141510241010083c00c10200412441c121a04503416140110607603051f8502a1444958640e0740c0148065000c0000100050703140f000541015500c261441d401e64084407900c8880240d0307550540380c01c00c03058601c46503c2507000d00d01410783c00180c10102c99001c0c00000304031035604007000006003048600300003985140130350b9800b00c0040c1c0c0114600340e941e4030002e100e50f016025440c10991541d080c403d890346c003508843c025018210b401c65032402d0041d5155078940c0a0b100c100c0c09401511807442904101d40c8078220b11582640701c0c00c00d41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 381278857 1250 381277607 381277619
    0x1060815030a1205130e13051203010305060403051e0c06040c090209060301121a010b0c01060e04030e040e071701020c06060a030215031b070807020a05120a0605090f0a0516050103090c 81
    0xd4100c04a840048111480b00044a50451b40841e00441300001c1c58042170304141041c40c2089e2004040c00403071a4100010000180700080080c2d10a4061070515140c4c04068104c0d1151782c8800341c40080c411020920104d031100c04112640900d10070401590a559214240d60590182e414500c0c1c1c41441132004004064030b0f070b07141a92051041a0204800d01034a84a07100000300b038119521029010612285580091042c10043c0c01d0301301c3c1d001914641070b600106202c0082c1c9807507005035268020300c0a071040412554010b0101c4100d204c0c1107110800c3d8180c003e410034407c51401384506004a031b21030a0120f459402d40b038001e40348100b068160030100b249640007a006080082103024549150a00c000240501c3e40c41400c485645480c0b82c01007004100281d0446840f6007100900946035020028a550395251b1082000c00c0503650728040301d003084004003d460360381c004d161440c0208075011902100e001110340c0c0c840307085900d41004400302c5040400040a8540040044c04a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 381280107 1250 381278857 381278867
    0x702102007050c19140418030f020a06111c0c1b0c0803040e0105032a011d0603010f0e150102030a050327030901020705030615101701060815030a12 65
    0x3450280044800010640e00440d0344039006130b06607940f1000303070701080c84041741208061401c0d01e0100c80c1841103ca41d14500390000341c80c40002014031289001e240e0f01540240540306010350401c0c0c0402220f121401500300e1540110038a149074980000b1406299074548141c118040069503118200d5441500183d0000c03181c3d941a907041d00460b50015031403204000030310251250589184585d403400040c98036001c0303170149205ca010002c1c1010200d1020600125a2144091a112140035130b040417000300b00c20300c030207015008040000003164004100400c0803c070343c00c3c1a81e086841d916031491415005000b1080fa0040e00104082c0c4d03040c80c454406160001c0b40d8034065903110349041004101a0092a1110715030781010440c2006503030144108001044250301130300e0645010071101122100007000349118030000c0308010b2001d48160064004110900c0002c0d00650b1151005040e04508440e04100c110075003818107140e00f00858100c081640c00b41203203030304022000e01a18 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 381281357 1250 381280107 381280117
    0xd0e01150314030f0a0e040b030a0203370609111905130b0316050a060203070309170f06130203010510061e02010209100c0515010f031713060807021020 67
    0x40502c01800844d4415488000801011950340c8440c05c88003c04d900f8007080c0c80c100b604251203900200d400e940561000305009008024901c03003045015501c441041180c00c1c6000b100b5000d0760345c0001d100804c01c065021840b0345004019115090804400b04000c0140c0c400c1e20070020003250f0010003543c02e0080803c44405c40481c00440d04001c0840464540390305a40318414208044404005c503040c00c0304010702500030b074406540fa1084548001c2d0603a810740c07040c1c01154404142940c110982403001c182803808100a031011403e0505c0702c090b454907401400c0c2d2282d46441c0204c1c2c4044032914070b01c000c13201c0b1900c0d00d1002030814160003d0200c0d04071040c0c401d65408000b096130a41e5825040d0f0048100740e00d64080381c94407824064078203842868034440c406048130040c400d000009100c01c00726035000e0090911041103c21170304613030140b450040342519201c4000300f4a03940002c00503205049503801c5542c08000318606400351007000c403441c071414400c048500003e55202c00104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 381282607 1250 381281357 381281393
    0x503120a0b04051315200c0304050d030804050c0402070f1e170406080105030f0717030d1b08090a020604050d0512070c06120e150a0e07060201020d0e011503 69
    0x146100038078007280545100316030802d514420b5030076440030041c04488480090034540c5d82080040781c1c20712031404140e522103080c490610003080f4030030140c0c000c200700d80c00307080b0240800340c82210354600030303000382400c0d00c048429000f4110000c1d00340c00c00b44259002c25400080c540c50803015a101c011100e202042d070b001c041c1540203503103000300d42c01140004081c8024404165160302d00300005014007010303000607110303400c04104144404400203a1001fa030342808034010300c2c4942541c00c50720714484c0040c1160054104400344001d100d6a015001c0a0301140c0c5a04107143c0c0c504c8582c40e210003207941c0081d404081440140924104500c654070340b0303845942203440355480c80f540b00856070024082111480055507040c484190f000c9002c040302003022405101100300b80e00040d4854001e1640b1102030191440003070b0002c3d5207030b0030540508805000361000e241d01d484000b0302035400804108501801d21000464106c014410f81502040002c400780040341150381b80c0c103440003810406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 381283857 1250 381282607 381282611
    0x12050a0807050f06010b09040b0103110d27080901031b09090c0c1505011403161428031b050604171e0105010503060c0c150414010c030510120503120a 66
    0x41414503c0811100b8044c050f56070509848a5884040005440c5440c440c03504050409800c040450a2041a00c00c40244001c020880c00c41d0145041a80c0c913950b4040482c041140704c10702c050001400c000c000c03075602030340c0c00d001c14002c452040e000108500e0082c80040c005200401200c1c00340c0d4003083e00790041d0f2170207400030641da440700c440300e201e05211403403115030301c100401100c4011582e041c80b02600390042d2041d09441d08207201070107040d21526060074610816445150748001d140e00480e80f004840072109884d161000450301500e00040b51460450301118284090f540034003411203c0c01481c0c581b40c6408d024a034901001e84410745c071500d10a03e10b040c05d840b01088048940314640800002b0550324050425240030005002c068a0300b00801c0b2441540d0703000b2a4280301c0300c90303020700d1508503112841c0140d9113008020940005501c0c003c028200682e150300002d0090082c186001d41054507a050201e0001c21148014540d0380304116400403864102d01056001c4040100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 381285107 1250 381283857 381283873
    0xb090d030306090c0e03010c020d1706010306051008180f070302130603081902061b12091608010212090c0d0f0807020a060905042306010c06110a0302090a12050a080705 74
    0x1000030756682100c02c80c0812120017078800142001d200e104500d82c543c0c4001c0042240508010380012142100c0c42e01088154000a0340e59000303030040c40c000c00d03000d020110082c0f0b04000050003c02c040e59608402c2a80107100000100000b03000d2900c020000c002e800600d01c1c0d98200103001103070030806011a52510400004546800080c140b004e0b0701000004003504810740090a25000500741c90b00c0406000b011300001c000c2d10140c8102c14001401c1803019140c003500c880c540b004a400c0001c501240010220b4046019006020b080c4103019056103c1e4403a01c5490342c41e007807015161a040034070300714200049081c14454120f181e008003035a5141c0301068000c5891a1103030b07000b0102107007201c001000141458401d4446d030421400b02d840c486160900c0e400b0f050a0040c0682e4100f003034009003001440429400344900b03d003542c0403140c0e5246e0300718001d4065080400014031425407514005078001220901817841c03033b8460301400713400203a562240480d4005400903116840760070b50f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 381286357 1250 381285107 381285119
    0x108070f1e110f0a0812040f02040515120c1003050c04170d080708151e061623030f18060c010915091e06090512040905010905010b090d030306 63
    0x40003003036114140e900c0820b0303400440c00d00741c41c00c20340c402000150380c011045400841c11250603500280101c0d1603504103a02d031030500212403400ba0f02c1c065449442c00307040c45030000303100010f510800303010750700000004040001c158a511103007507041d0b005800c10007808038951095000c2d139403140031110318a04080d120100040106d80340e00301c90526901c280f0600751101d8101071800d81c401010300d407000303036442c00b00a80c004103030032004598081c400d031a0445107a91504010502c407a81c0c041c010300c0e1520016500745099060790913055464501a6607410f40e49500c804004050002400082d4a00488100b0502c015806900b24030502c20820f600d10743c03150740d12001032120f030045100100d0561401c1c1408000c0c050050703040e0401514110b249400148c00309080c01e05140c0d00004030000c0c04107800c001001e030a500100404500500c10036040056000005e003080d619801410042680c0f0b0f01010001c6540078010b0b00900c84044c0b200c80c2c5c0614050024039200d13403283c6004124141d46c1c1c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 381287607 1250 381286357 381286397
    0x1200a0804060f0305010b21060310110301090c17180307060c080f0105030c03070501051b010203070f0e0f010903081e0309100f05040206070b0a090b040b0f07020a020108070f 77
    0x60003800002d00c40b02043e841180d41401441e01503c1182440e5107451040d11076401455110282c1c0f072540502c060006e02036503410310011180800c11101070001d68083c98000c045039209004568401d803a00c0c13090054030b44a000e0880c0f03050400140c04815480394403e501c002c0115010369525884200100c02c002050b6000e02d000c109001c3d1140e411504001c6049220040140c0040740242c5c4105102e03061580c0000d210740880e00b0078203041da518014602c01840b04182200842d038550f0000062004036503120044458240c0156191540400b40d04108513004000c1d0806900182d0b041400f0310100f04285c0080100d130102140d514031040a40000035947c4d0821034030f2031083e4016101720780d600d114501074004200c035140300801c9189055070005d0620301840201a01e00f200c20400296480b425510440c0380a402218604280c500b915140e88041c0048401c0240700d4086004211034a000265004c403d0fa4141c41d450390070781c3c95000440c1c604884210480030002c042e5001d000300c403240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 381288857 1250 381287607 381287609
    0x5010608010f1d0a0507150306050d1a0f01080d0503071106240126060102030705070b0306130216060e1e1510060f0e0103091a04060b0d0201200a0804 66
    0x114004980d00c0a4950340300842c0080c03121480d000e030000d00c4000006500469400203407401c1f48424103040311120800c07001440d851f080550000400b00603078042c4540c2104c039251030b440091029915580e8010b8000300c3d20428802c41e28642d014081030190140140095603202c15146028002031070301d075500714900b0505036404c400702c00c40d424480c0321007041043c0707001280100b1f0800711004604119441a500c20a00a89001c50740b18000700d0903a0b0300c2402200c0b0a43c0d040400c80c1d6002d92203072070548130b9174015110503200d50420011b6490852507402520580c4a140700c0042103d0702644494000e8405001260384c1802500794450b0b421b40001205684402814010048076040c50b040c0e601c02c0300040d1500b00c034912072440c00c200f201d42c8002851511031080c40c03c81200e001440040c0c3c05030844482c0100825401031608040002e850101482070780184000c0c0682080d500901411510340e03c006170010b44c0c4202031a010a0f10259a12072813140401100c1e4842d59a482d0340926402c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 381290107 1250 381288857 381288881
    0x2010804030c020d0b07080a02070209150d050d021615050702040b060c010e0a061401050306160203070803160314150d020f091e012102040e01060b041508091203040f0501060801 78
    0x904414441b11035804540d00f64403203462001149001c542d500050b8041d00014a00302d1100c0702403241035602e40721020002811644502140c101c542d110b0001f035120302d0082100f152002034510005146c0c1700f00c81c00d100c506409911110b10746515902070001078000d09642c80d400800030400324251100901c2103e03010407945003d40b099110720324290382568410321042201c03018003c010b0003169000b040e101d8011480c1084100e000300070490581c01d50061101c090800c40700030041005000c1d20306d4030a4403030021590100100f8610300200c100c6804c1c2505e01c03408002c01c0d000c4070009414015450b4a8450006000000c2261441c00207030003d40101d81000c1e1500b1a02d05003d0461404d4024a0260a1040d81c00742401c10590701101d002c1c1d1b1000e0040e104a45804641c034000100f9070090380501501c00c0300035074803074648a0059070484c5048001c000100c4a000041c0c039040003249040741c0c0708082400510b035889588448100749410b8805071481c1d5030b84c1d9000124103c0c244a00342a03c02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 381291357 1250 381290107 381290123
    0x303020c0f190606290304050a0f031d1002061602070e0a020918040f0b150406060509010909020f0d020c0f0102030a1508011e020a020106080601230607030c02010804030c020d 77
    0xa070310b10300303101520041d80c403100c54401101c179011a0750454400b45d02e116018144020346030341e120300b0a18a03140f0a45400f8020300403005504092562104c40b12060301440300c05200e00044e242d09003c030507400700d0950b20060304904041403001071b84503071000900d60944121620303191561a0a18031003070950720345030300c0c030360000d03041e507250030326a145030200c0d0041d60b18400d0310b107825219504004903007800200100304480001ba04503080c520340c0c100421000d4010800b039900c43d20098016230000c1411400f2070740040d0700003080400e0b402141d90203941d040c10b0900303010300e241c1d114011f508401d20980d400c1c042c802c403c080e1180301348040c40c8920300d24000401c104030000c0000e82401d41070340084100e41d04041004801d0383c200600c4580070b00019400582e12018543c04078014412900140c503540240c40000031002d01204040c0ba020120f040d180c048058220100502c2c1e100b130f81002001b2602c4001000050b40c0122519903000c0d02034104003829001e542d0011703011911071101212060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 381292607 1250 381291357 381291403
    0x1203120b06092101271101090801020a0201051b041a0304170d06301b0b07030c1101030c09060c030909020304080a020607031a0402090f060a020f010b010c020109030303020c0f 77
    0x21402d000340120003141007103002c0602c217030701e826038404c0200d40c001801c82e0713031030f06c040c06140c2c2d1007a4916802401410005c540700c854a8400a029200c01d442c401d000441001d04a041180c41c00e044408491b85800c1480d490a40c5844281d03041c0c00080041c1d4814110001212000350054001d01c4580f403d4140028060300f088020421900207407090b1805010a00c400c4030b24801300301f032048034650484030b5180b070711900b9070b42c5915450b42c94016034160200401c51108042d04490100d18462140c00e40340285200d01d0011012901544681c00000302002e4040048901481c4003442d8103000e89000000941c54012000590344182e0b0700710b9004000080b01c91105034148611034101e4494582400310004000c008044c41c19822821481284d00040262003545c4403504c50040c4c1d000034000b50f4696051240c0a91200c800030781e030924a500744100f4103041d41c494042e0501c032a034144c403420b00c86070854801300d000390000c414020f02841601c4450b002824100144258480701000b50b03c0c1c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 381293857 1250 381292607 381292669
    0x30705060106260c04060806040b122404030206060d0c050312070515090304090f0b03070605090307080c0306070c0615030b07120626120403080909011203120b0609 72
    0x2c000714403c2141d41024030060010380001a8200e8003194002d14004065848480002d4001c00700c40140986c40040f548050000c0880480d8003400048450810740156a450003140c0c51743c40c04480003001a042000012000d00e018102c144084d40954101615a81ca84010a01d8103d6940c54440d5052012a0810801c10308000100f031180070007000c52401e0400b80d56041e030b01d000e10b00403040000d48600c513050240c8866400300210680050488070119514100503102c0d50103503481501a00400342c01154500000032641404c6402800401640d6140c600403034080b44401e20031140c017916000711034091402c07808584091401100f03a01c1407400d06400140c41800750185158919090000400c9452611400c200b10f011070b000c00d113405091b4201e030385418203c9004075608010340107d404828840740300e0103040c225106468440f2166290007190342c9030902000000c0c00141b03450300b242da800c100c54002e816024030140c42541001241d100140104c030044003000c00303921500a0712031203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 381294964 1107 381293857 381293897
    0xc0312020312011403190c0308030c09030d08091606021009140703081c090b15060d0f0b092d06131b0807031104031103030705060106 59
    0x900750384851071000144060800e0714041d108000e05086000b01040d40c0305402c5410003203007c980c070707d0355a501402d90300060507074150b52030501044d03603640c60400c84001da4144079281c44446207015600036151840710800d00707904500400003000421b401241e02c04003c0150700e004111701105081c8001d039503d800110480c54814003000006101760000a0100880144c800d0b115a0390450341000c00d4a909031009004600f6010224816040320514458000301c050718072400d100100c460710040340c003011400c1c2506070311100f0b00c1500c3d2814a25859000465103072000d810556411000c440d00c204032402e240d4020400c02007012980e400c1401210080d82180030301a0348010004028442c0001200d00003044250303000c554014024040d19071741002d122201030801e80345486000710a0b0b83c100e6441d8044c00300f00b003410041101800b1140c041d0a0b59110f5500018505d940c40c0c030 = true := by decide +kernel

theorem cover : BRFrame.Cov 381115107 381294964 := by
  have h0 := BRFrame.cov_init 381115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 381115107 ≤ n) (h2 : n < 381294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
