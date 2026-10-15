-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4694
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:26:26.396252+00:00
-- url     : https://prove2.me/submissions/01f2d11f-d2d1-4eae-ae74-776b5564868b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 844064748 ≤ n < 844244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 844065998 1250 844064748 844064761
    0x50f0c160914061804021203091009051e150d02070f05030d1a150306040e0106060c050c0315041113060b0a020c0307030309060f030f05101502061b0a0203210609 71
    0x44c50003011503400985640a42e0350364080000d0300c2100400d03217000d03000400820581e9121070b2040103181c6e02d681c4074000c4603440c04051100080100030f5049005c1045080e020140d0f40352a050710300000780d0035900343c4812a140d1003070f00074845c1c40001800761400ca100c98041240100141401046890382080042c500010300c6038220141640240d00c085980042c094100080014581004018000107000c80400006600316000b03031b084400400c20310304d864410484100803050031200c1c10340140c03211070040d00c1546c04085015000810104824860518584074a00c1c0d542440000c3c5009000d8079a440c4131b1b00c0500e900001c440001401341c3c0100d503085080009808c812241e01d69181c0240515000302140d0819210715039400701511503000c82c08440d4603002d803c3c0150140441069035501d40f0441d08600c0360760054090545d080038041001141e07441e45c22400844003003014560b201c00540c0704900b03621401003003410880c6c8480c400103103045a131998038480c02d41038a10f180c180c5c8801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 844067248 1250 844065998 844066009
    0xb0c210405101a0d030e040606030e0613120302030406180303052d04080306030307050703051e1b04110403051906050705030c180d02100215010b070201050f0c16091406 74
    0x1030740340c8110909195640700160078104c9001041a02074a0140809400900010140d400940c00380c800291038000501d04d002c4280410360304144004081c0d40c031203c072552600c0350381803492038144c145540400081d00703002003a0480c1c0302e0b90010940000d846003d904c0d0190007003c00b075406282d0480382040c111900d03640d00c0a00d1512505000c1180040e60312542c880c0c4596100605854160009000315000030b0750030001080518495009450f071202031400702d4030080b0020381d40d801594030003500142d607002da1030140c005604081c0c4001c10b4411410614080c2c0344500c1d0701c004c26074402d0010082c420002400d95240c0070f44540c1c420701c00d0b0384801c2c50071249400145c1307a00384140305c2003256104d17000900340014400e000140c400c00244400342c00140021508900c0e1001503080043c00e0388156030382c0300d12280034060a44e610b030308000d0660002031180c0120f00114030007070030025400c41c800700b080240300501c080300d80d4000581a201e01c0c4c07003405404101c0d9056007010100c408244145440e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 844068498 1250 844067248 844067261
    0x801091a030303130303060b03010e0610050412020d030201061d040c0e090304060c020d0f030e04050a0608030403080706110c031e030708040605040f05031602011706030a0b0c21040510 81
    0x500843c11500d5415610034000c0350054110145990b0340d00c001910001c1101440c024200d48004102d07902e403010030700029104080f04001007200400041c00343e48000b4200c401096016100c81314520402d16042c2e00401e810b40209240b0301d8030600c0d200505c038500c141c09101c5c51107031452440903651010b00f0720b84180182e9019000da0014030042c0075040c42030030580710441c00101600040843c81c2c8904440910309102070b80010341160226010382071a01a2070f03001448546c2c10071445150034080c640302c0c0a58080100380000000d10b60003440310582040810180b0380001e10368580081c0400d60b904d074403450702080240c014140070184000c0c95019a88920596151104959299650840144801002101c48040c080383d08400b2490820182c1f4a803c075509642c182d55000b4000544984040c000802850b5011003c00801d0303100411a000c3d100c0d0f1024207400c40f41c58144894041d80200c001e050f07482000c02c104131090b6058440c0d810300903401542952540e00200071100143d415 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 844069748 1250 844068498 844068551
    0x18182114040f050603070203070804060e090f0405100c12060e2406251203050117063907051006090c020c10090905150f011e030903050f0a080109 64
    0x10b07030642088075003010f00c02982d11041a105032850840140d540f8402c0360010303000000042e105000c0328070070b41041408241c0004015101081034a0281d40300748c3d4580e54003550103e050f071202d028507603507800b80d502c106171034560800900519440720007252010b80c044860440c80b108a103a1300c90040300000900030001000782542c2e282a128003404064002401d11004001280e401c110001c547c002d6600d0700389070300320383d0007180d0b030b5140031207481c1401401c20303286c043c0703030000303024415103000c0080c030814000f1003a00340480d00d9400d120340c030b8090600f06000959030003001407d14100000480d1060442c141004104941c9460f2480d00e02118540310488015910440100c6644d151220740d01001d4040e91801c0c00d852034444805034240d0f041036030f02000c0500950701c420204d28141004205684007803030001032081c1440c0c082c0a028903c500302d0807d0682e21404032040c9440360301100c550302500c0b20919501c56014100801c004001d103e0801940e1078a004406420040140d1846048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 844070998 1250 844069748 844069769
    0xf0d03080403140c1902041104061b050f0303011401020115050f12010f110c0c180c0a090302040c08270a06051012080717041818211404 60
    0x10350316601511107008440540d14251010b01550013034001c100400c80d403002c07074030341d01040c3c0d5400c510501c0203417141c01c284d41c40c440d07000744414000302e50301807039401148010100342e00c1d00c01900d00388542094004811031505020000000c43d41001020400301ea100f400c1e40204802014038ac0d140d407901d112401a07030350100289010001c0782c43c00011403071a40708000000109800c0250310403003241e9100c42800c3c82050003041c0055500c80a00200300110800d0382d01d421000c403140a103600401008006d42d000d50404145032080360302c540120800303554040c20801034400014005030641000719045a91594112080314059443c1d607802c60046071294024081001136031348803006030900401703108861660040004140628215503180d0602480b02680d03250014100f11401610380520031500d100200020000c035144803884481c200420b810008030042c0207003c040c0c2c2c401c40d041c00905100420003071004011180152540c0016564861030002541d04a0420841c00f0320b106040c0a030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 844072248 1250 844070998 844071001
    0x8191101020906040519170a0b010e28060b04120b0a0c08130501111902060705181e090f0106020f060f0412021f02040509060402160611040f140f0d0308 67
    0x1d05201e081440c0d084682d02c550010540c5031f0100703401c4030100400e08001c4d42d20460104052081c08072101b8003414031400035080720702c1c01c01280040c00703840345500810f0b80d40310602082016541d80c04000a030031441c10296403a555240e0b07103001c44020460a641d801581c8000c0b505000051040c520011450345808140c0e5441d2080110700310f0600900b50f41c035540381d403e024605032000000f4082684170010300c03844800441002442c214008050a040c007400b00510b840d07a00c002c02c4404000241180e441c1c401e10480008900d185684004030380e0400b21041c14014520381e1280010b060b9002075003101d0001442c07217007481c1c3d12807060751001a904d410801180101c2e40201c6005080c84440c01114604800021440c0c90088000000403000381e02040a201d9458040307000743c1c101404403800e5080403080b003001c6e0880b480711500241f003940c1e201d6103004660030b031400350750082044044c50615507603100703a40460030003ca5806807003050302c5903c106035450306440200c849074060f91801080d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 844073498 1250 844072248 844072259
    0x13020304170319060b0703020d0212120c040e0a0b0f100903022e0206010305011505010f030b010905031b13051e0a1e0c111b09060a030819110102090604 67
    0x15072001d05904003d6124402c1ca0141c0c031580d01825004010070284296900785900b402030a00d5204500c090441d0011504101400c0505098400381004080d40b01c5582e12088401512032045a120301201d403601030400c44454020782c00300b080c050080c1c030403220640700c0d0403c000100c241c206c2e24101059403004c081c07000d403d00c400d03140d2820100001130540b841d206581c40c00d485d17030000140300060b84407100501c200b007820301030240002c22000026041509100000e8003250030041c625042641c0c4100404507a032140c46008001d10000e815035068000d080011418a00184051806000f1941030a11880058480c0c00d10401c00882280801083c1c82c2d180c098414014084030300e0356465051038244401518440c65043c1098240000e0340c0701c044d00040c00a540030310395064290860105108805000c4603801948003088444a10550303550b40043c040704201c4e000a880340c50086601c5100384040c54400d580a0900e0322181145d8500c91491420303403041c45030007900000c09100c00c011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 844074748 1250 844073498 844073543
    0x30307020a063303120302090603073f0b0a030807030507150f02040e070815120f0109050d140901050a08190c0201020a0e01050c06040231090213020304 67
    0x118244183c00b415516034610740301d24a02c6001407140b0500040c1c1100030004c000110403100410405800c056041c10301c14800541c01d404018058070038448809000340310100f020807010300b12009402d20ba00000030600100001c030702c264498040580c0341c000840315038175112600ca0708982e4000b98251522000d40e0701203170640c100e21021910945c814420760b07000d00041c0141251100e14150040e02ca510307040c010303800d844010300f400040c41800070134010704040e403c41c00c0030050320a98100c4800301001e00c4041c038203011520807440c15460700c6007600030840c01040944021040780d4946820211204040b0b50302d200f00800540811001c2200410706030040c103450380d201c1001889001407540c030141c854180da104140003070050b58000703141c080030f54100001c01506442807a2140c1032540720358005550ba84060710282c4200e2010320900084004d0b00d42c04201c2420b0070003042d00e0402822030328005000c1d511b00407442070751045140e040050251094030320550b0445486c60205994645001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 844075998 1250 844074748 844074761
    0x21010b0304080a110d0c110103150b1812030a201507110a0f0606141e062503080c0a02061f09111b030c0601090f0b09090f0708030307020a06 62
    0x43c2400410031419031051014081354402c2110703a2201120324a951414450071240c850501e41070620744034805800009584001c0d00346da1114400c3c03a0796030103c400c0700d03400c2c02c1d0040d08268028240307200800c0c2482c0102c0030f0900850182c6034480342c3e03840d48620317480c070001d41c07074501085a110380300000803241d41840c45a0885214240751455242007030345e107400c04019803002c2e2a00c000c0c0611000802c80240f080200030540150b809010220080000711020000034800320080020300b402c078117640c1c4100440325000c030700003002503113400684884074881e081c801055000ca0601381c0000d10015076107040707454a0481e5800b41111703583d002c80d510203405031104110a208a90080411201c0107442845a00e556050420303450b4111490700e11788203031050342c803005141c00c00d0001c40b0100c03d00040c11415506d190300007181c043c450303007010030050410404141d40107020030240203880201068000c01010b100050315001915a40159074034401600c1c6200160701c2180c26401240c200d41c440b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 844077248 1250 844075998 844076017
    0xf12020a06140703030c1704051c03061d04050c04150f0803090d12140d060503061302030307021e150408011d060c09040f02030901150e0105031513050607030221010b030408 76
    0x59101f1320b030207070082d0560541250112460307400300c3c5201d00e4507810116150540c0303849260901540781480660046916055080003803410a031001c0750805c0414404a0111a40a08200902944440c0c9082c0e44030b402e11444023010300c102c3e00811001404000c994400b131000d005c002c0d2428084d560000c2280d40303440340901704030803400e066449505410050000980c941808140b2905000030141841405040b03a000ca43c1c1151070000181c0703021007070310426a011581e02014140d400c0806039030f148000343c0780c2d03400700d43c0c803800e4115003d8500281059a44020003000710141040041c11800d82500d400282c82d40710300002201540c00304000e14903000041c0010920001e022070040c1070360401d9490310066512101c2401c41c0c02d5820b00340c01e00514203188802229454940429107a0481a2902d02c42200d10340c0002c0d019030000c07400075080b0b540034003296521701e08064010001c2d081400100c0310300c0070b400540441c2021000149040c1c4030501d024600d0364843d60369900084d489104e44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 844078498 1250 844077248 844077257
    0xe0c0705010e0d0e010215070e010c0f0c031203020711040221040c0e0c1c0c03180c0f1e05120c100c05240613060f12020a06140703030c 60
    0x5080094420302a03408540c45080003481407400705140940521454055a0b04650044101d03240130a0746901d01c54020800d410080750903010140100c2c0d501c240c0c2c00020303040c6200d082c0020100014400c10402b140c0c0182142e0030100045c1208030283c4c890703030b940501014600c1c103c400c05480c0950045c0100d000401e003481c960080581e10001d401000c503402e54044448101c20040018100b1038140c1c00700c0c070742c1c090a15120441060701b0f04024400c14a21075113a41c1c0042c0d4120600a50103147c124006032030355103180ea0540b510041d40c51071070041c8951149298400078205210404503010f60161000e5000403500385070602805004100c1c0b02582c038403c503201054151180d16840c50301072100c1c2d489080744045400d03d54503040c1070b0700265407003414601c500b01ca110154141150407500844500c221100724149601c05002d5035003040300e510004120024210036402c070318a00300780c820750b011700c4071542c2c0d048281d0380c9008445042c1d6000d6010042000083e10136800304101d910103052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 844079748 1250 844078498 844078507
    0x111030601360e0901050a090c090c090308030c0a020f03090321131203020c09060f060a121109041d03041e080d1709010b0a30060603200603010e0c 65
    0xc800d901d0403042e407160303c1d00f03001c02e010300a801c00c083c01000d80c00130550200344131205656840050700403040c07054050880d1303510740002020b0710500034800115005041d16440c0c0c1409032100340240d000c42c02c4440944a040440e00a003c5c02009480050f40000d0142844840e404885c0c01c80e503007107404211074490100042820540e00443d018094901404440002c01706460b000e4a0301d0b00e1201c404d4810084e1108210850340d8003140040d08020648003241c60f03212404c0140c550010620040c1c030b1341c608261104517054401d90261038210350403901404070304400d0b14500171211201c030402c4c4c92600108000d200c004070184985a42204901c601c04480796180951403c0c19030541c8047d0000d44509103400d01504032100c13858116038440c000b040310020b0f600010350f20041310300c60f0030b00ca018808600d54a040c0c002064840c181407158100002c03002e240b619000601090004842d03082c9421500d1304003c0101000e008002d402800072444c59007091040a100c840047c0302e03201a040410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 844080998 1250 844079748 844079837
    0xd0305041a09151c050405030405010e0f10020606010e0109150e150f0a08150f01080a060314030a11192d06090506070c050a06020c0a140607020111030601 68
    0x904002c4014111448031384484400d15003090540000040302100c2d0306100a02020800200c100c4080b1442420705026003402c40010441451a9004407079215801c462a070381d149801052892140c003090f82d841488040e52801512045050701604442c26501d1400d604518040d0b28440180c9100500030b0b820380d04034042c40c8030560b0088480001000020800302103030341d040030416420908000b07860070040c030300c9004140c0821010030403a0401141d2008a40d4a00099001401651300291041804070503903d1082c1daaa104046680000d80c050100703504616012a0b00c04d43e140c1c0c3c541c50135040c2d0200d500c90401000c00494808154001b80f00300308280d04812510780801803203000c0104182d80241491800c160000b4180d00900c0100c041010010784049103111089a02007401a19a604218100d00d8681803030001404a29031600300320381100000b4500b84100c8a5034000d00ca41c41c0f4641ca08940c501003528820b002c6400e4070312115201e040804541c0c01c50585000e10300704040c864 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 844082248 1250 844080998 844081009
    0x70803061e0904140601090612020108040809030d0c050d051204290106020a061d070b070501090203070b270a030f06110a050a080115210906020307080a0b0d0305041a09 74
    0x2a20b0071190303520403144d4030210803414040302c1d00400310844100a141c0c43c00c03a45410031000c1c0314009041000f00c03000942081030000903075114074409801c880a03081e030904094044100c1d070205850f640b02c2c44110303244c090701c84e03000c4541030701c504541e010301500c0e160754005594440380b69880010607500c040138401860140c189008006540c01000c046105050100843e2442c3c2600c0c0c8000412130082015044009521030490f00c011520b150b0301c0d80e280c2400342c0148039508000750700d8040d9810004075452b1750400340c05000404410840c654007044841c540050342ca1011942200650008002190f5a80640c421031030080c400440c40300700710014120241c1c4801c908ca00030460104040301c1c01d541c00800140917140c004d14000100b00a480068140b04051520700103c2d2850b20008903000041c0d00f100c440240d000310103640368141010081c0441000301c6030610013600d0b050b403251552034161400411147c050f1512072515042040e40b60140fa0000d41404100c1400c00c4895205c1d1070380b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 844083498 1250 844082248 844082251
    0xc13020d05250207080303150f04020d151508010909080d05040503030115080f06060a1206291801180b04120309060c050d0f090504050f040501050903070803061e09 72
    0x2207181e60b52101d0460448a020100300b00350403c65001540900104800200702c80d00f21512071511181011200002551a20760082c0721750850700203e021820a41c40f90400f0036000b001d42041030395562907a030381107202480f8021f81000641800010081c12800354455030f0040e0280c00d1040c68201c040128000303480301030358100d4169000100421420002c8041e002c0b810b003c03481c245c4250300f4040400340a92201624180c811000020f0b14a8014000c468004240d510a081070003c1643d541d142100c00c4409031005d041c907940ca03508004244541030490304165215103050403424001c80044805518602c0312850300041d210000c90710841305c402501c01041d003a030018804c0c40e80d234038009211481325803011007400f001040c0321000030300118504200d082940344c0007030095040c0d981290301e0807041e0300c4580c019261000f802050503294541522950164000b4451525080c0e81079540b4800c1c4140a881900144003080f854944414440322800c0d0004980041e4240d074000100c12580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 844084748 1250 844083498 844083511
    0x9061e0303031d031204030212041a0a020102071202160b07030c141e0606040e010b01020601060c1a040f0b07090f090b1f0c03080907030b0406021e0c28050c13020d05 73
    0x117500030030042590420511740c2a01c0c280c1210b42c04e09140030754280420003039805e8245030300380105400d0801031003541030b20034542e0000c1403031648400311540030303458413503407540c0c204040b42884004c5086d141240c1290071807603040c1e840c1c20305841d440d22560000070640301d803140c65010b80003810b000c0b10144080c0ca15801d9011000c1c2036142403a00801080b5480d03201d145071142d0400c1e07405002a178010864604540180c07c190540911078501445160030a00921400900100500050007503040300c00302d4040c858280e10169464145094840d2922485540307900c602c0041e00340b241e16650b81050000c0b00025010584080b0104541c410740928555044002105803075010b0038103600241c40ca801401d110302600d449821a201d00040d5400104044c21b06a00022000c19007180801d214100000d0000c03407a840e00c04095003d503c502c01039100c1c40484645d401003483c0c8003503c070b4030750b080c0e1030b44080107001c1b014940c000d000b40d5400002c441c1c1003060342803000038695181030240d1403203440c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 844085998 1250 844084748 844084777
    0xa1e05010f090b0405010e01030b04140607050403021306050303090d06291905131d0d020607020f0f0a11010210050109060f0608240a0b1309061e0303031d03 69
    0x103041c50071560840d0344603d4514415401c050041090580c1c0c07068a42c1034070341000580350f65550318200120300010308207031103200b0703c07807001084440381e4060090020b90340700311080380d41212245e410a096401e01e01440d985600700700300f00c0407689800ca0308041603604c60f6002103503905201000d01820740a40c41c000f59010803108849506141c208443c4130501c12142910300524204408a440b4800c205010b00d4116035400807861000901184801c56a041e03908a402d0164042030003516464251050b4015219903944658031000201d4180c225009036402090040c9490311a281d4402200401605600070850a5203002a0714040d160180c502204040b0b400f528160b00026490031a500600c00c102c100000e0015440748911801e0302260341042001c0000c0c4460002406400340340d00071800142c1c0021040c1350040a452864100c07800724100300070b61941c901d0ba010703110704841450018640024418400030b0b00036440700c40351411100e14050340341640d10710030745140c1c84801d401d075444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 844087248 1250 844085998 844086029
    0x121209070b0708090103091406150a15020c131103090d12020304030e0d02040b06220515030a0c05071211010b012a0206070602040e15030d080a1e0501 66
    0x24181000214024003600c00ca8030701d8080c150310740390001e000701c0c141c1c0c40c10984c50300041d40c18050368108420105200b0350a4440c00e007040c00d03c030001c00114000450041c4440d410008080031003070a804d0845000c4d802600303001c1200000c11261030000110103050340e503100e80b645c0f50315040b0000345201e040444d0040c200803440c030f01c4c050300c00503601c0c2002901d00d00401c00c01000a81c03100060b1950041035502001b900960720014020700210602c2c25045080803489182c0010b042c6046018801d0b41e403201c00380c0c16100c406100010284100c0d00d0006a0f040000c50400f060030b6100002844241c0303402d500700711060740c0b20003034026141d100c140003030183c100c601c100072028800d420241800742070420884044d00c0300d03500e405085002d24421400b014040b01c3c1592180411590042e40c020f204640d510385031040c020b11840140c4108400d2682002c1007151400c001502a80048003926510300075503640c260400a0402a801c60341d40000403208071918442c603009507806080e2003042c54825 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 844088498 1250 844087248 844087261
    0x1404050703031404050d1101030b0303030703020403480b16150c0f0f0512040f030224220c03060507030e07030b06011404121208090625021212 63
    0x55148204100003003c02000308015030364401404c1a061750380a00135120403944c3c040181c3c005c00c81c00c0c00842e0140400020005d41f59803503402030050f2882010703000509982c0005d804040328490640701c100d60880100030f00380300200d50480b0f20303024041400502c51916803031608030710f801031000444502010100c6104100001d000307070845200e4120100882220081c00070f0200c2c0d20261903809202a40300b0300d01c5501d10039000c0710031010288020a215082510b402c00b00350070500c500340d00600665a04040d85150761641ca010480c18902c080b50781e448072505000719140c8c103241010101504600d0000084141c04030a00035400360700c001420340750a08010781520003c030640e1105402c003420038400035890900b8036070030143c28642140c5080355086504580c0c840c5c0d8004824003801680444100003402200180604140e0f45008258541584903139940c0020785546183d0f0750342c5c020081103030007034000d0707010055581e01c111015141081d5003060315622107088091150202000c0001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 844089748 1250 844088498 844088507
    0x409050f010e0601020c040c0513120303050105030a0b011806090c0f0e0312030f0a02040b0d020405100908030307110c0d0b090c030307080a14040b0a0c023109020301140405070303 79
    0x100002c00201c006440c00000007900d42c2c1544a0140c416980c4a02c80c42c900c40c801d005031008244401d501d4081c0c1501d4803241c00d050051001c08a0006c1d007440008a142e040118107540d14a034481c40344400d50b4209101800c1183e15100c00c8204150b13075010000b003d078658019171243d00000d40300d0010003040321f44020500325625000d207010350300c030743c9103c50603c2d0307c441160391151500d082590302d034071030103090381c040d00c01e50707200d00442030022404a640344001d50003042194001c0707451010741e10f84850140e508488900c00c8540365042440041d844074003c0400c5000c012444080c1d52010f27001c44c1c0060040c441c9900c0948018628408000b2605010000c0072501582100114104601075a0b500c98902c00c84980d001000200740d4640c000709111005c0e42c010340f02101d507c030703210780035000014070400702d41780243d114000141d101951621264401720804900d4a401d0040c07084114404d40549080081281c1641da264040900c046600400c2c41c01a80f148002d880c21070b01d942002030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 844090998 1250 844089748 844089751
    0x918011409060f01020a02040203040c0308040b0301150c11010507030c0209010b040501032a0f020a0f080a27120201120212090d051206090903130602160611030306040b150409050f 79
    0x140103140c008400083c50380c00207095181c1550403980569a030790381d807070140f81d1810203900003014010b01142c08507030908201c01a506841c03404d036540d07a000800c01001c580c40f41a440740684103007841030140030203520520040190b1070203810000104403250f404104021003d03030004c003503201c0104080c0115a814010b96803caa50032401c240f40340740c5800204207070072081e400c003401d1128160a09050754000d019103104181c100c2507090041200741401121544410f20400001d203186070b211103445010107958403103d43c2241c074158451304200e0314240c3c00300c0709102030741884403000700c4400c004500e00040ca89034400a90541d86804c121110324907001c5034102c08814403d00f4010b07150b0814850071711690103a0304135144051394903415200740c10340c850010075a2422070b41240100d800b5800240120b401c44000c89808841c550b02c4c401158126982c05001445400401c0828454901904040207194000344024119202c01080150550003940400e026076141c0c010080c2d459a04030343c0c01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 844092248 1250 844090998 844091011
    0x13021c06051809120f04140904030f0807050f070f1a0c0304060c050d0e071a0c070e31021e03101a0406081e0c0d06020918011409 57
    0x180202070034a000960900140c007144050400064005280e4400411001d081c9121070000c0c26944c180310f01011803e40d1050042d0804980d9440301e10310b03035040004441340309035007582e10080b01c030b0009c0328220342c4038901400c01010404240840341c04101048010300900344a90781217080b021041c40c0401d185800402c4908400341c000c01000006510b00c411254890703403142000071800c42d610b90a4805c0d0090260a2555501e003c1c0c1440c0d00000c0094181c040d500395611043c002180790403005c440d80310f0141e0240441e0803200c400c000034401e45450640012203c41035500c018120881c481c0c008240301b00c2d084510800030b100c8006c0d814851900d000c1e425a2110b0000d03101c5240e0040780d40e81d10036442800041e076031035a680e15104407954503400403801c028410700410347d4400c0166591500105100c0c5103081c60b4103840700340d101c0090a0504210042e00c40c1c40e01490f541c03280b400a4014208003a00709000030440400c0420812549000c0e0103040146002c900d1004244021300c5d4005050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 844093498 1250 844092248 844092251
    0x5060603010b0a050d0623040b03010506030c0d021f02100e010c0903020108060a0504051503010b030a050a080a02070905131a0c03270304170d0c0206070b07050913021c 74
    0x6000e642c1d80300c41280c14110880c2030441d03588001c16034150080c0384c0340c0d00c540000c411609040e843d002c411010000545422101800f014036510201400c82d081540e0056151b440607a003504541409001101118002420110240d030b00001b4141c0d40c600c101403500044c2c11040908040f10300500c68481c5212612008100c000c2c0c06590192000b24a800042d0504c4400030000300e0998400e038281000d401c01820900c89418003c10013041c0d0b004840c1000c1c030950030701003a8000c40c100001d41c0441d0940040081017000c2d91525903089551080d9000030841c01502008078482c041c07400381500072012001004c0700c1c412603040040d5400c00e000901c02d000080181070240300c003010300c140c0b07030800305c1e0312424540c1b00700300e10b44c00e0039071140340344903400c070307000100d030009450760401c400312003804c1d08a056a8404560280850341c1450f03c4900079400348087c000e0340c0109560185640d8061180e003400c0e498118031a001a810008251200c1781964000a2804101c203d00b081a6202c81c0309100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 844094748 1250 844093498 844093501
    0x5061e0103110d1406060f18060402030c430c05060a0201090203010f0624020d120f180312020414041a090709050a1502030a0c06110a02030d05060603 66
    0x144404414010301c0042c2c4072207a0704003656401d68900b4803a18400c0d84c0b00d0301950f081455054015201c40e000c9030018801c4400c00c103a480d40d401c001411503070040700c40701c0c00f0030a0703550002003200a400141c040d80c420b00090145851034001110005800c5081c80f4a580b0341a0004c00c646e0304d080d5416607800120000a0754040024441d043c0c41d2041c2c580072181251101c6080008a00504070b02c24065855800c05118130300030395095010708240d0b117407440b02c0148038820389406440d900319500d4110043c1c2c004400021002d100c7c08214108020501001c02c0c460007030a05d080640d50344600361051001c041c00003900f01a001b20803e03040c040d05c440198113042ca40061004030101c1c1c681e845000d103407030702084460707008060981c050400c4020690602c6023801000140007002c1c0c0d00a0340e024002802020070b0082e05488150340070281640154030f0105c583c8411540840c4c80c000456004c0d80300c0072240381d030900c00780c090705004180e90300440c0c4510b91210110281c80c000303002e85004030b00800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 844095998 1250 844094748 844094791
    0x13050f0105060c1e2a100509060708030402060f12070f08060d03110321011a040308030a090f050f0a0b010909050c0d1104060303031e1a0d060f020c0601030506 70
    0xa02c088201c0d084000c0001494501c13440070309106074002540003400c501069070500300d07020031000c86a51825a10f4600300a030b02c2d901900e25210780018a940b11009014030f1000602c10350003036138841d2010342014240118600c14120750340100025045c4190310b801000102a489141020103104503e40a455801c06801107990f20031a048064100720101ea095040640100100c500703074400140b5000d180606821420540d0400303026103e03992207800a00c640310b9884400340c40c00c0e0b80e0407100701c91840d121002c40d40004e18106a003103600484403240310b0041071040c04032121f42c1c041075001c0c0c0b90003800d07860000c040400580280c802035144c61102d40100d9000228100490403d0b2220740d40c002e5142007100c000303c002c1d40710300d9020f805d005000c0708269058015250049d40c480609000c00e03d0b46510a05494031851194040f000d50041101c45103880a20440c2141c0280c000140c001e80030300e15501664009e451091090780701400400070020200a044c0c0d00010080006152011a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 844097248 1250 844095998 844096003
    0x20d0314070f0507020604080d120c2a0506010b0d0b0d1101030c090f1d09010e2e02031015081302060a1b1b05010e1c1113050f0105060c 60
    0x1510000412440b1a41c90390900d000d80225540320790000c020307580740c55403111055658100c0720b002400050081d00c1c00c0ba02c5240501542c4588c441d2510f1f0355283c0548048181801e000d000e0817009000710070001900403d80901c03072140603186501c07030030b6990703008074000c02d0594400d44c10050081290a4060b8041081007860034082002442e0100d001c4054400840740c40b080c0c3d4201201d4041c40c82030015046500c58032040c028074030382258599940d58022024201c1c0c4280d80780f042144c04c10452a80c000c0e5070004110303c80019903240001d09042c440701081242c10458502654005000050000100c459001030300c1c50307203610303000003145070041000d40184030001d0000d004000225a100f041d41c0680c0e520703203892000041d10302500780c3c41d0408009041c59032106002580100c0404203565204081407405100d01610500204200c00810710003100829000c2e20156070013920f9140640c2d8140c2c20b0040f00402c0c0d6004a29418104400083c020040e401a44100405c2041c400150343c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 844098498 1250 844097248 844097251
    0x4291b04030c14040915020901020d0504030209041106130e150f2107030b071e0f091710020406050a03051e0c0c0a02060a0f031401050a03080d15090b01020d0314 71
    0x100c1d10040301c0c02145030100c4c019140108004000c9070941324901d08170300466000d858121826422a01a400d40b41070542d407511441c00041c2d081007587d40007a001c039000c812a108200009004a0f160518640c3c00c104042c000d074100750f00d580e440e0400e10030b42c007036882e0300030f00c5d640c801301c8844114041000014444c0d15030542d0148101080c403083d00070b407500600800c00116003121b00c03c0480e01c5c1407000108461450981c2100c0b8525030b0101d228442d2182450b0004c91480d9101c0440c901e0805485060840382008d12508034801c0f004400446011400680000c00c0a52101030301c5000d400009415101c0040c00ea0080704c2c244400090340c4020180042d802c100c00b890125903c20290600500b01181c1c414040d40000c0d00044501219601c04600e07415803042c0e9504202d0156200e2140e1031411003813107640d500814181e424008280f042c0000c02003004024000110400d0401c01c04074060035560104c6181035a44160208550301408000c420800c1c2c0d2504102e4000c9002061250b40320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 844099748 1250 844098498 844098509
    0xb0a050c12040609150c030e06070207060311040f0e01051302091c0201021c05130b04030f2d0f060e0102090a1406040306090b100e091504291b04030c 66
    0x1080c1002c1001c3c407032280e00c60080315070811100d10001449883e1395018026940c0f108000134a4801164248030700071038018010440c3d5800ba0502c0e41c1342000c12400303408405440c0c0c114150030400090681016507902c00104000c0c1203071030041d80351004000c40900c41c9500b1132041401049480526070324441c907100004140400203029011a0004034505008541c0b03e1a64042d0603c0c00d00550360807502030005090302245510040e0b0322040c00f0b0086001758400101110045d1107403000040717070502600640160000010701c00e11015603a808115008181500c00140c111140e509018403400f65050300101880251300d0090154007040c0704403054424088800c0c0d603824105070f07a1361400f089070000d5801000600c0401068103100340304000c19140d06880b020340070000030f00710303165074000c0740300d00c5040000c0c05440c40801d41c200320600004204945400844130b400d41e05444840d5188400e9041103c60329051801d5100c1d07022088a104600381c5c1c41605000400026481807186805d680 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 844100998 1250 844099748 844099777
    0x10e0a12031b032703061d100b0f06030a181a070c02030a021e12010f0c02060c040b09010212030c3106030b030f0a0f110d02060403030806010c050f0a0b0a050c 70
    0x980d100009403240000e6003004200385e051616411504003003901070f41721f2210071003d07a419500c201940d102244e090809070303504040984414046464401e014550001203070402280343c1d802c0e8148420000e180c08021241011558202c50402c4950058590b10900c2418514400c80341500000d554415988000340706001c01c03000c109403442c00c00d504184100c0c003d80201004480c00302c010b07011b81f08458185003060b26000408511a01c0003450500a00e0740310b000d54030709410500c495155500c40c60456056204000101c1c0214200c200154400e41101012a40360303508035403908012640e442c000c40c035000d0851800700c044000410b8103c111050745c20002480c60741c0b6070101e03007040c2651320007410f940035014000c07040c440343e0380b02007101e54810114007041c0b540100821036214480352020350840c1c42800180002401880003503000300381414019888011a910189444070a10b05001543c01c01315440703080220303200c65944c0240c0314502c03d11103460410300510307a60041c08c02545001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 844102248 1250 844100998 844101047
    0x60b04060b160f17071502030115141201030f060c17061c0506010602250f0e150a380d090305070c0807240c020f010e0a12031b03 57
    0x40300c03d074441c40d940000c03144601c1444040254464001c1c0d8402c1e240c10741980d60040b0411034500c01c1340d0607180c030030007021544000f001d011203c0c1040c802507208025403c00202c0c07400c5280c85011402180f05064041505046141c214103031958211030406225441c00b921140b804a865450750004013582d0000e020300c40e080c610b03d04484004000780c854010240042420b036030104000741c2c0007421713503500901845060140301c841c070307494461110f240a652100f448041c00ea0100a034004684034400c000019040002940d0b0500704d80c0100c1c0d4046003091561300300c1d0101d0100184010700c203000c4219106414100289910502c00030307441541d501c0b10f02c0710425005a00381c0c0c40e680e03042010740e88030713544030718015070381700380a0141c0c0f49501c58540c0040d0041c1c1c0d842c409044116800d60b1a9401002c03a80d0034041c1c1c0c0c145203400d05051041050794a0030f1070b200c15110b03100074802552360103c0c00c20030b418007501045041d0700c20302d001140d00c681e0b1000310740c1003041c141121641c4120035009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 844103498 1250 844102248 844102253
    0x1030f0e0c01051e030a0906240b130816050108130c0513020c03030c0a023d0b030d080109060b070f0f0302010902040609090c050406060f030e100c020307060b04060b16 74
    0xd01c090024060004d0002100b802075005441e80f109020341d20808041092454a0348600c5e546a182100f20580034a201400e102c00c60801c40075204000c05204000e400303a0300c81d07061a003021000d00c40484103000300c110812003580d01c0201d80d40c2042c004004401e0140a40e100d40c4062943c0d40a4103028403054015070900301c055904450000401009480c2c60341002e50344400300740d1000850300700510030890031550b8500410301440c0314a00d8181d4070481c0e2100c072120032070300c054143d010754042584d521705000123890601a0101840c400d03519551650305108003030302101ca1607082140001010700840c8000b45845060b00c4149070408519640780c035903440e0490162a41c170390025005400c01c4000200e080f119007005040b0b0b44120041c2c40000e46920902c803c880f001e200d580c0000f000723410781c030404a000303070700003034054110b03038140c4095020095100041d070300c0c000003580069200043c0c40c0d0071322034144036a03c0d10201c1200c05103c40c80c40c0002542490140c1c41e5a10714080c03c03e560cc604 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 844104748 1250 844103498 844103527
    0x4080a0818060403030c060506060a0e040b040b03030a2c011704080706060b09030c010228030909090c1e080a0210031d1b0103060807140604031505010501030f0e0c0105 74
    0x11000002c05042e0380350b4a900d00140b510010000481e2940c2c1030a001c03d2082c40d2010688886500960361808500607200c01c11024001d00341d1041d41013a0785210764100d40e20b00340000d01700c100042c0c50310010080550754200000c21200740e40c014441241c0304002c0070740c1e030040d01d140020a060f01c07117000b82d45890529003034611890200038046445c04800248000c1014042c00ca03050b0110207030303144403109a00581c1c4804460300304602d00002c08000840343c803881c96400300e01c18041e18140703400d00d45803540f0b1000c031a9410000d40c3e1030042d4201c10000c00105181c00300e440340400b103186150070710700003c45a030748210090081c801c04555036180c400724803070f41c07210b2000305000030416070380f0500b2468961660710960095203005044400c21419500078010141114420001454424030707240c00b52201a42c1001e844d54444000c20001011070024206a488144103d0001417a0b524200014003211030303501141c000d0a082c8007000c4c0104802050128800400f0300704240d0383d409180c122103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 844105998 1250 844104748 844104787
    0x60d03030207051f091205030709051005070f08090f10090918120e09070908030702090601051b011a090c12070e0a03030305060a0506030405030f090a0e010e06040c030204080a08 78
    0x1070502c0540c04e9000c0400c0c0d2900000460b9010700c1c1c452a5034a0400400c4900703201c1120324101080144608004504100c0c8650307070806901d1900a051200036a00ca503c824a00700041c1c2e54010301081d001003610b07000c030395402080011100c9080354140b10310084c000d0a0144100d141e07403076844240418107044050101e02071684030000000e00344291001070400081d248075030340600358a5000a044501400b8240241c0300b0f40d030000d40c00e11030180d081001040d0010101d41c100401400b803443c040300b64101a0314802a59000403d803000c40c8125803003103a81d40c4c0d091a11441d002030601880307031480e5040710750384461004090f0007680c86980541d4078400c1400416041442c9201c000103140d403640c00b031402810125070500500b5514001c20006000c2030301c011380140c100700700b041850301450000b01a030405c007034040905555201110040241c00740c1c40f41c2c019000340d104100070740c601b034801c20300b035a012405c0850800d402c003100349035a0300508100a1102000103040610a10100b1012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 844107248 1250 844105998 844106023
    0x5040c0b0309101d0c042c1509010507050301090b0f060d0f2306090a0906090b15101b020406080106090209031501050f0603150a060518030105060d0303020705 70
    0x1d9803414031107951659034003ca007141150a14001030f90034601c0551007494904000180182800d143e0f54041200610300710282020340c2990745c02010001250760099180401041c0c00341005003902d00c210319070090b0042090f80b859140a0420906c19041029641510944e120021700b9a04101c0450040e00c110f182c0654001004038603100c0620045d0003d1010451203078050280210307003d284040020300340200c4a05041001c00103403d4106045100d522245c41030300400d00c81103c2c2c44800448203c41d400761206160340c003c100750103c0385610840c80c40d00c01d40c2d600e90035540c4418001d00040e02090048054001c00c02000295034682d00700b41d000d045040d000b000745035a43c40800000754020344a16003c5d0240e00342c0c0e134924412101c4018100d60015054080300d4004108010f00d80c1d000900c26a04c91030320070001c02182d15500180806801c10791140c0381e5465200c0100303031825003040c1e81c45100e84c0c1098200a015110b071307149400610b40c50309000d80c031040c0b2490714500304480351200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 844108498 1250 844107248 844107269
    0x90c161401020d0e030421020607080a020a0c080307030f170105060318100b010f0503011a251b080c0f040b030109140c0a0b090d15020906130f0906030308070305040c 73
    0x980d15204c0807000708115580906094036030b1660083c000416070b852240039600080c1408080c0109135541c0080001656620540d0804074040d5164941d403811500a0002d0b5030000c01d030081016041071403800c14984034108042c0c3e003160401c2c030407032400d414040d0f6401101f002c00170590043c50110b10030701001003c810380c2d68080c1c110440c03074010809a00c51600180c100c41e404070f4418001d0301140e043e10b40102d16604403101421809e00d1550164400c2401d50091100d951105048500300048030781c41000c00300000401011a0307802981c42c0d400905160704a0b04d0304000b0342d680e0b200e04e01e00d9010280d40100f0b15503180d4000a00521038190301914025666a180b0110440410031031400d540c102c60100ca91034035002119030781d026540080f50000d04c000700903070101e400b6909040250194000c050319202d2003c2c00311360f030b82d081420200c00c0c82d1000c0c00240080c81d44000b40c940078000101c41008001c3c9107031001042100043d0845007495502d41c0810140300b10450001c002e0800c2809 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 844109748 1250 844108498 844108511
    0x10b220903140c0a060b060306011b03020319030e0115080d0e0609090c0d05090616080a091b050a05040c050f0d020d06030b04140a031413091a090c161401020d 70
    0x6443d40c607031007003842c00c940b040e240489003000381c5000d0050313078040c00043e5102100d11360b100c503071800e250313056078016401e51200b4040f1110741704020346061454141540c0c0858070500000d50309081d40c14500c0440c4a400c5040000d003c485800941e00803200032524001e80001c0848010511601c1000c3c200307900b0641d004100b10320a030b4004001c014081c40c0d454100070542c0e0b0001b070552116401d84020758016201341800038602d200c0e9100940180242c600000c54000543d140d2001c041e00440e0192400036103a020816460500e0000000b05020740303040c024240c000000914612942c1e10070300c510039003c039682c80707890441e5050315005540450108212501e90401c286c40b40d4084070700301d074466024541120301c3d00011442440c001d42c075403034078201d40d0307680c021078499a0001160100e8203100d8420015144100c0d00523110311458860340c4014407401001807210708040140210b0350204c040008440c4460b182c07401480e902e4000c6800304002030200d492501a05c07401c440d010700c0034204031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 844110998 1250 844109748 844109767
    0x30f18090e0604260712031b091503020403050d03091a0c090901092a0302070506012402031603050708041e05120106081e12040303050408010b22090314 67
    0x40107400785000380718030140003000c0c2d200d804d811420300340700d0740c400c004c03e014042c0095488010490f9002e194100450400a044000e83e00b201200b44003400140151100700101e0b0030252400d804040c1500d81985800e00b182c6078203a0f40c0c100c07045004101a65502e00f1000d00118034105496440c02582900903400c00200d420b8864008007201441064075000005100c13000d4402d090a007800c116502c0d1850a4110082049402c4444400c0c2850b030200705150000c0d0003408142d001e0b020b5080c00e032503007803510100100f240c3c0740c0041d600c041d503108000f00c407184040481c0c58000c0760f61614100c1d641d01600c1c5400d40050049a020180c05140d0507032400012000e88003c1d0180d038030503944a100112000c42060076526244180f181581011000b040311031500400304030841c8400080321380d40210041c1c080410350140d8801c1e00001c00208052154020a01075448408421a140c100000800d6030110094a00305814200315986083d004100350080754514142c8480e85c5104d52100c3d03010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 844112248 1250 844110998 844111003
    0x506010801060f05040606020c0d0c090e150c12043c0204150501091404230a0b04060f06081510210603170c07120f02120703030f18090e 60
    0x74010094100764120011131307181428800d840403944164000e29400c46c980c000e2004e814110354042e140c0300801280407800c503001e8011603030107041040007840d0003490311203615903505000e048000502c030100612182240d00010780343d045608211160319003420240002003514409031b520100154065500490000302146425140e00a41d41800131112142d40d0140100f400c0c010140411a60b01c0c09110080903400029031502c0c007e00005500d002d031240c901007440c819400c21070b22841940070441c160f1954001d00c038401030240c03402d10070b460801700742000d01000d40c0608000c018003d00041c140040342042c10308170301000b81c160052051950301c000c004003040710f00d0083c00007468503003c1e82c0c0c145a100b0a0201c98100800e9550070f01e042144c24041e502c04070007164144240c000104001307003500780f4211424412031011944040ca4414441da0300000c20340780e0303030765000a035041010980110340c15002c040c551410804d510000070a075021a00d49412020720b641c6410003007220503d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 844113498 1250 844112248 844112261
    0x429210108060f10060e1504080d09081203060607151b0f05030906070c03020703050607050306040b0d03020d0503090106030b27030711011824230304110d0506010801 73
    0x1000180d03102c96485007224010000d00391483d080f600640d03082085402c0c45581000d8800c800101099162182010602642c3d00550001c1103a030304840b13800000560003500300401043c1c1900500949100d59280301d0190000070019801104001040c00400208612060001c1e45010041000c0c0d00f00c0e4103141e9891050490031404075005001c030030341450160702920b02c114540390050840e60f8501703030111182080820202c065100728030010001940920a19120344141c2c0c1d603c41e2685044000c0101b550030036690140564000008500880d50128007054400e1850905969070340b506003086005001e82c0d80040e0503001001d00b404104242c01c9039070400e40c00c4418403a50f0307041000c50790300d0f01c0b4840c451004151000c108000348540d40542c05503014090b1030030f0400541551075030034a0340c0000b400c0511508610715681d040c002a00402c034468424540b002005806600400d004241d20000e8409000c0080c039500280c00c59642c42c40a846940c3d02006484107960360f00c02a41c060080b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 844114748 1250 844113498 844113509
    0x60310090e0109020a0b0a0302040b032a04050906010c0507090f09060501080610060f0203130b071703061c0602070210180605090604090506030c0316050f0604292101 73
    0x244840408501014040c00c01201e800500c2a81001e1610440100c2c50707011f8841d1209042e0240800034030414058082c1d446280381a82c8112188001140380460b40840c1110800100084c0000c0c00184c9600002c84c0e40400f0a0030a8004958182070051500c1019440019094102a200022000190406c2821502c6088103000350303600d42c410303d42c403008100c0780c60902c030074100d4080100c035101e0303540c024540b6501c0c0184c0c1d151980c0049040b1103221150800071400d440026003034100002010b603940c907400c464440e9030460404070005401000c014000d0010395071140f0340c40043c000903a04035031100d5402001881c030281d980300081c00e19a80e10100c441044658000007078240d0141d401c42e030b0030540061505142a082c90003240091001038074546d0184505103a8a109403000c20001e5000e011103901c15441e903141504019419800c81081c90088034203000c00c2003d000000022003000f00d0f200e1070780310440812511581c45000d441c0c0c00e006c14082c0001040e0f0134031502114a8140ca1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 844115998 1250 844114748 844114751
    0xf0504091805061315060806040f150c0915090b0f1b010c09050a061d10020c03060a1a040908040b1c05190e0d02060703240e150102190f1106031009 65
    0xc3d172500d01d11007140d0441c4910102504401c0004000400305000564102d2060348450080f00031401e1030005c030340c6a000760001003801e00c5000d0116480010000c0a8103140c0d140c205803071410003001011310f00170305040c840146800f00d803400740f42c482213540c840c4407888000200710220a00c100185140c84078410720380110090000410071620442c484901213041e09054102c1d100540c080c0305002c4040a120421402007001e2000940c0c1c00f403028600400c11450042050140411040c24800280440c54800e030301d0010404006103c2d84150307170858030306800140e00c6040c521000d4003092500c48442040c98a408100091889544000e82c18104035043c200000707034003280020740da2260f0300e4400340542c0c420340c0040d500b0762080d00f0000c41242c0706c00078030303031860500040242c2565885e0044c410501c142401c001003441c3c250107109807007109100070140d0720800c0c0b40320ac00d05008040302805500c60f8000c8070013400304240c041490a54003800e2140c0d01e1400560340c2505039114000d51140a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 844117248 1250 844115998 844116023
    0x106210210020715080c120702060718030b0c180604120c090606051c1b080a1b1d030a020a0b0a0201050c04150503130209180d0f05040918050613 64
    0x4a100080d01c070705584402400c0103444c40362074010f8420800062801c0303614101007148480c0941d100e4080d03801890103800074005814105800741a08240c0c0e0903520b51400c000f9010004504c82c451826000765415a2403030355100504141200e0b000c0c4c00c031200d90070040000e4005207d084a4015809403806023010b0203616484151000665805102d02e90005402b0b00c42e8508201304001004071202d039100b40040ca020181d4550001c2a031007290f80000703e51504200082e080c0325004038035400260302110001030182e5003000d401d144106c000b0303104407500e00e225685180c404202c034800c901c1c0c000302005240e590b1401d400380281d000385c8404006500744001304000c603400a0545051fa0329603021000b60442c905012a240c1d0801460751071141c100c0084507000d600c07401e584074007900545143e841035030000c42d1540c5c030309940c04a2000c200306010b1600c0f20019030040907101603942c108000b0401144030150042145030354400074025000342d2050010501544140d1020f0328441d03401c10349203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 844118498 1250 844117248 844117279
    0x3011e0609021c0c0309021e040509030a0c0f03020f06010909050c01080c0405130b04090602120f040818031c360308070c1d0601140c070303080901062102 68
    0x1030740105920503d1001404080c10709810a81d0040240c4240c94540041c90351201d07000522a0580c8101d00002c40406c2c03007408901e42010b0180542c0702d98202c0003140391034000c40c401040782c00b040c00c02510082c03012004104161003401140d00d0090004229003d651b19080d12400600300c0200444880c8100702203075100354040c6d40407a2044100c0603845050078904014410b44640c0a051191032035a0f801108400e56034a100d2500c04500940300161148071001411040311405402d451544140004000003e08020112040c140c4808031421a0076490000f091500015550506101454601400c40203078040f040800f005405040c4113003030003004052200ea40740e10003492020a03940e940030710115070342c032004054852040c00210001560340e102c440100010240e000e000018580c1402200c0da48004c60311045090541c40ca880d000305951901d645406c14880241440040c000207007840c2001e6100400401013614139469a202042c400010f03500c108104a02c0342c1e01c4c0428403901e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 844119748 1250 844118498 844118501
    0xc091b0703022b0e04021c0608031201060924050c030304030305090d0c0206071101020a0c03060c14090603060d050c04091406090a1e0606180902150c070e0408040503011e0609 77
    0x1500403c507107500340c0139030000d0284170280d03001c0204d40064038802d12019071000100e10824000b051408090360b00c4100740d02030f05480c8041070b0311200410a0000c0c2c2803211013001c000800d0900f4034034220804400c0c0c503450590300307801a2a103c001d18000401000245500f60b001b1512070b4411a040c1d41503611906c0e01962024038000c40a500a9820300049000030f40d441c89018003420140100c40c0d9840750740d0341e465101c100b80e4000701d42c902d8071183d4450083e500711a03000660a002c00d9070034203100d815004034186000003001207200340203450010060150a002c01c9001400160043c4030085050038030030300d05089030a01081e01e201d450300040e00030b1800f241c081c404960082c0403c0c0c84100760554000b1680022000390355160b9034410005151114100c12402480d05560105003141da900420010041400e680003038032800304094840c0c02e601003151002d85161141c0100e140c0c0703440c01d0022160240307800003031f050361a01c029442a2414101150380c0120b038100244011900c4032011130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 844120998 1250 844119748 844119823
    0x150b010815061e04180f0203060f0618041803170402090708040512070b150f06220b07030e031608191a0c0423030c091b070302 56
    0x54010001c1d000181c2440c1000003040c072500000440c01100d0000d4900c20401e0b0f000303500400d14041c00c045402030115050140565403285100110700b503140081c0070444104980928510403240042c038903c0c00080c0c80000c865603107002e401000444481d1b050688403c0f22088141d020030034000703e03c4d40c041e4482141e603105680c042c0c900040703525440300641d40f60b20040c004481c00d024860b83c02c8074120410002d42041400380d941c4090358140069121400c0b20383c00d00480c00b800c29865034a030300751031304412180c1d03003c540321003a0303c0d280b00940b0f050f0303040a16800000064a00061a41c10f051744418070304078005044060b034030b84240e201c0422110441c2403081c003606820030420180342c00c420708040c4070028029400040c10703e00541c43c070b0307000c501c00711122020214003207000d00c116188002c2025410145a81480322900c04c2e50012781d4548030b5650f8a03210704400000600041400c0c00c00c409000e003406006500e4040c240b40c0a910750f100b0031400c1007495407007900b1401c4006c0a49030312 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 844122248 1250 844120998 844121011
    0x306060604050607030c0605090a0c080c011403060a030807050a060c05161121010501030c090908120a140702060f0f010e040318050307060504031a090607050a0219150b0108 76
    0x3074a02494141444266040410241c05000c83c2e900207a000c134455000da1442080d421014200700c0c48030b1718004218040c8ad400050041e8412051080c2a0f41c002080c0d4641080710750585403690394080004082c408181c10013404c03002c01040c40802c1240018204107014400c3c01d0500c004080c10508503584d00680103c0036842c4000a0500003103050000d00c05d00c1c0c102302070f014034100d181c20030907510100d80d52040214941c2d9030304010014070840a500c032001e00401d406c144150f450503140e0050714000d102000304544549000300d107617a81c055000c5142109001000f80301c5241c0b800c000703502c41c0001c4076030b00e4010720840c00241d00c4c41440140c280c141c400303801c440e43e4251603548080b582d00305804c045140c155203242d0f000c20556000c101303d03c018011076070380c2c40c3c0e100d045180406020640c03c08455903020000309100d03000c200454510351050a0746081d544411443c44128a088151080e40781c5035014000803a01b4030405034114100c6140300070701840b51b8003880300111204401100c16 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 844123498 1250 844122248 844122259
    0x50d2d02010903030503040f2f120d18030b04030216080c0d0821092a010e0d24020a020d0c080307110106030b0f0709080f060604090312060311030705030606 69
    0x10f0001900039000f550b0854000ea0b0b0801c202440384d074500034145801c0c00440ca4600400c1c00c2c2c072224400121191503800b600342c0794013584001d00000c59581748218003a013414012240341240d0048114049640110341100d0011040d0625060281d140c0151440020301008030703020215401100140f107040740030000c2c0640c0c160428580391301da180d0300102c401e030031400140d003600b0a06000000c00030f8001e00884004e8840d0315540f801d10042d500f2070403a20070500310b140c0304262042c0c1e00f1406200740c4280550b01580640c03d1803404850707800e6100500c01c60685203140126103050b2903400380c8900002a001c0702c180d0b0300350101c1502d1120015000401803031701080041c0c2c4651080c0424202161040c0020861030303100e94440d00004011a6620341010314601080b004580c0a038841008101c190007030101404030107030454032620010050f0340500d4465010108152003a440d407a10300d1401c240400c141906c070314000b40d1003010a62014400e110329400800d152802249450003200000c01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 844124748 1250 844123498 844123517
    0x7061d06070f0215250e0f091905190c09062c04020a12110304020406150c0204020703110f07060914011d0102070f0e0a0f050405031b07050d2d0201 65
    0x44040c0110008240b000745e803c524282d500c0203500c0b02c07403a02032201c0b591600c00345200300c1c0c2c0c10b020340d041552050f030348166403a01c28000c07881400806600c584d0001d020202c2c0307940d600c1000721040c001c6c982e01190020b1030802140480c079131114000f400c2d81d403199039000d400f4480b030410058901d4034030302c1d1800e0010405005481d9184c15030003400b042a140c1481c00d40005040e13004411256810408802040004100021854180302d050050300ea40c0701c0340b101c0848000001042c00314812002070040341e0000399002414040c075000d000c021095401c440701c040309103400a454012500c01c82d400300d401217602042c0704100300359440186e44180e442130071100c10008410b0490052002c26810760040c07000c0880d004480c10841405404a000b64000c40e003001102001103400c00300d4134002c198584000e0000148010007125038910f803000c0c5490004491800050800c0815800160b214503a09690070420111520506034108400004010210240041d1b02000306200009000810b000c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 844125998 1250 844124748 844124773
    0x123070203180a08011d0d0903120f030b040e1e0c15030c0c0319170c030c0d0e030d090b0a0504020325051c020405062d03010207061d06070f02 63
    0x407050380815200814a400c0103a4529040c0d003100d200c140400c245401401b07880700d91880c10003003070068002034074141400519544448255510008100c1d003008200003603000b0442c4070f80c100d4194150002c101304004102c1e01000c43e03980500716110211703505801c03803544180e000070401d0005450702408805142c0e030204402400c0303501c018040804c50700103001c41e03600804100003418407222001072450300c0309c1c04080040d01c202c00d9144a015035400ca20104000e040c0d168041c0da0700031440c41d500703a031078010b13030a0300401402220b180050540300c0032400d8614070155800c00d40c0014002d40804041e0745640c1c00700f4040d24812103019400d13500000101130780c581c0041510503040343e825001141561078900103001415100c2010b51804400a020760a42c5043d00c00c03150400b0040b28500e100c0c00c1d503034840c404140d50b40c441004200c06070301082203c58400b901141c5445030300c4001003080041c101c13003c054401039a20141c90522407000028a058080d40c1c28810b075000c5500180311180001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 844127248 1250 844125998 844126027
    0xd0309080c010c0e120a05070515120a0203011a090a03120c051c0807080609040201030c020c0d061a0105040b0f130510031e202a0123070203 62
    0x900450312450200004949020284035922805102d561480c203074080400812070410903610080038150400103101000550002d145001c490082d260204102480001000e031401080b000c401c0007880002040280c0145900941c1640c9500044d07400c0700203c5250440d050141ca010301d80c014020800600200b99070483d083c80050b1140340942d11840c0d59940e1509140e60340d8103034a04201181254138205400440307140e4031a6191400b442e07503151100000f41c00c94006130020341455510b0340d041070494401d0100911002001e003581442d6141e601e403150040a03150509421641012081031007503106000301c2e000c80b0400b0780e000b41030002c84940c1d40907c2c1c1c480e11528441200000c00040c894481d80c0c611000000300d9180054004c164907000c0d5032841c0f02290308040c242c40e0440186c44400c0d44080001070100414180703480d0052002019500050710600c9e0206580c0d840d00c1d01c018660541201140c000400100030b0843e400321000045000b0640c0d842c00541c006010412001941303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 844128498 1250 844127248 844127261
    0xf0f0a020d06090c08070b21070813050f070e1006030c0903080c1908070302061506040303110f1603030306050a060819110f1b031603080901020c01060f0306050a06080d03 75
    0x83c01d00030f40380e9135a91071710a180c65078651201d803582c140800c03040300c0d58a80c00003094850050441b0042c80b45403401d00240b0552004040402c1410790541c1e40d1300303008040000315042c100c1c00f0120750800d07803900c1c0c54450114045503510410380c00a00d020449078800d00072411310b41070644403140b4031800c41e07444100a400c9003105800922883c004ca4459003400b0b141d0688050241c44070684e94140c50038001d040c008010825149212240080892030321407c04075021690503180c900d041640b208225414240d5041810b9020b00c1034802c05030807920030540040449200391070411a199880042c01000c51003481824007007480c01c00010440c015203512030080040786840014054004004242c0c141c100032070102409101080c14211070312006040022020b080c00203505100c02450418021444180002c04104507a030100c0c41c00354094041e1a9005529002400307547d80700c035540140c5c0400c0d48415500c107420800843d03800c41d503610500094078081805844c06028004043e8060680c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 844129748 1250 844128498 844128503
    0xb090d051515040b03010915270308010f091416030209040c11070501080402060910020a0b0f1509091c050d110d200415050405090403020f0f0a020d0609 67
    0x12040003000a41d51140070701e1150585806110007564440103010441e88544a143d00a03850300b0b9240d0b02056020f122410b01c2007107840d0120341c7d40074140c003901100d901000205020240c00c1000000c01d03130090582c606940c142030070001100da948070380c902a03800048841000e404030f9070110701c0300604040003030b50b128200c0c1405450401ca40000c01c00710360f54003004c18005040603c4a0001082c207000d034400801c000d181004450401c1d40000d1074a109a80c200c910400c0440b0031000b18500074000d003003160b81c019903050480d1030a0204040c081c0000c90703031076a07c280c2741d480c107880710320f0f1110046d801004810300500341030b541004101044070138100e447c001e21500b48a018400b031498080c00c0c3e204140d1147c561b8640043c0803116054600c9512203113100e039640100c401c0c3d00c4070383c4001d850840b10b6030300380040503480f501c034159918440c51304000d800203030303102c2003109050300007035021800140c40701220b030321310000d540c580c1d144e50100200a40c0020142c0f91400814041c4d04520301450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 844130998 1250 844129748 844129753
    0x2403020c1504020a060c031b020d0209070c020117041505040503250c060302091513240806010f0f05030606090303040806150f0a09091106040f080709060b090d05 71
    0x38100104078904403000c41290321070318000c0708000443c00c00b450300500409a6003059404003032941d8014001d8005c808803503c000c00007143c03001c255591403240c42010780d00a0aa0710381800c2c41c03840104515039a080603030102d82c90308103441e12120039040d00791040d80c100e60402d0140a90300001005400064420f4400f0f10090060319507400142c040799614074400c0381003926014052510f900c400d52198080020f05205100980340c2d5168088a038043d01c10001700c103a624200c0219501d020704441d0410060303d000400c41c00c0d03030202c2e2040d40400002c019107400805641c0c6070b004540600c5141c1440002a0300c40c41c042c200680034502a41d00000d0040035541003030b14100101c0d16582155010703050562164007488080d4040001045040c0d00544222104507041d002190400042d40f04403000d15131359880010503c481001c41c058403200003480180e5880c0d840211007004030b81800b5031161341c0500000040c4500c243c1c8100f4007114200454a410320280c5401c1000282c2c09035000d60b681d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 844132248 1250 844130998 844131007
    0x806030a02041104090e03031003020d1a0a020408100c0516031103030f01030b0a110702280b250f02040e030d02040b0d0b03030a0c06180b0405030a0806030304240302 73
    0x60351a0300410f0800d201d180c40740c40c0c955107089400000d0b140301d01030410f200d070800c01c244011481d400a2080642e50150703806d1000a0343c0d07203005013181c0882d43d400740e12207612074240b000300240c03600200110381414003191902150b500200302100c80300c1000801182c010088401c041d888403820a00003402818031402001514182500315401202d07000d601482080052081049504109801500942d0304011004400403512a87c2c0300e003c1000e80708034485070145038040841001c0316240b0070040401d1040541e104026812600408094000502c40558540e10114501401a100ca400c4890048108182e80a01005003202c84200080d8042000b0407042140c46000400062401034100c65480100301e040100b200c0c1c0000d6228480d400801500070f00ca0352082e00d4040d8290031031000902e8804285e4203013030440c0303811402044510031100b080103010002c000b038031552480c0e8a500046968500070141c0302d100b0b9018440c10a90001c113558004138028190801c400814180141361 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 844133498 1250 844132248 844132253
    0x6091b040b070809030631060b100c060b030d21060b03180d0903120807030605030f0c0405060103050108120f120a0516030e1f0906060f090605030601030209070806030a 74
    0x10b03a00200003502c3d0310500191124650804205a0b98440003417500410440c00d4220072003015004400c0d100035030a0170300603010a22107181e025a010180c0100704040040040c0d801a22140c00f00d0025594249800005801820049100785160380c0981c0c2d40810900703507c00e0030411804002c0505086a603503003020607101c26100c01580250031501040900103141081d440c0341c0480b00c814002040f20031801080002c018030310701d10480010f41050420b030798800038110010301ca198016585441000b101200603c00403610301c1c40c6020644080c080741e5184001074007610028481c000443d40071107021341081010001a060321004408820702e40203c01c5241c040350402501d1700e8104d00d035100c0a00c40c46003c0000442c4601071142030174480d08951840054440c414029110310503000d401680112040300d074004100d203503020408004058480118000700308031400792400176840c012000c51a4500010042c1c126980201b20349242c0d960442c0031100796070047d05d0250584148042d00e0700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 844134748 1250 844133498 844133519
    0x2a06030f0406060b0a05030c16080f070506090a03051605030d0f02030f07030c09090908070b0a0605100c050a0822090b1003060806161701080601031a06091b04 70
    0x1540002140c4011030805003009800c40b292075100e02020002000049a1180c001080c6c9500003400809076440d42e100c03030a1045915900e1b82e0061010030009109207070100c104002d4402507004404480195032003e0a80347e40e118940c0014011840074084166102180700d02030210520a500b41c03030030b00082d10100360942c0c1e89200c46c003820580100405c0507800d00d09107880c1d4402d41514050104c00040c4c81d0240c52205c150250012a40e2154005002e111100c03084424296000b58030042da0710b4414012070040c02e141c003505110302c103890102400e00c2d01c91244102e18a40220180c0008030300c43c1e50b48441b6501c00b0440c080d0441a44c464999940800c51600707005212528021030410b6208003048412007810081c403060502d444c00511101070000341003a44210b40048548910b03000c0760040c1c445002818070300012180d800c00200b044480071541c603040300e1081115854240110140d06880c840840305a5006a41d600000d1580385007508400f01d0800c0d1440040d00d0240c179800c0e008e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 844135998 1250 844134748 844134751
    0x70c0801020c030d0f0b0904020906010203040e090c180405030d0f0b03010f060e100806010e130c15080105010503090d03050c13030305340f05030d0516030c020d022a0603 75
    0xd20a40010a0a105281c00307400b650315018500c05c400c011441c01c0c10002810703500013800190042001c2c0001a606074000c104540107421095003096a03441c240c03a10035034a005c0044200d0042150001e109d8080ca68807440d140240d40c40806182464405544080140b07415611010016280c00810059450a2180030300003096904045002c50819070034140c1100c0107088810201c030030803404c000411011400b541910804262080a034690001c0088060300014001d80306400311200040d55110400c0780c16603402064840c03405903030780d40006507080e010031141c2200d1070b0895801400101d100790b10050703100b030402d9503081c140001c00417450104a099002103010031000103c11102110407a03d0800220140040c898005c0302048a0022003440e81d100030b0650b04805000e6003001310034802d03540c0c00400741d50200101c1c5009040023444603180c144003004070386000c0d80c4449031840405c06822501c0350381c000f0a0640003901200340203580030300864050204c3d441d0200c00b0b995942000b90f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 844137248 1250 844135998 844136017
    0x14010b030a140a020901092315120304050a0807090e030a0804030f020f102a02150a020c01020a0e12010b0f12010f060e0405070b0301140405060d05070801151706010902070c080102 79
    0x26a6000c8d05130070b20300c149030742c241c000b080354901040000e0140030302c0480c80317106004d0710807111040d9501009840d60089401442d40101c92401c00b141c011800582e0400b203403000701061000c41004017030325480344140c048100000304040b00140100740aa588488840350a00c110f030a41001c070080c7c00e082170074622403da0a5611105861400c00349410035a030b411860041c2414102c03146070010796144041000c034600ca41c0080d000480c2c0704a01e60503641251010002555180141306008140300e51002c13041d0b1003000303105600b44100b10f051140640d201009440c5480c11303082141044400c80900c07118800640d01c94040d0352a40e10f06015040007011444403082c43c40c01e081c60214140302154012a02c140d00034401041b00499500c40364600d00380a075000107080d140d00700828220811290083d00c103200720000010155030542c4074900c40b40400c40c0d8900640e80740c1c0390340818003101c07006940882e8005070042c08002160b50045c18190300c00e440102da841d41d2400b000d426604000b00304c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 844138498 1250 844137248 844137251
    0x319020c0f060f07261b1e031e191802180f060d110906060c0a05100f0b06040e150a030807060f0b090403030e010608030d060314010b030a140a02090109 67
    0x380240360b0340105a42c1c2d51705a1000c8042601c00040030a05101d0700000c02280019110352140e2101d00d165400700c034148403044410300250144c0c0d401000065109646040f281d00d0070403131000c0341e05418440c1c00d015012016141139150300b55840e100c0a000400003038411440c800c0c1e95240185d0711031004155009401c52158100e1401070003500000000810943c021030b04a42c41c0000142c5084c10003800040440f104000c6032500d4010a1680c0505a400380d524803c024265040c0000000c3d02c80e030003c505202880103001e680106002d5540c601e248903000901407006109030820120b00d0b0f031344849541c00d0003e12110b0b860006540720400d42c029102d00d030b400540c1d507042c40303005e000d1130503904c14064051080c0d22075107001c6101081d0052010303080560302c0907442e140c0d403002e41007000240041e10480740c0f100089880000200b0b040e01c022a01c41e490b03141020800c58040c040c0420011009000e4032a000b2035455030502d01b102207a0390000c0380503c2c00e01d000181d503420754550103080341030070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 844139748 1250 844138498 844138501
    0x61205060f0a0b0603012115050a050a0e101d0d090305060a14010303052206120605040b0d080c010209060412030e01110c01030207032f120319020c0f060f 68
    0x3401e000500020307000c0b034040c0c2d0421880004944940080f0f034111401a50841d4074840041d8003444009109600280b81e002c2d030954141c465203546e00030300c0c060140b480301000640c54a000b140c0c1260071102d414032242e04030b1264090b951005a220f011819019180080c881d040c0c4140b1900307103000707074500001042c00c0d41014400c1c00004c2028640c1320a03140c108000045c2c0342d4900000c01441444000c0c10054001100c00c0c02102c106d42c559054400260380220903915114060542e000340314182c1c0000f85040400241c3c0c3c03070b01d4042e028082c40007501d03401d4510007584500306154040c0680c41d50a40d001c00524030703c0d40b100c0f8020f0004000e841c05075a1140f20b40d28000309110415001a4100074800e00444510b00b804619410440303801d00b4010380d940c41a140c140c0c4d038036580c16590031550f171307201c000300320354890344100c1d803c01503000030135181560344200b01101c4038001074811540410410540402544150f0300408028800c0c004942e40c032801101420324244046030308480755841e200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 844140998 1250 844139748 844139761
    0x33060303020604150908160206091008160305040c05090903040807060905150c1510030b010312020f1501030602090d0501020703120f0b010e0402031b03090304140d0f02040b0406120506 81
    0x200c5401801030480521807007100341c49680c81b501881410700c030341901908200046669030411a0320041c406850221800121038029015507001c903185400600019a584011803003849042c0c40f80e580050200c42c0d507030601d420f00407c0680246038888030301c4100f1010070641c508000c6c000080c620b41e5207405105080100340040d0000560400350003010501c4100c04c00e40c0301081120100842143c08a0b0540d204245d0044c00c002079400070f41100c030200300100c04c0c011900b044400c00c018580071150f00780d452501e01070ba10b000031000003110348281c1005000041a0341c00030691881c0c0141414002c015540b605800c80c1c0c8058001c401144801d01d03201c202c201c0500510741140c580140800102066078006004a058045243d114503400400200b502c0c10761041084e281580b0440ca0b502d0b4079280c3c00b031039600d92103402040d140c480d07121002d044902c2c000c0c80d503100706c0f5406841c01c141d4030f4460382030001400b00b1250850344643c80d0030001c281c9072454070300203030290300620081c0b040741081c0c4c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 844142248 1250 844140998 844141013
    0x209041101140403120f0909090c140108090607080a140a09020301141e1f18050109090305070b041113020a08061507020603040c23091333060303020604 67
    0x40207a81c9800148004c00c0400c002d502070207440b08141c01c01d106c000e4520b0070122602d0f421600803048440c0b50034245014800020280420384900403e0650b21310491401514003940c122030f1201c1c0c80d481107001442c1c6600c01c0c1022600210240c401080400c02900c00c40300c0e2850440c0d0f10810255240d000c02c0551609000e014003541d100500d10321075003041814261078402c1c0c3c1ca110129031025401040302e4100c03800340080c10201009a40e12100d4071103c50440140081e9944d607149820200003141c201000e114004000c2d605480d5180f508416a0360f481c0441c4004100b40c1345c005d118031004406171103c54500e010701901810040e03550900080c054010f6401400c8030303000f0100c400300d00540204031001c03215500d404071401034903560f4034641040501e9803500328250200c9501c0342892425954580010038550403030705e01080f90340b0402c42000303a8400790b4000e8044034907008100850070035110155100300c018030070311160000000100b801d41d03075075900460050340810100401e00000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 844143498 1250 844142248 844142267
    0x10b030312070f03050106020c100e13050601261b1e030109060b030c073c1401051603020d0e030f0a0305090d023315042d0c0c0209041101 61
    0x581c04d08002a50401000075558001400c6a5000d1040072113401d0b04c00d070003401d403203064810052820f1320440c2054135440181c682503d100d80401c00610704403401442030780341c1c40d500c803c11101040075035840c1c81c218010b002540e40c0840300d0100030403c007100790aa9014003c10301a1014400c0e40c0c9524140703400003140d042c0d038400f003030502c42802481040c00d005403c030740e011504900003100700c0319411222641d101c0800007034401402d6000f4085d0b250600100407081840c060702c03001e40c0c141c108412031b5090b41d07012142a010b503052030200090840c0254060602503c19030b0001a01013102a07107149940d1122181100140300400d4031101070b9407501940e0b600810500180c44d250f400b0040c003951707406c22030142001114112640c804d00e02d14440e140708240c0a480b44080c00c1d07040207500900403c40d011803160041e400c2800018500303c070300a09007400507400401d0845e40c140103602000400d29520600e081040c07900c03960700507a03942c20032a07005074001c041724610446443c1c00541900c88 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 844144748 1250 844143498 844143527
    0x20f031003120c02150904060803160210031824090303020c070f0b0d091b240906051b10020c030c150103021f030621060b0402090a17010b03031207 65
    0x3081e20f0040068079040814040c4035134265038192a44a50b400240251405d600180303402d00c00171911903150045948500001c030300a445141c09060300203030480607600c0001a0681d46071958403110005503188411001240780c2c0c615140700a4120340205054a0004009a00094011802c80364038031080c80648020300c3e92902d2030642500d810036051850103401c50003c02142e941c1200001e10290050700c51406480803082c1507620b0302d54003050242c0d10140e000c1c050a0f001b440b803070891180030304900018ae441355142c05080007007003140043c45140d40c8c810105540270b00050b407500f11040c2d0000d0000f81d16024061900c540c20004a545402c4019018060b1800f800c0300401c0903841c4d804080744000c0c046080300b00110320058003034000c0d01c80b90740110702d00c10301440c1e01e00385200c0840e20004031500c107400c2400fa54519000b048264028101c0040d80300d9502d00081020f04501c200c80e0b4682031111001283c145007440000341540c0145030f00c1040020b00c5800c000315264000b048880490 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 844145998 1250 844144748 844144757
    0x302060c07050f1804020607054306120f020c030a0806091005010f052203080309010f0b0619210f0b011e08060a051905040b15030f0a020f03100312 65
    0x164900c50480c00c600103440a1f024030000200300052000601c40365400e00595030710040c4076a0401d00f0451440e03504507000d02d1500c02400701149004000300a481150119501c1c05244110714496800a0000d0a031740704803664200f1162a00000500103031000a07504e8880f1005403070b1050500c950058018281c107809604010144841c0c0c1c1c0003140c0c40c010801ea0301d410754031440701c1c3e60840801d000c81101c6400001510800008000d00704009505c180306540090190300030b424400c1c400d9548100083e0303407041040c425040c44d0f00c0c003040b014581155901e480c40c000c900040108050f01d0000c0041c4240c0394031146035410b1049107000d4511005421706c0c10b520520030b045840c0980170390b406c40034000c00c45410081106a0b0741e070b4055034064140184616055401920124a03001c141e114231405141800d00e1a011444c240146028110300c4980003031031983c841900300404907008040245840e402c2c0a4803281c5d52024000d580f00305e8550884001c3d0750300307508150019a8103621b8550800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 844147248 1250 844145998 844146019
    0x30b0114120f060a0203100509091e210a0207050a090207111806041a1305090f0f0307110103062105070506040b04170c030a1208071e180302060c07050f 67
    0x20b01c00280f40e40d8049460200181c0340d885038403103400412031135480f850b440014030090100c5100080740318401c43c001d941d0b5001c02c81c10301864058660301241c08003185040e600351158a00c0030142c00400101c40e80d44181d0300d202c0d0301d400000c0c6640340035400480c181ca60101e2000c0400c02c0480384e415440c85d045845034080b1a0042805000480080500d4012a280c4905042040b3b01c032070704000350b420050250442d4091080410010300e001c03100b000892280c50381b022806080032440205d0b405e417860265291400945800005884c0084224101555401c1c00070b414010b44004991000c6803c05815403107072035040040c070700b20342a04000d204040402c82005406260422542181d400742003031049aa0010001810050014007807a050300864404104020507075000f003000b60b050303440d21207142d182e4003022107482170741c46545250f00240034640e0f0821400b0b0040382d5290400c40550369006600e941c042101504201c6170f02c045a441900c040c002480d080004807005038040e50380382c540d07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 844148498 1250 844147248 844147273
    0x60108120301050f0f150301090e070512060c25060501060f0905130906060512010b0a0911030411030a12020609010c14042d06020d12020909060910030b011412 70
    0x801481c080301a20400c05225900111b07240c40410040b400c4891061503101c0d030b510114540034140b01ca44059031030042001c00304483c40e200c9002c100b841588002030080f50388a40d00d110340c507070085000721410b8443d15114851074084a1a07030710514440d4801181c80e5141200141429050401000900100c004140a03d417180754a03902d004e448103e0210308904c40b801c010004060640069810246094200700d105105420030740b18088141d135200212035031209490700f215513806800c40120303070800108000c190a03038102c501e501001020b40302001c1070390b42ca11681c5070403450b952016802c00d10412050100030700c100300340302d192420320002200390102454a0b0748640d000d10144508802417212000201c0d481c1031810841c030041a5030030588401000c2d65624980780e1140000d80140388418000c03d05000340d8140c0d00c000380c500515901c9040c01c020365804010140366141d070380264000301051104140f01e00a0000c0070301800c01745900b00602c03840d4002c0501e1220240d002c0350b240c040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 844149748 1250 844148498 844148509
    0x40909060e0d12331502030a08061908150604060503030f07080c030c0f0102040509180a02090601031104060e090a060b030c0304050a02040e031c060b180a120506010812030105 77
    0x90340d80300c07a000541c299403800f1514601c913458401d004ea100048480c3e043c091008010a01560b400550410054680c0c3c2ca0480e40d92051004800c00a02440003240e0141400003503180214003c1c020001c010781c49050b46842c0c6001d0b00d829040c040340d4101442118100340c0300c1c0c98040c2c03c09a0240d803500c0d09201c1010828407030540010310201002a8110340c03a1400c1c02903c01141c05502a16014a03c4100150207034100f8001c0c01d1090715010b0109a03104d041c00c143c00e216003001406402419a507400700040490001d2205d07044c0340e02c5246200c085d4182c1001800600307900d403110002009502c050218507580148502c0c401c42c039150050041800403c00d0b258000101d1280c25902c1c5e84034501709007010b41940c402900035090148a0342000004405800c00c9070810b0020f48a001c9281070040682c0c1d154170035510480000c000441c201c6080c1c040c0d102c40c3c039602a00c8070b4000c644d5200107200c80c219100c400e9a09420103001845610418007c0c4a08180c80005160855040000090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 844150998 1250 844149748 844149767
    0x50105060412110a0e130606080a0c05040f090212100e0a0515070504240f1d0409140f0a1a071d03100e0106150206090303040204021b03040909060e0d 66
    0x10903504401561031003d540d422500c4d4007401112181d00c0303085c280398021340768a04022204560550070010041020b2500084620403c1e03003024072102035500d03000501c001410035404165425031076480b0240940c9a0f88061098126a40e006103e07900a0700d5100e4115260b2070762044035a0810302c034140100702c001a03001d5000301e40d2070210089850321842911075100320380c01110103444a564620b4820714011580e0381c280c0d10b581f6400e45540c080c0e54200c800c5054a04e11003840610000905c00130708041d401041d1080c03244014115010076111014039040b030008050302c01d60b101d0305500381080040000400b11003a0812119110b04041c400501030b4134074030207400c005a00c644502e541540d410082129080c61400381004010440d024940c0601070354021010404110701604001500c000f4502d0321440b0040003941c155200d540c02c00c0040d502088400301460601c484000d0007200503c0200f00a10b01c0044c0080c2e2144d035450f000d800d9031038007402d02419070042d690103400c0503040071009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 844152248 1250 844150998 844151003
    0x61d1504091805011a1008090706120b1309170f0307140d090c05010e120c040b0a031b0e0c091e040204121a1609030807030915080a050105060412 64
    0x120705100c80391a09158982c0c070b810058034944c2059098040541e00b020708900c004e00c140e912060248050400f590b07000001e40b201c0e00c0c158805042040018450807817954802600c10000c620040c011000444140300200d9a001c0760fa56000c49400f007244400301048100c1070302102e541410504031003a000382c00000c24400601544c00b9090203841c0304201220140ca1110702d01304002101410300c9c8801083d00c0c0590350108964080095882c6400600c80500d584418001d004011031402031201600300396281c142c0044507854048005520350201d00319285c05424481c0300c052410f0300103624a400075108030104002000984000e80319030013407a503219100c5070000c00c0002c010010170000e01c01e80d40f2100d40080303101483e10402017884150301442d1410a0072071542c0d21442c0d459256481c0c144030301000b242a17800b0400c0003851100c00b924043c0e020303007440e001c05070f41c82d001101d006520b020300c900040c42700c02c100a20b19205c1e1003800e001d89807d80f80315007002d04119a9a81c01d55410001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 844153498 1250 844152248 844152251
    0x60d031209020d060b0f010203190c050c061b0601050d11040b0d060f060302030c060c0a0f150606050403061d120c01020d09060903110606060d020a0e0a061d150409 72
    0x32614014503a04412403055000e040701c5000c0001e4140a0010720048026a1080d0a80451144150300c0001034440c408095034210b80c0c070790074407041500c000c2c0c01d40400b20342031301a1210a069550f40e410282c40e5023000d0280c039581500444c0c2156081c0041608068440c01c00b015409011034541007100c0c01d20f54080c3ca002400560100029400c000c0d8613000402ca01e003021b404070300059094008a088038829011911007040e07010421000d030243c91000d0040d54854001000842d41042d0005103040c0902d0803001c1c10b00e030300340710b40f070944030340750800d1300414070002c0c0400c01c00c001440b5944030300e440003010050b094207265070b0340e480300b07520814400d0048001c03500010300d10083d8115010701603a10010400c0c01c00341c4c038005029168102d006e6000c14a00d061400050b0f0740842c0c00da1140400902451400c414050f00c44025000820079100b040450025800c0ca0f0702c81407001006403a058807410644415050b080390a42e17110300d4080c0c068079401d04000003c0000100391421381d65161030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 844154748 1250 844153498 844153517
    0x405070b090d0210050a12090b0a0507110109061a04150e07030605090f0f06100c030f03060305011401030c09060608062e030e0d0309030c0308220308010f0806060d03 73
    0x42c90142078110301075801011400031002d00c1e07401c0802000b240520340c8034180103280140c004030480d2054000034210341c640000040381001035a020741ea000c9a01d040150440500701e00440c00c4071000d8030b0840d025036407680242c101c0040e075148501000310482c0c0510806000180d02500c0340e85a01c500055583c500300490711362402904404c01411000d003600006282c070811301c0e00004c0080d111000c41d8454040898030300c1c140741c2c8494581340d090307440301c20b150505694103c4a18035031703d004204240d52781c1004070014000703001d100040c1103245103141c007039411820300c0300d151810b580c8100095454070000b00071442d00410140d038400c00896400c2e00c084199807100707100156504845aa15001381c1c0c129004540560010000307806c7d0100f00c0d0001c440102060381101e003440009800716008807028400240f02e0b0720701c154001d083c44034090034009180250102410300803c1207000c1500480103100794012802d00000501c4004000d10301400e06d01c1c081028441c1200014040204458 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 844155998 1250 844154748 844154767
    0x60201110a0f1d15030f100f060507020604031709130204050f061e0f0a0e030705210109050615120a030504060f020f07090603050606040506090105040c020c100314010e0405070b 78
    0x180d0100c21502c0150a22135030a0710125214203d074001c4030000e0b2000c25240101e11480c01680003a01911b01c0a180250414203022059034a5005142c01701e078401420000400010b032805070880c050070700e50311032940341c59144041003410403150711402c401910500c01000203640324100a01c4082082d190241c1e112080006290160003079040042040340005405038044000340040001c142e031a612500201c244904140c0c440c4100d10a80c1d0340000002c140103c2641c0070305000001020034000040e4000789039031190f090800450b40e00400b240e031032511006506194208024505080018082078070003a80d0181030b0b4000d60180c4810000101c1402100703034020007500340d650300f40c00c0440b180a0380d100b0221015000b940002c03036160007210040340490030507024281c042da4000707100b019141c0c00c24003400020410300d0007020852082043d020303015147c1d2401245000416070b000b1451400700801503680c071b132041c1d22140451018200f044042180440c1000944000f14100b554492245 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 844157248 1250 844155998 844156037
    0xb10030e0a05011a032b0305060d0b0109021e030c031609120b011d06010c1104061d040501050c041203200f150606091309020402120907060201110a0f 66
    0x54400400710342c078007107240c41c01450f54110542d41c1c24048040300e4a20785441d00c2010460028400020800205c0c6c4030000901d00079040f507584010090604903c4200310386448500000070f9000d18003484d03000030071510390440c0302260308000d10180c40c2d5500d14100500501440c2c8001010050078100c400c41240d515485a8070500080c11103c01080c401c0700c041c10b00c1e4281c09001e1044c44265075030914542c03200d200d40c0d00000d21403c4140c44011200781c9948502445c01040c2d1800341d402030340d40d40c010030181c0820300068445000b40600100c10720b09807525a0860b1000f9000f226001d409110401800c2c0b8a500e8448855a040c039000d0841d4601881e51041c400c0b20f201d00346114011440209002038000501ca101181c90395090300c0103131264401e001981c418803214540041200c142c0c03410346c003115017000c5031b07140c80907200501d0b00000454480c401030f4140c52059803500704041c00c01c2000c0c0d0900410ba1802e0302910912f20304866044042c000c414828501000e00c26101590391844d41003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 844158498 1250 844157248 844157263
    0x304050d06060e160f0e030d0c0311010606050d0c020a080414061c0203061008060102070603090c1e170102090108061011061005180903250c0e0108060a0b10030e 71
    0x440b003854154105803640c80d4a44075a5914400090401c10841004c41d20440f281d00040d00b000d4050880d004d12210100c0390303001c80c3c040c01e46c107000382c076401e1092f01c0c582481683c00074000c941d201ca03111324690100c401a80d61301c100b0a0110340c4910301c80e0020902003001c807021202c102117001c0c0c4016001d004210755003d10304030390140040903048002c11a520f034009510440d8115044450580700c00c5040d101114107813801c40c0140d00030032061143e64004da018592450261071035447c2c843c0d440d000e514075840300038201800c2a620329010030546021070a03211103407550340b000354200030340c480c0000c14400d002886144681034044080d45003500404070b10003013842c2c9034203850040c5070140e150040d040d514032132a070180f140c1c044141d40c420190384c18a4099641c01c40510710f00608069040c102c80c01e41d18802ca8841c4056060400190101c03c1080c002c20306400c402c0074a40c50121101c1c02d1480092038034845c58100046010390f5590b800108081001504000030210f404440b0345140c000ca = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 844159748 1250 844158498 844158509
    0x316030b36061806130924051b090402070f020a08030903060f0f0c0a11060a0b120f1207020a0b0d05040c0b130302040e030d050f15010c050705040b18040c05030d09080304050d0606 79
    0x14860540c6aa42e89110350b40d450040c87ca003801d21403521070824141e5200271110540712261001d00109546281c5030300102200d90150101c500031048a40018041c1c01042c0c0c400c10041d8800100391009081c10f101140d07220402c0fa110302d60518118604025501000348442c034401400580000304500401c2c10401c5c2c3e01d2031104a030514601034030721380d00400718004030a00c070b0119030b080340035808000500140020384c1e0b080034000004800e004001c15401c0349208a034040028540407c81a5a100140902c001402d034042407504060070801c5500610380c00c04c070002c010811015020000250449040300d6065400007002d50780e0301103081c11070040f58504c074411802c0c8024019071411654235213000744680383c03441101001c0fa000545480c20403580c010602c6c1c20800e810810381c40c03d580f200400c11405003007004038005141624076164401c079070465855204130b0062016003801c01c0910203142c000d0420441c0d00381042c0d91245daa00903481501d00c00d0f0300e00c2801600b0402c03907400800c000c15 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 844160998 1250 844159748 844159763
    0x9040c020a030c08070201050d021b010e01020403050a02151b1b011e080c0415110c030304260309180703050609190506060c0d0804050c060316030b360618061309 71
    0xd086c03444145c2f5444402c441400c45d030a110903001f6448062080b101100d3744031004060240c05542440550440e25180b0600088140720060743c3c0c0005000300b8180c0c95106000d880e50b00003414103824482011300c105410414070004070640384454400740b40c0460140c0c1010149540c8045411560748078940040c85404580c000c13403031a65402c115804103005007481950300220b401420b056503405107100307030103452810f803003a500c03000300c01050504944060016280307841c4403140490142420440da07100e40343e80c00c0f010844015818402c550b00304504803000012410200c1452030b180c02c000c40c00d680c10307582c2e03a00031464960314201203840d007110f5002515111242608083e214000c21101600c460203501898200e82c40c04c802103900c0b483d55090035480510f110b110880090010005882c0c00980d841803150340c002100007010440c04509801828800a4810704500100003404990003031481d0802511400c0741d422945030301110a85400c0d0f1302401e103804d1440a08030410b00034046a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 844162248 1250 844160998 844161007
    0x25050714120c010f020a140d111b06100324093207081504030c0c0f0f05120c01181d06090108150406181709040c020a030c08070201050d02 61
    0xc1c50a4090401800d026000301310800d400505801a44540c911750313000119401190350517409164050040e05865250000701c02907040040c107100d074800f01c08481d20280b00d00d040c0c10703449400c203c00c0354450920500f4000d224515612500b0114182d030f03401780c04081610340011050015403295004a811031081e840144003180d00d41030324200b40004010101c40b02000001c005d100250325030440300d03040010840c0082d1503800211101c1c0c007920850030410341c40707900004107440090280241424041c0d1981d50b910b007500380845890540c0c4514024000e2a100f200810001700d2410504a028280108440c00303103103180646820031340103510803040f40e50f150506040c0c4d90f1540c5200b07807425203a610559803a4844296148000000b8041c4c01c0e440c07200040010300541c10008101d000c50022400c2c00d182c42e650201c901d8900000c8200c01403000c1342c02003803441c0c28045c5641608180c00600107404075502d008140d0f00c44000007415a0304001500300071a48134900700d45e1910302c03400003152038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 844163498 1250 844162248 844162273
    0x4020d020f0d0b01110703050c150910120f1514011b140712051c11070605030603061315180204020406030b030d020f030909091207050a030825050714 66
    0xe020320043c15000820203095040f03103140011342a820f4a401c40d0050800c2d40042c0208003010700104214060b03614180f24442c02602c0300c03042020540500e03100c01000c61904201c2904450802908a01150501e600a265a584022618280c07084036107501100c1d0396080c0180c5149002003c165400c0d58a61070013411f11440c1c00158000b02d5128054034522a80e901c01c051107550803034006002500030b400c03002c0784030303030310508001e40c110b0b560900b004d101c49480d440a08150f4154001004544000104002c4c2d2600b413181c26030240009480040e15480c4c0c1d2070342c4809100c4075411401080d60780c8404a8a80070204503150429402003081d541e5586620740140500440c0801c4c2c0c0c0a0303c600001c10101d0b41c004561034529800c100d0003182040004801c02010090142c030090490180c44441e0b010014800010f256540c000c500910038002d440c03400822841000381003100000c0c044035a44a040c0310701000700c12030645885c1c07454503075500e400c0c100c0da45040414000010320a03024030900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 844164748 1250 844163498 844163501
    0x30e071a0706141e15010f03021602060409200a021e030d1d19020303090409031407030f120b0d06091a15041d0c27070c0c0602010c020c04020d020f0d 66
    0x7080c0100c40d0703850185d1604001ca01c001304c070a0130345a0226555100d2002494400e030301038009500c1d004880b1040220b21b40220300c4a9025030054640780b41c85030041c610b041c42c05450300b5003042c12491940d00d030114894000752941c6000d845212005c010a1707628000050400030354000300d15944c0f0401c0304504000f8000803e403140244404540107211060040704002d100c14488140c024003d1458002000308000007084c441c6030880a00c40003020860310140c0e480050890a8403c0c0c460b0440102081d0003e44411105101402981e051210030320154507403200c0720041c50790200c00070030940d1152800e007843d0320641d801010316682007801c000b0901d201289290714040242c03070401c2200c0e00707890904401200a44400c4450740310f16207403261400d0042d90006505091050340200c1d401800c00843d8400d4207441590016402c030f040c05003889000f0000c2002070807140020400340c100742c100692a5411042400c0c4602d034041072101070046150100c038a07054803411061341d5003194060301d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 844165998 1250 844164748 844164781
    0x90e01060302120615090901180c0306050606030c1c0e0109050106150302040b04030807030212030a0b0906370f060909060509060603130302070e04080a030e071a070614 74
    0xa21a40c42c200003100c401c0408106140246440d15400c00b20305c10250074800b540c00080c103044929965031306100d81c40d41c00c04582210311740c411040e484e02245141001800e961002e403050f8482e00003007040c03007010219901210030001004503001c5006540c5481c410041182145803c919400c148080b000c110703040d4030180566520100080d001a242e04040f002c078081d50041c001b035960100b00070f0010032061405801c0e80ca02c24412030756103248680c200c200c01d07081500d509410b551140001d20b201e15044c03e1651340300c801541c280d8400e006001c0c1001d600d100344840c030040c942c2d211624524240001c8002c4010b01610304150000aa80380801045d07000c1038842c490340d01d458090082124500b40940a014440050041c0e0468450040c0d1001e400070060b0100c00f580305115000a50a501d404290321680c0030340d020700c0c0c94201100f00076003603407160808075106401c18176081c8850054a14544601c1c4c0311100041e40701c1001e86448001040414001c0e48110721280130000308101180050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 844167248 1250 844165998 844166003
    0x160b0d0608030c071a0d02041d010b033304150602010614060406200a0309050102190b2811090324010b07050c0d03030506031b09060118090e010603 65
    0x82050035901c102094aa001d0444190055000b9000c2002410304203450395000f40c05a0700200d00e440e1000c07010800b00d9120768003040c200320742d0140e12150b24107220101e03401400003510031403840c039140c0355050000800a482c0c103203080354507000c904245007050040d40c540001503c00c1100e48140e04504010762020b1180500540c02c0003404600d01ca4804002c120b0410046d03c010f04050410400303030380059a411180003c0d128548159200c103c08000100e0280c1c000d44800109508040c0024103100920012844420700031400300c00044490030903d43c0922803400948141040d203424074285038a8100c035402c0c0e0741c1011408036049008000070b10300c40d034003113046416220328000004540808011b0031813812403d038004001d0140328030f0003000b081d03100b0011b64540c0d1200000180c170076441c82c182580000e540700200806801c0810442521920000c1083c3c0500c0088002590400c40100240c0c108101800180050003002c01d601d0007500b400ba4083c0005490740c10494020001484107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 844168498 1250 844167248 844167251
    0x120c0323150d021f05071a1014030c04020a0e040e07060e031204090b040b0316050405181c0315080309030111040e130507151707170f0702160b0d 64
    0x41d4a14203642c04000e01d55001c0c181080c880b40e0181d1076806402001c84001c00e111040054000184030510f40160401c866403443e429030400c032560050660075030300b00e20765a1210003c1d41405650004440002d10700443d80541d44d00480351044849401050340240c00508180e0400d001100102c3d011058460554078a00c0d2805400101a030b00c4280700c2c29400c0070310b0100000d0100c0c25007904620000300000c0c0020074403c0340d010100340b42a115010080103601c090b00c2c00d000d0307490540207281d009100c1041c00d00b203604031001283e80359141203400c1d04c05410014400d00c0c2140c00b941203aa8100d90700c0782021891540c0741c1c3c000b07807694421030394103100e5440e00128242804180e019201a5400b04030200c03c00d40d611b00c92200000301c5081c0650350351164500010b601c501c10000d072246480310341c0c0c487c400d00440c601d50003501e8101811031002c1c406500110f494400c0412401a440740c40c010040f541502c41c0101681085a9190310f41c14200760440040740d8181c5442c001c00200421920 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 844169748 1250 844168498 844168531
    0x50a020f07350a0e061204030e010f020c0f090411060a11010c030221060a170708010f09030804200616021f0519030e030406020c1c03120c0323 63
    0x20b404001059918181e0010401441000303491440784060040304403020f80128503003401741606a04000e01101c08500041e82c3c2e0100201d203591041c8003000032900ca0000701118198140001c60084102d0001409030380c88a001a06001c51520140c814910142595035a03201e4250010400d0310512009081582881d003c451101c0c401e10031140e40441f004000611402101c0380003607000009800c89034040300005020070fa00704410035032449450482c004090013032034441818203645080c0382c0c2e0407415180030a0000400d8000a000b43c2c02503001040c05041208013001490504c0200b010541066001c030701003d50400c0301c80071600b02d600850300052208100349001c4c0c403491102403100f0000340280688042c142e44888180c2228105050100d1600c007400e00007851070700175520807401a80070308840006407c104d041414000060080800302d01c0c955200038104002082d0703c115819525008010824440d600c04801007682e040e0807000c4043d081907801507428162010982a00a00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 844170998 1250 844169748 844169813
    0x90e070e0402060409020703030f05010915081605040b01180303051b06041101080601020c030111030f1f0b07030c050a110a080114040b18150103030807090315050a020f07 75
    0x1050910490b401810689800d04110180c006500020400c405260304ea1010250205c00c600403180172f001d0308200041c0b070703001c24031b045c844012a55001940e20307001011000f90002105880ca0196241070710302094154030f090048840d09000f40800080f04812030000c01010307400f4000304a01e503002400caa4112442803400c1d40c40d01d100f5140202244184034110140394020050740e9030045050040e61017940032400401d00f0748082c4161007842500000400400c0242e295807590028000304000c00e603440c81e045440030f2020180902d00340c4000204004080500c1b421445400720b038090150f41140d01c20303180000c40101a0114131b4801e000348900072440c1803051007154210305403013180c02c4058540c0d445081460b43c0c0901714034106400c614041c0d0a04004118042130503c1c45252000550302d1410009c0540340c0c041c0c0740703004001d4009820804524a8070b0031201c007043c000400603880c1c940001900003481800141e000c1000013140c5e01082c040c5004945140345040e410103100b40c80409d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 844172248 1250 844170998 844171019
    0x80d050406050a0c29180d0c1407090e010b0a05190b160602120907060f0c0b0a0b1f1101090b04080d0f0504350d0b06070c090e07 57
    0x500400d800a40d09000003c5070501c621109440f0701d000c1d45c40302c030034582099458400704001c1c020b40801100c3d4034080c810380c00d18a03a4038901d040b41e0540130304044100b50200822a40c024000030f0030354044100c1481c0e00c0941401800014402294100712282e59280b41901a07c1c881c42401c0c8203809041d000603040c1884900d1080010203980f0051080d420480c3d90051900040c00c011000680002c00030000b91041c1b0040a484201080180315880c1c01c151080c58240c00383c0001c2c080020b450346082d480e580014580340c0b090b0f800304040c0e00503600c40020400511084403210360262141620031070302080e83d261010300000e26920b01101031403403048030342601d0340080c00409080d825800103000c1b400b90809411a00007524011454074030b400006801d071902924182d980c040c480220000704048101c0f40700312051900a110b281100401400303203e406080c0c0c02420140e21031812075003598491040b5001e881d401404201d40030303154010407009242c00708e0740001030f200354000401d112081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 844173498 1250 844172248 844172257
    0x64a0102061006030e070e090105010315090f02060d02121513050f0406230403090f2103050a090807030614100b04031b0302040203240607111903020910080d05 70
    0x2c02d000001e031180392100c110300070514a400b0300c0d21802030751404a41c00e24852051760141c140d5000104455040d0f04080f1a00c0c40030108125443d46002680000980c00d040702a10840d0112a025220a16208580040c0c030450046c0140813103070304200200c64819084d40541100155201c01882514500b5001240d80036100400f111351100300050008101d60410300c0d002d0030108401c40444000c081500304600103031005c41c08241c0a09041c000c10204600010080c02c42101c0c91003a46003120b907902040216100c09000c200e400140c07106c49500500030500109100001c85918540da4101800200300d82e0192000031310001c00400c0050246a40d110f0655100303c045510b40752850b42c0d0034800045007015030000c0301c4682d50002c0507031b46034405548100f4040c240202c180c818019501508490340780030b14415182805240007041c000200a6151082a40d0b02040000300100300440c0c09803c1e40001d602480d08401c000711602c1e041c8200342110300740e01c1100c044031880c22050311540034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 844174748 1250 844173498 844173511
    0x30612240c09120303021c091514150301060f09020304051e07170709050403020d090605130504050405010905030f0a0e0a18051009020406090806010f03050601064a010206 75
    0x30301ca000e024407003c0c242e103028814402d0400610b8055100d00020000c1161405072101c42e507184070400500c1903400342041d00e51444c0d0001c110240d18800000d4075880050801094184614004501d1b0344017540540003030a52070b03440c0f4980c0c40d03644103030700041e60046408541030b000d4004003240841401000c5140302000324041c200140c1042101c80c0041c0c40a10143c065124040d00014001814412540514040d6010300403002c2040d1002d02100d2050340b0050822008103e104d42c0006003038607040c07e1700e00851300403400d92100e0a0450140050b044007a11600002a01b0b81440300d180008007251121a205c4070900b600d00e204200305001f0038460700440413441e40b404108129964407660b4810b4000038040580e07a11201080300b01d17049500060041501e0001c14402d180741040880d0040c050881000310450540d940c1c07546400044c40b6000c28006000c203c400700d04503040c45021807400f95200b0401d0f22068150a10405401c1850ba00001040c2d40340f40702d0039407020410a1180b0b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 844175998 1250 844174748 844174757
    0xa151202040b0913180803160816231216080403080a0203180a120e0f1003020708040b0d0501060e030c01091703040302030a06020405330901030612240c 67
    0x903040c03007400701804e4104104485903507211850b8034070500940410122034060f040711a182e107003800f1401c00042c54242d0003001e100d40d010800c4100402c07045400507a0383c83d86032221294203075800140c40d152080c91150b2400d500410119412503440351024403035040c401d4004100803c454054a481c242900c014000604075000215441a55002581c10091a000c2c1c00040b604148070141005030306c0000721150200102c0c0101c0041d801107030b42d03640200c11640d06001e44000c00c0011500e80f042c00c003180034142c0110343c503c1800b40725000d171001040361014042d6901100c40c0064000c28003405040040346085220903900c0c00d000810f41010001a190805040d003001107140440001c4101501c00f031108102c00700068606103d000440c6110f040d002d61200d042600b00302908803944050040023500711034901ca404a800310b400240218031002c1a542d9400300012000b900040d00148414154003c1120030001492001904040ca02511502004c42d80304540103881089403c040001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 844177248 1250 844175998 844176007
    0x1306050705072c18010c090e2a0403030203040e011a07020f21060426040312020337140d020c1e0d1106070f0e0d020a151202040b 57
    0x40d1002001c1456240035201000202c00642e801e04122401266140d100301c03125070500131404400d004040390038405050080b041402c1001a503641000140034005a8502e81911401c803e8035444100d64804002d500300d50320342d01d0f0308020755682d03ca4400d12010f0003202d400014410452007401050000e04d41c070151070001c141d0200302c2c6000030320454652250f20391000306e03001c40030100700c00034201d00100070382010b00e401d06001e030a4441d840e0404812038141d40310280e514036140100c0301903036030280251030010000315081380ba60186802c50f4200105003500c01051071641503503050a219580248800d05482103c215042420211004506135080c04500f5400701c0603005401c0301401901101e1070300b10b00e03032007000c5016800c01c5e041c0c410390401040d0282940e4012400000d01400000500340350034410350061840b48440804410003103480041413407030f40c07030342d0144103501e800605010304a83c0342d5120103c510140c40c0490007041d45506982d003128240d0080d24111a081664103040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 844178498 1250 844177248 844177259
    0x60e0f01110f1906061a030727030f050d1e0c08091c17090a05011103120406060602012406030b01050d0e0307290c1b070b130605070507 60
    0x4a0908030000d0381074020b0a100112a03201041000a141c0e48840d40c0304401030b040c145001290b0454004400c8100300108004006440780e04580c1c01900c03500d0020302c5800010350404400040c414203e039000101030001081c440c0301c52041b00d009001d0806e44100c2904c000c0207031007045403007038108901d0760794001580000e0702480c6045c00c03080c0600c076030500d81072071140028030180b00070031500310103074421494406200c1100500084000f80c07030b40c001e01d4513441c0d0700042c040903a588900342c100000c80d07440d042c0c422014819a0031500315020b00d2445402e00e4903000d00a81280e02441005629240101040320040081c0070300088000360002c207000d00300702e01240580034000086042c81b00400603175850b10300d28481c510801110901441c0c03100c030f00e4904101054030041c07025a02c100301004011160808007603540c0c0014148d0180e41d43c42880d040107190684525810a6403400ba81400150030300d0100003e0000a080c480801e20a645884065485000f1141c028001d030344201c005008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 844179748 1250 844178498 844178507
    0x801140d0209090f070b1902030715020d0603080d0c020d0f1403092107050106050a180c18091e020c030d0213090c0507060e01020903031e0706090b10060e0f01 70
    0x20029403d006550401655850861400381d4951044800840000303402a5200340721401c0d4a010000e0b2000c0e44c9003001c940c941c4100000115501c01c01141d0020f40704812250300c1d172185004550080300191602212a0984010000c0194000c0580a41c3c1c00d89042240304400c658540e070880d48030a480031040d20117401c040e803c020f040400314403882c101d121107010032003808000702c07071004c10255441640e841e0a0f400c1d1001544000e000f40b8101e24180075450022900c04000da141035000122008514401c42c4d820101401d0306650078084100032030101c4403a0403640019500c138920348100303240b24510a013284640700384551290002d000104820150782c000300800e0141c482001c8050b6120b2030a4001ca60f040b04902d00481c100180310410401240a080c255026010086091985290110384caa1090b2501800022140c0351461400c034500c0082c2c07401e0a40209013005031003224500702c460340006540f134141540210400195140c4101e40c1100484005414418402e13501801900e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 844180998 1250 844179748 844179751
    0x6010b0f090409020a030b01090b09070c0b070216080304030b0f0402060703081308031806090115090f0f020f030708100303021f0f0f02040911030f07080402150c06070801140d0209 79
    0xb0b62081e2a500c9040241c1d4440c455038004d14064020348025500d86402c080460b84440c50b480e00801c220420007440980000b06100c210f41c0003480d16100350b6541030100d0a05407120306031040c081105030046400364002016100faa40b1640388003005440d860380d000c001034001c030b0f0000e601c08c408018480001c4d00c20802181c110105820442400032160b8a0f90900d800803501d01d0340c04900d01e0070030055040100040c64220b10102e0081140090340301d9000340301e64840c02040e40c02034071a1540085040d03690302051040c009550b0454a44904260034280c949c01071310030400103400e0001040c0720b4101507030384070102c0750315800801c0031001c41c01c1d1214240c0d98000e040d07401c4960f40d40140c19406414064010a0844c0c4000180d640d82444030480456917151444038580d0024000c020310b02c001c0c080560f8001e8040d081c051290303034036880010782c1c041d07030070380d41d00010310010420006122000802a004d030075940c540e055160780320a0700b00c0003500141e10071507021000240d030703801501301107a03144d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 844182248 1250 844180998 844181017
    0x603060d020303040e071e0c02180c0903010e0a050705010516060f0b12010b0109080d02151803040b07031d031f0b101106010f180b0d02130e0c0306010b0f 68
    0x40381015505c5040ca0203501080382d00f1000309482c1911a031059001016514a404186c202141000304980100706040e000c01d14035059600303507a000c40c2d40300811000f503a10f080340c002d0091041403003a90701c0039141c06507008100c0c0d0f40d00c6620404100366003e8400d8540340407101c00a000342d00e20701d448280c082d02c00140340151a96441080b80079a489030704428000010b140008900000210001401802aa4800b2541d0f802c004ca107800415408200762507041d40041d0300547e186c0f11442a1100d0510280482101784000103000542003d1034000e0401d440c003035200d10754001200c002090000303180a0b0102d5140d0007000150701c401035485802c2c0000d0382d01e1200081d20004000116031440c55541c18540400c5007034049018400301081543e0140801d50390030f2101a15090000f002d40261042000105840b100700104c41d03182c041c007084031160001c0078001d503000c4490360328004001500d00c1d000c06028203500201e4508000400d40d040350307030b1a04c40914140c1c0c2c07513445801030b40101e90035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 844183498 1250 844182248 844182253
    0x130b0c0319091a030f0114010903020d05191203051e1f091814031218010e03030705031503011109060d020c03030a1409011505060703051c0621020603060d0203 70
    0x1c1402c62040300210030003001942d8a41d0340e42041c00d480d8600781030587c0030418640080300c22203e0759034454500011a0340c140c4046840d01d400303281c814103010007104510744003140481c0d034800b800b882030586201c00d95692400c00c21605c460301d0354030800c0c14002c5a48030006041000c9800f00070907140c1c241400e001d00200e0403e00d51503c44c8202640c0605000c2d04c3c408682101a40c05c1c0544070701401d0204c07400358011403414a159840800340300d002410500200b0071161b40400086082d000640c0c10800c450503a696443c0c4010094059042940c009096071401b00101d01da5040c148526030201c001c043d03115040008540c10010302c0d5100100e8414065002e208024617482e04001a5000d10035005001c21021410f912686d06050b006101da130007a03040c0303400c6403e4080d40c400c400c02960b030309903626503030b0f8101c6080039601c41c8100d4170018500d803d0103c4200e1a81806ea201c1c4099411005010f0820007001850140030160b103400654007803010408900c0600d1706030b1145004510180a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 844184748 1250 844183498 844183517
    0x160917010902030f030309190f2d03021e062a04030212010f051b070206131212030c18150c050d111005041101030f060f03030203130b0c0319 62
    0x480d0a11400c04e440329100da1000c03050181e02101440420802c0e150082070400b201480e440d07007400ca1030400c80c0541044000143c10030380f07205001071004400218035010801115916009544130b1b042e03040e618061042c101015994000803417407074020702e02f40300102c5a10900303111030902d524001c000c1070110030b0f040000200503118155007a0382e105031100005003614608180105a0710010f000d10022100003100010f1040c1c00e005a5000d2034042d81d0702d40c2c550790b40c900c0992001c02160010328251744695a100200104105030740c010096603030f0281301711100d0302c0d4142d8041e0303000c08010580540822082c480045000c00ca2900e130003270740c6841e680b03001b5991101c44c20031101503903c034002550140030041c407403401c10010341c0c94032090104100e103262a032640420703648070764100307410107480e100c540c025030000e90013800182056201015459640745000ba41c1c0342d0000720340b207880f007030848000100400400c040e140d041640c00051454914041407015089240f0107042061100484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 844185998 1250 844184748 844184753
    0xb0904021e0a09060f050303090913080906070f11040501210602070803071d03030412080d0e0d0e040614060304031202041503020901121a0f0a0e100303081609170109 73
    0xa4821005088103080010712504000c0170804110203504558040d034020401c541d03164903880718696000030000c050004145840c42c00c0c1040d44100c1d4001c0342d200e0008a07401051080c2003107800c0c0c0340c5100d0902410900c020700203000c1610000d20819014841c4800100d440101011040c3c0f1345600c184401454014a03554205c915041070f20050000303a942c44c1100c14094034100308191240301140218103080c9003040c03840a10040c11340040001c10082820804401035821486c4140442c40940729610720407440140b01511404100d80703c3c605081d4002103081c1070b404441080c0401401c42e03071031a41c0d1034905aa44012004204070410703402c000001d10b003000c1000c205841c044c584d50240c2d540100230001060802c034010854070300c914154501268440e4803000c500b1450045d1002c900304a41540045c09000c2a90b002201c52490f4104010400b03103200b6a01003a03d10070f880307031240b40e1111400c406a482d000c0100e4400301d02c81c08000e0110030402c101c8003170072012400020030130b40c08aa = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 844187248 1250 844185998 844186009
    0x809060601031d01050708011e15110f06010b031f080601050d0c090c02031209010b0915060c010f05160c030516170c2b140c1e03070201030f0b0904021e 67
    0xc0710f006c000510000014031010130020301d80700d803100d0072181c804500381c00c000000244840e130b030002c4803e11810621400c180300080c8400300501d0003e8040e10f00543e5030741403844680d401150440b84541c0000d001c4401100084409420703102008001c12051b030810703048c09079090300403105481da010080d000040c100c141e8010072132120b81035400303036880d8200b880c490b101c0418090021200d80c0d041c880d0785040e54807400c0c43c45500a40d5002c03403100381d0b19210301003a6140b244c1c0c0c012000315401c01050b40b80c00141c0350040d500481480c520220b0304c1c01010000c1700c550a0b41500100029010044011205000c40060402c54000c140d200c11a9180b00003c80b602d500c40100da24803074100b5043d0803c0541c03665000d2152000c0c00142134042502454028880f4402e002600112140802c51062009042200300c0703c440e805003003044845021802c0555035042540100c0c00241440b07103024a0701030360301070101d01c0b40e40504002200c3c3c8541d800c22042501e11120031500107600010b103005039640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 844188498 1250 844187248 844187251
    0x200304050a020906013e0d030e12040e0a110d0212070905011803030c11120703060b0d170306240c06180a12050403081215010809060601031d0105 64
    0x803002480c20403440d1050280c40580144003a0500c0080524210001c1200c41d4944020044400d41c46100302d0307005c100422079076012400c00c0c541c481c45016508068256102d0f800140a00c002c9405520700c40740741e04507a2150740a101d109225210204550003415045205180d010640050405002c4581d0034201c0e00b10803036889004007140240003000f5085424440545000c0c80e00b003158109003040070078901c130944402000c10195004c143c0501825590b42d0750b003150000c01c3c0040b070000742140d180c0d44410720300059814030701e490444c100700e02d0b201c80790690342503024085100c0c80640c4000400766800040005800040180c01c201c08070074544000c0c1c061441855241d030302d540e40c0907004d030301e000e1008241c0400c0145a400140c1d8032000018102d80e5154071039001d203c40300c294541140d90780200d500c018003940010507601c444085c1c1c820f229101e442c00240b0344000041e01c400440d00040b082c0c4070003e00da00b00380042540d0b54460307040000c0c0700b01c3c04054150941008403c20342142d90 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844189748 1250 844188498 844188503
    0x20306150108060307060801140409020a0f15050a1b0503092d01030501180e0f0d090314010c12020f040b18031903050a18030501020d05090c0a0605070204200304 71
    0x50440d40c100c46681040070309401c2401074008100245c1070400150840c08180952070f84000489801001561690004800d00f41c0c017070469494036a403001044007031074150180e08510008050ba50310050b100d40103940481605640d0380e09034180d1742c104c4001a8040c440140c4050004110342d10381d40d220001780039a01e40c0ea030b0300303000168408032603000c554443d400c211504050804004102c4204011079608400a00c01000100c51210311021454001c80c5496330070a0300559042ca040e20341c010084400301c0340070b8260003250302408900e050884400380c82250215207203c503054280b040301e6020308039400f8212821403405031240203030641900283c0c0c5003503501e4503071200500b10781000e01000b900003044107640c0500b070006a0700070300640a036001c00c2080104038995140407a0b912006a0015034100000310340da9090001c0e1607016241c11101c030074461107000b05c4400700d400c080506030704865480c0c0d00c19041046590030040031b0401c0318031345c180004507654035011010491006602541c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 844190998 1250 844189748 844189771
    0x80103111824040908030c09031608011b171605090415080106140a0e060112050405060f010501050a0212091908100b062b0f020406020a0201080901021e16020306 71
    0x942e02d08000e1280e107a0200450b00403414015203400040890050300c0e0840c160240d425164418480460b141c00c034405844101c1a1840c02c0005464406510022a0303c0074201044901c10409000b9501c00016540f681100c3c0012800034a4000314030b045081d000e0002d151061401b4003c2002030b055800382186244600340c04002040b07a040b09100b441c00420038035064207680d01c500e0000500307104640c4900e030f04080d00403001425580c8a10346020080042e0542001141000c0c100181c1d0761b8401c0300c07000c07030541d10b1600100301c0d50b00450603640c01e503549500a100d240c280000f40c0c403c0b50032030700041b50010009000e2140d40042c040111000e0181d1500411011042c4481141507a0b60301460b540596420040a80421281110101413451904940c9001031500344400000e0410611854100388085400301c2e4440d8007007035045449000366070314003c54a51a00301401c0b445034092103c005072211101256802010000d011540500d000c0c5107680304181c4c000c2424a28101c0300700801a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 844192248 1250 844190998 844191031
    0x5040b12010c0512090d050403031218060603120905030c010e1f081b0f0f0a021e0d11160311031006033002070302130207060f06061e0801031118 64
    0x2c43c11104e0183e104421030000c104800349150050a60b11903800050200040c401017100c04205603080708401c4441c1c1409140341c0e8030030342000002400180400c41e0305040251400c4221881122050265403004014160310300702840152000600001074039046841d051201c011200071840f14100d450840d101c4540c00d1500842031510a00300041c459103c6100b44500da09481c0c07120142c8800c4d800c11407206640d1440c100c026417411404d0744030204020089403401c549460301041c40c40505480352110111030240482d59074850120300149100d0012b4014200045a07400b20b40300310050000d81070701d071240f141c80010815140e00ba001a29041c01042419a21800c5200842d25100c43c80c001603200d100e200c00001d40759a128030000c2e2240f544185986904052981100d41c0564002c80c200b00008060000e48041d182512410300803814698071240d445150145003400008160b4a441460782140e98581a00c07480f0140f042c0c1121181c249801d9000c1c0000800d40105000340017200380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 844193498 1250 844192248 844192267
    0x70503030f010602150406050c0903030310030c0503120d1814010c0f170708090c04020c0a022404060c030e0402030a09021002071508092404031103030601050405040b12010c05 77
    0x703074941a0f10000444d4803101c2025410100d100c40283c01503400746001c02c49849840c4c40c0f04450050b0318107140c1c1400000b00b8040e0611524400c8e404581c4100500c2c9406585c074001c03d5100c5080c410b101c40024000c01402140c5134150b170054840201c0c0491140080f04943c070781911004155920400e640c0d914070200350718a4024459015448980c074040c01d070b0212038881d40c4040c04007d009901840701180200b030f03500030140018010200064800c5445185903140540c2e1448200816406003044041101004289510a540304003400c4070b403610f003034036240c02280c44c518518000e408112041d0b6001308e01e60346900086000c3c04040e100070500500320700400c034460310181260015944180010001d04a12030071080c0f0003042d40c2480c0d845070355144141414803a600040c000b11003110654071901e05160340d001802070b8080c2d624804001c1d5201c8a450752403000340ea006d8082141440101718031301d01504840039500c40600211214101480040e095440183c6a20089540401c04210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 844194748 1250 844193498 844193521
    0x408010b040915050a0603120c0b0a09030203160c0302060301030c030203240112030c05012a03360203011d0c090402180c070b15040b090f060108130807050303 70
    0x5050204072001c001d0000c041c3e5540ca9126140000060026114000a0b503101d14030740c0103000035904040d0290151035a0080103050040b1400210307141d264502c0441d01035a40c0d031180c1480682d040e0021480d00881c1c12505001c603146000c202c0d45000d01d60b80110040e2103000265008500c194844c0d0001c1e81580304160a181009031980c40c03580100051101c4003d40e01051030440b4402c0c17448484048060070200c8249850303084c0034103a0f42c00c10400c200c0310810301c5418806d41442c100c402c08030349100c5400b141524070910204143d048580b9141a03115806482040684000d5140301c0550003158082401d6412000c3d8039100581a040a05d01040040c00022301844080300c0c480c046260a5001030a03d45000803c1b4070280307200c0c4001b405c0f190300001181c05c1d11343c1005010900c0e18007080c0e2020130001085086000b50705000040d40d560030035040b01f40c001d40000036844240d0b507507100112500744c270007400d000c100c8840a00007400320700c1d90301c002c040150080003e543d8074541b440035840c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 844195998 1250 844194748 844194761
    0x110723040c0302030f061002010b090408030f10030f121b030809011107210521070e061c0504020102011104060801050406210303020c0c04060806091204050105070201030f140c040801 80
    0x70141401003040041c42c40d0100c403481d502c02001c8880100c02d102100c4120b0060004016054000c5040070501040c0840d040145204140b480c9001007a5030b100d98038404042001d120041041e540c101c1c518000a000d0f190300344641c1400c0c6050b20b0000c1c0b0200200c02510107128082d00800d040c0da00344801d1031020700030b0342c0c80c807250580424503205103641c034400000c0714040120740c14440b25840f44809840380742111004000045560b901c00341d43e01c50400e0f070541c03c2d5880000304080703c2042c1d620303040000039035210651141340c00c201c111880c4414400703410020001c0b4115540d40c0142e0402180c144060800b800c03179640c402400d9810701d03045c042182ca0300e03080f404284680400103100410382c003503124452a890700d809a25064076140003842c00c0f00910381c039544107003810700200e07070380301e00158503441081d13034078229500c816030250b00281c036209a00503680000d00402100c009940070b0f07081540d40b005100c500264800c616851002c4401c81a02c40390400240098200b207640000d010302c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 844197248 1250 844195998 844196021
    0x3030f02100b15030a062c0f040209040303050916090b0a0f080303070507060609051815160e01050c0102030a06060215091504240227090711072304 65
    0x4110030b9140c80c0009041c0b01d9410042802000c0000014444180da40c00c503070010300c0907032603800080703150210b24214151403d0f004500d5018150004400c4600c64450500640c0c015140d0015a105c0e1780b030813009040002c0400f6228407403220404101e002d5483c01c0401070103003071030018480076078800300030301d40303500e0390104a104d0030070142030100031004401c81303402c0f62850030055030318403042c68600302500c0d4a901c403040280c90501003141c00082c00300700820b82081c80054a00034490810f64098a500c1980c1d1038400c03503030071000300d48080c1c01090300704841c6d0702c14100746087c8280541a6400d9900442e1030b50320b2147c4030901040941e404005101c0c0d010300005000302d4900c2e295078401e42d1800890902c800207180c5001003400d1241d910402d1780503010114180c0c803e1102a619400654000c000508141d2106a0300004000c0440c00c880ca0150005080440a07100c581d8202c4222000030100c030101e000d801000203013018429421002d1101c0746030440764050120040008441805420 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 844198498 1250 844197248 844197251
    0x1051b031914030a020c0709230a09050606101125050a0e07080604110d0b0a05060406140304020604080609070503070f060e010c05010b0a0605120901060305030d05040f0c03030f0210 80
    0x308142c011000041c0c0c3d40c07001c1d100800617240c029141100c1d19100855105811861038102a60914124105000810642c4010400070340c1ca4a5580808445200c0000b42841d002200424a240ba0402002c403900c1c41900d0580c00764581241a41d090ac601d0310340c0800c504003201074180302d900008043c2c0c801090308940d06286607151044810141c00d00070f00d000c0030001a100055416075469004403403005c0b030054101d803140c082d0707099640201700354034a140c0b00d05004207000805103400c5040303805481550750341d4080308918000148c995000508220380c00a014080498100c40820005102c0c062040041441602e08030070f060038480075402903035130030084002c00d101c0c0f2508100307a59000c00c0c01b0320340048160450304140e401044101c1c02c042e4401c0a2143c0000c030320f90300c2030250540461010317000b0f8175610740b0450b4900b02d40e020b00c001420f0b50000e0080c910041c01030360100394020f000c2e0310384a402000d5a0f03101d0845c2d42e00b0b42c2049020804500c0c0b480392881d410042ca540c1540080340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 844199748 1250 844198498 844198517
    0x1e06032505031e06011502030f0a0f02100b0f06090607021503010608060901050f0607060f0606090302040b0d0302150408070f1211161a0c011104030201080c160f0201051b0319 77
    0x2083c0761030311014007a81d0300307444003030b0071900c0f07082d10800803680031802c1e0b03054082c1ca5a086a40007000d04204501300c0006100d0a0003200488400b480341c11800c1c40014014413030391004105116007500441d828543c040001d004100250f101e00e20711604c800c4c28000f400d42e03258100040509041c1c00a00b881e400707032030359800602154a0b1a094090305003400c4840903214803062410782e000d00140150010002d00700340700010095000681d24094901c07c40301800501846400c1c01441c414000d00070340140c0c0110044c50320380201081c260f401034090080b40b032501580b52078481c80c03071000360412500e20304201e4003561000c0e0700c4003109428240b16006004034a01c1411182648141802000c40a00c00000041081c440400498198020040007402000d10f280c0714034840c0d8003d403109a01044404000401d011801e1b021281085501e007200380949885031035000b009182c2070400c906000e0100040348440d20f015060b002d581c03421000855607001c405c1d25403681c00700d101c003000061002400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 844200998 1250 844199748 844199803
    0xa020d1d06090411070f060615021606050f1207050706050108060420060403020418060509121c0204081e0f030906340b09151e0603250503 61
    0x21030300061412940820f01072622503144c09a1710540c103000381208581e084502c10070402d9000074084a039103603400c207181c0007201426616418000403103241c0510842d0b040c00100d0140d80a0b050024126903c1800c142c82c0210321500c034203060341c8220104a01055038803c000300c03030103141d000d00f80000244c4080d0a01c0c0d592600f0181c61265509603000a1208090054841c0700980e0019030700104140000003104620681c86298000107481580c1040005066240c001030289074030340b4450700c540d01c0c03e5504021070200424600c4d15003902c0c0c0d001c00c13001866a00c20005030600561404000c1d00c3c00c0d05080007545044801e0000c0246a0014021001290380745029621403209001e40d40d071b07241c0c40f11341184ea001c5583d40495091044042c01107424040c14043e0304e03106490b5030044402051603c902401d5900c0103c890041d903c04025400282d83c04902440c0c2d0080d0f406400ca4080007501340400744545040b400ea4034194601580400ca149810490f00d00030200d004400e642144111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 844202248 1250 844200998 844201009
    0x1018091401050a14040507050d062c012715060e01020f1b01050913020307020d020c04051501032f1305060a0e09130f030305070f2c030c0301020a020d1d 67
    0xf460241710740c3c2d80f0030000700d24178003603000c60380105540710301045825180e00102e404201d400301010000310418181101d81d003560900c0d0f5050325803080c9050406880c2c0400c24131031403540346c0140445621031800e00290700045240401420b510340b10b0745841c45054000a1801d10080740d50700040d0711848003030b00400d001690343c03072048100f0319000c1d503035038000000b1800b403007503003c0480c003000d10010070004216804a10200e120f14180d09658200d0411000c1006840d8140c800464051032101c0252140d030082d0700039072140c20800e08031069906001c555000100912040d04080200010624044441044100081e01049079018100b401c034080040458900d040702070300034190000841c450907200048280131a0340720444002c1400c1c0346c900100500400c0c0e521502203400000d41010b21400380030180d400b03d2508a038800300301c0c500f105c00c005040300c0000300c9400d0300502001d02001e44080c00200b014070300b0f5400070180c988041134001c01212606d0309980141081e03007070301e510b41d40c1c51 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 844203498 1250 844202248 844202279
    0x19030809060703051e09090901020c101d1c171006030926090405090a051b1c0b010311030f0a03080717040b01050a1a091018091401050a 60
    0x180c030a070b42c603007240c0c0c0350a03140f80c810311280c43e600301c1c00312902140c40602d41008007190b010a988105458585103145402d0340903071b05080f5090b40150840d900e54400395840b500352804480314099050714007103030003420864000040b40034056144060b802591f00401030035400032640e8400140c83c50b200c4e000070341200aa0252004041c0c0300d0b80b540c070a00c0052a0013468203c0400e5011101e142d0417500e2158590095943c280101c0c1001d0008040803004500815565000400f4195000c100b0f02c080302120100c01c2072583c4021101d4100000d14251340041a01503c07841040826504500781030011008080d42c1501c02d602034001c0021540b070105143c0606a454102806281c60300c24085c0d90001d0320761001041c103800042004140079185403507a04940c405e568001c9000e46801c0c2d615094001252403401248003041404003d040c1140c00889100c01c9103070004034518292285801500c0c0c5602814080b80c03213a81454041d4250b10313616004240c11101a03680e01d1428030501c070800c18 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 844204748 1250 844203498 844203517
    0x2a030509070303080112020109441038040e0703051f140405100510320411031602070e15010c081b06010b0304050601031412031302190308 61
    0x441c400e11b0403c6902421540f009407003090015082160320903200c14118036a0540c40c031200000c10000c000e540c2c020789183c0441030b20179000c1c140e410702c40038036480a02203142000d0385451200c1708441000c3c0c07a030b10900105021140b1900401c40003102000180d0742804017813003994001c240104005a00000c603680c20f40d044032504860030600d42d0703840c1d005182c011006c2c2641d0200d10100010810041038103e0950116003040001c1c0d2100b000301c0b50310324031a000700380d0085050701000201040c0c000a03001100c40800d100d4005419a00209042d602e608660060a410210a0002401a44d80e42c913000307280c1131004000d5a8a0202c0000304035030b010b08074440180c000d081a4140b6480341c28245c4e201900465901c0c0e90301d2000100324958034101501980e40e0040c1000452500000001c41e0300480d00301c40108403a90030750300c40c0f00303030f01c8400d01340d120041c85800d0b1620401d012000295104400007a1044030061190040c080c102c002e02140042e21f120400c8107100046022041e12141c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 844205998 1250 844204748 844204769
    0x10b010f0807051303030c0b0a0c2c030109031119050312061809060109060902090d0201030221130b0108010524060f0d0506030c011b080a032a0305090703030801 71
    0x45030b441c82600c480c4103002c0a4031000c0d00d403641c084180740e0010401003d003885104000d580d940c444540c602102c1c1081d64120014245c201c100c0000c402c104000c1d81001030b04169204000800d1000900f120b258000840c08501c1c52102c0c40782c1c0c44070521160002c48800030004c0d407041e083d6501c082c0c9922507500a1944801c0708004103500c2e848000c0480008205002021500e0401d215040e60381e003024070a02140e24200103000c50452880d009542e4050b40c080c1c5078500441642d070064000c0d400041d40300c20f030024150101c40480300c2003280d46010704240345004c07401c6d40b49420f00031005141604000d029a0400f42800119000d00941c940e1000c0441c1d222800240881d00143d15407062501c1250f200402180c814410030040d44502d000c1c1c00c003103080307a441c1c6110320019107a5200e02c070390303128400d100c100340c81c004504064002c000f038a18500d00002c43c070800c045c00b2020f21a07803403007021251035111440c0c03114076018880e05402c540b0310401040718518550b00100780d01c105000f9100c026 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 844207248 1250 844205998 844206001
    0x105220f0c020f0601062c03101d07030c151e030606020715200c030a06060e0f040f110a150507061406300303090d080601180605160c09021308010b010f08 68
    0x101e04292078007200080050949d0000c040c00ca40302d00243c82102c009030134465410f804000c105900050800c1100e42c03103c80000000d1501c0d280b41c041c3da4566000b00140507501c1c0344a60820003d40405581c11025200020350704e040c075000034a8030070300e90003c0c060008030003404441d445d04501401c801054075100003601442d230706d80c42c5007845030140d20290548581d13100e4100b0001d840c2c000c00b040e2900860007a4180c0d680c66403100c0983c000780c070090580265440080c0210b030b4042031030390410304040c21081c0402d690304211442d94042124850003d8030105a000400415018003440303006081c1004049080c280001685014044012003410300300c110046000301c030f80c0d92259205400314003a2501c916104400a880340f103c4012400007a5802c00054002d40c000c41c008038024044911080e00356040000c2610594030810158005200b1001134100060301c400360070f406408540000740c1c507406c1840100420020503044900b459040085081003039038000581c20b5005454031340303c03056 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 844208498 1250 844207248 844207307
    0x1061d0a0216120c060c0e0301050903090f0d0f02090c1801020a051c1403040b0405120c0303060409030e09150f04020702030c090c120c250302060105220f0c020f060106 74
    0xd13490000d400800040c100303441030100035000311504100e40402c0d0000d01c08c4c0c0d83c030211241d44078410b50311160b500007a0010b01606c01d00305080f020000030320400302d0301022401c1c2c1c2c000404040d4210380d02021a5000100c035410084003450400003400d00303000404906005903502c41c0c540740507d551020900070b1400c4014010321035016021641840142280e60b8280f81c148105003c2d000c642c00d40d03141c031130302d080801410120403c0320f6001080c0000745080da110401000064140303024150304020304008065000d60310000c0a60041076841010616030303102005004048002202d00352140b44180200741c05624041140e00700d000007124040701503a6881c0b04080107020b0b000901c200d41906000304408075203100c005100c1c0c01c10500300183e2079860070070098200c04002c040180180c01c0032004001c1c90801c008402124240030001c004182e0070798940ca42150240c680604501c1d8440f1306660320035406000764282d0500761000340005606050001d040842045450300715200a940c4603003c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 844209748 1250 844208498 844208507
    0x5120d0209120c01020114040305070b0a2a110d02070b0313140607140c0d1409060a0801051014120c16030804021810061101090501061d0a021612 64
    0x3407800004000990307900030031444a5540c205684030318090341c6060005043c0f9051071407294441c943c0342d520079180030f003a650703140d1026202411422445407141c142c0c6204040321001d902a42c0025001e603944080c4145000340780e984070101091b4250400707881c2c1060142d000c0b60760b10903140e922000560b00d071107108031880041e48010001e07200c02103038003c0000c0b030b9501080890007074101d03940d00d0014601e00c210300d405034403c0404403001e5501c8451540c1d1241e0103201c00903103410148000314103111040c8041482540107800c580c00088a45006002e146440728100c3e0b101035071803801840c1181140200c03c5607200f01c40354080080781384400a00a1208641200c907101d440501350038000105140283c519902540c00b20f110710503580d803034108421040c083d14441c0e04410b000c0003100d0310380203003522032031402e880214240d5202e048000210b6030901408004106110181199803280609243c1a0b07101a0911410900420595603500700445940e124071b50010300f408040c8610704400d45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 844210998 1250 844209748 844209757
    0x2072d06150807120314041202040e1e0703050105130b040f0f061b0f11060106030f0b030f0703031b0c050f03030c0d120605030303041502091801080a020a060c05120d02 74
    0x202e0700e100d2884041a85070b402d100b028802d9100b074a4640124030718081501480c000c40c051401c03c0c00480c5c1802e4058901600b1201410001d00c013610010707910b41d424000700445001506890380c0c0084001c004214003481166031002002c51040000e10309540c60003040017001d4005010110066905020300c055a02503117415a4081020842104070901c009007240e0246a440c01185050b04100750003405048030034611081a000fa0510760309040c0c0580013480d41d5040e410501f43d075a940209151010420341c090111060000c05560b491490005e040c20501c600f00181031950403283c2001501c0100e814081d00e208a402e02c000859140110b440c6003d401c0c2c0c441c1c581c0c81900b2080006540001416607155101041400b41c10748507814103071740b44000e032402441c0d0541c1c2c0201e000e540184c3e90240550410040400c0d11241d044045400c60400c20380142c00c05801414182c1c0461070001103201c024803207810414104035007600c0e0a621800402c24002e0660340000341030841c80110b60458 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 844212248 1250 844210998 844211009
    0x903020709050403230a210e010e0f0706180501120b100f1e021c03150806010501090e0c03060915100203092119111302072d0615 57
    0x100268541030070010028074070102400390303404d06a1a1741101209220844180d000c0540311f250714180070703418261503000100c840204071503440c10a11030140003809801d105506807802003049403d103414560901c0c5044e4018028440008100605940301a1508040744c9090034203c0313041d850040000081d00880540c80c0c0d01c458a035140704030480d0000c008071b82500340d940d10001881c900d0550814a10484404032300941c0c00741c11501c0403100c007400080c0c800d02c02031034040b850700c0100d11280000901600000d031603400c500c005020782e59000c00c0f444000c03d40140104070074140407848040318803010309031a0145011900040205241c29600880302102600720307024000d80d20002034072500407200c50b074465520004001d0000394500740f00000075180501901203508040910301100415600480345502c409100c032915945040c2901c2d80b22002100240e92030f98285401c0c0d44072007035400d81368410303513101c1c01c08000c090340855110500740d4000c0d40040e003036503c0100210300558a5112 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 844213498 1250 844212248 844212251
    0x601031104090504030306140109030627030822120e0d050304080f0c12061303020a0b0c0304030e100801060513170f0d02010903050f030c1c0b1002150103060903020709 74
    0x798420466108504c44c03800307541c0400169803510126160010302025090028072414024008240b80c0c3d40981c90340c2a0003440310056107841108508109240c1400360003190515003040508520f000c11206248440042101e104060b0b40c0c03202c081c07081460501c0c0c20068031500110140e22442c0585100b9038000044989591b0364001c4180d0b81c8a016a40507001d01400e10000b4907810100400b01c01c80441c0c101070000342c3d54182c0f6074000786030070780c4c4c01350118230030800c2500c081501804010f0145800c2c480031039680c9081e0502520100034010454054810f0b920902040c65020618505454161030210344d5090007426170703524407103560410f10300c142c20500c080031098000100900040b1898040d80d8161a50010076801c90782404000ba005c24000c00c0701c050700c0a00040110b500c100a047e420341849840580c0c00214600c01098040305581d5144400c4a85003421452041c4c2c0050310082c01044030201114000003c10f01c00280081d480703051220805000780b15100c06410072240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 844214748 1250 844213498 844213507
    0x30b03031c0c030b0f1c1502040f031e05060612010902060309070609120c05010e0a0e04032d09150c02030604030306051c02060307082206021c09021806010311 70
    0x41080200b030414500c8000c245030412a400e130703081c80504242e121100801d902040a00785c1c02e040d050700d500c850103c80b0103002c884185400c4005101600c050409815156921403e51900d454000e410040041c40c6c0104905010005840000c5260f8040e2065903615911b88030001224054a03000030300941c070030008000c20040300c20016100040301c1d070541d103003c4010355440c580803501c4400358001c0c1415038410424030095004051060203038402074100810b29541303840400c001c00007620114000360f5400744030100001124aa03015008406503903642001512001034000f220038818610381414041e0000c02c2d0301e001e48110f103240368000e41a00c040b0f10302440c008000701120302911b442280c80146600e4041d40803507a4041413039010f4a141e02e90341310488107840c4090002c01d9030000c460303203d6281c00944c11581a990000e0310982c005600c903248141c0b0401403a405074031402c44d1914008000015a807030f254503078003103101e4100400c400d403228001280a08403140041400a10000703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 844215998 1250 844214748 844214797
    0xe0109180b130c050414010e060309030c0d110a0219150503180109020604030b0414010f0209090a0504031718031804140408030109020a02030d090c03031d060a030b0303 74
    0x40288120315411609450240460b08500c0c0440c0c81910302c04001aa0600003440513210000003080040014140300c80001d42440010780d40343e0045448292a0b00701240c220f441c403c040024542c2080c490509201c20140302d0051a551080b01001910504414580c8400011080848000f801c44840c0d0b080042c03048644c0a002c0d64001e45410400309850104001c2c005410710400c0c0f42640d004107a5850a803440d1120807646102400943c3c032a0103140040ca03440c0030034450b00c5180031a401015844100200030400411300040c10000442d06041c02c10000a50000e0100c4005c08000b0382102591034980c030141d580300150b105210544000541a4410b142c11904110480c80856080c0007054400e601d441c0303041310a403401400043c0500c014082092540c020b010180603c1c411203040130201224082940c0741e85405407404d00c8160340c140103040d8001d250010080c3c1c1c1428048201c81c044c00071685504c14001204209595044040200e035801d10480d0030000d1081900c3c1c0f2160300c81da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 844217248 1250 844215998 844216001
    0x1401030b01051003051e070e0415090623042a0203090a0b131403031c05010e090f0a02011808060901140709180221130c23010e010918 59
    0x28011148a043d00155844015201c0d0044034400c1008401c00010007810a0714804550300240003141030094280401d4007030340b85d51095080c25a400301e4444505860300e1a18800c68005410409101c000d03907100700c000261580c0102c0001c0b200b40d400141441484210380540491040614a500300540080da461035001001d040c1a0004071050400a5030343e64004000c0d00c03501401e903030b2065040c81c040000c3c203042410806002405401e891402d01c2e502400b0f64881c0080883c801503d0303880d001488100240752200342c0c440c0425000b00307110500c0c016041d50300c5080d800c0c0241080360306d40a0441154050900e0b40c02041d0342812900c8da07060810750355004e001104411f00e000e014640004c3e40151250034070800700c41d951092043c0c00d41194080c480a91301218840428014a00f41c411485241d031403001e01c29524840044070304c40301840c145000e800d690344070310118043c1920420b2510071011855541d10001d00701454040341c4000180d807460402d038403c2c0131070540380d540e40081c0100c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 844218498 1250 844217248 844217251
    0x190504090303151a0f3702100b0f10021e06010311040c121802040518060601030c050702270c120705070825020402130302120328030209061c0f050405100f1401030b 72
    0x2142c0230381c0e41d0502c1d02c1a00720105c62440306480d5101e4030200c610811800e2a0f140888500020f1040d1646a0120032802800d44482d0090155560003c4010001c0c0f10300700ca0f1400d1488070444d82400708551601c4014061140742481c9120641d0b00c013420200400c040060101651380a8414006854048039246078556240c1d8100418084c00e00000d000c0d620911854010300516150b55080c10001c0c0c084c04514400300c00d1000c917141d80c0442e450481c8181c0c01c02d1511403810540d1440c2d44032810303c41d003454108007816036411700009105490016842d0783c19604005200041d0003802c6000000c154100686198045d401910004a0804e000c84460200c0305a9000780c030100c0c965107010440ca5924071801600001e09000201d00d407480e00c9055042c0310524045103030160821802600103091039000d0f090320841c19190004038000070080e4010046a103228000c10002c0d4035180d20b40075114078038204007411b102d44c0c80c0816003041c2c48650051402c100e54070240401b568503071802a04a003030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 844219748 1250 844218498 844218607
    0x19120c09180203060a1e0e0327010e040b0d060f0b03011107050a03110f03033d0b03060a0f0e0402011e020c190504090303151a0f 57
    0x4150601066203051040003000550103802041c655803886880d00080c020080301103003c0c4020481e291620381b943c0140c0c1442044000035694a0b03616030b4040440880c2948541a00c0e013044c28000c0c22a030308442e411407d06c20684003c80c86014100015140c0c1c00b90340c0c40180a189801034103170f4034010f00e40c00300401c240254001c0203440741c4103000c48400c1c003445d08018141da0060303040d10700081c451002ca9106241d40b0302180d01441c43d0711400b505680048410409140c07000d0000352911107080c80450391407094a41003c185106030003c0810604940940c802092001010810175144d940401008019040000318030350b0301d41d078000303a4816064405038000f0355503c0034282e481d01c05440002514615030014560310084030b00f80004103000091520994500100001e05616180298900544240e40009407a200c06d820205001d5498100c0062040a01007055802061000308c0300681a02500306441c0e00c02400d80005203440d407418121403071000b07400c02486040e4030504444101c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 844220998 1250 844219748 844219751
    0x181c0306060c050c040f0212160306090501140904050c1507120e22020906070f1703101806210606060c0c050402091f090305150106050919120c09 64
    0x50340c07100c00300c0d0545401ca0029156421683c402c2005107010384c81400d10740f0a070b65016007031080a400800308100102c0c0c501100140b1801c141010350f51511510700030781002c40080201e941801d402003050442001c049025410b060003050900000304040c100940c0010140e40c01007151408039a260b03005120304403000c4030481602c03103545000b2140c6d0505400090705012606404d123041034a6404c406240d1a50694200000201e60b10740600401c209802504015444030341440c0100406000b401d0070b0071200c0b403c0c814410340c0d040b4007001d90100c41c900002490060380725010400100132643c062030ba0403205082e4502074030070100d410742819002c0c0108201c0a030356484203407050004d11034010300f05110741c070091000e407030264040c2c45440130281540441d101c1c190030f50303140b84017800090030100c0c0030b582e402c00170450300304003510300482c003240c80180951401c007016200740202c0d240c040c82450581c0d02921400c840940d10030052a0760076400c06101414102020540b819014402405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 844222248 1250 844220998 844221011
    0x16050610030203070b12070f0e0a120b0a06050603060d020433060306031e083c07020a060c0f060f0b010324030308100b0d0c020c190e181c03 62
    0x1002c818055825100111006c4281b69442100071502d001440c4004414480c10411500c900c2d26802c40003030103403103c102000e15542903801d01c50000c00d002403070000001d050182c140080d031916016642c0100c0144d031481040c800e20b200007405442d840d0443c0600c408800e400f842c2e07c11200c8002c100d610040d0103440c525984542048050390f48902000e04108170300c161060254940d03281460059005586040c2008080c42e4410f0036601c807036200d5a040c0381036034001200304028038000d15a1810006d40a460721510f0b50100d403243e101440f0ba8003c4c0068802c82c00188803c07203e1a9220a03408102004095003264155008010b24424207000901c3c10650708245d030024000b459411032080700b00320742c03185907550803100c40a0040c41089500e40c0b03c40d00060040b401409440010003209000c201d2031641c4070001c0c0750402ca1104148640181003039001141c14101080303041e10071491210030f05030769940e030f402901211840f40a85900c035003041d90143c00e41c101103089100c8600c5d0b400b40f114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 844223498 1250 844222248 844222259
    0xc09060307060918060b0a031b0e0114160b0c120117060a0507090b04060809120304081c0216110109060203210a06090603030f0809120904021605061003020307 70
    0x44010900030322020a00000003480340c2542070044e01e054201001020032000d4540c2c201c101c440c0c00600c24080420b4948220080500010010b1507400665141401c041079102c0d00080c010980c410401309a914000f96454403030044481c004076481d0000c1000384942002a11030308283d01c122819010507904000110780107240e014910000810700e002401241c494180c1c41d4018070001e4003031003d1281074400020442c400001a10040a45843e4910a4903149580d5801c151203100c0c07000c5081410401c01000407108400d0b66080d00d0600ea420f0141c18040c0740b400001d124200340000208000c0c0f4103a01080000c00e03140000759401c0c0c2e036070740501d690385409a80d68003851745612030720740d540c89211792002a407601180e8001043c03100410f02a6452001c0b50440e2003d40013503000848250b004030700607410200c0d25410040540c024258200c01c03658413031447c00780d860070314425500010304181410078003036140c3c8160740110503503445041c03549100003c186184001c0340240140500020f1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 844224748 1250 844223498 844223503
    0x5070515010e070806010e19030b090a020604060f0c06050a060305010e0f1b06120f0108070b07020a0e0705211819110a09020a050301061b050a0206030c1204050c090603 74
    0x40700d40c05440308515032203d21040d81c50b0b0f24002c0442d410005500c041a0540c0e6030b0004200c441c9003410b850445241c2582132034108000000d00c15032640e400748450030300580781d2000302c1d03084401d1840c000210141018003114950080007018055504000500007500f44c1940140100c2e80304000030094507400c0c0b0001d6441d95541c8650350f03000d402004500e5801003800102c803001480c01060941b0388581c070a102200a0010303200b0512a010080050281d90750401228000d00b08204545083c007038036600040f0700c01c3d818000c00000c0400d600203c1c0c61072b070056094502541c0c42c141c4944160714024162607019000b161400034082c1241e500c41c90303040000c900b041344204501c2c141041d03082c00303841780100d40201c40e4002ea0009840300c0f0000f4101c085202400944442e075807a69603d51400c0c000418000100291001154180070f03445d00042c000582c0c2c1e04555416501c86071a40d50b503046c90040b900440c410303244118044c1c800c200c1040030100e450341d4003a200f10740c055a2525008203140d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 844225998 1250 844224748 844224751
    0xc0f0305060a090c0c05031204031404081f02040b07030e0114040b0304060902120a292502030408330412120603120806040617120f040e01030305070515 67
    0x103400c5100a80c1c01d01400f49180c001d40d500520b98101004041116960907240da4090010030802d040d4000c1031208046d805012031105000341c280c030505260520107110380721400c1d40703072801280b034082010800499840e0152402002101085501d41880c0d0a000e000104003440080c0020100d508241035044444184c4040d21120300c07c00741150b4547d9511401400343c00c105a038031504040383c0c0840040200100c0380510310602a410700c540701c403140c200c03c200c0303201c82a4010307030007030030400c450355036100c60321104071000d8141907503800204007050781544201e400109080c05004418180d403040d0311541c503d2111170b402c004003c21090440e1481c151402d54008046d104e4954044501c0341c400d40c090820f40a41000000d003540c1d4aa5590018075002c009803008a941c0307004008580c80d183c8a880c0050200d420014002003050381100d40301c42d110165039503464808103600004103905021b07100607201e4140c28919550f1a0b040c00740c150b0700000c4040b9500e102d0000c0484c04030711003083d0b15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 844227248 1250 844225998 844226011
    0x309070302120c0d140c01020114150d150b03060108030f0301062a030305070f0e030712030507050d030203010f0b13060806041517010c031506050319050106030c0f0305 74
    0x2002014215030030407118408101c51400b60f44100008011140d40d803020400006110300b00002d00091148007280c00d141c2484240d90669140120306031488043c000c0255100e1200e03004104040390f604001820445425405040c3e12880050400e0700070303040c5d00100e04403200310225441680d88408042d41c81c400c1d001012401d1380148010040c00d07020710640c0c06c03e0300e40800c03039811503d00001c0760340c092061101c042c0d0000e03498000380503541d038000e4295403080405240c0070f80e20011080100342d40700ca1134410a07080c4011319001c001410301c1041500c1c12198008182e840007203510308001d010390805e0180e2500c0c41041e050002d030fa9920301c41101c45024500d102c1c108074074a0090261100c400082809412036140d059181c0c13100011003140000d1312034460040300344010104610f0844a54580000c149480e21325400403030a600102c0b80c089441071b1400941e01e0b03850054401c1400301c602e030314507669414900007044441d0541c200724402103041d030760725850400c3d011045060710380c1664030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 844228498 1250 844227248 844227253
    0x306190b070602090303070f050106030b18060106050f091f02070b07030e06030606071e031202040506040e2a04092703030929040203010b06070218042103051504020309 74
    0x7500c00202540c0250441d00750040c140e0b41030041c583c45001b0070004440040b21180d540e00f80034020442801d034440d0300848a040c07051400c8103042c0c1280d03521b4006000e11414403002103a000d04040d5540c0c1101e4020b4030180a80e80100b522001c000101c0100c90850000350040c0070780890040c42c5102030383c20f42c1c0d401d0b0361000244003200c41441070030781c0040c01c01a0424020001000464001011038034040c54a090004d0a6010b9081c01002d403048030415140407030040100b08001c1d5030300c0080d203054401d564100005a00c45da01030317002180540145080603149011005035030a242c1000d4011109120011b100f2141c1ca00b001c21202c0460352842d01c04290303180510408680709500c1000010304c074454694a003210340d4840068042d4201901411941200420046040c00e0144110303615050741c0d4141010324641c002000521034100c0c00460f100c010700024248080800340450760a4001c0704141e81c01c008d02c000601520003203920400d1400c12074811112402c05d07108981c49040504003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 844229748 1250 844228498 844228507
    0x4050312100b0415080a0e150c0c060103051c1e05031b1306090803030c031b0909010b0909060108190905210a0f0306060c11120609030306190b 63
    0x3400081080140401d00c01d020000404180542040c0041010b880c00302521030300b132902040300900952004001996990821b08084c0c4030307600c0003c08030081c000f00f8000759266038034100d01700b10318000d0f5200c48040348961000041400303004115655450b0341401549113101e0040d2017034138030407010484d802c2c1d044036040101d418a44994040d540040000803208007401401592a00a03042502d0400111190b250200a11a00015600018040f07603018504510b0501052512030100070210406800d140031850740c1041c0041c11120a0300005003c45840d584482c1854581c0c1c110314a403d0081c070b000030202d0120360142c070a05100b100380c1c41d0003001a1511408003c082c2066080031501ea100341d0b0300599200c0002002c010040580494058030b6803100ba000801510b02d20001d136051509c2c0400c1407052035404a1a0111140c10140024030f960f143c40100b01ea82c00740700d441d4130f010b0044005100c03141c036011004600501c0200d8111903016891000340c09088018410b00003010310421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 844230998 1250 844229748 844229767
    0x3020607030e12160f09060e0a0b03030c0d020303070806030102181509040518010507051206010e0a080a0b0f06010905010e13090c090219030207031d1507051c0305040503 75
    0x12001200c004000c0c009054103c074607003c91380340030503034001c00035403c0c1c40c083d0900181410061100c0213100e8810240040f0745044040801040e020b0301c0b5028054591000303000c41c0d1401c000f111020100e04d0101e42c641500300300003e48070340007581d80c500002d11060100d4078602d014007d842841c19118000d402e03c0c20004200982400c250254003007452052058a400ea034440c401e592060120300300b0300340e0320340ca0031100c0d500710b50008281100b40141440450315407065891078580c0502e0070700307140e0070146140002a4040a2035800300840340f19031058031080000c1d080c00c01d0301032070b64101145e036140c55080c011340743c1e40c5c1d030343c0900c40c0001d000003404000f600c2c2c0940e02e060350b01c2100400180554294940141400c0d9540110750030070f400056990b0386c20f0400603c80040c44c05481c0c1142414070340e54004016480c54601b1050030310382e0b070441841a035924981803d01c0300d8441c03843c6039100020326240344c030791101111a65481c22440074180c6458000d008191107140d01002840c83c0a0408 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 844232248 1250 844230998 844231007
    0x6190f060e070c11060705010e0f06010f0608091006061808010b06070f17071b1401050d1e05190b0402160f03120c05030108061602100b1504090b190302060703 70
    0x3c40c0c055070003a070a080409400c2d1980c0d0001c1031643e0044001250840c5650021480c101904800b0500c075800303640100071074100c00608800fa40c01d24a0105d005850301d00710746207004048100c81c1b0103940707090b100280306500112b80d640d40581c2c0c0740042e00e09a640e000128221080e078426640c025400304440000250b2501c50390710007600c10003502004808021034032045812501003107d80d11051807800310601807204100d0b00400c0e5101c034144074550320340c000a00c28041c0440401c1c0864440c0421a5840504a8024111005541d080025141c00c46012480c0540300c00c4405000346081d110805078100350007242d121144503c00d0b1013604500355a007400f9500d5041d41a000c11070002c4e10088141144d0084c0200c0300c41c0c9070303501600ca505080e045401c00c0c6003e0081c0b01e07020714014601c400280c0114022545062041000507001c0c50240031500340600c5880c1802c800c0c00004000c6a080c0c02e43c0c0c4455014081076420000500300036a1072020585d00780406580110b040c42854006480b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 844233498 1250 844232248 844232267
    0x60605030703110f0316080906011a0703032a11010506030c100c0c14120a21091d07021e21070f0f122d02070806190f060e07 55
    0x203203081884e0000c481100c802a800c01e41c1ca01840380d44e009410903001d50b1086040d9000908107002d030020b54034200300c0e004440c003041810641380a010a0b000c09041c007a0380b00c4050012450f8483c100d804101d9403900f548008140d106010580070145402c400c003051295500c541005030041c000201c102d4104240380680150b10420400300c064950006000302020100030414102454030f0598448100a501c58442c1802e00f4941d100f007411001042480c00c400a400204140d04e00d0102403021040b50185641d4211200055903210b80d40d07501c003144810755120346596030a41c5d8004501841c0c4207081404031000074469404420155158000000310800d09020405403520780907550755520441c030403100c000d5800d01c0a000e01c5006011001d070a00d6000c0c0c20707502c1e02c4040a4480302c0302d90001420b825829a0700034405c0205c51405000b0032648010f0f101c120102c41140c43c1c00480c260741c583d61290b4a158803420002d8414201c0d68034060482030f5480d007010103a4943c0c400c4030445a4021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 844234748 1250 844233498 844233521
    0x6052707241d030123040201140a08070e040605040e030d050f0907090c0207050a08030c120f04181404050307060612080a0513150c0b060a0e240a091a04060605030703 73
    0x58901041700c1a40c06003212440b14a04100800c042d41707068000540034840c0001007a00d03942c010014083c4a41d44500507c0d0302035510301b030000c0032106c0c10700807400404550b048607812524100134101d0300a4008007031301034a5100101840540d456044625440b00265580d10b807542c040e020074040700781290490718030044640b0440309016a50000101c0724045540115140c0d0800100304994070410720500540c05910b0201d5807500c000030150000e44d1040d071190540c043d68404140d40881090740003400303140f200130030030b503114101130400303039142c0e40080e60860300c070392814800080c440c5203500c0340c410700750b044402c43c0c0c1000a075240a03241603100b6924504402041e200203d000da00008241580307038142c3e507840078410300780d1504620311800030b010b641c0b10b0810714000b003114181e00e40310fa40e4001d09102544401604100c10166070381d480e0b80b6040d6002400d4007000c954940c003607200089140c144900d07101070812000500c07003200c00301d00540b40014030800001350309a0090700880e20002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 844235998 1250 844234748 844234751
    0x7050c010f0c0801170607050901030f0908070305120114060a0e012003040807140a140d080705061014030706030c11160611030c0a06052707241d0301 66
    0x820090001c0c201d640321003900011070f411500610544d14402038281c50003003200e000704094140204083d01c14001d030720344c04e4105521040c2c1c003150b403201d030b401080c0c0056124010540f100b1103860040c00301d80101b44504944c001d00400010710800c0982070046640019150a00d420424031048491401880a480c1809110300415040e960301804070340344038480001840d2a141401a0a4240790451380420b80c81d0315002a00111a5a245402d908070340e01440342600f003135483d0010902d049203103000a8803102c4040b0b602000d201011659030b02c150580d000192180c0e4443e0f200b4040e029000b0703141c60b0954030040303040c00054040c1d440a1032a501a0a1115541c8011040342c0c2c901a121004081e01d00550300d401c03c04603070000100710030030100401950410811469a030b0703880d014403102600e80c5403100c000ca081e004c500c0140a04060f24500741070090381c403150001c0d540746120b10490560350403403000d0740e07214001e40014003142001075458005504182480000781b0040030525a41035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 844237248 1250 844235998 844236011
    0x110a03120311040e07120c030608030d02031015050d05330a0b070323030c0715090c0803070510020418020f0c0307051c080705032214010906150e07050c01 68
    0x200221030002c0d108800c590307070b584186c48400c121a4103582040503013030309140c100070381404202c0001c000c2c0c90603000c403d40011b80325500c5035003411101105912200a00300845060100ca9070710800621401032413503014096038a401d0031042c0d030040e000785544001d02c5003c8000f80c10301c041421108071401e001b00241015a12070b9801c1e8425170195600701d0100d52082c1c0350256503050541351a440c0d0020452030307819413815006070030303092040f014010032403c880c0440105020403540420391450b044544599640e8a80050341c2d0f50b544a654161518843d007440e052100b1820b00071207095980c4003400b250b05021480080000c1d4110340140c40c41da0009101c1d0701c03201320f82000030345640d9010b00e0081248880510100f05000e23941e0701c400c010401203104100213545c01c0411650491004044d058444075a03aa5401ca00c0c0d03ca080001d0884c88200503590450380d05401145a240c0512010407902c0c2e8000c3c1074a242000303900c209070004400000065115001d01c0c0038080c035460340400803606 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 844238498 1250 844237248 844237259
    0x70501180309170c0a050d150f150f0e1303111903110d0e2b0602070c08060c0301030b0403050706051825060810030609050d2a0b091006080307110a0312031104 70
    0x1d8410b410301004416942b000e0100c041401003400000803c91780a00b030b5006401c05400034918500100501010252025a0420103201c0c0d040440d10380031981c15505401c2c15105c850031408040d00040d400601c18401e8000d04a0780030600c05a01203841c0c44801061034504140001000000d00c030f403030030112000c1c50402c03642d080a85000e03043c2c4542c20060ba100102c1c5800407980445801c8049203038061410003004007105000c40c0d0569804c075036807851681e114501128248151b820040181e4205010300031040850b80b8607a001c1040034054a40101540000c1d80302c440000c80400d80d05107401c2d008000c81c501484c1403d400c452010444461191a40c45440a9954900c41114598008090705000f036501c43c007881003030742003400081402d84042294520b450343c2000060071944811001c9251a00204409410058682c1c824407820707507201c164503180d03040520300361644118140030000b135141201081041d03950002e4103000070480100200c0090013000d0309481303681000c0101092 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 844239748 1250 844238498 844238501
    0x100c0908060415180b130204020d020a2309030a12030207050d05090f040209030c010809101a10020d090e0c1c090201030605120a0602070501180309170c0a050d15 71
    0x861806020445028071116854104513040441c1151064620302c1501d00040c481340f1480b1781203440f044107601402c0060000800a00c00d000f4981c10031440000d140ca03407180c1090001c0c0201e616800580350100b00750b181c040329072249000c036540c5a0080d551000000d0700310106070f407412215203001030401982e59111031401c1c0030803000c00b02040d4041410342403440d20305502c0d062960103840550a06000d04046595107070a03403101410f001b4071600154804d50100f240300000d69410b4020f0240054603503208212441c121500d900400e04440104000350001600d1980d00c125a81ca0407842da2614132103c8802c174018000040c4000b082005803502d0740c0e0740705115010400b0307100c0007681c030f03003a0310002d001c41d29681d01841c001c40031034000e03603010400443c405260320780042c40585c0d00c1c020791030081d00400300c80344008000750091034443c2c01e066100c4c2080040d03489118031401c48460106040e0768070450340c1c0856510000ca07040900aa0501c09500d00b0420b2040c007242c0400c10b4600d07001c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 844240998 1250 844239748 844239751
    0x20f0f0d06080f060121020f0616170408210301030b1003151d01200d060302060d09050f0109020a03021012050702030d0b0109030b010501110a061a0f090603100c090806 74
    0xc240e008600500064039130302607141e40d51409003888480c60189502013800008914181c601c40c0c00c001c24040108500b031401200499840324000d4070300000d407104d0101c0c0350033038012001544140d558600e4a01c02a4400141c105400d0a949055a18603a5400d5035580001d04003a1441c2c004c60700000011100040d118a2052980000c10070aa001d410510007031071450614000368109400ca16521450401d40944e100c000e04030595142501c00f1b1200c0900800e0344000d411a6001a403080418100d92003041542c1c840d10541e03031080212600c8500360380c642480a9885400741d03800300010710b440a044289641c440c01c0c1080030b9919100100100d860849200016810001d40b80c1c0e07071132500780f040c10a00202400c00d10304d41b40c1543c07101101c2d05414082c0505205961a040c01c2d0949c0401000c030301958031100c2480a80100000681480042d4035028004c01c031880281016140c2015118810b007005001801c035200318101c0d000c0a1b01c41d07121030f00b06010300c504020030400414400035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 844242248 1250 844240998 844241023
    0x819052203060506060a120b03071d06090f01230d05030d0506030609120919080d090f0e011809032003120702010b030a17090604120b0703020f0f0d0608 67
    0x100e0100d45142446000d4800007000c00e80314440070400c01400d2a0000300d030718001103d03080b00003070500071940820f05d0103c0759000700a110111038100c0700072608004c04580300394821344a001894407074000d0300074481d2080c003a06c03084201d15841406c03885416100b081e003440004100d109002c00d2501d582e0b0444d40120502c0b0503c607162130800960341410032190741c06c0756050009010303a1a4520404c00300e0b000702d80e00c452080304c40601080325529618245400b8029500940307001c03694444001d8642e014a21400702034004403040003130b03021143c401240c1260940c8102e2031605c4003034100b440081054440440c107012051b4092004030541200c0411030000701801144c0e01c1c5116580540300c007034018501c07811607061a01d0b1120340e440114042003440c0d4006088414503003c80e01c00c0e41c1038040c2d00030300380e08450007081c0040c4188081c0b808011040c0107201500311525495811010b0f4460a841c0a104070000c0020308a2030008100410300712990540014000e511500d0301410400e072090503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 844243498 1250 844242248 844242307
    0x61401030b06010305220f02030309190e060402090d0f020d08040b07060e030307230408030d06140d021513080a031107060206060306161b0c0807060c081905 69
    0x400820307503014402c443e08002816002d504500f50b0940c180302146c0140d00040c0005600c0300200e0464908005840c040da1004000d240074a030440c84412020481d4403c24440c560108040341d11402c01c1e108850301d07a1000780105068004a8481c24903c460300c3c8001c907004050341c1d4a5078046400c10740500091f0105c0410180c2e02e00c0181850415030f415a611031211790810001c1c4514283c100b6004410510342c6180d041441d011110010b07100d003d544d00408090200040c01c2500348407070750200c0180d54079800a01c00c0341903040c00380140d00c403105600940140f54003181840005400c800b400d140c2d5004590000950b85032030005041c55160700c4110080b85006003854610f10050182c0d1024150b144020034092411a000a0b07072240d01070301000407022042c03041e00070700e0b00c2440030030b401c035401782c41002d40103940349820340c00d03039840340301e06107c1740a440800700e0402e2088140d01030301178015001e11f0800c560642c86440c00340c20701d030186080c03000420800b80c80c282d900f000400c401841403035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 844244604 1106 844243498 844243501
    0xa110a06020706140106180905060a05030118021f080105010c0c03021f110f0c210706030e011b0c1101030e0a0c03150507050f07061401030b 62
    0x4000d03280c50300000ba401c0074001075800a000090300409015151781ea524403c861442d2490300c0040e00801d0160200169041c9800880c0c10510091450b82541e80e01d40c002400c5403d00b02442d0070a10860286c1c0042d880d03c1c045404003690708640c81048524610802006020140240b505010803400200c081c8801c1070b4010010b1680580910345c4007041d41c09410084d02d042101e4400a00070001d0380c8003080001c0b8111100e040c5020042406441d074104100c055000c0b418212a1946401c50802040004110350002821a83c50015800c2d128442140c02d4942e420027008c8541c904101101c45a03900c04002e0014540003840d580148400c240120045e0482601e505100d118401c0004140700380c009221084034850b21501c02c0c4d000501c641441903543c101e4000c40441c5003480105127002e8014024515607104180005100c500a810341d1082442030b0420b0321420003240 = true := by decide +kernel

theorem cover : BRFrame.Cov 844064748 844244604 := by
  have h0 := BRFrame.cov_init 844064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 844064748 ≤ n) (h2 : n < 844244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
