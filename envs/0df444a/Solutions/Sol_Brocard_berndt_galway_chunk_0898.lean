-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0898
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:34:22.756279+00:00
-- url     : https://prove2.me/submissions/baed3333-014a-4cf8-8ad3-832f15c2da64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 161330935 ≤ n < 161510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 161332185 1250 161330935 161330951
    0x3120c0327070f05150711010e0409030c02030d050c030306150405030a061506080c07030c17070602030910020c1009020a050d12031125050f030a05030106030b01020102120604 77
    0x1014541c0a8680341e0500180075210090118000160200690390710790381d600c0045a86804014058254100041d8041e60a1054102186181c183c0711291001030411400340804080000c080300d03600746040b0702040000310100150300781081041c01c0c001050805510300300501e504243e49001c0100746901c10110300008091950305603003660004d220140441d00688080e18062001d88501048503044c0404841c00159040c4034a804c2c602501045131418138092840d2011641400310741c8042d502c248007000d4100720020600010501a800f81d403006840b41030819040b8101045000c1104504d4018030041202800225641c41080844c85002814007203a201081d1a041b10303a0200e40c2c40310099202c0c400f0f110000c0701000c008649540d0420413411640d241c0340c6180644c1d9070445c10f000384240881b04400719900c1c1660a14010012a006020350140346451540301c2000c550018901000402031107400d0b0007000100c5070240001c0d801c0020b02d0898402d5004d000b403205219580322440d13 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 161333435 1250 161332185 161332201
    0xb0a0504150c1b0602040915031401050103020604030609060e0303090a030206010e25021609061706010f0b0708070f03030219080f0c28050c0d0e03030306010309022803021203120c03 80
    0x40700c0040900071808c0c006c00080585501c40840548401da0390180c1003841d5903800b15040c480c2030305032a4000c0009081c070b81152a0742004000042080707440350361b203025064143c10704002440c8684840c10040c401032081d440c000b0304100041c0c1c0014030440d901b60a00412919003640907049c0c0a40010500300350403084c05c102d1034803414503003035910244c40b2080413894010603004402900c12500070307520301a11200d0042c0d40c03508c0c2486502d1a42c49203600601c80150144018105240078402c3c40e820804182c40303030511a90341100403000319600140d04110101040c5080710545041d0600541e149400080342e41c0219000f010520b69600c0061205004848a100b010b5182031484d0b60000c1c07920400384c054100c2e4022801d09426101d11540120150300c074644c0a8203056020300650b09641703c540040d800360401c00303c101d80c40b044803c1411111403881d03400404290003030303502e408100d00c5d40c014000501c20309641e244254004002140d800400503911030740111202c0866a0b980da0340c2c030380d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 161334685 1250 161333435 161333437
    0x2101050a05010825050702010f0f0c060b0d0203010f02030109050903030708161e080702060c0c07030204180b0a0204090606140703080910061e06020d021015030b0a0504150c1b0602 79
    0x1310180c0c2d8070303815903408242540d02801415802d4402e0300c5030010600038080175960101045105c1c4009204290b24100042e26500411032461010780449510f8000d40d0000e429070b240c981d242c008165011004001b00d54083c09103c0d080b407407100203180386040c5108010800b40c4001c03c1f83c61007580340611120034500c10700200c40b081c0c4201d0001455240c84003001002c3c1035050798a00c0040c031841020903d4080c002c4100d03074031410014024a05240707180c0c240000b46c00c2c255000b80702c1502c03c2c5800c8011420050809100d120344060040e40e0b503081601761400c65416030441d404104404806041103100715085815680d01810044034941d1448102441c0104018210b20201d040c82d03000aa0a002040020b1182d264540c554040325120320040b40d079040145c4405005a1040352038040c04400c592010303220072100c02100c0b02e503544940f0750425040741965410500355030b890800040c002421103074045104010300610100184200007003404c02a1043c6585030303508040c00d0340810440c0d034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 161335935 1250 161334685 161334721
    0x130504050112030e0312071b080a0c08160506072003011107170c03040e0a0603082b110406050d090b2502010203010b031506090a03082101050a050108 66
    0x410602007580c50702a00710316844100c20032804110504040526403401060188210b0a00084103043c480180c50780301c040c18440c5428125045440404152440103114058030140a0100700c2c03070303c2d443e06d0049444c10018050300e0080341e684400a10480e5a250100c41c1c0e016009a802c518840030040b19042c0c4415a03418540d041d8640000c40518040542c003034408103010360399480c0f90402403051040c5600c680440c4000c150401c00c000e100c4082c4500b5842e4003e80c41c098005600e45c0c6070741c2d841c0440da001d010701c0c070501d6503202070100c0400c0c01c055207211100d0b0491824482c0464046144005010702c2c01004140407022030b800c050841c555100d411203a4021040e1045e50804840308002801a04041c0c10b03400f02001e0390300343c0e180c014000c482c12203d001d040646103a07501404030703131a201101c82d4581e0010040081031519602d1400120145000c3c011440da1204038400c3c0d10300807010642290440c6e170703908004000c0703a034a001c0301804a075000c0c01c1507031440e80c0e80d80d0a884807140c0b207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 161337185 1250 161335935 161335939
    0x30c080c16080d140909071e030501031509120f032c07050909070501200f01060906090902011205040206090a0e040204111206010f020f010e0a150b0607081305 70
    0x388200c80540185412403000700da6480d420f40720555903480381241e00c600104401d091104e010000c45c0d881e0304140140580c44070851074a400040c0c801c0300056100b0840b4203082c00001e803114010b0091105014081c250844000420040c650103a950f591100410340030401c02e0180c082c075004826400f90b082480e0580d18044207095014581350102c41a182c8561591420300c5a070303901080c02e0500a0805000b409210010184030745400d00440d10842016400c0c02581c3d852881e044000d8010000206001c1d45800007055060620409504039051640200c2005080840820140c1d0b003040303002606080c1500d02003090f54a5001090840c801c00c005150019258007000038500d42c804640b60003076108603820302101503d60f0840c2020b000309840d1254040642c804119150b0041e03100c44005807050060b11080800d5154050031503400c644840041e400110040e130400c201e02010414006418034100245407000f404a05103000b0710300010b203501400541e01d00300758083c0e0320000c0100b00c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 161338435 1250 161337185 161337193
    0x20d0b2d0708160e1002030c1015090c0306170c030f03270f03030c0a0b0703020301030c14030109290c040b16080412030e01121e0c0c0b041412090303030103030c080c 73
    0x51741c0b00c000d5072a03110104c066035138040c0014149a610081c000d007000300c1050a281c0350141c1c1030200c25002480b0340e252020a01da40e440c0001036031204800c100381a480b9807070151600c040600141800c161a20b040c10015070020019a03135001c0501465240c1ca82c1612151120070042c14041021001e0030104282d0610010a11407100140082d1f825549403141404103020749480409400781e0200380401448583c52050900c054580901d104038107140090010421240945a00400149107080038178140c0c50488400200d52090041580040300101540d01c9c0a2409440c00a6070240351803030140710b2151080b101c140710369281598050719007003843e83e40c0080107140140103010307440a106d003c2002c0c00c000f03455160040c03180203031a0f00c6100c80060b002c403140d8986402810501301180921048a402c0300110302c010261710702c51032041201c600103201001072140b42c4080d03445c40f0030038540100004802e50f1804003d40f4110b1b581820100c42c1c040b45032070400600e001d410700480700d80c41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 161339685 1250 161338435 161338459
    0xe0f0307080601081507050d0b0303070b0f0709080c090402010810170c1c02030a03081b03010314013c020408010c030c0306080106060e0d020d0b2d0708160e 69
    0x1c0458100c0c100ca0525048603078072940c84014030303450039048580c040800d1003030040c03102411064020034400800102030380e180c00b2460340c03603617402481a80c0c5002802da86000300f000d22034001500034090680b001c018008040000c002074410701d001403009041044480c04120020f41d524080300c0a003c8855504000404504585550320044080d180c800e86100300000c0c1503509400b0100c17880e64001d070103808100c40fa510190380b036900182c0918803080c858880e050303440750170001a41c061445001001060a0101c9449007550107030818200188901e04006003512a403031140122031050350042e40075040070f4a4083c000703014a50103c000e0394207015280641603456482960701c41165101008400d03220240c80382203a642d0b000f2100441d00200b852030346807034520318070402640300600c40b0304217015580d41d01c1c800900036225040c05800d000102002074806400e00b002410f00122044520300d08018010500300002d4512410f01385100c548101103031040581c580b0300c8101a040c405054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 161340935 1250 161339685 161339699
    0xe19020f070818010f12050705211006030506130903030219030506090f16140910051809070923101116141905031009050606031c0e0f0307 61
    0x10b4400401c0d1038840f00803440211039903001e604c00003000410f030342c0e40060070268451039100802d0044c1500041c0f00c03040c8006a1a440e150800e00c5950001a00c80041c1d0304116201c0026268150084400d0508000030040c0342d0f01c8810540442c610861000310312040d0302d08003500203101da4100f48075914455003094103101d4154012a00401041e0342e100d03070a9032211350704012000c0076a405085a881c240341c07005440d10409402c401d0f04480764100c1d01e0b044012000800102944501e100800c40110300e21188a29400b124203a03018295000044d500c0d04810051030090b107401184540b0301584e074444550b000f1101c007642000c81c042d100c4000c040380003c024141c80000c14504115214080c032140490100c030b002c41c0300b1038613010000c03403240d0228401c001c0c140c054070aa001c203024510100040640c0c0c1040044000b403d1000c1c0002c000001c1d041060034080d0082829002c0d9000700445c01c02e210a03012400120803240c80c05508144040c1b000500705402076114990510072441c0108a803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 161342185 1250 161340935 161340937
    0xc02130b0a15020f0609030d1e0c23040b0904050a090606180b01020f0c010c030c0b0c1908040c06051605240105010804030c0b0a06080f0a12090e19020f0708 69
    0x342c0035000c1360000d10781058840c0c0c1e039100450351050283c10a100c0c540d4140b42c1c0c4e03008011030703d2046041c10480720890559108a4818049000006041c0310704a0804042018000d401d40906106140350a092220401d1079105000300c045c0a281c0d12000a4442c43c520341c000c0d141550300001c10700c00c00743c0d5031294100803030014040001c5540b030b021084c0401d40c000035402198201400142a20548500040d0b45c441d8140b04140d00f407041024040002610190310745200b40d00401d181c82d103801110800185e50208c002c0c0060034003207904103110209900c0c00703040086640c40d117041b984c0e682030902046040c81e00000010090b21840107201254400143c210b00380440002003100c0c1681d070344004580c9a0001c0d10007801103902c0c1088100802c1590302e40c5030307000c0c1007810080740a41c2d41d030000070314140701c1c54180e40c040c1e0480c0c0c800200f080014420741030b1040292401a03555802e104440c1100c540c068103c0e14000428510a08840c00070b03016259940310080d482c0b0b890fa4818180b11020b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 161343435 1250 161342185 161342219
    0x110d050f01061404021e03180d020a03021204081905071e03020f040c090b03060102010216080319051603020c0703020402030c030108060a02070305190e0603160801080a02010c02130b0a 81
    0x3c50f50585030750034600e040134400d0f94019204540308100039078a88008030b00c00d07440608a16640c10310000104180142000b6088085031aa40108501205414024101707001c2c4218400c544000700010003607440001800204400307541003203040d440c0e030351410515000c20355210201076900180700404d01c40c0c101c414041240d00a60303a007410b0101081c1080116040401940046030750b61b07000340920100d00c005141e01003410700005103407600392940007603182c0c607044c0110395410000003001140860050441c01d00e43e103101003070105081043c5c0803c0d8801e9080d0000040540c04180203105003800c01c6100c0c010368001c0d004558904140070040c419a009000d011550b100d00340106031100250300c00c941410350182e031842e0401984181010a010f8400c401c28100115424001c01564454005501501005050759041600590301511010050340082d8603078010f0000c10700981d800280210403140d04860f1703030ba1f040350b028180c0b0b0010841350340c83c81d41114001c0c82c0868500381080c11401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 161344685 1250 161343435 161343449
    0x1002010b0103050603070510050f090a0909060b10020d050d24061403040308010506030c07021e030c0a0f03062a0c061415090a14040606090e0601030f110d050f0106 72
    0x80d41d0389206146e5241624421160002c00d4000140c0109101d08040d05030300404090142c907203694203000444210071a0421842542e451004008010301c500c500d0321103007016203504014400200011791509044e18115041c00400112240c201c01c042d8031030160704503401c4040401c00824145110611414002c100204e5001c48031902001d0b003c1080d28030840e4160b4444059030300781028040b00790000392041e480200c0c10310100c03006035910b4885c0d030000100009910007004003142018030f05403500803001d003d07204103103040c0700340c0d07200b0001c5c10256134000d0001319030b02c9000780f4508640d400b100740c2e104409004d40c0207030f0703565030303001c220320300040d019000500c42c1c82014640618501c82c1a10700313480b41800300300c2a0f21b603801d160b03440640c00901c41200241051900703c1c00b2100c008121401c03034146a030380d80207000c508028410400c141485000401056040d0344c6e0b501c030340050317007100904a00b21303c2c50039504ca55030b1058030002ca50b0740f05041d500300b101c04140d0035010f07020a0040c68 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 161345935 1250 161344685 161344691
    0xc21061508010311060d0902060d0c120c020309040c0e03070e04020312041413060b070c030c080703020102060403112112010603020a020a03110a02120a03090603020a0816020c1002010b0103 83
    0x490644241d032030906898001c0004044011040204100c0d0f07804540038409503a2104800b2002d40c0e5000050040340100080c00b007102c0501d08002003024071002c1d541103c1c18609100315024503400010741e070340880260780004403a40c0e200001e0b1554107c10404590506c00c08001051015880200502440c42078003240c6014401c0000001a0f014034041c2d003030a01d40444080e8554582950001c403850040c960000b1403030340b18002111240e01000b4241d5007407154070030400c1000110071460008152800143c01c000e0b003183d00003501e4005c040e00280801c03100c00c010321400c034014080c111320540401e403141909004c6800711001d5411481c03400b481c181c014000001c50034068021140041c485a01801c144507080c0d42c15500d20300f05030841e0040e489060340d05001a00d810801141d0290441c0003811403100301e00c0d0003408002603400200806005100800d14a60010b494a8002a403042ca10f00041d6031240c00b00c3c51705405108055110036004892291076806500955800c2c0080e0f801b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 161347185 1250 161345935 161345969
    0x3130503030403023a1206080d180f03260408100506010305090c0f040e10050406020702030706020d0804060509030d11031e010302030d180914100905040c05040c2106 73
    0x189401a02492054081d003510103517030709120712500341c1811391070075005c0016003291960360701454240740f90800340c041104565410400002e4025840081a0110002e500bc0b400c0d0f943d05501c0d20004403102942e010403c0041103c010303074800303441c05012041c044522000300780412801800044c4d9285010a00d00804580d9604000c04c171003001d400090010250350003180103001c010f140454040e40b407405042001d844a02007401100d0049002d1503015885003560700416040c00001d9200006552142140d054925001203400390b005030428000107060342c1d40e104141c218030400c40003c1c0300600d8452060514440140514005c46400940902c42c600600031040821400e0001a60651040d0f222200b028400c00c002c501c05009130f61041500b40d6110450404d03500c6040e00d1040c01250401004210344241608000902030000280014145510707104000a0345d4040c0301d01039601e403460848107034043c1005400c45a2241c11813000407001141c0c0100500c0c050007100da4403240e0180b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 161348435 1250 161347185 161347243
    0x10e01020d050a0c0c0212010204030209100503150f0c0a05040b0d09110102030f18010908030a031a0f1e01030b060d0603140c03101a090405011b020f0c060313050303040302 76
    0x131280340668681340c1e204014071075020000c04c1d1424244c103118030340d000c02c4088010b0300d8030301c4028003d403071801c406505641030000301070070201c5001c1d1400940003010200a502e1460f943e00f1600003002e0341c61103030303911490007080711140301d9a00110b143c41e000042040b03041c50b00f5440552058080e11021150b00f9000c0012a220301c190041f0800c4080d0902144298044580c2c8050045c07505050a0484a640700809030a640110113450003290703450380d00050383e004161082200a404407601e8948040e04070000b44100400684441000c0c41a101c10020364002da11258056030700800075901c03000e07584e496401416803404100e48105101c8200c6641c0c130310004510015542c010050100c48409422240c0100000c60040488105101c5050001d031038112007980a140140008250403141c0201c40383c04038074912442c02198071400403030000c105c01160118808004481441d03490701d901101000301d0314001c2000e01207000003c1800101500060702150174a044041800d1000fa4000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 161349685 1250 161348435 161348441
    0x4020f0a060207090f0b180f090c0630130311010911091003020607062c281407030b070305060303030601112505010909051014060408010e01020d050a 66
    0x825100541d0008509100341050382d0450524003040c0380700011b0b0320080c000024120081c880000e108104e032802484031403140f00080a174880e0100c0c009040b02620280451000e10541500c0c289196490148059641d40c0360301e940b030348c00d50b0a40ea012207400d0441140d00c03030141c0ca90003200480c2400c801d1030602c51041c007691660b00d03040300d921482440d040d000c0c80722100000300b4031030405848540c0400140d840e2400713030211a0040000050340d00b01c0418100c5141404440203502c0c00703800346100600e40000609030300c0101d00400402042c0b00a044500606010300e800030000c00c417078540300c11813002c00900d603c01c8038054641c038042038644e0742d000e0f42111015903005405400800009480c0d501030258480d51400d004100c41100400e5103400006002e40c1004d59481911214100310b650780c440206406440c41034020016804d180c81c0400c01200e05200ba03a14643c0d09103a00500c035500c1c44103440c01020030310000e0140c102e40c02a954000c0d8040841020031600c1c0c02c02240d002c000d288 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 161350935 1250 161349685 161349689
    0x10020f0a06020c0a0c0303091d06090c1303020a030609170313030513031b030203060a140630030406030609020c0c0114040909060615020a031403040201031401080604020f0a 76
    0x8000e403015803125181c0001a601400c200100c82c800c03004030340c0c0011081080b0740000c3d4003e41d2071549050400030203011071031204070310b00b0381e071307902c030014022135070344a034130241d00075a0400529a0703c182803007001004c2900c580c0f010358494000a000028400c054010490f40f0f8481d0036201c503141402c0d03008154a020694810f48000c0500203002d000a02505c0200b540030030008a02c4462560796850349900700d103910401480d544440010411410304000d002d03001002e640040c00798400c8841400e003204802070040744202045100140788480e000d0501c0c0510b0020a41e41034807030003007990140d5941c03046c40390340d00192420600242412040c829984604050340182c000d03d116000111180441500301004546042000269090480c03040c400f00b58403417080465420700e81300c56280503402800006003550001381000d00026441580c000344480191003164490302d440c00120000c00140451314005040c050010540c41c41c00035100f4469842182c2101c0b068000c04240111410310b8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 161352185 1250 161350935 161350963
    0x307320d0f06270212011e050405060609090a090b1815010509070f02120a030905160f121118160f050a050702010e1c0312020703020703020f0418050601051002 70
    0x50b07101d0820f0701200c0c0002c000c2e5106003c00150034040142851498801c080e80b041d03038041c0190b00c4420907000400d180b00001c0c40125002c03c202d103041c1001c0740892082c10b041d43d1082c403c01c0009420100076503c141403494004030120380e6880c0c07a640380034448041102205130361040a0310b50140304211409203069a0002d0a072520b00c0c2c64459080d2102581009240294040d010350000c940900c403000c2c0490070070594012580720030504105040644042c008a030310618603038240100c1038500c107007004139001d00040b400e9010b0395041001d8501d502119550740b202e02c1c0130407140c2090402e101c2d0742c0500850030350768140c1c0700181000c3e10714607843c0605c0008214140174250096009202928016006040040c035800e0703071100050340c8049503c051101c1c103840d0f101400a240d4044014008003804000445c50304c0306a40f0041d585001d944030003880b80a01000788055521550006c43c5048070001c5242442d1031207281075512041c00b4000d00380120b0180b0014003a040c80001c02820700605 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 161353435 1250 161352185 161352209
    0x512072d24030207020f0d0b15010302090d03050c101109100201050907050f010c02030105010b120c0c0a060c030204030b070801050f010203040509010b0705070b120103030f03050405030307320d0f06 87
    0x20794001580650400207060b40d00070520000020f058954011220250f4801c0c0740007200e034a132a8446540d211180f040ba2030426106109846035a25800703035000040c3e8042c1081070301d50b08981d000500d03103040e00154141c90303030920441c0c00b07160400001a220501e01142e0030f071109080d10f4400c13800c0f25000c40f616402603100010800060038480b030243c1c2c03400d1061401d8a0010015000b103802d481003030303001032036000b00010702ca001600d036024400e40044c4207075402442c010b06124040c6c2d4032000018041c1072203541d10100703032501d4002c6e03040310700039070713128101030800d180000d0040c0216500340703e118010005141074451640c400303c01c50f030694a0080900290340d00703005550780c482d007100b50b044925105003240812180784840c0908161001d5a180180b59030541c60010a10b4100c0f0003642d06041c20001030200040c0040f0949034000100e01c0c1840c0e011560200891503041e1244502c103035045045881550361414030f0040038100d09c40c1c101441001c0c0e04030b4100c800c84046219064503200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 161354685 1250 161353435 161353499
    0x5090411040903030209061206100c0308010308030606071707030306211103190b0417070b0a02090a1a0901170702060c030a061d0403030509160512072d 67
    0x6010742c407481c0441d0081c5030040c108401700000c55101d038044d13034458058000d01c000f0881d40740382503141c0e503c07820745510b4600c030381076690398000d8407821042c04010300310302010000400a8070f8100070344110310340084203155a4104803c0c42c000540c46100d09030700181c2002c00105800200d603010344030005001c80742002c04c074425294620620040ca01807641802800110704100386040b8480f000107002d0b10200b1030360304091074400d0f0041c1680c52960b403204818410310b0003040182014a0340003000c1d103400741c1d80b0f0065400141480d61960030421807000403500b1404000c90780000303070605034400e0b00c0d000d84d100360012410060000484800c00140d120000141240c5d51440140d80c110101c8100415180c0d180d2440400d0408105c15901c0114492000c100501da854000c8540003100d590280400c007000b0350a0303c503922881e000c0e29025a00f0560070741c43c088420041d1400600a00c0740c0c0d1402d06407500305c403441e6410207514200c0b8050b850b900201d060700c00f040510200140d110213900841b5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 161355935 1250 161354685 161354689
    0x18080318060c0d0c050d020315011b0f120225062a110d0f08030a0b09090a020108100819020406050a0806010e04020a031a0702010c0c05070e09030c070b0903060105090411 75
    0x2207460304180c4c08111042c0b00510749089a800a103005a148952000304101032100060121000004000d0400c0310611a40b022904101109000c107800a4100c0d00100381590243d240020382101c40003441c03014413039004000145611601a0390440c1c1e40c07111511001000685c4c1440d41d01256592062084510b070000b65070110748003449d01c009801b60780036440d00d4907030540e9000c9000c2c0c00d40d0507e83c000708202500841d4414032180080031508103446082c202042a034a9505c1c0c0f000034188440b00c404210090142c4d006c48004000c5042214180a5050b50841aa4181c5038003240902d0400c40003080c1494045055419030f01020001c0007640c1c605030090700aa100680700b44d030440040741d40807003c14200d105a50740041040540d15050400c20381c001d00310390101101d04104002c0081c1c0000048c00811400c080f00d0100e90800c1d404e4581b140c089045108113558075105200304400000c0100040f0003800740500110b0542c2c000b40c1c0d032181032080e000d0301250010324000c4803074600d05880c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 161357185 1250 161355935 161355941
    0x31709030106150f0e010801030b06090403110714090105151603090b0307020c0a0b0c07030b09010e2d0601060507080a0c0c0f090605030a0b1918080318060c0d 70
    0x5800000c0012490b240d0311594909804a45618800080c52003000491810b0700080c400080c24020310b000c05036980b5503124084640e80c0076200713a10400030940410289071085102285001140050301d4031a90380300c01c11042c60074001011405001044000140c61030003800c141c1003d075460440510b08224540e01480d80c5502e04000c8041c82210303a40441c0c40200100510310070089500100020301608003000600b02d840e6102c1a002d420400000c203280801140a004481e800703503411289807260b400c0d25001d0040481030110621843c91031488c050013400058181075010600d178802c1c0b410320403000c4d46a07402406000c0101c1d0040141034005002213000b80181e5055113043c041c41c8082c0d0391680c2e8180300c43e44c016514008020410301c4000e07503a00c640d070014070046004207030000f4542c4c4c0320101150000c0161400b040c5100c2160722030600b542001ca111f046048825034910114a0a0358282d00140d44502d00c11a0b18201854000c0c80098900e00650000003d682410318094080c005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 161358435 1250 161357185 161357197
    0x4051015090315050906090a03050a2307030c0b090d1706180c090102150114040e0307050109060912020a0c0b0f0903070b07050111030118051e0a0501030215040317 72
    0x401048610010208620f14000d20400740404004101410162100c40c64a0b602070000315480d00255403107000603400030b0450b0556a2141041c08a400b01101404220703042144540303444000000c3d81e0382007540c44551021000c1c031408050006485208490345e840964450150116480c1118004030321000000740340d01c0040109082c4080908800440300b500041e03404803034800021680c440d10b0b68042c4083e44803403000800c01e4005d50706d02044030601496681c6c5560040390b65140345038802c0000e0040313071901c0750450002d101032031a500e441801440180010f840410003004524041c1e4400b00c2e85084107900503170b1300450701382068010a1243d00c44900340b4684a000c00c94490941c800744000c20042c541d5128443c1c465085080103400c0d904010130035840c0c4042040188844444000052523001449000054030340d0b030211101c4a443c0c060b09c40d1745020b6100402c00c101c01a054116505a034400c2c4c0e141c0d02c00095421420890307015500008080101a240d0f40c5c5914074141c3c040e0407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 161359685 1250 161358435 161358437
    0x1103090d140705011d06090d02031204020301090506010807090605040b01022d0d1806030b06031b0708030f0a0f200c070f08030409140112030e030106030206031905010504051015 78
    0x11400c9180d90b0b50341d017180d035002500940100142120301d000c0d04181320b41544883e00801405e000c04c0304500c001d440e071250018418201810201141c25501c096104225195204c0b0845207a96128050141d6540d268800c1e005002d080c203202103024202400360904020068000301604540c40c00240082ca16266600040301d44201c10300e4201c03c0c0130024416500e549480350484801d201c45c0418140308940c0208061504005140d0045d48401040b250700401d140c00400a800c02c148104400c0d200d14207010f007681401000340020a408524002e01591845408200342c0c0840c070f030b0031402e5803004201101c041c6c00c02c2e40366505201c804030044c80200c2040040d924400d4403a0b110201e8640f054000100e1a88007007001c4c04003910301c4c45008145400384e0300c4032440e985000f0071080780d400f0b401802010003084206000d4140c409401950285a0043c112520303803800060a2580440b60304400fa500703400d08000242d141424445c187c010594450080c003043d04200790782c3c08418660240304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 161360935 1250 161359685 161359687
    0xc06130603092f09060406050d14011e0b121f02090402090a14090a05010b03060d050c090106050a12020325020f19020405090f0a0b0c09030a151103090d14 68
    0xc09100c0803207894402800344800f51416640030303080c402484c1006140d54000e40c03502c5000d02c1242c0d07664244404159106407113601c03d5151070501405494401d01c80002010071100d89c2480031a541c000002800054601203100804100c8440d640d141408000007086804007520300303040800d4000b040c03501009031016140c200d0300c0001c600a88510f6011400c002088890b00d8102c0c50b00c0d000c10354000d402c1c0c07241804254103001c411215440042c09241c41046925482030802105103c04141418010040d80081d03a544402500941c044240c120008400350142180c20001c0d109881c000c1c0301e580031b51154554551118a01290040c030031800f07600c6000a03a0075000340c01c00142e58098290803280300c02c000f030380c0305000035100064060741d103070382000e591620010000111803100300e810103000480c94440c81001500c500c40c0701d01454045c0180301d40e22003030000120b001c2c0310b0014460400c10205e06d00401c1c0d620240411f5401080c250070036108092464031030800c00040310b0158051b6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 161362185 1250 161360935 161360963
    0x1140402090d060906050c0a120203070903020405130201090918060b01020304050d0c050a06110606040f0e15190902010504060804080d09110901060f05160519140c0613060309 77
    0xb000b0740d41c00d101c100da5072038403400200c04000c003d01403241c108190911345030514603440d40242a40b0700c800b0030f110f2070030350120000746042c2c8a010300c00004c6401904c01c00c00d904201ca03054013641d0310000c0603030200e80000c0300021a51240d01c10062490303104003a940003604550343c0c420203042d0341c02e07075039045110030b00021400b540c84c2088408940d100c1c107000c041c3e040c0303085c045c0000d0300c1a0741d004a091050020a0110111010a26540c000801c9800042d244240b241002c018443c8003020300652041049642c007a0300b01c04826800f07940c0e0b011000200800e542d4120341541c1309000700130700066060000300710650042e413000f6009807081d0241c03400c202c001c012403412121145416201c3d80f1034130522010500b40384c24000c1c050b006610f00040b600d041c0400140142c421004a42260340800d04600d013030090034000145101c80482004001c440507003006082d0086002c1a240140100e807440354041c07800208845140100c482080c4503903152035000e8005100c0c00301d060754981942d002d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 161363435 1250 161362185 161362189
    0x1b02150408062a18061b0d020312010512030703050703030f020f091207050a140a03020415080d0813030f050705010f020307090f030507090c0203070501090317090d080114040209 78
    0x1e51085140590282000f0540c80e0a4036080da22804151034080b420070100100d10500101c0003104401980c4c25a942c00d2090820030041c90245001d0440340980221101081c0c0d01000034080c105034500002602c2e40ca0300c00b0000104402c121004455000b0094000000e02400180070030364041d050010314960b540c48010144c4e030004c048850440c60008000704e0901d445080355a182030002d009244a504000108020f10024000c4000d40c04440310700912690341c00d050800507503406003050040700e52598000e04c071103c0f28000d280303550103004102c2803030303900ca281040c2c4503034130540303c10711111080e48095902c10514411501001403c212400110308240144907400703644a500580d079180a123130007401c0c0f12243d009030008030843c4c00204085080040c02400307a58450700d001411000b1603030309034614854603400030059428014901c09250300111321450441488103019869581e020001c2d0f00e07110740c0b002900105003090018840040c0711440032642100c046e200601c2c107101100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 161364685 1250 161363435 161363443
    0xa0b07170f07141602040f0902060d0204090b01020d0c02010e0103060e040b07080a0603030e100201060e390d0e0f010e0f190b0103030807030f0204170d1b02150408 72
    0x100441c60001180c240314625a01c8001050f9040300301242c20b0504883c40000d24030301801c588060310443e01c070108090a01104c1d40315181c0303158020419503036440ea24a204010790005c2c0704a10790300380350052000040d400418084100e00e00b03640e402105115550041d16460208161581010355503180411401c1c0b1091040f8040c40c0030b401040034070714160400401c00b140007400d0010080c1840b0017000001d4126076444e420000840c0c0724090704440400480c01010716a0203080240402e2050010030b402d912120a41c000b041c1c00081c103030241601c41214010079081c00c050300c0d41010021070070f04803140c0d07100000d600000001d0381d036284c07502e00000303007510441e800b42100c40c3c100c10a07540f00464100106040400c0b6421000004079054460203c102c3c0140f0001d02803010396030000303c0e02442580b0210302c550306100d04640369600d801410f0010122560780040610071764806080303a6000d0015074410b038000082070026080f040c4c2c01d100288400849680100d02c0511000ca820350080c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 161365935 1250 161364685 161364691
    0x50402030603070915090c02030705060a0605010f0507110307030f060c0c020a050607142a090103032c04020a05180109050f0112090606060c0b010b0f0405010c0203030706060303090f0f080a0b0717 86
    0x94009d54480b4410b04101c1c1c185540a041030b03680e00d2a2480821241e60002c4c0090b12070002d5040c0700340c60703400c035090460061800210300c41d031500540b44040f00300302c003075640700121b9401200d04000d0f035080c842e070549a48520000181d840161400304111510301200100001486201c40380d0510800503495403070711210034582441c505202001c1108080000150401c4500484040c1a29450b540b006800c41c103103064026040e8180300840f150041007207d04580076a0003410441d0b81320075450f030052064210451501c81480c000022a00b0366104409210541e1401056501540029001500e40d026003001d165011502c50880e00d01180c0d0b80e00c100001010562241c42c0c0700710492400a18004d416009154450f030188440b0385d010082d1426101a2403013800c010320042c442e4000689103006482009010074188000802050342c0403c80d90100e440301a00b000c2016183c03402c9021f0001c80340141003a55110300c0c0360101141000c400d4680144007030518994100c1d00b04803a01d8103100c12 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 161367185 1250 161365935 161365937
    0x71e031104090f210302090607080307090e01060815040c02100e070306060305031e12040f2406051009030201050d02071416030506060a062003042607050402030603070915090c 77
    0x110480944e041e240320190080c1c15504e002c600d0030200b00000740442c0198040601003070004000584840d0080724003001809036254904490b43c2d44600c020725140303044a6002862004e02c5030b001003814280200300310441d568001d03245a4044200c02d000a014040d800071051003400400008551244143c002a5010f1070281d0341d01d0050f42a030031500002440244984001008415a02840d2250880c1c00590040949030000018108034414040400f9811007004042d0307441c0508200ba580301c00708440c0161014481c0b840740ca00c055840300c0061101901040342044140310f40707160b5600070800c841c811150015440400005c1c1807400b8600c4001c6050800340407018000e0110410842c0d90000c0110b403165030f10340c04c2401c0244001c9909064500159040c1c0c408207116500b802540c0203405103035030080c2d42e014080796207944540c2c001c6a15907103005602010505090038000c503071050700c1c050b009040182c034080225000b01000007494400d24051840424000c00300c3c040c0490308030791 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 161368435 1250 161367185 161367203
    0x60a0504090606080403051602010c0605070804030806030d0203042d121e150509120c071e0303050301051207081218090105010e040b01170708010602071e031104090f 73
    0x7801c0000085503125044082404110420040081d0703103c0100ca400c5003d45040c6030400700b482c8010f079540e00c4200070040440d81050100412b00740d000d644648254040c1e940c00880d62039440034180c581c0e13095202000140c004002c180010050140c020811a0014150391100c075100f044840d001c06940e0400c03141c10705484248828000300e0342c0070420a40440340c0caa40440c00d00d5036000c4503441148100b901c180e8580b0002030800c9005e000c0343c41000f6038141d820b559030000d55006070f103410301805a00c40c0040300800c404044481c0500c10750a903a80350b2078840c03030359081400f089481c1003025401386251213480c2010621040a0101c1d000d03036104000030a071039260200b6030522a440482c0154001c1d442040108110b030392100441c0c040c10404d580c005110307011000125440d8616090008500c1c0068050203034096100c0c0c0c0c00c03412030b080d80d400e9551884d100d0781c1c0340c0032180060100045082300c0c640188081142e44819441381500100002800c0c0c019a884c4086c000c1f1504050b01d070100c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 161369685 1250 161368435 161368439
    0x12070c2a0503032a0313090b04020d0515030706020c06030406180507080601150f080402011b060207080408060903040303020726060f250206010e0a0b060c24010308030402040e010b060a0504 83
    0x410070800b03100c4c55406001842c00c0c104690220381e0005440c0c0b1a1142554450001d6003150711954100e80101040c0e031381c00c3c8900d00d411200b4612290581d854903002e4030500c2c1c00081c07054404990700195840081c40c0615644031610703030310040c0046501000e0302c1490030304036038005a41003204000030003c110160a09614000d0701e580748058207600c80741400381500b00050416800001903601c5035090811062003885103040300c1640c9910303070000f05540d100003854014410f603240a0411101c81c0d40c221100355407034041c819201e0049100c000c0159210000c240141d84075680c03603e1034041195080b0082052001405181007000c2e20035581040d088402c7c030810303030100610340d1700e03049400007141c0c031001a80740c0096030b5400512481c01c403c0c22440204461b00105d401c0402e00b814001c003a1a1200e000b1004c2c2031301d501060b00132234041607041c089004000040703a622412660010030780d034107541d507603003d01020300014801c81d40c035550380b5035005015696280190518255607a10b10791518 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 161370935 1250 161369685 161369737
    0x11030f0702010c0e0306181011090906060421020402090901090e0c01030509031b070803040b220b070206090406091e06141c06020f0f12070c2a050303 66
    0x403800b09401c3e01300b02e201410300310103440c001003d9400165100300c000c000d4501c141c00350f06040000c84a88480f034200207020501c1d50001c800703049071510440e00c0b0304094a03440200b10079446644615001451100c2036560741c907030700d81c01c4075842a0001d00003620f003c50540000300080002d0300700c105c405640710b000245004081140c0c00701c4507020300701004581000d10806a80c0d005d0300c0c20809124441c810710004025043c0303c1007000741003610031a5200c0e5100c50002d521070700701000390b4401c0c0481d240c9904400c885513040b0f0b003c48600300e0034186010261380902c1b42990022a2040d04151070381400600340c0000e205400e01c2180e25510501141441321034442590460791240e075240000748d80100441c1e5404081840aa000d140e05038245c101341d00d0304401074096246035456070000400c811020b202d044004003900d9014850f69003113a580d05000f510540e4400d440501111980810801e0700030140805501d41051401e891049580d0342c030009155034042400c1c01514078900100d010341c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 161372185 1250 161370935 161370941
    0xf09050105160801210f0305030609091204060f050903060411030c09091e070b0d02040f0618030201050309010e01020403231b04050415020307020c0a0b12010b0d11030f070201 77
    0x21561424107045582c9a114005000210602842d03519443c40000d00842010036421440c0070360b0b2002c1c1d104481044c5080141040d0030480741c0364042c10403c40000c401000105400003120303d5580140e003010700303050007124118031403580729050003810401f07079245070350030003455118500c51080d0fa504170301404285800c00c084030404500940110041c0703c0b44000c0800c80703000403100f00c59154954184008164504100f42e48041c80c94407000030610742201c42d81d00200203889256032103030b040d16520b4000329002441c1c01c2e59042580c2c071580c070600041d07216100441d0042003400010490140710b489450032070f4816401160b507107031100181d5803405c462000c5407503041990b4001c4c02907400d40a001c2c0d02c00b4040000c480e0300c516940c00001d0200881d44280c21185420303041c00715204d00c0e051102966600e18006e01c50b1103a40308200004407510303000121580050310042e00319269103803100302c04064010f2004070301c000351130310000070220750240051485402d401c179007000c0500745084060300b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 161373435 1250 161372185 161372191
    0x1b01050702120702060414010212160c0b04080322150306050406050922020316060e0a08010b06090607050a021012060b0301051005030612073002011e050d0f09050105 73
    0x102e501c00e2040384056500c610075a821a85410b24001e59000c142d00100d08002d082e00840306031403008203050720589400342c0100700b1548282038a0510325201c08030100c49024038464020203500c104200d00702c000ba10f004203180b166607031404044031501c89100041000c2c0c898200c000207659802c00300300c00c1c50103005d014000c00c1b05540e40d440c2410000c0301c08440e01d40050002c00c0c040044000c01003151020040301d80c51941e80b925900085894902c018001c14007202c80a12450340000040b5071120107200d100300d483d4005000d40e1070804424144036213600030540654442c050000c800c00035840714034461005807190755030241d9140d4034548102c2140d403650880c598040d8103100500c01e945959003151100410350400729241d94607100041c00740c0d00206c0d100d15050040500018007801406c1080301c89000c40c1c184840031307841d441d10b00d070303801c0c000d84030042c0c0058110b41c0185549003210001100810251901311319100b810315000081d230307010000c03c00e00d1030798401c900001d00c0740030300ca0290 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 161374685 1250 161373435 161373463
    0x302070b0c1015030308130f080706020913052203020a1505060a080601050901230409150b0409050d03020f1b0706141e0c03090d080405040c0f090b0d021b01050702 72
    0x9103c1d07003152002449808028211141001000b05c010240403107020028900c55001d0304e11640d41c188c500d00310001e034028510b41802060201d501e08000c5449000300351048085800c0501c040d00c1d0800c0a9006002c2c0c00f1041e401c1d0b010f100303141d00120380200c5402c0b1110704031810114407400c2560074002c0300c00141e03102d941c030354121b06c005000340e59562104038112070341c9001009078400c91030781606203a0385401100354040e19080001041000619000481c14409203040004c080c00e0f00500050f03802009005000f908101c0d0010409401b940c044e080980c501b10741d40e400d2a5044403044117982c844800c180c01540b01c000c0c1042403075800f8000380a01100309103940d0a00f00710284400d4401100303894140005c9022962004038041001519581e1074014610341c0328a1450400c04000d501502816004030704000c14030054900560590b80700307001555403071724440d00c2c00c464174405400400840c0300d0305401b00301c6c0b000c03190010380c900840010444000182401c04090103403a000c00541d00e50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 161375935 1250 161374685 161374721
    0x4020307080a12030b1513030b0a1119020102090307171204081903180e061f02060c0903011419060f0f03060b0301150f0e0609040c09090302070b0c10 66
    0x210000f03140d01c2c00c4020040c01c0d41800300c0c603a0440c000240e0070003000000c444c0011800308800780c1126020814604072805411960718649a41d0325900c10385080001500344100100041c040010f000100d116505c00c0e2840014107000306000024100074141d840142d140000c0e034250050f0801c00e0103000300c9007961005c01440c0610b041d84842d11a26120380f050314110301c044c402c0d0181405076039480c16000803500c2410301c1741d40302c07030307514020340c0013501c0b0b0f507000d200400590b2007404104e00c0c01e214a411141c005046c10fa5070a0000a4030740d000f503225940654a4000780c0035912503940d6094042c10701d41003000c104401500140c0c0031607041c1c0d405050511280b00303042150f80101c040d1031064076003010012030040d00c0400440d001d460640e440812892000800207038001c081143e9805036044a13000d40c2031078881d40d00308000c003542928043e0400d100c0e00c03c00c104400c80c9903c15120030b403080c019240810380e9580a0302603a00055124156038015002e481c1d04041d0341d100302e200c046000f00c120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 161377185 1250 161375935 161375953
    0x2030408072d02010e0a1e030501060f0806010302090a0e010c0c020108061e01050703031e060806090c150a020c190501111207140a08460e0613030b0402030708 70
    0xc03030b81d041048000a810711242d404404c0300c0f900d0303503100c980162081500d419050303a940c824098801156110a03180c0394a0300f038002c950602d1010f680000c0350280c500134012039096408001c0000b2000d00980d0415558404030024a0340038001c090310200152103d004c01e60450002402c8004010006881103010040035000c80c0e0123129000681c1900707181003901c81ca4245000d40050120ad10031102c0c03c0c1c031000215869000d1500312005484c50b1006a94241d181e084032b071a900e1420580650303000d02640d994141c940e480c00c0140541107010301c1160310700010800807562051503202c00c074040a05241c0c06001658201d112480d8002c4038a00800212000c1c2c00c4030083d90050301801003e011452030202c40c06ca100300452071403590003480307055440d90f03242c83d20003904440000760101c00c0820150326044101d240400d030f0541d400124034085206401008490011074080328550004040c0b04c510300324400030311414040e40c400c0ca03200003582001d00406160054aa12041d000e03807003c456 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 161378435 1250 161377185 161377253
    0x4050f010b0906040f08030d200f0a050f0d060503061503150402120706080406050a090f02040b041508010626030d05040510090510050106020c011b150203040807 71
    0x685811980101e0303500e0b480e0207410340003403c1c500c501e9110200f03148649002080c0088048000c0c41d1600d00107200304038141982c20308800191000700c00b030b0340c0e0b080140401d01400300c0820042c122040e461030810f2801c610b807028200c15401105100410b603964100c1840282820092542c000c0c40009000c0740045101c0d00007030342e600c412141521003085500101c1c045458100c1c0101014894000747c9440540700d840090201e5800c403401c0d541c203424000440d0050249102d401c0c4c0190300542e080c01412440d409000103041072132000f54025030fa40ba4131290424505810708082c00e81e0340004181140340c413000d24940c08181154049040d5103074022511010300200b143c0c000640c0b42d00100d80c0da82d4a040460a10310300307420b20108541000d01c40401c021002c038140d800820103580800403a602e42d00200da80d84407400c02d49010403020613001e0101484440d12100b941d204000c40000701c5508440740040ea00b050b18210380d10782d80415001d04112024000500d90071042c069415001c0280e00b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 161379685 1250 161378435 161378461
    0x200303090a03030207110406150314010302150304030e090a060303180e060904032607081303120b0628120b0a030b0c07020a0807080c040915020a110601031a060405 72
    0x507004062542c000780060801800844d207000e0004002d0080014558851103110300d08840401e20000a281200b0481c001c00400340403410303660003818010030402541c1480469503c00b800c15000c0c81494881c2c180c26071766034440180704540d881d0010400d00d26500d0050030303425400c0003080407400c2c821824022111b006481d19071027801110414180d48560500307450364220f114891540c00c8407103041032003c02540c03c0c030314011819a81c1e0341c0040e0b0f0366403200c10701d8860b160100600140748400c1c18224030703403550400032480a005019038038291040d5102c54025a401c040705612100c05600400440d810200e40003200b41018428003a0032440c60005403841c0d680c0c04028418015140424803102540094a40e22075010b0301d400461900c0d892215030f0744055126803c41d5200d00007003d0200d0506e80150452640d001441181407e0041403e402035080403526000708404103d1110341800108001c900a5000707a141e01ca03d0401c0d154140392414004113481c0c0100e007071900380060203207401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 161380935 1250 161379685 161379703
    0x80f1002270111060127020901120c030e07090603260702040f1d0601080105010918020f0f060a03020904060b040b03070c02040216030305061f020706080a0207060c20030309 76
    0x34001501c554800c030041e150141c0c900d00180d024030441d800070500185280d450900003c01106441403850310b00805c00680c0f10754a0ba45000618a0800001d41ca4a5410800a00c01281004105035164000d41460401c2c69400a4909030f11003804000344080081c41c007243c0f1102c41c03142116442402115101031281d900024002e03030b0740321803015859090b903000742c00142d00d02c00c0106111444080e6107584101c203010f501110f51030840000f980d00c010744218400300d4100f1914070740e03403103454003003101c244406191260001b020fa142e140703042da2440001d004142032a240107803141500e000703000c11900140c000c180c21f05801c010500c4030061200c01d03281e001c0018030700791420308440d1000c1400b0b4010141c403075042c421121040360800d90550032091089406650700780c01e03035010050380d40e15030f804030190710b000d600031a800b13200d01c6209107403161340113020000162414440d66244012121040c40c510005900303640031006510100480d0560a500040110705508100340c0d1240c0b204012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 161382185 1250 161380935 161380987
    0x90206030115140403050a05060f060a050f060d020f13120c171e0705191406031f030317060d031b020d0501020703030603170304150207110a080f1002 66
    0x30b00808003030038411210000303a4407010340156150b580d2450110307500c0c404004101c0f2240100340000e000c244806d50910304c1002d000301841165883e0200f800310358444084403503001041003024101c1c2501a0000f00110700c842ea01803599808600d4160f003e40c41e16402401f0401071901601012440040c442004d45408202440342150800c901ca440d01d07580a004e80011030300700700b100d004402c01044034812600c0c01d81e03800300001c208002c401e03100d0740030340100c6d01c03180140d4810400605010300559031021000f80416096884080030460030f1805501c100c000030716240381030b4480c0842d260020740201042d511044a40c0403590043c1403206204038000130f040c0804a09401d641d01d018501d604190440b00031962110903080c010301034801130105845003001030b4582124010a2800c8034400c98111101480d4803201e4030603a4003035400b07035038140c1d80100400e914801ca551480381c0d80000f4408000101040b0401409090a10846002222040c0d01c103012004620005484e0f811400440c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 161383435 1250 161382185 161382209
    0xc03040302060c0c1603060507030f0e030403081e070807060b09060307060e13091101260a0902040e030a020d020c0307030c150521061806060a08040819020a02040608010902060301 79
    0x511559280380001e4042c50b02c0c0522070b4885c0c00010f01c0000c2d888140242c0b400d136006e008013091680c00a05940c400c0268a400740d004110030408103007550301600180a0200e004180201d004bd0340d040c040d0040c10003540d450780005500d800304280c500c04c02c52082400d881540043c038107000043d4561130644100014402d8144003864a5960755100c0b0049080f40c1004118910503400d02e40202c40030300d480c01d40030801755002d01c8408040c03000a0140440040c0c00d5048a5581000285c007804100c0f0080b82c01540340c40420480348805e0001d001c0504440d80180700c0758525507402031620290b901e841d802500301c000188042003c103050101644c00990760030441d19180b102c1110640300729003030344859543c081029401d110000c140c560240e1802c0760f1002082e0801c818000700450151803d070b50000003084116171943c081d40c00264800d002d083c40302d08140000024030380d40d8120403030b6000160440086a8114070701032003600c02038800e12008100140c210340c0854503508c41030080040c0109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 161384685 1250 161383435 161383447
    0x1a150f04060501051207020c1005030402030f120319110f03040204060509011202010c0f0b0f0403080601053c030a0b12010e0703140106081615030e060c25030c05060c03040302060c 79
    0x100810013000480c5c0e025120144c0802c000b2700c0100603400c1501c04a10034020b140c00070302d03800d2000640c0500b0702c2c9410141461030b202d0b0742c1c82c1c00f518410f20b400404030545441000e580e00c520500031b001500c1c582040580e503841c25104220481e080c580000f489103007480c0051180c150311845a95038141d082c200b491859225003030010a41801e5180103140d600007004011545101079000c0d8003403407087d107803000e454403400300540d82401100308030640c41c41c07000c1c001e280d0948118030380010a403d0308036040c6400c0001200c01c005a1084907081e26843e1a0883c030805404e01d44030f40c510380024075008202e54205080e45949039281d80c44041c000c264542d1406241720001c0d44108010581a0101c80c0012441c4446410324136240c46148514499141c0b4519498028042c0301c0034094500e024225554078100032021030b0700161034107084103490441d007851032441080c0c1c10190768001e0300c650b91190007910b455890181c00600342c1207203040a10500000a40002c0d02d076802000c924501c42c1c96603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 161385935 1250 161384685 161384687
    0xa0c0b0702040b28090c122304050f101a060306063c120117010f050108030c0706090e0c0304020f100e030712031b1a150f04060501051207 61
    0x106241e4030301d078040e4a440c400c01080c80442d00c800c50300c040c030700c820500f81a643c1e4245802c0715046c41c0c1c03030404a00d10f000d61030280120b80e4020304207220070700d50380541c20b04078808180c0c030b030310301114100c0342944800c00c0094030400070018801c0d40324421005000c008041c080c1300c041c65810720300f03070740c0210320100c00308800d070382e4240c15540441030b0340b15000c1c4034043e40a0380d405180d10440394811940260500803102c41880b030304998500c40e070a881c1034410b134a40300c980449640145e444d0391540d5a04d010300500c410160080e54028101c0b00019516030300088405410300f5075a034008000d100a4100802502d81c1d468002c5511414820340070740c481d512800842e42080a18600303560007004604684601500720805032184a010360460322125115950101d0b840c4400c140a004150481c010040c030782c4a6002d900411840303030044075070300040c1d0126101c0c2201c5c1a80d208064550107844d103245810302d041911a159000c0b2014841e00d4a400000b030118441d80ba0003580d8160360380000b510302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 161387185 1250 161385935 161385941
    0x41a01050d05090a080d06050a050603162316050d02010e2a0a08030d05060f030a02060c0a020a060503010812031b1813060807050402030906160e0306070306090e0a0c0b070204 77
    0x42c642000d05540d68040d46e100341c0300207110f2406514030a1843c0310000c5210304045041d0ba00c00d0000350030304032003003501c82001e86031448c65202281c1e10920705503034058610b40b00d40c0a0000030302d083c2d01405d003560051900701d0600000e21010402c5a01d400380b89280d0703580000e40f8201b0f007003214030818600701240d066500400034500c403154110300f00610000c0c4200e000802001c140c1642ca4041046844035800c119610888503203055040e449144500c015162103001000e41c002e01908544c40da14060340400c8043c0c07442d80c0040c010560210041040c0002170100640750045c095050340786182c020381082c01c801030b50660800d00c42d401310307602c02d00181c4030300c24280440c03000b810300c5c10703c00e500140c040140c089801035180c1c40c0220000003600381014004e480c021402c8402410413a6600c00c4603031605150922014108150701d6088452070314180112401a40070380d501045d464100628641a507201b0380d400744a99011000e0321012130030003031507041510052803080d5610b10560000a003e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 161388435 1250 161387185 161387203
    0xc07020402180f0d0201120c050d05070e3c010c14010b1207030f060b060f0d090b0f07080609070306090f06140a03080306090a06030b04050c041a01050d0509 69
    0x54030018080c100c0c00c401a510082c112400c660650380e004156040c041302041040c0c0080c00301d40c213010070101090041d0032021400c0802d180c03450414581c00c07564019104181c0d03c0001180d00614001118101407840d51101504100b00940344182040c50003074403240d424400380740c130900a110f007901c1e0f0321800c950205103401166a1501d032100e4211280281032b4050b0041c8140003c02c0e40d00040700c0007140e9002185d4210100304c2c103000d03840d168100070b003c001c40300036407000d01004140c071300010a43c05005460f821302c00000341003816203003543c0d40500241c81240703e2030100c0300b040390719603001e00c04030352011050310b00d02c43c103071600c00069000d8181d6810854019040c80c0f01e03a102940e05601042c2203506103060106050b503401d051102d0030406010150403000200700160690404070a51070700301e00d2200f00060100e5503500c5010520b40152800c45440d0065258400d2914080c0030b9409225141407a40c641c4c01600800a00700d80f0880704001d08980d01c88001501e00c55082c046900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 161389685 1250 161388435 161388439
    0x2040501090b161112010f0b190305070504020306031908131a0711060408010c0503040213050601080a230403050c011b0203092106010803030a05100f03030813080c0f0712020303120c0702 82
    0x206920a20750300300948640030307856015503805460303d01c9c442c20726600541102d4201014114450401d000d100296000402e550340511902892607400150502081ca42d18083d040841c1c452042d40c240e0380c102c0c20903901c2400d450400702e0030801c80c0006275040b51040d03940158044000c040351004683d141c0110342c84207d003940b8207404c4054140d0070000035441640f086500f00d2400b000c00034101d0446106482c000d00085108002a540c2002e0fa0b2101d030100c66021680600145007030164200d20f0340c2103900310002040451212445402400303080b01d003901d003c213161103860690030001c2d901e00601c04094803403142035030b4060b00d800b82a900450740e0784955050700c1c01586c640030102da8981c82502d22064851802000a20b0380360000d00c01c1e01502c03c3c03110045203291440c2c170210341c072510291656520400d05000040064060002854120707111310241003001c50a9040b5814551142d00c180000c049281d51800181d0340402218034079807208000c084a0b40300c40c0100c1269000742003000b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 161390935 1250 161389685 161389691
    0x1503090c0b03090f0c0a06020a080f070c060906020d0e030c06070f0c0605071a090304060c03120e010f1401050d02061b0a060209311a0303040902040501090b16111201 73
    0x60205000c40d038004c2040302c80d030032103020f8403960017405401e200034407502006800401003040040c1c0038400918010186941c454181216611401807420481c1d000d43c02080f0004002c00400b0303014444400341400c0740c1481440c1c030240001203a140c16280310100c3c807442e40042d94804212429201d400c140350803480041007141ca07558003800c150b001c0c10f002c0c0d444001d000d4120a04618003406d50f4810603048028601b440d00d0030900340e40300350355100700b142880b0414110310f941e05100c0c8202140100808000b0910803540e80724481110028005405080740000040c403d80e21204d02c940144c42c2d06a41c02651031070121030700421161405800b03942030180c60211010300c10585c0140924410032140800400c02c9900c40d180340c4c0c80c1c40d401a1002c4180744860415002c41c0d40d019121008000703c0c0f0380011000d40c0006403c40e402a0072048061354041418041541d000090b02c1c05041c1c0710081c903181c00450440342146866113000140b01d06441c42980c2d02070741303418400501054900c0001c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 161392185 1250 161390935 161390941
    0x9061906090e060f01150507120905032d030a140a110615091012110f0604030615080705130c050702090c030a0e01020a0e010e0a030f12020c0a1503090c0b03 69
    0x20340d102e180a551540000b2004c41c00401d54038840c460f82151030a40e07440301490003045649030720350405007c2d002c0040c414054800500d0750ad05002010402d64640304520742c52508820000c05500300038035004696009000e2007828640000c0030360a8004505a095196a49070400f140c0c03604000e505401d40e40242018410742e103240c090703440c6007003108403813480d05a620100d202036840c1443c402c07400c41c00c40040010380455019401d01700c11311405001446074440d0072300442c2e041d910941c404c8a16640c1e5010041c03402c01d030300c05100d002d804484060703c003240c603001c001f81d0181e070b102c0b0420750040da4484000544600900c101c0b04003550141050780940341181e456401070300122002c0c5021410150018040074040c422980098000c0d02c603c002402c0030001119091040e40c07003540c000b2111075010011a40800c10b4550142c428081d00c1e44401080c40000d090103940900180200701980007230040c1c84080032058003010741d0f483d000940d0740c5642490030764844540e00c82041c807c2d0000074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 161393435 1250 161392185 161392211
    0x9050d061b0c050106081506090402032d21070213022b0e07030201120b04141312090305060708070320030a0b06030c04030807030c0b0f0105180906190609 68
    0x1510b0704280140020010955908806512540300001c81d80841100c0c2c03001076018030b03000d601e440c4c00a00250407a45407401e104030240c01201c004040c254030800c107180481c1810020080d0503041e00104510501e51090400400480d01a800000380300318034160110b4000701a80c0c0c1a28040102d59103402030410f1400440307200d41d0700854409414500b05031052411030000192081140d9040e5034000c2d010440259120040402644007544141c4558580700c08001623040e0300d0080c1601c0012215820140c540000030748404031220040c8009000108041000401c030141d122006092000702e0365030344842280140030090101d00c030004803d69101688864001440c807820aa00c81007041035a09000c01a10380001c0b2540050745e0020407040c0001180341d4080e0081b40d100342464410441650781d03071090074000715400b61102c4000e200410031440d058914000c511449030840c80c46040c8030080a840301e4008141d07004018000b80c0380041810141d1029008100840c030811401d039040c85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 161394685 1250 161393435 161393447
    0x702040e0a061112010b0909160504052205060307080d0c170c0d020709020f070609050705150c06070c020117100b0a120c0207060f080a09080409020a02010f02090109050d061b 77
    0x608980c404011340020070510024000c990f0240801421001160b84100850800b0403071040c07041e0800070280300c0000c8680f100501e40c00d0312005120344011010500c0c158134116103004210611a038814a41008030303410201c1d14030070402e5a450826047c1481c0c0c00d00002c40d0300310300c50301d20030701d03400103030030b0b090702c0700100361082c1018030ba60036242a207070b48100c1c04099016800c0aa550b0985c1040b0b2000016003540c0042403862052054400c140e5481b80000d403003460044940c02140d0f0006000c454940d024030000fa48003800d81091620356501360002019112a508002000340741f007400b049a9a160020700002080001c0240380c1c1e442880c0f000805030310340300300d050b0600790404005400e00350021460b00180d410076904d100d0110700c1c0030801c407400b00300500300001031070f5150a1400410038010045c006003254030780240e901c0100c00002800c40303c4980352200321610502840700340d41e900070a42402c90380c0403507081c1b0502c00f503410444014001d2700340e045242502d0300c11001002d60858 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 161395935 1250 161394685 161394697
    0x8090a170c09090f0c01120e030318190b011202010306030605190b0904240204030501090305090f090f13140114010612020a09051002030c010c2003070203030702040e0a0611 76
    0xb5503040240d803214070b012a42e6007102c100e50b280542010034607003801e500c1891080241100d9040106400d000002068207540c0300381c51038081000c8840146001d414100089400c26104c004019204412500c9404483c10103000c0d01501070350a2280c1000c1d68070079004900034640080080005003000850b58221403001c40550000b64140446071382c0d2881d08d008054815a00409a880307401103414416a84941849010003c194203001c0840810405d10652010354405d441c3c559036080000100036104940811080c420840d801c1004802031100381007941000d0041c171104410141031501c15011201c0e5555084598680044000b00343c01d050700c60760480304544c0700c1c8000c40811900303503010f1f8841e07031032020b001c544c00400401960920740c0c0e061036520b900388140c03410880070303007001c0b0f081d2554405014000340728a8045a030203030301d00034800d41640c1801d00551800b9913542c0032035241d00030740c0c00c0039100b580d1760fa450b2100d0000602807800c4171503002705e0410a4518005024032180c0280f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 161397185 1250 161395935 161395939
    0x60b03060307050d23190602070b25030c0203070204053d030b0408040e07110f01021e1e0d0615030c0e15040b0c010504062708090a170c 60
    0x2040005150910303013604d0900c0c540001d035102c0d032840107110411840015042218141c85a21000908802c00b002907804080c03140e071001d03a03101c1c1c5504003140041c00140c12004294000c2c00c2420103010588103c1451842e103040125561401ca007080c0c2c00c5014401d40030390407a00b000c04120701240301198005c1d20301d10001541c0709046071054200c0c4000c0e0015003030003104440010920120f044044030a520a00c941d030b2051a140d20707204412540c03e025510f0f140407034007002e4041001c1c001802a00c00300c640b03540085003000281c5c0c20318520890350a0b03414101e0100020410100c1ea50a48108440040284416680c401c01016034005040900c209480e50017070100c100107003403181c09810f8080d80710340d440d50b50202030041013041c0071302035030940c0b034400500700301c000b0f0221444005403403450000000019549410300f44002079841e043c00400a05000c460380320703900c11801908050321600990101d8480790f01e18007040c0030620b190041c09205881d41e400c040203036000109040c0301d40d01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 161398435 1250 161397185 161397193
    0x1b030c11060412151104090509030f0a02030306180c0403060b1f020d0906030b101b020306070c020111060705030f040501090209010b030117010b100c06060e0106020618070e01140d06060b030603 85
    0x2410800e003003181e1740300d180780302030700c008000070004e2420359003200360016842020b691a082d50300109030780c00c0d44050440f2026030000300070008030b8a82100a6800002402c0d00e04065282c0304117a26154811800002c0503155554107280b0240c03903251301175450b421090394643e10201010780103541c8041c401c0720707640010101035000c034501b8880d0090b0000c00c4005000352501100025081d074408800e40c0e46d111413a80c061900b64050381c0d0400001d8040d11a580300e0b21040740481c000140503c10188401810b50310a03020700c0202c541c40b03011258008007640b5520003a0b1a286030450140040a4000c0d522100070340c004500b641024000714100d448079a006d030f01a000d901c115500f84d9038841062a4440300268000d00c01d18041d10320b40b1312081c49920001038490300c8818074500c021082c1c00c2600143d0201e410090300c0d65204002040062801c4010100d00340361500e5140c0243c03050082113824180d89131000c0741502c8041b000140d999100200307100491f00c03000e40602e140c000703c46145c86445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 161399685 1250 161398435 161398463
    0x250503191205130909052b031d0309121e0303271002161a01060e0a03050705010c060f0e0a0501060504140a0203100305070b0a030c1b030c11060412 65
    0x10203a011a5450f448402c0c0d400e8400f4074001d00040106520340c4141e034980203044011500e0111800100b81280101c0070010409682c2c1c04000c0449544462410580709568600d4014000010070b0342d0050004543c100c131400c1c4c84a8009007443c050402c59200c1000f0024600e0303800d880480074500c00c114032a4107c18510181c10741c440500301c0f840342c40142c1d4000b607640c04640d4006400810f0907030544507058812400e0ba658090102504903030640d4105a41c0d00140300c40740c3d1203019129080e504807080c0950038155202d80d03480e00b4662041a051000940803001005a150050305a1181083d4108081141509455103d59119a08440a52070243d002c48c1c40d251920904084c1c0c1c11916100c200d03036441c40780038402544041d181d164070300700f82d0000100013001000781401a2544800f9a5240c184c89400901a11055520b032030a11100355002c1c4d50155412a410000c0303074252400044158042c20442c60b2400e0170b0081c6a00f04400140115000311424410710341c541c4104020303000c4ea1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 161400935 1250 161399685 161399687
    0x1c030306091b0816030b0604060201060e010f1a03041b030302012301080705040902030c0306090304060806040504030806010302030a090b090c01021c140a02010e0a0c0e0f0103052505031912 83
    0xc00c14002d2100494000310126035010b41e4107a0340741101a035030900080e51520307100003403000d400640c042c00040c0e44414003400f042c070b0b4600a041c0140700c03100001c041e990503c5805c1c1842c2c0c028841c10f40c2040e1f004000038050042403003101c07842d4150540b208100a4503410000e000e410595100a6a400400044414000c031006020304982021020303200703140c100b2080101a10100205070b0b450f104041505006580c248043c80c080e0042d00002c0d55a289403450240030f0a030f009005074811480e081c1000302281d04654025444402460300603542d980300202400101031056015080c0c1c001541046802c076000540c0207241030090b000c0b00e079018140c0181040b044a06040300c40090f81c810040c00c281e00391031003c1d0452252a000101d007002000c001c49180484c0d159083c1c3c0c9410822804005001c4803222090b044624130341844055811741c3c894543d62443c8180e440d40c00d409c05c901c403d0f50b0100410351070019040040c00d032401160204400304804007604002e0f283c000f03840140451507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 161402185 1250 161400935 161400971
    0x606030b0f0604171606020619020901020a0b0c160b07030f0203101202031f0b01030c02010219050f07050601170c09042f06160c14060405040504021c03030609 70
    0x11000289001d03d0981090641162600499005545813007600d990005002c00049000060803044c0e0003000c803440c124844100c08241d1311000691144100702d428141e0368049541c00c01c1d81d412215240040c1c8888a405900384180c041020307561414400036010004c01040d00c41c040d59440d03400780b214241c81300d0300b40c01324413094803041c21080f8245410848030425814194400380002d0a032100c5181040d03a04130515100550015110380c1c0d075a82e61f51a41c4c0501c954402c403203191000b1418031500b42d2031240c01c6045401080c042c00400b04404401c2500c00007290446030740b1000340c440c5540c2d54070003220000464444810240100c40a00c28a4207007000100c1c0702d40e8000580d00d400200c0c181c1d181c07218500d0f210071124817005020501c80c2c1074807614000c010781500366000482981190902c092545500d4201c005e4003990b546151505981d00d0003035900b5920f007141d002030785448920001d240c0d900070a1142d41d00480c00b64021051680640c07005013180c8104c2c50611004a054440e0075031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 161403435 1250 161402185 161402209
    0x5061005060304140f030a020a0507060306060f120f020708091305040309060c051005070e0102070e0c180a030c0e0a0b03030a082a1303060e0c011709030405130606030b 74
    0x34400b0710001d000f10f07000640602c4450b01c40301c181c5110030000c150b090f0840e0702040d2003001503030001750b50000300001080714400411141c941003104c107040000040422128854480c200300a0301c0c0f041c1038000590340a44214264030100b1551030041c1c0c80c01d0b4525812000780248210341000b0080d81140f01c40c02071610440d40340e5551101c2e54100700c425107406002c0502035649100d00c0340b00034034920309446401e0103a441c5480301003641588000084c90f1907503a0700024018482c140502c9900400b51041d80c1480c0c07100b03001620b0701d186a03000303d10051690360000c2c000c0100340c1c0c80081c005410100741402106050800c0c06251002000d0550743e2051800110000b152a80000d560f01000324408260038120900302c0c80b0031a042055804c250412000c031314201d02c2245003002044500c2c41107030b13015840f100180c401498004006400d0b00e1452264610040d560307c0000e20a034420304c100d4018040090007160440401034521005220398016a80461314140d00400580707841658060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 161404685 1250 161403435 161403439
    0x1206190e0703080702060304031b060509190507060e060d05010609050316030308040f02031e0102030601020c0103150e041406091005090316110609040e0d080601110703060203072a05061005 83
    0x11404c6129400d01c85036601c0144190208485418444041c242224142000d81d004c0d5002150034142261614203241071504600904021740403500c002840108642c5c00301d0b202e03401c009070030a4107a40855010b1144000082d01d083c542000407844540158200058179001e4040382c0500128004011503040c0310702001e00801c2c001e9000030001550245881e0120744041d0075203001c090b641c3e5000118901d030b50403003002ca075004410411a940d04000c08181c104003440c1c1440008010181c0740c2c1900300d140125601110300c603001a0512079088280e0100c5181e150444000b46010b400464030b401549641321412410440490701c07001000044e100c04104900d1034041100721940c0d01c16020b0000c4202d290080c4082c040c1c00c03241d94070361141c050501041070240c448200d0345c0400801003c40103140703034180542211030011100340007400700262980000e00507529290751805079581d00650036102c5d4140c500100c11107050301c4106486084a1103001110340640b20018220b48816450041c01d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 161405935 1250 161404685 161404687
    0x80d020d02030d020703091d0118020403020618010903020916021b06030a0c09180516090e0f130c0b071202190b0a09021c0308070f08040b061206190e070308 69
    0x103500403d1503030041c40a24402d05107001d41c1da59845036246c8581c00280343d005180e4501b4010130800c5030004844545050341841103207070030704507800610140a40020201541c40482c0005130590140452802441c2c008240c0007030f41c40c0036038000c03548420403440c100c01405a00040c03a88090004600b0010031001002107082d50741e022701020041110f51801d404201c0d486c00001440840c0e41c22640d58900005004110740c9400c102c00c0580f0000c0b0303407040f0200602590200102c20815807201d40011916900701100e8503061407580c41c41c01d00362400741524034041c0300000c40d051004c4c01004014458503c04084c40b0341000103a0315449014200744450199038100c400040780e03071070259885424200d00048048861b00400c045c2014145800340000e0001c0b07880c0c043c55003290140b540407d151429001c10003507804002c1c50600b0140c40189402c16074008104656200c20b00c030803480e0310074000c44145103080d50708200c5000c0440e502145480c42c146941d403c40301702150060a40341c00401039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 161407185 1250 161405935 161405947
    0x60212040f170109081b1606051e19050903061501081315060b0a0912031d010314040803060a050109120803070c06020d0b01030f0b03120c030f0c07080d020d0203 71
    0x90070204501e18000019541c13500e00d00c0000303a4810203002e0084403040340311040400f01c4040e80c544080e02c1000e94501c440610100802c40d48a002c4440701c483c0c40b1010f06c110f58008001603e0b40c001d191050310f96455208400030a00e0380300014040009040f0708441d216100c407540c46600401c0d00e0309490018903240300082c41c502c0441455001075210b0b03012182400442007a08045496a4010702c110700360015481c0d00035a80621040090448020404088801664045d100c001c02c4141007114040b000d500c1c0100781c2c0681d020800003440030700600f400f03103094500944107502c00c45400d07214820a440220740c0f54800c981907402e50f0740c411081c04134604039489010594100605d941d041004421240c0002201c45c00a0040840c0e4090042070b06001040050305440071440310011683c9410304a401541c1c1c0003a408440d10341c4150440d07030319907000e01c0c21401c40c450403503088008003001034990706650002035100104c0700b2420030342d00c0c0b483c66038504986516600e4004030060740b0502403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 161408435 1250 161407185 161407199
    0x170705061b18150903060f070314150420180a06020f0a02120109021504030c05092503020f070f02120609060103060e0703020d0302010c030b011809020913060f060212040f 75
    0x20205a0ba0000c070000e608160082000920f005000c44000300807018040c2489082354043c019840036080b110000d14807450207400100e14810080c203010310441e00c644c0385080b0311f1101c0110003444100b94090030340d40c440507800808a810b5420229010f03445ca250000380c03440c40800c0000e440030090015018040c400d030200807000c40905d0440106568840079140160f035044040c2c0c0c401c009100706252924950705000c4807c40f1664401801403490700c04101d0300740f22041010103000400355903180d250b003000000318000d006403c00d00349215000079925062011103408448440c0c0b003220850210210425510f4075580191052185503003c07000600018100760842040d0002880032038115990341d03000182000f131100016400360351769060110b20f80d54140550210f110b02820040d0480d820740f401000c171400a4410008950b50114400c05240d440d01c028600d001c0800e0002c4c03050540b10781000b0ba1041291090307001510520703c1c0341d03540b01d480109940403207060b42400c00416251001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 161409685 1250 161408435 161408449
    0x503120309030f0c060411010314190605041e1802090412110d26040b07030b0d02030109060b030601092309010e0105070e01090b0408060a0207170705061b18 69
    0x1607007040d0301041c08401585034007a4054503000280360024402c504181c00d24449070f802070381d1072604160410244020034184d418440b030b004600c1c2c910b86003030101104034010007894190440c0c0c0d440790500120100181d10b1300008c07490031f14010b10410820892898840e038121182000a4000042000040100d05c40780650225014603060400c51440154200e900f007502480940e4007050f14012040c55280c0c081d800c40044042c1d044c0030042d0b0307041644640c032880c48010051401c040d00c44c0c1101c1219141c8651707044070294090700a108105591908038042c003d904101800b900c140000003414003458000c542040f00200d00045060700b41003100204d82c0d60042000314a59210380203c41c4c49403091190381c0c800e41d9150f0340c00609900300c0000500c845469800b185003e40148000e00012801181c0250002c00c00000180d8a504514202c02000e40c0040c001031000400301e915000d019011032481c1c428a803807554480c41050400c12184d447c014602034115900481ca0030012a0030070b64 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 161410935 1250 161409685 161409691
    0x30b030c010e03070f060801090606050903060604020313050f01050906090601060906030f021c0b0a1401020316030c0221101b0c0219030f060b01050c1906090803090a05120405031203 80
    0x3c0c05075402c203511034490a111144581c17004002070220801000758030420701c60540584000c2c50030038504400580000d81c1c410000c3c0c8100d219030740c004007144082c0e40e417484800213260301c4030580764074a0000990314001c240c1142c2411141c020200010750b115400b080c1181642c8060310354244181c1840300890051400d80c0340f50b40103650070441c6403006100844512003011a0100200d10004900d043c071a045619034000f62001407041c1c2003034400e03a004015201c0d0510b1541d100301100915080403160081c1800d006034000c2400c600c08000140341100584c0700b42001821102144104140f5104079421003621446604041c6003a160032480307007040303034012800100071900c40e031b043d20000104250260300403500c9040034818242041a240605c0d1481042402d103e03007010036005aa54035841501e407461441400c072000c070400c0002d65400b546da402c4d00401d00ca0303100d00d0b01c20121f40d80d480c855107060300c5070f2068072102d80c4012448001c40301554000740c0a80302885446250141c960009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 161412185 1250 161410935 161410939
    0x3030954090c060712030b091b1c091a0601080c0703030510080106060e0405130b0402060309150708090f060408040b0a030906020d02070314031012110904031e030b030c010e 76
    0x35188880e0362844080c054480c0164481501c4280c282c00180855290b455441c0c002c1c6148c408106860003803800700c001030090004450784d20480010001a440c07124984011018940120b003414024a0703002c0003252012a0000341c1d6944450005503611041180c0b0b40050407820000c1070002442a005190042e19285002504c40e8841d500c842c03d603481c0d5040000006c111a0081d0000d01d068010150402440d410b0640c100a50703480f040f45549005001074010300b00080820744030031302003141c65014142c1090401c01030404100040c0041d000b501d0180c40c6101d40c610b10f4103804c2d4086816401941d01412091415141c00c02210712900501038420500d0307980d1182a001c00c5070360000381094a003894005036110000d240141c0f0000070410103152100c414001c2000030503d49072030f501550300103248042e143d01d452800300c850f00781000c01a0b40140e81c1b04144802c141d04540c01c107441031a2030001c0026000c100404604076080040840d40c5030f030082c00c2081c9103502030303030900701101c86c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 161413435 1250 161412185 161412193
    0x114061011060106050c2104050907020304090e1c020d0804020f12030c0106150f080a1d010c030c1b03090e040f080a09030c0914070e0303095409 64
    0x401281d5062003026805040404c0d400143d00401d0202481204045215101c0c0100d000d0003042c40d0750180e00450080c6806001c00e0004502c4860080068074001d1030b8407582070000054102c03180740c480b00d640651480134855144d140509900219520080743d005a880500581e41c1f6001c01a00700a941b04654003c0e44403102c009a21740184020289910803400205c2c02515050341c00311513a200d400d1540c100121b60f0751240101f0303440075000c0e402c18000305c404120801c0c9243d007640b041000030800c0c165907180400c118010b64041d0401080401c0d151140c3c210700c81c6900d924601007880500040c005034440c41305000316010b1859250300180142d1802d4400161695120349035800302060b0740105a5580e8100208602c8040300e5000c1c0c40c64a5043c00005600b2000003036841000c2c060206102c0d50108404a035182082683c117103000082c426401003803201c02800c221007581c8500000b091034100700403040e882854100e480748942400010100d0100410442c8501c800703802c095107801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 161414685 1250 161413435 161413457
    0x6061c0506061b06010503060610020d0509130f0902040f2c15070c0b100b09120f010510030c050402030c0406050310030c030b01090c031505060a090807030b0402090901140610 77
    0x91a104604040e1180f5030041c900355042204141c5450002040284507413086144181e88980c08074644900c0c44413814041d440e002814009022101d85200e40d04209240c050800c8030309801d60840078420f07009a03000c214810882080d0b60030384521211404c8601e0041004841082114214292034000141039030050f84000c480161000d4080c1c582c9000104050498818040040302e100c1c2c110417280300c1144901c2c940103000c501c50040c00500c500c030f501a6910f01c2000e8005114244a80f01c0780030007008146083c0e40380705100d40f607901098910450175000071445081620803a0702469070001003500b02450150111425400200010504c80315000004006901e1244000107540b1504400f525076042c041d41c00e08886140141c4000c240c1820316030100d41134090411002d0f903506075171417952004444d40998101400381d0002416104200002003070002010200d801188200c0701a039145e21203000460a03240c48403040500d10071104003050080c80c010240b00e50380c41131420318462401e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 161415935 1250 161414685 161414707
    0x5060d090c08010b03120c15071e03050114063406020706140c090a03080a030e0303090309030c060a0e011b061d210904020a031d0703050606061c050606 67
    0x200d207680c014080c40c0c2d100e00c84501c1602d410b000720302c621a80031074424204907500d614a5940d00f590f01c1c450a41640810101d842c06108804d444591051600c503054079800110340200200401d1245044203600780029040c03d15101d0704480d201007807a01041019128100d07810b800251150700001c810100c10009000602c0034000340c841c403405075000195540102d548071080c92001842d02c00e030b0100130032141429549529862060725000580c69468820b2035105070300600c000c0b0401d1415110120800c0088140000100f50f8200280c2c10340301c481a1480600c0f591f40036a5400c000401e146107101c0c051544100540301c0700c84003054201058003859100c02007240c44040741003e00c21070012100c8224001004014255040e42083d0f0004111142c103420290040c040c0052203503400140c5038101e24400d4102044a801c070554005004031801412603442081d0304c0120341c00d004110000c1c0c580d00c4c0c0074054904520f064019055010000034006008200041c02c0c01d903c0303142030084001034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 161417185 1250 161415935 161415953
    0x200118030c050d030e0613080c0f0f160f09051b0723030406170405070503070f0e101503090201020a08160606050906030a0f0501060b07061d0a050705060d09 69
    0x501039250741c07001e4501030a00600700180036000405142c240b042c484100c05002880561201c12402201c0c035103c0d40b440d04103003901c503504000c02548a2400d640d150b041c00031580381e000c00d46c14805c0b07989220030140e41802d440854802e4400041960f0002c00016580342c1046601c1a00c120340308540a03900b02c00741c8e44540245800791024440f045205c0c030005aa0f08211100607040d41c015420706140c1017000b400810b0032904000c050040f070300410200704041094070080d00000302910413168a410300c44c14204400d1280b80041c400480100b071030490f260798000c0507640d60318040420220307030b400e055002c1c00242004904601c2a50315400200c2d0000e030103403040494090002c03460900c982800000c0d205140c01c01803080c0355010038480e07903560002e5035140041e8402c42a0007061490f060480c0140752550142204800008135001000665400482ca038004510204400c55103400788640e18000604010302552100c6002e1207e403400c070340030b8120301602d0300c004900d910b10307135440c4591 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 161418435 1250 161417185 161417231
    0x20904031b0501150905090120130e0108030309060c0c0717031c02040602070603020f2a01020304051c180902031b0c03070620030a0216050d08090d020c012001 70
    0x40d02c13a2910510046007140546a0000340030300080c4546107000d03228000d5a40000f600840340b150001d00c0c01c0400074401c820320010403801c03445803401e42e5944c02054a0390f0044a82414902490000401280080301500d0342000000010300d031840c1400301803102100f04800d09007a0344020700140d0b40e6040071100c2ca002240d030712400561600e2900101911b400000d0304041c1c28180148100540d001442085c0c07808403144881140701704103e41b544000038a14815400104c0d40000200020b00400003120b1914584080302585000100b0108a8201441c8682ca19007070318110000c01040e4802d4000d19000000b4034220b4102c0741c1a000795203429482110214100d41010940030144443c81c0b08000d184201a1b0035486011203d040000080c480107162000d010b9000c076007030105460800345505040d501604075034404800c81006004a0700032200d0301d6284c8102d003405024588041280010b10700103071541e015510102c04072a80e0b20003460007600d8199600c0f84c2d0102044401003c0c041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 161419685 1250 161418435 161418461
    0x30c030902091806240907091a040e06060313140304050307030b01090e0d0c1203110a0512100b090f0301150609031407051305060112111206030a020904031b0501 71
    0x41c80c03c1050f8410303410004000d02c03a4150260304407042059100000f040d1804a0742201c402d5101e94a41100f69035200c034641080c8011b2813052043d044900c4010000c006030307240464019280e5480300c1c1048414482240e03a101c0b10180060b11400150b41c070b00d03582031104002410f036820302e5214004a440d21405900540b0b000f50707540e0041101c00518400d0b0415401007030082c00c005111401c014003015410000104029080b4081140d224865031200c0c3c083c40414001540d2034200e000d00410340e4000700f00c002010300746140030540c01040902e5460496001362042da0404080c1d00402c9240300e02442d41c56015500c480b207c29900d0f2903011014050030864491801d11030960408000340d40c80d04e06c03001d00c1c1d07a20a030300a01040c2d48801854070550200e88002c640d550315400100e44d00b01c1c4c064940e556140c00c0200b0308442c0c01078500600582000c004009610340d0394401011354408009101a40144504000c140440e02c50180200b00d280d100e4151107a844031075690508440002c0904a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 161420935 1250 161419685 161419711
    0xb01081b1318061e0e03090307170f01020a0e040f05040201090b16020904061b0305060303030a020f12070e18010e0a09050a170909180d12090203070e0a06170d030c03090209 76
    0x143e06084c0c1c0d01c00c949080360440c0c000c60500700721201180d40c8901c60700411040c400f4200074034a856400300f002d2503011000400942d1940340034100a4158035400300c41920032414240c48d1040c0400a101d528032954059440d04075403481d010341c00245900614244c06415210400d43c005600c0e0001240d000f03d1161500113200944014031042407040b03030400038109070502c2c081c001541e40000507660044101c0500603610610341303604040c248940080c181c2040401c81c10054550b40012140c8118802a500e40101094400b840402e0582c2406821500000340010070342d410000d40c001000144202d04982d101d01d0940c403101900130b8420030000e00340ca00046d000c041800c000c00f0468000d84842401003c61998102081d283d000c269154000c02104913184804030302160805104250040c05583d170320358441216151103901103446105807404d0410009051031440003400c00c0002000c084c0c520220065011005031040e10b240c0f00805486c2d419000160396460401c90251149010075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 161422185 1250 161420935 161420981
    0x3010905100605060307050403020f040612030c030207080f060c070305040807090501050310050106081503120705031308070305030f1309060b0304020f030d0c020d020d08070b01081b131806 83
    0x74041c0c1e80c0b03d40009000d110280103006041b50800180d0341500c1e81100c0e80c011604d61311011400600c2140d12a10481c80301000000c141a0404080c1107000d029509032059207803a06402540c56000c03212900840c2d2228000070300041103200a040712600c01c7c50941d14103641c8044061400d0055001031600c640d81d81c00411103440e040081404040240740144110341c50b00c0d401030310004005050721139188a1100042055038144030b90682d084c000342080340c0701c1d000e07405d00955a800207221064811101e550124803000c00003a60400c030303540040210b141001c403590086040c0c104031001d80610807100d60200300200c4074043c2c84003500700528040c0d102c0c506401004a00b0f941d10700c0440c0a500100418104507610040011851342c05032508944090349101140b404019480050036448010545500300881006564122100c1d403007221681500c0740f0720981041100b000701903002d01212200380070606c0c59004070303e040c247c0e600d44c00100c09864a8200941d00800509920789450980d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 161423435 1250 161422185 161422213
    0x20303120906091c1d18130c051c03050705010e011d1507120207030903080c0705090c0f03011725050a0b03040c05040b031018020f0d0302070605031503010905 70
    0x7a00505940214a4034402c81d10103005d40780440b8000304010100001501c46a152258101600b100b10301e1014808185009803807200a0000460101c400f8901100c000030246080030201c140b0540c007224400c03800800c3d517030030f565075030000d103007141d00d5520340941194a00b001e105e004044000a45084400e00141c03403850309140782c50a80d1060700328120180416541d01c0707046482460324040300141d850129050a82d80c018599000400d034040002c0d590580ca0030109050007210f03011b40c0d0a0306241c0340c00603001c180c3d00400761740d403c0405080c001004001c0b9045103801c1c400303100209890054501d10003010110340404d0b100a1031a020300d504016604103c00c400c40184411400380c0c1c107600b4150399610700d844d006c1c07151610950302c41c110100260340c203212000a610481404004070240940007141341190b04000760b104081e904992901420140c9506c00800e80c560702420500703080420541d41c5030000f42110803850840712200e0144e032000d12a0302200c0c0d0142d00200000150401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 161424685 1250 161423435 161423443
    0x6040b010914010612061802040e09071d041703070807020616120203040c0f030b040213140601210204030503030a1802060706020a0314041a0f101202030312090609 72
    0x3104095003071800c0301414142400700900703410354080c0e2030181200a40d1600017030162600341c00c2580d4220482c0d4800d602195958010403c8452860840d81d4540d100d00c58180c4400b05486902041c001803a000d81982904582150740140304882000111002e610140840e40084440002043e00030090000303480d01003041e25071000014040c00c0030303124400c6000300165008448a00c2076500880400e04003c19020003101514900c030f0308250080d680e052a03010130105640590140d90751200580300741140340100b6034841c407000c074610841e89581d4011982c140300c510305000c3c1e41004002c5000d141a42d80020701c01540104000c584038203081c1c91442c11610340c51a41e440750010020744500680703402c0b0554202907003080005840302900c84050f40940040d88070026071290072001c00007007055500303164805484441c02c0c03031441c1e9912414400a440c0907500000b51904502d0304224090011088485051010702a24140a115040750642100c00d9410b818140c002104124240714100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 161425935 1250 161424685 161424689
    0xc0f03031205060306100329100f081b0f04110f0706050c040e071809230604050402150f070b04061b050703050a05030c1905210103020306010509060d050f06040b01 72
    0x10050117040c10100c903011021155484000d1102410300c14240381e86000400070070050191044000306450000700302c030051402c81c05851401303171580b80c0124a4a60005070580f0014616002080410082e020496410880c2c040749502c40d0f01c6940b40a0f49601d80400303042d4466039501940d468140500e48503003a150024078104080c101070004000088000c541240c002c500f90800d4072243d02c8036000d10104143d40e030030607943e890511000e002c0d1884014843c100e90800b0f802e1a80c03c58840d1001c010036a44143c901940c04540d80e400803500700b04c48002061400820b5020702e15100f01642d40145440c0112416101d10390303076000f000810304400d44c070602c00800c207240040c80d20b03103190340107003050003500d00c2d45003081404400620350b2020501101c2a07074070810b100140b03501824000520b0b66005611000f6030128464000d0700789080ea02c3e2442c140c1340e0040140002d0380c00e1209000941c080144042e52151640031500d002c43c5041c061100c20810500103002c40c0c0c42c081c05c010f0032a036410303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 161427185 1250 161425935 161425939
    0x60b122b080f04020409050a17070605061906081e090604170705071e080a060614030708070902030714030403030c140903191b090204140603010305030a0302070c0f0303120506 77
    0x1007042181480b030441c8203903070099040302c00180301140341c2459172411005940007016009609400898003542d14040d1404910031482406540c1e20f007410302442400030311180b0401440c0700700c10702c03000740501740195110b4000c494500502000e1404525000c20540b90240107402040502041c03050280c0c20b0000147c00d448460f20748070720382d070715a0343e190854480ca541080418034104102400e40080d40d0080c03402c01e046449080460410800031f040501c6080d080c00610030964607642000f04070340d0100c0b90410081c0024510f0040038502039032000b04020708002c2c0e180a00c1c3d40d00e02c10040694080d0b070007613500081c140400e020182159500c502050805001031158101c284d800040614581c0310151407042411341a1a2101c80c80180401c41c100115200700e0105044005a0240084480b080b5415078000860414480d1504c401c1c0005021900100305000000e0b0294000b400b28a00c00c1d0f22404d0384654038091802c110700d035a0421030018100300c00154002c9110300a05804c8181 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 161428435 1250 161427185 161427197
    0x60c0803040b070e1e04050601080105030d0503090a0804060203031b07320105070c0203060105040203011410050705030403060b01031b2a0501060608040506090c0904060b122b 77
    0x11526100164080180001c01c002030103070004203807a02c1540700444002c4042d0500394000007509100000030f0042039803034082c0d031802d000192190301c1515114102c0d4005006003c2d99002264225141da0004181c00040d03c50f00c1140c00c0040c001078004c1c001050303154007454903070400c000140800044488a105e0450017400b41201080305c1041c080e00c0c640525031540d01c2c14070240d285002c101281c014061095217400c04000159400001003c0c200d4822420348660b80e0700c901c2000128082030003003260600803041c056016040540e407400e21040c480c1081414007580d6543c1c546182d21035081200d1054903116281010b5801d80520440b030004a0070309425041c58100003800e14821512400007005500e40d12000190b4010007a00da807900701000f448041e482e50005014600242c904032910322038000014800040030403003003004070740104806416115625444041c146640c1d6541c0e028001c4007690003400e000b0850301c15140c81316009c150900b03024130b2400141c440009812014031172 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 161429685 1250 161428435 161428457
    0x80607050a0203090d0615080708121305010f050c100b15180120070f0e07020d02061f0e09070501180303090e0c1c020306100f020a0b0a2009030706 65
    0xc2c002c803e0395296032083c0c07680c50840141c6d0800501410481104056024030a00003044520020a00000b603c5100c001c45900010300400c00074184240085c003100b45100b0178041c042c035813049071102e01c0c030600c3d46011070810881568980c140106003c3c6402200e03a65480c1c140c1d68181500f60325946066055a9170601c0c100403580010715813242115030410091006c07a884101e030140400d880d00c0d20100072107500c603454804000700c1c00e01c03a005500c02d0181700c0c000111028030000701450a01c00c0c44e4050310035511403808049040742000b01070780113100c6202c00407440c07100034443e80b4881d400d028010a12180b50600150901c401815100c2000131000c50502c04260408505011140c8903504041c49584a2840881c5800b503240c9841c41c00c00e2101d00c0031601452500654040c0e10102c0340c0d580d00c403403100302c10350325401c00c00c18001c00f5030056540c0700c2c0803409100e0504d6000134180303804a040712105956003104080207a240d00350020114000c200c070701701005442d0141c1101e0400300c5c1d501d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 161430935 1250 161429685 161429687
    0xc06030f04060e0709060e010f05060f07060c021219120509070611030405030a0b010f080703020904080a0c060c0c031101060605030c071b0e01030b060d02060d02090d080a0504080607050a 82
    0x3200410140c95180c031090880c0c00381204018803001403041c0c960401040d5206e0703404100300c8400b0b00c0b505143c440c0e80eaa001c215450400101c1d014aa0b03140d1810f481d10046659650203010464042d10550090000d8148007203110313401440e0824200101030f004400010000d001d9510540b601005245131104010810000152072000d4035454200b0510584400c0703201e6156105603000940c142c00345a880a08200720102da03203068645098450030001c2d182d01c0c0d03060b17890b031003440080c1d031040080001c10081002d0a00801a070025403230090705103245078503218281c40d010707150540002c0742002164241070f40441d400c040380888000900c605031901e5002401c44c00007030079071445200c0020716501081055805c0100d0840f440c450b00340c95950760038903440b101100b44000d5651010000000e00700e464182648170000fa8005e1501d030030b00cac0030103e03450000c2d0000500240c0010940c001180420032000240c00590515592140c0d15410701101c00d00b041c5000e40030f8030030f10009100e4180c0d00c7d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 161432185 1250 161430935 161430961
    0x120a0903050901030b030a080d060608011703040501050a03020c12030a0c030e070501050307050415120c0c0b151207030803041a01060507120302090607050d02011b05091207051c050c0603 82
    0x500c400341303008a0058082c80010341007002000300104140400504004050302a03000001143c070603444903c12a0380c0c54245641c001c465011143c2d0a40040100748103c1d030048000c0e211803000d03071500500303200c5906080b40c50300e20034000141c2c09d84c3e0301104200390f22042d4001d0040d42079841c9014404010351805030b80d07039072007107028460502c0f80c0800002c2c00c091080040e81d00510741208041030310b180042024250050401c800e0003e07034285814404500d01a1240018150f400500d0700c05aa43e4404220304c010340021001d94450340d204400c00c540d00c010095000658043c0102c2c1da62810035240c0700081545800054841131f26060040140c0d07604001034881c510f0304000100845115020100c0c0284a000700c00c1ba40320300d002c5500b001b885000100006030b0310f800d4000b00710b072255800c295003100c0011011500000d908200c00010303410041c1b124543c0038249030880d8540d60f122000103480d0021081c5003a0440004e07490a424401c003002030804006042d40c00034030b141807944194400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 161433435 1250 161432185 161432197
    0xf02100c08090f0609101121090f040e0109051e0c10080402040207020901080c13051909080c03071a010911030c0c1e0106061715130609060b120a090305 67
    0x840e4082c10440f00c1c041d25007400f250055440103103c0d007240c40c0c0f0303645e001d00403100e00072410825110b48090900c2402c20541844c03c00d40103d8151402d1060074810881840d020041082d00551100500f034400e00c4240501901584184050480d1164200349140f000000d062072891716030003000c2103801605e0b8150f4a00042540349001d0001d030395035001060283c40b40040094001d9600d400000f102c06002ca038030210380e40708551696003507015422110694100b0342e9420143c03041e108019010300441ea11442c18284900803440c10030005500150454000003402d0f512504000344240c08800d005852a01404102c50708102c2c2c40080603103c3c007107000050140088100000704c07003a140c003041006002034401c9807800d00213510360020312806803100b4440d030004078403140514080f5156824080340301e40340e203440070113030020f000d0100001c0c01d4400700d0805400b80e42d10008244014580150700c00742034004c02d0b5542e9425850308072620080e0081140386604e00e401d032208000b81d0b0240485030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 161434685 1250 161433435 161433439
    0x5040510090305030a05031501020d0e060901030609140103020a0e070206151f0f0e090103021f1b0804030c2c06010e09090109031103040b041e03050a0f02100c0809 72
    0x810100d400500380d5503103000e908080c14030301c0702107504034086038131100443c1f00780c143c000d45400100c00c038401641c0e2603180203002001f0444074108a00395007845c2014104500052401040860752060503000319601452103945146003000180158280b0410440090824044100241c50081e600130340300c81e13000d1305981d0511011074400c502591202501c401460407051607492054030030b030001e0640045d1014200c00f10b4041d03040315555140821109040380d4014000c114000d04a056000c494141c01e00780009000120700b007443d4420b150a50301401a10522101d6610390031401c2c04015018640d200c00005c2401d20000302e203200c82041081c0303c0030780003848950175480e00001a103491040c005941c2d0020b000c0c10401680c40015000140418000d450744000aa59030248544910960241cac0d20901c0c401c00c01017003500c01080506502c002c1c0c078401020255100d94a0307501b07020040d90252290100c0e803042c40154607144e034034296601a075080c100e0316000740d03a035011142c1c098215814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 161435935 1250 161434685 161434699
    0x30301030b06190b0d06031511090f031e060415060b07021219080706110901020a080c01090b09060702070801060501270905090d031a0105031611061008120703050405 73
    0x710180c0b00c071550f03500182c41110f03804c0307445161180800000701464442507420891414041440e4002846410540c0203040003680c5071088010521940340d05000038190144206070f580c44211050b40816020482c0034809010316090a0401e0309080c001000140324042c0340110400000c2580310807074500c5039065801c40c0580c0d18a081c518148030b104140d500740b044180350301e00d04004036000140080d82c41030004000040720840703101854020a4030440c0035901c80c8904c00c01042d40b86001c0d0600e408041c0c0081a4200d2907614030580760415101d007000c55002c20240441e964051001d000900004002040f615180c080024500c40d01c4401c0b030070011041c1c128003402c0700001240080a40005502031105050810320076685607003094403000000d1400ca44201441a1558031582c81507050b5291415500d415103c282c584600c0700f29001448140c4450b00d55440e0140101c2d0720030002154007102191404c1c40306420008c0050040320241c10030081000043c0c0c021040ea400e603038043da102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 161437185 1250 161435935 161435959
    0xf06011508090703080a020106061e080402090a0905010207030302180405160309080f07081b070609051509090403090504110f030103030f02030f0c010b1c050a020f030c0406090902010f02030301030b06 88
    0x543d0070703c2002e400142c50301500084080c0000e80540004045030203903601c103d400d40b902c210050000a80c2070040c80006d0444001c10054074100346450703004040c2410000f403c0e0102d95405007280c0c04240e0840200360003041001c0d401d0854071608401620555050049292040055401c0c551010444c0c00785503a038004c4206021142d016181d02c2d0419114047c0d80301328508000310b960f084890f842c60072640034030150340a03d00108101d401c855054540840d9541000d0800041001001442c7c40b00e44e410700c45801240d45502c0401d000324000c1e1540c0880c01d0415040c441510070510f004901c1c24000c01600d0401510401141c0c1100d4140c034010340c1001e00d40d0b074224110311030929803010f020400724002091900c10b600a414000d801c803090b03010f40e42c1d000492101d0752159140a0848d802840010015041100d002881c132003004051710206d9544d400018100c40c01da4114680300d03640d40c0100021960405220710107589540019400e561466407030741d0240100411650187c0001508 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 161438435 1250 161437185 161437201
    0x1902030601210902030105040c0f080f0d031d060f100b0c03090f0103061707140f030a1b0b04120605010902070b04060c050403140d020d09081510030606080f0f06011508 74
    0x844100f40307600800074000782c1010b0406000d0349006000c0c0561464292a0001d00501d0000324000c862010f80050079031700407940b0068000741204403402510341c0c0030f04284c0900100c1030104512030716440000c402d0505280c2d18060b051a180e40052440310010005c0f4510010b0003c16219000401c464052400194000403000350540d40d00a03206034484017800542c0050101e44041680c0c14a00001c0c3c09514500030841200c44c0800c0264040d004042000f000c00c07003080c00003420070128000701d02d91560300c0042039402e605ca503003d18901c80013101d0034030402c00c06010751401050510015070034001d80b620740942070304024000600301c40da12a013000602d802801554011070b0000007020340990000107054540104803402d000500503880035500c075034012000703002500c140d02e00500440c3c2c0000c581500403080170b407c03c111014407003000000a2000e004200c05859030700301400102c05510085032400d418256111155004030f001800001041100e105840ea1213180070203864448000e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 161439685 1250 161438435 161438441
    0x60303130608090c0906132a11061506091215130201022e0b010903050a0606080d0305090d030c121a01020d0306030c15090f0608190203060121 63
    0x441000390000001040ca411000c0e041c460000b01d42660701d4207076000100f00c480c000c2240c03010790010384001c1000070300c140d03580b243e00c3c0341c0400f91420007041c0039090140e00d030045000041000603d204482d00c103000d41405183d411881c0742c4038a1040c00303030300000a4201e01503442840d001c0c8103015200498100300b08030605c80c1c07403072044081001d42882116100b903d101010282d001d88140107071a20114400710f2100a5480a44003403403404090760140d41c05090391001c43c1d410811890030210128009101a01105103e070324005205413422000504100001c400c1c4030a1600c0c110402c941c001d400701d2000c04404c034501e0006139484c0c4084046d00d0700c20301c10407a1100c0510701000c00000c0c1c410b90380d410386519426000c94a040d0a00d54044003030700c100340001084101200000c0003803079043e4070044006180d50415141540d1500810020031105030301110000ea4480c09010903d6400000b103c455041c203030040d85146841d50000e00040c1c1c03c080d29103c240c04148920f20072507440c2e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 161440935 1250 161439685 161439697
    0x9020d0605010303120c0219120c080309100b090405070b1e0d0501090b040b0a0512031b0105010509130b0f04031b15271704030c060c061b020312060303 67
    0x140401c034550316410014241c2c11a0940000c4d080d2030880700740d5440b0700009204d4980145074940000d500d00307981d100c41100e1000110031040c80303500703980b079000641100051403144004100806400550308070040503102d000d4881c501402d50306003840080b4001080340b0b002e545404140701d9171040810b203a0480d2041169008034030034004514688401b680e40c20007412201d84d00000d00c40346650408000032140028800da074001000781d810040e600304481c40071609005034086d42d041107070000350180c401e0015004900182d43d118010b110a20304440e050b904082d0011101d0320340b041684d1341c22551080602042a12002c1e000003604040c480e0f100898040c44c402501d10420340e292a12511440c2120340ba08803035400e020501056844461081081a040e00390100c16601c440d11080031542c00c41d41d000c1c241200c100008008200c000203050000c3c080c07a0346403030182c1b0550038514104c5220302d41c10400c015004501e454501c0c2c2c000143c0c0e5850407242c121090580310580041c0c038521440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 161442185 1250 161440935 161440943
    0x708011a1c06080c04150f05040f06120f050d0c03090e100503010c02070806010b0f070201080405010906091101081608010b0c070509070f080901050408070f03050c010509210309030d09020d 83
    0x1025012852150200d5011004001505c09004240100601982d0444a401000c0c410380d00f01c00c01300060718068001c202c10204010b000162580c5035085440c1d2180a814251080300040b8450820004200107900c8072800903d0310b820a020541e8008040071074511950100130060300110b020381da21041140c00a010050007003110a142d49400303900c56581d8807c1080a02841c0c00004004200302d040700d042d0846220000c0c5400429401075840c50b4003d0001e48442d9660043c0400083c1300e0b100e05462603005010340f030740804030b0200042000350000c0a600100319031501d2840406d81207a08203066405a03140300e6110b46490f00c01d40d00c0c14180382d0120381e00c490f801c014812403a03041002280c481d4410350313624406a4030312803101d00b65032050701c000380320346c0d401c1080c0004210f08080c0c501150384a89059490070102c080c840742502c00c15564140c140e00094541c074410701a00300d500d005c03661492600ea0962400004450303c07405900f2010010b95102c1407800219516025030503002d40e40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 161443435 1250 161442185 161442191
    0xf09070303050901030209040e0a150c0813030f18120210170103030e0f0d080c0613030f030b06040308032502150c070512040e1909021e040b13050901050708011a1c 72
    0x442c24883c854803c40c00c022f640c1c007450f000940c03001d81c0c41014142d100b00000000c0542d00341300b17681c044444100341045582001b51021429050b0401422190002c101500582c0111151401041786a00900e0300030317030510681d261101c00124488030403c2c1101d402d820710101003040c0c0c10100b0000b88224031290307070007500041c8503010000d142001e00382c1d091401007110400c0d42c5010004103001c002042c00740200e0800c8503c0c1c071600744682c100714240d65001d080581440e0b0361303a0303820030300350815295440c521115104680c0300705514942e481d2058014801094090148082c40f480e020303014040b180580f6000996005205042000107101e41d00030b4071141d9502e94540c0328586c44442510005103000c918025261028a00d000c1c10354025001403d940c00940400401d2408080e81c0c25880c0d002502d9044014155441051440501e0407000700454249000c10101d42110001800501800b90b401c005000e00155074048040c1000051141e81e541c00e601040340e49c0380001030080700d6031641 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 161444685 1250 161443435 161443453
    0x2030309060d020403060606050301032f10050a03150b1b12040608090607020d050f16061e0608010507020a1506090504080d14011401050901050c060a050f09070303050901030209040e 80
    0x1d42c6074014002c80b40a60410041c254844d00c04503a04c2c442071002500030000003250004070b83e200010580b00e20300031008a40c0c120300d08000300d205417801e03030040c3e40030600c00308201e40855058080e0005080c80191800304c2e49041c04064401340c000d514202c04181c80d01d108a4440707c500b00700407940c0c1c4551011980e02c0c4c0d55030b030034014141281280c880c43c45000d0b0901003001e039400050607001880c080d03292242010068400c2c4001500000c0c1419400300a1460560102d0124032980104015111000f40544164103540040c0d900d1544051000d80c501802c00101641c04540a4600b43d80100c40b21200f64014081001070700217608503c0c41c85162005100c03c0241c418000c02e51400c4080050065040318a020036014009204450200060200315035035584580000c1c01e000340141007007401c003a10a000280303807440c1141c441074020350310310612108640f92100c2c00e5004c2020b0004101702c80c00c680e0002d0050258001040c1403680114194100d036499801003030b03032001200101c8080030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 161445935 1250 161444685 161444707
    0x18060f0305011b050705030a260a0506040e030c0601120309030818011103090102070b0309010608120a0e0307120615171f0b0102120d0204050a09020408010f0b0d0b040203030906 78
    0xc10032041c0403e0205688180e02c844501074402e44d40d5058000020b141480300f07061007070314007415080204040c0d03c0700741070030140d0f03107501d0780400e01409101e4030024840c90984207000440c6c00d8086880d031030f5881404244081100054041d055410b00c00001ca00709d8050315042d1208000381c2c00c0208501c10106010b080c040100740301c80e030001001d0b46c8402c120400210156168803a0300081e0307006070050201031100d000e40314021a00030380400000100c0560f034107211802c0c0300540140d441070401c002162134815078003628104000c02c0c110041c242040c03801a0011400525280060a19850f04040d41807107040b0398029008101182130300540b10303015000c6546030300c00e0414120039124006558a00d40304503115113004204180c00600e0201000300280090b070b0400ca084036200d40c0c0070003001c941a00c9443d03042c1c0042000250258503541802019425100e5400c4c200020510740b9040c039249582d01d10008000e6500008608aa43c5075800407a00318461610080c0d040480003400c05150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 161447185 1250 161445935 161445941
    0x40605090310020306062a030c0f2b0f1b0f0312020901090b16060608070608010b09010905130615110f0109121b020a032004090c18060f030501 63
    0x103000120709440607041c0040000c030480c00143c1e612500241c050001c14050054204140606200101c0c8105c0300511909814510341c0000d0940c02e2940054603804d24401d810030408034441050040784881580c8150150802500c0c10220800c20144200000405004810300b402c01450124080210070250074000200210980d0440019102802020b0302d1081d81c0f00303854100405a4800202d149402043c0c03035690001c0c8150820282d00c12075000004409104540040140c5000f4124580c90b0210283c501c0205a200d07170440b0008110a00c20703a030b07100d8605400d680080725000e418a49001c0b928000b4030031600884d5084803903042d814000c0e0b0300140400d101ea0960780841d1604200000e547e400e0300c05821006104c1c0382160642d09020b070103240c0d00c0045000213195a006602d454001036402c0301140d000b590765100c590a00255006000b400d031040d124161000d100600e21f90303407142c0e4070483c1751140148240302c41445944110050f00404000c02c0950102c04030651242412402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 161448435 1250 161447185 161447197
    0xe030705030a1d061215010921021f080106080f0103020f1513241106011202190927030207030201030509100207230604031b060605190e010b091e15040605 68
    0xd0000c0003d8044150300c2102d40d035094885260220a9000c1c118500c8022071200270800ca0340241c007954a8141d1071680b1000d541c04c200030b07a60711070165140650213882c041001c0d055000240c0c0010060000d0384951300d07501c03501c500c240e0b10a804100100c4e008641402010080880c41910240001c0e80c06034003050950011781c40c1d026000f58200d450400c0e00c2c0e64000d10005080d82e0041c400400249043c1e1000e88080d0340040d21900513011903800c040e00320810b82e0080482c59541e14140350790948080301c00c58004070901d00000c00840581c8019584044500c0004c0c10191528000b5020200a01c264080d50824410654840e07019161030602c950740d20502c030030412188080800c0550780041c05900541e016214030740c00490f45400d105c100d0f81d100c801501c007142c42d2480010140c84a403190790061001c0c0c41d60409450419008240e1140107a000d4820080c05220422080c0e4500c4451282080313000740100d0392221002c0030440307000615039640d80d01c42c0c0101e030000b5915006001052 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 161449685 1250 161448435 161448451
    0x70302070f061407050c060c03090102090904082206020c10020c040608060f0c0a1d0f060301061d150a050c0c03031c050703050112030806010e060f04090e030705030a1d0612 76
    0x3070344c03000011075041c000d40c10003018641c4620302003195140514025a002802c00001603d0b000408012903c121410340d01110034040018484000d141104104144c400b8103070a004019480c2c008001d5a9860100300e0521907107001080700d040c1c500811560001c6040a80188215640c07521102d40f5a602240d400b856600080002500c4501203c12504100340b281c40f0103407018501300d246cbc50000c2c912910150048580c2084611a941c0c0e00080c50090203280e82c0c5042440141c00340007074400c50342d00d5640c000c41c2c10121b51410440c105059500c0015a880c0441e101c0300c90484e80b6140038104412681c02d80000500b04601c9480711441e0f003c003031200d550174006611400b5045003102d5007481225080c00a8504400c0003910980032150000c005240400030b0b9000e02c00055456840000300c8442e081c00007070100b000503620300070050000c0d0700501850410026803660b5480c1d10034200312408002c00303005a1040c5c41210201c240c1042c3c000707400f0944400011035500d5030213005844101c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 161450935 1250 161449685 161449721
    0x509040615021b180705070f050303240405010b2d0a0f0f0f090605030702030d0c0906020f03251a09010b01030e0d09060509060c01090503040f050108130b070302070f06 74
    0x2c2807a080001030004c10043c3d02c2c410b040c2c503135920f100803103168000c004100d4145000708013500c007240b001c1002d54000c080c1103402882c51100f4805184a280d442030a00c2d000e241818010031840b140c3d04207a9420000c00300804849200180844140f03440f01409840b403044041008011203501ca107810358285007a488840261004031000d44425038068021400181824010300140b40715402139600301c0c80c1030040300e04000001c00341c1c0c0280c031b080c501c1d80c41c00034042405c00c111040e410071085207506000e0000c1c51420b0b186e0701c85645001c0c45003840c1c001c000c04c41e58194007040304940c1210a9880c2e29000311805003401d00380c0354060908965100d00003400c4c80c142c0d030190000400e1400344540320741c84401c6120f140020a0f074640d001610301030341c4001c050043d0a40d04c3c070300b03014a0303206d98803a0000d16541d5042c160503445000d0242c10050401c030080c7d0400111104203120350090540040c50004559102d0304220041c1c401e030040104880c0201c07a60104110041d04001080341c8110190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 161452185 1250 161450935 161450983
    0x30f060a06080a0503070609210210110a09030f02060702030303070507060f0b1e01110d0c050105150a0902130b070f0605220204050402120105010b0a0f020c10050904061502 76
    0xa81d54550941c3c0134040d90402c118010002d0b50540c000306655202d40d0100700c520f40f04140207490012581107550158000b0b44509660480b01d1052000041d4600f448a05155401c100105849103600000f4520308405d00c00005554420f000c1d2840365078011708490703503031902010060a40c0c000c40030448507a414820518882031072405401030804024205000b50b121810405040070189a0041d040c014030035030012950310240284400c0c0c0405c3c0c1c8030310a450000f41b60031800c4400c010800c0c82108450030700c4245540c0c070521482c041b685070b00300160316503140c820100d0703070307684182d0168244000c005000c008220641f085100b010303000c0c4200b00541d0f81c0d5084042e888045070000e51b568413580310b07010b4005141c2517000e180c0090001d4036800c1040348021029085850a800020000e00301050341c1c1201079000d543e09840c245544040c1c0f0858103580d0105ea00c8000c56100c8005100000c607264031240c840e580310000510950148482e58003401d0300103034540c1480085a4503180052001e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 161453435 1250 161452185 161452199
    0xf120c07120e06030a0b1306090209090a0c1707030608010207060b01080a060b22030b0421020f030d050a0b03011b030b01030203040209061c0f05150f040b0601050a020705030f060a06 80
    0x440d80b032000074100707034078503520344811400805418100c01e51203442203102591500c0703940304d541e001d003070b01c0840140e480d028030040102540d401000700b1455801c0034800340c005580a200c11100c1035181201c0355a031b0301e4110b4164041d1025030406540e0358404204a0b040c400d168026482c82d510030b80318800e09844540714a01030300c14a001e4884070a0f0200140d0070480c030329031007031400c01d212200d404840036120703510401c00d100c0944090320005130b142829642c02031001d501488d10704060009003041c40040314180d8490250400400d01c1c0c0d5507800009050444a400411140e44020f000300000945a0482e810f80200d1000c0440000d19046038450694000c1c42200d0040f5002071103c6003e51b43d85040001e800900c80c1841d040014118031407000504903007803402c0003446030002d410a00c450856200100000800003110754140c0024007011a0f443c0354841d402520a00c2c102e80d88442c49441030b407070000c2c04e511194142c0b06503041900c40700c1c00403501900640741d20324203000c11691020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 161454685 1250 161453435 161453447
    0xc03020c0703020f120102181206070f23190305090a0f080a02210706111903151502030904180812040611030109020712020304080c060f120c0712 64
    0x100c03400d2540e00c500014009854030540d88a400b007402002a40210343c01c964076400e90b003020807060300f04076110080c030890746400d03408080c05c101003000400349490f1801c40100103095441e0707820203001d1908400e0740b61100300a402c03200f10144011042c1d8401e80303041441010300b8101c0c121000039240c0340100700009800301c0d4203880030342c0010310381c0300120071600d640c0281e80c04101400154400c08881c0801c2c0f5002610000c14003002c0850507855500504192007034039166441d0030803a01e001c0003591108050081c2da24490030340e5250001c1d010030401000f40049000e80c1100001c080c40010310301d815507000008100185095409116130540c00c1300903090000481c000520b0124140044110001d09140e6181d100c0e00901012500c00c0304056100c0050703000780c03c00c00c01a60005410702c14404d0181c0e40030482c098510040d803030310703142505290710781a0740c1c132082c2d22400c5c5c00100c515215000740c040d41c0460026602401341414000408002c0d9405510100c0b2082c0d01061b0b2043d40704c2c01a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 161455935 1250 161454685 161454697
    0x7081905071b06140d151d010603020f0f18130e010b0a05032a190306140103050304090e010b0907020109020a060206010e01121a0a05070912020609092203120c0302 72
    0x40c41e01404c0d50301000080f00d45030404443d0100c2c459480030900001c003c00003c1d000140701003a0080d05080c032045c3c00000aa1050300b00206142c010450000090310b2041100da1150340c04224a45620310010380200301030f07440340f59a600c40030403000342941400e43d0307002240d107090400080040596a07024031110071050f02c42d00d903140c0c0041d51103604440c8139513036880a49203203141485a003031440300040c14031040c1d03071380180c0c3ea0b41510300140200b1906108403c00c41c0303802d0b90503072101c0d031456603281c0d500c0c0305034095210755540712a40d40030608000d42103480000c500408145641c980581d000b40204031700741d01a845503e801c00d0000d03009001145490698407986191020f41c0e081c8100815203540d01201116010740c40042c2412178036440b04d0080c0607401c040c00200d101d04211200810700440b68002408038610200028016a14401241c9410f80d05030703101300003030350340c00c11802c000210300102e0350020790899104400c0591240a561b4005c154450401019003180000c80483c0919 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 161457185 1250 161455935 161455937
    0x1701150b091c0b0a020406090e040507170a0b0a090204050105010f0c02040506060f18040509070803031306110403060f0c03050f1302040f060f030c060807020d0507081905071b06 78
    0x4022031612400d00600b84200030440503240d00c8a421559201d0102c01e00464003400d405038003041c2800313007035400400c0d18014031008000081c607040c291070b501e840e42501d201c2c0c2154054000c2010040300301c01e0200c111101d41020410041c0e01c1c019071441c01030b0003508012031245140500206856001d44c0c103a902c015101c0d61103540c422803690a0100030040500829800101440801030308a0450010701240c580709406034200034500c01800140c6402401044807500310b0041405403100002c252a849580d9000f115800c50907401c10340c0050441040b080c050640c001004424880a50080e011454038a1700410200c102c045003102142c0302603401c000d03480702c0c52012031702952506403c41000c038001000003503843e28810528048a0180c0d000c0c5001782d429110070000d103e50001c41600400031804c00005626041c0c40c02510b80340100142414800045550307000d00c0801c505503049031031620040d140760080c09501500c650001c02048501840342c010120405201c401807400700d80007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 161458435 1250 161457185 161457187
    0xe210d020102070b040f0512030c090307080d05070303110c010603080307020601052202070213050106020f0c0303030f010b160602040b0702190303080604020702030a050601031115040503030d09050a020a1701150b 93
    0x81c3da43c4410013074030740781d101f03550b248283d04184045002200055004d2070480492956038890001814107080d40ca074029403580d00705440c0300d100250403008907201c0d250316140008081c901c60400c4803042c0140c85600110791b107806000305c02c10040500440c040c110366000c42e18282c3c0e07600100301c075404010030001d1107041c00c2d00c1550880007542d000f9050b002d100414030000e0068007035540d0704a4a099100030010381c8840c820b07040000b4103100090608005a01451442c80c200039410300c00081841010454040003490440c10b030342d8521000d0701a03034888402e560b51a911182501c1d9504101030682c40b41500e1691030b03809194405e00182140d5061700c91070b0b10b503a11401000001e400045040e038140c010300c012000000d03018804940610310400c42c505054401c54140509441003040d140740440082006004a035000010388802c000d006002040000c02351404a08089a01e54002e40207030400c1d101240c820440003040d415500890000c0181c910f0002520030822403900c554008110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 161459685 1250 161458435 161458441
    0x91207060201063b09102a170f1803040807060905030a02030a030e0f04020f04151803110d050f010506040f060315090c03080715050a0b01020312070e210d020102070b 73
    0x12000c081c0315400800f01041d11b90b45c1c0501981c8030151522400f481120102c3c050042c210f07003d55401c40c03d4034407030743e181c072000c012000340210106030809411504d91b1112135000901d0502c541c01040340b00756086042d2600e03140d845044596a41041c00ba810111307041800201e0b6a0400080211031103800a000300b0540d40185c4080c2d030490340c0320384001d810400d0b0420642c2da5484500051600d24000f042c0c440e07866240c0f604c041c8110008400c2201040f2600505020280541182e1001d0302d0b0001000c0f00c0d08900607001404d006202900103020b40646400340c0c00669041d17100901c2080d09540500c90143c45009820807034603140402800300301404201041d03600c5d6540440c501d07901ca080c00d81e0178180c503516035010a40268808480306000030090f900311074490b020312504514003030000e2141410010001c0c2d100d002d144550321a4003c1c1000140b041440351080d8082260017034010140050a040310b00581d840b01c0015180910810760350034600d40c8140300700c2d036060742c000622050a403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 161460935 1250 161459685 161459789
    0x5100b03120a02100b03030d0c0203070507050a0807090b03011d01090c0504060b1215060c03071703010e0a0504020a030209010f380a170a02031503060108030f09120706020106 77
    0x2015440080d0307010f01c0240000555140c48d03218a100c040050340003142c60f010b0030300d0414076006043c1c225038000c001e003250810040600244030410b8451b481808211501c00c14080b82c010003440c5e240c02141e281c0140032002d402410340c00f403c0d00d28003d80400c00915200d50501081d02d0072449401080340b030401a84450b003141d14145900590041100c07440352007a000040c507150040c05100b0307416040002c0301000c20402034804180c0702c1c0c05903140703415907240821844103a40d0081a50100d540c94a000504655400716105c000d90b5008103450706c1035841d1518158002164000d10501904034034185041e0302445469520724001c0e5580c8030030814601c0d51003c40f80e0440004003051114501c42c041d030074184041d2452040880810058076803a00b040c045000c0b0010403141c50080e080480140458031380402114810308010340c0e02903440c1c120300d000c107941941c06000c5090303d0103207031008903000c4e03410740042007110160010694102c0401c045110001c09921a201c18804402c0080d020740e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 161462185 1250 161460935 161460941
    0x91609090201110a110102240402010518150301090b061602210d080610050304030e0f1201020705010c091a0301060804030306092d0204060507060e070305100b03120a0210 75
    0x584180740c4110705450f240b801a1034100141400c803480b0400c1041d504095070f04100c0c403012104c0040318880005100e032481d1140000c00f91029040040009524810317564240355040361207406460f1031004101507d110207107420138056104d40c141864804a03551925100b41c5013034240710592140c0f40381c070b5942040780703604802d00c161681d00500c00c90900700e4030f01800145011003580c0c40743c0900d442c08004000c48510314410f2501070080510521001c43c4d4030080706021200c054030200044248400029507a01c4074116840e1103600004001b420044103401280000a090b2507040400c1c0c0c0701d0b402041c2d401c10039036800c001654240300401c030032413042c0e0741300360001c7c0070b42000600d66403204181b400313035010f030f551700012000c4000032404103800f8140642c90031031640c2c10440c205414200014454032032a1703c00741c2495200d90821304100310a102e6880103507800400c84080c4c5a2402d099409048003a12301c900c00d0007001c0f0404205420311741116041c100c0c1d50301a29002010041da1802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 161463435 1250 161462185 161462201
    0xf060409051e0f090d05040303050a030e0712050a02190b0304030503060d02120c0a0b09030a030513080102031305010b010815040c0c0206130801110c19060902041a0108091609 77
    0x800082821161401c6080c0c2c0481c1c001c03214000c2d404030a180210006240c51940c0c0c1500c41004800c000030401b080e4404140c40e004a180d160120300c0c403002032803042c40c152141e00030721401c1d4400b040c80410400000707407a00119100f07484400350303e4502180990704107a03a1180d030415034030030400580003030b204e100215031000000700b140c002d5080603000310b000750000c0c0c480e2600940c82440001c04500d004c14090000b0480d02c1c1c402854414000301190f120600044010103104003c030b07058486292034a0194040d0181200031034491a20f490401c4184281c4102540d243d4a070581055903948030b01e420601c44c40b000e0103003c3c181c200c0c01007804010000d03962100d0400200e140d000005030781c6c68000b46030a804141040b24954180074225084880d1100e03c9030344507500704844402c4441c0880c080300c603003440c000403003003204040c1072160141200580081d4088c0c509040c0c85d4015415003802000540b0a98901340b007503480c40604c6030b54241044510258001106041201102c5c0d5044210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 161464685 1250 161463435 161463451
    0xc09011e03141027171306050a122c010204031b03030f0c020603041509050124050111060406051905010306090c0605070b010e1513020c0d0206040c030b060109320f06040905 76
    0x300d415103591141b4014501c641001000800c0020720766440c40d4021181c03111502420810400000248210071483d41c0c1408016107403c02e030380c0026942031080d030507900210780000041d1038510805070318204800301400100c010440c280d8484c001c4601c240365005101e540500700703510715196a1201d011030f20b440b44001000b42d4903520801c00040003801454071081c00e080f1940c40080c0b0401c0119401002a040903040148170745401010490018a0a400c039400080004a0340c440c44040a906480140c0440c034590034840004208401503004c2c0d86901c0c050001c520001e070315603c00725054854460054154203418005000741d40e640714425800c007072004c5104041095110120b0120034201d42000c2c1036507404200381348030343c800b071184400003045803028058610b03040d0f4840e180d00202d80070241c50592483c0005900703074001c01d121b401520280f21a00307058503c0c44404888541608403031400da2800ea04100080d00700680c882001440040c1450f04160030085450014903000740b0101b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 161465935 1250 161464685 161464687
    0x61e0e071409190f080d020304030803070302071e03120b10140d09080405030f0102040503150a14090f0c010203090d0204020c0c091807080c09011e0314102717 70
    0xb50540d84000c02035803191424480105050b240030801400510310740c0c01249075400a04400041950100845007941d5104107400c1e12902e035a9000c03002809041d00040112030102d07000c000071f00f511810201c0d11031013640c0781440c5020608004060b01c6560112070f800241c003200d0402c000d4020428000700d0345056120500348801503c045007a50300000003540d000030f000400380840e003410304c00b41c16907000160095180c036280001086e901d003034809a0710700b9141c15602041c2141d21a03003026a90a40010307048415003020b0303000355110b0f0a0054030409034400d9000300d100550000c0269060a00d0081c50120001c1e00764080c007000e903004103680d03035290082200e080130650b500304060340a0441c82d8001c2500c40b081c0714900307103441065080403071590301c480c42c41d4405e595224442819140a03072541c00c508003201e900d9500c4003c4a0b00000c3c0f09000b0503001520012001600003501c0c1503100c028400c54024080c5512403400f4000d00002c090103800541000ca4101c0300b442040758081c103959 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 161467185 1250 161465935 161465947
    0x9210901030f0203130c09060506030c070c120308070e0109030201120c020102131203080a110f160f0503180f24040b0f0304060501090e1c120f061e0e0714 68
    0x84200d1344201c54441e6440d21700901c0909204010030010054400c0c0441041200e040c940040c0850100520707a11662600040c1002000500d28240c002000c44d0b854202600c000b91501804801e0102c40c50780000d001d00c0c88024940d845040664110b903010303185c688c0d4008426404101410104518405541d020084078002c805201818030080c00517084040003000e96140c02051460b02520400d44203040450f10a924001c0d50700b03e40c0283c0300001e43ea9582d0380f850b042500340d004c200d40c000d0308801d191480355040c4400230001707202d2801c4008030300c2c0c0c68451110030040c00c4224607454940014405841b0800704000300c2001c1541c482c2c1e20b003402d04161f900d0194403040d60007010b91403a40000802408208015400750303501401d10004144000e40605003c01c0d92412010319140b4072418030003074000001c0c010707200194420984401446400116208480031b00f103184a800140503100406442c2100c0030406103098507800d04103000d0715100e80c9011140809041041c1440460070820b03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 161468435 1250 161467185 161467211
    0x402150c0a0c0303080f091207031106071d01030e0a060b0a1509030c0906060f080a0f020d02040807091e05090c0907021011130e040c0302120609060921090103 70
    0x1004160510486440c002e0500318500180300c168007410750f4003540840d405111035400f012840d03070412424900080e85400c82802e0071500b8150003414031690303006e0401446040d590000da000e40740d442c440100c00905204000443c11105a4130b0415411f8020014050006e0065000344442d410020029160141c44401c025030014034140d6040108024400c10402c101c1e0101c00d58005008035101007000c0e43c50a0f4003d04002c012190341402c0088030130008000b00600d52121001c1d9aa40301c04540310866484d042c0000d511502030322560348030b6942d002900c200240540308400600300341b0180e4100300c1c001c148000e0030015003100000c0c054810035042c5611030241d1a803041025a0040801e25492174010003141c1c0d162544100716803080040465040030810094201c640d102c040c0003042d41c48d81441c040c065842e4000a5122800c030200704200c4030002141030041c0c40c41c41c151903041e202c409201c0d60750741c7d06202c50950013100c2072944ca54001860068078080c0b4040c1000300701d641e98540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 161469685 1250 161468435 161468443
    0x9050408040812070506010f12020402030405070905011511070b0f0a0302070b0a230c0301060f0302090604060509210c0d051609150e090717190f031409090402150c 72
    0x600403007202c00484c0c6281444002c010b0300e030040a841000e000d68904201c260613004000e620040d0280d500080880c0401100304840401420750341c030104410b503129100c10000140240280c40000c0c07001d2a2150040b8012812070101c07601e40e1019460511305404510094002e03884070014590b082c09594041083d02046610808200354009910720203054820025101c40700c0d00d170f144d50100000c00854000ca841124103544413800d2268017460500300450291007044403c58001002113400641e168010014221600049030000300310980080648896869800d061685601c10440b4061342d00b042c40f0350030300c1c05008105881010306449509440f81c0043c0d4065040e8554a1080865500142c81c0c2e90001e4038100c012500141001a1800e45c4d820560098421000c0c94000340d00191808205004006c80c080c84c546a0398010390420048060448030141c020a11207294500302003400310072910340e094024039030096a100c6800703100800030714114041c0c105408100a40300c03000100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 161470935 1250 161469685 161469703
    0xa090c0306020310091413021912080307020607082512140a0c050909010e0903041d0610050403020d0609020604082a0901050114070206040f0b1306050a09090504080408 74
    0x301004c982c16141084041c00c031810300c99a0140c00b00c4038420301400d0002e40038218500d0b5011100e1222103201a62070b1000c61440d544182d038040c00e0203844800308000c4602031841000b2640a0b01c170b0a980703001050320841c0741101e0100c10380030302884101e14541003000700c406141d50740c40c124900000b840110070454991000d640c0c283c0c0d0002040210f95180d81c018850003c00c0344c47c0c003504008040000c1088650103005010040910000080000f1010001d60b001050342c000503410404408440400482068032554002e0860081d50b0003124041c1c4212001c41b5409060441c0c40c0d142034460b400240700008040f640980208000550050100242411445c10042035529200c854003004207c121030b0081e580580310040c01044580e0300a5142e84400811040030f5945a80c240b0004040c0e02c2590402690018001000701d07040d10703000c0103003403190700ca000540aa5520b0f45004d071150300030305110400040f015101404440300740e0304001d401034404e00b545030900b61120401d50800c0164 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 161472185 1250 161470935 161470951
    0x20102180f13020702060904290603100b03270102091311090112020f03070e210714011106010b1314010503010b03040311120c070f08060a090c03060203 67
    0xc51442000c900030900000c66200c100e409440820000000c112011500d200b072a40c0b20b640420b481d030035905c544040702c0040d07200400804c00c24001091402c14191580880403a54400d804100d0060404500303c0c0e01980070012401e11451074201e076404260310050202c9007210000020004406510303510b280010842400540c0350140d0f2400d1024010595003a01c001c9410311400503400002c02c01103510302c2d1401e00e0404500f10781c22628001a2007a007000030491a400403c0146240d8000c2d8000c924910885400f00001045070b00c076100c0341800c03414095560003600d01008484401c030005d091354501030414030140c1e200c0e03030002420301509030710884810800150080c0050300040410010709140312036000c1c8901e102c0c0008101e80070500481021010000c003090506006440c180e14400c42c440440f283c407176540302072a000e60007400075880548100355010428a00421051069424040050015648071a40c550142910b40340c2560381241244001c004038207a0f0000750712580070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 161473435 1250 161472185 161472187
    0x406090311151603090c050103090c1d0f010e0402130518060109060e06010f0504030b13020d11090705210a0e0d0503070e150a080c040b04030f05010b0108100905090c040c020102 78
    0x3c10800c115250082c842c0c1c0101484d1100d218000303a180e41907001504c030280780006841c541490004040c070440d40056001d4100c001c03400544a00b604d92451003480c1300c59401c0c400d40d0783c0d600b0b1401d50303071000c1c1c0300250312164020180004074103a85c0625401030340c1c20030540c103d4084450031341c01c040083c0c10290a1a803070f010203128100032b10000d02d42041082c6012810050007030b000a010b400740740002840ca62411000c43e010021841d02c5044142c3c000b04401c0c0e424660b494182e40ca0720034000900d0050a00c0000622020300410640c0c01c1c104c070502280d810003001c0451041d2741d00d00104030410390780c0d454a00e003440610401030004090b000b510703000d58a040c1150050413221001c10303440d01c0740c5030104080345005038032020b442000c0d080d0b00b00213040b03856490482d441340c002c40d007220440300404500001030081d0502031400c0702d070044008015000030880111000c25080701c1102c203421504070100b0004100781d000a91140405080d41c0c0324041080004050301c000159030401030390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 161474685 1250 161473435 161473441
    0x80103020a12420b150313020d0f0c031b05101205061810030c0e090606011d0910081e0d051b01050c1b0102040302010503040609031115 60
    0x3041e90801d409801d00e8088140641c4943d41c407405040d4902d4600329110b040c060b0001d588400c201403c290864585511400404034035040d040100400308100340f048048220781c0141d003d040e03045074040e000e0866028007000c002c2d028804000b0150f1001c030707244502c1503424004034440f062440e003c1c520902140400500003010800604059000f1a10402c0400b069046140d04000c000340104800040402c1d00e55a4100055441210350152444d00030050101b02c0c3c000000c84552003030b00c0c80703252909002500c450741ca1207075400854814980740e1004000c40d00715802040c46681008500082a009220f0b10b00400c400345004e50300c4240805004030180140f1200703114a11550303624004507101481385c0d00113107640700c003007490042c18040f0010b03113030050283d501c2c0140c1a901246000f44040e081000c2508240e42c00a824111580c0346845248428070040c0201c80031240c05a40d01ea080d625183c54500060650400440510900340450044e11806001c4800800120000304000d85 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 161475935 1250 161474685 161474689
    0x17091009080423031c0c0b040302100606080a0e010216020103050606070507090501030201030b04020c0c10020312010b19020f030304110d0b07081f0803030406020c1f0c0207060c020105030f09030d02070308010302 93
    0x3030070403070300f091361720564164180300164080d083c00d180a4100008800c030b901c0d2400d05070705003110300783e107041124103140d004525203811100850140e000602e04001420303100284600300d0003566510301c01c80900c0d0855802642c8290031603600181e005152a00d012115a1014549140c0390300c401c0c440368481d00100250742c1c00d8030803000e06900c182d50540c9818600c4a0281d21040c071002c0452140103c001c107004201d1082096a0b411800490588550b5840305010f10341600000c914004001c55419501022480811100040c5000d11700a500395280c80c2d40b60380c0403120000c40103410017100780d1054045501c2d00c500d0303400b81a881d152440c071401c0071409a400c60064003011005100d0a9008102c1818004216940140c21840040c0c1b5841c0300100d56085c242c0c8220350550071400c0e6440402114140d5000001c208883c3c2c00b01c41d8900d6990b0030036201e408103184043d001c04c03c180000b4104403102c1040c168000c0c1690300752807a080c9017140c807504a80100009400080311000180118 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 161477185 1250 161475935 161475943
    0x18010306320f1c080903010e060108060a1b08060607060f02090108150a030b090c0a0803130f05011b140d030e0c18060d170301151709100908042303 65
    0x1c02810369405848900c04008206401994030341d4040491000c038404061005400590f904660020001e1040042c2000d4040e9103100a0040744448e000300c502103058524140704007088020a40d40c2e45841c010081d000751114038005000b02e410010030401c1d400040c00703a110b0300c001c3c004a003a00586440c882c0700010505440100500301c10504c452540d04150780b200e801404480e170121030403806030346091107a0706242e4100c2c80150001385121000c25981d5001c0040d010180c1c00c2203000d51180c1d42d0340c10728551010309110b80e5000c9041450b0241001d89200c0c10303040c256000d6a4070000400800c0b076402e1400411104030342c002030b031369030310100d1031082400007039130119040f1107481c01c80140700700c01c4203800350250402d0702c5520403c0c840410070000540c50000c9400e410740c02920f0f580e5455101240c0140e4401d51000180d0000004212600440400d8090003171400180281038845401400402000005076000202404000751f070010150f032440159038030701e800885001540c81030510f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 161478435 1250 161477185 161477279
    0x20c060702011a040c0e130204050319030804080901050714010606020f0102031012021809100c0f08042303030a020703021c120c0e03030c071406040b18010306 70
    0x1164108820100319002d001003c0c1082c07002200c0c00542e000c21400300f0740e45010f25000498210740f401c01c00c00700d0070788103901410440d20b040c1c0070303200d00102100d5082c0c1450f8901c00c0043c0803c441d0004074020801d00301c0070f0904110107041130303454140c1907100d16079581c40090f02c0d003496a44560050012541c103002916080500000031340c294102446011118807a50081c2a0045005c07001d4405664440c00c0006c2042980001d0b00824181814010703191030b800c8030043c0000e803c2c0520754896602c80d40403410400025a01c01d6415140ca996103041c8100050702e46401180d11604103d2410040c0021030145e80740c6500140c0d26100303442d0281c03d10b000140300048001d0003d480740340d010b03000011988000c1011000180803180704400380c03400d079403248107184c05200c0410012000e075400183c0303d041c0c4075003203030b0103119184000030081c5511544c00303120341e0190184202c00814500c11003100c800e0710141800705045031281002480c88007070001d0100d000c41044000301c16002c01640d5041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 161479685 1250 161478435 161478437
    0x6061a0403080418110a02070e10050907120b03070806180d0c110112090b1b030106050a030203100314100b01031a0f0301091b030204240510050403050a06020c0607 72
    0x1040c545076444409890040784100c0840400b848100c10100015078011000b445120b04115214056507900031369032041d1f40100300c02895010080f0307100c1241c3c0c004050495800a03d504255500c200007200d42c200081c6203002401e49501d259040f5940900222001c0e1002900170001c5203402c00500c180722503036004141ca00d0f0083c2c088400011750082c601603029800c2441540300081f46e4004a4000794072a05207000f091800c41d000f0304000301c85001d64011520f403221054071b12840901c221403444207118500110384c080012068407030083d0091039102002810100e030b21541c98465400c2200050021001c0703410195038121160018400c14840c2082840c6c10412002c034144501d51000030011483d00c121640414400b441c3d4003504040b00035580403020070512403604505000b45601400200c0c4658101000100c0155040b651501c11a01a80c1c140c240d191402c42400380070442c50306208100241004040041041001540034951244a0040c0c1d81e4030701382515820090060700e160 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 161480935 1250 161479685 161479687
    0x60e0118062319030506070c17130311030105150409060b09070203120109050f01050915120706020c15030402040902031c0512010e130b0a06050a03050709060b07080a0804080c010906061a 82
    0x800818130004509500c000740b801c2c0071069523840c2c1419209003020610905400d4030010b813000e00451301c94035160840f486400d007801802c1c8511304041c2698000c440c04418540b41e00103031315007441c090300042c10042c0074410000704114600b010881700d881c1121094050385c4005444900b590340d2034038560040c80f00b40c0007001142800740007034010040611402e0b210b92075010108a0031071942860015014000b0401045100b089010984500440c4203c4015002d049060103250400e07951400c1040ca030741402900e165101e5003080020154018141d070140301e0b00e010010b0f01e190340740d0041c05005c0c40341c8890341c42e600c001c148059244070580014414242c40d00034450794500701d0b140004680d41c000e40d410580d03a11200312030300403d07031503101c6036100c4001c10000090110216900090302c00100741480211303202d440310a254801d5580050400104000f052180c601c1803e18507081807140da460713881c10214031001c1d0300755504c044046d10a55910303101000194000d0708010661079020f035403d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 161482185 1250 161480935 161480939
    0x7030e24160212031e0306060409090b01051e0a03060906020f031005130b090a09020f15040e0705030105010903081c0e0c03010b040c050d1104050907020d03060504060e0118062319 79
    0x16000c4da2400c85c014079450340c8040b000c28120755aa90940c3c01500352503208002030400c40c00e02035a014000e1140d176000fa04201d80b0000792030640380c409050b52401405c82d8400c0b92444d03441030014144003a00b40c40d40380c1d0921101c134548022800650140d050844400c0c506420039082168603008841038207042d030320740980321450b9258009202e600100c01030000480c00b000340041ba10458444101d56400788042c0150038030203030040080c105a402e00c2884450301e590300401510741c0e1000380070b140e01140b110700d000c0000a01e21401000b450040968441d4000702411548042d03c0c04040400e200380c02005014600342424480c0803031501084800307100c41c20700410058018803811420034000390312000300d4903150814404072001050302a0441080380f170300040003902d079200c500d00c00f400613060400005080c54140038801c1620240c00740081140d2a003a048900030540030b46401540d500d980c0001414900003076620f10382d03071030040355004262401c0c00b040100416928101ca90820400741 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 161483435 1250 161482185 161482207
    0xf030f14070c050a020301050705130509010602070b031509011401110c090c16080c01060302091506030c03091e03030a0b01030501080616021006090c0e0102010207030e2416021203 79
    0x160412100c1c20020420245070506a01300107110034041c1d019800c0c14240100389a201c1d0091030100107030322030b40741560b07151020400c0080e002e200d1100141d0190100741310700442c013401160084000c401e0051a01c0f40d140c013182d5503441c01d90282e4074801c544015800c5075604002a455030b002e51030050110750f00030000140c26a0320141c00341451550110380c91460251101c0d24601040d040030102d80c170765111a100d13601030503542c0400c0740144c107010042000b0310880307002c13140b0f40d110003010b031421542e6481d580d10303841e0030003415011140300e4299080c01c0501c22404038076281c004000916507030724006048a0564401952540c101407034900100110305011135020740120007981002c0305111030b180100e01e002d240310400a1041e181040020f90b0072140d40c048102000300d500c809040c060b8000041e07080f0300506001034041154034404a0181c540a0903081040700000d190403c00300101480403840c0c1c21161003009000b0102810380b00317500c0c02c4004441e80407003c0004500d04a44002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 161484685 1250 161483435 161483471
    0x9080d09150507023304150c3003060f0b091005070c0909120809060a0c0203045112090b0703090204110406090b09030114070f030f 58
    0x810031100c0044905040030141c0308000312805550002e018100b03004030f4400a00d0180103000c0f0040c3c5460640200c05100303007205d002e580485440303000c00e10420220317202c190780c44000b48900322101c0f500403460f01a8203416184c040802e40065280c950052a0040c2c050100c80840d00a143c450300f140d02d082025a6000003100d684080544002e41286440780d4259158010000001c10a0081d02004150403599030700118070540600e012043c61114102d099812030f905a0b480d040d140c10090001e0400c3c0e505412403400d03e007032841101d1070913a6609140c8000544d07181d1444002c1148409044aa42600280c101c0c4c1c40094004030010460b43d1012480d14400d0781080c42805a41200c1568504071030f40030125890304840c0705d01d01d078607040000130003c10780325408031700c2586048000d801c03030010301c400e80c0d05036065500da02da44a424070000100316000004c410382c0c55901c0c0e42c2418445c2c009100410300521103900c4403441040f540700043c00f41e414800d00c2c200141c0c0b50140170011064019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 161485935 1250 161484685 161484689
    0x9060f0105060702040e011418060a090209060f0a0801020c01020a110c091f03020d0b011e0e0c0f130e07110a030f0e010c0210020d090e01030203101e0504080a09080d09 74
    0x4030000361462441c3e82c480d014204c0003098482c900d023440c0400c0740c081040200320040086880c00e64072540d5a03600a038044034040000a03400c2501d246c00503440c3d0610024401d1182c2c0024241d1404a541d201800c0c00c0e03a2202801589594011921280054200240c02c2107c201800903003014501540420000c003c0204541c6050149ca85080b83d500c08469401016607009066103034068200d050084007020203100e00c4007002d20b0752074007800e900700348200842500e039500501c210907165001202040e0b0081c403034245170034104104d20158010000b00301c00003050a9290341000b460001e8010708101c410700102c3c811034214801c02e60000740c2c000c03607110300d0030030600b040048070321184012510740311a41002500200401e80314144640c0005201714103040c40d544607400d03513403210201d0460038000c0c17100075090340c020451003c10a00a80000c0f4004070484a80d001007818040a1026102d081d90180d80c00000040c0b0702d420998071401c80300181c03845070003c060101c500000184800c0b494 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 161487185 1250 161485935 161485939
    0x61b050301050312030417070f170a0e0f0a0528050603070f0309030909051008010c050403030e09060619050d0f091101080901110d05092e1a0a030b09060f0105060702 73
    0x100290411000030744e01030301307107c44110321f0f900c42e000391030100c00d00d1a1a580944064204034841076800382414110750291203a581c88412842648007404160300c4411000780d0311002000c404640c680350380d004401003140c048100071a200d004400e0858055458210310701800e01002040740305508a58485100030f00d900d0001050030540c1022150009207806c151141b6003000d0a120f000140e0000c3d02c015202000000c10002c0311100f8191190b103d0783c40010007103411020140c0d0645005080c81e68072042c003428207803500301c441c50031110350062581d040c1e02099002c03c0f01441c5016a1040020004000d5401c2148400c0340d180e0070401302e081200141040030b2000082c15014081d00506402c40000d40d245403030f4143c054952001c0c1004032803110040c403401d00502005007111420a20300740200a241c21071181c0100c00c180074103100001018000000ca00d04406a210b11b0307000300c004d600440c0d01142c01e0410703941941c02e2180c007401000c80340c9171080c0148460380c1d452089030820350381 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 161488435 1250 161487185 161487187
    0x5010504090b011206020417010207122609160b040603050f01030206030402120a152f03070f02030903030f0d050a06031101030b0406090c11061b03011401170103061b050301050312 79
    0x90349400001b83c41950460f0f00645094445d0800b1440150085d0a1140c464130300040e07590440c03c3d088070f1010040401003504113000518240354080d50781110b8010298006959a44100400c0d205e540d018035442030020f040000707400c0049039458403801e6003007400000c19003120b500d9500000c80c00c0c00301400103845400080c4030b03045201000c01444804c0350344100c80805a444a45c0182c005201e2201c10404405807140c14030f00c880c008440b80524500a50907460541d203804504a41e017480500300081944400c010004081c0e03009c102500d10240c60b440a5130ba00c149100304501512000f071b00d24500c071403e001003400000c0c048207031544c5080c821702c0c0000340c03800210000b5003d41a03580c0f140c020b680ca0800c61448466000c00010700da00c10110448803141c42c0e04654808204501e039040b0040c0b03200384018850140c195084030f100b01414034007074000034a10002502909000c0e403007244c000d9a00d0300d819403041104c0302441885522400c050707041d03600d00b001103511034580680035141048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 161489685 1250 161488435 161488469
    0xc100203060d1b05040f05060a03030809070314030301170d0e01081f1202030c010801150f0311030f04020f0a05090604090507030f291303080403021f02070605010504090b01 76
    0x450b000d10303412280d0012046a015510540c1400810300c543c042d81c1d0040b414a80700365800b2895021b054091350015140f450382c3c514648044030041c902400714001c50150003400400f01d03c0c1c18403a030360500500c101541e6254500a000c5a0328001810341b01a1a008103155012541d0454441065010203080c40c0880d035955041c0350040c420000d00007690311030701e58004076040c03c1070000322400c10320942c101da45005282006640c0494244282c1041e00e034078000c5211b1551103400403566480c520f041c0441d01703061038200e410003604202d410603800301d4060100030a500e014024810b2514044d07480807d114200f401040c0c803058024607081c00349032903041d035800300101045000300858000100420400d030a00e41149890301c05401c1100c845014140c106482d00040c546600a030310f817042201e9480129902669004c00c024415001c1d4001c0600c200301021b2812070311501c1400c0e2901c0141e9605007883c01000311303071041c0c020500840c50210031100080341001c801d03041d50341c09100d8103455a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 161490935 1250 161489685 161489689
    0x7020c0f0d1103010e030f0c0d050418090503270906100203121902040e070e040213060804050f070b0901090b03010e041e0c0b0304020310050402010e06280206040311030c10020306 79
    0x46205c14812248000a0008144c0c002240548a0005000161248404102c01c03c486a000300d00480240d00c68030740b0340011510076031740009003080c030a40c06c1e00e00703121030b00080040000c12140406c2c00507800c944801c0c442c1c94160002c552000301220051002107203110029501d003d4000d40640426041010a07020010001ca540b070380400301206655030f1b03445400d0780a8000003605c000003c9031004140010514150003600c1480c6120b02c0c400010901e0203604881801000e44113441c140103c1c3d26603c0c180e030061010001400c50b1842c1c42d1740c1c07590648001089800705603c2019020703028401800711a1000c0c80c0ca0b600b1941144c064501c0d0001c3c0803031605a0900650000c0c80003500c180d00107008a2030f030014503c50f60085056503001110b18002c14184c440c100d5001303000a411440362411485d10101804002030340080010f1100c0b004803800074954170413200240940d100404000405500c590a8051010200c0c00703103040c02d0140d060250f51302485800380846e6500440045c0d204d1f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 161492185 1250 161490935 161490941
    0xa050a0c0c1110021606020309011107030b04080904090b04031e031a010807050409060609050f0108070e0108090109150506041803020706030c032403060b030c06070f03020118050607020c0f0d110301 87
    0x50150085c5040c070f13003a80e8107406035480d0310103103c16010402c242442c0320340804c08101c1e034040700c0d001804e0154075601d07540c2d039841651045065031b0b813090351040c902000c18480c1151038132403407003902e40d4619106029070000d07561a0b80d0040300704040c2030040400c090b0b4070202110000c45003e0800741c0241d15014000d440b14020340d0011100c031071809034002501940f0180c0c240440320305590140d0681d01540045444240440d40c00b0b01088070301c40044015441400aa07500a46a000004a100c5103507110765400c10030899040c801600c0c0c00501c911483c00748681002000c041d40411709040c490ba0340a074a5030725500c200030500d42e44c1e25894208501a070882013030507549046a000781c00212800c641c0005c0e0602040d03030481d190a0680c030103400c00160140500c1401000fa600700074035030b40d030035440745102d5404030300715501c91500c1e506042c61038803010b1070a84904060551fa1820b005e00030714002c0c2c1c0304003652181d0703480304507502d076919031090b800a42c5401160458078204142c3c0445c0c05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 161493435 1250 161492185 161492203
    0xd02060c0c060d0b10030903050a140c010608060a0b0301020a080f040f02210607020d09031410051810050103120305040203010b0603131b03020604060f0c08030a050a0c0c111002 78
    0x40702000440406903c49030303202c905245001c44408000040300d5a0850880d11403070700040200d5001c00c2000b130214043d02c281038000d9400f0000901c0c040c0c0c1c00c06440e003503d4043d40010000e903c144280b08903581c6a01a51580361000e40c02103003045501d81303008014540140c10006400c41d0070000c02c0074080c221003241489900501034074125114185900c8203c081074609642d00d0084c03601050b00c0520200e500346980b14180d8406907514250740742c1c0007012242181c44151032040c40c00944070f00c40140202d9204c2d50306030416082e41000071252038113200107141001c032518607003001480002d070700480000c500a00386c42c00280c260360700d1003c640100b04044205070300207404000c220341100f0071407001c60814420840c049044403003a0040c2210f00582c0402903211009003c103000301c901c41c90301d40c9050807042c9400f14681255031520941603106680454400792205e041100c0143c0d180101080f8510b01e180a0115907202d496a00d40041d5084542e84101040151703c66558800c00c00f2510f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 161494685 1250 161493435 161493439
    0xc0609060203040f11010c020a05060c03040801110c1006081b060c0601090b03010605030a0b04081e0a05040e010b0306011e02030d0509011d06040f15090f111c020d02060c0c 76
    0x340d2418141013a10326910076020403180c4600002c400c00c410b5100362404100300e68003070941e4032000d0601041281079000303000384441c584014080041e009900b4041d0300b1500241100c0c1c266a50080d031105c50420a461260000c0386040a10070444000d000481d42101504000e0740e1607228203800004090748500078800031284a484000b10701c800403a4400002080d044000b049010365603030906864990700c103400b400400f00c80c4000f80129501d84028040051307100c2c94121401d0707034000002616002082d0b140c000510114090000810040495016103045900075043d40f5105000030040314200070003200b41c20058910f1001103000300b083e101190045d8505200e146002c1100900030400c550f4100b00031011450050000c900209809020f180c00a071f1103042495241c84420244004a482c0e05500d903980c2e02c0c10f0007080c0070315148101d203071007220480504201001084101002c02420100e5a1400207844006a1350100e140b84000c2c0e060394003030f44605a5408140c04e0071168803060b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 161495935 1250 161494685 161494687
    0x70204051009061505030c0c07031a0a060e06060711040b1c020312041505030403090b07030f09050901050d03080a02040509040503030109200417070315150902090a060c06090602 78
    0xa200720348075001503030040041003010326581c03c10401000c080542042c04030340708102190501d8801e80c0101030b4540b0b41b2084448503a0740ba9242c241410000c400a004070f0424410301c01d0504403809208020700300c503081c1440d107081c0040040e545126480000385210f0000100c550705d80c0742d6410070240000001d180b100c005203040115161803c0b061702c01c03071180c00340700744d5031103182002c400b43c0f01503072104c404080e8031980c03680082e40c1a07480900b0503802e010302482d00088129918008118140c425546e42060000351580a0102d50161300824847c440c8540188125201c7c900c26420054041ca00036001d9120080d5800091041d90000c50300013842000f0081031181c000020341c100c0f04004c80800080c152404405981198031a407102e004070108410040d03440c2e0003084080e6801e0300c03c207480c0600c0d80d0b0b5031008030540b50812350b822056110361b9072030f10048a02c019a0020480d2103001d40c0b40c8080400001d60009060003041c1c00d00002d0b140c5d0606200c2154044803c45038420700031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 161497185 1250 161495935 161495941
    0x5070603020c07050904081c060515070302160b220509040317090a08090904051c02100e07050603010611030c07081605040b0a030311030909010f030b060a03030203120402040207020405 81
    0x200a0362010b0880341461055032800105401e00611700c510139500519030300d04007884800e007102e81c0d010350450000c0564580201140c555128114044052803083d41e0366070301d441601c1c01031300b400b01a040320707100400305000420600300400202c80350445072055961180021484031003070b00b50781f03800c0300b50080c1212007000201604046a52040400e03c1ca42045943c1c401043c036a81d800c200b030b0000c28141c41408400040d04007030040c107801c6031040041d103c580f680800154520002502074000580c041c0d1002e02e0498442d10076480c40e9500d00b405021030700c3c200008a10340388030600c04d0800b080044544e45201d114103100740c1e980050003009680000e640c5070081030380d034444001101e12000001c100041c40b490300d44a103240251f00a416590007900d1510705859420a0150710304850208002c805090754500c101503000e4a105441c0c03844490450a2520040000401441c041e0034006014004240c002007626060b401c01e4032107a03960b43c2c44c3d2000c10302038012100004d40160421080c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 161498435 1250 161497185 161497187
    0x5060c0a091706090f06090a030e0406080d030605040506010504081c02070506070c09110a0f030c0203090d0c080705030607270f030602031602010612060902040b0303031806060d0b06010c0609050706 87
    0xc43c0d016884807030443d00505035480e41140c0710142a20101803d501651003100000c1c001c40c0e0407440110700500000e503403699401c150b401c0c41a0540007000003569504144103a150601c0f4041d0040c0081ca800c5080606090017165200c1c4080d68001c44e00b00d1803410351030200c1c4204040c0001d00001350205072540c0300d03031800e00721102a50145003640c5040100144005a55005403080028030b40c2d5a45805400380781c040c0c2c0203200f20f002100c01c5002c100300481040d11a46901c2000501c20701181c03003001d05c0c1004117800e05080d0b400051098116400340140b980e8441c0240c01e0740300c40680442171582110000c1001880d199200c070600000c258000410700a00b640654420480b0320721007071700000c40e54000c03030807a1020302034061141c58009071403001c03e4540d8400e0407603520281c0000307101c00d21600000d26582084030414034105511880d4002c8010501680b0b030040016206054140d40c5035807940f40c8032000500301410881c480f4800d07002d0041079000144e180340c0100070f0ba6050394807240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 161499685 1250 161498435 161498443
    0x106080f0f0c01080c04030204021e042c010501051215030604060c0315050102070b090402070c080105060a06050c03030a020d0f0903020d020706050711040209060403080c0303010504050c030405060c0a0917 90
    0x1d95901e070b8000d0208680c1154050750a2601c1031402c5075410b490a829942040025000541e0b4000788405504d8030140c94855000104003138901080c1c41d101843c51640307002c408800000300821340d4000c090040089036000030681e1200446048103602995805114440c2d40420450b520780c14492002480107000140c2d20660000d02c1581d420701c01544030030302c0280d5142c903a114150059000c800200710604800c8041c14000400a01c0945000015105c0550443c61904130820301c0c2d54801c18000d11f0300d4040480070007070500b1b0801606001414010b1038803030200500c908a50758000406040321002a40124519201d03c00d0400c911701d06814001d540c0c1034098404005441400300c0820f00a01440c15941d5041e401840710410301000c00c1400701941200341400d41005040c480400043c8081d409848441d03005d0004623101c1d85000c0070132080c4c6601509110035520100240008503c000c5001540000200c005554940d041c034022103045110358080c0109601e4040788907041034000c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 161500935 1250 161499685 161499703
    0x406061a03060d060e010e030409141b0409051b0c06010509010909051c050702130c140405030a0f15060605120717040b06130e060618070903030806030106080f 70
    0x140c180038005094451a605a200584034240d02c080e52141600000c1d40d80d81059805800110021030009060403c0340c0c50b580068100480c616198182100300791a1502415845801d80603400038070104401d02031468800d074000c1000442d1180005070100e5460a2a07401803058000b107039a50b100542000ea841b404203018242c424502a400042c10f48214020048020382000142082c03442585a5012200720301d101e882c180700b4103102c0300000d40d0b501d50311440c08520003000424103400724880100540f000014402900a0500051202ea10000760302d00301142d1019207400c801006043c1120f10f0050504030b0f00c0e00c0d07801e0000124034264800b01605c0102000340300b402c002c1c0c844480907035000301103000605c901d002040004002c1952803210030b41104025000c51001250b440501c2c0940309417150003102075001e041800801d040400300108460252561000030b4101400000c03c02140c601c409810004050301040345503400b90301880c0241548422502d80f06451014980c503201a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 161502185 1250 161500935 161500949
    0xc09040f060b01021204140a0504050702030a02070e0403211b03020901020606040b0306070807030b19030311010e1905070e0f040c15091203020a0f0b06040f021602060a17040606 78
    0x400788400d01e5000003000740c1040d032100c50b042c3c2003908140b8403200074440c41d035012358480b04400b0f00051584880c441c96000d864950b02a40c1d50310200380780a45420455403082150151740410040881d510400c20b44d03c210854510002020b030100b440c0001d070101304045089003540700780c1c40c071216415a000b405444020b03025640f040e59800100011140314a46244e0540c0100d000070300000c0c4203601d280e6000701036040004454540c0301c0810641e56004281040001d42010b040c0181078106a00c9220458428024400c15005a01d015120f4103070100145850300001e00407020004148080c0780a015007090100382ca10b05250384040104080c0c03803c0c1d03021401c5210100d0100040f111051a00c2610748a031407010b858a043d280f156110071100350b0440c065840f8000000d003925041030202400340305078100c142452010002280e00e42a2443c02c85d600c1008180ca4094041c5d01c8844040d804543c4152208034071503095034004141d8041d1401c81e0b0a001c1000300b0060710354090800d481175 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 161503435 1250 161502185 161502191
    0x7020c010206040507030201030c02071a04091404200a08060916060513050118090e010504020f0a0e010b09040e120a0e0f03060f0a021306170a060e0a0e0c09040f06 72
    0x191001aa01ca40c01654098219000804203201550183c2c0022500540d0381c8110f42609076500307000c0c0380e00d164034a071003820f903000054100b00c1c1e42068011500300440c0d220142c0302c281070580ea000c040d0136504480d0840102050040c1c0016640c10858100078241c0405940c1c07107181030b5104948903424003c000c501c002041d0804281c140c030420545000740d440d5580420034074144401941c0489408544440c0d0314000d00d0082041e82c801d014107043e41c1c40340c03000480c180c105481000703000e0091514041c01004d4101c0c04010350400000000d0441d07400c4403450f55104104800318002d0980b803050700a013403044044504c83d0401482c001e004000f0350f6901d105040008900708100c41248954950f819804000440e5502c804110210f400001080c40103280003800300401e0020911a40140003241114070b034440c0148a40ba9965881001820100f000c54280500c00000b148040d0143c25482d64a210100c0c0000c01001092900310700240461540c2c0303842d00d0540705d0340510f000c0c100c403650300f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 161504685 1250 161503435 161503453
    0x120c0e070c02100e040f0e0d08060f0d0b090102070f1407080a080d051f0b04031103010504051e0a0b0115020d030c0801060c050a061109150403080a0e0103230702 71
    0x403140e00301e00030165004005110b503480c0c24000301c9644091242d4180e02650780c00c1806031407482c600c074406462000c1c0e40502000055518040c040c070708010155800340100346840880d40c0d540c41c501519041d81700c00c0440880c1c0f50310501d640203004d03c64008000b641e0b00100e042c2031294850034020991902012500c0e00c1e41c0341d052a0752aa0070261000b002c410381480100c0b4034072055000b06031702c0300103100b002c49005015106100d10b200d940d445150183c100003424000c0c000c1d40300d000d5910800c190000d101a0900b9610340c3d5403601c04a15042c03e15183c580c038141e003070100384815035486821000c100703001c0d615011070310054640d0764960b60141c8690304495a50300e0080c002d1001d118404d49942c0308583c80c08905071071030a294074007114540100c0c000035000400501c120302072110440c1c0f0141c0c84058a4052180740c02e0b100c29030100f4100140010000079800d50f04891a01d0014907060300842c01100060b00030303041c16030f600302d00031720401901000c2c0a0b03c807011600c2400e281c1e0865007094 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 161505935 1250 161504685 161504687
    0x803040b0c1801110c0405040605061e060d0209010c0c0f180b010c0b090a050102130302040c0203040f12081204050c130b0603130c0b031503122110120c0e07 69
    0x4400c0d2103902c8840d600301d01007280c56601440d411688644038030140d6401000d00000a42210011070f01244e035a5521003e00c03290f420124503084440d40c562815003003440380e80c0c001410030302032480741020711500002d83e1030160b48141e8048545039880320281d0401501c84070020350115980c0200e204510305032036014104683c1f4003e0115800701078440c82c0c07a11015444180795500c000f0300b890601c0c410b851010340056400d2005240c805032071420810600d0644c410041030b90b128030344450440d032003480180a0b44101004010840d0f080d45044c1a004000345008802d60041240401c10941c40804200500101154658024004030b4940d2548030f43d5070042000c40710a91845a0805070510025080705905c0308885400c41c040c1007007540f00b50391030741c1401e032560044842400c04129a007031942c940c2420007000242031941c1c4a0642050740081c80c200e024111400c141c8200c071812004140b00040303c1c002640902203102603800050018281a6191a002e2080760202a5541d00182d005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 161507185 1250 161505935 161505937
    0x60a030903141c0e0115030506011805090303070503070210050a0902090123010e0301020c06040302030a140a0e0609011e050c070e07080613060f060c060b0306090706031a0406030803040b0c 83
    0x80c4000c0103886003030703182c1c01101100811030281004e2140d96201c18050900360516002c10065118900404403581001003031144103e100c80b000c00483d0a010521000c0c01012013500e5100c065440c21a81703c0d90f40d50307402c900d8542900c0012280c00d1411081c0320701c4000c140c1004225500076101203c03170b030740d9a011480f4000300081d4001d1505466100119596104d00c283e44000c0340d00030000742c10054003000943c105003007641d007240568400103802d0022600201c1010040310641d60700c0d42440d50380d21b0b010b8440703980705405612400001a401701c80c0d81c02002d42c81c2d0000c80240e807a0864010148000e802c0703a0209203942c0039485000d8001550b42e940000891050311107a8980c2081e807a51340502107190401204c1c828280d44035100840c41004642184000389410741c1e40d104415100d060403800c5030003c0050300e0003500000100401c11000144120403a00d440c0f80010f4840280e180071003003211800c1231950b010b82801030006c240314180001e10702030390007074a02d5031560310340010300501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 161508435 1250 161507185 161507197
    0x10020c06030c0d060302030d2007050d08030a0e0d0305011e030f08030615070501020a080f100e10050d050705150a2a050105070f0e010c021e0f060a03090314 69
    0x22003a03003000012502a964806400f00f44694180400c5090f102d500190800243c5ea0417400041c1182c43e00030840f2400301c5011080c000030f035001e0a080c030f05050102d03568803c44034000c0c00c0341c0c50000101b42582003580c008442d04000200b07580310314117030f800020041c00080c07043c4001e425044c4c0054504014070b540701800c40703610800890810b00d01d0340c0c40900642005200580c00302c000d41900351411004401030001341d20a800045e0713104010b24018124cd007029044031480c0402800700301d0000081c41080081d9401d450060141d55100c6a00c0409002035030003a52300007006d200800204000040c01e0010f94004581081003000034034000e112078040e1400c02000100644807100002070094018ae0500340c204984212807162512090f00f5100d054505100044d500c0360310f04042940b0400c2040c600009280440c2e04a225400194540b10000030541d2462114411101f0513601c0380074145800501409142d01c900b04414054000e280c1c0c07000503004030f1241c0300e0b092140d03040c400807104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 161509685 1250 161508435 161508439
    0x50d242f0909040602130608040201090e07210b0312030613020a1202090103230f01050105040b0a0e03011b091d01030c030f150203010803040602010f05090319052710020c 75
    0x401c103000401000310800c0702400594000f64200205c003000c2200e0b8039400f01800a585076403c0e0342c10a440014030b03003e4564000c40700b03030b4008800c0c404407d5100141180c041005032110300c98841d031660250060062107000f9615200e80e400c030b8a041001d02000d50f200c5c000c100e8810b100c0500c074900240c00da12844103000000f83c1081136030800224a41d01038240344406160006450b0080340805100d6150404541128842c070000c01000340c04815945000d001e080c0790442c203107446d040200600c0e00175409000b040c4000000c201000381c50035440030203072002c60108444020040003002d40075181034061842c480c2d403ea083c3c00b40c50140c015066040b41c2d07020410041c90341c0f450703d880a02c3e90320072804032161401107504c5070518100d400614041c2c609440a1a5120301d00140a42150110300c0c0c0340b1304042c1084200590914044141e40c0d05c000313240709001d2000c40c0306070110790520400c1c2c4400030300c01d5640071408560b55140c4010075074078000d49a06201c55025581170782d490440400882d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 161510791 1106 161509685 161509687
    0xa02010c2d120f02100b120d1e020c0a050907020f16180605091b0705060a0b040c0507120e010c14061f0b04050d242f 52
    0x51400b140c10300748a0b070520310070503003c0e44034007652910140441c0da944201010f030b00e4030b4000d03844a035800000d460b0440d407200d01c0900031296035080000f411000051003510940009001d0060210090503404100e10304400c004102800402032021802518002d0301d58440410119a03500e41d45480050258140f07044500501c0c40300508000700c0e420900d04000c44d46410329070a03005800c0f20001074500360000400d80f81c3d445420001821071144104000390005160304c0001d483c58121000c0c0680410220211000e00600c48068090704500300e446030994010203042181c0c2d0010305100c001c00c022615114125000015800519044013003001045a204009490300e8201c2c0503401c070075070b410b2012802c502c1c000c50181c20f000d050b102e04d4180c00d124182e03440d0791981d141c40c001c080582c0c90303024000d0007801000700d842c088107500740030340101c10001c1800001600644a142c1e = true := by decide +kernel

theorem cover : BRFrame.Cov 161330935 161510791 := by
  have h0 := BRFrame.cov_init 161330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 161330935 ≤ n) (h2 : n < 161510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
