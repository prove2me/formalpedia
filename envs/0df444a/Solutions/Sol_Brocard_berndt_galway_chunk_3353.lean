-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3353
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:25:15.81463+00:00
-- url     : https://prove2.me/submissions/912941f3-3cb3-471e-ab11-ae34e341d2f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 602877697 ≤ n < 603057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 602878947 1250 602877697 602877707
    0x2061801062d050105040b090907050912010603110603130b0c1306021006050a050a0e06180115030b0f0114161502041a0711060c01021312062a121506 66
    0x2001140d0b50074544025034800056482e401544100c5035145420320140041e4240568003030703882031a034a070031480d021707680e40004d4107907142c00c3c22854260b665a20a2013040740070340c07015000c040c0445085040d407800403c1c00cdc8103c0c0700c000004281c014450301050203814020243d486507900c3c1d5500c40f00701d0b038503100003e586000c0400c10b020740d01d09002d000a03060404401e24010b440c0701400301412641400201c01d00800c01800c0d00303411140e5040d0700301c0107180c007600f0389001c0d0444a06080d5614039521004090b1100c07030092a01c01d8408010410030b0707a0b00140b4a54070642000509070700d4100c084050090b040e01c4400c007400e8000c1d5850340801c5047c2d10350060060f1000c4a403810148241440000c4203806008801001550f68080480702440c0c110058214507010000241c43d003044031314843c16078803007a4448a10707456100075507000c22601c1e0003152607641260821403552202c8c03180303104e1940d00c190450b009201c0c1c000701c0c8219011181d0020480720fa200580112003a13030391b020044c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 602880197 1250 602878947 602879009
    0xd030e130e010b0901030c1401020703061a18010806040b040516080c12011505060906040b040305030322020907031e051812040e04020f0a03020306190506030d0206180106 75
    0x41d603503e481c52814003840d11800082c1a690888000c80b0202d00f4400104007003823045006a042d40f01d4890004000747e018011404c0a0000590640b01c40000809210160a22207410748011800000500005030300154080d8469081645500c140c0c071207040c00346c00e025090108504001c50140d0110300b0010000302109140300a0303a005a404034000b502900f21010035070441041c03043c2120412041c6014000780402500080ca00c5d46010b40d02d820491155009500458103600044100180c4200008103c4002012001c80f6041c20281b42d0025030001001010002490342e140d01642818416035501c99000045600410841c2445503085940320a0308040308441d00c26030301440f0b8400460400e80d0201d80248010796030f16100d036401c000800c1c1c0005680c50700719290b00c9001026a0341000741b0750003600100751184039500100820b20a54100400503401380d801850868400c1c0e0b070004110703034050f044507202400302d620b002c00c00d030141c002c0c0d82c0041c900040040c84080e4103942c2c5c5038061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 602881447 1250 602880197 602880221
    0xa27050712020307051002030c03192303070f0915020604060b010c03080114180106050703020c0406080d0302070c0e0f07030510050d080a030e0d020f07230d030e13 72
    0x200001c1d60780468210141c00d140c0300a406400c03c0108101c01c1c01e001c900c0d03116882884c01940e05140c404162180740d0b801c001d5501c50301e01c402c5850081d090790001c41c2e81c6043d070754104250340442412a89a111031101070450820448101d544a0041c1e10a20030200070b02914483c1c030b401002c080030000d580701c0c41600c0640f0f5140c03400302c1d0a0b44560282d0380700d10700d080d4152205105a8030740300c000307c2000b80f0524001e41042e01c1c05a0b0304881410908c8140c060030164603a5a2141c0541c200245070820b030a5845009514000f41440000c40004007071034a14078034500036949a0503490920407100480e8450220420b408060140030710400c003245d886403000d550100602e41c4c401da494041c81002d0b12a19403c414842070903004078003440000c184090340c904021030400340d181a80c1e031504d42c11880800058108901d80c0e801d0f103105000c40001021002813581c00340d090b41450786c40140f60081c2c03207403040c41324685050400d805038a40c0000100000c0c01100844da50740402d01c003810490a01c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 602882697 1250 602881447 602881453
    0x140c010915050609040f14032b050c0d0905030f0d0902012307080a051303230715050a0216060305010e18120310030c09020415020714090a2705 63
    0x555080c0c0c09602c16980b042000a1000ea07050301d9546800c0045c603100b042c00e030358074890400088140ca1040004242c96207505041010b401c801c0d0000ca25580d004855450032a400c007000e22600e000c0c290250b81110403561000104401ca91401c1e52861140c0106010750401c00720f040312459082c0d0303000a1100c0e0003a22101c0301110b9200050600d185024280f215811040c8407550202c4d0a01024150003070442c02c0c600d28042516031400c0d20401c280c0e000b222040000000070f02c501c56041c2c3c0c3c1d10505c0c0c1544000303010b01c40c1850204044210503d425104209010598000e0039208010010b0f0500c3c0740c0e01402c0c00c4546904000b0054103003405a0540c004643c40441c4912030800115a02a00441c001d80b01c0c0302e4444c00740d80425800075150001c1a45684408808925154150001400b034000016a0f0303c1c54a600901c450442c4100303007003550400c10041000d0022010501241c40341260089890355a902418004014184401c00000c2040858010840e02001d042008a00600c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 602883947 1250 602882697 602882723
    0x30b06100f121a040212150a05150a0314010803040515031303081503010c260402030718060b04030809120706050d05040539060721140c0109 62
    0x30540e0150101200d110000b504078071481c82000c416031114402c0e901511002211401034400141070342c02005048200050b10401c0c4030715100b80040d00e07088110103035841000c0d5850400050f0408031046125101d0900014400c10214400da0101e0410034210000c031030f481d610b81c901786a40f604240500c5001c0d020000ca40c50101c640c15080d40c0c400c0c00342003124941421695000c5940450151440900315681480c80a10ba6020300401c1c100001982e034207200c000c00010311007009440045018200c1c041c44041c40050303103002c120322050703070411600000000b501c880404d00603c820781c003500b840c01d4049004010407510800074400e44504a03514010130303a00705402511034805124420124100700140c050170342d0582c201c00c0d40a4024025240008080d440341d4000016550034080d4425a10560400c400e41080c20078444507015511103080c0451666041e41661520036220780000c0d43d17160407405107215002154004078035841c0704da00e45c00829007060180c00149000c1340c41c00d900240e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 602885197 1250 602883947 602883979
    0xd0203180c0406140f030708010c0512010e010501020a02091305060c03011815050d0609021c12030c020a0303020c21041a09030714031908040509090307030f14070b01030b06 76
    0x100b20541300801c0150504285142c1080321500c4108a01c41e0103006104000609642c01c0c410343c90a909503485069403184d050719648a40c040503013000b040902688018032859900141d0408400e905541001c103548803030344028400141420014040e114030002c00031681c2082e4091070407076250f4120304034400c0e02c3d10440310650700c0500e82030082107040c0800f0082443c040c0348544410307005803000201c0458a03008600c042c00400000c044e40e51503241a001089103003040050760141516080044050180c4000d480c0c000c0c4c664080c2c01c140e008168000d9171b54041c410410702a6880805581406603c078035036510b5003051043d0181c84003410548512121044212400c11100501802e942e504094024280c03030003208001e41c0504c55035001f55404800212021201d6025800454481c0d2070309003004102207000300186031680051100c400042d13001540c059051506040c2117105501c40300b502d40e510300581c1c2c03001d00b003503059000000510544004050043e241543c0040001750102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 602886447 1250 602885197 602885201
    0xd0f0b0306040210032a261902090603070c0c14060304020d031e09140d1a0a0b0d03032a050f0901092d09150b0f0d0203180c04 56
    0x4202601a044040024010300d0941002480ca058506001030240ba1001c2e880c16410b0001c1c00a1220f2920458041036803508440315012014084d4102c079080b511680035040b00e0729000d005085825038054103403400004a40640306810741c0501074076100e00e0130030390081c00ca402d03030313070007502d04400c0b248000c00c004088201e400303001040a40243c1c51515130b6400e00c0030040f003102c816810070240041014801c6150000080c0003d056134070f03416840d003000d080b42d40600c0c0031381c0b02910900c05e04c02010009103001c405008600190300c00344034250740d07140304600a814611049580010203190300010075030550b00c01d903a421201b54584413544c2ca031100114258800380c03510000300d441804a4944030304500014120014185030040321213030f076550200e01d000304402c80c100001000b0102c5080f00368045000c84001e19003a00c00340310201600302100c41c02155070113201e0031044000b80c2071112002c0c00040b00c1c030854003030700215543d00e0320088404141d12130510004d550301030045168036501d018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 602887697 1250 602886447 602886461
    0xb1c14061f0c11060d050c04031208070e060d090206030c070b010b0307020a0803280c030e010c0f05070c031403070b0901050c1812010603030203220f0918050609030d0f 74
    0x140c0381d201c0812031a03141c40c01c00740c0f0383c090300c0b0341c0c4000d081040104d15492802403d0040364003182c4147c03520309601c0c1c1016181c401189082c200301e4004204101640e00031804411400c0c199801ca13a0ba070111102400540700c030107000384d0003000000c18040ea425041004200e844d020b4410a9035698a9061070125440141c0700140140d0040c10544041001c100c02541c104c041c20141c031030685506640144080c8c141415000b0301c5e80e0300c41c0c202c1da405030140582d081c0360034410020041c0c50308a2402400e241180102401009400705803e8100203e402d035642c007840d082406a04000b2000103084d035203520404089400004400c00309440f410140074090060250f1041c0b181008503075065030045d40a00390015611054003504454014028401c25000d07501075130207155140000013903400d1801049114480705515864200111900b500c0b054055170440140030403081080c1001c1840d45001340b00c040c0c694000d480c20311141700000001881507040d204410722034003075090784500c1100c00c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 602888947 1250 602887697 602887759
    0x30309030306040e0a0b0a020306010e04150b0a020f0a0822030b0109110d0c09050103050115140a050705150f0106030e1b0111010c03091109040c0b1c1406 68
    0x70310100710503107000d4011020142c40c80c1c08032001c1c440c0302d4840301c5c118082030f070321601e003958000305001c1c031542d02c2668860b07184020b550038004651200e540e4010f5030350b82d120b00e8038444808141e2400442c42400000c42103800e0f00c08940c8824050300f00b8904a80c004904144240352002c80c280c400c0c1c1c040381940c03045071b401a00c00d00490f8604414180500081403140c1034031401007014500001840c4110a901500c603a40e9208840c1001c2c000340c02c4880c1070300003100d900c3c01c061821110541c001003035030301d51034030701d60300e03511545048815622400740040c02096800303440070015001c91002041271260700040c04002540c1d0741c0e01010303011100303100311402c1c03640c22405102091040c01002a05400380c1890b00b81403910f55110f440e821030b080f00d00708000003074843c00014180000c0005440342141d003181c0c03c110380e0800341d0303079507046070784c18464950409004289002402902c1ea0100b07540310340e0803030034802c10b182180c1c01105200101e0f80c0500c00d6032002415401410070300e1203120b400c42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 602890197 1250 602888947 602888953
    0x309051f021f0209090705090901060305272b030510140609010e1903030e06030907031b05041401170708030906090a05061603021005070c080307020a0c0e010f08030309 74
    0x20042d19041003454045407000c4010381c080090100030b4542103480e610519183c0e40d4107464418000c20021035041c1a48020100342c02c00c810b000c00d0030000e9141c51110a140442121112201007005003004190f011000401c0d0f01c0114480e031051a150390400403460310390b010070103076a42d01400300307408896001d845140d4041c1e1201e003c0a081c01c8c0002c0492480506128100c40c40307290018a410168100c008420096030780200101034000001450501088450a085141c6648203a50707440c110f1202030030b402510b0203045200b80c003611151015100c0500140b01e80c0c004080001144103003840395030542601c14940c00414a4013083c0c60003610014000b40d480c095110003001140d030442c0c84c220741c1c03096080c02d0000b4250f4649004080710708040e0084a4102640e04019080155500f204180035003003004101c5030b04c0d400482005002d5202a107643c5035102c00c44124540076032180010100100001c000c0f4841201602150407501e095a4200c0340340d03101e41c21103441e03010030b0300c440030642c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 602891447 1250 602890197 602890213
    0x703050c091e2e0302040506221806170d0207090518010f2304080f03071115090712031b020f09070507060f0204031e11030a0309051f02 60
    0xc60a04520b01e414900322648024600028000518185406480c4440781c20146100e03100b071046049104000c04040c00c045007007900e0100440d4092240d200c042a0800c200b80300d443c059401d2004940c09020f4014a171100602d400349001c1c020714581c0145401d01c00e01010310041580000303280710000c2030303550241080f5840c10512801612000d80400340c4008070039000039040c00c1c24801c442090600c80c0300411011401381c48001e013480c0003503003c4c1140000c0e40420010840d4030b411907aa9548040100da5240d070340103c102c8442400c008000c0c1a401103c2c040d8601c5284205ca0a005542c080107880301c0a6a840ca407404170000000018040b4901240c04186486075115103080140042c040c2c0480c0294000028503030300040f1102c8001c198040391038418440e03a0310034404240c00f81c080031460141107480307000e403c0e42c1c1440050245a8000c940e0010000c10704142240c030900901141d0701450685005000d001d000d0056038015000c003440da00340da48a402c8408080d14954020781045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 602892697 1250 602891447 602891449
    0x1032006030c0d09021210050a1b091404090804150f0f17060307050607150b031f09061118120a1e330e070303090501050c100e010c02060703050c09 65
    0x581004207041c0d1b44203d00002c0354480786000d0040140e40700d900540001c180ca010140c1008682981c660340e0101201c00000c0e10b012030304540301c2d105580c0120781564800380f8407000100500100a0b004011682c08140060741c01141481c0f103000c5021074642c0300100980d860216003400d0303e031a400000564503440d4004100c420b05d21590840400350603a541e094803400820ba46a00445046801d0005101030114080ca070303104002040500310046c0070390342d81d00361018400754138002e11480038640e030b103c0c04000c11207243c2c0002490400100c01030749404e41304070641891400524900d0180c00900b91102c0c00c02404103110741d5080c0e000d81140c45141c3e02e01145c03c070030104000b0860b2038076011040c640c01d03024145000b0078128248910500d444da01c00704848103a80301c01030480090782c000541840041d411050b400b042d60003e10f056a1a02201840c3d1850a80c40d035032403100080c60007a02e110301c0c0c6010b40080c0d0840c01c95400312401612050030032000c4074002c81d001100c1060a202503115 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 602893947 1250 602892697 602892701
    0x2010c050118122c220c0c050d02120a1d040e0c0406050105250201110a0501231b2a0105011409010b03060f3714150d060e01032006030c0d 61
    0x21401101d01c0c3d110743d060100340c45000c44640d06c04001c046004502e0407070030050100b10042401c0242d10240029001181d1090000d000310f0845800384521400004d040488280801391103c2c0c0044c801cbc480b142c5c0c019041512404521a014003450400302e0110345075004904654010112481c04118080e48202c41600d2124004089042080108081908100401652002c47e00440000544919114900355040c00c0b03d40e80c00500c03407580d010445010031120303220a600307440e107104550f994560a58003007149004400c40c12001408415000c0800c41540414140d440e642c0d94030f072095081604200c0d40c102e00f4420b507020140b040001540da401d165141e0592440041c0c000c22018900c21a520651460b03102d802c2c55019241c40c8003240034100e00c11200041001c0d4a40c50200d49410022a4150280708060f0858500000e0725100c9171803e503109074000c00001c01c6c043c000756101c0c42c06110003880c801c0c0b003a0790880d21400844061030b218040f2806000c030003004900e010143e050440c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 602895197 1250 602893947 602893969
    0x2070f06090f1719030903020c01180f06020f0709020405060d020d060b0c0a0203060a06080c010c050f0106060203040f050910060c051c12061205030702010c050118122c 74
    0x7924201c01040300d40012074400c1c020a0050107803501a482d08078209822aa06410204ea40300301740c240302c800004a60081070350001000e081c41c2c462221001003110388842005076002c01c0d601d600304200060102d9001c6560540b09040405490341160b0f00c80102050b4000d83c000c040d400107040081214008840e8001d10760042d10003400b00e1000c2da10705401120350048030f0203e410b508900300c1d120461070103101c5986d120030112410001a4185545c20f0785d9003030342c17900f42e6041c000d04010715803e1007410440c100b41101508002d2100a4540100a40b660071600c2007421240c00d51102203020f103440090a0f00c2040048580460b2918000742203034540708420042d0b0b40341c020883d00000041c00401d45c1c0b04428607907156247c9000310381307015108490081d4030681c80c90b6100d51321040002c030044215100702e03409203041012107219051450052001c15001120300c0c58105009040102e21180401180c00544642902c10810110b082e40800744079074035415000401c1030b1240e5450041305007a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 602896447 1250 602895197 602895203
    0x330011e030503040f030203012d24090b01170f0a1107020a0306050714091807090f060909050c090d14030903072303030a0509040513021804050105070302070f0609 72
    0xd5503640e94a40a09551064100d0341c081003681c5014005d40c1803d010320b091494401440e0034406c10189101a103c54174015440701131922140d11000780b0000011000002480c4c081000301d441d551100000209a9948942d0104440308850940750a403600a01d115240e4a070134426a661a044500c00900c20183d010702006000d20264001da11030408400c003451240c100018079051055028110f40303d800402c00c04000d04204ca10319545400400b0740c0d2090200c00703c05a6900c039040180d40c510500e0b08410000c0d01440c80000302d40c1d9020710b261040703a003000f03401c1200741c940c4000c80701d01c2d00c40c1c1080c0d0b503002046408840d00207080c4aa008810011490540b400c10300000c002905040c2298046605501c80c0e8044903081c1d603181e1840106800b0031002146405103030701001e0994010030030b456205c2c96485001800b0b05054500540a4540c0144003003081060745401b5544a1429502a69150f2821001403a024040c0c0300303c441082d004a10542203000c00d644503005030900728021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 602897697 1250 602896447 602896499
    0xf061b03070804170c0c0a0801270317190c0528200c040c0203030112080706060902161406090703140f0d0f031b050412020102011409033001 62
    0x802140342e5450061302c40c1c085c441003e0704100c54075600300f00920010b1380016035140d24102440c551030b40b403071007107001c40707486841e81046404250400341d558183c030b451643e54141d40c100c200000c410151700c0c09000858651010044801152000c440c24022885440b1501c940303040a07403140341e0244c0403408180d40c14a40404403040340a40320400d0190301c4080000e075801400c506410349882e00070f40e0310409c01d82c4019400c41d0701d0054080742c000403c0a020b0524440020b8000900c003103500314070302802c1c99140655513503403c2000c80f40c02176556842600d0070046d10200050780040846c0c0780d4081e1410f840100102c07411a10390303640000108840802c544144551000804824440c05aa040a907140d00910700d005c10400303004c0c1d039000d140481020220088001c00c5542100c2030f00c041c1c03045280040d442501d2840185d00509090000d1032210203034030200544204004000c0c0f180130400f4203c0a030301c0c221520300381d545280c1d4100b125440342c103050051060024038090020300070701e04c21032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 602898947 1250 602897697 602897723
    0x50a120609140114010b030c190923010e100f032c0f0d030c0c1203150b1c090b04020603041b060203030a060b0c120d0204030c080f061b03070804 64
    0xd0729074000301c849815101c1d84d449100c1d0303031001284140120700611030003c40c0c030316600c0c1154038a203592040715041002000d031500c080c030b0910f20402d030b4040a0000c0ca024ac0480c0070400305480345075039481001c2800220044030019040c100344028091048450f01c074507100b0000c08006401419a1581c0036544281902c0742c180e4500111410b80c00c41d800050241c618076440c1280d0b1410101800d405030701303042c103000d00c0c1d80895138840b05082e001e580096003100a002180c4049018280303a40c0042441410700c440807441c44400300007001c2a108050194100f020101003c0c0161040243d01a02c421100d800250141c10007038000c5520500c200040246144070b00d56803100c40c4400e4210500581c0084104141d10506125510207005070f2002c00b800c206004000690319035803450f94208910000c00c805c0c44c0342c0c40640594001d184d11a41d1f07600b20688404c0310954400290110540500c12080424003001c1010340400303d0311f81c0001494510b968140007070b1030218020700116014414400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 602900197 1250 602898947 602898953
    0x100b0d080d061508040b04080f04090203190b012a05151504060e0c030a1a210706050304021e01092402070b1603030f150803070501060b04050a120609 66
    0x40108040e0500d220002410b42c00e10410101c4001c0300200142030200303a6090001048000d511075600680c031031049540c825000d4610012806a54006400c1e18004801d01c00d208800b075580d4120400048004c1150b20042001140c218808101050181200d5141009a010040c050b0b2840f603001e1b404460890b015604d00381072104080310101e0300c2e0549100d1080c0c0303a180a0085100034181204c0349492402d00c0d40f1300030f5540c0b00190038800c3d0711340d40740342c010b80c2051226010b00c1d0b07280c4d0041010300c01c110398044420355900c0c600b800c8082409a8030001c190180a041502d000e240c0107401600050061200d814038000640225414031600d15400500d4500900d41c16032071f844682002d0710700390320020002c0d241c00401e80080072900c10038001404940d00040110541c2074040c034000c241d9840c01091003000f01f000101c1700020000180380441c45110010041006920400c020440c1c15038450b0040328502a902900760300140406003000a801c00c40c44110b80140500c0001400003403d40d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 602901447 1250 602900197 602900213
    0x403080f040f081209010815120d0201050907080c1c30300b030303042108010501021506130504050721080301030210112d0f100b0d 58
    0x2800d0540051030000d8140007401030314980c0001025a20000c3c4042011003420300504d003d50040e0904105540d80007c2d40400c5000c0f0007072038008094040710014100103480c0c0c0c1c540381034000b90809907007400c01050408078005482011908040c0180c2502c040490400c6011980d001c103000313103810119503a101040b900c114410002561001c946002d03241c05070940350a0b50705011030701c01e21170612034040300310301c1e413005000d40071041c01910680045407041210081816021541d090b120110030402040101da044400307005101d001e036030301c0c01001e00c000c4940c0d40703090241c140107800c80e241664402540420aa410981c01040c0381d85000d488510b40d070456070100d405031066407040000708031400340403000c0e40c402c4421a20601001d003ca0320b43c1183c80c441032200078052100207086100b07451186800c015403100190030740d003400384500c0d00c00100303100a1000d51207400d408001a0b00303403040000c0d40d070790307c074544030181c0140c02c0c0e004004c0008044101005070060121664007001892070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 602902697 1250 602901447 602901457
    0x60306011404060309022b02040506060418091b06090501031d0a060b040b030d05040302270903090a0b0c0a14010f060e040c050d0503030a02090414040b250e01080c040308 75
    0x140d0740042c0174140c1d8010000c1d00c500c042000802130715000750110000a80c4805410080e80594000c515500d81c86c01044a0348280c0c2d006100d502c04003d8001c4130f030081c942106015602450200300790b130102d501d0844804049116440c0840d00c07007401004154080e41010300c14400e400d64003040508001001801c0030041d880031550255130315040600380c83e0a226006540405800414244914000c060f040d0f02c903a0001a11540c20484425034540840c582024040050185803d00b0704000c0c440c143d894100341e81c213921420b24410049500c1000c2019624200802002800e9010440e11000410254803400c00d51554890307001000d000c080b07014181c001c200807080400c4a191600f4124400a5960800d91050009800160203d0301c0002a260884840c803001a82c0b0480100021b008004584110380300300c41d15000c200c24040d10385642403203002c0014850f0020030142031054041d140502118000c903003183d503010010f510803050254880e407441740c0b1038606a12511004266042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 602903947 1250 602902697 602902709
    0x215070c0309060e0105070311030c030f13050f0d06091b060f090504020f041806030c030b040203010c141813020f030702250b181008092406060306011404 68
    0x30010300c80c04055021010200034042880c0549040c0d202d40300003403241c031034880060700700505840346010305c03081403003102c1c1c030b203081c801c1180c0da0b4104d201c0000c480e0fa0031108030052440c40d181c00011720342c10a554180e0140500030301c1441d1405103540d48000810103403a003601d80405448022200011404288001d0081c4e81c6424260041c00032000703000303d40e01d8020340d01071801031140000c1001d02c4001d450640b0103034030380d8289451009519000501d003940c0007518003600b0500020a0020300441d403030045000b40e000380300b420780700b0000b40c6400000b055000f0088030100400ba00c00c01800c0c5011100440c01420300504601600c0d07440140d800c4541c01d060207000000c24400c040ba0100b00c1d00c10251226501c000b640104448802400c901c0c0e0b100f03915180720001a21071454525080c02411a0307001000708200b5070000a0040100c0301c101c84902052081d019a0314003090542078003207186481c01d0503070205941d2502804116040506590306005504640e042d0300413000b0080c00241031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 602905197 1250 602903947 602903957
    0xd0b031506030c1f0c030219060617030a1e030f09060b0a1505030109020d2a0f11120708070c060c030f11061602070902131d060108011203021507 64
    0x10698100340c1800301c1c401c01140b00702c00c6441c000d80d0b9580751280c000780701860780c10310020008050030183d00745049100540c1023421803062480401c102c50b0301000035541e07008005480c20600c1d500b131542ea48030701c40c1e5200c0032444128120300714410240e6680400c0f881d174230740410202a00858401030310150320741181c105480741c41000c04c030b00744062400010305038400300403807580b182003001d000c1c0e10040c043c0044150700011b202c0c4982000b600908803142030a0070b1002210644140070b04c0d00c1480484010001b01e201107450401da00c11504030b2101030001d4040e15200c580100714010316800144d00b01c0302c2e40d905001c5070000c1000c10701a00018101c6440340200080c0504d8011b04030032a4220303c5c024800510b050708024080022901c0c1d0003014240d004540c010a5801640b51400681c80a1025030000030000245007440007008101d4040b06840700404907000c1c0c1400c004103088804d0b40c00201c0f408010000c1000c40e00542d0f4600c0c0c041d0060f107503940500034404942110884405010907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 602906447 1250 602905197 602905201
    0xb0f03010c1e05041805040215030a020703082a070f0c030b0405010e060f0a09110a08010c02010b030708060705030a0f0203160e0d03090b09220e0d020714060d0b0315 73
    0x103042d140c01c1d680b80300c2d103458524680b84c1001c0c4001c0c1000d0401103d010311940d104002011901c81c1154110342d40c0040c00d6103a100e07d0601c803000701039800300d501100050201c41c0410081951410244048816090400311841741b4005c1c0101c184c0002c40c082d03400616550624001c02c200c048400040c5001d8274400d20503140900300030b400d6a4021107105043d034410b0f001c100a1b200c43e240c99a40100c0392181c0803070340e2a69400c100c03414424425069500881c064000a1000350550100010302020b400920038007841504154843c221407003600420b4000314006070709a80b00d44000c50303001e08003440000b40e1103600000c0f030b4120303082141c980c1002d003610130910b040213070000f40ba000310520858000c03001c2c20f21a90014101b5180e4407030720341c0250340840c4482e5a80d86031054503d0a0400021440104064804c144050815014a1143c50054505030481ca07440410300e40260307407040c40c0c0780300281044018001d01d030f40141c0e80030954a55035200f10340c3c55501031105c41c2001080b102c80c00d407a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 602907697 1250 602906447 602906477
    0x30501020a0815090114040b040507050415020c0306041127010501032403030f0509042406021203070f091d0a0e01090209010308070c0f060f0f030509100b0f03010c 72
    0x5200e02906500b8445810000e01000c4ea8440c5440d0f41995100c0668203012524440410041c20b0400346095000e8100001c0100855000c0b001c0d204a41401c9121001070309142e8040c0c0c0c44421061026815800140c0050042070851005903200b502c080d00f559a52146440c00c42051460441090b5038104114010001d560303240c002d0b041043c0940000302e5072280880724402e03400c100c9200040070320001c0703940c0d0042c0034010026074680c084094804c0c8814400902d9840c846001100c003929000400500484d0ba50b00c00602c00d082c640001a0440c0f8507264004d0070745071180550f41c8201048101c24001c14074158501502d001120725544019003030521040402c141d441c3c07810030001a0b07141808a0000d60340e5040d180e411603410a010a07600c8961b420b0620741c5030441d402c0a0f0401149100015402d0740c024220300d8203404581c1c0d81c240040d2002800c07030640d88151786012041d4032000b210214031405a011580d246402400c00e03581c141c540010a0954800d0003008020a02c20000d030844 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 602908947 1250 602907697 602907707
    0x51c09121a0105090606090f0402040b040306061802090105121504090515010b090303090121090b04050c060304200103090c0803090406090b01091710060308090f01030908190504050901030501020a 86
    0xb400080b00c0364070070b6180200106c4c45900594540501c81c8500203203154031030303d89604440c094500e00103295500c503100d0602e40302034003042c4a072400300711010301e05201c0c1c00c4081c402e5070b6951505940e0745180410864103180d41e00d01c05040542d5011041108007102ea079280b1548481c3c80c0b1441c01340c0580100d2400b41031035074405900540001004000440c2d81e40e802000f00c42c102602401c00f581071505a0034144400f00b18100c1c1c3e07084a07803401c1c6640043c00f0340c500b119031040d846802191411403d08051050501003039034014910070000d0a4014000c1e412204003008030710615000a0070151a1145c098640060707000f1310389a0000110800740d0f06040c00382c00054040c2400504c040d19403500000c0103150179104040340401e013105400d04000d003e00454154003a0a003050040e2070f140d0074460706941c802c140036882020b1500c111150781d4020300032040b89603000102d80e800c003085065400501c014000d1824200102040301198a030b450f098601d0186004000041e15100f100d000948 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 602910197 1250 602908947 602908949
    0x90d081c0b040b0a0b041a0c0703030c0512090a0509060102010906051501171501030e0a060204140f100905060306120724050310140d020607030c170403051c09121a01 73
    0x201500140c001817000f50320740c00c2103401700c038a40d1200c03d184465218681105002d0320b1440c0c1104e018a00000044c150320840c1980f1060140c402d44020f5245948019200d02c5020000768010042c000104242d14001c20b555a0054040c000810349150503911901261021140c1442d104240500759240c4e5900142c1e40081e1100c0c640c4120b40c508005284000100010309154109a166030316507080d9181400a40c01c0c03e0b610110a64886407241d003028584810301c0f840e90b0090002081d500ca00d464840001200d04a090300d403004164102003d00040354001441c044d0031603040d40c03030211052002c001500c010628a40f02c40c0403070382d400802000010140441504000c1c0c1441401204804a40200222a0040c1c55401900f00b0800803401440324801c004c0d52244011030700405050b00480c003a20824480e54550a400040e05810b240600842c0000f820a500c50700c64038580786041c03090151040f045040c4040601d5444145822100d05178108903a0114555218080ca00c04414528 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 602911447 1250 602910197 602910199
    0x50d1202070f060b01110609030405040f020703052a160810060806010e040303090b071805010305100911121602061608370e07080111090d081c0b040b 66
    0x5458a110741d101c1c0c0c00c9006401201420490352034140600aa00800d4040115036051b0191106c5141901c1c5403510303904144a1180100d051130304d0100302e12210b10843e03030741a6168943d141000880c0201e40301c0880d0200d8004002c084100c034051001c6030400c0300d41c070204103a6078800712950801c25404d0074902c010b1010301c9183c0c01c100050003800c401294140c1550030420803010380b9500d80c1803c07005848050005003040c2c1102e024022a20342c4440d0144005403c3c040c2080340569501c011412034108540c420040900104188016079440d080495421004d0400c10300b0079015601c3c1c525025002d9413204520b0340b48a1407071151781d40602034103512542800705184421b0104502401102000f040104408940740380d50042c0709011500b02d421051042900000030f01d001c0c4170000030950071500b5141480340f038a00140e104414000d414403d1000700b8001d00f40502c034002e005d103500c00d8000890740d404050001d0f1210012101100507a05402c2101160001d00141400b00311900c3c00c54035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 602912697 1250 602911447 602911451
    0xd0f0605040b06030708070c08070c03030219081b160e1e06031903030f0c050409141b0a140313020a050d0203120a1b0f060b1e060f09040504050d12 65
    0x100b1103680f0b203000e0302d41c03040740c0c2d0400c200141d6605e00c0c101d8043d010721000034580440800c4034020300880300c100c441628480d40071140304071701e0426030341c0c0800c0f82441c0040160204100c1940000390004a166100d8229001c680c10f000d4030007110021038041e5001340c081883e000c410030400704c401042c6000b41c3c0e108002e4480c0c40c0d040c1a00425161002c9900c564040000000402c00b014130990242414a0550f00300700441a40203100800075489131007401c00c1982000ba5084c0c10f0039410188600648801074088a806404101010303141c1280740c40505121507054445081d14001d001184152640e26680d603546a01d441040412072480e080280141e001c1d94400c00141c60015401c7c03120032248101e65100d10686400b100e0f01400e60264411001c00b440454007000440560718654074407441081c810881c03450140860310802988181030400c0c001c003504e5460074000000c1030aa942c0c1e00c0100c2c5404d1101001c20103036281584c044070ba6500c4058003c901960203016001004155803007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 602913947 1250 602912697 602912711
    0x160e1b0708030105040203040c090c080114010e010c02121e0604051c17150604030803040209010801050c070312060f1502060f10090203060a030611030403110a0b01091e020d0f060504 80
    0x203030350482c003050141d140181d0380007010905200c10260010300521941d5010711170940d0107135000304030b07035000c1c440c10303040d05d0114414010940c0603098503908080180c0d45e1942a00840e002c210038003101c02192002e40c05092500541021307000402c0801449200090509003420320305039140c8600c66040e00d403d400c000d040b00702070f29480711220700501840c111510b03c03600c51001c40012081100692130b03100c40300003400001c0050220245101d01d0080f10b04d03100d07980eaa41002426103100700c4581079243d00401032078001034041c5119078010107034540c0c005a065203c444010300c1c800e980d000240d14000202c1480456607041204e070b41d00000c214a00c000600f0100b80b00e10000b8002c2c0511007502e41c011000034010f8407880b500d03400841e0005010710144000d15514803440e40261425400203150340c2c00c061f084200041c00780c1c1c1d00c0f0340c400ba103031415a02e4146503900134042c40c010000200b89000241c40030400a0010342a0700356504030004000144200c0d003822520745a01c2180201d0070081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 602915197 1250 602913947 602913953
    0x105010b04090e0c0316050f04060509072604080706051e0604090204090203060f0906070f1b06090203120a03061431090510050a050f18160e1b07 64
    0x566044407203110012071041c00c00c03000316040440c9904c8040d058842e42c00103442508003404d42204403030007954401801081c24082c072040da80c103030103880e030400c0081e0003082c5280e100307090700000d00040300301c0c1c03012070404005030f004410025101543c04080210b104401d0100c41d100b00303070300016000c0319007040c650280c01d65070026100501c45c520031551886030205640b559048214001e90040035075500b03280c00000c020414600ba9011016481041c1c001095140202089800c0700a540c4894000306000380d550203046c460b0404c22555a03071620109801a00c2c20001040c020561003030064650f120175800804a65656110b5681ea12103886e004400f615a000940c242402800c034142c0c0303a2040c0c072100c19400c40680c2d01c082440345003141d11002d2000200f00110800b100703079820700c10341d101c880d00c2a0030ba0340f050380d41500d01113412010900c1d41120140050110180105650501482911100052030781c0d500180c103959510f010444e018055111951500d1030482d1254148400303a2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 602916447 1250 602915197 602915219
    0x90a0203090d080c1b03030406110f1e07061a0f0123030c1c020c011a01080a0510080a0309051206040803041b09021902010b060c1002030a020c070f03050f010501 71
    0x2c0740c03040a10003070380b0104825081c0c4500710350b102445076184510b03c860112000741c0d6540200e6055820a1902546030301c2d003100d0b80e08a4008452a50ae80c07810070310800400c000344660380821001803942040401c2c00904070707016510028240c02c00105108038030401f40111204021070540c100141000740100f020303440740b28580c001254400781070304c84e613a00d201c1d01d1091148551a4503a02c403c090714404403480d9400420b2084160002442190b0200361902c100480070069680407803a044001280711069900079070303001000440d000c1c00c1d195a01452824110802c4064001905801007030281c1d040007110f803d41002480e000b000d40b03185c103072a01804d600000d80004d0803c08500220307500760402851440140c122040c08641e6070910581500b210f00d001d2003244059401e120200c81c95241c110252105403c07114090014a002e00c49094000d42c00100914a056400c0c4200c105520042180c040507003e18106135061506506200d840c040302d01201d02c0e22603050100510219000f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 602917697 1250 602916447 602916463
    0x1031d10020706150e0115140a1b06050a090c0503060403052d0d0606020c0909071202030111030a0204030327060c02130f0615030e060c07210905090a020309 69
    0xc03180142c803040d2600d882c0010340084035801c60b0098420202041c1004203943d13050488144030801025002c076581c2c252081044128003150148007404680c4489001c0c160011040c045000100b2800c15a40c3d151011141c0c1a07485030346a550f039900c5403040291200070728000e4002140280300916141d82c1c0207201c0d2040401c0c4102e820401074402c00c070421180c034039081107000d44041e19118601118028018545441001e0041c41908a0800582040d00800780a01e40b000050040f2500b01740e0030350144840e442c0120b07099962071420001d0001c2e201701a50041200d18005641c0d140355007002803000d07031100044e1140342c030a800515040c10b040d580e0381007201c0300c50404074089d0308a4000541c0781c3c4490300c404c0c80024100000a00040400e80c03106090b6180c10703010741d00e240301152044044420202088020f0751110f004149070421582c06002428800e013810444013101540340126030135440c90000200c0c2c00d9900034881868030000c555408071b0328110460031442c001c08860380d50042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 602918947 1250 602917697 602917723
    0xe070306091e0b0a090f050601171611030f040b0408060907180f0b1e010822201012050106030912030f020c031b060105030f07140619050901031d 64
    0x10303c40b010384694031454040002445203140401090700305803030300780141008954050004241c040300c0c161943c2c2d45111180121000004010710003514001983d80b241c860140040e01e100c14004114080c03004c070f0060000d4140d444042e51114541540e0750300c0c0c40d50150404096401c00d000c1444034840e00d0003181d50100003641c1c0801c00c5014901c40c20020300c00000c03460703000552000040002034024a80b600c1d8200282d031400c2c10b036070390717021151541120110901118200c070500c01c004036081c805da1380602c1c1e00380c8144403000408080040c614144280d940c0c0c1c0852107003041d024040003107114460042c8407034101400030000ba940c0d00d0341e00d80115007046091550313403410300c10004001d505451203a0340400440e43d440400414201e084440c02c00b46241c4c41c81040000300383d42c10041480707100714040c60001d02c443c4c1d043c441411041c0b0580089290401000e001c403d9000d4a5900f81440180c0303603444a603910f4802100040a58050302e290000c4841100680703403442d80005030500076018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 602920197 1250 602918947 602918951
    0x20406150c110604120b3c06030c060403031e0c030915020a1401060f05100c030c170304210c02060d09140609010509060916060503040311070e070306091e 68
    0x2a00c60001503c0f070145410010381312410340f1800341004110400c890054403612119030742c0301d1000f408110902e41061100381010a11007103490240d003003160a58004031f001302511114240301010030307200d420642c0107800061200f09200c452002c03030715540c08402ea8901d080c1500d4207994402404041072842007184607000203d000722028400e1005070b0400380d000441014201c040240039002e00744c68003c8000e0360003c404002003902d03080c900324809908c1603c40c1c40000c0010303142500c1115050300b050f80c14a010070241603030444101c3c015440746208542510052262401c54120f2841070901d084c02c0c00214600b000c00b503603400090341c1e1403520030340340441c2004140c07800fa0b01c40d009040c0c09403214444c007424421301d00c2c410340105201c4c5240070101d483c1d9a03102c41d6059070b11848070f00c26104902100d04144a018807410040d03502500904045d103132400c0681e071070b0f46010980c0c1c4c00303400c0e040e44520500040c0b9906005180040074840810301c15400140781d11380c414155407004048040e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 602921447 1250 602920197 602920223
    0x80a0e091e010501080c0d09150e1f0b120f0a110108130605090712060c080601320903062a0414040209010c02060706050a06231201020c0118020406150c 67
    0xf030003200b114102807a248040c001181d00d4a0000b00403040d07900b00c03d0b49c55081c41d81d514110f050008032074608094601880c0c10000114004800074282c02140300c0c1c104070040d1f1a548124820001040c01076007580c0100100150303810103100c0d11040070b441504010070501072040924040450300102d40d0885000140c58441a03080c6180c000180d0004007007040d130850f900d040c0f01c001c1d8041c020300c2c011915003411036a00c8400458816405040d031394880c041c030140c44429180c0c41e0800c00c00000139502800c0c03078000441d000903e828000c50b40664400d4001e0041034440e0721402080c024150000740090500c0c2c2072112000844000c00c98040c0681d6020440e181c1d81d80c850b80c4100d9580d5005054299544120704100004d020203d46642020b0300301140040d030381609055a07808080ba800e501c0500919110410a0150b0201200c000540d000d22400c2101d14080c80703105c000c90302c0c600e46001c1c030071130510522081c0c40040c0d01001c1d0380301c640d07200000b469411540d80b4500c664003a84180d044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 602922697 1250 602921447 602921461
    0x427050109020711120c1314070e13020f1201030503090112020f120c0906030f15030d0f03180b0108100f060f050d05120a09081009020319020607080a0e091e01050108 73
    0x2107255106650155410014015030f80c81c550000003140e48d4410f02004690354204140da9008100c241542c101012001402a60915a0150400788450054285807252604104880c0d4900383c1041c2c5040e040010000402c0d030304555015202081002c056040001794402c03481280240d55041520360045c20000700c518400000719164994018034041d102d003010158100c41c480704031001c0c40244120000321002e454001a003692108140d03440040c0d00c4124641207000d00a00d19941110031104100a0001500700750750301c0c003030140c00004015684904c03c4040036610501d024110b447d20300441400b000000303080050641c1c1054841c800c00300320760329040380307000d408001103030201d040441d4003442240e00403143c3e021a0701e0241110000881c6e00a008101c0d0080100207600d5801194040300080c1e07261000d641290006000e1380c10441c607a00c40d0440703a8850400400003034204120701101e0703c4c02602154004c50b442e55400c0c0314200102100f00701c1181800f55505000b0100006100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 602923947 1250 602922697 602922703
    0x210606040b151b01020f04030b0f010b0712120c030e19020a29030717090319080a0e07090b19031205090609040e060108100e030313020402042705010902071112 70
    0xb65659440c021503503840750840c001b5403a0464001141c0c4846201d010800d5210780001d210306039035641c1c2040c0e1518801c1c0d03075504600740240502506000c07140d10680c07002e00c1d207841811183c43caa0386003c2000500310f05560b0910741c1a805404041000d208600003580710401c41c00151080c6c0d1110340003206810244031212080e04400b904d9107800041000f9990740d000303d215142402803003056016449a281040d00c80c043c4500400841c074004c10302e42d41d040c0c4180348031500501144030000d1500d00205549040201c540c100701d0320340b07031a409134881504180c402c40b40c5440418200c140300c60b0542e81d03100e0f04a080080f5840c00c116011908104581e584d03401c842c0e81800c02030003040003407203896a05440d00360900c50b0714510702580c3c40004032840540500f801031540e03034005d189566106400600c141c40d080c1000d0340c200ba1700b0f00010030a4461120444a905100c2003c442c90241040300641950016045240b00500500500e80024103800c44880052401c0b1190a0002240c0b00010304d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 602925197 1250 602923947 602923987
    0xf0105040c09090c0203093307021e010e0406031a0105011403070e0f10030e0c03030c0d21050c030901060b1903020904110f0702040e07080c060f09210606040b15 71
    0x40c1c8400100b002c4480d01208030500410615210b80003031425280c101010009c0c028a0400303900b040c40b844030500780b85440590022482c07014100002c040140401040444616400465060880001034002c08050103a005d00414003440c04414240c440d4080781c0d06400050410030600c4609220040c442c1c4d62450903201301340c005440f9450900160320000c0c00740002c0c4c51140c4090141d649890041e003404003c441800050790b00400900700382460840b91034050142e524110180c0e1720242034500840e02810340101640307459030b80c072400d10303a104c20f003140c215501242c440da80410039400c1050326002fa140e0203d0490400589440300c0e0400318000c1c00b415102d00c4007954000800702c0381c0740705104c09482401d009803002c000490040c4001c0b03603117041c0e034010480f881d4040c1450301c03410f04d0f1020082c11080c494840c12402c0440d01c00c0810b00b11214508154401001002c2c1c4d1462404208003480d404902160140a01030280000c90f402e040c241ea260616020b000441c68001c1d009010154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 602926447 1250 602925197 602925199
    0x15012309060f091804020a210606060206060108010e072a0c06050d0f0501030b0105040e070f120b0702150a02090303130308091002060f190902180f0105040c09090c020309 75
    0x35030748801014412610ba0300051035244151380b240a041c15009a503206240704960182005140b0760030140281a694510080000c5842c1c01e04c050b10001186800b0362002071545030010038041c100107002404a402c16080407021980c000b0402c80ba6030b0344500014604000704041c40300c2214900e500c800390690300c02014044000700034001980315489801071203200b6100c0c40c1042200110003054041c0c50080c030010700240303541c000501280c9010b0788202021182e090480d0b91499403038132402d80600c00d0b584152502080844003105100b4031500701640500c0c10301c0906002e07611191841440400900600d69003903010400c254541ca04000329808402150f101c1a410380e602d24000d8103c0d4855900d07640158403608401520600006125014035500081c5401640e03494100810074000d181410b2681600c81820030056203400000d403500b800324003249003880ca0308104010b642c12040e0700450140740341c0903440c08559409000002520000840450000b0240800f280741d401041c0601d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 602927697 1250 602926447 602926459
    0x11203110a051509160b0904180f02030c101d0a090f051914070302180d0803070305010f050303041802040941010902090111060c04050915012309 64
    0x65003402000a50f03072240410032010840300c0c0d030b80c9545041d1680714013801c0b6503030b0703d000140601250000724054500b081015100041c00300c0c0e1100c038100d001400e10420340e005480a02c281c0150f050a21500c5070b19181030300c1080300c1041a000c01411582c0c44010300b040e0419040703c41581c5e0362200311017802455004070a12260713840030724440003420140c8001c4550302c902440903029031800e004590b00c41c4401600b100303041d507440b00140d001e5882030001074040150f4003070460031070b52100d48402d9140c1c021442541c0303034a4440d202404980040e00841c0030340d00c4141741004155000412202510302d100103240440c28031403810f40180c002d540103c03048900300309403000340d54101c6400c0c5c141e0700805980ca2444910800364120f500854507007611844020780300501c01c12605400600d4150018036211941c00a29040c00f410300d4401d0320014140280054200194503040c2d0441da080319260500084452049001805070043c4211549003202c0701407982d680301e250300c0240d4010503405450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 602928947 1250 602927697 602927713
    0x9071b0204051f1205070515070b15121b1009050d030c0308070807020709020705030c2a030111070b06010c05030406030501090606020a11191a030f1303020601120311 73
    0x10071080c0c0c3e082d03440c21900510540002032280c6003800310034580b0380001c09000031038101070034021b014058048102c00c200040040c0c40000d80350520740d501ca8880403122a0030038546004021005101c401c11400c1507101840f43c04ca2550304101d100402902110103410058082e4030940f0042d006500c07450380110000620024141c0050b455081140f0a40da02283c50351141803e40d0710600c25200900103a208079030030303ca00b1040364020848280a94116400c00319513a620394646000070390f18051280300c40c803513988410305425030340c41500c1044000340282031840020f000305019020000d0102d0029402054540c0d01544421100c00e8229050f00d5487da2a40c0001e006410288074096400e8505140010440e201090402810b40e100815980c2100b50700c042100038001c0c0010091020850840003440e03010031400d01c420165000105522460003000e00c9628201c024207201c0140101e0300e0b0640007940c0801c800d819604c14803031810f440c010300e0030704131145444451415620b104e071041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 602930197 1250 602928947 602928961
    0x204020d061a0307092105030a02160605250f0b0c1c140604050a020d0c020c13020a1b05010f02030f0f06150f16020319110901030209071b020405 64
    0xa1016120000709218608182c80048240d51008540d504001403c0d148113110405500c4414491202c0d55a6000841b6569448103401c0d5403040d41c0510150303021640d0640103200b0f0f012007100030070003414594108900f40190000301d005607400d43c0840c40d08015078000300540c2c42182d030503440e0841a0500c0a180c810341c005026030010854005140d0310a502e4000300e00303540601c0c58074041c0080c401e0f20549407182030001070600606640c620a40174800746a4a44e110301c200c403031244031540103088602c1c480d014011200307003000c08130030201d0040081d50013a98010140002c40c50b0900c1080c83c3c00306503410f029004000c6110b800074200c0c0000709100306180410b401c540205802d40298009880d000d04001100b00e0342014081070f4a03080c001d01190070740c08800780140b00f040c248021841c0c0040c1e07000070300b09880c5141000c2d01801c1c0c1c0a10101741b110580c0210040d90080e191a0304650454000503118003005003c50100041030407000801d02d02ca5030301140c0d155000c0c00510050034002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 602931447 1250 602930197 602930201
    0x102120f01061e0f030f090b0903091906080412050c1006090b040911040213050d0f05150705090904050109020d0c152c0a081b0f030a030e1c0204020d 66
    0x700c90000015000840115243c4a1102d02510400343c0e85401c4107a03d0300b140150f0181008404212280340d4590204010681c0500900e108910850140d6900e10b0400c0c104030384010120005013503036a09070390034411700d0f802c41407158009420003a40c00310721130190001c8426100e03405041d4042c0c004c99401800b4022103800070380950740c40d40c03410b100d030488500c180401c8030707c01c5001400e00340718081c258409080036401014668144002030310004e864901080585200c11000c0380c411a121103030006100c42844039040040c0541541e001c0c50800280040407405040403c92103503030403001180412200b54070445a0a6001d8100c2d40025914200707200359118030b11500c0e02c0c5500ca0380d0710411035403140005406a004584001000710300350804408448000b90f01c0e0390300000e2042012425007410007408a140558401011010386540c0a0212581c00d00041d58003e0b441520711200290f00510441100d210544e000c1c2d0250805600031171580b00d450700302940051001580160800141e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 602932697 1250 602931447 602931449
    0x3032502040b030607020601060513080f0f190b010e0717071206050103110412050f0a06021332030c060a0309060506012a050c04020a0806031608030414030102120f01 73
    0x1c4504120300c00300720051540300d040840d020001078003c0401801f559010700f024010000c0c20070034030328105449011041c5056210340c0501d0a9074402c201503404030908100900152003002c0f0b0300c5003c0062503036461105c00c07042c000c4842e5004800c0005110510901702c5082d010403d18100c045c0781403015002c0c0051010b0008410120b0400d84003103003550082c003510184845c8908014075191903c0d4480d8603406403035030116841d0060002081a5200400c1070060180c0905401644c0e2440a00e00800514183d400040000070506c1c8840540c101845415022180b21440d02c007514070143c00241404501c191842c1d20090100348403088640c141d01094180d841450100981c2e1107542c015100e502c0709411075030789c000914150368290f06417480319843c03140c4201c04407040880420300040580e0058400c0c071000031900c400b0040d0628040002d540351102407200c1e404c0690405800545074849c42c010a010344240c000401420f4a0035811180c3c82c0e40001c4108000d41881caa49501800302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 602933947 1250 602932697 602932699
    0x30c13120302060108190807021324060f140d140a1e0908160606030f1a060f01050d11070c0303080718050303030604050a0e060103030f14031e040203032502 69
    0xf03000021a0059000a0400e2034141028940d041c11829a1710018254400c00c0101d03048490a01d00f071030858402d004001c0d4040e103024120015491107402050310841d56440702d400c2001030000d02c1d00381d0b0b4000050120126500c00a10760360807003000d404014100c07a1201c500701c0a003441c00c0000880440e0302c2164201c9082c1c420409070251406402c007a00e0003214082c280c18010052905420128140d001045101d2000851060b84e40d03101e05c1d00c106002c0009890f03024010840d80034032000342d0034040e0304c000221000c0d102c00601c000001c14a009450000039000c1da942c201d1244a24190180c950381948400603112068481c6002021810103507035000114059060000c0322440b0115171005a5401030b00460550b0307150b00421000c6d0202a004800003655540d41115081c000d00003079000e54001d868000b14650b0381c070030007002510b50100d1344101030001d0091100300003105001d05401d045010080302580c5440c00003030305511401d114503e4501e81800205494880d4038282c03201540 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 602935197 1250 602933947 602933953
    0xd0510051e011d040c08030711040b10170705090d0510200706021602040c0f080a110706020c15090109170c15091f1d0c01021002030c13120302 63
    0xc4607101102070400203008890280c0b00e1000c6405000c001c0d01c0f0416401400b5030007299540b9510203800d81164001c42041d22202c21001c0341340740a08190243d1b0840b02029214a0f540503100342005100644400001c0a0b0021080c080b9050611450654982c46e4000380954980d2420b4a0320356541d03049034a0703002d4a43d00380422202100c598005840b401c03403001081a02e40809551014002d41c0f212030303044600042c000911015840d030703100b40004d0a00076214005071101a40d009402d9175402800b1248440c144500b505d00104101f0a580509500050250311b07490a802000d040000034050100415a41400c01c148a0303015008ae00e40c1030b00817200280c18100d440068445c40c800c010f00040703640e0011401c1c0d20343c1a8040000f0341e1200c400e00aa4484104c04caa64100042524010090103a02e0310b204141140b21107234040821030764170380145007690045002031f4545803001070300d10100b1b5021002aa010f0840d000711030040144000c0601065100d106002c68401629003c1c0c0042c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 602936447 1250 602935197 602935231
    0x9150905100b0304081e040803120108010e120d0906110a1d010c0b040302070513020913020c150c0f0301170f06240303040e090106080f010b0a050603060d051005 71
    0x1040500c00400d4442c11212a4550751360381e228412076030300c200e00e8000002000e1110003400b511039005400a0100703c3e02460b51882d01e202c220f69404410b0704081844d900d022031101918100103422000300ca4903030500c9444036616143d4030010940540050401e908080d44078281c2e9074450f0041132421016160004503c1c54001960782000c0b528203142d022030166481031001c141e240140641c060b11a10442d28880d80f90b4000c03944100c01942050f0249030081100411813805000315103600200361001c40c24072100c100c0c42780d52080d003c488655400ea098010800310100c010481d040180049200d60313132540c1d80d480910142e000003840344090b008103030201400060208109005034000c5d00102d04800100079004000010706440380c1d45031104000c001420242141c1d100c0c45040010000107074203140480050800300c11081081782640341070f04c0004150b8610310b1500c140d03070058400070344036510b4030041002a50100030252091041000c0452074a003039403c410303c2540001d0190201e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 602937697 1250 602936447 602936461
    0x61e080a020f041e0c031a030a080a0e061e0405150705070b0d021606061a04030c06050d0902060d0f150302030a0b07170106020c2e03090302010609150905 68
    0x5102400d20003580300091045414a920f0a9041082c0055034000c070200007000e10341600d07080b15280400307480440d8540100c40103120050050814851043d409003c0343c03803241d501d0794554071442d405d103401e11241c560300400a40340c81c0d0a98410180391108030150b040003034800602504540f013000c0c450180540c060029450003003e40d0b00361030744180201001418030071300009c1600816880c0e07080590070b2000b10307105002c034010010085c1c0a05000641d903400c03c0b03c0c0c10b460945407004010a031f03504001c1000060440205c60040b54018507180e0703240c084141007680542003480c4041c0d0f0000000c50342200d048003e5102400403d030100c010042c040c440103188c0d01d41075603840040d41c5a003080c001c0001180c1c070440c41313561080c81e034a003210304c00e441000d0702000030b8420b81260005074070450034650705080600b600b000342c40d441d0440403a0302e1240c030080041d044040008208040d11214034204142c000d40002c0040d01744d4500c1807144000e4090b65264203501031050b400a203080c44086584 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 602938947 1250 602937697 602937703
    0xc070807030f0c06141602030309210708010c1d010905060d020307180518060d0209041202011109090105131d0a030315030b040219030b01150206060108060f01030e0c04061e08 77
    0x103407901c00c2c12035040000784908800306d580c01c0c1600381d8050208221400c191b40c0e965004540031060070300c0c034520800952203210720740103060700701000d80e80c508103001e003180f0340180c00307907425020350b01201101e8aa0040100e80781d041e81e0744043e40140011032081e003c0781e0203402844c800e450725907800c900003500740c062150001d603500c00c2c01c2e084401001c1030003868660f91010340c2e2200025081c0340c03a207030300c0340e002c40c12481c01150140c0b009076001c070810000c45e030f080c00342500040c0f0012a150502480745c1c005861080d0600c10540705031004620442c911031580c001155002008620441072061030038031944820a0410841c00685455016540c000b0500074080640340c102144541c29031b91a030038040d440e9281e00c40c00b0b200d19501100000054103803030105000c0c140e51000c01c02900e55414019280c04405415075041c031211104010080d1210751060003444803d10740031030328406402d8801e060203401d940382a0000d00301440403941e41441505100e00c811030030081c001d01541c0301c0700c442e2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602940197 1250 602938947 602938967
    0x11505040c1403011a07050d0f180819030c20011103040f06030207030c0b0c1e0304021e13050c030610080903030417040803031e0702030a080a020c070807030f0c06 72
    0x44048010303c01440494000b120b0040d041542203207032807402c0e000b0344400345070030000100038000510180251442c543c0c0040d180358003500f0125000f18050030116a1a107403410450004045880603421609151041c8030301c3c4030041d00243c3c00c011003012800b034250f9070501c40c1400c2d404100d00f4161004401c5c1d0010485046410000d1103121003410028120b000e07510154090301004980a13070800401c6507488494010070049181f00d42d660101c15008502d089e2225a6800590081c400c100141e10344001e005203e4107500249503d045030701002480c913500d019a680c01e5035141804100c80402c0e000c0003507008481c225a200d0700782a4030a0116500801102ea040d225001400850006034210031a880310349104900d075030805840318407041c65600304540011150b00d41441851200c1d0041d451103404c100903101a52038802014030142003548041c050384440340c4e0019094403200000c0c13101a02512410056951a0f5079904080100194100701651710fa0042c020005100d4080d071460300e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 602941447 1250 602940197 602940227
    0xa0507201017040209090c060d0218010509031b120706020601080c0d2a09050c0706060e09030f0c030702060309030c010e060708060d060e0d0f020105130804120c08011505040c 77
    0x11442d5070b190b60070700c042c1c000c014080c1c007014802d4800c0c0070303450360fa040050003c03103e110500680368001d9211003008510403c006074180001040494810b850109000300c042d9a034500000c21400000b02207902a50b8030085000703103000d051000306000d680814414102d848110454419040400401505816450b070061100c131007c20442d01c0d60007480d100351010840c1c0f60004105d0f6980313400401c04d8500480f8a0886014001005010000c0e5413055031301601c5125407001d0149022010305980b0712038841d41020a1002049880c02003500304100d499069018298075100d003403800f28255641c1150440d01c2165007417a00320300301c3c1040090840d118140a41c1d0340800346c1c886500740680d1015246003230ba1003a44924044842050030410f110030f60100e81d8664103100802c01000b801c40e100136041141c000f5225603d80c001c41c2444041d079007945d01c01c40070154240603d00e4443c01000007944040000d500703000c21078004242c9042440c04446094805001c402a509012611001120740700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 602942697 1250 602941447 602941487
    0x72f03090f180f0705070b340e040b040603080d02040e1b0d0e19030f17010503100c180b0d0501090506090406020901030905070b030a0e0715050a05072010 68
    0x141070f1402401c0d070540107102e500300b00d86454010f40703e164864104076106500c00f0582c1d48950ba0328044905603e4404400716007046500d0709000004040e84034101c40302e4400e64940c05011032954403680040002c40d0b00041c40f607a1651042004006500180700e2101c00311452800204480034822200c001040d410850a2500c0c081080802c000c21451a81640c41d01c0350811b4404541c1081001071101b034000e40701e80c8441c07160600e00800c0d00c0f4121400f01a010380b104010043e94400160092007000440b801050151541504891069803075a4681e46510740d0200000c40044200040020f5002000140030903030700e17529444155041954080e0300060f400300024081071096016204c2c009051401080604498035110320700000364102c0c9203071010000038000640000c0c800c0003074048524003d40b200a19001492056103226450b000500c2070000d50002c0d031a1003002201d40181d0310803101510500441340c8a800c501ea403a210501550000400001c000e01800035486801404005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 602943947 1250 602942697 602942701
    0x3040315020d020d021314030d230c06011514090603180102090d050c09011401020703120504050909161a091302040305190615030803072f03090f18 65
    0xc990002d600c0041050344080d4280319003101c140260004068040c0c03030b0003d5404547c14207141c084046070768100981f09030b108180317070005550868910355580c5849003242d01100f010310303411081481981104105801440004120788a620100c0510210250f0f1400803c00746400d2041c4c0520407d06130a0303000c01c1c18000107401207602c800021050b4903800026080070040f8011580011409008486941140d00741c2206420b0901000c0d0040a02002d1610000c4403c0c0001c2c1d155030032400050b000601078801854050b02805c112030042101909012051800895494441101c0706000911303c2901200291125801095011542c1d210240b103160407034880030088200341101024801c0354082c8000000328030184240310072b1014a00103800907032028906070b42155600e08001400340708a01050002c0f03882d060a4950002060a0843c0711240f280c40307101648903aa500b10303c000c0c182c848240b610039800f001400b07102c4402d40e2030880c1c01000c0c1c801c010195000e20b40c0d100c164208240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 602945197 1250 602943947 602943983
    0x602060c0f0c07030606090b0f06210408160b0403031b020d0e0109120807051005070c03030b0d0215041503020c0c0603040215040f0e0705031014010908100506030609030403 76
    0x24202c0d07050344011100d00581d039580d00015122141c0c081941c140d03807051410ba050a2000e01d1b0b6002c07034011907440d0f24143e002e4100d185101044e9404a034a444030342c002804204141044460b0711070064850444580c3d41d02e03143c42d115108039811030009050443d08041404403841000e851400c2e43c001e8210860b0001e0210384c0000300c10075a904114481400060400300700c001c20201c06d02a1101c2a0f5600083c1010b92a002c0f121807803500d180d282100700013a8a52000136071103803c2d03047c035000c1201c50040001400c1016100b4010354855020550341c003c0c40030031401402140c92015006e80440d2451105900f240151009088a0382080e100c2220074a00840155805031005000b02581c0008070010b50b020340243d00f0081010b542090180001d0a4a0385035a600c00b00a240c05451454285603007404000240725803002864008041001c1d03078058016040640644000c444642c42c6140107400548416908075020340a05004108640004021582901d400810402400403001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 602946447 1250 602945197 602945227
    0x8060d0807081b01140c0913020f040504060803130303030b0d0b0a0b040b040b06040308030403022a03101107060b01030f02120a05070206131707080d0b01020c190b09150c160602060c 80
    0x556001d038402d856000c0b001b400c01440c8041c0401010401140c1c1cbc4075410441070008840194001c40c1190b801404240c03155000312078040156641854080f4005e50040c0c00700f007403c41140d800421488508080050150003913002d08100034040700e041c042000d000781440104e0360240105900002d04200901c0400c2584c0021038005100344101c80d030b02c00026490101c3c8071245042c5070140c0c802c0d01040101407070100303d80d118800e41c03c1c074200034003091411052203c0c414100010030340c60b1a112060016070080d4030800404d0340c0e46500303550700d00c4203e0504448050884000110703615002c0852022071002034045c1c41012900e440214400d2035850300c4501059230080c0c1030985030104500000624400c0c094100517003050408110300381d5400000e07040c0a00c843e0041d002e000014900428010885c0000301201c1040250700e503221a15008a0455502c0d40c041840b40400002c80362a4140300003500400d00c0b03c807203170b200d083e0358440601700d0706e0303a1003175400c030300054030601c82c0301c0c00c2c01205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 602947697 1250 602946447 602946457
    0x5070507110f0a060503100801140109150b0d0605031b01050a081005030d1101050a0506010f140d090b040b0a0207020f151b06070201060501021c08060d0807081b01140c 74
    0x51000b082c1c03200075000070314503c0c080c1d00310341e0000b80c02000380819400e41d0354041d809010044000c1c041e019154800000c034080500c0303021101925115041c500c0c0c080615110007500b100d8910030b075581940840035001d000c441c4909800380c4241807507540210801c1280030b1140354141c1d601c40c0f402c000248101d4140c1c0010700b16514401c81504009000d40e41000701558003482c41d01c501840b08a84808182103510003040401c503507040004000c650780c4c0c0014030324051450341c10500c8064500e06010585401040c0341403d869240c2203201742801201c0b90310b24400d6110310f003081d0341c2c0e81e5250349000c16070043e01c10003508060b40464100c1107241030b25076880354400765003541b070a00c0807804200c503d0700c041010740465500072506010703501d54280100c1014140a00040c03550b85603465400340c40c10510200501088111004034946a4550380b242910b16048600303145c5882003400d29240da58050742c00444048044007406441d2007060166054006a01a01900c0d0b5521420115030562107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 602948947 1250 602947697 602947699
    0x603010f050405040507170a0605010e130602180901092a080109021e16060c05040b07060507030e0a08090108070806091503011b0e13060e01060e040b0a1503050a0507050711 76
    0xc1b0f040201e03500c0b080c0f901100300801180020420000c00341049000c861068122001a5a8050410030404025001150041d0b44008010ba507500902c0440200d86000004030354841140e00000503803188540008031001c19810740309030b0000c20100d52907160b20381c044007400032914002c01040900859406440040300c0280958103c0041c0c030310315440da0340640d0060243ca501104910240300c6184500c40380d40c11681015843d25040809403202e81c0140213008106c00c3d1507000003042d00780f00343c01c0100418100d0045501d6034000785002e003c0f6030041d007855030018400c4000955018400c401c164025000034102032803684a4405210402120f1003405400d903403035038500940b0241000344031031031149540ea524401d003407a104020003d10b01c00c002031100c608046e02030010b00c40181006044414a08003503840500d008003280c064221485410303031001400100007004103007031544101007100c86c0d4080099940b105900c20845800b50340c9440094028050398002609c012540600000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 602950197 1250 602948947 602948953
    0x230702030c0a062d020d050f06060708030907030803090304091401050604030b0a06030c0f080601090c081303021203190509161215020f07020306070c03020c101101060807140603010f0504050405 85
    0xf400c184030052a0300041020100d030713a000840c581ba16850b07104003504409001280440c0741002d40004405005040b4040c007124400800700d0302040080119200460b801150517840e840d040e13031b00070740b02d41180c89410141402d007008050307500d030104461810781c2c200401c81ba00386801d41d200c015004a008021981640d030b40d1002101181000c0401801002e0007035a000c40d0714202810f4a06011040e40240380e0719080025a03000e064210701041d9121858011810030540a820103e1400010315443ca030003080010501c0408030509030441c001c070070403010074040307a00c40922940d03030341038056000d8041141107001400b16840780307a9610031207030055206120a07182d81c0e150a0403648200b034034075000d030000106041181070500519034003200c94141082403403401d4401075259022001c180d441484031480d00f48090380036000c1540c00c0024000200a1079840c1c2d21105d03a00c1e1014080e450a0450b90303000b50a0614003402240e05903502007401c010390a151000380700203004040c1046410740 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 602951447 1250 602950197 602950241
    0x1508061813060207030e0310020d0c0212181507080717091302030703060302130203460f1a09091b190b071118060f0d05010e01230702030c0a06 63
    0x2a908100034544d02d401c423503005035144549001a800c842c0c004164600f590868456903c020440000b0784100010440a0103250003080002070303000c150040081c50400c00c0400d1200500c41c85201801c0c50307501c241c2ca03c44184081d2000c40d40540100c00d5996480314406504110408007a0090f680100c81400d0110304242c0f02d5000960705040d800f40f01500316404020820300e8100c00003000920300040304803041154480400414100c260a4440201d6000340c50301d80303042c070a9134404207032072006c40310800c03900030000c2440440300d4101410340d03c40d101d002e0100d15030f21408200d65100214002009090b521003400b8441e20301c0c0c0343c2d020b60707040444001e00003644c400001c006040d660301c94100072410801ca0420400c20308078035030104c0e0000800308208043c03030b101e034003041114100465070381e02c0c8408140362080c013400f1021400c2d20103501f001404141590003c13200b000301c00e00010740500e40c7d900c4800c1269680a50b400c1e07100c42d9400500c2c80300104116a000343c0c051a1690500c070881 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 602952697 1250 602951447 602951449
    0x6010f0216060c06110f07030305090705040f0f20041214010c080106020f0a03050d0923070603050603011401050108072601030318030302120903071508061813060207030e 75
    0x880714691141022801e1a5182d204115440c400d4072820602c85a210313041203048a19184c0501a4000003001e250381da0010071003410703081140344000d0100900c2404001404510784003d843c1d94600040c3c45400d141ea804034080c0d11086c2944d2002412003e1814245080e240a4030030003a18020707907203034402d000014040e032020700401d03d030309413180c88040c607e5240104c002d1901807101006c940d0380d0403410030301000981c0542110700d04403061001090504080c2040d904403d2500881280e101d042881a80c03000c070045403150480f01d0702c0e03d0030011503540c0701c01c0c9400e842c4903c1d8820b083e0803039040140065801103a4850b00211903190484104050403060443c5c3c0c005071a042440d1400080100100355001405c11010780d502c134440400a0703d9030b40e0103035650b90140c0440702007074070114000c00c00c1e403020000c050082840089080800c1400d0902a2803d007081d5042c5001d0094010540b541c40b00c6c000307806002e01034000040c44100f0300c0b511120025042264110f0030002e007001c80c0102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 602953947 1250 602952697 602952733
    0xf050906071118010e01080a020d1502091002060603070e1504020c151540020f13031a0903040e0618040b010e180307140f03030c040e0705040e06010f02 67
    0x1108442c8083c0740c1d2a541801030310410690164030480c1da66002c0b5aa041c0162248081d181c281e03030307026840340301500071320300a280a401a05410380e0421a11000c200820382c0c0090b030740d80140006d03030980347c45944071103040d40b80c4481251811842035070b4001501c1a418154000e0444603d200280c0e100d1600e00612204641c80c01c1c0d914000b8081214a049041e14000c40c01601e418208010702d240340e840403040458111201d04048210a04403031b00c107a900480f90100c40120503c4c2512075036070403100c0c070118024040c500043d04c107079165490421300345002c0d031642c5000d5a8184001d605181c0b030501840c0781c0c010010849038104400140c07003116100c1c55881c1a0140d88544020803266051402500200000030006418844450210788020b5004012544070b20b4101c60401100c820441c0014070b0013103400c07040781d042d00c000400c0100008201000d0403d0321042c040c1103e568030380520444040c040c50142c000c98a10507000701c7c000e58005c001140301c1c904640181ca400740c550008040d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 602955197 1250 602953947 602953969
    0x30b0a0b030601032903070902090906190504060e0108061b0f13090608100509030412230d09080c0307031a0a0906180204050a05040f031409030a080d0b010f0509060711 74
    0x60100003581701c100852505210342e50103030031444000c5040c15032002c0018201440034040c0d0740103005c2071a0141b0780000c00b02c00038019110240003844459a50030950444c09024801c10b802405544045482150400079080c4030a04c0340038110b00303080154410281c154410f881b05e8055411410b40002c01a106008200082180c0c0000e850b001031440d455905590b4000e011020715003003080180000904140085130a40e001150300446881c4070840c448511491182c1981ca840741d4014580002da00c066800b080d202e42406990304000480145550f65020b4003006144405655074064180e461045140d030083e411000407501d01210b031203100440f4124030440c40110a05c0074000254140307401200c0e000140c6040800c550710741501d0b4600c102c644c3c031400a0400540f0001d02c40180082d2042c0c03070070300000406464045030b0798a0311408650113503860303048c1207082c660744152035802140b080101b980c050301c3c0c07185010031030010080c3e660f006590849624544450034421500c42e044100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 602956447 1250 602955197 602955251
    0x1a03163203120307180f06051b03070c170d08180331080307051914010501060c172718041401060f08100c03140708041101030b0a0b03060103 62
    0x365241000040103001d103185080d040084090008100070507030480c2c2d41001215020300c1c03e09d44580d90003200c10405401403c00e50014031000c15004240250410142c0031a54020030201d10b019103d4a0692140385c1c41c040c0303030042180140020758034040280b04018010f10b60702668034000302819600340c040e802c50903141c036004109403400d513200c08070303c03441c130241c11800e00460400060381c3d540c5585441d04141403c140c1c8262081c0c00c20000da039041013404008102c0240040e42e15444000e04004058900b034810030ba018107440303040d020420480b10038000641ca15140319030703ea04600c00c0b521401d01d61540152a01c064a4440709012002c070b401248190501e0b800000d00c41c03013880c01e40d003143d00310f0850300c4980c21042120043c005036240746043c4d000400700303191f150404160004c1004c484e070a907100da080800c00c41000e50003005148694411502003072040d40c018011002c4416125040d0b0300080800300a00507404900050342d40490149130104015145408594042007440050707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 602957697 1250 602956447 602956483
    0x114220314011e1e0902040b1002030a0807030501030f0201110708030f090a05060f0d150b07050c1003110403030324030f12050a0e0d0606091a03163203 67
    0x1182c000060290500f07556840c0c00c1d080c0b00c081034400b00d80c910320340c0c461803592840341d481c03a480c000c54072607421046103248000d040400442e080300d00a901c80c1c8c8010455000281d40c14002000d940c00b0344240303411b1342d0304075103140341e542415401551940034040142c07090740f103981000900c0a104000905c2d80010380c07145543c4403100d103c10f100101d0036a40184d0f00c1088144500d030349145400b0b0550341500d40c1960086559207074034083c080350402d250064007107400e0000e4543c050050000b10485543c030146c07001c100c09500c90b40201d04943c0414100c0c00c00c000704000820109100b030304035070704407100c10030302a00950404070000b01041503a40308842e00c2d00d8211007841800b94605015024403203904050780b41c01c0450700020a0901c0900341c00f4445d01011f4028010300080354080c0011340f0130140f08000c940e245500010840380500000c80c03092203030300c0450055132043c001c0c1508450220581200c0440104020601c003059145e0380e4a084100c40000d01c00741e40c0802820041c20340042c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 602958947 1250 602957697 602957711
    0x120206100603022a0f1b2409130b090a141b0d022101170f07211109010b0c0f190b041b03080301030309080303070e0103021303020d0507060e011422031401 68
    0xd016040840004071812078011541c0ca000511031f0b0002c0b1120284110b5607000c0d0740004100e01c00040808000719030f000030b446010800003a125a000146ca00c009540f80140c40d40c1c0c032000980c0311903158511750f4014006105814000745950007a11100802c202d441645005c4051000c007080026070244002001089500c038100300306100d5031016400e404046c190075420326008080f82c0c030800007030282e0042c02540036820310072036042c040c2c60144000d01d65405940d5031034449110360800c84001a1602811040000070600000c0c040594200541c4038503080c3c09507107540c03280c400c00034415940c1c00c95041c12080507110607401c010140d882040540e0f00c0e5411410300404484845c0c1150b2510792080050103110754218031001090502440d01681d540a06c00b084128400d03242d00081d0080c4a5070750075400c202001c50030344140c2d00300da0384040c0d100344000d004480303811911b07180ba100110b041190904500e00042060403020035130f2514080710740d0f240d494507003550180040c96140d940d80c100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 602960197 1250 602958947 602958949
    0xc16030201080c0309070308030612030c0105010807051002060112240e0615130c1e030911030102070803010306090309180b04050f06030d0813120206100603022a0f1b 73
    0x82e0340000c2c000c0e040c54150315040340d2159480440d400054000c0c7d00106c00103840f682c90008000c25001c800307060301d4440340c60b80032050181c4805e00411040e4000d102c8041164141540c043c18800700503402010700340d00e0410b240211025294041c0c2d440400c442c80305011801e21020201c0645042c0d038006540000c040b046428030102030f00a180c0c00c80c10300c101c10303030680d6414004c8550401c1a10700280500c503281003a0b034220250701481a980410749070110980d0781660091240038010a008180c0c40070170020036080313100c2d021f80102803803030a00051011400b00d030301920060b0b01c81e04002e4041c940395480c40244031028501010038603203504050906043c18051190481a200d42080c01d60500d070740020b8550003080f008004004078600001e0001d101242141e890319000a0304140c04813103403500a464010441d420306064420b1500064040d03c2403080b66a480c5152034420080742504800400c0881500d29032180740c070821450742c0350007900740241340c007090341c0294070441041c01d80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 602961447 1250 602960197 602960207
    0x302060703050f0103080921011517010204060c140c03031b01140402010509040b030a32070b0d0903200c0f190e04031407050c04111603050a050c16030201 68
    0x2441c3c080211400001040000d0220055070302000040712001030290b01d82c4010074501e04658090380066013000c14605400502603a03010585044507810500450341071106401e038800ca01c2150000780031483e0f10004103140540301040714511500380c5407054035400009203190040c0c2c0c401d5108015110130450080000d2242082105003002c031087c0600c0e1580010340180906000395010715104c004182d900e95052200140055022445202c9940c4845001d0145030500c10714a100403484c56540700d2a6400080c508112100740013140e00e40606e95a841c405400608411000d00c81b002040307008640340c240000c03042d0340100c40100071020440041040702c024002d0301c103000f1941d0007965a00a0303a010b01c82d400f0fa440d844501ea0098a680c82c0407140d2900901510744c00c100086500c004211010504295620301100e041c0105101c44642414038802c01c40031505401126140303000183c010009403079607400b04d051031420720150103083c5090500d81d0b001684100d940607014000c41d030b041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 602962697 1250 602961447 602961451
    0x250320130c080604110d0608010507020c011110110c0d03150f03110f0d0b0408040e07051912180602030402090109090f0f0813240305271009030206070305 68
    0x540501c416080c0d070034040c0500101511040c00785450358200640b0500502c110340140c1041d00040010540d2642031500030003066444c0d400501030008640820b44c8180007500060b450352000e03001d084202d5000c14000c04076110400c1070f580050119401843e41404504100381d4240c80101c0d001600f0414042c02c05000d4101d500b400b05484000c1c0701003100155144907082044d18140030111744440000c512052841c8024021140c0b0420441009031660191040f500c41c8140d1050329214144246d43d24015921181c088a211070b104090b158811601004d0b07180143e00c000403a000d42c086002c0364514608000d44080b90000148800c40c10301c0b2101b580180031000382040b401c01240ea80800780c2e40745071000b070a16510402680c0901600c2000c07124145101c58500400355980e030101c040981c0c031102010091208280300c618002d0280c00307418490096480440c03803108424206045100301c05074403042c1841441c204549455440c030405400900a0700140100d18248100409032640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 602963947 1250 602962697 602962729
    0x3040902030a181a0c03090a0f05010912050403060b010305040201050f090a1503060e010b0c0703031d0a030b041415010614070c0806010503071a04060e0d0f12030c050408250320 78
    0x806c200004646e000c40e40300072181e4483e005007080412400d00d0382c007400c000700d800f5000480e4101c201c00382a4002d00201700701c4e403158106024120101300190300700c52089601a0100d13134104035411484480c1001089102c000514070a0310316240ca2101d030310308048010190201e6034465060010008204c03205006210240c032052034600003003d61030b264030103480001c0a02c1030030200788009181e90f0f181d400300d43c0e401400c00100e25513241040c6244003816141902c00d03901036400100041008501c50703c1150400107807008591907c0c01c21500c03030070b111a0701400e2010a00c004400550b03400c0d004801080c01d94002c1ca503079410142018100f801c1713507200740740d201c0d04d504249a0480c02c040c00d58044030700c00d040103095004510003040004245680043c400160030100d9000c0100d8582e446402101a5500708000d00701c01606a0340c9104074022920305034056680360303200303081c43c4120340328446241d08d03000ca101d45d495a49101054102d1055100c00603c0c400d070f0361007030800113007c0401c1c4076 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 602965197 1250 602963947 602963971
    0x70f0f031e0b0f43120203090c15121b16060515030a03021b040b0301020c07080714090a091415040506060a0b0313030315030503180a060203040902030a181a 69
    0x39882444d03e8042143c60010360003484950b40c00403071580100c100c061021305a20055540c2d1503c0180e0948940781c061001d0b20501030015156a240002029100d40d40e081754150740c1c2d03907101c007051820612900c651f03080b042d0a04228481c01081c1201c510050144034060104881c2004080c005000e02444450b50180d407110940c6c0c40400e60003d4031000b10207a0703601340000ba8034a000810041c0280070340311b9416600000d4010f80760140020050110362889040e11406c0b616200c000c40c8111500d401a6030142c008808104011780b180d104031040e80c4200116040503000001c0a07042011600c89100300c03c2c818410030003845004e0160582c011011070b51041303001d04100c03042c00d03240805412105c400c45c88402d43d504041c025889180280340c05503840d00003564030b1800c1e039a00d40c0055080b074042101000a03600c0c1d41000982802034903a142c0180d81003030308141c610320094000400e20600961104d541c0542c80e46400c800701d204a0003017050013003200200000042c0710300054450740c1e03401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 602966447 1250 602965197 602965261
    0x30b060f0102030a03050a061a0d0501090b01020d0305130f12171303110f03042306041203050a0e09070e01030c0c1e020102120318070f0f031e0b0f 65
    0x2030b030b01000300da101d240307241000501a150031030980002e2909806c290350381c0e50410428181c0c010310740b001d4101e48030b1024040c0041c0e80c0b5100100c0c1500c000609180c0980d01440001d01000e00a4200135481407909161441846541d01e5066019409031403d6032060f04480c0161a116807150400303a805903043c80a0318241841c80c208203800d010590050100035044a4840c59000300740581c2419285a900301ca0304ca40d05c03511428a81c810203405119004e000c10300b040014140b5900b524100c0c0d00700101c00301c1d800140d4506441c1c9500c0744807008108900355407800b1003681c815101e40e014541c0c60381ca0503030f40c091070000501124503994501e010b004081c1d0071140051003d07030781c0409000c00e10440300c220b41c0c1d891005038900440800c01c0700540c5004020065201c40000801d5a890788100c200c40c28155152880c00c4c145110340208520101c1c034034030601c086440d1041c42001078041032004450040c0e50b490745101d0402c2556507006003c00b50b4140030500c03d01640200c541411150318560032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 602967697 1250 602966447 602966449
    0x108010b0325020309120129060403060b060d0c0c0209070c021f14040806071e14030c0d051f0504020406080604090f02030d0f090e1302040e0c04060609030b060f 71
    0x80b5680c0078400121280000d442c00001e1090090f10780021001d0100b41036841450350944c0130740410f1880074440300f280d10000c82c03100d400500b01c200c1440058101e51800c0d0071500c881019207090301c81a9000901080008035201c03003803060a0071182c8540d59000c0d06203091041110700c800c09090f50080114010190025070740b03402d09200312568107086042c10720150a0140e074400b0000400c1c03015a1004500002d0144004c00c045104404540e501c69101d510400d106440d034001d804820b00007040e50900c1c88281e40c40000641e041041440b881e030800a0303188801094510840d10002411000c1e19681d0012410080e0000640b000301e4040d401c00d0b06100d07000780b00c5100140841d114035100e00084007880030000e1010045038014041c1d615020781364070054046200e210008000540314a800954010650410350289444142035100045140c003000082d140001d00340055003c0c00c40310760b40682d07880c41003100400722a218004210300d142840714600400030102070042404098200e59 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 602968947 1250 602967697 602967721
    0x4080109120503090c221d010b06030405060a200703050c0705040c17180312071206030f1101021e0a20061b0c03030d051f0e13032c0108010b03 63
    0x11801c800c0e9103008503041c600c1700300c0300010346d00c5540d2100345142041c5108010400c062144070244c0d014028010f9864210910009110031a03014209130030110210b000c40324650400660320a03800c0c14600440c1c00269401880d40c032081045000c5800080c40d52051a803d01c5008000d0000721020007581d180488003500700f042240e2000407043c42e440001d890310440906d1580c60400b11411251144854584100c88000640728440403e580100d40305129205003e0039054a43c00160024484070543c0d4001e5a0080d60f07107020b0560280d02c41c1200c0c14000c002c02480350020030342c0106102d122908100f00304020700d10b00c003800d240345400440e200e40c440d54100e80c0740c410020b10341c11101c00c0d41c0c2062810301c214811180d0341800001119520b000c0103800003070040ca40952180e01a81c800c0c0745035022101c2901c42c16141c041410005420740b0115003001004501a06000d96103120703c0b04030849005000070054044000c4400c4280d003075a000c0d5840c1d0240111188131444e40c1010610144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 602970197 1250 602968947 602968963
    0x50901230315030f0109050c180405030d020304050c12010501061206080706141b03040e0f040b0613090b010803040816080309060a0c02040504030e03210712140408010912050309 78
    0x41502a9940b440340c06480c104815114003403550300800c4a4203062600580340c40c4520303c81c6216a0880d1044142002204409405160b01200651520201e180900e020b500001c5c42036841c4e00030960010160f80f01c45c03c000003001803000c000241d0350305025000d00701116030800014a50702d0540c045c03015403000900d0b041520000e05000302821140349010020340314044000110420602100c00500320001c094004e50300e81c840c0e075038107564403003001c1034100c0e5046901801c68140880441c03410b05000b800c40d000b4401616011582e602ca40c1c031206000c030001c2c1d000d1000b551001400700103e60f010321160f0200b01a03610715006051400300c3d2281c1e240034110407144078050004140310868010700b101c0203c940d018006201d545480d05010b84414103580d9424001d00a01c03405441e40b100032091803484030350004446040c01030a07255500048003550541d020301192040ca4500341c82200050001090b40800100d5851071500e84a1001040a20303006d0502805200f0721044a0003c52038034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 602971447 1250 602970197 602970211
    0x170f162a030f050309120c040b010e1c060209030a21230f0d0f02070c050307051309060b0409050a05160302011719020d02091c020a0302060313060c0509012303 70
    0x800c1d034100e40c00c110303044d8820b482016900813502c0000c1801e0301008105508170001c200c0d01000600030f80401940c0106001c00d00702d6214410300e803c0320284940560b0380a47d68040c4100501704000000803e1400045000603a50300400e207401d04241c0c0d14004c3c82c0c1c0f00d020414034046000c600d900844000d80c0c0c4c4802070074072060402003000800d0400c0d100a0361f0000017280b0081c013022850a4043e00250b0081c141510000300e038060104941c01c00140050880714050481b0801d40c1d580c000d10002000b1142c421644140c8807803002e0041c1e0303614040e500c6000d014a0240c011490b891901ca880c101d04001406240b0307071641c074100003607a004001030070303242094500c07026917541da4401c090388040e1107544079010703d10101d020520032038250301400014800f44c4264664048aa1481600001c2c1e40c40003984074a83c240240010b060035805581c01080341090a00d500d401c0d651001e058030884c160b1500068804a244442503920288a1011806414200e405441580003d844510004001e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 602972697 1250 602971447 602971463
    0x3010905180d11060c210a0e0102030a0e0c010207080c060d0605030105070305100f030305030105040f090606030b07140f0f0a0c051510120302060601051303020310150f12170f162a03 80
    0x4114021fa5003100d150b80304114001c650701d00c0c1c2074030302d0401085407030042401071098250301c141950000030900240d5101038010300762001ca103001c104a940c0015500485a074032010001785644090007220b020384200d40700800c00346000c0d15040301d8444940c6c003054141c07032840010004660054103d07415280d0035034012989030f8040c1200c801a04d401c0c0e40040c071031407070a40c000003440300c001800f5018200d69602d000120390710070005190b602801150700b03403001302040710360814040440105402d110500784004948440d0315100d0501c0344100560101c0d09680040009070882c0c02c403260042c0149200c0951603007a5601d00961b207460007800f203414800c0c0010580e40e00c487d108001070083d94010100e40075403004151000181c4030600b40503c09030302c0b0311400b003190080d0710b14410607039202802d0907032203562035104d0003a00702c003402d550024100300708040410120420000c004007140c820f01c8003031507007052500b80d48060021500c00b150701c4140344109400e40440303103442c0c101c0b0b80003c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 602973947 1250 602972697 602972701
    0x309012a0c121116055409010509010f0c0e0405041b030f1b06050712090b04060203091206012d05040509071a04030803010905180d11060c21 62
    0x10035948010481e00f04012440380f10400d4002d21990482c41e8240c40095440f11080b00c604049214000800c0704a42e444c21500b91000e042d00080d580043c0b402000c0030380000d41c1c0e80b20790030320384078061095441c005c899460f4410002680c5c0240214299a03000c403408201a00c1003103030042244101d00c005031f106640341c1012809026032303411941100492081c4d4120810b549180c1190481228041160340403212010b10a070540991139000491308151a10751500e2415034036580101402d48480c801d00840b254003003038070300c181c90241006c1c02c4942c00a55176a4040402c12101403c00c0c03a60a0300d5030302c07600c01400a20007031100946040070800d603507202c822990300c03042c400030229005107800c03a15144c1041000700700019040304650815900d6058000c000880502611a0f4003001e4088403040004015682c840d52016034044200c0c03006100e0450350070b58440c02d0104c0300b13400b540000c0c0610f140503014030045c0203c43d0043c2c0c164038501e00d48410304080c00414001c1421000c044000480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 602975197 1250 602973947 602973983
    0x21204060c02040f050709030c0b0304121110050408040302011206051c0503071203051008030a050f030603010902030a030305101202130e0712150c0815120a06020309012a0c 76
    0x1311a1207030310310314244424030b40b11400034980c0910b48015242200440b90000d45200140304890150f50032481c48440905103100603148102c4403001590b03d4840c4032041c1c00b105149106090042d07206900141c2d540d8038500004014407440703518041400e241840410017a0703104c2c0062058240c3d41889902000f400703060080c1180248180035040b54909405001381d0b6034160f0019201e0050b4198004000c1e80301c0005030340d0b03401070200e08800f00d20f0801440384c52030041d1001c0e651009000b03002083d13030007030740c1d001c80e00b02442d02e041100440d4864051111140311144014081c03d840e5654038403941c0d0700e40000380c902500380003891406503129102c520241c000d07c5080081d124030180100d000070b0514202200c25400310204013924a0072040000f500d1040c0603c1d0701800c0e25401c1840c0440ba8441009042507030044440607502c60b8402600001da1280051445030480303100010341c100030708444004800c210101406131110b00b28620240e15000348134418000d4200766080100c0071900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 602976447 1250 602975197 602975201
    0xe0109030b07030f050c0c07170d08060418050604051c05041e1a04090f0c0806040507020c0d151112041b030206120a060e16030b1807170106021204060c0204 69
    0x398080c4281c0c182406c2240107104400101f03814001030045406071999002010860410000107500c160025081215030510031081c0781d4224900a20000b0308440a81c01200c3e0310800400454443d00910100400c0c00018007140380d40d007502104c0d440c000148810010f055126602640d002c2d0b411510500c181244082c040030050040e1010100c20702c002d4040610068001d449080c20b080d06150300041d465085000d800d20940d003a4480200c5526071b02c007040b001c1c002c000c08400852081c0c0041204582d0307181b2120085a0080600c080d4411010449805940c80800c078500c400b2800c100c1811a1071482100f103520a130000c0d295000454002d040004980040d400a0351020001c034520a1000004e442d4134000c25042004000c2a6928015900a07001c00c0700e90518036010882c0041c00d031030098004852241d03006010085070032140240d1907106500352400710000e0103103100050408280003ca034098900d40c00100010140e10714401c40b0341c4640d001d802c082280d80c503000c1b011501c8607 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 602977697 1250 602976447 602976461
    0x60e0112080c01150e2d0c0a12060603150503120307051b150a1a0a14030102040b03090120070b150d05011103090c0a080303011215050a0b0f010e0109030b0703 70
    0x211200713146095035480071542600099030680c02103000c182e10790b480060141d03071000d40b0101d00e01103030050742e82e441080904c035042038241c1400c2c09607806151030544c51a200d20005082241c600080701820310b40202e90382c201a0300964040d038400c140c00340c12180c461b415680c0c040114038040381c4c1d0341c601011028181e4045441d01c80c2c184035600768241c001c00707101541803080700c19100400002103040000070800700d540c000541c00150740441401000340c28500243d15100c058005840c046d0381e81a40243c0760310849408406035541c1901652003040c611650740d40300940382c0d0203820105e5545540402c03142c0644000108050342d6802d140380d46841d24200ca040e90410f00030041381f080009a000b00b503100300c9019116014004c9002c0480c5071881c1c40c038007900d44000085085a082451315003080e244000700b52640d444039018032104250a00401d80314a01400e000b0070560494400d03c4140e08402c20018140400010544000c1c0d038003c940b00100c94001c504985181c4840030194010110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 602978947 1250 602977697 602977721
    0x1b0215040905010b072a170c03100902010f0c08030105090402010306030203010507030b0f0105040609410307090209030d0c062301050a1203050a03090503040b120406060e0112080c01 80
    0x18030000003880d01141c0050300f60180900441103105050030024250311412916129481191b81424482c20b91f690300c04d4a4144d0200044914540340c803400245010702850140c0541501da5200300c0855a120700751454640e01c81c03d1400c241d0696564071041c60005004283c0a000c0b220006400d5a02ca43c020301c00441d000390080009080c9541c00802030507844102c903005440110f203091141d44141c0454040340c2c0d1540c0d40e560b4090a045070011070a454148424000c07914400d0380410401610a1508030303146201d40380d070080860b07018141000313915403004500d50300c180280c41d0f840d24042141d641c9103034603241605404100e03180c0800282031a4a100c0410b18401c41010490800300c2c1c203081c1600c03070498107090080d60790320345104440303030502c40200022014010230340001d02035001900c00310b00c2002a2424a0b40354440501c403608190940b00e2140e02c20800c1c4002d020301c0e031013440701504104040b01d502c1d40c1082100e52110307140141c000c1a100b000900140748003020360100f250340345 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 602980197 1250 602978947 602978951
    0x16030c1e02010f24150522170d0807030b0d02010513180e010e0606010c1e02041a04181101120b1903030f05071109041505010b0d0c1b02150409 63
    0x208071002d1072540015000608202d43c04044089801d54004281c0350428034036550340ca260039008682e82c54241e40340381c4181000b10301da080104100308c4a0018010a4520200030718441a046000400c2e150029002400341850410003484c1601e0f40c900c1d41d0401070302801c00f40d545000c0400039046642c0d4a0b0310206112601d1041e81041712500e0f00400c8065112100030b001101d08400466101ca81c00c5d070f41907000c640395501c41400640050b106404901e4034031800e100f00e02564021606444000d40710030f041222070b28410a40d883c1c03501c281144c50200c19604444052540d0b03d598200c14031084013070512566051500c2c00034000c0c2c00c007029608001d400b81d1002c1d0303075070b044101d4801c2c41808201d01141c0000c41450201c0c0c8540140d072030598000c60b810039040d20601c1031105500001c0c1094403508817000502050303104034060b442c020026050300f29a9854007688200840f48205514000c0207005181084411010080c100000e038048030082c1405000d01114940b40c42290701000800b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 602981447 1250 602980197 602980211
    0xd0504030e15040924030210050f07030302070b0f0402011706030723010318112713120207030503040e1e10090b040e030a0f0306080f0616030c1e02010f 67
    0xb1510501500031200c501009101c00c200c900c001c1c8065049200000d0b41207020420100003601d000d070041c2d00f400700070b4148940340c000800081c20580c1d00013402030380130a4000070303503030b04008010350200e51040201242c5081403c241d1f00082120040e80140c1511046c0900031801a41e81842417000401001900ea0741c0c0a02e0900c03003000e0665480d8010740441d191a520005843c5004102580203901140e0040e50343d40c90810414651071444030100c000c0d480600780401201c004003402d000e40d0146c00034030070808082c9841c06034686000140c800315000101c0420000c0e50005c250f400351880e981080e212070356241c0c010f00407654074080b03281c00c841401d410b119984002a82420a540c0625024444005a1800d1100b0f031132000042200343d40c410800400c44034444c2c40000354151040c50041000ca9684240502e8580e201da8400050303004017013840f1990001c6d4200c9110f1034560b0400307202d150042200501600907261401500c01025450b92206503c00e44c00300910b1003030307180c00300080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 602982697 1250 602981447 602981479
    0x50615030c0319060f020306011b0507030803010909050d0f02030d11070501110a02011a0a03061d16170601081f02041e05040f050f150a090203070f021504080d0504030e 74
    0x101c00100404d40300c0e185458050549406a8002c60f031240c1c1040e1180d1580a4080d41340d41400340052405039128080c0120100004207102c1c01035001f003100c0d42c00400d48407041c0c240030f401c01c00403c20038414018a40841ca180a030048242da42104e440030340000c0c80e03070896a0f0045540705505006005500c1c100e0038150110904000d01140c2d006a8000c01000e2403c02c0038140b04148003030019400300c0c1d410310030800102513030810004440744844064003a20040d50051500180010782082c041d011801408021307018602050040b00000061902d5403400712900e40720038654000401c2c0c22052461014078079159012a0700900b030700111008903404c02c805004104040f0b00480d0302c5181020032480940c2014081c3d9401000c800005941c10303107404403208610300c2000300d450b421400c60000060340e210030740701452203035042c0d8403009070a201410000307040c182641c82ca020003441c13010910011a44180c00d441103015412800103284d00e46003000d0b210594203105aa5204104980300546 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 602983947 1250 602982697 602982733
    0x609010507300206010806010e070e100305010918020904030c0203191a0108061b0a031107110103050903030403050d02070213090f030207090b0105030a0c260402031603050615030c03 80
    0x2040b141280c414008401224102e0f00d40320284220500c1d90700c100700601203905400e000b5a0841603e003030002500810310046100c03002c0c60300d0341d000440d607641c00422000c0481d008034500004014a501001c4580c1d900064040b000940060308000d1460300d85402c5403000c11440480e42101d052001840c5101d00d03000300380551050100c035030541c8101c00000c07110720001c2c00b18025a408500e0560000760441c0c0681503410a0b1170000405884500c150821306000380140320f080d01070b42410008007141c500160543e2000b4004d48100d501c100200b10100707901009a035580bc0f40a41c003d41e0301c1d4058000070300c2c20000021650b10321031034500d403001040082142403080301c0c0f1039002d44500a5440030302408607240d020201c0c1c0440c40800c0011100507040e403000300300d55030345d00301a42648002140e084541c4195282c0c075211890210a01044d45410801c281c1c2445901d5606544035041d6a110b40d100c030409041e4ad11011104040100260790a0100c848070304005404c40301000d0b003440d500c03c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 602985197 1250 602983947 602984003
    0x5062d12010f0311060712080621010b120a020102120706090b090a030e060a20030c0f030a12050106050f0310150201020913050c04121e11010e030d0e0609010507 71
    0x658402451100102400c005c8180c95081d90810015201c03808980016160524001c0c101588101c082461480c84a040910201c081a1620001030100c14240034803502c60313001c00000c0300e10780c0708101600041c4c0c0d000440c410b202e81d244000944035807051501c07030301800c600c540003840c8000810400c07181107800900744107010300955230681c00c2030039281484000e01c25101800c0000303043c00c4244a138100d4102c54001d582103030108891800e0700006101c1d0410170010048010398100143d10240395a2049025521031400351040007254540400a00544100303a1445e6010310088009510380120f0040c500061040f045885010401c07048021700079400030b01000d108010340d0070190443e0f00e80348034a511860340101090701e081c0c01c00c80000c400e0014200d080f1250403c000c5121040884a065096141e12543c0c803481a0b036641e000144c100101c2014080c029800304001e02841a8071902c1040d60100a071901581c80d038804004841b54452110058071003040300d100c1c640104044da01c19a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 602986447 1250 602985197 602985203
    0x51b01090b0f061509010309021507050106180203071d010c0b0a150923040c271d0618030c031b0601270c0318120905062d12010f03 58
    0x3030050380e6582c3c1002500a580c2000002c0c0c0102409000e80c1135000b139000d00e540e140024100c011024070030002c1000380d848020100c40d079035103951040001e0341c80030380c0024107035001550035820f51416000c014080103030050f02081031000c04903181c1f8140d02441e1402615904414034030303907503d446403148014102000d4460100200d400001410500130b1040d00c2412502c80c0052680305500c81c00342d046000d000c0c0c800d0741c2c6c0181003880001d040101c1d0100e01d030f207034014840241030a1002c86203101100d21006400b14982e40344064120344030004562994407040b00c01c2d500b40401c0c40c2d03480e0780b4910f004d2001008428800050760541c004002d00c05d113000c0c80341071421240560389407903414080383d40f82c05502190a035480007800c00784100b03400201c14640300345000100c102002128030b2480046200c02e03102071280c1c4200c0c0281603070025071071014007820b07242d5504c0e00500c000d20000c4003010008040902d07510b20b0f0f0008400350070300200c840d0204040c1e0020f00701d503114080e44840c50440e00c012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 602987697 1250 602986447 602986471
    0x607120e0f01030b01093303091a0402030a021003020f040603050412180303210606080906160906050c010f1d0607030b1305071709031b030304020907051b01090b 71
    0x1c040542c0300780908495a0410b81d1149030140c9443c01d00d030803901458043c80e10f00c40d4540117030381024101015240c050041954041a1030006042100025107a40c3c1440320390600c000400015840c0083e00c0c980346541516400701c1c401c48500103c000340030b9600c0c0b44440000c0000c00281031541504a2802507004000b00c6052141c0800300355041e980240e01484503001114003000401d0244006907100e0803c45c905149214104003010704450707241d0040000304414106202034120104101541704001214a0719080f13882030001e00b10149601ca03c070100b180c00240d2000e1400c2c290014a00c08407031020601000d0a8942010b0401c44020240050380c0b02d40300008828602c680904469014064028040150344994030000307080014400024041c5462144c1d850b001900b0340c06124000c2c07180990740b2101d91000c0d104800000c00c500f42d000744e1090091002603540d8480141d0000d5660400307a56650300c80da80c01d045c010341c40b00303090955440c2140c003805112440807040e218800c46901c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 602988947 1250 602987697 602987719
    0x601091214010b13090b0c03100b07081905070311121603020102041d1f060806011b1b051302040302130b0d081c14090a0b09190503040e071b0b060607120e 68
    0x20b00d07c403030204440206054215850400c240440ca10060466074080e1440c14503000c0c03001c0d0180c101c45000d001680008600240c1c2805140d03002d000e1151070001c00026100c07a21804081946c00e003d040b900b8001d9400070176481c1e0415000358103c0b0b0003040001851001c20200c1a84800d41941c102da03421800317004100d0b0240b1102020b040181500d80c59100d580042e2100c000454826840306d96501d01d084a14040343c01081c241071180b0450440c0315206030909007001e0900c240761151701d00d1141400d0042c0030620040e598800c18102040204400041162003c0c0024080075124000508080d4000075035044100e6030014a9035015040319040c41055400d806a18800c0e20031524090160840d00710302c1c001915060400c1d401c1020642140c5082c08030060b2600398a200c404103c401ea44000340c01c0003420b10010041c3c3c1d120000c0d09200c84040c40e0034a02c1d11782100327130b040300070f241c1652100014480d039103490944034000e42145420100401004020341007038400c02a2078403c0341c100c28 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 602990197 1250 602988947 602988961
    0x3080d0b06040609120303110c0703030f0c0201080f1b0408011401140306060111030409020f13060e060316090b0c010b0102010b0a12031b060c170601091214010b13090b 74
    0x10031141260749554130050902d1421001318070100d5003020031800c044c0c40300d5070403000929100140000000000c054400d491640c40c3c06004401c003500100d0a101014603c030700582c2c2c01c1071090303600c040740010103810380c2d440802042c100182c4040f0000c4000e000714021401c00015444140880d41c600f40c0301c03001b81d8030340c0703142c0703041c8141c0580043e0716070f021500103261548070b01da0000d20344880304112030400d034036042c21109a81003201004c1d1046004074089070300600c0c0c13aa5590041041d030800c40020024040412114800100b400c5459054401d5650040b0300c0707a429500100500ea2400c0d07115a5000f012901800c0a000f00c03600660234070000000c1c600c0c0101d142e00071240200c070300320307c1175038a568140d8402c590020039034001c0414050030000700300c90340a000080311203951a104645202912441c1c2c1403c041c280e2410021048400c2c44001c100b07075124056140c200c1c0e03049911100b03030300107d800342880050719074209110446100c0e0500090b0810305074603100351030b8400d066031145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 602991447 1250 602990197 602990209
    0x1005462d030b0109020c070f1d1b03041212110705061b180f1201090b070306050109090b0d0614060103061d040f0c0e04051f0b031b060405090103080d0b 67
    0x1c000038180d240440010000000316900404c006500310040d00c03038442d559020b07464602c2c0513031311410150300301c089038070340d6011225405988212004504443c0c01520781c41072066001c0144014400c082c400e121030041c41c00b8000341c0317891a0681c10305004501580c2c4d2034a202360040b030412501d51180c200494030f52420341c40c4041c2d021302c20f121070311700304003c103c4505240303090324031132941000500205119580721040300b004244000d50010a4201d00c0d0300d440300e141c0c0d9001700304200f01482d000c0240041e03a80862000c00306e4000e0300d0b001c200d03803c030100018440c4003040e1008060601e004a0202441c2c8010800f9102c0d0b0402d8800b00f000607980c0a181c200c1040000b1408116190f46001030001400741210041040c000c0c80076100c82d548500a81055080903102500e071135110790101840103e40c02096066081552014800051240003180d5146204c8020070240c2c0800c0c2c3c0800202d860300e4080e20010b100040ca0440256501d00703016145500c0301408060b0181080800384041c1820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 602992697 1250 602991447 602991449
    0x3070f0905030f0a0b06060c0f0a120212030420061305150a0530040b0412051c0b0102011514031203040b010611100c081005462d 57
    0x458058800383d0070507924030005d4036005001c241e00410500c0442190301d0208029844100c0940050030301d83c205050040700701d5503c404c444110b5110a42c0c401c0d005443e1002d5a03001a8049003541c411050600540107140700c101406400c20008180b401e200403104d00a41d04403001510301c08441c1d2160300c0f10710b9480c890048d450012800402518288a078440c1444100e2071b00c3e06c100002ca603070200c003145036214003078034292040b460000c18802403010950007400d0048180c20070b05e16010a0712451001d0300050900030b203050703a0303441601340a64002c0d005214151541c82d666071086840f42280c100425114082a0091040c048002420030014040724000c039004402d03401030703038030b00303601181c00c1d050f41400c0510ba8064008581c0e80d6800e01c0c000c03601034002d10b450300d155a240c400303407080021415034840c034461036070b5034900030102c481d800440300203418400000c1003040c45154102e045854040042040f20848a40000c51100c100c0400202210041c44005950320210510a01c4609 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 602993947 1250 602992697 602992723
    0x20a0b03060a031e0506010303120f1a0409170301061218080f0c070914010501080916051905100216360e1606020f15070503130803070f090503 63
    0x1d541d5003440850604c003c82d01318044070b290381d01680c20103941c4040c00c10600b039200300c01180301c8a102c0c02c49010140900480c141c2d84010800449901c038040302140e0750040c050602495035502981c040c0030745210041d01c4860702c2d200a503544d580d5090000c00c0c0380344248a0764805450441328101c16602c00030504481d070740203440d450400d89007061240180e40b160000c480c02e446068400203c00c0010b010f19981c51202851215440d0714023400174000d0070000380301c0f03c0250441448008449940d00302c0c1c0c1c0c1a607006854450200000c180c1141030b41d01581c004640c080302407414200340907800119805180351803403454810030398940700d54900c50442e4100d1185002c1440030b000c800400c00044010540e81d50401203004c20b2660f00240c24100040b0210303103000c1050300248130700f540411008101c1c10f0f0100081c1800300300700c0b4018402c3c685c007900b0001002070000106001c010584441c40c84c2c00e40002c3c0c411f03681d0410400c00340c00b554051039508082a20074500244078070700070500c0300078441c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 602995197 1250 602993947 602993959
    0x209031b010f14070219150509040c02030304020a1406070605040c0302031c090b0a121b020d090e0103020d060b03060708091e0d3b120d02070608060117040f020a0b0306 74
    0x300c13950802c8188070014a4005919039a0900020841c000e000c041d4600302c5ca07500e8142d03403042040306110640e03503203496150540d0b00070024000161144051a000c45012404540059026100141c46c920840401908a90601051106210340d0f065a08101d81c4218100e074141e801442070310b858503880c901d1020218850700e101304407840010000b003002c01c9a40c909900990a40040c1004483d622644441c0c458910445003038140c4e010030900c02d032500e450070840081842c000790782004c4801408002c0c00348020900711300400800740c0242c0000c00008081d903c0d10301e032007000103009420407070b04c207581803045480300d0700d401c042a1707200900659054003520740c400c000c08040e01c0d0050400010008008070031407140126101545405034a510800480d46040310281041801c10014200074265000075400e007a10030380000d5180121451400c00c12100c2d07907100c00590300d0b0307610176246115402d4103004201c1000704048500d28414402c6650000c602e4503000841c00314042190303155000300c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 602996447 1250 602995197 602995207
    0x501080d030509120307050a0906050c030d0b060708160c05010804020d02041a030106090b0108060a121502041a030901150503121b070b1e131202040209031b010f14 72
    0x3510a810855000640c442200d5003450180c0f80504035034070858903580040d04c0032a01c0038095a00ca0180802070a41d07140c968200051505d80e15100d200d00110f43d119503a50340e0981605845040a42c1c0540b0b4220600c0d60b101c404c0c10300030801441c1c0d45d540c1150354514400c008a80756004050705801141c003e4070640c0c500a1603402d203c010315604c0304442c0c0d0200300c1d20142d0540d6a0034090900581082e4001140480641001400d1040302426052080314140c800388400c201d42801d00f901c090700700c4c070411100202140c5410091041da00441d910f601c00d05007030303124864940015402016000300170801d00c4490349100304030001d1400740b29455000601202030082d0703103c000c0d203240315034202e4980c40380c6001421a4503094590b41b00d2000c910011600400c541491520b440360170302602c055614203420303d4444000030415000f01180320002185c000250b440f29810b984501801508035282c0304d800034074205111030851401400100780580c11503103244500961207494820821003801c2c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 602997697 1250 602996447 602996473
    0x801090f1203090212010e0c030606180709030609050c10030509210d0203090703050706140906160203010203100e09010c02100903020102300114010c150b1302040f0504050108 77
    0x103441c003440d000d007010f8840c480d40000d81d03644c881c6034048066820001440e0800c0601e4903080c00402020280300790010800c001da01c0e2560600c494000701740314448800c1303640e8a042543c6140749600003400346494001c180c1d042110003d5142c50b110b40072254014250403000e0201c060701c200b00c03181e105907009003d45043d2949044500e002021890f0701c4a810070000b00010402ca81046070002000d6002c0c010800c14020240101c201074482443d000480300c44820119240703214031100c043c040c180004101e100030580300042d041d210b60044c025075483c240b441004001003203d00910905a441c3d80c0450f41640c414421143c1c00b0b002a00540116100003002400900d030b000c078182c0170345d50200074400491460010f501e000118112140c031a810404138008243c40d0160400c20365a030b9406034500f102da8100346410700c91540084584164042200d4000191141c00c07410343d004040812415102c401940207803040ea032980202000050340c3d201008140c460038803445500360090031045c440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 602998947 1250 602997697 602997713
    0x1501030618021827011d0f1e03040e16030b06130509060402090619080c07030c0b0603010608060a09140a030f120e0d0e040f050c03130c050307080114010801090f 71
    0x41309898a0004151032a01c8035000038080d0300008448499640700d8450011400d1081294084c180100040a02e01c5d048840580c6d1620004042645182950100c14400c0c504208031000391144559a14490428040f64000d00e0f002c0007078540071a00700240c07494075007801019903401700c844004c0354050740d00d080305000741450045d21140d001a0208030300311560721203c0c0200b156003100000400b4002007460020041440a042d0112070b28040020f4000301c1e074442070180c0c4190b000021903010ba165100082d0040c0556848503146008020400c4030030821540304014881c0030740e03208118200701a004648444000348020f02160035a03040c0c1008901c078040a100c540d170940400119070b19107948051401c40c0e0701a0b002e0000344090401c2d0745506190080c0ca0780107205140510240c10300c4400200c4074000105070034416400504140c080c04403d03ea6100180406029950115224960503019159080c03c00303011107500d03000002c003c0814030920080b20b400c51442440b4000c0f81d0346a6903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 603000197 1250 602998947 602998951
    0x3010e15010f11190f02090a0501030b04020418050115080c030610060e0102190606060e12101503020d0c0f08031e0d02090603191b022d15010306180218 67
    0x8141300b01c5801010b4942607001c01040e65024988410791020350b84100104598020800380410342810010000100821071454116a04580101d06e010850300b183c00c0c1507003000c6001e8055801c0400c1075016441306e071401010348040300700380d943d110b00d09001e150f43d4007403e0702c99100f20780880d0030802126119401013500400705105507109000d240000e800e20485410b41522000d075100802c02011380c00018083c001e10082c0c89079070070710708102031003602ca99130b2082488443d512410042d514031407403102a0b001e1a401800081800941e09101020303c1c0f1a00130700e00423244400f00032881603800800d80300c2c14018a100c44008420740ba0b0400441c0e046940721080081e001e12409020f27a03150380186102d180b5103040071451310659014101610245072010a51766952001c10340700310750126081002c01005e8101d2a0f080e05991401000b100450a0030003079801000d000800032100b110385241240e0103103000b8000b29803240d036895000d031601e14001b5804110540c811405604d0441d8840d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 603001447 1250 603000197 603000227
    0xf0e0d0203030417030c071a180406080706020c130905071a190e010e06130e0915010303080a0608070506030f090106081b12070b090d240203010e15010f 67
    0x1038202544c0f00b0240301c100b406081100314641001c14801c00d0309808000550040920314035208100824034401600f520605200e02c54120b0b140d1800d1525844a4010314020b0a41c0b1085404081d5600802921101c00740c0707030305100b00701104004483e05294003d990050341c11902901109280500d0003540003c000340039607031114180003626803e881d200e400503c14220703858500006104400042c0482d0201c1c0c0004c0c17051505018802c0ca03400000c404000340d03000c540420780c3c0e98403100245480c00111090148001c000000080300b0558004145400f80030022028003010b80c507142140d13200d44e0305000c4ea40e0864800d00000d2803000c608001d0b1784c6c0005aa4000152040c1c403140910b081c00e80400d1026403005c0c00a0000303260b410402018007035109401c000e4000d040c10b20780100b001c0d220b4103400c1885a141d460340c0e10140b02c29030902e4030513011360580d040b100c51010040040607410034414070040840300000030345080c21960f0600404c848c141d45844440d18801d0007510340400401000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 603002697 1250 603001447 603001453
    0x90306010506071509030f080604050f13020a0b07030905011101020c0c010305060f10021f0204080a030c1509030305010504050a0c08061c150204080705011803030f030b04051f060f0e0d0203 83
    0x84c8070036950911039010154025641e041c862a070b8520080c062001c042d14050156207404204031021400d419425002001e86031340c0554145103000180344028a90060206182c002070158205904002428115502070321a0660385902d1100c0030700700d02601031801c40540000d002001950707c69803102d50303c103500400300ca034022501d801161002c190340000c000964812500d800007043c00300060b4556040e201d605624150405080300c1c2c4829100000800b4481902d50544c10011000b6a103215415515400c10400d00c250500501605013882071a002e0b40c6042e002c15407981450041009a183c90340700c440b09500e901080c840d401070580e03650600400150400c0d400144108120714401812103000340e160303400c10403c107003480e100340c4c403203414030404060b06030030266280038010440b50541040910070b00c4608050700034004074a03074a603202d4170b0001040310806807005005230082084090750705585d00c0c0c1d40c05845600c0130487d070101252114508204600d042004c80554034405015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 603003947 1250 603002697 603002723
    0x150504090c0207081605010c0236060118120b1b211f09020a02120d0905010f1a0f420a0504030b15030f2109030601050607 54
    0xc011075050566050050300061401c000c400002c026289a071443d450b02c10f41c4661038507001814042c11803500901965800075142c0308540842d4641131360300548459005110035017024002c1481e812940280400c400140ba00b44080c2d03000034000554810b1640180103081e50707190325001d40b100801c0b117600107424502e042c00842901d006080e8640040d09441d050b43c4460030820401e2400a150480040c0031f1814022035881543d0384508503400c009005a40714a0200220b041c0b20b903034070080101c1100040d050705101005e5200d4040940554020019202d40d00d00420560344bd6841c0004803088030803a15042c0d20b0000554228003500400c800034045002e80d04121a01001c50788006000e21042c0c0900c50b0ba00920390344956441c5c1071034003071400c1c00301034000d084c0b40103500000c3c00039014800000c1d03007416407884400140800030700310743c0c418580340d06582e42c0705850043c2c12104402010302e010042c0e4220b040c0c2d404006c0c01405040d1980c02d140910950303030030000302602c0661410354 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 603005197 1250 603003947 603003959
    0x6080708100b040908070b090a0b01030c080d1e0e0103090b0a090515010302011b0f020306040b07110105010b0f2d0a080106110a03030509030f030108100c090f150504 73
    0x1294a00500c2014090401c40d060100407030100c600c0751100034092030420500c100007603890760403036040c82e50042c603881c0c803601c0d200b044510b0200c195100500304141748001205100c0911012803c581154084800c00748071300340101c038000d518031944078900b406031703ca0400d024025088492071701c01c1850b00081055440e140e071004204203071f82011800340d031880c40000788803003484444031030849030700c0320511941740d580000c100380300e4023404141d00f000c105a00c400708025915010300c101e400408442c458181030405101c521070664048021810500c00d1403040281809075a04951412507124104141c001501d03041c0d80c40821a452007a000812200011401ca0030003291b1007041000142c0b2206002d4016128842c10f8001d003060040950b0054511140006c003540b0741a03042c64003041d151120301c00ca41c60350080303035422501050080000315680d18001680368050845030b4090200c1103803460181c64110300c0f8010500c10001282d81404806001559603085407494640f451409940c0c02d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 603006447 1250 603005197 603005203
    0x30319051b160303020c01081521030304060b0901080114010504050912160b0a0603082205030d020303090c0108100306020f19020607080a0b1e130203010303080108070906030b07050d0608 82
    0x1000c81440b08085000910078154100880210720388203081280d07040c20a6140d0f5a40c45690554a91080c0300c070401c150800040c129003034080f071242108403620f1341402c1ca443c9001d4002042c640b8000c0140000000d5a000140507040c0c040d0452801034405908000620001d031800600082c418421032031507016281a103c01040e1591051813909034030012441e101540d4440030300140d461500f00701081c000f28000704200c800d113010285802c6c0380c1d1405044030710764030300d4a507220543c5409040700480c00309c1c1c2c02000551151105800f03031802c02607188019205824150359114032006003100500000303515500909184c42806045c600b0100d50f80642d50364500f003241100c0042e0802c00a118096400140c4640c101e810500f0600060113003038042441e401004641c4900380501d100200030340e0b1a28000c07034a060b03e00a80c255525a143d08014001202c02e10601006200317181001130950381d10720800050300d622116013041c40e207070007204840035040004064880d036070310000091003c03010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 603007697 1250 603006447 603006463
    0x4030c030b10060f050315030a0b01090e1009050a26030406020a0e150a050a0e040216150b09011223060117151b0415030911030319051b 60
    0x600c84081242c5080e1070200110181548682c0030302260010180c4182d40107410b9903440840b1461035803c1c1401040041d00d0003844550203008d00403c0c9001043c031248a421441c07012658900f1144175074005c43d17000003250164100544583c100c030b01380da4002144d034001d5011309441c8207500b60b5200150386001c5981d0384140c42c01c403030950380001e41c96000b42d000340c0c40c00c1c2009011158034400c0da600b81c0c00c0c85032522400c0a140104180052464851409035112020469010344119117400402c004641c0ea805001403d030745400078030141d910750100341c2c014a114150041c00140c01a440c0c080182941c0d488004c089542c1d44405150745841c00a030030201a55000f1140240819458032182401030341c07907455036204a03006101d8003580a140a0002a00481d0031311482849032021594025280107541000d481070817035414a0016550603048819500d000f16170710300000403601c042556904c030707a0b00740b0484503610000c1c0461003809000608440300000d14900800300040030302038107100003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 603008947 1250 603007697 603007703
    0x30b10170a11040c020c01080a0e061f0b040317030402060405030f06010f06020d051801111209100c0f0b06130903020601170102041a13030c03081e1606020f04030c03 73
    0x850000907052001020002c0c0d4080c1d0150f6003000000c500f40c00c001e4030398040c450030f103040c003000d10085403840c0e41941c000ca802d041c4a90980b9410b0420b000041002c400042e1101800c0407400c0006c40d111130076908450032030358000c3c00817210318600c06d0010380303540004000303980c045402e00c000107403600d040c0501c40b112420030014250f15070510389190080d480703d8005a003150310600e060040c00c0d030480f00720750100d60304c02001d21600c0710227070049030001c0310415031400c5801548400402c3c1e104800c00340440d1282155031401148980c0b0303044902181d11003014000b40c2004003244003080b0560469034011201400481da405c0810718210f0903240407481c1100180d00c1180108291a1440341c2c4006442d01103009500e414640707940341c02e140c292401c034841c4248001078840c0541c41c40580020003540d10000c4070019640da0708100f1425003141c00306500307441c40803805100c800c40c3c40040301d80c0792500c1c50f4400040c11103038440d0030094012031140400d441c0104004400710b042e02d0305032401584 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 603010197 1250 603008947 603008953
    0x70f0306020c0706050c0c0409020f150d0e06150d060902120d030501082b09030c170d0c0302030f09010c0611091305010608190f0e030904060b0f04030b1017 69
    0x10000b0852807401d02c00754002410080140040001d8000204218400300700c02c40700400c42003504e0002952490300080840c0e80b04072a00c1229a41004c194003819030a1110303103080001441d007441c0e09071542021a01c05c142141d02510f0340005242007100c60304201d00130b8400141c044486e030b02080c000e03100e800702e2403440e6014aa01e907000540c107025103409008083c000e0305a0301c001141c031a1010a25080c05500c041115402e2000c0610034075994005507000746591407003aa84204071160005540c4d500801030140005054480e8007900201011540c56030003903150405818030011503821080880d8100b203112401000811a14011a01828044001d903680d40d03080e0002c10181c0c2542500c0c2091050410004101c001c0e0080d003110703403086200020516040341c280012004241c14540040741610b04a00106411300010203405103500c26502007005030b40f070f40c0a4441e54010071300004c41c12a0300b0001400002c10003003819030807243c49980109036988882610641c1d4030944400328603a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 603011447 1250 603010197 603010207
    0xd09081305060f031611060a06030b0112030c0312060b1c05010e010e04060902011116080c030307081b010902030703060b0f090609041101020c0a0f030b0a0b011d03070f030602 77
    0x216a5100c10040a0480b00342d49041818250101580001058041441c1a41c01010100da0044484403111740f002801c0c0c81443c94184c0c0000c004004d140020b40c1c1644214001107100c90014062004003500f43c0c07198954088603036811a00903c0d400e410708070190b00c0b10400542940240c0141c40381e8134960100704000300440b180c4070308450059000095560f07944004004554074624455009900101c0116402500d0700040c2ca030034080c440003840c030b407081d002c001009141032260300c019107a90348155208810f4140c1055a28002c8070f00180c42d018082000303503061a540031010102144660020641c501c080d00040d080000d207a1050302e10a0700d544c03a1054a1821a03c0080d420300201c82d0340520341440340100c4c202660081c03004240c401c1024141040d03a0080025a43c200c00c000c0c0722011984d03c0c1e802c4800e0051640c44101c46403070040c400303d80f1285c41030203041100364040e03603283c1140c42a02460813000103000e16054060052907404118291041d040344080e500508001d6551 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 603012697 1250 603011447 603011467
    0xb15060a020f0d022d0102070c03140d020c130e070b0a1706040c080a02090a1a09010206101d040f060204090b010e01030b0102190c05060301240c050d030c050d0908 72
    0x3c00507184602c219004407001d2468018990344620708140c1d1941c0c8013103843c03410020f9500911511001824000c50b141000040182c041c0c075070060400c006040e00c00300e030f00d50682a43d45e6004d030181d10340d004010040042201417039900546201000c079088564242d80c80d80038242c2a4440e25001c2c000a80101c60320060414003100c1c1908600162070030070085003801801415814082d0000d0810b0381c0014400c1d40c0742e601d03007505a01402c00c0315a03541d202c28003081826102e07441404840d0243c0200f0001400440e1480302c68400c0751504003102100000c06041003142420040080b540b5815aa080001084042c4044e0029101c010400209451850005011100000704044c105810a001605942d9001c03c40c002c10381e100041c458030100c1036150168603645140c11041c0c000340080000142c034050001240c030900c8074a58212040c0c050014121484150500701030260390100e044044440c1c400d6020010110351490450300f019241038012080d03814400c07050302d0182e00031804c5000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 603013947 1250 603012697 603012703
    0x209090618031606050c0717040603060501080103080a030e12030906070908240703110f0306090c03010b2727010602011a04020901210f05060f010c0b15060a020f 71
    0x2401d0520000c41c00c00c840c03148040b440044000340140700507200c501142461242000740e5120b69480000f12240c280d0110802249400600c14940060f041c4200010700c1c5d405845900c0c140c070f0b0054180c0303184c50710b20201a405020110f00315200c9114000f1050f01075101d1b0005103004103401e001408407814031201c000c040300c00c0e03500700c03401d55084070880c000c0c0201e1031504a50a9921a075003041c0940d900340c03066004042104480c85601000075860000c0c00c0030703200071481007a04a0321041c90b500e034106000800c2c00700340202c0f0060070040020f500c2c456924a07405c0410103100700c0c0045580c1102c404030b1022181c0803c1c00c5004031000103090380c508543e000d820702501c424802000b0741200103405100340c0c854940c50900640c1c0c0002d000300182d00c00c40100c0b1a031001c04500c1c4655400d0008480000e103424200c40f00000d151801117091494944c2d440480780605941f01a458040d27615405d01500001d080384400f050b40c03a0b034160030f58075440064440680542c014007102c121004000f41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 603015197 1250 603013947 603013981
    0x40305031903050c1912060b0915190c023f03131701020d0606020d11030708120a0603172502030d051b03181201060b1e0702090906 58
    0x1c249801c0900308141803442c0d100351000d022480b00e101c20140004c0b00c0a5801814400014640794249100446c40380c1945e0008c0400440a071111003e0414110780141c1a01030140c10020766110140b061034400d103c0d0466900840c00104801c0c03050200464044c120202520004840441c0c500e00c0c0d100300c0741c00042c4101c1e0207003150240d49880021420343c102065980584007400540e500150742340442503064403030349007c980041005035200c41006c0e40c1d410010700c07480c00140490180c207010034004400d1315100381d0320240050038000351111025030060014801c55441c2d5440d00b0001c00702d12000602e801c40d0000d244803503501e021070310242d00303203200c0c26144030600c52210072010010b8400056814030042e4503e0803a840d4a01c600003c041000c5e8404812101e1001044004000560032068088203004540b00c030114014840b210b4240c0f4041c2c80f680c01c0c848001c0c0701e5003203d0a880494074203940c043c08075851800c4640d50004003161020b5880007500d41c070600401c01080b02a10b074081e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 603016447 1250 603015197 603015247
    0xf05131403010f14060d060b0603040b04020310020a02070512160b030106180503060406020a020708010c0519110a060f0906050a0b0316150c03090803030703090b13030c0f1704030503 80
    0x4024418802c202d1391001c0c0000e440d15001c0d51030700102105014059000088890006000c90307603031b00b09420602c445003000c4c0c030180d10a0042034541d0940800b41d100302d90045200d034000d040d116242c14100702d0140b141031000500d500800c03c0e441150200100c2d00405842181c94845d200c0d41090002019071082040e031003079050040c03c091001d551300140f0581d1250740304c0409641d4005800081341001103960110a4940c01c1c01c214194240e00305014042c044900c0b5010700c4014034100d4111141000c454620f07955403c49203c081c0840c1460300942084282c40300d02150300c2841c1d81d070380c10880340200c401c01c2c0c0642e41c45840002c6031905000015680c00d00141c600e403000d0500b001070360944000c4032080280210854050105400f07204107400403c40303a01a00d80341d05c0c2503913010b005414035001c1161005130b80700c00602104401004603041c44c0c0c01da0703500404a00c0340d542d540a0301c16001c1042d242c0d00319543d0b481050800039801400a50711440c041c0d529401055910009540004030346 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 603017697 1250 603016447 603016451
    0xd1d0303040e150d0209011206051302240415030509070f031a09010b0a03080304021915031e0903120506030703030804020f131b2604030f05131403010f 67
    0x10440c9100c941e80b482e801010300484202c543c03a001c000207001c0440134000075005001240000361300340c2d0404200310094020304050040703a03030b04503020101380c00400000358800030514100d05800304516a94585140d007680c06464103444038005000080b200d58100b0000741c58504014610a040c84000010f11524031400b04031400d607513500c010090100206010b103134181c40080c032100008d4205d140340c0c20300509080003450301c0e820202601d40c0215000d138004c01044105104212046a03182e00302da558411081ca104681c03441100900418204801095074044000c00448160311402c000c1a1094680808003824025914284c54000781708912035042000100007013504007071001e40c4582d040714440390305403c09001078622514100112981c3d4032341001c000d020880c81c01045c0c4104c4c0c254413040210441b864106c03d1b05a0060046490382100001142c0045c0c010035000d4504891410810b0419a4080c1810198069588a000300c05250402c0c0a121304081c400d003050b4107106a02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 603018947 1250 603017697 603017699
    0x90914150609040c030b0f0a0b0f0a0501050d020403061d210d0209010302070b0c21010b0d09050f031908010b070210081b070807060e030304050606100507050d1d030304 74
    0x40100000051040303004030102d0002908004507001c007038001c0e41c0d0104c2d407034145040c144800c8200003021940d0314007042c83c001c1100c1d99031420b810000350f030140061006110030b0400004454075002003481402c1603809000200000704140a880190000343e918800400080101c803854440165007918160410030442c0800c14000c0003180c9000d40c80c04005a696046200120020712074110068007074684d50040c41480d07808030005004002080c9603a2850303058900350104014030078804c2c04a0b00708100802c06080307006030041d0036060300a07400e07a070740d4805107040c3e28103690203c1c03082e0554180c0303a42243c42c01d030f401045080c09890724090441c10603076154041150380c02c0d50b94881060114600005011010b80d144040c13800701d05458080c0c4800b8280b51007400c903000f141c0100c51180c104507040d4040c1c200002a00d200316080310052a0603260300050009106103042c0400400c4420001580415410404061440050383c1e41205240a0500071240a1a001c1e800380c031903041008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 603020197 1250 603018947 603018973
    0xb090c0a0303021c0512090601030201110f03070b150d061514010c03080c0d06061707020a0c0320040207030c060b090105010522090c05030a0609020708071218090914 73
    0x8290450058004213640c0c07680c02000c1c240c136203003d0920b200d80c0b0514802d0400940c2c540c04540c1078101c0e4401e8a0340d071403a40044603c0d9446602050151075654803d000850218a80400e000c1c0c014240440d0007904801503c0490007070110700c04161001138031113084d41000e810729102140141a1480980c04c08005100001c14440c0c80c020042c0070003107010082418000d9074402c44004a09941d420480c5542c0d07910003403c00003000c031168a6243d44000000c160a0010500c0e441965104881d40c2049055640302140819000c4804001544110680c8041d48542c8000c042042c080e45a824030500300740b4003441030f03568003412203001d105400010415641c0000564801c501d40c511031203010318500c05410010626980191109420f041c04502c3e166017000040d030251005840a0042d15101d014410591040100003810030404010380808a040c2c0800c00c1c03651041460b000b074180e4092001c541250100d030700850350086e1703501c608c04108007502461410240d0304a000d080f19404500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 603021447 1250 603020197 603020203
    0xa0c0b010914040f031205090718020c120a02070513090506090c03030a0f1809140f010503072d0e07020c030a02030d0c1e06050106090803090d02040209010e0303070b090c0a030302 79
    0x140000741501300c140020020180100d03442d032080f0042c0c0504100500e41400716580e282e0341446191360600c2e09811407682d0202c02d008a6621014080c010300b811a0a4031070162680e12013100b82045000e24940481c0c45d0703948005000e41d121545c1c00c042110310450500a0030301c00d014015504aa000c5581d01400d6103005c000d40c1e480a100c3c1c2000b118034000e001d02617071582d40400c0c80201d010030080001c104139000d58050280c012100d4240c042d1661400c0c0b031040c0402c428000e403a4503a000c01005c104200d05541610304e40e8003041e42030f9072421100c0c008140880c035960088140400414204981640e04100303400340340101700c009000540e807030740110f911602c10007210b40030802e6021a03031040c03240c03119003d40c02503202c1d03000c001c0314260350030b084005006c00c1c0900d0000541c00100011350410000035516207080050514132003082170744c00c03c0000d6106000c40380c18005045483e0040d5542440030300901809844400c40c00e203895040300341003100e01440306100e034001940500c0840d07400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 603022697 1250 603021447 603021451
    0x70c050108091006030b0f10030b040807030905030a03030c0e0402070b18030f0703020c0103150303051b010f1415060f04061d12010e10020f1213020301020a0c0b010914 74
    0xa0030804241d45415140e2402c2240d00d01ca190b00b41400e00702c000080101406c1c00e0b91048081c0b54520340c0366140d20300040380d081414407000e003044101401080215404000074194184a03003403440c1c440b40d852002c0380c20076002c0c00e401d40207c0c0c1e0300e070714080103190890a580f0907003004440861500506a540240307124004d0101003000500e1010081080002c000b06d40080003004d078440c0c1c458626140083d51640c544000c0ca000a0601548071640361200440c0b00940354191120f80c10b18080c01407001d854110815004002d6481301d41085d81110340380302d100002d811a900c0c0b00058684054505512803207615241d00800341002940010882d41d016581174a4032031500312100301c4014254891034100040c159803281071029001040b800540c410784040b6544819101035400044c0329100301d0244204140f102c140030803c48030880c1e480000d06521070304007804004e402030103030042801c90b041814100040b40940c6400300034040c0c584101c078010100b0507003e01c01d0902041c985c080840c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 603023947 1250 603022697 603022699
    0xe010516030e031b1c050124091401030b0403030504030e15070302010b060403021005070515010b0703030f1e0c02070806040605060a150e040b0d0b0a02041814010e0705070503041e0b070c05 83
    0x1700421400030860301f90460044540000350741c000600030521422040e503681d10518062030310b8000d00402050002c00c1407412170790440280724075a1350310f840070b44c0a020000c01c203e00700300e03414000d0fa944ea6504214603040707480032141682c070754895207000f80c01c4521010f02144915420301c410070040c0c1d00c2882c840c1c80c8040520741a910781c881881c00303904e80480340d011440c2c0d02128000110b00c2240d500f01805403540a50b8092060590154480c411103050306080100d049000500001500d07181d006540e603a0941c9c13040312681c4e5980d143d041e0628105840494920780c0361418441a4509104c0b8030000d0080312501003481d4001d010058001d1041e0b80503207000d583c6501c01c0c0d800507030f10b8405900c0a19001100b401180c6403030118003009504c240900c0400c00500075901d01c420070141300f04080d50700d081300c00800d00d9007800c1d4032905229000f840785007000001c1285c01c2c0040e07000d002800040c031009041a90002c05041c4050107600e603030700034281c0740a0901c80e0b00301059411440f207088402c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 603025197 1250 603023947 603023989
    0xa0e0103050919080c030313020a141f020703020301090f050105282715050112200301150303080412080903090f030c0d080702180f070e010516030e031b 67
    0x5031031a080006000307040300c0c88880c6c0030100c200300c0105289404c9a1216108841400c0d1b03064444080c0d01e0441d00d00300c00c060b0801e405900e94904000240803600054103140111411641d41307600003070030358000d078000f110003d814248130800c01800f4050740d80c011401c40c05040300d65050b078a9241c060140c020070f18440944a1901407020203002c149249498070382d0700c0ca03528041c09800e0071142101610000080c080c6010000260046003181941603540d01c840010170341e00b40714681049d03407882400120ba055689d003468158458031810000001c40c42910b6650503440c060034030f1400401b000e01c103c4184810081000050040403007124103841d82101c9000400c98440003080c60312031b1100b20039070040500fa107607409100c4040090449103208460709802040c01031095001190103039000c410702200708010860290254038050598201854514104544100840d4404080c01002e4001c40e812140d542c803141402c1c8070304405c202d0302040e210b080d422554041000c10030010b8809640321 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 603026447 1250 603025197 603025243
    0xa14091504091401150603050c0405010c02042a08070c020f2103041412030c060105090c090a140f01032d060f09020301170c0607031b15020a0e01030509 67
    0xa030701c0e40d2211111640252a0780c00d08400b103034199000f4440c150320744955070241500004c2c000d100f406903521451503144942e0405e072400c8010f603100c4140c24404ca0340b0540365151104410300d02030810441040d00a0403108082c000c00001e8221b0501802880c200403881c459207000d41c0f030b98000d0701402041500c0c003a008a0303500b0440a41080184d1904a490200003000681c031401c2008510306094101c0c0d03803030f009009098641c0d940317100e0385a140d6041d40101004200d945803410740c1e154000040440d5a01e441c40250029000034955001000b441404070b014080710b04046060f004030f0902820100000210030f40d240182c500c1d030dd40f070345890459141b140b4400c94110f0700400000d0405803c0b1024030b83c1c03140070181c0a904240240300f8030f050070712442061800005084880d8080280c045442c0c9862078a0444580e02e88c01d81d46100e24282200100002e8015074000d01fa1070158000141ca407401401c0042c6412040c40c10281014141400e004014001150b00d460440c41d2201c41c070340301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 603027697 1250 603026447 603026449
    0xb030a020c0d031a030309091b071401020403060f02120402060913090c03030e060f04090b0a03020907021e030705030414120609060907170c010f12090305090a140915 73
    0x40e105001059500b40182c9000710341141c1c05400010300a2010041c0822000d1903034141656802100222076100a455001c41e413601c5951b90340151007001d1410441c545007071903ca8000e081040030000da01c60b90300080030018000780d481558200090b1004c1545000315403031641c03003150000b500c080e208060008102c581035891084c80c00310b41860700350030721052040341404040840a403000b03501244a40c0f59002d001d02c7c000085500d15030310800014141800d005000c0c00a103a59101507030801c0c1c8040c00400540e0341c5040c2148256042c0d1300510105003c0c20044100340206502003019074400d00c03460000660100c140c0e4243c5082200e01e105112441c40011003d000c07458208030140950b00500c5101000864a10311847c8040203c07143c242d51921002141d605a111030540b0b0b0304001124000756100c0d20301c50111154525015800b003281c8030304181200c403080012004101c00040012003030802800d804010000c01c844035010304c59050110f60a035100030803182480021031019005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 603028947 1250 603027697 603027701
    0x50a0620010b120105010819020a1505090402030c0d060602070b0711150415020d05030f0708090708030c010c17040807080d2012130203120705010f090501021b060403090b030a 77
    0xb19103401400f0000a00b0b044aa2034002d19003030050070100c1c01440d81c142c0c46240c071841f0008803194082c01b0100450f10b48015210305c442140c0c6003004001c0200070101043d61180040c6005080c485282c3c2e98881b00701113810206c40380c81c0d02c41c00c255000050100009040b00b015607210540000b92010410750000001d41c110301c004104107080c242c04036020404000202c1107000c0001c0d160221214603000d1a41030700c85000407a404000200780c1e40000303842911402000707802440d20300450b01600d803542480c03030031500180d800c2e0706581e664088001c856135000e016024010581c07410b1a0b0300303050689940c2c003684140300028140810000301003d0003001548076101c00250786201c1d00795820450305104860b80605060907201d03034254041280414190026006580c1c0100180190201c80c007209089402421090710a5584c0b50380d1b81c1000f07c110300400c28804d103ea00010f03591414245d9036080c1480759100c2812540c0030004110004c0d4100c0050000d86100038400ca0310f0f90780701c54038540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 603030197 1250 603028947 603028961
    0x615030a06020d06030209010b12060103180b042109030c0b031806040b041118061005070501050903041d010602061906030f230d050f090414040c0f050a062001 70
    0x1c0a440080c422032291000d502c010305991088543e88010390307a606074002d083c00f807041c0781041c1e90000404600a0f40c040d5111048028020000d0f02d08424643c88007606040b0031501510b039821060400c0560b0034224404600c404928105140210f00395200e207494603895009004034280e000010130311040c510303442081400c5603441140c0c1c0c54942441e0001420900343c40c112452248034035100c030a4a0b10800e0340035044c92003030385079445a658004121002e040100140d050020070042800826800e02409110701650002550380358030700050248030b0141c201140c14060503010041c07220a5011078426040180740910000c00c07060058108010319695000500001c040c1c2c4246d030820144454544101c2c01c3d130300d00501e04055814025032140e051070101e600207203041143e01c510342e4460001e06003000b40640006400c08440c92040a1010251400e4803482c811320300800c216070507402c2001c0a81800d940812000d45099401b420701256060000450030044030510704040f82540400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 603031447 1250 603030197 603030203
    0x50903040b0f04090b120c0d03050f0403052406090c03040c090c0c060e16030b09160b12100302060306010c1b06050901080604020a090b0d020f03070503011401020d020615030a 77
    0x240d80b16248031034440d00342e00c2803080d08201303410207240c1041031605010315030460100f1406064401025010800c4500c00d44100b201402402d002020032980c411b00504081d6209000608d064198032840ca1840c1d9100100150003081410401699448900640c2c0c0c00003400503100362a071301e6500d088840d060440d0000003ea81c58280181241a4082805084103000c0c0c4003c10001c2403a808103a00c0c0e440f94072941007085040f42003000005d442d400203d0380300365004142c61000c0c008184203600d41c0340907400000600b902180e0b4440100702c0c041c0e581e4015101602c52490356141da40030400d1400000c2c0783c0c6040c40300d04003060307090007610301031980840d601c4900c034290ba689808018115030001da00310b90005501400181441c10701d4401ca82c41411907031619150039150664810107580040c94030400b0079004c1c010040125900400f4500034500c84e1aa1912503040000c85480745030280005411944060f0403003482030740104180307400c04042105a0241103802020a1924000f00c41c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 603032697 1250 603031447 603031469
    0xb06031611030d021204030f09060f0509031f09150227040b0d05030a020d08010806011203050d02041805060f010c2d050114181c0c020d060b0a050d030504030605090304 74
    0x9442c01080110172580304520944548105018021045030070031a40d0040f80c010420724403016110034020390141c003607144000c00302d5030b41e00c603d55414418030289103c407911107911501038104101d0a181e5150420302c6111045003040036030b00f9850b0b01c111120300261034440322110f26110a032a680c004074a11040a071000054030031600d8500d40c0c030350051030590018040e020007507404510484460381207031014001850240d09140700541c21810360302084092040c02c200090803109640003520003031606c4901c1140c0091514401c2080e41e800030203041c490100041c48049036a04032880e008055000b400010a41c000c030001000b0102c0181c4041c040740000f12162010030105410001090340d2a803010f0a04c0c3d240c24940c0e10308030300d82c848500355a810801c0f421211035091211140d030109640b921491415481d00841c080e484140c206072000703130700d0b00500354450402042200040209507030044e44240c564400800501490000030480c84e00d903c04144502003c0003660050140e405031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 603033947 1250 603032697 603032707
    0xa02060403121112061f020a0b07230310050f0310090203011e020912010504021005180a030f0302060105100e06030c09181014130216140c01030b06031611030d02 71
    0x110b0603140800722003051180b40c0c0c1020001c0c44807981082d4010340ca081f41c009211408403661540c0788280014020000c00000400c2e20514208560403094410406045a5960b0615070340103801800542c10680c0500c42c03501c0c01103070a40300003800040ba108500d0700083c1042c4035100003400b6001e00c40a443c850103e480d45690b032000258000d0404040880301d0000d04680c804da128240d800c100c8002e035104042004240055000700001d0510007803040c048404809681e0028680b600d6541094039010f040c4207a140030140c0400c401c42c0507200c01c0b1003c0100c12009880207000242103035001d40940c60110108807005d4840e4169074080400916901ca02e0400074010a942c030404c075112108016070b400c001a0030028003200d064003850140100c408404501c031410041c2d88070240242441c002914400c1c00300340c2040040c5c000e0003100c4042c0511240302d10005064600e14001c55201e0001002844050500c0d551401408045401d0070340026034010041c0b810741c080c0c01d4004140c1400060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 603035197 1250 603033947 603033967
    0xe070e042a1809110a0804031b030c0b07090f0b07022202090a0b0702010e0d050c0a1e06020102160b0402030316061b020604150b030c0409060e01110a020604031211 72
    0x2142c40c20182c2c444489410840c0c2d101004000c1c2c0350102d0040440c07010402074428500d1080641030b81c41406414921290b12504440004804c10200b058000072200d140c040100510100e4050b0402d02914001141900340f04503800c10400602ca0258855400280764045448100ea0b42d80703090f011440c1e0610514198500002940c000c0303140500c10a028000844d8880b000420344051903010303500d9140040c98101400b55181030103100340c9842c89100442202c41c0d035605490009013084801b080307044036a00d0520341150185401070b07800e40e4014001d500010100e550908003041c0c00c00c1058000340c0b1540003181c114800d615000e40400d00c2003c80b401440b0844d0800c0c0c41000351166040280c2051007000c85e25903005450080980c40080e668522580d40b60300014180300c0d0003829030b400c0142e41c1d00003800b255560f80c0c0c112440d81d140c60b80429540f81c2803041e4883d0f042c00401c424500511200025143d1100500080078850003800350354980700b8a90040c40d071406540304596030340a1000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 603036447 1250 603035197 603035207
    0x3010302010f110d050904290a0504200a090806070203070302060601030b0d0f0501020c150105040501050603010f061209080a0c0c1a070308090a02100f090e070e042a 73
    0x40816404515560321615240344180456039840407031001030000416500002c888681c0009280355009440303000b60006030700f40b43d104503061014002184a007001010622800038046e078400c51142c0d181c540a0b00c0b10307002014808034488020600300396642081541038130f032135000f034204040600c82c00040103441500000181812402502260525a1001d0044003510a052106601300c50200e0020000844013604d40813250310890025003403110320211503140500010b84140f840520703500400850a1502c9240d0240905446691a42d0b0600707102201c500c00c503100d0389080001d01d85080c600700e600c1d94814044982d01010040d652004044003d10885400300c080d1000c2c0b58003100060141c4c8403090056466040b403010500b0075200383c030141c5400000400d4003289008031000180160ba03500d2072107410b004a5241c0100c41301d244040103000407616080820b03107250b0b02c000d001c0c1d070603008601c41e810120100c4021500d000c0d071484118028031005240903c900b400000034a100d0b03085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 603037697 1250 603036447 603036449
    0xd14070908061b0405190b1818010506070f0c030b180c091006050c070509250f17060d210f03150b160813061d15131a0301 54
    0x1070864456440300c507a4040032814500000850140800c4200040c0c20014944104101c0041841012542e01e094140e80c540c040350350701da01070302d041d28040d236989404008003184c8280442010341c10740c140408602079108034400a000a091a02500f081044040d010300245501008204850608501d00040325031916011004c41c0640f080f15582070400442407441441d402a121032803601c1d10100780c43d035a0051660300014003408201107002d403078040d04c150144503400d030000341410030312030703c240040e05c140354410421882680d8101c0c910303032156200c01950718a20a07030740c1d030307440311301c001340b01e4070344c1040010242404c1a0040904038bc003408403038941825902d856035071070850b02d0210112500002071340d00b2020780b40d000b0300c400c00d0043d001c0c00c118a822229004000b10640383c2c03080c1c0e074201181440314400b00000910100750b100407405034928405001d8800d9070b4150700007030516100c0010500c0c804c0e1000c142140120700c01c1240c0e00081008054098581240c1ca041ca0100c7e402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 603038947 1250 603037697 603037709
    0x903060a181a06011d0906190503030f040602120a121a030f010b0301180c0308180a0f0f050d0213050405010b06040f050f0a0815090313062319050d140709 68
    0x34548499007104218041c1c03142d0349800501d070901b699200030800c000d08096204c0c00e07103910418038010986840c104003c1000300c3c00b44400c9500d0300c2c0b404e00c0c003d103801c944041004106405200f058501038001a030cc452641d8400c42c0490318256162603011400441003009616104401204091000c10742c0500c106100c10350080c001a20003402401490142100052403100114004c002081241c0d01402d40c0240460031040d0038007200d40003415040080d00014031400d81650f0403c1000c1104203000003c107000c0e030b1515000d031129000540c0104020051040c225200c500080801c242035101020880000742616111510303113443d0808201c13140100c0303009202c584119a0149444040717075003140c215000600200c101c01c03800c0c680b07010b0040c160a01d40c0c03209120420808503404010800b400d05503603552070f51a003030455403003518040c82d030059022008004652203d242c0325a0180301c2c4025082060791040c410500000801142c0c500e00c0c190003030703803060141c05c0e0b0b4003010f510100e40d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 603040197 1250 603038947 603038957
    0x22060504110f0109050303090d0f0503030708181f05040f06022208010e0601030210180b0d0f06080340030b0901051302131b0f020709020903060a181a0601 68
    0x100001550380c0100c40c0a43c2e41d140d0700501008202c3e2402421480840784126440d00c0ae42840d0b0b40e8052454006070340d01c0d000314091408004502190f11030728140c80c0c1040300108032550140c84203904850491210f04004e60310b40c00001c0078849600381c0144c0e0254400c2c421036640201d400094000e864580d20340511000700000080c0b003074030501854500301004070151075564610360070480703442c04081104d02445151078030030381d0f202c080c6c0341080c0050007100c0c41d05648d1981c0c000c0800403030310342250303008240d480c000003030141c4070001095460302c00c0300340110f04510030211025001040103030030080c0c1c82c0b0a4180074060702881c200b03c3c0011139214045a000c60345940c10900c0c03c0c1c40c0101ca000044011403d0010054a00200303503000300c81c112180011071000c240c007420419007080c00440041014080361002c100d82c1008008020002000d086040c000d042c0000307a11503101402141800342c903030030086040d0204210b03203109030364805171108607054000280d440038602100d125001c64 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 603041447 1250 603040197 603040219
    0x7050c2a1806040207020d0602030a0606090b120106200a06060e070815010305130503070501060510030903020c0603070509060301061206140315100f08060a11122206050411 76
    0x10a14611540d0081c0210000041d2036552405010080d004003005a03030212440000ca00462110b00c010350142c881501d022800c503080c950f026140d60f0181d0301030b15011400700481210390003000c003600e040d20114074102180c5110181d41c2e440c850071042e1101b800d4080c8080b807208108259000700c040300c2ca00c10311034403180c0d41c10f00180c0700850116480051030500071301d2803860358429484554403c800350701000200800d500c82925580245000b1a8141e6443d101840207180c548444980c1c04510f2070240554141030703900075198510640c03528015100403010a05840c0100d06135624010080c02d0382da00e9607510100105203903248003031020014a00348000c66010f0380860365003a14107000d0001c01c0040c10003c0f0782219414002c0c40c00100903800480402c003460100403000042c50400020086828a100030b101102ca60940019460208001e10800514400045a0f108000040304544651031141030070000960341c200404041c68502003004004507001e078400b140e6010390302032030f201d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 603042697 1250 603041447 603041449
    0x909060f0e0f040224041403031c050408070f05060601030e0309060a0e06090405070513090b0604032405090d080903040303020a0b070c050d05180405011a07081902060f0709031a07050c2a 82
    0x183c490b0401e03943c0ac40110342020300c54080150003c6401a206203540740c900280b944039080b5290359010110303415080708044c060b00303607414003e440f40412030f0f40180d480d041917440010860301c00d141d1900140480100c0034070340d598901017a00d16160001c0e0003032000c0d1410b42001040ba0340418840307085030b80ca207000490b985c045849840044032000d0425883c05040d42c50300141d5100304513a56803501d580b8812001c150f00740340900c0e07020301e202c2401042c19a02103540903000d820020310f142a55402804100042640081c0c07040740c0c1c5030801c5128141d901c4880c030031036a0762201803001c0e01900c241c200440131644d2240c002c2501d000100120221021910b082005907242840390002115a00c100407402540c40001070007060b01c00c00034149000c149a40031405010b407130220b180503810900c108140b41c3c9105003440c0d0f2001c010300e4040e41d054115500c100c2c01039072400982100116400004080c40c1c010012600010440d42c1100c44001c4081d40c07074058030351503142c00690030005034440105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 603043947 1250 603042697 603042703
    0x40512070812131202010203090c0d15020f0706090308060a0b032403030d0501090903080606160609020f1c03030f0b0d020d0c05100909060f0e0f040224041403 70
    0x400350300c0200740745030030758592042c994014040c1c0a00080300980c00d00c07000003402d0454402e038100c025000907880380b91401303803035003000125581ca030b000b948045001000030328130345450300c0046000320005131a40310440c8481641d0058410040040b454550f154090541140000307100d44002c40d403400b1580d89520600410b03010030348070b00c0c1080c074125030051100028882901020301e00541181e04080840c001c1200f44c88080c2c0c0600c0b401c55484001c0710a0581c04061950300c80d1083c0c9286140c20024100216440d51101010348030b0741d82d4204603411513842001132414584007e100017a00b50501217441403d408400c41100440d00c2d0400e4800c0c20310b9907000d2040750510013085241030100b15020300500c01d4803282c00300c9091540c038101245aa50f8052000c842e0061659058410f1741089680d50031140c05030408200d82c000440100100e60301c114006500005504414140fa00c4901c0841c02c0307602e200762000a641d1000500c082580d0a80c800341c003c4441400c06003001d50040f10030b05031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 603045197 1250 603043947 603043957
    0x6050a200304141009060204090b030129060405060307020c010e03010b10050310090c18140d02190510180e0c160c05040912030c03050609160306031a040512 69
    0x1014003400058045003400b8a9001080b201c2415140c1d002001001d08007100c1800200701e46c0b107503002c80c051105000311710400d90070349410b5000b0040302c0142c0c4000410f54034045840d021440c407600951a59440d41c0c401c2c1d90040c103000d00003c2e141d050a000c0a500c0c0c1529452150004604020518440c9814011901c02880c058008101d5040c880340441b80c550004002c040e41d803071800e00028400020303105203103904a00f035135004c8010003140c0c407808200440c1d901103080203040e0015400e46d079803452900100164126082552114860140d800c91240c0d07502440c0d00c000440412075403650441380030b5800e01031030300c00c600b06152100e082010703004003900c0908103804207015001280c20012503402c0f03124050000f811560b0f0342c0d40b0000b000e441c1e0081c0304690422190030740c580401c0d018000c2c1810805a0304081c015841d02c600403030b0310b07041d00030081c082500f1111140c1180602a41c0b00300041c0da001451a1078440d03c0d006c428101160075030f0100e035280301d10210103203059504000c0e91 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 603046447 1250 603045197 603045251
    0xf0a06050a05100201140403020d02160621140702070518040503090d0213060b070317070f03200d06050a17060f061f0f02010b0a06050909040303020f040306050a 71
    0x309500e040000f4003030360f0800189020300b990f50303c403030304070480200300800b0740300300e04c0380d4010420250500402810170b040503d050004684604003804016081400f0341026440c44580c2d201e002100301c0d0600207806102c00100100401c1800d01080c26404202d406c06c2e01d80654181c2e2006018a048a182c1d1200701e5001e0043d0f041400743c15110f00d07106504035038a9000400c80ca0301d0040a6800104450440d030007000304d98000220701003011341104440c501044040b00889aa10b02018042c200d90070b031803010b10416a032b03042c4151a0601030240c10b4034072541118031980307543c109680d507001020301d0b0103440d1182400440000f4600c0038011201e4030b02040202801580c0c580440070002070602504055110b01d00c0320b100c110348410441b2030403407031106a0324500c131140c440c1c2c4003a0850362440341072130041c00d80480a226941e00681142c44000080d00c03009400e0b5524101103009005001100c10900b000007400018000c10740c01250084502180400c01100c0155050050b42c2c8540c04203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 603047697 1250 603046447 603046459
    0x70b010312030902090705030603010f09020117040212100b030708030a050a0c0606050d050a02090601031a060d0f050408130f06090513060b1c051024021011030f0a0605 74
    0x610008407069651a42600c0390705010030088942d41c009825800110350f0761000070030100801080385001d00610401d12a01c1404125840310b5400007404080c8a4604040101c0700a020404540b100480d4010940d000d500346c600b403d000c24900c0024284a2354954800d01c0f9114012a0080c004402c440041560340c031014030701a9400e10035601311100443c01d0360125074601001a541d26001e0070854a40d00c00e0f40070b480041510310406c207080314003030540345c1058504041c082012492030700b040380000048a40c40d494004002204001e801c0c0030310170aa2950030007041c0b0003000f0125001d080a000c4112451910315214000841150301ca403040d000010f481c000304015504107064450002149001c001c64501c0c0c40350042050780e48821001208488104207001c0780360352f6482102d070088060003400c1c07441c601c0c0c00c81514209002d45c075111a0300d41d241c04d0700c29445000304000d2050030341c25941030108841000600100e90030450707182074210968000030300c000c3e02500c2000c0075118000e01e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 603048947 1250 603047697 603047699
    0xc0504050c0a0f030209030316061506090504110409111b1b040f090c030b0912090619020f0604061505010f021c17010f0503010b12060f061f090f0b070b01 68
    0x4444140c801000003003130503800c0001004640b400c1c0014981c070315928600001c00211440c01c4d404444e0150502100214041420311400394023a2400c41150b10440d8049401001c00c280140c5600c19036010b17403411840c001d02d41701606004005419035107016088040c00c2d04034070600d95110704484044081e020706007100c080807440c040c1e0080c2e000013151080000e0f0000709680c4c4004124454005039107406022042180e5000e003004201c1d110517601d4862030500341194042103c500400f1107018004008143c6501494802c010b11a44d4074801c00072142c043c245400d000004201b0380c2d5181401062240b4041240c0d40030300c501d44101c4000d64010b0600180d8100f4201800202c0b0000100300100d0b0910301130036a46081c2c03550702800786000e5500c0e503103191008240c00c41d444d0311040d50060001c84942c00d03414001140341070b40b00140c00e14002c025a00c544c0064400801030b00d8070280402d100c0c4116440a40c065043d0301907488080c0c3d000c0307400351500080d1415000f40d080c000c111148540c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 603050197 1250 603048947 603048967
    0x1140f07320408100f0c0201021305090c0c030301121a0106021933050105041503080702030a080d0b03060f010503030714010204050604240c0f0b040311010f06030c0504050c 76
    0x10158804841d500116810030b41c40368811420310b840e54244c1c0d030403651650000000a54544104100302e01c050008518110900c6c40d5603070b8500c42031161510480c1420001051101a1001c880e4407003558000c2d20781c0ea41c0c69400921320a5824001641c042602c441e589a0411a544010381a03440760b030000e06101c0c003402c4899001c030a404504441c1c6100360102070202c204882c07a0f100356100074501c00c2c80c2c0342445900000840d00d05910503480345007098a0107180004201001059a030080c441550368540c0f40080ba1030141f69401c02412020000703148480c0c14038a621865050008806642031911502246901c14500b0b000e5550705800401c81c2d9000038586030304450460b500c1100260902e540e5100050042d0003d40c0040f110300c600340c80e581241c88a80c0340f07440c400009400c1c82055003585c3c0c1c8852802016000008040845c3d40c400f00701454051051410f1150501c2c000780109024000002c018140a02c011504c181c907001012440349094010719120311003041401e810290703050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 603051447 1250 603050197 603050267
    0x301060c06021b1605130b1c050c061c0b2e09050306070302070320070909030215010f1404111801091d07080108160501030f0e01140f07 60
    0x3c1c0c0c42108400c85030850b100c0c0302c0060000f000b20741c200e000c102c4241ca28003024004409040070f51140306d146884022462035980d15036508691224aa03440c0c0c05ea8150300c0c1071468001d011044d150b0020021401c128000354035900c503095058402002d000008a09060003502d0f081d202e080c040c0030b44210075190000c0141203c0040560341c61904100340c40c2d41d44003007070508205458140010340c0014a003002d05030010070b031032015403402442405510703000a401c0d8890203030780950071009440703908010505200304079040040800d8110f1100c256900c070340c107141524a078401c043c904540f07141008414a030500c41c07d00603c440da20130318686615051405a412503840328a8188103041c1c401182c0075403000d100d8080c0c4400304030803034211700341a038000d0b299940503442075030345901940045020b040604410350484a00b800d011604a00030256070003d080440d0b07050140750721304071000900c09002d016103030080c01880c0200580743c556420456008600c243c2001c208407003072040044402082c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 603052697 1250 603051447 603051457
    0xd030209030c04090503030708090a03210605060c0d0e0102031806030601200c04110f0a032f1207030603080315150a17101508040510180c0b0301060c0602 68
    0xd0590311601800c500040c226000140c00750f17210b51004c801c002009800551660f081003a4030010700c48050760341d07002002e0b1a081c6070011491170604948c1000001517810a03009400e00902031621000c2038904a56603540c2002c5810020f03895803261903680d4001300440312010324003c66854050b41d07140601c01d4561000d07001c0d504018910030710701900100c14903100300d51454000a0042050030b0410001924031207510f41d48143d008105002c142c2e00c1e507200b115103031601400d011500400b42d441c107080f4200300d102000380c564154922550402000001420206400101040c580e00e694030120101c80003408010f04401042000c1485228130321051054410020180d071426558880b01c401d407a00101c1112010401308d4040348400d80301001c000d58000d200c0008805014500481c403000786620080800900c148031002c201444010300000000221000090004003c00c02c481c25840c10380400580e03080c106203130040f580211010440b0b0480d002c1d565103034020704003600c03100700079801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 603053947 1250 603052697 603052699
    0x708010b180d0204020301060c1202030a081909120504090f05010503250308040902040302030606090702030a03180c030308010608073207050106030b0a0e0102043b01080105010302100e030d030209 86
    0x2c403000e44005a555000441c080c0001e0341d0341d18500102460b0583c0d26005d000100b1083d500f061240c0e005090f40010300a80c0560b107254100000f5241805100051040c41400f614040002001c1410b680d00400100100c90007000200005105d0140c0d940450360f082c010b050b49034000da04015054560040013801030900400050080c03680c1c2c2c0c4e6006500d500a0b0703c06041560003180400035440e090010a0740401d0649500d042803500c090000d450b4805c99100409040c0d80f500311118515915800380c103507a92201e02d0750302440e16410082c103072460900c914400510548002003000e445490800a24450a114928415806000700402513942c5010408141c402e0106401140003402004c005501440108526040a601002c161515180241000d03801000200310711f21806403a803403c1c160035203151200700384038070500003178110b00c10664181d9a407980012801402c10f5000c0760489100720340c1186030303841c00c94094501002040003158181c1041100b0491030380660000d10103520 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 603055197 1250 603053947 603053959
    0x306180103020307170712030201060302180f0604181b150c030206070e220504020114040321050903101b0804240204080f0606090a0b03060c070c0906140103050708010b18 75
    0x41c442c426801c7d07500c00702000741c2c0141e445010800a50031300700300c140752410000c028917000d0315040900096546016003410b004560302c0e01607640c602514444072440c581d000c0003074001100540241800070801c0e020303109480c0c082c041d44465050140340300c21010787c0e244d000780041d6503400708103640c94105010100c3d0055036108601d140c0700107071b110317500203d0203443c400505401c15000042010f80d000d802e0301201502000144046010140071141d10072401844141515a6000480b00d6004418600303030148504407000b0520741464202c000417484a0500f00c0e90b070440c124007110408419100601880c0134451a2500450721403000000c0682c5030001500c1c140d03940c030b1602d19010b0b040d81c110020360012002d10200346003a00c41030781c00081010040c0034103106140040d0b207800d0b02415140484200003600c00030040701c06d0759900105040807041014590f248441c071800800c9032040c90000e40341c14000f8409500604050381030f00c1d119022a814038440701c4208a215440d184003c0d4002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 603056447 1250 603055197 603055199
    0x1021f0f060b2a0601180e0a02041803120b010e2103041401030612050c060325030b040c2c13050c07230307080f07050601030803061801030203071707 66
    0x480c030140280715000e8200e82c0101402c641c441c40712000d58201c400e00c41280c20a0004001ba2006030f02460328115202000090220314059101d01e0006c04101c0203410508003110102ca01c810100d001e40064040d031500060004108600c03801c540c2c100d80003602285204856220a0030011030f03403c5030094031184820710710701c10702d070b220301d5a00706500041404001400f058290b59060041000a110900104246150507034500392980c03040e942c42805004c01000203400c82c607c0b50080610f440319444208007191385040c0090250844418040c0283e0824955899076442529510301c10098600100000e100204414040710f90380000152b110030003600c0c072680100d40784540750050788160b03031075a91643c103490300c40c4c8029040840b0351454580e070b00405034040d03800300465a003039a010031840d51750384034246455801e02900070701510038407031200040104000c080086020308000c0718600d5071014482220304c80c160003400000c1d0180c1140b1010000c510300c0741c510542c1134291100b134603200d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 603057553 1106 603056447 603056459
    0x7020907050a09090e060103060506093106050a060e09031806091305150a210b250c02040c0302031611010f020a03050901050601021f0f06 61
    0x444000140b000380c0610680d00140503048004040000500c508400c0741d0b240070900045840300d06d404041001464100b403400e00c03d60704080303111025500540061505003a1101032200010001e45540c000f80542c02581c2c85080550800104207250001c42020340001a061044c1c03a001000180141d00012080788002c05054409503561100000410402c5a40c14400e101d61480c0000f441846c0c024921828017100702228400041600c03180d0940c800a06c4806540f04540328130040307030000c0c0981c040716500c41c100d9201e0311415480d00a690f22102c0d0850015000240c03443d106404500d860701c111030300c00006103011411450150f03560b801008140d102c00040c0000d403c890740340e038502504521b040910050080d5119400d189000c2c002d00020356031002c640d420a0000740c0b8a51000455400500c0e1803038420a121404860780300c020140e00c4000c411107620b44501040c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 602877697 603057553 := by
  have h0 := BRFrame.cov_init 602877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 602877697 ≤ n) (h2 : n < 603057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
