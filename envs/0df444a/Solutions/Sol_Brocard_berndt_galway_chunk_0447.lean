-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0447
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:51:37.523508+00:00
-- url     : https://prove2.me/submissions/255e0b7c-4120-4dad-8a88-bdfb3104cf8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 80215828 ≤ n < 80395685 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 80217078 1250 80215828 80215859
    0x90a0917070f020907030c0e0f0111071503060f0b030a0209030304090c0302120f070c0b1e09011a0102070f05040b06190e01030b010f02060c0f090d05060105030106141012020c07 78
    0x244113001395000f042c00140603104003440c0076200d07203405484030102004c00200030031071600d45040c496054034501403004180b0a0350003506810b07050203c21085020000c084400c240c00800f407030282c2210034810070b9070000540307030300081c0104007503502c151800c0070074294010355100c1507280e070a054000c603400340c1580182801020096401060360307103900d0b88140024043d5400008140001c1200004caa850640703580d11000b030b0030003851070009010041c00c100b60200e421440596407041c1201244194036000403a03902d091000380301050034413003d07410b92181c9116903841aa41c5a040030310710340752a01520703005107940349400301140da070b418060042c04034104001e000918082d003413031140d8003503409135812045540c0240b01d1591070f000102e50130360254400104400050025a617150f507020724481c0418800c901034402c1d540760105240c251901c0390086890410384c480c000206441d4103030b8803050204146000c0c4070140c042035000f4020f10a00450340920b024944010a00c1901c5c1c10001c1d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 80218328 1250 80217078 80217083
    0x403080402130605010509090a021303111806101d04020703081506040b0d05040f0506090f0105130201050a0c03030f020301080a140c090103020d0309080a1202100b090a0917070f 78
    0xa09180c0030100c1c40e081101e00f94001c241c041503003441260241c0c00c180031078640c05440140e00519210440300b800d01d40400701d5100315849801e11043c908141802c4804810318070320400003203100c1c1014400140b107070003980481020400c20f41681c510683c3c000101103500c0d0300c0500110358901b49802c00a006c0038089134202075a4503000035002c0c0a08021046408440164401d241413048010f52040a0032021f8000e607142c00b80e5121003004504140038041c0610440001402c0405c0b2840c803c500b07541c130050451070758404104800380942d80003030445020034410318044501d00d450789404d41c0141580c0c102c04110b2031001c1300200b4000030000b6003569060140c0050046c4007603100d41507644011115565410000541c01000141000e450b03640d0118428184000c4240d2103115052800b15104e00c19903e50b08241d4441c84100c0d0144400c48490341e940303c0a001340c16400c4007042c3d0301c1d100a03005000b416901c2020f0030a0101d0b20111006146219880e03556800c910309104d5859807070350000303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 80219578 1250 80218328 80218339
    0x21c15061403042a1d040b06060702030c0303040e090d0206010305030f030c0c0105042a050d060b030f01090807060e03031e0a0906060801020a091d07080402130c0206010e0703020a1202070c0e0403080402 89
    0x1911000781c5c4c10150384c030440e80034001081ea9900d60701409095003102004a070503204800d0306a1480e50184041d00241124000030140c2e450a0b008051404100000c1141903410210052022440100858082078071a4291655a89522150095038401c82c184070000d5441c00051008128801c80d15400160f03c03002e1000340d90494526824a42c5420710401d030380020121f01c000300048481e0001807500a0041c20b945895581c0380b00076007581c5400d0300031142c0042c0000c20b4010850903108070455071501c50011821468882d90030400c07490a9034101d9081840480040c1d060300968000091003580104240482641d1714605401f03500440c0d034000200b4403a90303011a5007260113402e004920b04603040042240c4400800703842c0c1c0607000d0406e0740c21025400c8189003500a0340981c90800289138000d00e81c41d0303d040c0111001c104040c00751420180100580c103450380d40090030141440022030300680d0b0742101d1503c0c501c0e05074a41c4c400380300045000c081000307150304090381c40d00c1a402507a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 80220828 1250 80219578 80219609
    0x20f030a0b0612010204050108011208040503060106090e070c0b0f04061508030403060507030b0a060f2d0306050303190810080a12030c03091a0a0b04021c15061403042a 74
    0xf642e403e0f4000d82c061070b03000070f0300000108020b202140d0301003562802641e5241c43c00f0748580201e414040c0903000b2030046180980100042c1c16829521a4048160300d890007500c14a0303030312203840305805492170255004c0312000c034042c03042c154401044640c945000ba0384203542c40a2542e260780007032200755140b9103041e000500e1140203009090140c040100700d00c07195403c00b18191813003007800300f49204005030198407040c0c141001e20407580329402c010071016003e00d0b00d000181aa04180c00440c020b41050109041e2012400790f120600c89850400d062156240600c01000410baa444440c0503c82d140c1200140102080301261000055400f48402030380c040e015021307640ba071030300104000100381081d20803642181c1c010750000c25480380072400c010500e002030180e0308445019000c551a407002408140018440c24034910006402a542c035440c0a002801c0200207008603415500000001410083d40c455030200744421540303a0040b00661801d0300c0649103590160300f49580c0501c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 80222078 1250 80220828 80220859
    0x142b1e0b0904020102070e0a0605090109020405040b01020a0c09180512090a12030c06020d0b0d08041d0c0304020906010c05010608210c0c21060901051b07031b020f030a0b06 76
    0x5001c503200e550182c00520300346141442010403202c0040540506030344c1d6103c0802c3c1642d807040032a00a04510001503115410704c0204402c95105550560641d400380c00d080000400158494007203c4031804002100b00540c40d1658921040b120000c02a000e80c075041c00342601100090300102ca801d9815100703080c2c5444070b00b5118010504003030081244180c21200180c02034000b0000c0350380c0c4100c0454010700c1c8030045044240340a004451a28011500f8001d02c0280c0c0d02c42c1484c0e0341c0500714010300d070a120400c1040c40c07201900c040e0088031840c0001300140d0040c640703070748083d0740040208213645d900c10540b511401c51205d0b115a1200500ea180b03c03c038040b100703454251007080041c01c841d100500c100500c1444824103007240a5040c860b51060b0f02c0140015482a60120008221840c094081140f0b040f04210400d058031024814400030030f03032104442c2d15601407030750889040c0226000240c070400034181000d038144a009031031030400406240e4035000e10400d90b0134103607034503894 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 80223328 1250 80222078 80222089
    0x50d14010605090c270d060501080c010e0604031403040b130f06050309030d0515101d0613060c0f06050c070515060f06070206040f0605040f0501142b1e0b 68
    0x1030320404c0308108140700c00a4022142c100c000e402e03a8000910500c0a80601e010601c004180e0b48242d50b02555280100200314050003e110504001d00c2c2c90490181e60380700050450040d0f02001d002d190449000e4189200704204980207030200d6960300e5120000700c52100c807200030b039005010351703580c144500080b290700503003d0b640101100d0b0040c60401520084840007014003d100013007906e40c05c3c50040550300c1c1d00e910140441034030b075542c10f4142014104e407601c8100491400780100410007100309410400350041c0107541107490110b075800040d080180302314954100103000d951810040c80306000e400c00c000d200140c403500c1034605040701d01442098002d001c6a4103a008880e0200c3c004852500d6001040441c0c0700903c201c0c1020f8a07104e640c10322034443c2c0c000c038020440000b414011001d141c80a100200400d00e480e40c070744800c03108005424083c24003401c00e004403846c9494031080c43c240b400b043c40d020303410003000052034402c4001c0f101441107400d14946440c026040e041d43c20072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 80224578 1250 80223328 80223331
    0x170705010c0807020d150e03040302180106021e010e190201080609010321022503021908070603021c05070503100f0302060a211119031a010e0406050d1401060509 71
    0x4120b40a00701103a940038400c2d00390b1091822260052200303600a54040e082c454560356620440c001c42c4c45034218410700c1820041c80507282040210340d0300412100754000750607441d0040018041411100130000c1030301402c20034424104601460f20b000c651070041485c1456114000d80e02c01c102d81c0c40e00000e2004072402800003600c0b05200d11b1080140b0b48100c40c10740035420007481141c001045901007018110301440310070307520929202c401c00551802c42c040004419054284502643c0f400c80b407142d940c020342c412403007070507001300310130740d402c9a50700003000e403c8400b00c014805407034080d40003081540119406c01140215000116000e141c00d45104207a80e8042d2500d498801c00d8101520300300002d0140000c3c1c4007124507000d1607444d15009840e04206184207640e03c8a40000c1c000d104090300e480c15008041c9480140c00303100141c11325501c8040820300b0715900c00c1150b080490f0140c50303a608800d4000940c1e1a03079004110300101c4000d84450681300030020740707460750200040641c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 80225828 1250 80224578 80224583
    0x40608250c060b1c050303090111030c0a141207080a050108030705030913020c0f070510030c0c0b0403110f030310090b01120203060d1a0601030501080d1b060e01020301170705010c 79
    0x40030301c1907400050700c540c44403c180307000070300c60358251004c4c010250030750594000807900f40d000803061107480c59090060550446085001e1801c5180009000340c49003e220043c1d01006941280074420b5900107080702c5443e10900400c070f02500c0c10310b2010307140035000e9405209041c07074400006071954001c000d1380c0c20213034803501441c03410104008020100b5105240740f111160301f004030642411003002070b0514154000c0281c00d25510b041c08000150000c1030f0500c0900d0b017421181040075900c40018010780794000180c0c0040e40b140d050072541d401170300307410702c44034410020032254549002026500c1100c800d180d0009203034480741c846081d110162001800705041e02c01e004190b00090b00038580c420405071480031401d40c1c584070050031032003002000c0200380200e0305100c040d50341400366a01400c030b41300040c0040740101c1c5c4000c0840f800c40420381201c401d0410004100145a0046550619250002d645070758580c0c80520484c92006081d0007107124106000409502030140307080c071180c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 80227078 1250 80225828 80225837
    0x306070908030d0e0106170709050709180903020c0a0807030c091a060d0b0405040605010303180308040909060e06010e06030609160504090206071203051506030609040809011404060825 81
    0x3580350450f0009000d1508410b9225500c0d05008260445603404110b001c2011304000c200061500807000d0480304041c107500208150808240840b915008124a204544130300008020382c583c02c0c00c9040c40030080e040c503400508d403940015480700025040055034080d0720381c0c0005645e5106850225130401040c141560082841100d03030380b420001800c2014401d20300440c103c6602c900080031510115004c6490b540d0b220010b2043c90f070b2200032002c40c8a01902070384015801c1d0344030386d0038600032841024031040c0c0710a00f0001300303c031940154010995050890b180e5584074030503410140001c032021400381c812a400034900d003000145103000040b0451a0302e40c428281000d00c4040c00d403403007003680c11160401c240000544440c810701100305295400043c5400c100c0051682560440081c51042070207000780041541d0b43c0c0000c80c0c116610400710383e621020f1100590344510400c82c81d200035400460005140c07a00203a805106201c403812210341520594410b00c1010001d0400a0018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 80228328 1250 80227078 80227087
    0xa170703020919020f18040b01080105090703020f0f09040c051206150408031216031e050a060f031104050601030c020c10020c0a090e0c03030a1d0607140606030607090803 75
    0x1400c040c0c1d6116040801c0000e10014500840d03c820280e134003c00d203284aa010000d04010118140e0354800c90f42a0300300c40610600c1c40040008004a4060003258032480c42c190101c8e45060090b4100c3e81d4640c402810144c0329a4a0030a041698110385c0c0600e000314146030290f00b005105100701c400b4411901d1000700c0c0c0f03480300c1c030602c40c0740d005617590004543c004000c04103070004100050901c0400d24088103085290900500500d004c040001c0703400d140c1040e004000c082a070300c071381c56111151240c0c00616542c40111080151800382e1142c4804591a0070200c140801900242880c900c280c4040c041d5440e69401101199010b001510050f08184d003000b48034035000301c0414282031644120382a40088400044580030035a0003080303103a0740c0300c50b0144406814030451142c0c140c00c0b0055414a03803400700c00b401011800702d0404030000302c00000085a518003044c2ca02e195040520f110181c0c900000013681d0342e5060720010b10922034980005c012030700c184154070a80e55558091030a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 80229578 1250 80228328 80228333
    0x50411041a1b0109031103030702120708070b010b12160801030807050a060e03040f0f050f01050f0706050a0203041a0105010f0f03090f050a1e0503040608090115140a170703 76
    0x8401101090700d01d014204002000381e003060701da12100078400d40001075a9586407402400d00c0803000400d021a070414820868159000725501302424240410140d072a1428504400c440c41920001843c8070101c00001c00c07028055406401c0020951413602080d031110040180100c00301f02007440007400755030050000450354800f800c0d15601c203404075003c4c00301c940c2d1003800761014440c001d071450f8000704080229100c5008a08001c04041e10302441e0141010b0114984115414040341405000200d81c00100c2c1003400f2210282e401c5681040039007023100d9224080d42c8141d0f0300b9910301810042e48a01080000c000a040300c10503100c00d281c0c0b40340304106442204007841c402090569502d2010085500250107805180c4518040d01d0200b480e032a1103030840355000104101c1c05c20080c551000510000210380c103954083c10045041c0d91000320480c01350904040002c600b0701a1800061440002507a200d04003100301c840ea580c05440720000c442484e500d0252003600c9d40b040504002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 80230828 1250 80229578 80229599
    0x90f06030501232407020909010209040b1c030e0109090c0903021005030906010603051b070506040209090604050601031709131a03010915020a03020c0607080105040b27090c030a030c0c05041104 85
    0x42140c440c4546401c0c0303401754001601d124812106403c207030750000b074201c07114605403080304c07200c030000ca072842c4a81c1d030b1803800f000e000c19100c0c000034203100000700707240b4060f8080c04c010300003000440810f11049a190f9002046441c540c44100e0007a1804225040203d005505a070f2082003040014450340c1e01c1c02c0c3c0110b0250101030b24031201602c0d40f50204180303420410080c41540d000c0c100900380380c00c00d0307c1404400700c00101a2903c80d0854418840080c01c0811100e0449030000103500c0c0d100d1210300421003600c2001a426031282c032074030084000641c260031911110106003411380c6503040580515007a1400130400928224120203528010106036000c1c1014480900d001810a41e20040040c90498284c0d5101d0108048500411403481e0034010407846400540342a040f030300c03202c00d500104504600d880802c0c420302c040003815007081003040380d21042c0e008040b00c00070407850801410340324243d0402d403445070b850500480d50f4105405018810f403100003425140500d0b005140e60b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 80232078 1250 80230828 80230879
    0x1b0f050a030f0b030d0314010e0103020d14070509010806061305010602120715020a0507141b060313050304060c050601050301200a03090b04060606030e060603100c090f0603050123 79
    0x242c80b0340e80d03079a0040140c5040041c0d40c08401c0f9906c00280e040103101801d03078507840580c048524000c0c02c00042c001070321050240b844c1c40d940110f076410346002750000c0c0d03400e060071030b005103800c07421801c00080d8116001a0040c05a44244c40785046050a89041015180240540d40150348808002a2071031a03010081061a02807941e4298041c000b0149100742d922108420300061402b007075a81c00e00a0400050501e0409100100038030700b68000840200190340300110711038000400020f007a00101078556113840c0d844401d8030380d915140c1c440903001c0c0340038400c265018030a040022600307013014810043c00c24000d200c800b180740080000300c622540700840345000c140c1c075000741074002030b003071010700303002d184035171404101d4a0500500408032019041d00101545c015424803502d41c50116a4000541c4861408915404208825180d10400794071200a2a11031000058920781c50781c403c60580765400324050300d415140540c041114041b44040350311917541000034070038a48162545 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 80233328 1250 80232078 80232101
    0xf0304140a120e180901050402011107181a0a08010c021608032b0606050703080a200306030c090a14070903050d081902070c050316030b041202030c0706031b0f050a03 73
    0x440301c41c510000c07082ca061042e281c0c0802c683d1100180009c40d83c105481c0032011514030020103c02d481c000402124103d002c0040c1e50715540e80d070304444064061804171044500245c09072040755603c2c0010f134020080411250014061100c03035070107114560242a04275070001c4021420410042c40440d59018000d40501038940c225801180c4031859001d64001030100786c80f4075449400c2401d0107412508010207140b030851414100d4a01100c40c4862034481105440f44030703844c0d688150200313280142064026a202120404020448000b40c02c030039181880c074941514030fa21051300a680310039590100900300d800580c490a529403140542540c090400c8102c0e1a80741190008001241e0000c0c009032094036150000f4070040c1410404140c115045012000c480303451070306c908044040c081c0c401010b00051a0140c0c0c4018820010703948056400829100350a542d064090b0040080542c450021114403800c800140c0c002ca191105246403a240d0b23a2030603955103400c80040002c2c603040d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 80234578 1250 80233328 80233339
    0x6080304090f0b091e07030b01050d09050709020f13050102010b090a02180a09330306150b1306020d0f080403030509070906061101110405010c080a0509060f0304140a120e 75
    0xa02c0c00c559071304d10080d030094000f0508400c1c80c0071001803d0041c914010201c00078142400600700469038400100e48513402040ca00080c4403400c0e1805078203111507030b40460061400881c040909000040080c400d54422004100c45d0320382c0c84005a007030b6043e0006d40d0781d0009110b40001d0000c0995001070030154001102051803821402c0010014915504030340700041c0d03220381c108512040d07000700101c400d640002042054a10400034a014504d5000c001d003000d4444480010203802096a00701500784070900782e0b1101c42c89000010064400c2c81840010f101e440903251074240038080040000100e075541d000f882c3d0312620260f024010180400040344180c040c001a1010325104410250040d0307a94010840d00340c1502a01303642c6c101208188a00c42008204080ea8125090081c00350b03102c0d100356110044100700343c82601039020441d030040320009040a028680000542c03080e8440c404851201c8080b044880e6101203640b80106000d0395480340c001c140d4011010f00f00022001401d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 80235828 1250 80234578 80234591
    0x804050a0909060f0b030613050304050604080102091507080714190b1b04230616030f14030f07081308070f030221090d020105070204020c0a1506080304090f 69
    0x4104110031070360010840c1d80d5980344941c00c00455005051a0143d0100c1c140441800c0f180001e03154040500321840309005044a0310400c5001e000752801000020501790b1a69511100c29004c6e60007071151520910320300c00320441c0080c1e081c003600c81090700040d47d80d0903c1c1895030f0782180da10300c00030400070902c9443c542d40003019000118a1341a84660030691113400c1180e1071110454040341034000180040c0018003134100d4034011909003214190104001882c030001142441c80344078503240c5602034104201c0c05040d0008090348587c00b0316900c0b4160400c02b4120345019003c03e4078070030388544c005e001140402d44100d031425080300c2071b40321800543d01190360320156580b00c12021070302c001c000c1080c88107164050002e8a0342119500c660051514a01c400b852188244441e4502c110540c1d072a05040da4410703016100c000382d0160086540742041c2d04103550700e00003c017045480301c4415290302000e41c1c1500441c0225078002c40114105401e10b403800024009002d1641c100ca0354030703407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 80237078 1250 80235828 80235839
    0xd06050402070c080f0c01020615240c15040f030c02010905060c062703040303080c0d0606030b040b040218090c1e0304060b010c0209190603080406030c021b030303010608040804 78
    0x10041c40050700c11203101030801d24203520f290801a0000d20400c84e5007106c1702d802042e98000c00c1b0345501c10484001691900c5082c000a1006020b44907034418807a008108400380110540c02040d83d11080c104840d0340c980c003407e180355850b00c200c4008140d03407028050640041d008603000740100b413050500c945020b8982022501a811400c449030311580140f0610100070b040b80704400140d02001002603030411701000340b607075070f02c21032100a003048070f400c0020342452141c9040c4c806c1d00c40106400e1103400c0c2d41e0080200a042d200c0c4405110b1072402c52114000c0c5403078401c541011058460690501c00540c00b00102000300502161303a035901048030205104075000340041200452807940c1c1c42c0d00b002e00b000c004403030b88100c04c1410701c141c0310032000242c1d842d03a05560340010300d280100d01100c0104002d1028040c1540010314600c4041030106526800d504403040c1480c481c0d003141c0060240d5010759258200d095a29030305500208014401284580301c4c065001e40a4082c0e64503103991003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 80238328 1250 80237078 80237081
    0x1302040207030921030306080a0f15060315020a020c010806090106030e030702040c05070c0603050108060406051e07030606020c04110a200d020106030209060405090606011b020405191409030409020d060504 90
    0x1307200407690200c04c0c406902c101a010300c2007801030700d04040101017100140d036455011110b00540a00300c50500000d00d40d42c041c0741c0c0c00c08405541e004440c5211444020680300181d000b407001100580200e08460100c0c0d403003098010f20a41000b0300500969107408030030303002811030440541c1d4070f0108002071009130301d40d409031400402c00b55480c40d81d036420300e083c2018001610341001e4105070074035004004026002a055401c96040080090701d5210040500040d50107500c1d40240b43c1a01e07030420030f010390035501030011540540c00b55141046804104012240f0101c0340307460904040c861481800c0c03044078140c10800e00c42510662000301c0b00341161408100e5141440140c0d100c1c41d00340300314109500c007590401d03801e40d0244207a00b0301040c0f664a4060080100f4101301c0ca14220419040d00070010744652500a801000306082840c10308554204030710750101894142450a246100742e202d00c140325101080c003030340c00c1c40d003045200c0c0041c1d8040e032441d41d100c5881c1c030004102691103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 80239578 1250 80238328 80238359
    0x1803170a060b0f03010303020606010207060f0807050405091e01062c03030906040e010602010c05070206090108071202120405060c070b130804030c0e04021005130608040c08030c0a06060e13020402070309 89
    0x2e02c0c644e207940c50b40c0b500070301c1e0440041c03400c5c1c1150829002040502e8200580e11151080d0f07044c094450340e12010100c2c1c10780140d900c00399010240d5000c2c003100010f0041c1c20402d400c3c1c0c6140c400e505070b8a60005440411b6444c4045003e00c5803003c03143c20701481d07030201407100800201540e140c0b4000c50005800c6800c20b80080715200f8a100040100d07580910a00302000f50f1801c0580c1800b166400240c07a0b8080d08100038107008103c0d001a16440c0300d114802d801110244045465004803848082c2c00074045408441a1203403d010a104400c0074054991701d552101030f1200c00c0e521810100303040c01c0e10020031924a002800044000364041e43e41c0405420840d00d5416140303083d00400400034005022081800710030050b20002d00301044401007916424101840f07103440342e01c1c03c0d1003010640d502c0003156000105410aa220001c41d86064003800344000b070140315101d000b0350525070f0041e149102070103c11f02e10640103041c180c0242c08118080c3c00e0003541d8540e220350241040c8031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 80240828 1250 80239578 80239597
    0x2040504030f0305010509061005031807090903170103020907050d02070501060303030c081b0306040b1f03050612010203070903020411090a030c06021e060103020103020c16060e041803170a060b 85
    0x1e01002c1a441c1c1d80d0b0500c070701c1d07006100031101964242840c1c4e004c00c00140e100d4017a4000c005000000595888100c2880142000400100c400740b0795901d0381c5200410104030101c3c00546074000714586480300c100c5140c166900207201c03010300e032030f0380c3d40039540c5505c0010b035801d2581d003e0264a0122300f080c400d030002507000303450115045206410041400c00d00130b104108000d8a01480824611600241e9130b01031016200024800403000014a121140c0414141d01ca040c000d90070683d15899013000380580c0c4203440c0d607100c540070b0110050907408203c4660001601c0c0c14800c001510f00307504102030003034414002c7c84c584540f600200d0003641e0141c0003610300c00f05003d41000416070400408544039000ea40509203d034191803a030f910f500041c440a41015004601c000c40804103108100c0790103001040c048669903201c101404a04194441500c02c40c034000301c4c5104250310f103185118403541661541201d81d54041d50301d98880c0050300c403000b001d0369035001141c52041c480043c000d001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 80242078 1250 80240828 80240837
    0xa090c090f080c09010503010c0806040b030a080f0d060f0b0f07020d020301022b02183105041109090c21070303030b09010f0f06030c02030f160b070e0f0409050a0204050403 76
    0xb0b00789021301461400c180e10080c003aa15089140c0c034515407000005410038001c40d0049a8400501d00280c58072003600d50103000d01a0004000c1ca042042c240100100c0051000a00a1070754645a80c10105954415400c050f507042041d450807659050062010ba07100801606c5a00c030b140e00841d089800804002e03000741c07003050f819000e01e403481c54015040c02c4280825071601c07c0c1d13840341d40442e140c001200d0740a0000c9180300c0007007002a81d04c0030050240707180d416050100645a0501401d000d4500303a8440001082031412030074440d00c075900c80c807050801800032204a006018a05880344422040c0140d51300e1802c1c040302c4140400300055000e65404501c0c10384002c1000101d40040e84154081501140c2c2000700300034043e880411503d43c3e08000508401c912410f0b4114415024203200602c80014840c0110200c1081d6141d580e00849181e4419500c8103010b99074418502c1e80c041c0c3c84503002180c104540f60a030130802e00c40f40308805030750318102c250380030606589054134103d0104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 80243328 1250 80242078 80242093
    0x1090c06030b090a0e0705041805030c07030b090105010608010e0403090f080102041409160503180607050307030f050f010b09030a06090308190c080610230a020d030504020a090c090f08 81
    0x2407406a07603540d000202c1c061308025504c20201d11036038602151050324086c40d15510131048030144000c51000158010701681d594100700d201903a05e5001c2d0340000c40c0d51990140104007801d0052059605030b541e5500c17a000b06908054016403101ca00070011000c208603c50042130607900080340c4070041c0302000002d6207503410079000c90000140d204456010340854000c000400819005241c91444a820031320360740d89981d84c1884615681401e811094816001800710755035000008521850103541c0800c00c140010048900f6a14255400201d0014000042c010703c030044000f001e030241c0081c122421002e007a50b510054401d9080d0a901207000c1504010040348501060905400f0b98071040001041c58800504068400703008540158130441c0c03451112400707410350300e44103580350910200d01c06102140301c800707510900c8042c0040c0104000710319510b009000d22800385034024501d0700124101110803000342803280d0a00d04100201e44d0002c1c07504503001040002c3c000c800081d00e902e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 80244578 1250 80243328 80243351
    0xd020c0111010b0604050114280e09060a0302010e040e060109020d0c05250807080c0105040606080111090d0512040801020d180b04020906031c020703110d08041701090c0603 76
    0xc150701c0c0028411030b641403949480c02d507919501118260380302400d0100c80205540d25502c614050140c2c0307250a03200320030050081c282d0404803040140c101c6c0d0b848a1151708124140301c28028140c5419030040340c0c01c4000d100542c025010603203040d0300075100044120000c03550900d040c8081e44503001c80c1e5400940741c8610702d150702800c80102e01c1d50a1440c5020806c4d640e2942401082100c80700045a105590040050210845803829040070340d49403980004e00c54240200342c10354007110b0062801000140641c41030050a08a15500301018104149032082c0002c1c0c82035001c00301e6203406510070000c0500103030f4003c1c01c06090102e00042c0c0b5840b0006c3c16074115801d24a0300c0032104107802d40840041c20410150741e1141d816648094180c0301c80300170a14100c0301c84802444014010545190301e40d00041c0c48040380d0040240c0ca4028458201340000c0c1c4010100282075541d00300b0040c02030b0403e4a000800000540d000001c000342d59440f415030420b10380d04204002034450214003034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 80245828 1250 80244578 80244587
    0x6040f1506030f0507050a06090b030705070b0106021006050f0d06020c030c061e070203031b0a030603050106060c0b0f0708060d0c0b0304120806010e060d11040e0c09121f05090f0d020c01 82
    0x34040958107624044e04000c409270001405110300b00c88032800000046100d41b14100365043c01351b01c03080c280c80b03950b15030754060f4440c500d401103400421300d404000290b03803810050340038070ad00020380a0f05420801d0748030351010b907000034007600d0180700030808142c0a4500300f08040c40b41d204040c18800780d5480b441902441d9801030444000c641c0f051050004100c41040c0c405c2d81c0b510031008060740d0300d26940d425005884e06074006060380d480c1c0103001902c0c0e500074003242007040c808d424042c001c1e84c440d09003900e441c200b07440e8540019804000038005003031030f6002ea140c0d280a00d54923402e140e40d03400035031a182c0c0129422190594105001c0050a4200d4134803a00580309003007800700074a1010104560f400f9030f0550b00c2c4000d46038044d07920786202c100208c401a01d020784a00c1c1461805110000240d80132001c2c1170f020b44a110130514003000d01280301400e007280b916545202c0c04000180d02c0242401030002846401202048901000d04210342d011507000e54014000000c0842d00140c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 80247078 1250 80245828 80245843
    0x3060412080f0103020109060c02031c2007080705060f04030503070602130602210d0e030f09030c010906120906111206010201051602060412030608030a02060a0c030b0306040f1506030f05 82
    0x12610310b080d5005200517a00481514145c81c10f07462302c120004100d00001e0720748040c12445c5501509402d808150999110ba03a0443d080d51404900aa0811078540785a40f10f01c6c81c0710711009500050014451803400500030728684010907646803c00d40c594a56904542c084042100c2031075001900140c020103503a03402e4018083c0b0300140480380320211032244d40d080940c0021512420014842040804544c0078001c1c94417044226510741d121001560b045610a0940c540720f48203140d40d038a0a903120360009020b5950030b0b550081e0080f6000d000e0809000004d41c1240c185407a0345241e07800c00404e00107418030002400002481e070401d1000a42100c8010380050000c0c051460041d4502d0340006000e42c000f944691658020014000210000d01c201d0f0403801d990b01000614882c2280c0c0040c1e028040c024804040001074174400e030940407a06034031010340d0150045000500405c8640e84041035030340c014400c80140d503400b91612021640075800440e03d006942035040c0a0003010013409 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 80248328 1250 80247078 80247091
    0x40b0904050c0c06040f1407060806040617030d0903020114041b05010302040506072003030a0801030506090601060e2202030115020106150e150d150510031a1504050306041208 77
    0x1403a1050b0400c0040c3c84500085c40a0100503aa800c148204a0012104c1120f0074103481503407540341e1120401044034906032503440c852401c004010614a4540c2c60210611a022000b54a00b81042d003800004e000d0a0005905555803484142c06881c45103230010310951090388031117008138103200c4450075040b0542005041510611060101792114411074580b1034100410540382c211480040e2441103503400c1054050001060741000c1d1904080b01c0380c107886c0b08030165006036448440c02983d600c0c0034801c14000a641c101e01c02d5035414404200b507020410020480440b039122882c0b081a42c1c4284d01400095541c2d01c591144180c0c20721607803010f05144074495120b01d0a080b0014172080c208282e043c8902c00d1200f404411882d0041100e40c06901500240074045042e143c0c0c01301102244141801040100e070011310b0140b10b8410012030328a40d400003520412a0420301008102d1060200304c201410000440e4680e410000c8a200314800c1680e078013982800000241464009400e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 80249578 1250 80248328 80248351
    0x3191406032a040c03020a02071703040608040615060207051e1509010507050a050c09091606030c090315021905030c0a030b01050f0a030506010206010605130b0304080f040b090405 79
    0xa000240d41d0114205208040c002e1020b00c24a05880b10714107000e03620000507034080d14203d03c00d00043c2d0150060700c41c40e00c494080d41d8125942d480ca20114541001e041081900200014017134240219041e5030002d004003000110401c90b85008451428a50003030320150b40320003400c01486c54075030500e00c1034052070400020483c800c4008948400000864101c1030344010402c0c1e0203692241094907249908102120100d00301e604040343c032182d0181c0c800c0c0c00b80890000140348800001009141d0040d01200152000e1800c0000c800515181d40203070f0802c0b005a4001000c07406240600c018008030940040ea920381200700d080b040602c901407081800000d0042018178162001550404c00c401e0071302040034005100121a54401c0804203000080f010070f4000109034507500052103004283c0854085988071142a20030b40a01c0c0d80e140c040c806042401e202403123610001d1a00240f04060700d0b81041c00c0c03d0150002c0d60015003080c1450800407444240302c1c6420702807580c004944018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 80250828 1250 80249578 80249581
    0x60807060206011203020c0d060207050d05030702030306040e010b0d0308090d030b03030d05100308030c0903071703041e03231006030c050904030905040501092a020a1412031914 78
    0x42e448240501ca0b5400c128030700a146001e150080c080d16540b02c2000f002107241d003846203404030094100030000e40d4644908000640a0740c007074403c80e405403a16400850460b0303504010007020f003480c079820302402c1d5250208480a920b40141000807548179480302e40c210325022002918000d0890401c0d4105400e0008003660b985010003101d2400404c5113010996544550900300714250340d07070000385080c0c800400c1044800c48a0041d0800c0003044007522116a41e9a140f04044180c42005007815017013000100807031140d42c510440d003c904000d00c44480c960f01d03110403144800144070083c070280c0310b45500003009014440075040190f2110108941411130301d9213101400385000d600d001e21071f0080410b05060181c13400c0c8005100081c8207000b15038660541c0300282403c2d403130503d102040c1c3c0b040c5111a4030b4504030148540b02a41c003c01100002d03448104500101250240c198000d2050078600c4080d00030003940f043d0444100350303054041040d0b1400c00c8500174081d02110760140d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 80252078 1250 80250828 80250839
    0x5071506050d0201110c030303071101051e0c0705010603140106030308070c03020307080c0c040606030b0a090504050a02101106090106170d020d1112180f06040b0708030403050d1806060807 83
    0x1c01a80702c07141c080c43e00781d124500c1c0c4c000329860813801c001c07802da00d488080704001e102680f0020041070746505074004d018544949205800e61070360002a207200710010300c00070380300b40d2680d4080c044160007200080754065903070302d4140c848403003001e0404699445200034010b040d00104200d401280c0c501d0802e0054045440003903c900900000030500c102c002900c1d543d1400812005c420407900910401c5000c0e030b1034030064000c001d404c80d45030003003511540014581449220f2144507135008400707407007850036640c20170003420100b00c490360031300c11800a50700409004000c4c044c420480b02000255250a14108035121400d10f00303031076030a500c030013a00b0b0b0b803144d808501074a02000030304001c5549032074000140d0400140203d002c0c12030201248550100c3c0e80d124401e1184a030941710038002e001204203001c41403140303000d0818401c0c0c0c1049208001944d0134000c540c05406484d14030f0030324001119840907142d48a81e02c1c04d416045401c48410302125124410060078141c000b81209841c19 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 80253328 1250 80252078 80252089
    0x14090604080313120807020607020705010e040f060f030501060603061401050a030e0c220507020c10050d02041208030610051e130e0c040602070b030c090f0f0603070507150605 77
    0x108001d10000000c000300e5840749041018076807550744541038142400c2089401401c02008840d6000184507810100e079419001184880c25a0710607910501d450403964140700103001207018a02c2c84964070440040c20440228000c0c02a5214100100c1e000d494031000605032895600418a80310203090858001d0784c0103412200480558200855454041d10850341031030300300800e0f15000010311030039595149808200b8201c004900c88100401d889005040303030b68503200c82c4040e03006419140390004950251000c0c25442052441c09450706032210302414900030546001c4a5643e40030050111605d00720f121031180102130b140060402552a0404078030301c40d100340003a0016000200380210b80303401140000a07042808844a440c10035030501b9540ba4040c1c03141200501a03000042405500ea078100ca000c0e2115215050030010303000304003e1103550022714560b00c58020162040c094039400081c42c8070701000d848040d00d688403810146142040c444015107202d20740b20080c0030582e40c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 80254578 1250 80253328 80253331
    0xa0507020d0303090210050a0207120f0314070606120201030c1103030105040e03070c080d0927050601050c07140f120601090b0607050a110a0b09010206062209080c01140906 76
    0x44540360007818a60909600920102c10043d402c104c1c281901c40b0116001402050f085040b5401c89851075a20750642c81c1c14038101800030807203005460b0140200348140521404581d84c001818600041962500b04235003d540c06111118001a41007081d5a0940b140d1040940c1c607003007007800c008010710307003a03181d1005001c0d40b84101e5452010300d01d001400c20946180c258840440100281c0b10344695550341000000c00d00003403448031000c60512407010080c403c207a4041c1c52608810803103000078001c0c2900a0210381040024410000f001c40104200700042942ca26200c52411000c0b041c0200614200c13100c500a91451080b0324260310001001030444011800c0014903a40ca000080c005110750b07a00604540306102031070090012002d501c4501c1c00d400c8880e00d40a60392242040c0090140d0704505016070010400280075007491210348002c180d001d4000310702d035141400c2c100100c481003581070b101c0c0e0f000410310600006c401d00c500e030030800301147c1c6501f052070206002da43c1e07030b0030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 80255828 1250 80254578 80254583
    0xc060406060b07150e0102071506030c1703090d020112050a06080f0102040e010b0f040302030615040b040e150703020c0304060905030c010c081b1009060515101425031107050301020a0507 82
    0x7a220445c0300203031400e5054a02041d07000d105c580b85100e449103448043e00c1e1500065982c000c1c0410001080c807223000d06421248880c2e40a9414080303000108605406d91440981c1400b90220844001d03c03001c4c45a2482042140c0c000114142061072482c5800449500c0711110382c8100420301c8038000f0701d0185c5044488400d415503130b8050f051a4191a1302407540029094400d503c144a84042d09002008280707205039410803000002408220507a1010144a00350742c0007a580d100742d01881d10b2009901a90604001d4904170500c01d40703d01e540d01c2540844006548090140300703d10b41400003220581c42442c010640040035200c68009d449140301440c650700c603500302220030210510007003029080c10780e0304000100090900c0d201525040311500044030000708003103071510304030241c20340d00f06040c0e4541560801280d0b080b6803503841401d0400b4030052607402c402001214002522146200c2d580d907804041e031454003945000b40c40c4d04624400d0740140f000540580c2c1c800c042e81c00d50b94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 80257078 1250 80255828 80255831
    0x50603180d0819050604090f0803010806070e1e03010b1e03070f03030e13060306060e0117060c04120f0209130308100602030304061d010504061a09040506060d05120c060406060b0715 80
    0x45030440000c6c02440900d00003028104a440400103200000005d14103d84880c01a10255503500404580e10401203441d20b51003d01841c0700e40056900c1e42d8100f48140300036000086080306403000807401c07134ac0c0c07040002548040d2482c21500d4101070100c48010b01f46d40c5100140b07141150f074054684a582008140144020034080141c040d090700981c005507044030003081140e80380e000c0c0c40e00d105000d028100d01c01c80d4003040004404000074105204000c2d00040c941007600300711411303058040e101310a542e4800b41c05101c1c0d01503030303505c860580902098481c1d14030040d01071801811014008001c40061140010200040c1e030700882200d03031140d84503100203800101b40b50985020750b2aa50340351031540c0303414100410030050340d210b0f02580a095441541040e590000c1084080b000c480080050b00b084012a01d2810000b540040d00780c811010344000e030131072140c8840d15820160300c03c60340740d000005010601416100c0c003406010074101c118a040100d032188040c04076815162410a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 80258328 1250 80257078 80257081
    0x507050d110a211116050f040e0f0f011404031b03090e0a050106020c03010c090e2203080601081003030509120f030a030204050f0102060f150a050603180d081905 71
    0x2141c1c14000004440d6002030b070307807401d0007441202100040a00d442d2101040340000b00040240c1c0000c0c0b20f4034804401880b100780c050915090005a8081050711030b0130544841c900110304c48140320300301e072a00300d03d00101079225052008a0030348007410f1800c1160402501440082503100d8910100b001100580e45802c0d0700c43e18088610b4034059004080200880f8140400a0100c0d04107c0c1215195422904038016803800c0500303d84c42c0500c9100442c0ca0107004001c2000400d141a038030948044d021700385420101c00141484c1f05a03001100025503540802450b076030040642d03604150002082076140341143da01501c0c501c108074038103101e40c507003c000c401c8010341080403405078860302050f0f039102d046a18019020b90060b014641c49007000b0543c2d030304254030004429225103242c0f5031200352501c0c0da0301c44000203c2030700c1c00705412194080c000300e05515564021401082c42c000140d000c04118100582082d907030100039820803842c50705000c604150404480c14030501d081d4000380c103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 80259578 1250 80258328 80258357
    0x10c151e05010e190e070e0402030703080c150a06050a03231b042a110c0303070f140a03020606190810020403050706030b10030c022a100507050d 64
    0x140d2400200000140c0c1040000716070780141103801030203942011061201e0403501c1c444802075480c0d1039090801d40d030001c4800c0015084032800c05421074000303030648030510340783c0c1c4940c1c00340d901180404210f03500c95000302c9441d4603d8054143d000c40e9039103081207514101000501d469503036100203010601c2d01480c030355014985140d8900020613280071100c4200c5040040000c14031000b006512803490a92400000380d1581e02c14845241044000e04407480d041005445170001c0c5040c102ca00c1c41044840c000c15141003009050300d6009a038130b0440c69a891400525004990003900306941140300c0620000c3e0700044e0381500000100d80c42c81a8440689140d580f423007860b40320032070a2080c0355040d00a030105038001c1003541e015006507004c00361611320a43c2500c0c124003800760041102c000b030001241c4603601c071094040c25803045d40c1d03003000c0c2d1040484078104000c2d8168601d102c1c21110401e0340c6802d00c5400d0b01c00f02d090420751300380999911140d41b035110001c020010310184c040303000c1d40d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 80260828 1250 80259578 80259611
    0x1090603050403051b0c0f0f0901030209070203040b041e06110717010e0a1101080601020a0503030105040906020c0102400b0a020a02150408010b060306060a030b01140f030a0b010c15 80
    0x1050b0140200c850402011550703403185e0440300740c7d0098100708100f500d05d08104208608e6150007804482050740703141d01344110804000e00c0d0800714081030102040c01e003d07090040000304120740081c40103282c82d03004180f20204070750211080c451840248002c0d4400401d1000c00c460b145100711828028041202e03000d041341d001101c82034002e0340d440d1020001e01d0244000300e28001c1c0d82c4c0300c1141e0b481c0001a643d03141c1c04007000c2c04680c402d01c01048146000d400c1040140e200364800341c10032081e0900182a6000b800d1150f840b182034001655964a00c0c5140b0044201202580d022034074401c2102d980070002c0c5d0107030a540110019903500201c0c000c0040c00d104c00da01400c80c0201120b81c036070b186460f401078090312440c1e5081151414840c50194152401a00f005040c10b02e01a515001a07000382250f564190611070041c004030307191840b8201a10b50002100e4000f40c0e6890f00304420011202400c5ca00d50500070402c050601103284050b445070310480606000414070550b518001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 80262078 1250 80260828 80260837
    0xd0f1d0102010f020408160b0c070905070e100507020301050f10170304050a030308010305010f06140105090a0e09100f05070504030305251a070201090201120c050705030c01020405100e0109060305040305 89
    0x88955000050006c1c000c100000c1d50203821030850030321200980c13120200900c40c402d1003c07411007a400450284407910055018642010040c20194000c52111011580e43e000710349210020400c0442c28106506080c02440e500120b004032201741481c000c00084441f00140c0102c9000f03d00d0101812540c010410482e0701a120090146190031b5591400421a05e424001100c01d5424540c880d83c0c0b1803180c1c0a51415a0303190721003101808981d000459154112041181d84074000b0030000580300003141ca0380f4011401000908201d00e80300d0000c200307942e9640c1d003c1100310b05c1c00041006859000c020760741981d038545803596540318042d81e031a2a0090b0040c00b50301001402031244d08000301c440c00c06c0c1c0d9030344100c000340c2e00a9480310403e0b401c0b98140400070340410182d15080b644c204080d4441c0c40010101d0405a0904510f51190f500e503411900c1d030001c1c03036940003030240840e10b8040040e5101a58030b2804265120305400003e00c3c0414070310842051607103d5010900701800760040c0c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 80263328 1250 80262078 80262101
    0x70e190e01050906041709010c02120a060e0616020601030b0601030e070902030c070b01060c020a03020f010504090e070515030112030503071103070b04030906111e0f0a0b0103050d0f1d010201 84
    0x2800b0a081440c403040d220704c001d036411200609503070300c8605880c1032070741620054207058540d41c440941e44d4080c460345104114442d0b0f01401050004ce0006013603101d03622040040d00c0c014003540c90300c0e582404500100861400c29584071000410000f40782c038141c0e40d1300031401c2c41c0128042860740c41d200c0c80c0408070707040618018008000c00410300312003405400d410f8060f41e850355041c0d903107020a845001000c140a50481010213050015040c111444c104070f11043c50842d107001d50f1007041741d08540b108075180c00150072501041102c2e1400301d0900054075010107003a45554981110718031084d06020f07008041c040c0210000301e4060051168443c00c460324015030740c2d81e1080d880d2200c0d44c590112011030111b440f4041c0032503203911500b0b500040c005000c000309142398480143c0c0c44406d03280ca00d0000603204520004002110500002103464480e4001c803185506500e00302d418011561810310070000079110090116a001c03030b030300160030b180d100200140b00c2c000004038050a03451082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 80264578 1250 80263328 80263331
    0x14041803020604031d03030a0c050c06040f030501060f080a300f27031b03020d0f0b070315030605193b060f07090302090c0a0e0102070e190e01 63
    0x200000d240d0082022485648070307550b0741000e07000c00035a28801c0da00e80001d03079815610034081c4000c814050541000d00d03e000e00200d41280409100082c0c180d8095040401504840c020400c1004000d00802c00a0b01741030b030304040e401e070600c85110380c1c13014000c0c0003501c060030070414814607502410641901c240310740495003911038116005402e0042426404001400702c80700c0160010842c0c14024206400240c0e003941d16146440740c0e41074035040a520b2001d020400b40010050785e6100044a800b44500040b4200403610b00345035a10080080c411010325051246d1442180b209150401c2a20b5100c003000400d5200c0d882c80b60030300d603000168424614a0204655580d101807000d464004089450048000700706055440304004a69004e040ba5400381010483d41d02c01080c2c101e50008692811015569803600010b1113284244c0c0d10390798205000886208040e03020940035440e00085c0010860325182500e03c42000d0401010501c080045440700242414190408010303100b91000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 80265828 1250 80264578 80264621
    0x1b020d0f12030501030203100c1704110111070608040807110316140609150306120706031b030e0a03080c0903061017071a03100314010c08130206041404 67
    0x5050949199640e0141c91003119031000440c118030a001c0c0a05072035024024005040d00050100041c0026156002c2070060002d01d611580840b50032041c0b1030fa000d84607500b4400305580001d00282d000b001c1a0246400c20341c41441603903081101c158100341e0180105a40314401d04080201409118640d945402095203594840100103603600c183d0744408555011882d01604000c0b843c4240000e045c0c011010885a010900e040f0000c3e40e8401405017a40398005a00d486480c00c0c00400c1c0c00c240b0100baa44c03100320034540c00c460410f80c5c2000c0e0034141040b0190242d400740d5603840c00c155000f001c115080c00010140190007041e1a045c102c0542128030718103181c2c0d20f0301c10f58682401901c2e214440b0402542c03084500040b40d000310f5103400c004603003000c03055040a17025031004109800070b9031306901c00400190681d5283c20291310300b42c00040d05a20b6250001d100ca5005014038000d6001641c2c07050250766184103d400f204e664103200c00300200c440c00814050051050881840c141072003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 80267078 1250 80265828 80265833
    0x8060403080a0c05041404090f02030303040506070801170307020d02030705120f010f05190c020c0d0510050604020c0c0409020a1a0c010c03061a0a0c0c170c030a020108071b020d 78
    0xd50301c9000d01c0000c8414040c101440c07004035458000ca100e040401c07041e00030a08010b040c2a40507040b000d0003001c80c40c240c4401d40d000303c0d1840e0700030799044465034440010804220390018085014180e0081048010811030003120342c0da010b004000303480b0300341743d01b1044219501000440000c05010305011040c6c04000e035001d0b140c2c020884084015402e080507a07200e03140070700c0342d41d2190a204043c00741c125102c001250080c0b0710598441c00358858180304018070b5841040d0b90506620071b5000b0014422020305010650b100544494050307070043c401b015440030701082200100c0810798002882d019140006446200302d684800503000010340115500b4440400030100000c155000340241d9400c03507022030885840c0d1140700c2c20403d0444c0c2000d81000c010b00141044185807504041401950b01c3d004e40c15406d65201c0c0e034015280c003085001900b028080c107650700c80c04034003600e04940242c0001e403050300010804400c100a50b040300860500800039565540d4014040180c4482d551 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 80268328 1250 80267078 80267087
    0x1119030933020309030606060708190c061802120a03140c01180c08070608060901030f02010c02030105010f150207030515060a03060e0102090405010503030304170d020706090507050a17070b0d020408060403 90
    0x1540131400303801340000090a9040c1030040300d1405078428106071510b0300711803d2038040c0d00c40b03146000c10440c0c4406804041130b140d0068070348040c452035075440c24003aa441006030b10003c5c0c0c034040c9103d4012089220100f40c1140804d06500340d102e20403036842c1c0c00c807440540107000c003102100720321101c0403c81050081044290055640f00c001b203580094a5000c140d0300820225001a802040c0000520000f030a07101041c0e28184181031419154103140c0c00a0700f912426080b00c010301e0501c0318100428a02002070300c200440600140041070306648a0350f4586001106046c000010340011401540380c0710f112100658104074104050608002c0e00c6020394814a0254441c40c1040c00120701440c01008480c000c50b44403100800100306a80c910240c0d8020307020700c0601c6982408a080460128014101d480e8841c8014012027800e0400700403403800640c000140f03180300b004004080410010b0704d0020b58101405050312840c0c0d086801c40a480380340c01c1350605016000c244420140c20 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 80269578 1250 80268328 80268337
    0x108010507020f160501030903091d0603120a05041401110609030a030c0504050f040c031d010506090a0606090b0c01020712020a021503070c020105071103070611190309330203 77
    0x2103034281c6043d400e4402101e55210030851040ca200407440d03a08000342e41c000e9200708401c038800d0900300180c070b071307240d01d5071607070090301c50380061206021404c0041c240341c1444003201020808208a041c0b034003105000740b19000314020180c1c0000c025840718210b0b0301400418601c0d14612080b0b030a00d11300f0101d210307100d400c000980d44c0442d06240488142a0103a01500c0669001034481c001c80901141000054120759600303100b8195203a10007001807149815403a411074124000bc0b03120b040c650b09010408200404c0404514945207003031140b66802078405040b99500901c00e600d81000300c1c84107009101d089001404000c0e1028401c61301a0041007510456000700c8461901d130ba65090315200034030003106c65900080c036a4109000660203800138010503030191054100b09200807000c645010301d160072070008240e2651030502c0442c000c01400340c07003040034400c0b80c40c0f00c1125600645224424041d00c140b5240c03800d00c01c440c0c0540c60445200465a450030b4a48070f11140b14069103d034403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 80270828 1250 80269578 80269591
    0x7030302011b050a27061d0402093003070c0e0f040309050402070303090501111c06061b02060910051b030c07060f05070c09060e092b0c080301080105 66
    0x2403800b00d01072407040c0d8904080800e0a510380c2490b2000c413100481d042141e8400c2c4000703104800e04000e418090306444070010b0452511945035002d545004108000c02814070144218010402d81105845148003000500e001340c1c414606401807542e010070900000f41014018480841c84800744508410346008840c034a4078146403d8070341c00d0444030400c204a03000307404506000780400c0302e81865070040c50014001e2400080e038251980d502400c0d80e91482010950210120307064458103c81804080c510200081c100300d03051800707001409003140c40c40740b500c450f00c45203840b40554507054202d41e040000104440704000e81080701a100340c2100a840f0326001c1550b1079000c441c000081110050440c0b00001c00006c0d14004c800c6945240c03010000c800c22405021250000c0d29030049400605004000411118149800c61601c084018007102469200c2e20302c5d002d03032122145005400a990f0190765404528070941550a0f1000400003011000700000020b803076541903200de8040c15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 80272078 1250 80270828 80270831
    0x603190c090c1d0118050603011502010617060f06010507060f1409010b031203060a03081303110108011203080405030c101e0b0303120703060e1510030216060f0605030d020703030201 80
    0x340029000c03550407000800e200f1160301c4164264403698020003403100419460300810188a8458010465580081e8050108021201400c0541d0380d020300462010f041e052042011110a054400f40d586101900c401180807814012800d0359216104550032241c0040007480034203543d02c81c0800500c1c986c0c0340081000103040c00b081c5029410302035101c00c0c0c0c1c1e008000300000350301c9081000080c7e002600751036000c3c0a2035000000100d0742d202404403c0c201c55444000300f0301d1420226110f010840c0020304024181d030042c8124440c0c021550138050301450401c000740d840b80f03000703442c0d8400c0202d00c80e51840799005aa0b9040c001d50001980e005000c05800c245034491560300080d00e528425040d49034105018411020301442e0969500c10014507021910030f548409074015402c05640c5040310140e20001051076082c000b44805107003c080c5400c501d008016006541120218100100040d071a03000816a0100a421103005424014280c8034440f42d526000396490002d480101d003d075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 80273328 1250 80272078 80272091
    0x30b06190305010e060d080d1b020d0f020303040804060503040c0503010219030b060702061204060204091b170f01150c15051801050103020904080304021f11070b0408070303080603190c09 82
    0x13079400f295617400360401504540c1c01c0310b280e07511a500c6801c00c500d050400b07a641c840c101d813841d0904c007540900548640281200c0140040014010300d403418003602958801c0050000081000c0120380803100c1c0e078506180c40740c80f24075041c40e01c118998021a4150b0000c660005e48440c203940c03c010f58409620108a600e0309141400090b01658030040c0d401034091017020a44602c0c16042035109205103001444c2c240ca4849031000c13950400f040312211100103c0d80304080d9000031415201c400c0c070184e600c042e03180140e58054464414058104c66160840390f1104d500d00891600f00c0c4240e00c80e041c080d04843c01650100200003c0380c940c00c05246020764000c00301c0040c8151416030b600941380503055540ca0300c0f005410b40c03001d00101c0c0c0101d070004c1c80e1030001c043c501c842440250705070303a070003141d0a0325805140380041c2508504000300702000104032460b03000580000312945410194a980d89000000b800d0081c480c0c112441522b40302d0302002089a01c480f00401d848a001c8104040d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 80274578 1250 80273328 80273339
    0x305070306050f060403060b0d06020706020d0b0402030906061c050102040b071704030302100b13021c06080f0712080c1e0601090605062d0a050301031a040b010306020a030b0619030501 81
    0x1010f100c215a550003040c104800e10207c0c0042d00108581b06002c0d01d0305c9411403155032040100d0744030300700990300a0f0380494108030340d100303170301030f03c0e42d0034108840560030b6042c41a10b00d52a00e03401fa0072184146c0d0308408140107209a01e0500100a42080085499941c1c0d4080283d003a030002c4011a207007650703010925511120350003a50b05036034060740180743c0940f00d40b425000504100c3c0b0010b0740103440c4112800d1903038032400184a0150786038240107103141c1101000e41542d5042e0083d400d03503044040301c1000c0120000301c001c00c43e10b01251402c48856181495078191150b01b00390311950240b00400e10101300b40c1260050300d07a044c041240c1c0c10f03a0b42e402d280c2d0221062402142da001030200441845000340400200240c100c1c4004820210030322801320043c1c0d44070900200c0481c0e0044010014410000100600780501c003040100342e14180c0d031014580c2134140401071406e43e01040342d00109100b9444031100c100007070002542d41d500d001540b03d82951040c407403070000e820807002149 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 80275828 1250 80274578 80274589
    0x140403030306050319210507021c02041a0f04090c05090403050301060807140403150f050109151502120c0f070603050f0a06050604051c02150a1b020a03030c05150403030507030605 79
    0x4684c6c0c20500313815111520032070b140074200303200407402c00f0007000344654400f680d40d400f0311280c004040420780240f001244107003c241c4d41d461244050001281091030b9554503814072201c0e000301e085030300140c82520351518600d24090740d0030040d04013000c1000c000805070007400840c1070700e0f0a03481d41191a031703400e0812030311401c1170070102d4180700c0c0078002040018014202d11034103008030780300441d4405035208260b0458001364800780082c4e458580d5000c1c48248000501c0c058500c0c04203a20310008c0305200655200f00301036800120040009400400c603505201e1083d00c4a150f40986070381c5a602d40009019100c10780d401c0c1d800e203940e0310205000412910440e003c49101900d054101440c0c401080600050351081c4194800c0340141e19005980e0a02c0500d8105100300c2c1150b100d4076003410050030403d80e03000d81c030780c8042e81d8402407015a68000c6164212681403a02c1d0f00801881d00d019810000c0103070b0003410425290044c4404c140e05504044d02c07491007680d040185540e11020000f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 80277078 1250 80275828 80275873
    0x31403010f030b04081e090f01030b100c050f0601060804060605041803050a09080303040f0b01060801060e0d060e0109050c0118050a030b07020a080d0203010e01050a0b0306010f1404030303060503 86
    0x185258400740c07042001903444804142e010340074802c000c0c1080c107651071110860742600c58440001c0740006040031103140100c60160720380c00a10301004940d080c1404200050044440c800610030160542c008100c0c0421517441841020000d503842543c2d9030f0030243ca4118159401c9030114104280490705080c980302d4081a54100e030791241c003103002c81d1000d54590b4403050200301045003141000c6070505040005501403841140c11080b4820f56080032031071040180c020b40c0070441003500421400e603002c0c8141c0c60541c411941c1f821001550701d13090005100e8145070401e01e500701000c040501002003104140b9030000c0e210b0089100706881900301500040c0039095120741700880a00110380714540d260360080c2107004035081100c654882c1030440d0004204040041d030000014001d0402d40d80c00382d401044251100c0d203c607800d0415448090100030b0607107040000c2500700e51603081c440c6810b100071b40c0c181ca52003580d035612428020098403260040500920400c14080741d24140076007002c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 80278328 1250 80277078 80277089
    0x708120a02070302061302010207080a05030705060108010204050a0b180a09240602150406150308130b03072c04111b06040819170a1a0102010b0102030a030903090e09070303140301 79
    0x2491140c0d100380751b160341c4c556012810390451144401c003183d520000c02c00780c268140a08000d6403154124500280303000d005030090303e2a640180410001621900031030300a5900a0a002c0e84039041d8009a401420100c1555503114820041c00035a103802c66000c0c42c11000f00f1a609111502030b8140c1c03070003c01c101e00c01e038001a0300001130b004007042c5c0c9082080d00284a5807001c1131980704401640c502603d107402c15038450600040d1000c42c0045845010020021660701e24210b180c000317000b070000000fa80450004080d801344050825550000341850040c00600c10031110f030002e0030641954110000400301d884003111103981c4402c001030500e100c3c0c3da200c00d11038035015001e0031140100e01003261075014456020b01d2002c4c60b094454040b48a50250100000e1614121250340254950400c0680c1564500315050445990210444048051505000c180b03811149030440700e2416035448180c4071a4150b040c07014046020564000700d9021341c0d030360008141815503101d524402803150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 80279578 1250 80278328 80278333
    0xc210c07120c0212060c0a0c1e12020d020106030305041a0d0c03020415030203042a09020706050a1a0a1e0315020c150108150a0207080d061e06080a0b030f030708120a02070302 77
    0x2c0c1547c9403040b07009100040c40707002404c0f50002c500318504c10741a8a05030131070301400391040440801d40c0c104010085122580f00901499103561000340051040740100d128044042c4000f42e4404103102c200c60b40300007e031904018503440316100800a40090040840c20f00d4241a104c403e18440d0095901031508900d8100d16401034000b90403070501c5080841c060040781040004514440b0310240c07230300c64020480413440d8500349020707508a07401d0300c2c040c1018090340103052041703885000720b840a441c50300419003074252105400c9081082c40d9440202511202900c03a280300710369401504240e030401c1d040703a078244025152141401024000c05132203a114520090420080c002100d42060140c0c17130041c0b030700071242c854a005600541079101043c1e100c070010040560401d9a40c500c10381d09820b08103815003042002481054085c007170315141a12440a42c0725550103010040280307541d40d0071659100304500d8482d4003a0403014402c28110400c60005402d5002402181e85e0180c1c542d01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 80280828 1250 80279578 80279587
    0x60a060807090b01260907060503010e060f21010218030102030106050f03060f0a08010b010f020105060f040506030f0304032307051c1109070203070b0c210c07120c0212060c 76
    0x9440700105a52469141085a44110b58489100c50040c0c164602505043e0074114909040f1ba64644074280d40320b8410010b01b08010812a0700700d000403500244225210b041d00003854000038407200300361001c1c03415040d0104031040d64150560003802400d0022403094070a00d8141c08060803400244500d0740807800c204030b2650011111002103174850401002c0903121702e1040c2c00b045001c0056044080644e43d2011031116641e00030800c560007286910007840240780c01c001050159071154003580c0525103500c0440c90aa5090140f444241103440460703031a40d030b403401c000c46444000041085040f41c0300d403044c2e0401d180880c420040d918003800c11980c116a0403106250042010001e680c0d0420181c1e207152150b880e08021401441143d005544807507403400c4c508901080a00b18003840e032000c0000320244044802055404880344810320701541c0c0c1d0098152841c41b519000801c2a217074291344c42212508081c6201c8400d000b512090f1a240307403852980e55601c0265000c05190700c080c070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 80282078 1250 80280828 80280839
    0x509040b06092203030e01050a05012303010b060a080f0f040b0f06060702030a0311070902090a09020703020312090d090803120c0d020408060903030106080c03011503020f04081509060a060807 84
    0x410a6402c021000c40c01c86850f00041859207140c01c2c0c001c000c84c006925100c420310450701c2400b4464110405907000c002c5035151840900407406a8030301d012000500e41030015059800394042d10340400d0203445555107005410008082880469103103040a0b4980081400035102c0d00010f0301c07441e840030301d401550301e400280c8280d804005201940c008801c03c0250010f0300e042c01100300c3d55119403a401e1140c0744100c980350902142d60001d04805105100c041c00658490743c80c10f08407050381c80b0042e655005402c08901354882c100a100420400345c00380901e904000400130025440d560b14030300c56645171250903449109101340c90340d0780000d29000c1210000c40030020046050180ca005143c5951094114208201214854180d400100041050a8002c51003036130010440c24401e1071503040140c03026292103100000c100f01036001c91483c004001c0342080314050300e102002c8400e29807640c080b000c420003040b90204414000e00c2c01040c07d4007101d000e920162010400a001080d0818 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 80283328 1250 80282078 80282089
    0x203071d0601082707230f0f280303020606060309030a08070e100215090c011407060b09010b07030e01051602010e0a090c0804050d0905060306010507050f061f0509040b06 75
    0x15114885000b0401d803424888003481c0030f80d0107941140000381031454501401080451034401000b4545492145115010787e903a1780303c1140da0340100d41c0d1913000c024007408603184075107211141444040d6207016080340f0400f0b0007040d04a0744203600711011035a641092000500054a850f40c5592052101a01c100e0051403da503026404e840d02240503510360002804000c0c1486508000d43c001c016500f80da6103280c0c280c036500c2900c1a00500f54600088002007a04200d048034500c00f0a02103400c00406c920358018014600005040d100c007541c54191440c40c3c0d43c0803403411804500c8040c03068440f03502403010303105103134036800c02e2282940701500150750310b03141aa601c0340e01000d03c41d400311b500e1489218610828103248d4502c0351b185010300c0c5c02807034031002403051410b200c05607000f08035607503903581180da00030428a000e90f2994001d1900c1490582c9000c00940341780607407001c0005140c0e40d6104030030004104446070380b54079507078001e004a80c80242c9001c6d0419205900003985030400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 80284578 1250 80283328 80283331
    0x1203090b0414150a090c050a0302060301270c03020d05060d020307091d010903030b0109170709240608100e06030703030305061201050112020108090c0f010f02030418090203071d060108 81
    0x5481682c0c3c1d0f4640301518140088011038034082400d41e240201d1041c080c65070745510141c041510003009281c215000244103000c1407180c4400c408100d80ca0107803800f0740c0c1c0c1901980841c6e8141c01e0100b0840020007a01070341105045101d00ca24100015815103085542c0040c40d0b60040d0180500034240210b2704050101d00c45c001040007000c90300c00c5a250000d22580c3d856034002d540c005503552021000410a43e4a0b50140d0304204078128600c24420740800c07180212003085400207a00c01e0300b00851a01c15950200a2030110300724000055115000001580b041c00f03240300e4aa0b41d51b441d9100a6016a070964000380c0650000000744001381c0072380e00294000d6002800d8111034101c50a00c282910000d0304801210040142101c045581056440350003484440141c5500010100803484000340003007103904101d51500300030500c074006c0c800c4501420105510700d2260305200d160034080e0080b0b4170228000d01c5a0040052480610703600d80c1000c0d100000c011000b501c0d03107001140c0c200e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 80285828 1250 80284578 80284613
    0x30c03050f13030b0109050f041208040f0f050601050102011b05030103080d0608030d0b030c0103090201020a17040807060201090507090209100c0501060506030114090615090402030415181203090b04 87
    0x70030803040c00c0c41c924941101008510520000c195581000c40540071340f0000750131f10700680c0e95081071000144494108000d020700320b280c104510f64030303414402c450301e00c40c480241c081c2e40c0a02200301031050100d0f00a050702c0080c2c00034404002000300e0791001d15242090400010000d20050001070030507001407540e0f2058400100b140ca8135800f0450550f8445c101c4680481d40d00c5180b2989814203000c4800110000d0a007042500361540010b922450580e200030030400a80c1915500b1014000940c0d015000c940201c41c001038072190044c0c002c2c44845015501ca01c20960300045040311030085503624003024180d0300d10200000402c5c1c0e80030300403000845e09552120320104407900c920015500030a10f225005410543c10b50601c12a84c00103400740c0d0098040701341041c0d01d001c40c1811252542d0f0107817801a533980e20740c1880c00301010030b5545032060b02d05024a0b50b000ca10340f06024008180135000d40102541180016021249040c80c018200000e510003d00410007440d448000d034030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 80287078 1250 80285828 80285857
    0x9050d03030b041d0d0810030f03030518060a2a0509100c050a06090204140702031b0a0b0705030412030b031b0d0c240c0209040b061c1a06030a030c0305 67
    0x4c9007058520a164003214201e14a5800b180181800c0c13980030080617080321610013013089185c00c6480d03044980745505e00c0035044c103880e800416452002c40404500c0d0a0130102a22850304140801d03001524148108000c1e0700d8000c0380c2290380540403500b4200d00c01241d21098a4200c01c40140728400c4400c0307015405000500361600089002403140c00f007000d00c281d0700025003544030305c1000201ca007001c02c0720820a01000401c403445400108981d5404416442151002e40018145107044840300c0c2c01447c50310900b05210380c00b50004003440c003851240540e81c4282490140c22411119401c40040d41644170403084030340001141c1042c890444080c01c40b4102480c15140c86000f01c200d648008507140307510728240010101da0888920181c0545400ca4001d10b00341c0025440100203400034024500c0c2c0804501300343d0721040781c0e40002d414619a9082022a42008031a41c03000c00c3c000840c20702d203000062084c1c81d01140c01103c481c1d15484031a262002e6460440f030039000321030742d01d0500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 80288328 1250 80287078 80287091
    0x4080408030705031306033812010912020d021f0603080c0a05010e010908180a080601060509011e170901060f080109020a0b030c042304020304080306030601050109050d03030b04 78
    0x9010030700007460304600410003580ea5080d0700c01d540c00c00c10307801d60045081602c1c00302e01100b1100c807208203115810f254280d201e1114050904200803403c0c0c0034540d54403005210540b002a14107401c0708180c28040c0c5000160042041c10a90b1584120000b400068106000c0d03401c000e1035442c1c02812440419200103840c6481341d0f10070030315912540040390750380d01c840386040411400740103041d0b10540700e02c003d0000c01d840d41c2c2e510306c040c020341301007403910356140566140c103845440281004009000c01c850742e950b0758941c050840d03170050140c140007810381103005012901c1802c0c4604404030a982e03220f15030420b100700750310014001c1d05003541175480d4000012800511003880d00941441000040c000002d44104403020000d5888100c40300c1c0c040c420044401c42c80300544040350f2030800008000b00e04c024805013070028412001d82d015202005110034003103101c026610846003a01210141d0762143c0040d0b50005203482495400401c0601c80b100107442034018000700000588081502c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 80289578 1250 80288328 80288339
    0x7050d05090a020306180304090902040b030a03050d0b0d02010804020607150e07050321030c13030b04081c110d020a0924020d08060a060f021501080c010e06030f060405040804 77
    0x155002a10415101e900148822083d442c05010043d0030011701c1c040403a070300c41ba1310f840b6500c0307020b00c0c802e0407034030740e81d0f12051020354075150050203468500409484a403250303860050807030b40040c1c0d1501065890320801803110b0401c5044c101c0c41c2601615101142d079955420017150740e1000380d0480c2c548405101c44080d400c4140036041c000161940505551410401814500318021654106500d0000742101201040e0000c8075081030701c0282c801c0c1e0b40c1802041d00c403001e1000c0d0380018040a80c003010081800117400141c036080c000082500c203030b05074013100344050741c188103158041203e00300402c0f100100f243e8010200081c4030b0a043c1450340d510104018240300e030b0200081c40710701804580314101d40c10300099a004401d42060301140c02c1080c0450240c0b6498055078080c0000e11038000302942c000c002500c450180c10300002003035030b107030030010380c0311490311843d42e0110b00e07540c0301103070b1514045050301e2041149801d00049035556400300700c041c141c0500103452054040002184 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 80290828 1250 80289578 80289581
    0x90405010b031803040312230c1c0e0102060106050d091401020c070f0b0a0537030f060308030a02131508091c0c03080903090402040306060302031b0d080307050d 71
    0x801c01109465100c1c40c001904a003e08020084101c89820400050000550b51540400006481d281080d0401c0b0aa940ca2124101e2360452000e20040070074038080d20080090700c00f2100c0140e200000410001182c1504e00301340b1080002e025800c0640180882071040025110104e281030001c0340000c0683c44511200400c800f41c540c5903500000d07019015201000385030014040d401c031100d05580380c0105948075004c1d1407400401c2220025800815007640340080103850082445601c2c403034446400007041c04850811030011a04144820390308240e20f200b00c80481c2e4019030802d1440c0d036480c810b40c000f0741c8540b48001d00303154841c101007020090450b03014400f00040d21419000e0410441765481d1070100040f4075110b401d107002c820081035010720348650065040c20013503120346642c1104c0c0d095004404540c1d8001344042000800d0202640009040385c0c001d0701a1200500000c0d400403011500b00401a040750026050b60f0000b084900250f6001c1e80a10709a82840300f0300d6815070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 80292078 1250 80290828 80290831
    0x3030601111911090105030a02060706111b0604230703030c0204140c04140d020f01030e010b060d021b03130b0a030212010906090c030b030d0e0a0302060301030b16051c02070602090405 81
    0xd6081004103903a440f14180040c20300d000d840c0880c001c0ca640c40030361340040c40a02c5003006c014600c41d19a403032000340240d008103440307443c1d03000a603000241580003000e56031200120307400c0e03e20a0880c41d402c0b070402190449010b00c00014405006000d04603113080c0ea4900907820120307000396a418444034580d201056a900802040b84041c1d81c81d841d02d01a0120402d104000f58401d107c0840e641c0300590b03131450000303c1c010303080c00d0110740503000000c40c40c01400702d180103640007040051f0065581c030f8958005e02081e280c8000407408148440700f60343d542d026001051070b180150305c40c280030210b0240c1c0500101000740c1b070003501d0000304c1400210340d842c0c00e9000001054440c00c050241034414020f84058040d180b0f01000040000e41c002540d0b81020900c640500c03003040e800600c00d0b1100c441703120107550060320075a6079582d00d2a06404810040f05c0d080114038101e14107040e528414401c40300300c041052012001008880c0701c0301c00940c00010100c13400d690030403001d880ea80b100c1c0a0325 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 80293328 1250 80292078 80292083
    0x141b2209020301030512120f0604180302160608010806040b04050708031303020a0506070b01050603090106091a12070605030c090109080f011b1b06020d0209030a06060521030306011119 81
    0x350b22540746261035460302c1900b1080d82500c2d00107000c50b0492854246c0c0c450340c4000000c440c1000c684a00f400b1800a04410003c01d0540300c00303001c0d841c245600054240c50702e10715403a0b031320b0780c0301c0e901d00003250000001e010750f40654100c00c01080109801424198006001d1004c0e9041c0c140d40b8030405103903074040c22901f61aa180000e04005510b4010010001018103a8400c0d103081c0300e03a07507010b0310841c050040c0342c4100c1010000c0f590140c1d095000c1c0c006800100810440700b075041c1d209418094000c410a4444d5502010200720084041000c40c100d41780e075250142191610808a242030b01305d413074084d0400840c15000507401004004512039100707920000144401c0c00707050482c0e07a0020706030007805e2000c0e03038a051448180301d0020b0401d458000320016100d00300114844007900c16410403541c14800e20292006018040e4414401c40f40201c40c000c2d4120031000425a02904649000b082e83d0010300011701355500800c00080340c0420802960031007414500310000541c4103041c00e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 80294578 1250 80293328 80293331
    0x18010e060403020c0a09020315190504020a030f0f091a1b0703050310140d06020d0906091415040308010306050619060512010807030827040501140103141b2209 70
    0x400300d05060018817800684104402549189405100c43c61820090003c01e405080c64030401100c81c1b040b04007510191030011310a42d510f40304550000d0103402c1138100400707000e28092800100b90043e02c00c07820800c1d0710404a071101c0d07020264428502c04010300940004c100d0000c480c4801d4843c1e80288412171203525042d469080c00c1c861107404000399008000d10b0303602d107181d08400d40c0d1846000800503070701c6080503039640700b808000302c045e0110500050415050210304810000340d8075500542410788005c56220000340301134600c0252084da8060701240d05003005001140041c0c0100e41c0c02440680042c3c10030b010695811002103030340c0c1c480d00c001030740800c000190b165540d807103600610000f0000c00c0c115065499800691243c0010ba2100c89000180074070040c4480d00c0010711060300500030499903035141840c0b82d00d14070000b402c60000b40b40140c1c42e21301c007200301d01190140b6040402d100c0003014007141103850b9407201e1043e01070b81108454404003001d19041c180040c204140c030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 80295828 1250 80294578 80294593
    0xf070b0106081801060302061e130f0501170601170601021509010b010e09040b011e0305030a0903060b01032a0201020d1803021e210d0207030f140405030618010e06040302 75
    0x44804811105900300300c05a410602e040000d650340c08e055941c98029040b144d421071501d12410300c1284204480410381e90303010700002940303141c2e121084080b0345080c1c883c0f080c0b6048916174000c848100716440760100d00c05065110200400f1643c45a00ca40e0600440d85003610030081d070700c5480b40c115200c2402360345500c0151299644a1044482160103a0343c164150a09a4541c2d004070b0050040d410740036030600030340e00c80300124680213000390f80100c00d4a560700c07100000144079540301c0c0000d49031641040221102c9500c20322528580b981c41e4009140e90f4581d800c00c0079100c2d81c82c16081c5046640a001c10319020541d48181c80301110a1156885400940e02e00030381040d06020207202c44a4460350410005400401c0c2411458421090030744000603c40c1e14100e54003400c00c0c2201401d04c003090101c10144c224164850210050321007030045019240300300801c0c4124014650581c00c40d4020a000e030643d012003d4101500d540081030b0000c90003019032a10008540c140c0041e0312298 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 80297078 1250 80295828 80295841
    0x6090203010c0c05030306060309120c0a03030606050c030a0f050d06090203100909080403030804050709020304060218040b01090501032316030f0501030201081302040906020c0a020f030102040e0c0f070b010608 92
    0x41803241034509400d02c400f07404110349510f9242d0000401490048234000000b0320f00c91000e10850242c0040e00140b03c0d110811811855a03c14500004a021038900301010840900660a030380501c524a0011882d01c8420001282e98031364001030304091000500511554980ca801100098808010016100e14208420248045150388440d59251401c0d0428011174620030031a0142d90f0103007801281d80d00c4a00d0b086150000a0340030002c4984044280170410226030000d01113420441c41401600003101e0800c070449503a0a40c00d03020403030403031003080b195000e50000185000c82400d071040c0c031022206501c8144204a0b1800628494004082c40d6250580f080941d018003548040000b5070540d400600407400c068640341880c00c1c200301b01c0c82155940d8000001e590b602003419905d480c06020810360781c40c2d1281e400c0b0311901504000300400e00f0140309840480d4aa0341c1c1c0c0751110348807080b40e4815680100401800a9402c1107404082044108402c1c001c100a079540f141500c1c3c0407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 80298328 1250 80297078 80297081
    0xc090301050a020306010c0803090f060708090d110601091107020402120106141912020c01090b01080705032406060d0510030201090b0711100504050301060f081e0303130317040609020301 82
    0x40200d480341d403040c000c1c058a031f6403000c4000801503100000311368a440c0c585405240101025500140d44240c10810051941c0104400c0c050400d038030441e1030410a20384280e42050b6030f424280d545500c10001003203654500d41000c50b1082026640e1f43c135082c525008182a0307845059000301111400c0300420a0b154400c00014034014200c031440c3c2032042e07082c620800540760350400b50410035003062801c08204141d040320028011503000301b10080300c5150a00007000c0900c103640307250040c5c01000406050201d43c04800d2680d00080c10803200d0701c80500141054064001e9410150030f009050b46001c991250364001c85007800610720451540c4001088031020742c110440041c000d010720342c0002d014940340400a2001c9500280116070341d0b10440e4140a243c3c4a50b5144d800c0000010301c0026020700d031800e42d4400b074242d90303091400140c8210034401d0200401060307030007080013480104041c44041d421034824035000b00d0900071011420303062041581c00741c810f5039580000c241186002d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 80299578 1250 80298328 80298331
    0x10e0601081902040f06090510091b0206060d03020708030a1101060603020702030c040b0411041409090c0904031b060507080a0b030601060c021e1206040c05041103010b18090c09030105 81
    0x1190000d1118401c5035054034041d401d070b800024007558a503080828455034a8001e4400392548210400484c91b0178502e8000c1c1600c24824146c440f0f00d408841c01105045281440e032503c0e55400078031140d103d40d414041c8040140324260118003c403500415003001c244018840c907a0103585401c8542140c200d1a800c444880c1c0c00070b070506204020301d0f00180c9021482c940d91000c210b400050340c8160401050142c000c4440003141c200f1300043c0403455540b0001c41d0001c0e01c000b690030880e1070b6100c880301d650300c0b6508047d40d0f50144011000400192260121009082034205410358248040d0b03036a5040e50810340d00e050104d801d0404000c8200c0161107640c03080c2108400508c0154505400030304032a29406003c1d00840c802441c01403070884e201140640c3c1075007d4081c0e420034080483c101e445810540f01242c50b01c00700b640020791454036000b0400052040030300649075921b400482001a480415602204800b420540b51035660380755409115412480400d0380c1c0d03040030780c10107084510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 80300828 1250 80299578 80299589
    0x13060306051008160c050d05120a020403080708071502041706090d05041806030f030c140d17060117010b1321020d050313140a08030702090f060a17010e0601 69
    0x8803810040d2400780d000f4540d50700309901c5100c0040c0a20200c80c2114415040c1e01c2c0a8814840c4040c146400c5600c4070082103a01d200341c03000c6450361100008141a4400c41c4005464403d0034010f12010418071402003075942c1c402c2c2501070f900003480c2c080e1816600513a2010010b840c217510888a80d6100307201d40e65000403110050410102c0c1c0000240c22130099004884008030840344142c1c0020003684000c010b0360b040042038404108070700d002081d2440ca400b0840c0c0ca40300c242410102c1c004000340102144e07145403109018541c81100522562030300804040c1004031841d08134014000760002d240c00b0b082440b00350f6544610011004880100c1c070740c866500400810113100010403603690801c040c5504840552400505007001440c601504440c400c0e02d00b0b07030b03c90004400545070700e20b40302e000f0162400d81c13149a4505065071240038000000c0c4d00007001c1000220107808113000642e1007030780280386401c03080d220801209098101c901d440c40d541e40d1008408107802c0204083d600408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 80302078 1250 80300828 80300839
    0x90812070305060d060c09030c03300207140103060e040f03030e0d17100f0b04031a15040b121902030601050d03020d0c080d0504050102090a0e100b0d060b1306030605 73
    0x207240e40456130400d0400005080a80d507850107051107803007940317000c00858118503207144c0241c0700e0030700107005484800741004901c0d8a0540c9078804244001c0901d44010540141220600e00b0000030b0820700041d84107410559a10004600d030021030140d6070041d030040499820140b8680341c0a8210b9141c0c000510881c0d01c1118843c441076130104203420804068900c06010b500c9a41d407010601d242c0b40c11503490a01c0300c0300003098400c03450000d007040300d006045415660211200100b0003120a68016600d66035045c0e901c011400d00ba080342138000c3d000307010901d40c50b41d08051f25050075501007000307108194655034001986000c00071076025100898040034101304984d000307503590045020880034000030500340d909004041064403221940c844061195160524006e0b000317520181e6990700c1110001c1e0702040210804209074880d541c3c07000304906c8203082082040b03847c3c002c400445504c9886403404581d09014001404a800414100c403108a08005018096407000c1c0c0140c4d01a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 80303328 1250 80302078 80302081
    0x1c05100f0308090f210613111905040203071d0306010f05010c0606050301090f1209051003090f020301020d09020a0e090606060901020a0215030702010b040603080405040b0d06090812070305 83
    0x12401100c0d1a04803079110848a0303503462201c000c1103e0300c0410b002c2e0390344041d50300f0ba816072500d04103c02568007802642560341e281e0380e51a0351360303003080349400203000d44180c49001d04050422440103081ea45102c1c4840e0022680e400009091b68011240e0b140041c424407851001c9501c80000316846041c1180a40405e40c10140b00c0c20031000b0b031780300700d504001050007110180300d450f50003040a00702c090000c0c01a02220b090161404102c1c000c102c1d80101000300380607402e8426151502919401011400c3d8a00355540403805401d11520035105060203000381d200580d0b017440101000e40308007401160445071401040440c0316950300c07407161407928608006e00000046949548181300311503503070f02c400c80302004074940581c2500003074100c0c2107822803600494010015610414481c4d000b071022600031703020710050b00c680f07100003807540c6002c2c0001e000915058110202034840941200610340c082c0d101c5d41c0c2a52104081a980ca507000202c40207644040b8400136401101800e003400f1a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 80304578 1250 80303328 80303339
    0x21002150a0504030e120c0307053307051603020111030703090611150115030c0c050d030906090209072c0d060e01180303020405090a090b1f09020c0606040b09070503040605060112021c0510 83
    0x81c03407078101a100c1130303500301c4040c1c440bc80b807c40d0549480b41d070030504661502c1c01c1e4002012003c9903a0209070701180041c186000c0340b000002c00c85040036410756803844413070310345807041d560204030340d00200d0680038200e02c280c190320f00040011b008001e14940d81c0805080841d020b81198400c1003501c08020f40f0340016000304000159607940c8400710301d000900c2d10882d0410000030030307184c0002035216800e24140710710385600c50301c000c01c5040c2c040c0100000c00011000103284000024008e074118542c0300850740420702940c40000e18030062400032810030031000b00132a44000b803c01c2100440c2c0d004c60705002909050601591002c2e0303a810822008501c1d486620418400400003e803804145414140045808130303108000c0075145006d6484035260400f181e200c5808951321401640740c404034191074a0142c20581c00768005494a03031450300c5a071102000351000500d0b141c1480f105000c8a02c01120903c020990004880100141d00903070034928000c0d500040c00301c41c241c0c8002e030701c148003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 80305828 1250 80304578 80304619
    0x603070f08060604030b1603050919030305060307090903050c010e01021c0209030c270901090317040309120c060813031e02011401090504021002150a0504030e120c030705 75
    0x1084801424410029528100000c15504c41c0350001440000304005200c103240f0a003045030501700c801d840038007a41e601c001d0002e42e1404030b80c0b11204d040303210200c110007283c003ea01c07003034004102500f07540da0346071507499400a4502e851400c0340045e40000d58010b00010a00c10200d200001300f00941ca003101d0f00c1d882d400103c221900e21180c442d03001030b158585540c108a16003413042e01900000322002154407105030039660b541604003a10342140040d290043c107105507010355504d034845250440c9030342c1c40c03043c0e4468002c108400b480070f01000404d1202602e020b41c580c0078404d06007a40c0050911900504d410009841480d0007030300a03104800081d000560600c08050000c560344500d12126400c90141140b0000942006005400461901d8454100380d10507070080d02c82da2a0f00d01140d908999400c0c0340c540d203541d60221007002c41c1d0011807507041142c0043c0240b602c40c401d041110001522a52042c10641080d84001520595820240705040c000c00b8212349404008021000a04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 80307078 1250 80305828 80305847
    0x20a06110102120a0f0f0203040b0705160611180904150f020f1308070501080106140d0905030a020604020906010e130b19080307020108181c030b030d090e0105060307 73
    0x500608409140385000c095041c1c0f05207411412001201c0e0502d151800c0003801d00d8402c076040e0504025000f0b40440380740c02141e0080da4040303a5510235642e881002c0303e886c7c0107011840034031203003010036501181041c050100c01040d4032103a1a918031001e0401c1164209056055020b0700900c820080410305494100215540710321010601c17081c0e01e0300c600002d225484513081c004c1d1022440d0000000c621420310b050f40e0700002290000c0d80c50300300565006c5024424071000070362101400d40289107241c05802a0b004002d4040740c1c1c0100ea9580c0d60a50300034a40c00c00040e4480700412042d4540f805845401032000e080a000c9644490f020403c00c0a80141000c140383d2079150b804200c4d100d24000e101e41c1212a01c4240340c1c182c03640c003110740300d07882003400b07a00040303240d000300700c0c07001c1150282031400140400420301000750381e0760140031010700407010b024141d80b880402c0e1070340c070300b4010348820041c2070b034070040c0b1b403410410440c240000603085240101414001c1200d010f4100c80f060f0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 80308328 1250 80307078 80307089
    0xe10120f020d09030203120108010b1003111303030c1101090605070201030513230c09010b041824030209130302060402011404090c030c081608060d020f060a08061804020a 75
    0xc5410044103040344040e1089503141200d06103807070f41400516602102500a0740c40803800340030785903607072120a400da50b5942e074071503071150010000e07081c0c10b07000740e11800700702071100070b001d0401c0d02002040786180901da10640101c2e49182c494004c0041c100444136009000f42800950a42840303001002c0380502c0304001d05040e552000300e095005d0b03443c8103110316680302009115410280d500b802c000022001140054814001e50184500c1c10522440c140c5d59289a031034101841c000340c0542c00c5607504d0315804c045039030700c049995504040e40440003101c0301e202c43c2c040d0289180705022039402c0081c904501c009400c0160382c0060b501180450f00960246070070100900c80420f0781906224943c81840300b180390000001c00c03240c00d6000003141c4285078545020a584030713101484040c81c3c02c3c006500040d0081c0000b240da20f02404942e40c1a0700240c03250240810300c07008549180d100e00c0c0041c002c80c40500c1044954501282c0c1050100340c200508140d0307045c80d50101e90f0001460182 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 80309578 1250 80308328 80308331
    0x1906031205090a03060c020d080a0509060721090602040512060f0402060307050f070309051008060d060c0c02031005090717030d0b04020702040c0f0f020a110d11100504060e1012 78
    0x19081c2c2d56681d00b240c01c080e5401030020002d4101400d4080c0da244ca9180c5801d01203684140051034140d0300e8401c141c42404400d0142041d50798051044412135002c400b003054040700c1c180305450800c018404c80b9901d40c804e0900581d1107013810100a041003081101121a500c21010081e0803419003001030780007076056030f45035102d032204041134880d401031800032005a00041055018585d101500c90102d45e01038424401f0341d9001d410440b0342280454150350001114280003001079025403081d400460180303024800181140e00083c200002c0d4240c2d003006680310300500c102090107008000003071440b201c0c41000c04a00d840e5103900d03401400315070318043d41d5900c039180c210340760383c0c040315842d5900501c10400c6c1451407401600d14030340d0496810004a50b110001111400051031015803030b00480444450810b510400481d0007035503400300c410340d89840000800c0d8846a51080580b042a00d27100d85590811000900c410303d00101c1a10034980c002020719030030340004034006005500f060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 80310828 1250 80309578 80309587
    0x1080f2a060f0307030501030c0b09060304020906011b0804090608061b07020301060302040f091505060303090d0f0501020a0f0e030304061418120d11010c0f080a0603080d02031906031205 82
    0xa51103000d98038980142d600700000300240598540d2005047e244036803050051980c0b142c49252650082c525070541190741000842c026160a10006a0049052515802c140303c240e03010401e0000f0480116048280810203203d03000c080d025000c06400300c0e800420701840c1c00b11210004091049945250300000100c40c1c05540b0290004800307103401800510a07200024010001000381100650320148409594468007d40b030007028018a030040056003420618402c000120a0400d000c9524402c2c1540c100700040c001c0c00600032825203525003246039911000003400300c03482d40940500c613070802c100502c140f40d004100d040310140d4220440da01d6100319010859510980c9038000c1c3e0100c51440aa071a03500006110104026550388403180064001882400d079112202c41802084560610721201881804500d5000c80c1d032917800301d40c032a40d030f0b00d50b9081070341701c40800d441440c1c0010401c440c501d102090960000c0c15503204000891a5480300b03601d000060320281c04101e00041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 80312078 1250 80310828 80310913
    0x11a100c0602091005040509060d0213020a020a02120106052803030503150a090c1808060f06280302090606120105010518041103060906030f0a0201030b1309050601080f 74
    0x2e050702c801d441c0160881ca041c81a100d8003030442e821a01ca0f551007000e06000140d901e04105150761001c0381d0103450101c14024481002c0082c1d04010101c5003144601e00c07201c1d0141c4c0d105500d82d01200141800081e015081c0014400141c64080a2424414525103034003421000768420100f1650036107001038894035003014030003401c15082c1c4030a5010b1150200841e040c100c40d40b081d041c032070540d15201443c40050511500c0d620540c8200c41d15a00100001002c180d031400e10706500040090044e80c0e540d400d0b10907854000040041c0c450450120340c3c0500031030502c026410b4024408548440c2031101e40d41d40c3c444c0c0b1040c140555410000c0c04a0103062030a007400003441c1030800180b0070721821410704108240398004460092241000c200850281d040100d00d4200b202c0c00361020b45441340142d00150040c1074246d407016000695164007005007801ca01c2504200c40c852400f40040c0e51600100d50b180c01500030304002e06400c191700485c8101149400b4242c0120401c11240f0400d0110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 80313328 1250 80312078 80312081
    0x3050d0207060b031c030609090f020415050901090507022a010c0203030906070b0a0c0504050303030c220602030c0d02030a2312070c141903030b04060308160203011a100c06 76
    0x7402e03d20f40520902e402c291441028681641d107034959aa0304001160b0b90381c1043c41501d69100e005010444d00450070405070a00740c0240000ca04000c1305131100f41d685001140b01800d00340d12403240c5070358460071710140f2941442000f00c2d1580000c1b01d071249072a01c1c0c51588c4058000c030301090603c13501850752003c5480038000e80f000f5400050000381c50388602d040141c28040e0444d4a010103514041078004068040d5050703805a600c0a0b00843c21552303a9041d80300c090b8081155106051900b017204009194071001c070300081c21603a80550b4032104145410b5160001c1c00d540f01045d9001804042186036000f2014000745c020301208030342c4000c218400940d0362107035041203c4110602420099040d42007412000320300e1094030700d4844503003044401c903180c0c06400c40f1000c2a2041c1d440c54804a03200ea085a61070b000300034400943c01d950395503440c00580c00004403d0281c51126424130540c41c0a202c0c0001200805115400000e203030000240200c1076541340b8424800301c00603013424001203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 80314578 1250 80313328 80313341
    0x50a0512070908030a05040f050306090703080d061802040305160b092e0801050909030705070506091f0e0f030c0d0807030c0b010b0706061431020f0c011803050d020706 74
    0x3c0410780707540b1030b000a80144640d01901803d00040712000000603c0c1c1400600d5a01c00d40c1c802001d4800d0509503aa02005507200107042e11035279844140102d0703004100e119114410342603241c01a40c0340c4c81c610f4418142075607400307034140514840d502008140905000c443d0b002008840f00c00041c0280c5a003400780c09154400040502214400165025049141241616400c85044189079645803c00d9940c1c441c0b24401865600609010013079400c0a4000d00b00e5548001c00001500400341911440581484200c1c000138001d100000b645042c200c40e1904002e00c260080e2023440501e1021402908008400601c070707500018981d814140301d610481074070340d0320850320006940c1d2843d040c80d5640150030203aa1162030200300080602566142154550003c1c210181c10144030800f00041d40102c010110002ea0802d042e0107418042d100070046003095012040e2a000002c11190131100035400a509628000c070201c070100c0d4020302a1940c3c809585400340e83e17080c0524100024061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 80315828 1250 80314578 80314589
    0xf0302040b0d0b01030b030303090a0b060109080609060a0b01020c09130201031104030b010503060c1204030c0c1a0301260a060203060a090f050402040b030c010c0201140405150c0607050a05120709 86
    0x1c001c9071520380d80920703030072081d0b5454090ba428810180b40c074081680360b10003910b6024899210034051400222012000ba5208205040464603699690740705030618401700c0318a00c0503040a4100309400307029100b4004880b40a1005080300484640442d032845030140140013500c6110f17110008580c801c1c0c0100c00700485070300751680c482d59685001c0c01961400c1c000c841c420300900000440046600c8242d800000848040030216203503a02e040d0b40010a000c130544010281d51740200e02030382810751031100c1503c00300e41c05a4a6140140030300300032081074001c040d0406e00944c03640e18030b01e000801e102c80540242c00180e41e500c03070400081d94900303e54040301d40ccc2401d00d15000080c00f000d42c8814442d600a071418411404210205a122125007485601090914a0110241d40f241c0d030b20340404041448102e103802c0d15540094101c0d0340f0303c200c2c4882014000b805a8990005014a642128050030814104a5240c6015049008040481869400d940001100248507144104c02000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 80317078 1250 80315828 80315849
    0xa0e1803040b070b071b02010c140105240301020703140a05250b090705130903110f062a030112150507030e010608060610030b0d080309150708070905010f030204 71
    0x82c0e403425080d4a503005400b0684110720400c2c00195400d000782041840010400c0320142890455401560021280d0b00c0964002c800d00100d10f640e803100744245402005102d03500306149425045411141c14841301c118002d034014000400003030b4010200080c0e618403001c0c4030b51500f0541004a5050041c14000750b9030b407075410442d090090b40b40c4802c281c0da502070448041c01e9600c1c5540565200350f14828a500210301030515001c042080d400003a409109140c60450310365400b401514103030105511408542241301482060340ba0740610491103980044e05011400440b140341c45240130502c13801030100000b41c4034404110307060308030141c1d0041055041103142002031000340188442d54940c1180d44c600f0a01140002c00000e50324418803004200e42c48240c4005400c40143c81d210140507040401e6142e0320001807004409580b1489041d00200300c03030384840705c400301d881c40d000d800b020900861005000391a03601c8464001a6002801c14544c1001e407900c08400a1080760322010340b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 80318328 1250 80317078 80317087
    0x209040f06050a0b0f0609010c02040f090602030c04210b0c0a21050105040c030b1507050f0d0806010f090605030f15040c0c060501050910150e0907020109031d0a0e1803 74
    0x107000700c4d030210261880a98083c0164101c0340184502880740d40700c80380c0410005088600185082d41200411901c903040200c0d500b1019541d06080c1d030070a94402198941c0400e0600c03203909144c00200b01e600340300c50401181401781d11100240235020701800c40d20440012074210403030190701280d64054880904680c90342e07030380154100420003130040a1041d03061a0000661521070300401009000040242c006e030b05100f0502d02e00340d03004500440b0390b40148112a41128800c1c0300c000188100794448000602d4a00c0005040e00100d00305c2074144943d481080c4255a88407060780c1c3d22014820b015a055110780c00400011010014115070284c02d142903181c0f00e41c3d001d07420007011880785000b40170a9880d03004115954800303c519403001c840c03001d0100300302aa2410303080c14007441c81c200000c85081d103001041e80a581140c0800140c0e454009a00401da4488541d2030021020a0402001c0b1320140004180c005076118544103001c0c0840410204141503600c104410800000c80c0d41c0d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 80319578 1250 80318328 80318341
    0x31b02092410050f0d091208041703130228060c14071a180301141e040201120b03070f0e0708090303010303020a06050702190b2406070209040f0605 65
    0x60a04812030761441000004003814a0306010b060520900141d8484500301300210040c100c0c03980141c007140c1c40351760302d400313124002c10281c042c41c90b4505420f070b0340c0141da0700d864284891450b4410216022410342001000000e00090f07a800b4081036044404a01300300c80d44099010030102c20700305c0000c2503516039001881580101d044011981314484801d49401170080068035582c6c0c0788150045e010213641d09070a0944014000d20300c5400280b1540f0758041a10042800c6a41400e95110340a101c1c030207014481d054440401030030b0181100095032450203600092210f50303100244154217403100c580f03d240d50340502c155406429840c500c00009076694089100201040ea0300c50b000c0366000020456041e00882102d060782c0d0141c0061803001c9407035032060006c240c01442d05046008607142d03410410b001e01d19030f04105010700d012a2140c00c08000d941e00400c0019080490740c21440440482a02c1d80c07070030350b40040d130101c03203000b1143e455090042c40000b042e44010b089034545400c01c00d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 80320828 1250 80319578 80319601
    0x40f0203090c0423040503040e0c0a03060918082b0c081f050d170c070303021006061e050c06090303040c1205060a20161104020313031b0209 62
    0x1c160200401c80300344001801c14801110a44022107008066654084585071506016140c10900c15001c0b20728040d0360711181c4401220503607407034001a20014421b50000c4d414054000a0000040c04001d42040d65280500041e80d0b1f40d0010040e40011414800040112921f6040c543c901c948100d03202d02d4020000700205001181d90000c500d05e100030400d2205e42202e500d030508a41100d002600b8140010071004040000c0129014014542c018441c148082d014101c078801180080000605503d0f000e801c148404800180d034515240302086503561110081e0b0220010440e030000758a03e00074115818802c1201d55884d6108400c10301c454008000011442180254222014075840e2888607941201e8550094100d5124001290700d0512540c4952001200201030110015603021060301c0b03504032600c810381c03007141c001810b0240800725180314000802100d0031481c503d015140350310a000307407810140402100905082c0d031140160381d000b80030ba0b0000c3c2402030501d4141c40000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 80322078 1250 80320828 80320831
    0x3090510090503040905090303061309050304050d03120f1a13020d1d0601050102010603020607080307020c090702030408070909050a0f0c0b1209011802011b0c0504020a0201020306010f020a03020a02040504020f040f0203 96
    0x38081441c6c40002030052201006485c001c61000b005040c00d0451100b01c1c60160a040e0b00584403404100700001d841e0717407166402e0030840d12a03219101d2540ca07003140f0b03400700d40e04800346030314140c1404600400418004c820100b4003204035011103006001c440e004000340141c0c0310712441c551400c0e0160342c00c0080c280c201301c10a507410381100d0060380c130340d8012401d0321824480203402c40e1007401042c3c0050811005550300c45450700c1120140300306c0d41d0001c0c122b44c00903134030540543c2000409001803a0244180400346c030070400207100094940d9140c559400241ca00039000070f48100744a806c01040c2d40d0054010180c040c0a9030722090300e010506d041010a4403204555840d100e51000359030400890222000d405071122090741c1546440001454020901150344004041011501ea074940c4040c01408515600042c1c403450b1050014211184c044100b0041d9400b007003002000035030000e50540e0f03066040c3d030042140e0312140b000c940850b01840300c5036407050421500c040700705040d034040d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 80323328 1250 80322078 80322089
    0x61306030c0f051009060206040308060d0c060e0f0d05030f0f0c070609051813060f0b03030304050d030507021504060c110d0807020c190308071110030b0114030f070309051009050304 80
    0x184d68084c80ca11056480006610904015800c10400107001c28050180c80303500c0300000e41560b404420690301d04180300c07515003044000c11415000700f00d05040081914004580070f0701c0010005546490300c80d640c1c0510030011030b44070800110241100062401d451071403080200b180c103a00e031034000141c03c1d01160b0080c01e0190103010300040d280c501d04030f082405442800284144c031411a25503102515a500c5000061a19581c03240346e81d4034104002c6125501981c080c05080d0820807004098920280100c02154800c0000c0410b13404401892604291300c5600000ea014050b41d090300c00b00c030b965614841361300a8210505003103030002210740c411400350b82945d02290062041100c070340554046030ba40c07803034020000d100191100004002d42801841351042c8240441d0002e4010600b0350203410002e52100904d48045d42c00c59042002000703412103003419450103046203a00381c0300c024025410503403030391100c2c400c1c0001404041001c030540f4109024004407820b2140e9284e0040c800e5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 80324578 1250 80323328 80323339
    0x402010f03060b090d060605030307060608150702190507030206220503010c0507030c080d0501121703160f111c090b0c060f0406020d020a080601021b0306061306030c0f05 75
    0x100e03411548248105070569100c1c0b03100a040c800a5403d02901c1c1510f8001100c0c0b45590701c402241ca40d4040003d08401442a0302c08907038203041c081100d0400c0e80242a05a1007180c0c1c40074020040e0300800c3d03008a01c1d40b41050100240d50704d052461411001e9400a50051000100f09030140143d858801c00c0204102c003a0802c5e41c0d950301814204c5801c2c000950025506020703100009101d010314802150141101900340108020100d045a1080e070208190000391500c52040194921180b0a00222500c515003103160500c082480d01700d0b0050403e041180007003c1601840c003c9030036030240d00c98841202c21f00e6152460641078103504440c1800030406c007000000d4200301c04230883e810b501c9001c000d0300b0281ca5036030b030314044510007400441d0385075001c0c0000301c01d02a080c805042e213118103594030119400c0803c0007900b0010022416400d00c500301080c00d40743e40b000201c0c02e421680603203214540c03070080700310100140201c2d080101221110310000540c07130141d42d000c001f6108110f88 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 80325828 1250 80324578 80324597
    0x20909060121020c0705040501090603030f0306050109090e03160302010f0e12040b090112020a020c1e18070c020315040515010806060907091206060e0108010228030902090f040201 79
    0x40d0340780e600884100b0000c9240007604a500d42543c1c02801003800070000b100d21440d19440000c050700c7c400d8201035904ca565020800c04d0583c8000b401c0f40344215400c08205840c00d000000302100c039a4011400d00903218150008111010070440c1e448961181c1c14107082600781c6070003030180101b1200140a1410148001c65540c004200e94000304d0b116203003130780b034603180400b1800c0c907410946005041c00503c801720a130040303460001301190b03449540580411003d485c200042c0001d2000c1070b808549500441c61003a07203130081c80b5010303030390f210380405199074030540c0440b01050760300300c0290503010f16240030051030703504001103010300e02c900192441003200e080b403050410001d100b40c1c0c0c40d41d407000000c603546003440e040d5035811a00d50300d00f25003055269440c000340852042c000b20b0f19299582002c016020340342441c1c5001d061440002d52078405011110b92108127004401c00d400454500b202c0c02060080c0e000b001c5040e8064100480d41c54244090340c86c000045506a020420350034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 80327078 1250 80325828 80325841
    0x109080a0615090b0f0f01020c09011d0703020a0507140c0a090e07080303040206030a050601120603150605010207060203041404180302070806070801053003040f170106121401110706020909 83
    0x10b0394981c0600a0140607003269480200441c40000f11b0b02c0c80d040d4060601410580d4541ca8000d9000e0916421001000440c1108150301640000c284100305841444008142548001151461034002410500c0f0658110096080c0300003441d02a40c410307100840018462819002200a28041400d0302d082c81e5607410095183c0c401150004d500220030030008080c59901d40c445030300104185420700159080c0358120007190259001130ba07114003000c01c0e0a408600e41d014240141800b840982030a42c82d00c1c1010f56240a03d001d4404002607038a88000c654886030f1110f1550381c0030600c0326585454906019448001038016021640107a0001881441c0140d000c41d040b01c0380680030201c4941554007100c0075403030044a918008440300055502d0340c0081010b08040c1c0242e21807000d0091410072400342101400f01c200748a41d0412100300410100d0841503c28030380c0105011556110a104c1c0d60f00401040145e6220b03441301064420a000c51a0701922400303030107484150b030948504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 80328328 1250 80327078 80327081
    0x201150915030b130b0a021207090b0415030e01091b06030902030c130e060906061002070b030c030408040b0d020301090b09090a140c0a0816060807020604030e0109080a061509 77
    0x6811000001d4040d00c0100001009080b145900c10542c01100000e00c201d990707041e8400700e00740c0b101d82c075854002c1603001c2c2283d085d03c50303250400f03107a090861403645010202100381c0668400c88805080c0000d0703000c00e59029401c05c0741507140b110000c00c460340d41440e100a2001202100c8200c43d50700340b0010400c02e00a00c42c458100d50020010302c0040c0721a000c002c0c1c419606c12505186c20344543c038206030a201000300a000f80d13945400f4003014546641880b140c01244824082194806e00080005000b04021a0b400c00d0760031044070380c0c1c1d590b11300704048144030b0355201a401d80400103040c94170203195030195040e40d601d180b040c40410381c00d07020003114900a0b41c5003106900440314100000300e203683e5038224003c507801510741d510500c1000940748a0594020303075241d00420848050504010360001c041c0441c1d003000101030420900003075940400501c020184008502c03000005d81c000c0081c07000410703100b02250000c40540c50020f0161000030000c840c41c1200c1c020110350560309 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 80329578 1250 80328328 80328341
    0x4200d12031b121a060c010c0305160527090a020904051308032a0f04091d07031e0b01080109030e120c0d08070c031b0603051905040611030702011509 66
    0x740d84400c0c10419805108000b0941c03d50313400152030b1300e0084029280c81c5c03d03001c0c1028501450001540c142c0341c0002034143c0700c0c0107040700001c07100e1101034001c554024043d142a261102001d05084014461001c0c80c1844194180d5120704440100658010150010203040505450070b00050701da407078140b1200351000e40004d100e14001c1c03000555080c0035400c010300f5250358003407880041c01c411501c3d01046c2d2109d030748607480c40f1000a090100b1a01401100c246d00c003481da104001514250f504d0b6100d4000740001080e0b40114684504221000f0a0011030160400324480d50703560f4038854940200418003045000c50010700e0810914546000c6c004103800f001c401030b04600c40f0540800a402a500740104d565280602c003800c0411a060100b1700038501c1000200382c130800d000701c002e034a0f040d40d174071100816003000e04000c030034261000c44010300e1132040008140d0b515507107401c40107400302910045031490040304009445038150071141c900403081c0c038100403c03078490f0907500903241e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 80330828 1250 80329578 80329631
    0x3030f090d02031201030311010603140304060818060f0411040f06060e09010602060a0b0d080a0c0b0c070f030807050c1204150203030606040b0903070801060b030a0b01080f04200d1203 81
    0x80d9001040448d00403003a0020030082034000041c40da03100c1d9540240c182c4610320148203588045001d120340c0c1e03080443d0641003540c01d045414007008030702d01642d036208000c10742d450b040e41c500082400c010100340741005000c401882070104030a820500001491a40b00c1d0100140c0e610b41d0441c01ca080c01c0c05030768140c4001d54040d212540d40e82c0856000f03044022907103030b00821040161008280030034090480ca681c5903645102c0c0f07900d00d044c03042c0350590162a040c0c060f001000a100041c02090f82c216409501d8240b806c0c407984c1e06482a140c9000314004403007030340694521003a1110340d000040050b20515001c0711404080c2c0034040b641c0b40002c4030b81c65000b01c1c080105100803035000000e00075100006044440041e00c45401d282500c0d490351002c24000408810711400141d640107000c910002860a204c461500e020850f40702c000144c400782507800d03944207004003003800000c415019903010340001d050300041d00d000050203006001110000f460003081c003002c1d02240030604101c55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 80332078 1250 80330828 80330857
    0x2b020a17060406052805061f05121003080a2a020306010506030606040b0a02070303030f0926090a08030c0f0706080403050c03040906030f020406050108070c170c03030f090d0203 78
    0x1500c0e6501c01d0021300014200400003c00c088220000000960502030490150000450305050803401d100c0000c0300054495000800407092150490f44801030340c12920075010061410f0f255070041c2c1c26520780c0d07604068024503001842a051a402c000c0b00c0c0321074107004d0b600c83d1080741c00142e0040500c1a01d04002d5050f0402c4004220380d1400101071500a18010421498070340e490f800005a079000b025041c0268203c14410424540c051041d5102c11301021401c6c40381004960b0b42d0800c41407040416001004480d0001d51401029010384001a00281c00c40d01c0a03916901516500e0b00107801c47c404c7c42c86a0a0038560410303021481500302c58560f1103000050b102ca13a4241ca0a800c48070881e19070340b03c02e01000500000a001d860002d5020b00600c0581108600600003503904c3c58001606000265050045082d8040c0340340c1503031a04844034141d040ca4410219040d44209109001c25200100c10301c20b00b4015500c0e1507000c1c004000484180804e5100280c0e203034081e04561880d0103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 80333328 1250 80332078 80332081
    0x50c1905040b061b0d020f030708090409140d02070906080d050f0a0c020a120311010606091e1203030203061906050a0e0103090f0605070f02010501030215092b020a1706 74
    0x2801c007074022001d61000100094100001c1021145100e200382d07a0080641d403140e000c5500140e0144543c011400407440554a40007181d21052068840e41c0c91f5103000d56035400c600400e00c48600d0460f141d02c6859800c0e40c0c50b5043d4001c0096869805003e0008043c3c039100c00011000c00024289050502540313a2900300544c406030344c81f00743c0103010b41c00c2c14031840c030509100694484510f41e003e460480180010b041541c2001080d080032207031051101e0385480010700c0610f8202072a00b0031501d0548103500301200c015011580490a80e1050100034296481c0038101a00358000e5807165000b520300049402440740040300040d200c0c8141703008074404101e6240200e02c1801c1000304802d06040103e108041c03a5103100c40c0040740d200980302c850b43c80c001c0c41921b60b4082100100802c1301d2000f40041d50654001611030045c1ca5040314920500144580c041e884a00c1401600071411038455120041000022500128110221b110b00b958100102c0d0744491a05141c19031040e503402460175 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 80334578 1250 80333328 80333339
    0xe01110a060c0c05030f0307031d061503070815010501020c0d0807020409060e0a0f05010e15010e0a06081b010206061e15040b0703030204050a08071518050402070807050c19 76
    0xc002d090100c0081000b240d80c0c080228008100070f110340002001c00559910308080001c04841440c5d01d011110f10407207810b410318480005040d170f0050000c0c10034040b0b011160f40024036000c000d5001012a008100e02c410304000c1e00c00c0901e04884081e002d503810840c00008001070b031002c0200082c40c48500303214207000360400346e00030542244981e10004024207070040451401001c07500484911003030201c04c504010080c001e6080c400c00510041c0b0002421165403010442c0c14010402940001d0340000c685017041d801513002400303c3c800365005040c0c141c0c8207242c00b04403081021b025114041c041015400c12551144020034a48407202075002003808020f1104585a44941000d805001c0802c4030300d015801000704900c42d48005030359614080900031444020340c051045600300f5401000b80141d81000a004a8041d182c99808440c2d400c5800f45400d403190031468216201042e841c04008001e0018600c0500800855600124000402a69903100c2015010090301030a08110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 80335828 1250 80334578 80334581
    0x1f1d040e0304120c030f0506040606050f060a0302090a0e090f0f0607050f0a03140109021b011109060a0908060c280f03020d0f02191403060303030f04020102031c06060e01110a06 78
    0x114413a0603040440341d501d454403095200f0248040c0d4075501700000b488108801071142c3c50061005484401d44e80806000240075030244a51138001c0c03580004034450165191500c081c054100080c3c0c0015905002880035900e644000c1060200d1284001d03007220b100700003903054070400c8556100f91400e4104002e00005400c000c0c00030051548038403005201c1d61101480c14084c01c0d00700401030300c51505140051800c01007021000069252000f40000800c0c06400c0f24076002c0f0644490340d980c5074401701111071200d01d600c40ca540b80034a9050148200751a0b0041c640c441416a020300642940300c01960403040c5240708d100800c604103003c01c0c0140c00f0b0703009490380d000883c5000594804e100c001c0380c141d034010a07480d400c03c1c09030441045410f41041440300f2012a64180c3d60851030320b400131170380d0303032101800740b5211a092000107000c44e0b208204407404240c0303507076091011080501c1484045e02039409110003103184400c204113503500c901c1c540c540c000c00c000020100002e10707031110070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 80337078 1250 80335828 80335859
    0x10210092103020c010c080709060c0b06040506030a0803041a061e01110304080109060c0f0203030c180d05010c03060303020f03090109140a0b1603030501140d0b061f1d040e0304 78
    0x1c060540901c0340254207482849006200076840c1c54201c0107240103a4000e24081094000f902802071403411080401c1d0100c1000e98424000d80d40019035450303400000340303810b685440003043c8600010400c000c225070110002542d06103072500385140d450702c104104035030a115084030070560040c940c00c440c1d58030880c181d00d00161a41e0a43c0c3c0b81c151a04c0e40381d400c0d12545c0006580b940d407612640020341d64030039040c52070340021388080c5066080502080c1f0b0180b140764004c0811040d224030f003401c51307699101090980c0d0303402802000703100032840d00540540740a01c02a030141c020b03040e492016010220032240001c105a480349461b90030048500b00c106040715030300390440a0043c010400404d1036005005907804180c4c1e05405540300d18000b81503d074140c02128001600107074003c05c0344c603000c603602d98082d44400c80080a0359034a011442e0340503111050b440020100311105041da1300980319144844114016051401056090105441205400c6100350303004000411210110004030b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 80338328 1250 80337078 80337143
    0x51c03030b030a290702070303030b04062c0705180d140a03090f05040603020a050603040512040b0408070b03090304150203120a05220209011e08030406050901021009 73
    0x2104000c03040840c1c07800d009a00111450b007400700342c0d040c4c401a00c0c0720a82010f07481c0041d204180c40c04800082d00c6801510004062503120720446e030030740d40d5580091000d00b1010000154020843c02c4503500d5041d403030406000030300b419020036109031082c8100d80c80596042032200c50080d922091014448108000391004000342d0484103046500b0b00c192304581d8026500d0801c0c2da81003450492031651a80d022038411032401d0390801c0180c4910304a101101c2c0c048541d25203d683e241062803c287c0030809203580718000040125007081c4440144c011b07119400e04460351252510520000c3c1d1005030703500b4085501c1400308000000d0b0042127441c0500c268410f0701d042500b0110138181c114030a030f901090382070701c440c200b20300c0071061000040c482c0da49a000e0202d001458010031105407040c060807281c04005140340d1341c0703105507000c000003c018940480760b80d0781c0d40d4600103005802c0242c0840c0140100601c100f6038291074043c2804443c1c104045a40350b03038401070240c1601b105103854 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 80339578 1250 80338328 80338331
    0x901110304080102161202010902030a02060304032f010c031406100c0f05010b120c100503060f130b040506010c0c0504200a02070620060c0a030204050a06120f06051c0303 75
    0x2c2404102800540b50340e40d00d401401c5030350300b914a066100402d0858544c1d003103a2508000300090790b03001031182e105030340580c4c0c1b8a47e40d440d982022590840600c48080b02d8180101ca005000b480420b02a40c20003403900c0200308a01107030070300710700f6101c000301c4040c0c881108402080c0360303240000300800c070390106041101000240341d491460346031035040c098965954032013583c07589040c0b00c00c4401c0c0d041d0541014000001c4c541c070010b2010011800b0000421030048000b40c10740d100c21004650354800204502e049110400016010b082507609079030156040c8030104145500924404408a501490504415041c0024071004002c4001700100c5498200d0000300d014084000a00100e001640503050550604030041c00702e081c0b07014900151240fa0a00078080400401c4482c0c1224070466420750b01c0c21811001c902902072500045d501c403151240006200780c002602100c0010800300038810392282a28040c21211640304c1d0682002042d51012503440f100c44100401e1482805d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 80340828 1250 80339578 80339587
    0x30103060504060b100c0605070e03101a15032502030a030c0e0d05030c0c030304030f060b060702060f21070509011407060c0f02010b0103181e0b010f09050f09120304050307120e040b0f0609011103 86
    0x1740115407102e81000c1cec5c104000023400009450602c815103581e00c80c58040c0b0110104c004002c1d035034440c01c00b50004042e640c02520b44c01d1407060710000b03103940303000b451404519042e081564690340005814086440340c1d100c001f020f401c0101c01d80c0c01b00d03900301c0402c0344036000c552960b0025085000030554004000c01801e0f00507a12100604042d030400306126031500081c1b007030b00c40c0140e000d40030502e18108107010001910b5000085500c50340382860700401c0007000405a0146001d41900180f90f40c1c242041c004178560301a0a50881014a500a00c0003010010054041300ca55a88030681450a4034421000c680862790038010a21000351403d1940b441d516030140b685804e80250110081e000403c0192001900880341c024a121f4280d0100e400e2510105580d403a80480c81c58041001000080a0001c20320545140381e80096000c0d000c1e0b0040c0320010329046a0720b5036507101d035107880c01e05415400c10090b542c040c03910280a1919000581c401036640d041c82c6131032010248030400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 80342078 1250 80340828 80340881
    0x10507080f040f080114060f1302040801090605070f1e03021b01060603020c011109030d0c020612100f0e1504020f0405060c0706090506030705030103060504060b100c0605070e0310 79
    0x1000b000244a56040c4035030703880c100660300d829513281480e0442e045040341c00f8082180d41b2840f0000103623004413030078224001c1c01d81071030010380144d50251420394a41440d100a0003041c1c3c100b07910031406076554032900ca1307422209540c3c41082001c0700880d18891001070150038000d5005040c480070221502c121005051030060075100c0b04d40000307000a40200d181151543c00b406864482da203016101c6040c0801c44002c03954031580c0d07138006010058010245010754850108540c9a55010f019010480c908803c1400341c0c50454800c0d2004004007060024041005400c00d44c064885202303161002c201e0141040b020f9003024203041d01d100b0741004009055507030100100118901400944211494050b0182904001e40e0056004c0e003420804c110b0340a5010301281e065960100000030b290f15541010001032000d40a0a40c2001d07078038800c440204d420091040c1070764031442e000c1c0040d41d60020b040f04c04511403501d0507015407140110b40004211a042184602d813079680e100c629003081e2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 80343328 1250 80342078 80342107
    0x7030906060302090415060506070f080307180e010e160203070204051f0906090b150a030203070306171507020304080712170301060c05120307081f03140115120308010501050708 78
    0x9545c12100c80c095101201c4074124039025200c0288402c8446a040c040a6110041c12202c45503004021103000000114018003d03072116075120750306035004604035180c0c4441081c0d003000f0300404a00c46544e034001505481c03821821403810382a076024500300303207441c2d0910014000180040d01c0c0000602c040c2c58412400d0400c5c003006058060021441d076150072400c1007103a0031812f8003030140c42039041c020a03003440c00d01113680380b04c024900143d417550b071050708500900254000710490540f6034a5060b01c00400038401d20440003c0d002440c09445010050340d5a01c0380344a800e4040d00311100802a164071101c205e004140511480e0f500038031484168200742d44240c0051001c5a001c03682c2800b032040403c0710070998400440c41502d1800d0006020f0004000104a1070480c19103061101c5401f00041d00140210b0b4011158003030704690341405c50280c0706070048800220452000080ea07000c1030b00080b81100d405895600326030b401d003c011125580b03c200c0948800b101000800c2c1e01c03101030b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 80344578 1250 80343328 80343331
    0x60902040501090b09010c120c03081b120c0c0a0309080c0406180f1103010906170703030e09040809030f01020d140423070f030b01050405010b180f0a1a04030210020d02060703090606030209 83
    0x4c9e03503600389200c01c0d4074014102d194080e2049001c82c0381c00a01000c0c1d518020100c40100000a0300015569150b80c11010f052088150901d943d008404000c010150050110000e40d26200282c402100b6244148402c0310110301c20b125020300d04001e14070042d03031694420b2071010490000441c3c100c1041d204180281d00a0380000d03101c65591500300030710b9041001e1100b84c8006103000e401b480e4036548008004282a81c0041e206286420200f0100300345003084554801c00681604d0980c50014403150003034001d11b2803109880d05010790201510568044240325075840f501084511469202040a800003040c0ca002c4034401c0c1c02010072160000100100110b04ca041c04038015814241030009552060b0703c5240054401e1214114990101d0140d4001c180b046d43c4444068255070006950b6243c0f585c003110015488040b00f842542090004006803070007a908221400344d42c01040b81d4412600d200000107800000c0401c2c1018800d40210f6080b0b8003902001c61099183d03000105c1d091030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 80345828 1250 80344578 80344613
    0x20c09060109031a01152d050d050414010b01030b15030c13030b0403031d063709061406091f030605070509100201110f0318010e0d03060902040501090b09010c 70
    0x1a500041003001c4503094081004081d40c901f91103a500051120190b4160401d6585807044100390302c1c503083da200b0740541e90012203006089c003490403e420014201d021400c040c5801e94204407104e00194006d004e00c0c421340301c025020f99401d1407202c00c81c1006403c060407103042d12608201711074000384c2c61110f4102450280802c020700e410302c0e1034054100e0b51310b0a14400005c90305089551850b0f008650583e2000c016039450b242c40070100d01c04140c6403901c4002e84040c150540d42e4843c1c0708170702d40c8600345031071040c942080070b900c44180c09043c102040752a00c2e8041e1300340000a200300ca002d4480902003200c00c1c01401121b8890b0340302015904d0071600e400010710003103900c0c90380d4500405180b9906029000821201c052100d4120842c03050035092240e003640000031840300c03442400e000070314008890003004014003680101d6190001c2904e48400681095004214130195208840c2142c80c16101c1801040c90420200455000090001d0611124080f9007011414001e83c1502d04003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 80347078 1250 80345828 80345873
    0xf070e061c08180a030f0303051906090b03061f0618080102030109141806071809050408090a14030c0409060f0515040f060308030f06030a05030703120506010c0201020c0906010903 79
    0x7903d500144502e0420030038030501c16a90200b021030058940302d0440c5806281c040b40b5641c2da0541c81c06940071512600c214107281c0540000c010002e84c1c044902d00c0000c81c10796115460f00d00004000fc0400c00b0300e441d800140c01d100f000a41d0040c0c20f082c0f91110054104000e8960f078500c0c180c01c9800036031000001c030b0713200c2d030045001408200d5440d900c0a001500d2154401c503c00d1115554480241100180074100c82015064254849800e00038240e03000b00340710b2b81c609441e00c030815800010405025018804020070302d8040c0003002d02c001c0401a00401001001c1820803001c0d01c4d188100382c900b5035a441080205201f68010144039804404d004984210031105010071076a481d811040d0252406c04113200040604040b2900161240b10000080d152040064145a0015001000717031200040010405da081485212000c2c4a00c204000696980e03005591408001038000d005030407042d5040810720703140340065045032042c54660100c0c3d480c3d689505018408c20314000d1500c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 80348328 1250 80347078 80347087
    0x120c010b0a0b0c060403031d0f0706030b030321040201110d2003090102100f0b060412120801120f050c10030906181e020409080d0203040506090f070e061c08 69
    0x1820400c510720700038984091610b2a084190181c903403a0314002d0002002c154482c1110400a480d004c03110013103409060a0300c044007918000d0540d00c0b48144103910109081071050500340c45d0200648246c02c0d02c044880380030350083c0c509810040c00c0200304030b0510030285031000080340c0420010700e0314a80c507101c00c030a40104030300000701d003140c694582c602d41e0300c108805040c1e0b990201d001540c0c028503074004222100741485020140c504031b006c541d04054085400103000c60076016200e01c03030740103141460f100c42c0314142c111007681c030034042c1c0d00701d0542100c00ea0700090200565405254054425100a69100000613a6110756001d0000019881d5070343d010074080d01384184086203071118014410444695034005200c0c2e0110400202e00d009203004000307540702d582084c0001503102d401e45503940c041422110007900f01f580c0a403124404c8900003002c8560000305400350740400001003000d10301c2c0c0b403108100810014095504031080c04020b080d40030a21480c00d42451003407a40d01e484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 80349578 1250 80348328 80348351
    0xa14180103060e0601050303040f0b07020a1a030109060b040302010f0c0c090e0a0b0108030306011e0306052215030203030f13030b10030302100204150e01020a020904110f010816030e120c01 83
    0x1300001038201c01d100780c00c01c10007040300b1001c0305040021034910784080358543c240b41c000a03100380d02d29840680760b130810348022014891150021816500c64100030400b031501c0740d0095425010b50b010082c04280c801c44220a41801a4a164040d62242070151a079680310920402a503484d51800202da07400049660104005a0680c50160801500039411803030210002068100039940c0d40180b28803101a41003218803a4115101a20b405080c0610301c0000e070715054280007140500d00c0c50a0300c2e01070359022030741981a042c4101c903002401141800d40340c09404089500c00c480b0602c0141c1ca01100100143c41e540185108000c6060082c03009440e5080c01b03401c04482110041c3c080344108010f01c550030700200f652a80c045285841720f1642d00b10350040c0e2600c9443e14000e54414030b81d030704104c100003070741d8485040501c0070348840020641e49401960014030a48a40300044451a45442180d100b5441420840400c030201c032510381101d03030340b84000c2d41301c040300f00803036515000058107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 80350828 1250 80349578 80349583
    0xf03180a11130513020d0c0e010b04090c0c02011d1909240f031511130612090308040204090503070f080705070b040503030d050702010f020d05010806150a14180103060e 74
    0x44449a01880246044d140e1246601d0000d80024450701a0200400030f01600c0042034019043c500368039a00795031034506180d501c1d0080d1180400c1c16041100c200c14842c0720356400c61850351b0686840400a031a4140c0380920b007100000c694001548103860140741000c0000000244480d201c006001c3e110031a0f0854804003940c2c86844540c40200108010b501080d102000c481c0c00241c84900c41d07250303c030700f10040d0507942d010528800e00404c2c020b02283c1213190308802c60310700d6201c148c56035030303141520b40a4824505002c0c0220790008000b5000d800c0c25080b0002075480f800c01c2d2450002680c1ea401c04820115030b041d00da401000c505c2e00100a400c03c17141e4060444091141e0a00b03141c08d0000e5601d2042600d12601141c5480106510307038000d400041d0003001f0407506544a560400300b0030020482480b54112520509002c9514416441c0799001c1c5100050324180341c0a040074414203039840f13041c40154200c2180c540c1503030700c0f00902003094044c52040c4404268803440e80304261 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 80352078 1250 80350828 80350849
    0x1707060b1809150903070605010311040609061203051e04030c08060901020304021c030e030601120605180c090415090b010503060601170115020a02030a141902060f03180a11 76
    0x50015100030b1000c400000180764030f4a49241c03103100507a981c4d9002490440c050904010b00d01c1d030070702d0008820400105040800907130283c44c01c1200702d541e1302c1e000301980c04c0780c880c820b10003d07085100c6021a21482c000c0c80b09889158840c0261010075805e024582e01ca54000d881442d01081e0038046401d041c0403203508100068005e5056081c65000103401c28036000081c900441c000c2003400406001d60b0120592010040541d0310b10f40c1d5481c039401c0a114002401c441c9103140c00c000130245081920300c1d100e01144200244600c41484042c0300b181440600306484041c514016008039804d680034040c03105103d01e21181144d4940000d040c40d10901400b070905000c500840c2d00703001c10750624002c2c1142c031200d42504a070340c6100416801c00400e00c00107505070161400700014003698980d04281c0c44801da0031140003014640c0444030060003000300a5000c542007107451b010b81c840401560f0030188280c000240381d4000050241751400556088035051752403100c0c9180752804c1c08040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 80353328 1250 80352078 80352109
    0x8011e0b0c031c060305030f1c0504061e0e030d0519090302010207060c0c020f0402030a0920010207050a0305030a0e060408010e1b04140105040207032726030a0c1707060b 75
    0x6011300c4d411962803d499004041e0401c90007003001c2040170030403695403080304210003041010862814141840c0b0060b2810b07494031005030b400230700321121809861044080e411801409103040030000b454400181101510055403040039001100000c4503c1c440c4007815842a0001a030755a00c40c80c1040696a0040c4c00c4021705c64580148005038643c1088032110b20740c200c0b0300690360360342c014454000317000c03c980182841c41035400303440710720014400c18603080030241c00311900746503100c042024400b100d01004125410500c01030f04000d0240b0454884803100900603410191100764035421101706003103150096005052800350181c0c01156080000400c4c0da0030300081c040c41c140101c0806041c85002d020b01d6000901800b03141c440d80d40080c2c1c00d80d007401c00012040c0306a81500d03030010980a4542e041448881c0d420715011040c0c800c0e6034048103000594104203002000350751039548035005891042c288490260b010403120300800038680324100001d000e0000c0c07400e0004281e40180071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 80354578 1250 80353328 80353331
    0xb0301060c140111040b0304020406090204060c14070e070201140705090a050613030609080406020c0102030a080103020415090c0f0905191509050301060608012408011e0b0c031c 78
    0x14000c0680c402029030140341c11000c0012261036040d119801400c1105544010b028040360100f8043c0300040118043c40c021078040c403a0300d07102c1401c503040303106500c40d40002c54100244100010b01e681130125258003a2416038800740e075101c0d2880d05440d02112402c0060350740d0f4a903403030403854030300015401401c1ea280181c00c0448410100d10740300030f14001e0074822400803030310003034803000601e0403006140e20100501032460b01d850506860b4016028940143c0980001c1d40c00a5200005603a48103086540d501071591a64003070000034076031a0403105403141e20f120041502000384c042c2d03040c0c484c1030313980e0f80d125070b148028014003481c0f040d0845440340e038440d02d907101d480b8560f041c48000e031904112403044205168000ba90280c3d2140c0c42103816508000000441e503810030711a5040300d1840c07c041c2d01001c5407c0388400550001641c0001052041c0014083c02e0144c0c11155004004041c4d0019090b48500c5406810341207000395040d95440058214800000c12180c0c1940d000b0101c070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 80355828 1250 80354578 80354581
    0x8160305040209011208091c020a06020604020d02150702030105070e040b011e1103070f03030c2d0e03120d090c050904030509060315060309060402120a020102060a09020d0c1502070b03 81
    0x9455480103205281d0000b100c03644000038007607821b003100d54110000b44400c62641c8502c41d649603040d4182e205a101e104072a400240041c0080b80c0c051045900520880701100c81da0300700b020100c000450010318580520801005803002d210301c41c0648066240c460440008204120940d0030340346101d0b04200c114035000a43c1140303a40c0c000402d12a0341412461401948000c03480e41c003480001825440c1c4a903800c00915415503c0381078940801e81ea400055188101e4115203041c04004560307005500e1901380c00039a2082c0380c4500c2180008040d18036040c1c02d0021562190448001695815910b241e10402c01000f0b0f801701c0001c041c02d84448280b483d150300c0c0a0040c4c0111034415003d540e0010000f11001020580e116140600500039626424864000e640d10700742120228000c0c80c5502c16078006040004100d060f09505900400050f690300c0c0e80d500c0540b03051a000ca0b00302da05401c58078005503220324418060400c4c402851281840c013980207140240300d0340074000d011000c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 80357078 1250 80355828 80355833
    0x501030905061603090503040608010603052202090405070f0308030610020c031005060a12050102031f0f26070b18010804200a030507140103060503030301080303180a0507060816030504 81
    0x1a10741e4410b070030780c0704103c0121003440c065001c1c18802100922a01000402150b515008640503040e14103da804204980d249612010803060b10104d6594087c11400d0f4a001840c010310602c1d802031192069409899480345000810059504101d400c05000710401415041036040803c0c101898030040ca060a000800b00b9180c04e455031444130f510b038440300000e02e69260301d000c040080107842c100780d14280c03135428500e00039001a100c00015104101401071030541030400c60082d56950103070700758180c0c90031a003204d050711202580d00200f0040486081c80c4101804054020440d41e82d80070b0f541c001e441115101d1000f0740c548981400841c0c2e0a010110f10a80e1140c040300701d2803d0304440c00700700400042c81e92a402c3e0310040c0366110b03441000c03404443d0b00760345480c1a04282c90900a05482c2c0c0304050b2240000d0241c04a640d00c10320010340220b625010041000d12500c0681e07856407001e45845040901541001012807800030501c0340920480890400000051500b0011400d066 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 80358328 1250 80357078 80357083
    0x3091e0d080c210f22030504140409080f07120302040b0909070c020d0c180509060601030203061302041202130903020709050601110a050c1206010f0501030207030e1e09010501030905 80
    0x28040c2c0402c0307507010480c070010007010b851000e1140302c40b540080f42881c00c03d150100c4441d089841441010010b0520b20311510011050001c0700d6158443ea0308060410b41c03040089101203010550150310f40210002207039241c0001e05d04400303c0402c03150344280c6828486e078201c0a10101d00708042c41048100f040003103c4054810100044801c01c40ca41c441810465400c900d0070f0011b54083c114040001c00c001c3c001d030662007140c040c0d80c199a0307206c11001c600f80c1141c01c1240c1d204001d801910000d0313080e43c446d074011640100e0042540d030f01c84d52204c117200d080383c0040e007121b90300181d10441d440c02c0d8a00442c1c40d2598a06500c0140217003036150703038001d455065502c00e05082035281c00110b100c03030b030082500300721071a103441c1120401d29850030401e5840550342c8100d40143c2c011300052210303020106210b41601c0b41e01203407420403803801c4011030095000c00016000c115107120f81ca200c0769a1081c2542020140005801c0c1a82491080011080040e400241450315140007000080c202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 80359578 1250 80358328 80358331
    0x1f031a0c041503020d1d0703050607020a0308040609081603030f0609230402060d0c0c060f0c021c051b0d02101506112103070201050105010905130c02010b0603091e0d08 74
    0x101d180c050317100e000c0c98214030060305000880031690401020f000c441c0b500000750500441c0e02035800c881c2c840e25500b01c00da8880ca030f9544041c00081440000070041000f0350404031215100740d00580ca08401c00b100304003020182c130b20860001fa200c40382e1600c007140c0740c0640c1d40600306088081003448100780c02c0a050400b1051800c0c2c5901c010400101559190710580d00410b00500041c011030302c1d2580d00a00c0300101e000c0c00c607102e0345070150700c40112101d84070712142918280c000340709a14a11824040f041c0b184003102d400c100d01002006080b0f4201200d1010030b00d419401448540c10b005400303400e020f1001c080841c6140762450081c014200d0b9005a01160594144000b03401e1000d10424208203040003880c0c6401c002c2001d548030300d41000d00440c8210010780c020005640c80b5801100d04060900c50287d0025011002c104800d43d40e9001e03001071441c40c000000c0e00c4901e000401c43c141c02c111030740d24084c1c01040307020350186403000c0c02c0b0384c500400101038020007105a0005d80031580 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 80360828 1250 80359578 80359619
    0xf17070507030f0c17070209240913050a1a070309031409031c0215010b160602030606090a080c01110f0613171c180f02091f031a0c04 59
    0x40b01c003d141c03105010f0480381407050b41203410548507807100d00300c44400e0b510403142207001d100d1690005000780d10603005a0544115203403c142d40c0000c1c003081040425016000207001400100c00c840010401c101410529110780d03840383c228024208519030300c68008145200341801d01e04003500180c1d0003128260180c4000d0781942d00d441032140402d01d00fa00c2c0b00c08241d03400c0c0f900405080080d40000700d28040d8950206550642e0382c80f2176900f0010f01032140d4035085444800046070001d02550051a40507034090308203401c1c12113010000b0064055a03200e1400c90304907980305211940d00c89841c4000040344030007450b00444080d102076480c1c40040100450b504d0858000d0104695030310344003804440540703100d03218100307105c044851010000783d00c00142d00e02132801c459075141c2c00c40114555008050a8101189070f001e00c801110014081846074280382c211405000c0310701d041001442c0a00008140c4180b1091140700d0100081e04100240e0400c1c070042207050001d241c01c501106 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 80362078 1250 80360828 80360837
    0x901090510020f07080303060306011e0312030e01090c0608060d020d0b0402030304081e191a06060d0f05150f030d031a060a020102090321070b060a030605070f1707050703 75
    0x81c10450128100194244482c11030300840c04001074180317000001e9802024100c0c103454041e682c4881c07074001520081c41c0ca0b103e001e0004400c1001c6004d2030101080551141408607881d094021007500b1100115021205505070b08424003140e64080a103591109040e1010142c0d8907103a000541400c800e01e80085c0b04107540d070f000404545092055400074420b02c0f0441e10380e4881085104a8210129140c4140d4412101029451100c141841000300d0304a0209150695030700d04507802d040c0700070040703078200a040046410102031445403000414505030005001d09202c2100c58202400c03044d0720380f00d543c061031000c90642d00462050100001800c0004030701030301d44000041800c031b03801000da000e40301080300c42d4110b0301034005044680d001c800b030f42d6044c080507070f03090300354041128000020101800300500082c0f030410965000705c0001c180d151001c0e07881e903c0b41d050f107000b2105800001c0369003800002890304030100802c8412541102c1c2940d00c0c00c440000c160f4000c21a0150401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 80363328 1250 80362078 80362099
    0xf0312091503040c03110301020f16050a120201060905010e01240e090708091608070504020a0e030601030812010602120304030e010e091f1e090213090504060f060b09010905 76
    0x1a514200340c82072420002002680300d1503d030800c0c51520051344000e551102203000c229605107018803c4030801000f02001c1810518860902088000c5195044a0320322803011060089900140c2c0b00502904690003c07a0103030521521038141e0718180e00c5101e02c1008000184042c400c00c50741c10103020742c05540c0d014400d6951400325080c019090702c0c0c0303030000305100134000340a5200345c089119060300000c8802c1e100c122040c0004040c0c507803040c040141c100080521580c074064000300280001440d1002c0c02070035040000c0e003010070a90041380c00d13840000341620200d20460b602070041c9010300140a40914050302e152452100400c003c081101e02030030200a42e014011300c5410010203024613040340b070000031a02c80200250b02c0030034441101400003c080c3c03000544283ca003504d9842140120303203811150300288d0401d00c050f003590304110002040c0d100c564403d55100328066003001c150703c0324120104003158440d0300925400c090400c40903070166080040d00c800c0b24010b5a00c40c400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 80364578 1250 80363328 80363347
    0xb01110705060f1315020109031704170c01090501181209060806010c0c0b0703020c120106080319030b0306040501140a020909040b0c0c0f03070c0b040e0c0a03090804080d09050f0312 80
    0x240102e5044143d041d98550060085c46a0540c84004c103103210391903030180050010780300340510200300d43c01421340d8048218100181400c8001e40709aa0030304001142c3c0b2400741d55180d007507813454554481c80590911500d0240864058004041040c0e420100380a6042c24401006180010700300341c1031241c2c440001040081c1c4003842c20052000078030240d241c00007840c00030749444440403840d1140d503008020341c8034104184208011150107a00440c42c040f50240217600c8e5208401e05003041c540d070744a01e0f000d103071400d00038644140d103d00000640303003510b000c0aa418920160080c0c202520600044400c1d485446c1d00d25045504051000295940c1e44240d803801e02c60100b8250701070040030120340d0290400405480a035101b090107000c0c45071110706e2190135029500c643c00240700c0c65800300d50020142801001a00c0043c40d0205a40480d0345803204c5030fa005510031f04507a0701600c10030416035845141c2001074001100ca0650100032000041c0e625580000c03501002d00313000a4170b002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 80365828 1250 80364578 80364607
    0x304031202220b030604050a020a021504020a08070e10080312221209030507080303061c1b2301030c05041a0714060712090201050301061b020a08010b01110705060f 72
    0x21240051000b4041c0ca84402031007005402c20758801d03000f00d080401055180c800c1c1d00a0320300103103c0303034010003500c0c0c41000280d507008005041a81c04c00b140170000304550300180102809440c01d00590001804c002030200d02502030350303000b80c1e52500140308000c4403103105c44449070403094250420b40200c00d200e64280092402980041043c1e103010b0a20071019089008081280d0081c020348051580da13210060302ca101c101c40b03607948401142ea1700040c010703640d41e0b80c4540500070f42c01c45084901d41c0050030008501d07504600b6881c3c8082d001162804020f0b038040320f25107403c2c40c0031310154014950161150007a80141280c054050008840000c25401030321364a64100c0b8921052104680081e9281d038410b441c3c0d4000140760508a11010380203008105402d903040e502d507131540c4c0c07810074110b415812052a013100300c030700d20340c582000da07440380c24000141c03082400000e14115100b0014102510390315040040d60044001040150f5425042c0e40c0305186500007540c0d00c1201110504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 80367078 1250 80365828 80365867
    0xd08040317070e12012c0a14010902100c0f0210141911030711040908040509040b150a05061b0109080c0708120306030a03030906110a0e030706050304031202 69
    0x1424072207404104007554449090703282d20b00207032916032110030440741d69401e03601d6140c030071340d14020709800388519010814501880c81c1a81401d45512500542d01c5114440c00c00c0140c81c4980c2d16100f1a1040d480c03c0c1039483c544005034240490303104542c0d44d540028142a82d0082e1144200ca05031090450007075400c284c44107440039086079540b00980c559903042c2160064500011084c10030000148400030440704c03103e80001002d84070000300001c000117040f050030106c40301c1d0018440000c0f01c0c0c903001d080900940c41103401c25064a004c0842c41c1c014a600040700c1c0c882d0442800411060301e86a045448450030303e00310300440300885443e01e01601c2464030040c01c214001035003042c030400200e0440140c0720900c05682424a01c280201070034001500d40f01c4c0d040c0c20030450030b80020b000c1d5021454480c0f04a00101e2640d05807880310107250405d540c03210104520303003036941283c43c05100d160060b082d10306005c1c1c21414a914014014104004845c407101e40c000740c2200003000a05400d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 80368328 1250 80367078 80367107
    0x11041b0c080d090309080f0d140f070b041a061f1d09040503030109060f150804050a0b1005090c030c1204140102040b1804090302060604020904060509011403100606020d080403 77
    0x24084100f1524000300003a14610030b404050050740c3d408a1000d1000c554404504000d9440100c6541c4000c0a1005503003c008407200100d000c10112002464001d00f061080f40102000000741103a411900c0c500f94005240d1440b84103940111300348110010031800e030404142c5440a0820b072680510001f0600306060f26074000c90030001c020821100000460507a09481403d200f070555078034080c00090098021040035561300c200c01d02045d4442c01038164070501400403150a499070b611040d0703a100054508560320010104140314900301030040581190500c1d12032031840c504810703c020140100c0c0000010301080a000c1004d1085900c0020040c02005001315603443e40c50502440592104440d00010f64220411a18510b4944940c0b40c6c59501a009403c0381d1780c0300307020400203512090260740c0c00380d514a00880c0d1030711560100e40c0a4601103a0401d0b1000088040502c1e2462000740b88078054207051003840503e03804208022a9081400d081c11140c94030701e000d6920360300d004680f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 80369578 1250 80368328 80368331
    0x9090b040608070e16030b0102030409050c12010b040f0b07081911060a020405040c081006320a03052202040504030e0301180b1803040b131a030411041b0c080d 70
    0x3283c03055000d4081401102030040014407402a1172040c2d040c2c0e44088510760160300284420480c51010381c0100da4410f03500c05d402407400e42d2103401d140c94000300303130000504030380d0200f814880b4030f9811481c0070240c00340d1500c5074144807041d90785045520400c0b500c0104456450b20045103d402207403c0e466494a840c141c50381ea29003002d00c40000e4010b4491305200b507040120450005000f02c04003800317090b40d62280801c0e581465800e458a0008041c101c55000f00048001d6100c0418034142200c20108007207165110754500d0f000742901c001034800501d442c0c03190446104a80b503482014541c69054030085019a120704042d6203220b0100d41007a019401d00c41c4084a05a141b000e5184542c4a5a0301007020b071201ca00722600480f861404020a502c20482444088080780241c0070441542035407039842a1140c40d032141080c2d251030b00c846152000b105000030048500c0c4c3c0101c012a00f43e40c00c00c444140c04400e0000c80444103090750a01482010803401e02c90305a0403514828020740b030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 80370828 1250 80369578 80369593
    0x30303040b0a0c0804020f010809120f190806031005040602070803090607030606050f090d0c091103070906030b0f040f09050d020705120601050d080309010204090f0e160609090b040608 81
    0x20816409002280ca03011682d14208080f1150743c0224800c0740a01e070050056801e0020341001551003040c00351840040d4032502c101c240d40361031020001c1442400112045480b13030f0003003d004c0460b030261401e000030300141000b0403c0c50f48000690800344000307201c01148944803401c200c0024400c00c1340141000000000300403c46400207541030240d44e107640d04100f4103941c1e500445040c0120000c1940e29107040126086505d0200c0c3c1c9c1040060144d01ca82c2a0655030314064800c41d40c0c140804212a01e011041100154002d11204010040e030708007404100034020002cac0082c494042e105100701c1d55415041a4252a64000b2a40d00d500c002107514642201002a59030005440755a101c2e20700c002d00a4490b003008500a4100c03000a48181d800d06c2c0b89968070580742c0c00003040b0218940d401d102c005841441405000c20340881c280001640c04029003050b03090030303d10b5046010400c2c4c1080208005913101c50038004443c204040040c442101d4030004000d03000d42c1c1d02074844c9110380c11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 80372078 1250 80370828 80370833
    0x19080109060605100e0109090b0f281a030103030f03091209080717030702010f050c0118121e1110050901020d15030c0b0a09170c04050901020f07110f03030304 70
    0x41c40306040c0c42c3d0403915400e4110250300200d441c265000010713800100699001c00a03840590041c0c880310b50010250002d11100001148502d51316103003040c003420b207004940300c0b401380203400c803005009903030b80f40014046108a280b03100c1c0700c10720008080042c124500b0407424801e50011040690040e000844103601c0d40e80208144194095000740d07000740b1400040b8050051401c680c0030307003450043c500b4407510350015503000441201290502100b0480c1700440b0740e00b0700c00d08040b2803000184101c5da00300c600309480c0c0000b0000c180c405100c03804002c2588582d0440051005c91194681681d0f1000803a01e00da0a00d8840001406420300305400d200c40c1c20019006403101c4061020200050840e070260b04161841900c400b074602c8a0080d024040c0c04440001000ca240ca6030400b22030040c0c1c0ca104100006142810315030f00c5420000b5640c0341071819004090300108070707038000d50a00b16400400d030300502c0fa1810050501944854410312070b00c2d00c00c400b902154000301580d0300ca20707150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 80373328 1250 80372078 80372081
    0x30807082a0703050f030c12070501020909040c09051b030a05041106120603061b0708090a17010203040302010c02030918061305090d030e03030f070503090f19140118021908010906 79
    0x3d000c11a55401084a4000c0c150400400c1e00c091810070001450148100c1c40a000d0a80c044801a640c9540800c419410350715100f1440c0d009922420702c5090107444e10071050f04950002d0303c050020a800ca0081007205440c1041d40c0e04070894150000350307030315a40380c806421000005503540002c800f05586202e2142540300c98403440303041d016545150394545900000d01842d603841c1440c0d000600206001c102c3c0d940207032450410282040c101192140761003013000c0060084140180e400008102c205903081c011142620b08a00046003003004410002c1e00c01f4801e01500d924505c660740000d00940d9a8041c0d42c41492200b440c100003904011200c19261151001300d800820305164009900110000403039109003a0401c0da02807030348910104071415400640310300d0310b43c0300c3c04d101c02c082c100090244816007030512516a0240b40c03640b41002807003000804820f12645450f901114140c100c0803414601a030450742200110b03d4002c3c070400f0187c5030780081b4515803900c84650b04004a6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 80374578 1250 80373328 80373343
    0x70c140109030806120601210602042c0906060d150207030807020d0807080601030209120f070906051c020402090307090e0304060801090c02100f0f02070822030807082a 74
    0xd03520300f50309681d02c10521480d54224241801141d00400041256121880307000342251241541041045616142e05050b40c02540206000b0320034030342110704e4403844034007200c221601080b158000340f03400c046441d26417400901c000d0083c55002002020400d242c20340002c0f060802c2011074442041e420003c25040d800c882010144c45540d03a658134450064605030310958855640a45031380d64900114040e400a07602150060110000721051075000c1c800c5181d01d107060002042d1381480d2606040a5401d0b40c1d00c210300480c4a05414000700e580350b01c603056a55015140581ea0f110300801091070007010394040b50460703242c404404080d40c000303c002d00c115250340c1d03503030f0321242d0705d0301810b4080f181d06145800140c0c0c030054141c5148451030708500200301030036000042c0422054141405ea17400107001700d40c048000200c0440071804500300e0030301a00c2c0e101c20400071504640d2000307440d04c109240540414400b2400c000440c0008401c2052050040c0e121010306017982103203a0745140c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 80375828 1250 80374578 80374583
    0x504060506010512040f11090a1a0607050709051003150207020f040e0a1b09020414030d020607080f0604060f06030b041b0f050f0c0601030302072904030209070c140109 74
    0x30a00458010340c4248251840f142084080151640b40d0f591402d04001c4800e20459042d0400c54174800750780e80e99186580320b4000300101254641c1c44084003102d240300009850320401040c461100819000203043c015a00e4400e030008080e01d42ca032000440b4a0250300040c151228480001c02c21a09a00036212180c42070b01c00c01c642484680070001500e8004030301d03060343c1e030041c440080400d0102c03440d000e04418160b48a00000e4542c41c0c1001645d01c030b600107600441e0f0700c071041a0346040070400b00b05800840c1c0301400301c50030050b50050042001a29120f08103100078040f9055981e240e000700014052940902034240c1e46580190181c641f07800c07c64452842d16040c8403001d0050766040d4202c031440e03902d540704002e2105041d80c0682145d00c00d650b48081c01d110f035010f1004100581e030f0185001f80c0060101c1458032110310500c4a506800350394000700300440128040c0c0d5502503c054a0741104c002c41e05a0758a001101c2c0101d0142000c1c2550b5070b1001000d00c1c07004194005a003050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 80377078 1250 80375828 80375831
    0x30903060b090c030a0902040905030a0f0206090d0203041e0519031401090503190203040e0711060106020304050a030f05010f091b122312030403051309290102031606050406 76
    0xa50110410018442c1261035045601d02000011100503032079002d880b413544001e0001541c00051380300e848c59a002901504c001c80c048074090300e9010740400c60994081740c18002080b103425103000003502c0740140c0c407442c50f05600c0c00c0342d1406107800110319100500b0010301b18440c03040d440302034403110710003502c01560510b21020300c83c0580c134018007985980e20342003801549044170f100540c0c43c00a50840b00c241c00c60105220100341e00c1541403507140544500e07a11040303801c4144c0c01c0c040c100300040c0d0020b001d40d88100002c0140340c9500c0700a4045035000781c003006802403542006400b5015081b14000c0040c81c050105040120307039200101c0c09089609030002680e1916200d51a150034400054005d1958840e0301c40c106038002100b06c0303400f004106440e0311480804156134913030020360b41100032800109010010b9444244101c0044c41e42c0751003131052668040c81301040800c0301d00003c40512101c1c0724206180d008100716210420441410034003041141800c100516050b14100c5029 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 80378328 1250 80377078 80377091
    0xf0105040b0c100f14070806040605061602040c0503040c0509040609080a0206090c1203041703191205070c0201121d07030602130602010506150c0c090a0e07080d0906030f020409020703090306 84
    0x3105948030b860001d84205c00352000c56120503009450b01c54000f0a4a988961980c002080301d45950014001c003186000b0f41c1d0340384415510401c0240d03403403446a0703400c2003024410400810102d4000108441c002d699450307039516039003460000f8020510b8050b01030503000407000100e59001400031304c280e032400140e40c45070441500308442a04003215804c0207034010300081c00603c1c7d43d5003451b14105100c01c112850300446005c070015248800780c5030f00200310800e40b07480d4034042a00660b5403000d068036221810404990018003a80400590079046556414101c1c214a92260055050820604c2250100e55803450100045c4d07210300f08071100702c40303442c00000b105401401024001c110040c29104101c40d20380da01c40460b08100e9200b210343c480c0c2880c0101c252240110140940700b42000410b2103541c01d00341c00e16001301030f03112004175070103801601400e69020b02c400c1c0580b0918070380403030305044811495002e40200e40051196500c0003821000b0980c102d000b24088a00c544001e0000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 80379578 1250 80378328 80378351
    0x6080403020606041a01030509010603020301140a060e0c0307050703090e10030303110f03011a250209060d0206190309050f0604050f0606150d2c190c050f0105040b0c10 74
    0x544001041700c03841c515040759025103942c042e030071150380f01902c1d600005269949070000790030341c1c001091008021741c0160070701020004c01c2c007448015210900b040301290030141205440342c07200a104074100480403941204040c0301c2c02c07500d4000c00140b500f00c0f059007800328440903013451911045010a24002c500b003c0890042d050b586a02140c0542504682c0380c1001d03104400b043c1034040c1c1164208000d80406003075030440c002508081e105103282250510303c14031105900140c007051280b41d0088644006950740c00c11a00303200c0c043d00010024182d0400b040d00941114140101140528110408203a41c0000c005205900620444040b03405280d51940c503401c0030340740260442c001c001a02c111a80c0310005240f030402d031000c001a50060703c1100d003140c0c4a1503210032003066900b4109088020100402e002c00e95143c01c2c100c11940b21503480e6000b0401a10550380200c0c021282071000303a0080098400521881c400b8aa58014005041d41c4500c00400d0303900c030302c80c80c20210954 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 80380828 1250 80379578 80379581
    0xd02060402090414030c06090a0c05061305010509030a050601080307030201050f07090b0a0504120c03030f0e010c0609050a05030f07031e2001020f0708040509010e0f0a09030e0a0608040302060604 86
    0x25a000b8007000002c0e2501d031540c8512940500304900349100400201d02440c40811902c0d2190286001904a010391417511251200f1664000d500c40e02c02805140c0b580440b0f012400111403090900e6981e1f880008082410504100c0340075000340104000003c0e4903c1c04002415400e100e540200541e60f558a810044410b0544030702001541d24032051040741d04400043c95403110b58100741d030a040d911514902e400014507011a0700208100040080641000700235002e081e01d810441454041200000c101c25401e44015001175154803a000c00c0c407405001090382d0380d422030150b0b03945113280300d1010351300e5103c000c080b0002807640c4842c04114204070500908000e155881800111100c03108040c429000c00604c00d955508100c11460507441c20000d2210500c0303000caa45c3c480380341004201340b01405a1089801450403002c022906030480901d0b648181d5000707001480035800d080444c0c21a41d21145c007900080c015601246181e003001000d8401c0c0d10136803c6400035580c980c107110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 80382078 1250 80380828 80380831
    0x3010f02040f050901030804030305031f080c0a0605041406070215070317010b030f060402070311060721020301060512040309030f0b0105040f1a0409110301020403060b09090c010903030e0d020301050703020c0d0206 94
    0x18840e041c14070049c00000c0c032407001980c1100301c29080042c00c00564194024501d0580d004201540c40507a5088150600348100002800710741055810545024a112016199104460300c207580c0010540c0c11540c4660145641403035040500f61960424540900180740c500c41d030354400c04424000007000c00380e81046911605e010f4078040c0031070301d40c201071101940220400f242806101c0444e028802c108000807803007071050b65503a6038883e443d020b00c000f25032080c540c1d80442c035004000602000340c00004480031440c51404540350b0359180d080c00c0f84c2079041c0b504011705400f0b280c10300d041408125401541a15800c41d01004100005480c48007112000b591684000711544001c00c0c0500e41644044075141c0030382d040d10304041200b000242240d2154000b20740d00765407803002d41c986061003881c2640c429001300040186070040c400103820340425100007010003100300300140094540c0c1d01407003c00760b8050028065800c1117103010b4007a400c03503900142d00d4880d09010b2480c0d1031000071080d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 80383328 1250 80382078 80382083
    0x309010912030c0312020d050405100b030a0803040803040302190320031c0203090309031009030e030f031e041205010606030b15030114041d160501080114120c03010f02040f05090103 80
    0x980e4030300f159580c00c1c1c030140380c0b89a011714425400c1c051207003c49071600803680318a110b000500001c00081c2000350480394581030301802079000c0c14226001440d00d50441c0c2e003044d000145543c40e0f40d22840c0803850518064818900100301c514004d0415070841da541001c5007008010b0b40000c280b140c60300356130340200140301c00002d089503c0c80d8800c0304144d00541d0841013080c2920b14140391640800e20b0b0003010078500d4503050b030700d026010925074440c0564480d0301e42200075041036140003031107560300c0c05000020108194808104120340d13001c4801c41d03000b44141190204081881d05105008000521440380400c1c10704a06106500c1e000441e0078000c40400099802d5900f0308104448840c1d409030031641159650503111315102048210315803410842000380001044203400c90242c0c1c40380d500140c180000132005020007691443c2d030071b40350002620b407220088075111001d45484102c46c5125015441c1079041c0607008031980040c016101c1c5607581401666581c0300340195a6000d1001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 80384578 1250 80383328 80383337
    0xf040b19030c062c0103020c0717010b0108011203080702010915050906010605040503031e0409090c180c08070c0f0213140c070203060c0a0c0c06030204060e04092102150702030901091203 82
    0x22400e0402855511302d5216078185401400c14042031004c601d0004580c22810240a0444404045c0d040c2400b40a08440782880c10740442e515002c1c0e2003007807144488005061003665400144003a100754810310700079821100103141e9200c0700ba5504024134080c0c1e1011280d024040001ca9458040c408075000c80d5000340c003d61a1810300010080c20415038a1304c1035040d40304000000b10310196018080b081401404c502121300e2414007603052500c0b0f402140254039040c0703241207200c2600f1034902584410f00d030602140000c050718110010009030900250b120120004031b25015840d50300c105a0050f0404070545a92640240510a130088005c0254958817110001d4034401c0300c1c8001d0003405903681094111000a561140c00f81e00d4250800d0000950108003045402e80c44a100d42001c00251820003580c001c42e00c03010b140705244907503c041e851049501c0207103d07108204800c007002500755141c10504103014001d4407035204146460001c0e103450300205001000c00380340048564507403903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 80385828 1250 80384578 80384627
    0x123041103061012020d150f0e0c09010c02040c11011802060316090305010603050a0204050c0c0714130504060533010305100e04050a03090f03050c0f040b19030c06 72
    0x1c101e521120f91800904101c3e400205852814042c009441da0800c0360101040f03c216002030b4000e00702a40e80070b0b004400214204011051035801310a4202c50701503100c5545004c69401654031148800000b50020b1501282c0d026496008003164018a0010300070f200c20741d000c130100c106207100010081d40c0020200041a401905501c03840c500b051141400c100b52070740e81d12454215003041d40251100d0304100210340851a00d403290310352110a500e8480e04045803a030140359100f0480c096134010002e1540300c40c000e0b030b5441c0c0c1d1a8906c03072650711040c441ca24052600030084d00c010f80c0c49118903941c44818030100d100711881203919071405182010150f44500c011005440013810981e01c501030010082140c0782880c003c1e5212700c1c01200140b0355601c403403800400550459010110034100b0750030610005002003984130201c207089880e505a00300c090005001401c0f80e80f0174a500c2021110080d0741450f40320510070449004034881d000184d90b80d107040e070700302452880c014410a00d007031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 80387078 1250 80385828 80385841
    0x905040b01020129011e020f0c0a1d090c0a0305070e060d0f06200a1e050c0304060311040e040b04061103070c240507020106030507091404140f03030123041103 70
    0x45031000b80c5881450030706c10b0684141c09510604142c100e00c3c4005070458504258080c2040088170840101540c642055900d064508a050000d8480a94003425001e0200d40142010410101001002440300300b155540e8540759030b882c805e03481f9400c0e03c09160700010740103241c502665404690084964001c1d40b003e0743d518802040d050200003508081d0381c040c281c00f0a00c00010b0840340c00e05440e0003c40b00d2959980142102400808004001d8204484400e0305004400d440c110383e2681000303e082e000c203001c281924000e42c2c20440c1c00e90009000c10003800011464140603034011340d41081009194118490f15110844a0a000c03401e40004000060290071641e2079641e201224a03106040100344501903540c185d0740d00c001130f9151202070061101c00d01901004003140f59017000403100140141828003030080026015006040e107100e01c0c03840500100c0f0074170078400706a035529a103c0c0b1000100441c0850840380c2030340480306801642c1043d00c035174400701c680c1400a0b82980d5504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 80388328 1250 80387078 80387141
    0x11030f04021903080d0203040b090a0203031e0417031306090302030307030e0609030a0b07090504020301030c0e1e130b01090b03060408030606120f041208070804060b041103070905040b010201 84
    0x500b201d084400d000c840000410903140c040c060b524261000903a507410541410030750130364042c01c0e00481703421a803200c4005030380c00011100204c0c6c0640301d044414582450191090003030b907214454031813060001c000040c401200070a006c44400040c0c2d1110354a80c8070480e40009c2c90701000303415030f108015907400300e401050b804201c01402004140703006e4003031002c0380c1090418901140c9140103981480710054201d130070b00c1c0280205690440c2190702d0b51f01d910f030481c00603114140b91818000d0118242e401402d20302c1d00d8900c1200150070040c02c0c000c0040b040c0d80a990390680780e00095000102c0c410b1114010070b50b010100a00401c41c644071912400c0d020352024086940c0241e082083c409030015000000b4454151110160051300c0d203400c00400310800040074404000302c00040000b0550003034400d90704650031600015034601908082002403407545103034141811701108222040ba4000540415600161024810305088900590980d40045411084c211030b00042c0120489403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 80389578 1250 80388328 80388349
    0x8070911180105090a1d07080105042307140a0908060606120403180f1d07050c070b09010c080c01021c0204050d0b0a090614090c010207050a05010f030b100f020111030f0402 76
    0x5200c214655a10700303050207550701ba0f42603000c00c8032240701000102600840102c0c0140030688041c44a81c510003103240c4604891100740d034003c903078100840c80c0030348225a442e00d8041c0d02d5034100e9480c403545001034035101c032511442c8030502c184000902d5a0034004181c42410500b00e5000945480756941a50403a441c0c4007800c030710502007400000c80301c0300050b481000f0180350a20714000c05503084104081c1c980144010180b01b02000003891184002981108403203142c4641501d54040000407130780000c24000c0a080c2e20000301345140d0070320041d401000c10780d030010b0f103018502041e00c80c4403082c0d001d01d100d46503100c0750641003070f400704414a10540e4483c42c410400240c00c421966000200d030700700b00303030307503005100c40410031242000030000030510080900061072007600c0d000002d0030703051940c000c03217041006504942402c28007071f402c01d940d5244001c0c13044580f1103501100a1120031024210401582445200b44a0100150842e8000c00c0200064a015a075070380034400b04005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 80390828 1250 80389578 80389597
    0x50d0b01020c0301020a0c0203060c040807170c0402040609060f02071404090609050a030804020117150d02030c040c02030c12030c160312050c0306040b011b151508070911180105 78
    0x30125446495030f000c0c401010540080d407503a007140c081c14010702d1f1601200401020507000c081105000342c0c0c10015a142c1120041c070f6102d5407481c1e903041c60031b040a4403600740f1a08180041400f08000750040c603100c080c1c50080d62401c008015041c0d0481e03844070385208005202c002c004049540781000d81025000d507004410220b00c688032070f61010b04d0189040300030303400200f45a062000f190703840701e1150b83c1003154452071003140c104803402c901c5100504000d03602c5000b4040250045440c00e0000345002c000080041118403502100a034036a4000351070300b9541d01541c0003181501d20004192405101c640d15840c2c10010202c10a0011152f896001d4060002054260402c0000340c00b0305803107150002072680d221b04001042c030041e510b0b840c08e0a070501c6141384650020722401c00c00c03404407a8100010806942c100c48040c0c3c018034a40441c800104001040030689c1d101c0081c41e0402c07103a00d44010407503010500001c061a002c2c16888450380c0041900d2080250b100c3c0028101480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 80392078 1250 80390828 80390833
    0x4020a0608130c180506011707030c0311030421090806160207080313090c08090a150605040e1b040605060a080c0d0e0a03080a270f0230030703050d0b0102 68
    0xa41c5519a08030954890340084e0500b0584181c100f4021158001d05811a5080c02c2130070310240c41d1461107440200082220042660310071034881c04a20941200c1044800e40e0040c99584c1881d080100c0412414585c4c0d1091140c0641c0d40b0703265500ca0001407040718005005061940c83d110b15501c800301085c0104000c40c401e21901140108061006080c00115608044400c82c501a0008280da04115a000030b004001042000040e030100b00b6083c010b610014a801800c012401000101959040b190b001031910000304404000040c1c40b41c140c3c10042c3c0c20a415248090400c42500c50318000c440c1c0090301030044030408c40c020241c103500070602c0c0c2c1c686c9082c07d2414510b00102c821681c1c5c0c415490340051412070074990405c8110b60011140181032000c215103000c2d40460842a26001c038aa0f15600c0c1900e042c001408058144039038010007490521074100350060b001c04401c400b560010624828001c0d01c040008100e80c03c017540754450300d09150100140707030001c0842c2c580c66070550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 80393328 1250 80392078 80392111
    0xc041d040303050c030c0f07080f0a020615061806090307080f010c0905030a02030703031206030f0b0115031103010b0903070506030c090a080307110105070f020901170c0409021c02010c0605010305031803010504020a0608 96
    0x4120306010308001c2c3d01e07a83c000c20dc2460301c50300552000d0403100966008a400700280440c40c220750005085900b804e84a0301d9503180b405012900e40b01d07490740590880c0c00ba8625100d403245041d04035188042240c0e1752200825204c804050b05e0f0b1001c0c000082d80750f4410032301000024014040300c3c248000c0000c000981c0c5580342c0750021144c00c1c00d031044170081142c3d03005026032903c2103d04030f01c046451404004261001109019610041c02081d9080402003421905554100034200c0a17040c040c000e07507242e082070421410280c00108002d0f02c0f41da4160800f280740f55000054561050b0007a1001101462032401518158051641611b150080303a0b9040f01580300c0341a40b5000317115180400705000802c90315a41043c3d2200002d510603801e00b109003016030382e030007400c2c40c0350074420704281425202c601c010b0700c1c0380c43e080100619490812000009014010014110911884603203480440882042500300d4a0440f0000c0d40101825020700109210300d007902ea0200c802e000c40c0360074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 80394578 1250 80393328 80393347
    0xe010e0402180a0603030807020f0d0818070e1b0a0507060203060a050414060a0609080601051512280501030b15010509040908040510021f050c041d040303050c030c0f0708 75
    0x20403800c4071a02c983c1900d8150400800d50300c6002c06600964910281030704412940d40c0b01d445080d44403154042126110120b94107090b24001c3e0031194522804071070b030b100d5482281d00144c03103044507080030050400300003051156221042f039019078115035815140c20426a00c80000750130107040640c000c48909000300c0c66898134030904001d60107150307190b090362800500b080681107442d0000010404503a90401004400180f21815a00c04440013201c03007030441081c0301c080c094000d00313000211581050006d170b10703070740c0540d0f0b000958020600d602d079480078510740301a01e03420300c802800e4446840002d141e107a031038400304802c1a81454141c0ca000f41840004054625140068400c0c5100280812030703403400000c017003001c2c44640054800703140e0061502c3c50541d000c0181d400501c5c0c40d4000102c1603401c0380200ca010f4a4852082d0070a407941c8584080d001d2402c54044022900e00000b107500a582c1c403041e248501000504075181402d40300c2d40201940200314219010701c02404a800d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 80395685 1107 80394578 80394619
    0x6050112020d02090307030c0f0e061302090d02061c050a0b0607080717030703020315011d120102120a091a0405070512030c060405010e0c0a0e010e0402 67
    0x2894185850750710b400781c03084440d6583e16005208004c0200300c14251200d050754070068502444d40e0315a2410040c1c540241c400c0d50b840555a40c207248481c50741d800500b0100c0c0040d00c0c120b078160b8075501150440c0c00180d0041500080884400d125181c640b0800e5070000c0901c00501c02040d01e100468541d20440c0401b5002c1e1034001482028032240112098000181d440c0072950381c070f40807900030000e40082e190b070f580030803042c40e07030f040150301c20440300f500d01440000801566102100704141030407042c940010303030354080c804860150041000244151250346002c03a483da61440c0c4800881418810090038041c610300f400042040040e9050070303203005507890342080c80d8a100c40e41c40c5003e0000200c205101e424204010050306400100102c9400d41c05c0340c66002510307041140445a600802100d40c41160041001a60b001c1c03907643c1090002d402d015228020440692 = true := by decide +kernel

theorem cover : BRFrame.Cov 80215828 80395685 := by
  have h0 := BRFrame.cov_init 80215828
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80215828 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 80215828 ≤ n) (h2 : n < 80395685) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
