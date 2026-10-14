-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0588
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:36:24.953331+00:00
-- url     : https://prove2.me/submissions/a949ed28-e0a4-4d50-a2d0-537de213f2e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 105575539 ≤ n < 105755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 105576789 1250 105575539 105575551
    0x3030804030c020d1202030d0605040603020f09040c051302040311040e1c0e0907021f0c08070e0409020406090f0b010306030c140d1e120c0f060203090109140a0506061503 75
    0x40b6241c0003107407194446451500c1d0003080109121141c039500a499034010401c2c03070103144c100b510105062800c0c1c400c41c800c036980180040b04030012002800190b100041050300e400900120018540c0c540d883c0030001d804440c1001aa01c031b04615104410f200d03c094881d01580c6451541c00440c4400a50f02c0002c0d07440c003c03c203403801c205c05000c440030b9000001243d040840070301071000d03003a00090315007040e0004181c070b00c1e52510143c1841c01150100390540c0000707804540480d465501420a00c0d5507420050000b00d80001281c0200f001c0c2d500a9002a075102e6581d42c007403800340010b108150f0400d509107014040c43d03145031a5595013007030f98080d008048443c451401800d943d070081d000e500710751000032802d01994504c43d060000000d03074029035940b03000e49150b8007018840c04c0b100d03520071703401618050b14410340d03280d0f00c0094000600a440c2d9640e1900e2640c0421107161020920540c09401401498824a0242e0405001604075401a0f4030380724007a9582000109895103c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 105578039 1250 105576789 105576797
    0x5031c0c110c0a051e19060906020a0308040b0a061509090f09020312030c0903060a06030c050a081905030c070806060f04020901080a020306030c0405040b06120316060f020d02031905060105040303080403 89
    0x1c01d28400380b5005c45011441c260301005120505081150708041c2d80c046940c1074031803028803580c60310260b03151951400001d00183e40c950014002030041c841454000b42c50f41000582c29448154410042415080d80800318030007090402045199000c3c0c41c081a0b000c0300c040c0501182980840d82e07074002144d00e00b10346000800011400a0b042090f9180140d008003100c4690610b000000300605150106882c0c036607202c040469681400301c02e400032109254010326580202c2d600300500800404d404036183c0c0403c0001d22000e000c00c10100020342081005404982808010025884801204140030328014407114529a8114500c15441020101c016950781e4403003000070700300124189500c0e805454001400148055180403500c031342c07000d0702d02d40012203200309810b590740207100702070161040c6512000d00091084d0000b180a082003030026041032214047c02c1300340d80003290280c05070107a9440000c038801443c000c032604031000303081c002e01d400d0842e2001030011800800150500c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 105579289 1250 105578039 105578059
    0x3060504050307080f0c01060b03060a0501030504020102100e03091908060106051b0717010b03070f05060703030f0e0f0d080601020c0904050c10120605032805031c0c110c0a05 77
    0x44007007441140e19540d406440d5507514080d000300036030036400c03002000309030f50310b00140030030000002c408580c000c50006100b00b4005241c00011400f9200082040341107010f0300310380d00c5500e60103001e0764080c81e4080001e140c849807400c0034421081021400f080c02024070344010000b0403000700e0b9960545130075142c421340c0d8058007100d03c0c8104404c0c280c129000c0c841c1c240001a04841c12070104099002c00c1700070310941003010109503940d9424062150190850b00c01004a45485070061110720f00c00e00700031404424150b1300d13030111685403526141c80d0700040f000d10b00341c3d4000e001000c03604885080900480c144000000c1da580c501410543c080e2480340040b07024440100010845c040001341040c9510010b10b500903c0d4403080d140203e272040c10030703c010605180201e00850503800ea5201500c1c0e0710420400c0028230070034001c041e82c550008014a0f14001000d401c070f1000074a001001080316110131a0084c482c4103050040303042600700c03a482c0102940c880c01c0f00707021204129603503881 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 105580539 1250 105579289 105579293
    0x50306040b0607170f041e0311060705060a0f0906150602071211040213050d0c0e1b090f0f03060403090806160f030b04020904020a03090209070c1211070b03040605161803060504 78
    0x814030a83d04441e40d0040e00391990b00410200d01c00d9130f408d0b00d10501985045071030300702c103124850084c58001040381d040303c000210500750b0b40e441815489030003e0082a1450107448034001c80b41240350001d030300d04800304184400307501041100014508005500d485001c1c0391910305001c11140d103006d20454002602441c0442180c0031017000e04001407001130014000c3c034041d01c41400901c96102502e80c410001603454103040b5a207613804d402098028600001c034010016410310412115a0040e101c1001280760745080002e05c3c030031403280d01c0d4190f00c2810030315201e00c3c08600414862448040340c00040d038003540190400206110781c2008282017101d100090042d002d0301d51010b070082e00c0030030083c07240307540340d0403500c0b420f8001d07914040c1d550ae894504a50035254030030b0180110205021a45060b4420909070040807604012743d409140c0b1a80019a10b03030007980d05582080c0c580c0240604015a001e680740012034070f05240d100800c03003207003104180c591444003402459139900041c1c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 105581789 1250 105580539 105580567
    0x8041101050d050a02031021030c060e060903030411040207020a05190e28060f0b0c0f0a03052a060c0c0705030304080109150b06041a09030607050306040b060717 71
    0x780500128043c04241340c0024100c000703400407030303002d079008900a1000a10b58081d1103901d07a01e03c01000300c007100c0d400b5600c05a07182c9108440441d0001e80c0c0b1038800d040ca04080c40060f0140c0da401000e1643ca09081c103040400d00c8008040504c04e510411041005030342d450340b0b00301101e109881600140703900048072060099203a01440c1503c00e0307802000380050903a0070880d00941d040500380c0070782d00f101840030308894480c00740c0600e80100c0031051043c00c4441000d0500480c52600701d400084140134928101103250314110041540401ea0b602c03400c0004640005410030010280b140307181c2a8443d03a517a10700500700e203101480c0050700c00340b075100500071040540b034050201d0380c0d0b65589484150080c400008103840d0b000e0460800714008805000d81f81e49070383c008010500f02401d28400b00d01c8250010348074040180704100000e41610103002152148429846058891400d0001c1c0000d4a040f0a06944290010096400003d450003150102492151a216240c04144509038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 105583039 1250 105581789 105581797
    0x5010e0d06051008160e0c070203070f0303051809040203150a02090406081005070908060c091f081f030203100203040201090305070f06090e01060f0c15090b250804110105 75
    0x2505180c2842c042158907030082c51107000f101c80f41030464083e8440c0f1000d004d400025401400034048002001c603102c00742c503d0280c41118001010303034807043d907211a85070000c2e03c80e40c03040f80440d00c0410185d8400c0000ca01400044105848050807031034103500294071460742001400e4001d10803000f0990750841e40d0b0649156400c050b004110f030941302c0c00c6148d03030303090861078440308c55003080c000514980c4910320700c404803008003005141a0b210030741d000c3e01c107030004005940c1105060000070b958148004041d02c202c60181c4031810107050131150b00040043c000d0300c81d482100c620100300010b0f1400607083c040d104254100503200d031658130040b61900e10540c00a44184604480801c08207003081e01070040f02c60b03a0b16029040d81c1d0b43c000c0c03110110f001348180c1c000300780c40501d01c500385401814020b84891103004200d01401d141011203044600c52071050301c50038000000c00003084c070070201c00302c9802c3c1d03225040c02c141e00b000d210007860000000c10003130041d0258100b8800c281d028005032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 105584289 1250 105583039 105583043
    0x20f120414070b03010512010b030a0b0406110a11010b061801080a09050708031206040516030f0f020408010f050f010e041424150a0803030a1119030203010303120b0a05010e0d 77
    0x40c41407030f0750318141c42030325410038001c003445001ca449040c000f100052259144004000c1c0c060241e2000c65124400c82d010000d100343d40003502d07500200710400c2e814009015584494507500050420150810300b19420070060601406040004046042c007020141811441c00d10304100c10f82d03a00c410310b07800380c25800c000801030300c611000800c04841c08000b8083c02540710709018516512801004162a010b03182044490700c000c00c21a1414444e421800c54081c4484000c0f4030702d8107180ca898200e0340198040021655944491b02011040d8015641c1007403045161074120350420101030942c0c1005400201440c09904502400003414030485070b60b04000440d035900d0016040307401c50790041c1101c40f1211010070742054140e928044011000341c840c454020350955445040361740041020454180803e002840855450b150f40700c0759a81c0003525075005a1a13500d1480c014040d10005402d0000300303401d0021a2440e6102c040303080049510901e01041450360340b4000c00d81d40a003070303080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 105585539 1250 105584289 105584293
    0x501080304030308090c01050307030c17010806060a0902030c03060d21081005040516030e19080a0306081207021003090213060302090702030c0a0b0709050d030806040c03020f120414 80
    0x11a94008405081103d000351a450020b6940151242e00c5072051066280440c4c01807020075101d501c13a40c01808200264101252110402e840b400f2452000f42d01007005070f400041048024105020344a0042907024019030850134903240140041c040108082e00540c1c2080c040c0040c80700d003140030880040103064000112030403200041c1340c00340403500c007082684903601c000f030181490f1103014800c0188220500251660b0720b803c4000d080986401c941c580304944000309842a0810000c000f40e120f09880c035616035180c0c1d000740075102d041c0d203c08800d410114141d009000c010013100c0305154100c990307800900e00b80c0d905400500145c08040d4003d64080e2114060341d0844d40b000c4c0039240203d5101009a0b5020780403a070703030f1048440c4d1034115000045c5240c0040c0c9010904d68001040707080c500500c61b144c00c0407035408241c010081d80040ca2903014417030142801d1242c1c1c4003407240c40c9400c0d80740822550094402e840303220051201548050002001d1003403507075404c0740d48000c40007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 105586789 1250 105585539 105585541
    0x705070308040803030702010b0607020102100f0204090218180105030601180216031101060e01060c08090f0d0503040603060b03010302010815040b0301020c0c0307122613030c060f02060705030109110702030105 92
    0x344c1c1c0c1d136001201d050001d580b1709011083c1e10f00d0101c040d500220390590082100d01078045025028210980e02603003203940902c004124000d403400501804c40529160040902c6100d0070050307017800d001403000740000818014080c03504c1c041011410340d6960034042c103e83e614000520f000744120512506030700761060b880410141d12000000700d07800b074280244644c4d40c461030701f001402020b12030745012503003145561000590070700c0941080c0c0801002507440410040c0417943c0f0040d111821030b42508001400d00004c1e405120380c502a200c1450300790b0440d8110750003e007000b003001e0854560199080070f841e080d580d40750000549030001600075919581030244055903405034000b054424044c4860105070184211174000a068001e81070065621003d540c26a0071001340000c60150241003003006181c141c413011280003140705091603481c0c1450301d040105040c0070b5600c020700f1034100400f4000b0541d0300800356415180140000103890a0b103109981840c03060140080d050b501300b030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 105588039 1250 105586789 105586799
    0xc03110102060f0f01051207030605070305040c080106051e120d031a0d050a0822080a0309050f010f08100f0906090b0a0807090911040e010c1e080c070507030804 71
    0x14481010180a03000c6810a0f00c50040e18080000122030944502c0b110380010810341c40d002c408030b0054038080098403882c51310b0b0b445040075034008aa0a10100e503d4005210400009a410000521f20b810080007054100300000784503a01880c0101040105c0008848465680ba20351321444034400081b91061803900030041e01409858141214400b42d110500c420fa0400044480c40c1c2c1b07500c0707000303060031a0490341c681d286500f0206000c81140c00d41100c1d000084005880c40000e802d80380300074a0070048074580207011070102d4100c507000304c1d1254600002e0f6604170200d030014802c2e5090a959550f290040ba0348485120ba000d11040044482d0006000712150702c08420b40314110018001c081078074082c4540c50100348035000403036000c1481044075416990140e4400c40c0308548210440c070340400054180e5070644030030310700313a5519960240c2031908000e01d00e03c09103160603001c00c2d0100b4084040c0081c0c0740181042041c0c0400941d4400b0031030140071107006941c0c00f482080c4c40319220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 105589289 1250 105588039 105588053
    0x60216060f0605040902010504050409050102090607050a0c0b040b07020d061e0207110109291902060a0b010305010b090405091e0f1204031e050a0b0c130510020303041403070c03 78
    0x840c1500240d1803400001007003506240c056a80345c1a0182c4615103000e00d040d00784002001c0d401005e50f15550b090000420599418004001c00e41c01103008102028a600703141e400f40b500740d80402104001000100100e400c45416180000d404441a240c008420700b0540054440920041411a012181111840742c1503000d411a103019074072814041d01501d00644641601e0b002c0c084805041c0f048058070741d030642c480b1240c514901c403c1c2c142040303c3d04c03181a92044681102c44e002d40c100000700410480f0b00e1044200b0700009290600140d450207281c800b091199000c01406151208000340e4441000c0155251000076001000d40341420007030b02c035494000c0034158046070b0103141480304003a101c0d001590142d030740110801030192440345400c080070484007411140ca014160040300840d001000303203807080c00c500b440165100c0704000540104441c40e080b0f00d00c980307801e44c100d201c296800403e40c0c0d800769200040a00030607092035400d20b18003400000801c0e1024120001c401c0000b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 105590539 1250 105589289 105589301
    0x3020402090d121706030604050c090a0603020a090f1a130b03030f0408281509110901090e07060c0507050105070c121101030e0102030421090e090c01091703031306021606 75
    0x5108407410035143c140c100b51f141c0c0b02c260b402a00e240d000c941650b80502c2c105001c03a401044c1d03418006040d40c1e496012500c0c158265100540b1180d0b10720040221901500800d5864240c42c010240d00d820407000042c04e4610700c110b40e990345e03a601d1301c60340e01680741081110740540d024410143c4641c0d503004420764030340c15090501c040040441000c10840c60500301c400903d40d0284021100424007503444000305424442038503045c540a440740c1464440c0f44040f800713004c0e6000003280410360a065903141101c40e500040c1000303d0b0014850200b8404501182612002d20345196500c405052140c1c060b90f4a41125812408452441007041190243d6103005e110030b8034140445150403410074200d01048a018000d034800c50f0790300071000040154074888440360708000740c49075160040016010700c1194600c07265030103500718802d00d40e0040c2c58100244031034130322031200704d031030000441d142e00002e0500100c0800d0170903070300200b201d50380540d00d00100c0844400318401680c20300b0f0300a0a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 105591789 1250 105590539 105590567
    0x15021b03041a130306050c1b060f090d080103060509030702130e0d0503010302031b01020316031d0a150e041d0102030601031b05070b090109050111030703060807060903020402090d12 80
    0x41001c242405070740b40a016940c2000d500c1209a800398910b0701c0ea1300150000800350b03110000b04009082035142245213040d200b80b030700e41c003e204910300f0290051890501928000180d13011685080c172803944122014152031380a0303404a413640300d90a05a256004072007000f9032000303514580481280c8e40350f00c030540203410001198042c141e03850080d14a44020b003c06505500444202d50143c00440d08400d0805c1c0d041c81128a0000d01042d140c1c01164001c60440001b00010320001d5162441c100684484000b02d42c6c0b4100780e40303003c0c014031305050300300d105905014000c007024101c0d40e5150301041020013101b051050021680b46118000d50007155240c1c00310349044100003070b1030340b0002c21344070700020b907182d03140b404460381c90b80030107900010400074407903403140c0d6030a00080080c00b54903080c503103c4d54083d4403820b21503405000d0342c005402c035007400c0d4843d441c20800e8540c800d20b03040c220782e0103079001681d40807d28041100c0b002031a4002d4040d59414012800083c0c0c03240401c4e181c06 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 105593039 1250 105591789 105591809
    0x2318040311070f0f052826030a0813050a0203030a05030f070e2b02180105091305120901020102071212060512060a0b0303070b0a0b0109081915021b0304 67
    0x54991141043d0300f80d0b58020110141154071091015041811500d9000042481d040c251081101c41c521421050b41e04044e9490012541d200b00d10f08244118442c1c80d1000030203181002040400203020580041c00d0420200c0340489940c140b00090214007012900035095a60711a8070f03500103040c3c0d50050311071071500d1000b180007640706481007641107243c1070001d10411220f445030006000600c80c0c005c540d82c035034032005c20b10710069540b0890002400315280404549615090800059400c0180400b4001019180303000019101040049144142e00811621000002c004038024000c0a900038603d40803031800360031103030300940c4004074000003000a00042d61100e0602850032640010007015601c0035011460001ca2a040a140d11070013030300712800c04180740c442a2004200341d0b2100491907982c80c6100d0789507400b030600c9020301b44403c001d20044036690102690f0341040b00b0041e00040d011003407600c83d18155011140510101c114031030b88142402820340e220b50103841009420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 105594289 1250 105593039 105593053
    0xd0b040312020a17011e060e030c0409060b0f0a0b1c0f02030f0f0903120a02090d1208071b081b03041e0e010f060212090406050a060302091002072318040311 69
    0x40c61000715000207200d1b20100c031500070f920f0914161503041030b50f00040c2c0d00d802202c80002c040e0b1518400d84800718000c1c000813a041d0012000d2001941c0c1032107115028280c4401e0a01100b1030354011254081c91082c403404041d040742440200905445c901c043c01c040c0000700b84a048001800c02902441040b080c06070503443c0c41e99440d50305d21903864245801082040014500141c80e4041d100d40000509074040307000007030341c1d42e02403006903030b10180c0031030050002d1280c0c55a02800c0c0c08081000501d9a00c100f0a280c0c558000600484095101040340c0912030f00f00b04100348107071002807d45108140304201c0408450394030300007d0041e004a04801800000c0005142e01c6040840d19650050000f0b4502003464000075444440740356009a194070000032181c40e441c9a11006141e107580c01611000100304100e41c0382d11140d441d40840d03008110a002c283c22800040302c400010300c0100b46d140042c540491b040b442040111404840090104400d250704154003071307044c91100c2c095501e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 105595539 1250 105594289 105594299
    0xf0703050603030c0a0209041416080d02070b16061b090302030c100e0907020106030b070804150b0a121502040b07050f06040c03060207060f0f0c020c030c0d0b040312020a1701 77
    0x28034011130441e000c669200c0020700000d410f00b8014260858000c01c004031200d01c59042192030503500100b0b0070b07080048a41c003008403031410322080549000c2e40c806006120f01e00485200c950085400207010403d01b40801010084151310122500d18030240140c980d6098000140600ea00c4e40f10582c0240552002c07000b140c500023072120181c451235218400203180344028010440401041034044d50343c1e070707040170001c9508850128881d502540d1013181c5444d1520703000314508184c40c5c10b14115410310019501d6a540c194030310059036100310321016407864038106a0828081c40c10702c00d00042c0b00180118045080c100105401da00403401c440004103104c102a999400841d40a4600c0d06054010300009665400402c00701d40540d001203500c40d0001c00120440d00303081140c1c49103a40e118141051203406101c8144145022005800f0290744440030849210901c030004004401c0e040010f0205801030104081d4109004030464803042c3e15000a0007503510035687c0110350b9440000014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 105596789 1250 105595539 105595543
    0x120d0c0503010f0e060111010203041b05030d09051e06030a02180a030c05060a030207140a02030d0e0906040906021c0b0406050a230120010204170106030201091505040306050f0703050603 82
    0x8100c1d0f030843c0d002c11496242845440326800040d03d00f604001e500e0304111072161090010354043c031b01400600081e0700003440b0400006a4507801240240c1002051003880350300a4031110403280c040d00c64007a443c100d40c142c1c142d940c0c950001d0580c03082000c010b102d07d17980241e0107800d940001e6840429071900460421148040c10311005100121034441481982040c1001e00003101c1d65080140c10043c43c1d03030325142c405601504245560b401410140258903040201041204039420110540320510012400340000102400c0c0a240c60b8416078041250702d03030490b45882c6290081c5821b000c0e0345a103402c090414141d0851081e401c001001ca42ca241500040d4201d070b208050400032603090035401801444010718180c10301c180d000e0f4012a200c100045410900e0343c42d000180c0d01c40c2045041c1c040400300000c0c00b0380582c034200c01440140d0700210044140c5a030801c0402082c2c105560858040c4244d4200070320f5181000b05102c2203920231020540180d801c0e4070184a00da0301d00302495 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 105598039 1250 105596789 105596791
    0x901020906030417090d03020d14190e0d050d0224010e07030e070302130207051b01021f06090c17060f0604140307030f050708120c030304080306030c03120d0c0503 72
    0x503a01400400118000604c0e4000110040661030a9181068400070010340081e5540e00c09401680080f4400824603512040b0039900410520142d8100070032000c080000b00e180c101030105116801d00b810180e591521100141c96030700c00c04844081c8036400c00203444074080c0700000115108601c02d66040b119002d503040c181e510708280c800807a510000300324050b00408540610500a030440400541c5444034080140554400c006d41e0b210683e18110f0b1920300d0b00442c2c184040410040304036680c1c0c0c0440d0802d40c0d0542d5007026940d1035507410000b03008208e03540c4401c0d000e030b05e0b100c01a0304081d04507142e1122003454090004541d56403a0074003101b420a8009103500c02c40800007400050444101c1006c05c003000390441c0c8804c1e840382c0c0c1e0a00010b03045079090300c40c2d03440800c0030041c0d0b0301c0400c0400241800c42e003145042000c450041680ca00020304000c2c0200000701c00101e403510100071454039108010102d80381020380c000c643c0035550224820021490400f0101d141d03140c010700450f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 105599289 1250 105598039 105598057
    0x2101240f02061b071403130504110f07140a12080115091e121505010501050c060c0a030e1c0e010903030c0602090a0e01030c080106050108061305071206030302070905090102 76
    0x1402d5190b4403840307014040b1041412403540607006201d420003240040e0030152142a074000110354442401441d800c1c055220740c04203110b10b0416503450b01b401b035010b0503520000c824a034000e1f21b440382031810803004000d40310072902e1791040003684014041d4540031210008116100c160640e621203d01c034140c42000100c5602107031007200704001c03211401410505004c50000558015a1640c0d11841c1c0d440c20b1b001d01f84c902d10b010750606005403409208440c0145401d08202d49042d140c184540e407203880080c503400c462040494680003880c007a400502003515484140c48501d68401c0d1020101c20405010400144c040100110194025405501940d405840d200d04a40340ca80d94034020358000c0428035040651410300103050b4540c040c90501135881166544245400c100c4980d0840d0955030000f8100044482031110b0741d1105560b5200aa00442011400707980301c25085d2900d00704c4103902c00c5c1c100e01c0c041d0b0010506d42d0110314081500d1940e0700c144100c0c0c03130f1811014240d0252002d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 105600539 1250 105599289 105599293
    0x1a040603030f0c030519030605040f02090307060c02030c0a060c05070f05060f07080d02030c07120305010b09120f030a090302030105161413051e01120e10022101240f02 74
    0x11185114001c0180201a5100f0b18000d4500901c41e028150403448421030381e001f180c0c480400380b040c1d00d80b034003d40c48100d60a903821401d00d411100040e079260414841c1e002445080c076124030540d03d00f4000381002c2c560207040029690380e0740d000245860566541030395240030b4410086a04921440d0090440700f00030541070400c40e840c554a12264000b1038222805102001005e21080d494000f0318414031807a9201911a0010b06055004104000751901010316081c018070507002903030705941c402001950f0180000156054480c540014070100000c1c0707120100308200c40a0f44200f0700d170103591080d0002d0103180c880d180311000c42069082e440002c01c0d030820304c0c1031102c07840c2d20281201002c07030040e00e040d0325aa0000300b10140d40680c040086c4101c21040d8030356550700b1400b021507a80440008014203440380150540320486098032031086900010800044204010524162446080984c1e038a580d03e00a00f0311020419054000002420303400e108000e0082c0040c4140c000c1e9900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 105601789 1250 105600539 105600557
    0x40513030816030b0a080d0909020a050d0c050702031f0b030708120a1707020604140307120e190806070801060234120c060206060a030c0509060d0503030a1a04060303 73
    0x29650120001102e01c0c82c2015525842694140d40d0600320301d004003448405026081012a001003200036103410116115004005000c41c00758007108a4900003102100040c1412484404807041d2103240c0c0082c0d458860407842001c180e01d042a40c04204042c07580800c050500b10052545441c082e01c5810026003082d44080340450001c0001c0032800000d181c41d10042c802607c3c0901284030a80303004005030f00050411041100001740300c02480010001103040003815502d15141600340ca400000700500b04003049860f48580300300c1c01030300311b09651070a55607032111702203640c610341104c0550000c4d40140002420a002141d4003a0b0f1400f068402c1910541d81155419080c01038003d07080581904000011100f908400b154921031003008544c60b4903182040080c03818101401c40e600c68400070000b040095102200c1408a500136200c00802e5036074100000c2140c541c01c000985103000c0081040180e0210760b20400c030340c0c0c94031562902c100c001c40301030101f1508540801004030303400c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 105603039 1250 105601789 105601801
    0x2a06150f030c130605090f0403020610051c05011b0507020306060a120605070e2106062205090f07030c08101407050309250303021011041203030209030102180405130308 74
    0x10700702407012010a0041010740c1d0390004a01b1550048660604a900f190b09110030554188540e82d0400e038809a451036090070200001c2410741010b0200b20710a200240c041c003013200a400101c42c0700789200218411500c8000302402a070b0002ca0308a200c1d019950014101345804189501641c02e002e0301c0340d800000c10f5480c00000c14001e424a000e00144070180405503982d40301c0803403c004080c1c402e0301d000c800305010078a020000342c1300511400302c12030005000c40540e95540c0010a0320700d00403c0f10303101c148400342842d0411418030018000d595010007400b000c290700350210382e6058119a000c812011240d42210780c0b80d000d010703049800d640070490951103203008e0742c0c00101c00400d8509e41d9810b461a503034800c0203104900c1e461403030038808009050b01030207903c1c255016440c0600050060b402c5244040c4941d0040d01c400416002c0d0110915120354181c0710000c070060021555110030240c1581400400400984114148000030710190282a2105103031a410f44507005d1544580c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 105604289 1250 105603039 105603049
    0x7080c01050c0f07141801080c101701030308010602102705011d0c0f041107060c090b0705011b031a01030c05090a0e07260402062a06150f030c 63
    0x10b2149000d44540501420307040803d010030801005225100148690f410b010701182080c2ca2051200441158004000c9187c0100d120194064200d0b00743d840b400d081c810a882e50410142401000007004c80003000701504601c5e541d059500d150210340c4000405421141920740492030b10804c4020704154580301c0d01c030a401041075134414400410214002c0000d0500c0a03100e01080d1090380c0400075043ca28104905c1010364003100344e4040c80f901c6502d420702c008a11070303440014015640c030342e1a00d20382480f91a500010b80749402040340d9500761810040e0103041c0c040200300803588a0245441c165000b8810320341620050003042425071a0207005400915142d8010341c180042040688465500c80707207250042c012452582425041c1185d00034010b460361044442d6401c458924000c1d41034001064944c41541203071440d41e035182c100034441201c094002c078588000290400c41e01d80b03d0340820601d10600104103000e4410a40c4070030090140c400600c40358050708520041126400c0c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 105605539 1250 105604289 105604297
    0xa080403110f0705010801060906080c03130f03020c0f060316110309060406030e06011712160606170f01060f050103051f08150a060b1b0f071d010807080c0105 70
    0x80d0610450700c4214052941c10400300501c0b190180e00064018011580c005038042c0c05480d0301d180424078a400c045020b8403001d000b43c502c0044540210020b0910002c446403000d840342c0c070102c00c0e50401ca1915001e580d441c6c80809061081001003102c00140c10701c613054911a0f000d06c412118807640c401da090710105138415181001d80802c00542c0f109460b15030003040180f501d5a0300040091070004194201403042e0011800d4000e041c2d540110f560f000034481d002013094103400c0b981c0d600d52041810220507041d0000340340c1401d100b0002180b0b100550f4902214600a040d1981b04c04113031401802c03160207014200342c1620100e000d20455200350300155020302005030324142c49022415500720806c1070b5010a0701d542c048410710011350018810705401411284041c000300d418010840b403540540100030190740860070704420651010000d403902031080350191080113440c0c04000d0200da001c0c0005900c40450000002000100001d0441c11160080082c0440852041c011101540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 105606789 1250 105605539 105605543
    0x9050f0613021e191b020f3607110a020a060f020c1801060f05040b030a0b180a0204062007031b080625020303040f0201030506060c1005070206010e07050a0804 70
    0xa5002462804460010190b62540780150003c902a2190082505e8001141d54103888090000000142c984407220303090604121050820318580c030584580356902ca404282c401c0500c0202e04004035200f068607030148400341d8400b5451041c5503042582c80301c4042d0001d410007089242000030900c0b40e0b0022284040320320644001c10a000c0c0007880c2c84101103125000843d4480c01000400e0300004003010481450414504180c9411801501d07400020116040c50382c07034280900d80da03550000071408a032889069000c0c0d500385200b00c40300a40041c000c21002c500c80031400caa0031034509101c010706402420041015505590366001c0060009415503804039101c54040f40700b02d07041c00110702c602c003590310303110305042c0e000445552041500c0d070b14015500b040090101007000c18009040858080c2404122030300c810001c00d0781c510640481d41c90a01a16504032407007000c5070000f0b03000b01d62550841d07505076250b070359141002200760fa4030400300b20300f003020703800742d41c010071041e0340c864 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 105608039 1250 105606789 105606817
    0x209010306090203040614090f0a11060903030a020601090b011404090f1b020d1202030403201006031a090d1b0804030b040506072c04090507080a03050409050f061302 73
    0x550b8407030440060342c0056600700c500359107414170100300e60300400d074055000c6030600040c0030800c11040501d80341e000122010707280c84620104515503031154012130315156000760480340c1c1c401110800030b4452800303000f0002940c0c10413150b494298031820f819041007a0310a07030180360614001104001f0300140300d00700312aa4840030701c40d16245c4500f96074049030382c00b40c025044e2449143d600600e03550302086040748262040c0144408258403100740c918028420190251010081c813101e40342500141c003124059080c11804410000c040034412003480442c880e2070100d444403961240ca401c0c3d0105e4000002d101450205a04c8940c050314174402070007a48a2480c05480e074480e2481484102c50982d1640d006605000c00c035603001e4949014001900024428200d61f0b1000b400b030170141500351440344d0f03110f8000b802400320500c070000c0104009000c8038600e002c10700d8064103036001481345001c00d80c5043c0020b2880502c0585e154030640c40249170f450148041065035000f5007081044c8a051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 105609289 1250 105608039 105608051
    0x904050a090218070906020613390e090705010e01051803010207030302040302090907150e01050d020408010516030e0303010302090c0909190c0207050d0623070f0806030a021302090103 81
    0x56190583c5421009040110181140c07078110b5016140c0c0419130f02c0001154130110401459802e600f003a01d2080303030700441d015500c134003c5c1c100900d0b4804010360305101d401080140301c034581c00960301c0403c8901070300d13410303d0540c1e58102e8580c071182c0601c1950b02040380222510040e41c8030300e004191148000003840038000d484070200f42241c00c0020100d004c80d500007010b01c15841e0007840c2640c0001460b0040c01c65078284800c0707415002040c001c68091202d51019000d40d6030251083d603084c4050008110346841c0d8618055001c0c14003914400e01c0507011083c0003c2444c03007809006100d081c103a0045185074078583c02d1021504008140011200e0180b02a1000b50f440d10030700760007000c40d8120712501195803c0700b0401c0f124040c00030f10941d0701050b0704003c5a210000710141140c0c10010003c3c415626650805440c400b201101c0348030307503680341041825a0446e44c3e0880c050040c0e50b40705141c4c1e41d00d106040d510248060065071044107020a00074400250b0003e00c50701406140110703003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 105610539 1250 105609289 105609293
    0x50712090938040b1c030908030a0206130f020907031409010603020307031709100207030b0f25110102040306020d11040b0a050a1b12030506150904050a09 68
    0x5208040a01001801003801045168040d015644440310a46015031115000001c0100780ea80000312588030070051025a04050356254081c01c0c0d48440900000054800c0d1000002205a401021008224072210101c0c05501c0001a6600d0040342d4004115a440d1010301e2014289006c10031695002070104220040e1221a030080c012407a6840115503004646009041e5283c02042e002550385016020405070341e0000381c05080b00d4021900c0350000d0000d0b4440d801f2480382050719a0010380c41a20841c0b030f1640000d018046a00580540d043d070780340d1f84402040c00c42c041c2e81e0f0000300c0c0346080c000e001040c405408501d00e50182e0901d03240c5002d00040c0303203003a80c1242c0d10035550300e41d010441d01c910240b503014003c503040e00180401c0c074141c2003413400d003610700036920f140f0100300000c1a040109030103450030726555210200d50411703040e01c0e8034140050500240080d0002810a03000c2840c17800c10898604102d452441a1402d103180841440010f000003090384d1409500c80940d0b0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 105611789 1250 105610539 105610553
    0x40c0308040b13210605060402040b0304121e0906050c010905060903040f0b030906010608100801020316020d0e01050a0f1e0e18010f03060f1b0203090a0b030402060301090c0507 78
    0x401810424000c6499410121111070014034560122135508038040910814002034080720044a500800008a80d12041f01040080c0107540281403880750000901c81844041d182615860030603a50b04854071032951515441d1038480f06540d800308a00303074018071615000c0c5024016003a40348000040030b00305601c4d4189008070a551510303460b080000d01f402843c40e207c140c000900380c4201d9641c59801c000201694440c0144105070400401002250361100c0110004c8001c3c112080295201c0c1000740d04101040340011126000d4482c60500319a02c138020b01d040d401403101615001c1c10b02080074000c3d16001c41c2180d210041105000c85100e00700c030a5440c2802100c1c4a584508000c4820401d0102000c4540b40710149600f000004108450030000e0f8481540c0d030220001c210300d4808070490b806081d1165840c0c12100303030f2000c2d0426490b030000142c41a94421140c2e40704096450840300038512003034030041d400807020401440300f0b038041e401800341507050f464030300d15204c00354a404d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 105613039 1250 105611789 105611797
    0x20f190302131707050108090303010b070c03050307030509010318050c040e0c0306090705010f02070e01030303111207080a05101208091f02010e0105061c02010c020102100e061e0915040c0308 84
    0x100750b030fa19440c154022110402c1480080d01c000e09203c1850300f0b06904c4181e49000522904200c00c40c006000c3c81041500c40c1c1140003940d20900b26a00d42d0001c6c0b402800b60f421403000140024a825590614002c106808010064001b8081c25507941c0c07010a000280050030282c81c110321541410704459141001220f1143e40320714054a240b50030b22000425465551600c0f00440d4010342c4148a41940c985002e41181d925080001c1c0d07125991540030028095908103415804210013080001c41e00803042d03621468241c50200925910f00301072204401550149031603074800c3c081c4c003200040703c039001412000c1d4010040c05c0700c2c071124800c00801c0100d2048220050b5152105043d1910090085a400c02000ca80c0b1140c40301000040d420024407690019040041d42e201090a5900a1040c0000400881f606115000d5000c00071943c508050f40d084501c01500340e081040d00d42a00c4546000c0c50701003014080c04291554880c2100e4030180096409080c044000800105840024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 105614289 1250 105613039 105613049
    0x105130603020304110906150a090905010605090301150b0f07050328090501030c05190908030a051b0303010b030f070e190603051e07120209040e01140109020f19030213 74
    0x1695900d02841c0450304841d07442841800741140406110142c0d403014540fa8045c20092314094650b6031044088400080d290300100d41280342c1400801c1c0c0541c030100409603110160000c2c842c8143c8104455441b070010303c1900742d0701100340402e01100c80f03210010720703140c1d0050045a0825415048400e84944444c0c20704a0380c0e5200d00541d03c0706500401e103400104401d0900300089080224064000d100f00310141000115109881a040340154003481c05850b803202142c1e160309080001800903440b00036000100300300208103d0341c061001040724142c03101000032a085450380081c64407150000b5007080c0500121684003030186d01d0700c4002c0d030860303207400800d040480c1c0742040107802c03103102900c5400308160303955100c0000c012505100750082924a4981036611800321074900034007440609540c8641040d141800110f4150442c0c402c0d550b0712807804407107903a103c3e0048201d11842464107024541072064914040c0c1404085072805020700f000344ca06042d00000b40f60312003c0d07401c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 105615539 1250 105614289 105614291
    0x909010e010e090a080d050603010f1509060816060e030a05190c0617040209060f15070b060618060a030603061e0e0a050309101404092016060b0105130603 68
    0x10004001e601210580000d00c9101821039a01d82d81c480c05c4543c407584580c020881d48030b001007003150b182540481302c003852010702045401c00c2240d1844040100e4441c00f03540c00c0c00e000021611030000304503140603035080c4000d40d0901d460130400703890942607441d03440c0e8940640841340021a0060080511010b00e01414802c0c0f68440d10700b4600c0401e041c2c0020040103503103e0302003200c0305200c9015070850b4044540302c0541d80e034940041c0c0b2404603a0321007504143c440c1d5a80d43c5000c0d903d0302400205210f0390314902240c2d48d80703043c0322080c060b050003040e8082503100030702c940d0b040c031800400e4903028030f10700840e00b90788a4441c0c20030303622941031840b082c8009400c0054035a11034031a0703004910700c00000d010050181e4441903600d01900500511a51003815026403050040c400d03c205811818070660710b55a4527510100200002d40740d2106121684030412000107550702280c5d407600020803445241c100a46400340100010742c1e0b1035040c008200303e140380c842018031032000204095a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 105616789 1250 105615539 105615541
    0x20403080414040609020f0720030a05100515060304080a050906040b0a02060a1e02090a0e0910060e011d070e040f020c280201050d0b0a090501051009180b01050909010e 74
    0x244021113110b584075019091042c0007900f04140380104440c0c0381071300032030a61010b0304030040d91744c1105030001c0c0480d450301c00e20341084100000070400c0b08180a40302400c00a540d1542c201c4c20300c45010045465025104000240000d400c0170301074510b080e803d14005040444c080049441a400f035002036802e000045402d1103841ea041244551291030b4110901c1411445000d1600c60105840001c001c282c006c07401030344030340ba07840e0344900502c070b20214a0b81d141001080180c40c0c04807043e4400b050350820101003a0300110328a12070481e1043c1100881c05600c10f00200440170f006400e800030410104d03100380042d51540914071441c20989070042ea00d0240400c06031400e2110502c4000742c074001300d961445044014483d0041035020300740f0a0760350401262031802400340c2d14401e540120441c00106e880e0303000d07520080c1642c105032400100b08284281c00d0b10760601078804ca254842d210581002061001e404c003c0c550364060600e50305040364075001580f155006d80006c0b15405c2404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 105618039 1250 105616789 105616829
    0x6060507050f0705030c13020d020d150801050c0a030207110a081608010605030307060b06040911070209070e0f041e060b030f060607030e150405040504050703150218090a0204030804 80
    0x10010007075504201c0b0050030064544008680c0f1100034103003e500c15071503811040595903058048030780380301c520403086654605d81c017800d10041494641c04c03188001d05a4012681303510503c80d9901506800e8440381c01c02040f4542240070794000d800440f41e5840208918060391220041d140140180078040c0481840d07d903c2940c68ac400741c0d0ec100603a0381401000c000d1610b01104841d2515000240810b00c3d405580100c1c0052141b075004040c4945000b0044042c103041e400074200e202d2013115640f00680300d1030b01c102c402c80c030600e40c441d90100c120302440a40b440d165100c012034800b113901c0d1088070829083c4120803191158040442000000f00f042154a2208070013540044119289410290241c03001405c0c1141d000d0381c180128207460a102e40e841000c0705540040ca0b00400c107105610b007d00d8160f0700c469842c4007c82d80b03902e0503030050141400c00d00039039810b5840b0b0850b10f1a01511441001360042002d000010782c19400c20011000c5880030005001402c500700350784030000c51013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 105619289 1250 105618039 105618043
    0x902041b020d090e01050411090306090318040b010e09150d0b040506010501050a050304142a210a08160c03140606090f0c030907090501060f1103190807020f010606050705 75
    0xb0350140c40c100000050184541d8440c482214152641070350005010f0320181540e80c8175200780c5032019410f100f039408000c86807500200802d14060b02c080c0c0300a010303088200b48010b5651403460180451001201c8604904040b05480e90000005820402107c14540490a80781f44800e0988800c4104010081844801c001540c010a805c2c80c1480c0342031f045000c020a01e0201400c020903683c10030300e0100200e81d0400070312940320110a048000172680d808514240340300c02e400c0f24000c03502507000c180040040d1200186250101c0c010300200c0703500d07a40c2d800160b440645100b12580c899a00000414880c0b00503a000d10712810040988200c81c1c19000c2c900b00004200c20301c6a10364070b040210307003c0c080c075051390010300705052191242c0755610000e00308403480d00300c081443c6c0f8020000441030b80c8502c52a08180060310781240744040642072070b44a07c0364000c94001c40081e211583c8005101e03108156024030140705545501900005860958000f580800c0000d903000c0307020800d000341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 105620539 1250 105619289 105619303
    0x60801151202030a061a0405090f181c030b0301270602070c08060907090504030f0e010e13021803031315120c050711061e210a05041103060103030c020609040902041b02 74
    0x5240346841c109231604c0c2c00a500418001e000c40d002c40d01500200c3c01c0c0080b0300d11015007040075882512815032440d00403a641c41d006001d03905c0080d003480c01080050806104842400709514407405c00845081244690740361040d200f182e00c99420882200844c112071281d00140030f02c0b00162456080c010540d0f89813080d103330080b103c424941800d000020f41c0001000b02c1c48040b509003011141d6041e00183c540c2040c0c0f42181d0341008502101c00c0342007406030f00400400f0300c03c0712a11500b080c10f1040c15580d02488001e03200481101400b84000c0301c7e4030b40242c58140d2075140000c0714203c08880c100c107032800c02c030032180884c4007c2080d108100c0c0403140040c14580030b889071030912248011002040510740000c01015200040e013611054406007041000d01d2000c200d1040b03802c2c0443ca0400800c2c04480a644140720030303110841c146400314010341244d0305542c03080150880ba400300b091603131141c4403860340b040d0340764400d01c0180c440303000d070b00c50001d9a01c1d420803002c92903440203820310007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 105621789 1250 105620539 105620579
    0x8070503010e030a1b06060503030a030f05010b09090103060f0204121101020c0f03060a1a040c0206040b01120305030c0a05090d050303060909060106050a0c0203010603050601080a0c060801060801151202030a06 92
    0xc00c1c0002c0c4041e550041062403001d9440c034010811741032904140c00108055000b40d500341c0000508460101d405d82c20000107104c4c039007001c1005a030380f00144001805000b816592010002004201040d15500640c4811407a0980140f40a80c7c683c03291169600e008021598514007031032440066805008094041005403620b003c3c1000d23000c00a070b196400241080c0205685a42002e2095803444010000386006801000071100480000e541c41c0c004031012500c140302c0b84001301e03103054800d00700030201d941902c40a0564a032200c0b640b04c5604001c1c0c80e8070400200b80f00740d034825035070003201101c0310b4048da002d5a620b061034418010301c081d004011a216a00c100010000140e221007240c81d2001240707840281e804407840068003506856102404600c212400480d00d1000841c003440d150b4426800349400f140d44010540d00b20409124400c0820f4413000100714510420700401c84804480c94800c40151252018600320f030002e68002044581d00d44040c40800c009a00c007040540c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 105623039 1250 105621789 105621793
    0x9060b030f0d020111160803040510021303021c03020319050705010507050d0c0c020102030d0f060308040b1b010608061503030c060a02030910050405190212010603031d04090b0c0a020f030408070503010e 89
    0x80e072803132005096048880c401401104000005003e000ac01d003d00a080b100c3d0740010365a502c60001d60b042a21003901060744920a002d10700f4030314442524203080c20542c1a00036504141581c0c9205000e101000740303542c288030041103408001042032103618803034621600e4a6407a4440c2e04803081c1200d0310b00e5458014480e080e4030040251303800205445c00c20343d000d640845d1050354000c84101514003a40000c04c40140070501180544401c400b610b80c4540320403c900114401ea8000c90030307100d84e446051204d400c040c02243c1803c0000d200310248e1030014080700d240405284901d442d001040b211002047e5012082c0803516200f0f020704900c0f140d0502c024089820700e1b40b00c080e06d400c0c08201115850409090b01021034a8200c22000d0048680c402040f0302c0e0b6880c00c3c003510701c43c1c80714480c0d4603071091030f00340c1c54161400d071140c4d24505800103140ea0099842030300086255000c01060001d501c5100c0440b000018104010409800f1590240c4181d524080525081d40c1070042d11125607 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 105624289 1250 105623039 105623047
    0x140103121106100e01051c060b060717040503150c07020d03050f0a030902010f2a17040807032d0611090a0f09051612020a0e0d060213080606100309060b030f0d020111 73
    0x24045d0784890081c2e000038001503051402c00c000f5105104290300141034100c0d11102081c040512804dc0044410540a0381c00a0400303400030402d5070310450b0810940714081c40444091f0400040d00401d0074420b0074824a40710288418007600e400240800c4d0000341c030380c0c0391030085580c02440d6410a40c45800c1400b65540d08404001c603100b4040a0521640030490b07104051100561f0300c070fa660b50b00f441c0081d81c0c0f41e8030360b10280d45400c0d590105071071000804240d4080c82c04001041104108008818048045941c0e42d6070040d004605400c0a014400d008007007040da60403501c00c00420003010b050b005945441e40810680d20010010b42047e0002c508110301150000c40880180580010042c0d6820303100d4070580d90106203000040e08120103c900c2820410264000c1940d9060a2030306201a03a81d03039481581d4900c101d403410b400c440c003002e003000c400303000fa00820a80c903c00c000206903000e40c8804240351072480b007000381e43c0350320444c40c2d01401340c1c081c407400b04c0d4094001002490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 105625539 1250 105624289 105624319
    0x1404050c0a06080601020307110f06120106140f03010b160213020a02010f060518040c1503051f030302100e01090605090307031b0503092b060b04060801140103121106100e0105 77
    0x108d0203003d0340034009039002e00303002c0d03180d0755010350b041041400108a1602c0f52014404001240f00034016070340428002d1107107044030f01907003043e1114600c96001c0720f8510786c2085034215007600b254000180210b00c0c48001c2005a64070f6000c50454000c1e00001078507205140c0c2e0090079501c5811040e140030f403602c0e0003400140c69148481c05d249120545100b140e44a03480c041c40c50402d40ea102c42401d03507072446041102a03140e00018010900130980b0305084011070f46c48404c0c68100d21004001d64441051107005003407641100b41c0000a01000040a14183c1c41d08002d40e08101c0781c444064000050410406030400c07080082c65403058540700c074213051a500c00380da902c14035608600c50541a11030010301810740d400f8081c0130001d484d200380c000d0b1003850100040e0001c02a07080c825030a040c400318643c0d40503c140703c600d100400c1d0710025646540c42e04001181e110b84810700300040d516010002c1101042610700174450a4000ca407941d19081c01e0341c00560068020354428041700400c080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 105626789 1250 105625539 105625543
    0x6160908150403051b1e06070806040b190f0509010f0609030f02120a0b0405060a0c0504091503020a03081c02070f11010915020304080c03010504030915031404050c0a0608060102 78
    0x1841e8015110100200c2d2207908080c1c8660040c24000b41d2000c84800c542c0e80e9145020444400d6211301c1409180c0da10705041005866110840c0e5810005183d0b8002445514258120307234000c2c903014000500e04a000c1c41030031031103000d940101148130300002040003e0304090144500601c8191404201a8142140200040301da840301410b80403078807001c0c20655a13186d07034520481c404403013110181c004e00d01c1c0468103910b0840f4180c03031900a400c0025484038503070081191868484d03070750314605400c10b501a8000d1244007620119641050400300040e2038195486024500500809481d83c568604450030380d05d04080c080c4844d8010b2141c2c00014a0f02c0118000c5150b1101300702d00c0c0504500012201015680e0154004126051608a0280c0c0200003401540c0c0351809a40c088400c0c0000d2600742c3c0c20995000b0002120204200502125003814106007080c0c1d00d0041280c0c40c6028400c10309503420355044c0c416400c10345d0244420b02e4506180d0b00140698101203106181c00d2002035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 105628039 1250 105626789 105626803
    0xf080a02060d0b060409180303141302010c0501020c010518010c020a1203020334030b091006080405070803030106030609051501050409110c030d1506050313081b0f06160908 76
    0x42c01d19403a8903900c452541c44106030b074042e2a40c128200455100054044c070b643c00c85540c01d4011910f44000d010807481c4c04c1240030310030490685009011040da500440e803460408030700340d80719542446a40892582070040d2401004641119001c51200caa945421a01410180810340d44a030580340c1c0064200d0800030b0303841d04c80c1d06005840e50342c0c0f41041c0c05840d1406070705501420421000c075005400d084c00c1519404042c1d9402c00c02c811002c03091140b403000c00c2c1e4a1201500d03040400f0003501303120782410f030351243c4a0016103070031554800d040362070740d0400c0c0c0141c4007083e2640c0050001c28104e10510b640310503001a0a00c9c8901c01c900082e02522039401006040d5480306800e00004654604881046107044200c030754901001c01520001d20350100c02c0403001c00303200c40024480d03120364240c80c0070b8110416450003900c0140d075280c8150380080340e8210b41c60507000007105400c10a0000415028441c80030780210329200075415400713100c40e0940c1c010300c1800681802a00c00000b030071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 105629289 1250 105628039 105628057
    0xa050c040902030c0405010306020d0b040b090a0207080d0509030406140a140c0a050a0807050f0303010e0f06042304060b01020d0e190302060c0a03030b0105030606091011070902040f080a0206 84
    0x19000c9030718000320b401c02d4414408107401c43c1c00c10000000308051540241400b40946400300480b2040340100300903120000c502076441142000030811080c229401407000038441e10505240150103410541070740e800301c90b840007542021400700b150359000741e10704102d842c48558191074441c0c000d20192900c1801a901800b0700c2021800020f900300c100040348045400504607441d0002604d0711074504d80c0300000031641405901400003492030700100b9281a1900c1040d00d091507540d400d994a070b024002040d03030b82e106458019008080134040200807480c01903407002c184514284c02c000c803d0714084942941150f02c40e0402500c0c081c2e000e4000040300101b102d040019401c85440c208481d0301c0703500044e62202d00010030030702b40e0b28001143c8410314030a45081c855101c81000540342d0b400111036a94020800708510501403a0020145504c160b9a08052101c00c5181500501c1c280040e000092035560000d01071281c00f411807102c3e0000c100d0f0b200200350300e400a9012440d00d0041c0482c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 105630539 1250 105629289 105629291
    0x80604180f020a09020d1506050901090e041104110706200435070305010608070308041707080f010605010806090702030f1615320117010f060e16020a050c04 69
    0x141c504658500381c4500043c008641c040d0f4681d800c000300d41005240c03184031070a4605500500140300e0340104140e451000c0305850350702c442403070020701118503540248211054a45441e4440c800c3da650300c169561444c0003c4083d40b140410302e8608221428140003000b2500c003040c82d086811a01030442d02a14481400c12114180d004418a407510078000c0d103c0c2c029040300c0318480c007004000b41d4070301201c7c0034000070302085503075000b065110403460101401c1c0748020041070151005100310000e1326a20041140d416680d107070301e414141309525400c04510b0751112010000c3e507a0113001c17650056000c039100151410003500c080d640c0e2041d00c42000c4c00840109030384441c150311608000381c0c039800441480301aa01180310400404003001148603c1c00b440d2030044e03914412040b45c0e4200b40312800c140100d41d082c0a1045d0001d00f5512a000c5259264107840e004c5103e103002d00002400701d20103100241c10711002083c4002446a0054215131000c41020003040700020700303814040003030b01c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 105631789 1250 105630539 105630563
    0x30306010c150e1c0807092c010e090c04020309100513050a0309060305012c0c0403080408031308031c0c0c05060f01090513031d010513060e0108060418 67
    0x5050540c0e00c982d191109080b9141200d20ba014030400700322403006040c41912004401851202695030490070342d040c800107206040b09000405040c2e240c00b074444400012550038041d04040c640d040c04c1d098102c800d180090005000d44802d042040c45072250003214158254a025240b4959030540d4000c440e400980301c0d808249459030745030100010b10b0f0850140c40400786227040182010803144109000240303060000100d4215986207505854034144011a0302080e6040502000d0300203000c50381c10206c100f10010000755108024401030102c00081c6444d101c42c0300060fa2052040d5024844a4000300b1001c0398030685401e2060443e00d12444c0081c0920820f402190007603030900c7e008045e407190f901480f514079103686541d4100c1e440710200b8855a511440e160740108000200200410f02540c1c0c03c1c80f03002e2000c0400400204180341050600744d01c0342c0e166241e00090742c40000441d50380d0345c0c855071765640711003040e510031401e6400703100c0035107a0304290080303241032007000e0f1104840103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 105633039 1250 105631789 105631793
    0x1021e030615030c0a0801090605220b04020a0306030b0a02070b2202040504050c190614031503070308030403080a05010b161a0a06051305070509010f09051009030201031d030306010c 80
    0x240728441c1e4a208044083d803a45030411140741c6a40c0135000c2c103800b2a043c14000910074065000c1d41081d1b80014100300b43c201003202901055038410100766402603112003800481e5104d62026100c11500380e603010414624504107050712880181c44140b800d03004111600202d1714400b0b00710b4110861100403410070f481c40340b602c07444100c1c100009501c10f003442c080c032062200c000f5000420800854a8204103c003042d180c2c03080821341d101e0000419031030401303182082c1c8190302640d07002004000c00038074014040006428204290400c4a46100100074081030560088010f40d01c00e060100070083c5505000301800940204144c51069480c000c0440b42081154403a0045501410182c0125401c08031905405070040b405110300903500328440c0408004a40036a500030019601d03481e1502507002c5c01110b030500113150b15004e02207150303000911030320b5040c04070301118080c2d0f45a5561a0a5200040076900f1041503079111000819084030160408000c61383c20401c242010300ca0000303a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 105634289 1250 105633039 105633049
    0xc0d030f0903020409060209090a0b130b0109050307030506070206010f120204020d0b090a050601031a06030106081308040305070e01091401090b0d0c08030705010c090e0c0f07200a060201021e0306 86
    0x350b00002e400c80c1c20304c0c60b200d040201c15005001d00020446200096649a0603400101c0300c0d106c00841c2e001ca550300880540d40746950140c5580103040c0b6141400355116000719240c4110740e80308680651040f810065015410f000d074501503c01d4032840c003450b6183c01c6001554903002c40010388102d5000454041c0d18400390b120052400003e411340b91640340c9140360300010b0030102c81c001d001c0b034100012240716640d01d0400340c480f540000c0049003140d09081c000c03a5400d07401403030400c0203413040b560b540c045003860000c5d0004500c564000c00b81c4a05182280441c1001a4000211907090040c51841804076030320607410b50710070410000b417500c01d040000340c511402c0c0f44094214041c540f0081a50f0300d000c0700070801640a18024000c00038000c8045a40c485917129941d4440014400310f0760013503201004010940300c0c144030b1400d0800540350041d00780b4581a0541c200304806041800906000b080400100101c0c0021800c015200c00503802c01c01d940ea40c2480304450000001d0515510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 105635539 1250 105634289 105634307
    0x609120a0e1207050f04020a2001060b0712090b0c251a0403050d1b0f02012001090b07031b031d030f180603010b0d020c0705030d120e0c0d030f 63
    0x1008184140782881c0c6001251281c8880c040c040c01792400c0c4541c0c42e50b504050080314035a54070b659421501444805d00841d58182000c0660825500c6400008440a40602074280e1038000c250851414400700c5000c0d000c1045036108144524050101000c80303c800300301c61101f80020950854064824041d1403d401000c3d0001c1824244040d1401060800c90010340300b501e125200315145622010030944403010a441c401503103050448200380040c01040c8518019441810b10800c0061119451144010741010b1080c990b95590780300c106200c042c1c1c5140340c02040508003000b04101040e003030361450f400f4051810500d42c1365801108a1348181e042d00c0351a00000c401e40f6110800c2c0c403441c450a904c000a0394000b404a030b20401050300d4820200c83c12905420140d0346030141d001840000fa410001c0180107a002d02d00c400140c54500b031142d900e85107102d944129018090350044412130b1a05480c141d0160300000c514001601c031408104d070001d4050030200000c28002c07108840343c00d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 105636789 1250 105635539 105635567
    0x10218010c02180c1804090210030209190b0403112e0c080f0a0807080601050409090c030b01030b06090c040f151808060702010c111b0d080a0201020a110f0c0f04090206040e06040b030609120a 84
    0x794004001031002c408003f82050302d20a25407041d0410070ba10401041c15040c525022039024440da030603480004036030340000c0090490802c140c801c40c141d203426455801400344e50300c43c4403002076000001503000b104113900807164101480075040100008006c0e006c1d81c040c40703c82c43e03502e2242c00140800c00380041c2c011130b4041414551507071240717071448650005941090007a07440350081015644018240c40a5a401e4031303101c1021440c0111880306004040b03911814400c0e05c0404424001d82a0040350141803440000c04550409910081c21103032035040e20010130036900140e401c60100815043d81d0014607c2801001115040c00200240a0040c00400c43c0b000010841400317034040d005000c1805907502d4200030907235025001e58891001540040311034100c00d0380b00c2084d24001c0010b2084c441c010744009210b01c183c5e404101180c0c080c0d042200290710000070000e0f0b0703190a0054050000c8180d001e40b0312070404640b0160b07181d403e2011111070010218000c04941c1c45070813140d559207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 105638039 1250 105636789 105636829
    0x9030307050708010b03061b090105040902340203070510170f040210080405060601030e0115030f0c0b070210080408090d150e010218010c02180c1804090210030209 72
    0x44162070308940c0c51005115101c007a50800385410042d10303012403654440c58070080c2c08000c0c1001060030200c143d000f0341c200c6050080600020400c2001c1e8401740007403060142280c914011410800c041000c4c95410a04204000c1c0005d400140c0f000f040e02d80841e0340c02e446040030340720702c0d000950f001d082c91080c40003050300340c6040102d0707040c0c103610b540d006500035503068600c1e00003d0801c440c00c0f441114060700c907a2140c3d01181c80d95109600034000700300e00c10000521003c08000000038286507a00c00e440c030f408507200f1401800844020007000306400c0c040149040110b5021405001c04808910144603100002406100c0c002045507103070f1400a00c180d0b03980046241c0001006071058134428150302d42400450405414421035102a55042d041180c910007840111741c8030251050880c2c005da0b1413000c000303182510070380807406003101c0548691500840f0b070340011a130040c0a0404d1065041c01c10301c40142c0c441b80e441c1a41e072003161a01590781d016040204e0f007001e03401080180c400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 105639289 1250 105638039 105638047
    0x180402180612040c08061e040c0e070f02070504140f150303030a02040e0610081506070501050c070512030601170a0b0d05031312050d181206140601080709030b070203090303 76
    0x160010b90600e01c16072003003425070315594903080a195540b20407907828411032610301030307401074a010000d19948148100020030301c860f01d5110483c41d03040c003610501c0104003d51901c071441601030200001526050794200f141d005001400b4104040191071003601101a601282c0239400714400c58116030800340440e9039031306000318000000d50262082c0c0d072869070110b004c84e000303107402500140040f503d0b83c1d6032402d5495021340415880d01c0520110b9005030108002d000140081c041c580c400d04850300025110f4905040850070a006120240c1c0c011000b00208002c5a800c402c800c1c04003441c80078012015510281904028081c2c01c6d90cc580c03000280c6200c108104001004010603000c2298404502e0f03503440c04503e600303030171250040c119040100320001c00f074410500c4c0c0440c15040100940740a80d2401d00c01100403001000b511039640342d0002d00c464130301142c0900d4000c202032816100e540707092000101035070700c240001403070512a64003241c081482002641c2d0707405001000e8a6071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 105640539 1250 105639289 105639307
    0x50f011a18182802010e01110c0103051519080c01020a080d0b01050708132103050d050c130b0c01061a091908100605100306030203030a05031b0a0809060c1804021806 73
    0x102c01e80943d8100c0c0014090490203041d54401c41a043c5401801d0380182503540b00c030340c0154080d1070002c141400c4001014500706441e6141216440e08000c0e186e2551600303402c00364600e0410704500c103c5410365102c000c5c00c038000f404900c11200050444100040d0b0798061400403200c500c940130b40600007200200b0300001040c170040c0640129030030080078801c81c000f448920f01078840500d002901091050050030681c40380da07000180e10401284003540b4084010a140030341c00070300d41000e40cc100011504024140c42445100c000e807000c01150b0403191520402d212091241801a80c0140006080d4440302c200960034040504865000d40d42c440b50514450303001050f003481080d2050500751588003125009125031400c0da034016019501d0500443c8055949500c0900002c80210328042c01140390350301b8402915401805513106211418070b9460245001c0001c0d000400d00142000099000303401c0c1a90710110000c241d6001d41c440e481010090301201034031881e00e400032000500004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 105641789 1250 105640539 105640603
    0x9050309091608070f090b0706060b040303090e07030b0a0506070222090204240512030405090103080d1a22020d02041d01080303060105030103060f0207050f011a1818 73
    0x2400d031070b0681e0f4041a81e6a403620896002d840343e403d000c0450b08001342407103554125401890098006d00d00454100e07070344d94004030140c2c800ea109800144580005110b02c0c003140486a0308003080c0d240030710013802c41c0400594401c80c90311070140715401c001a04001c40d03c0c2e041880001e402c000c503800442d032602c3e524080203483c0e1002e04034466898803120f00f91032000301039840390070040c0000720501242400c041c4180080a44400072103840140800962680d07009280ca0103588280102511800404841d001b41c460240c0411003e80c4001c01414040d242c0440741c20b403256060070040c10400801142000074400d8404c0e200c4400e000080102d09000b8242469001c440e810100f115140c1c0d0300c124094030b030300040d00c1c10b6000650420041000c80d00c180c0041c0b04400d220320005162014643e1103d181c42c111040c2c503400d6035152820000c07441d00704c00e9456018402910b086401d8403c1e01f45400e150200140304400c2c044014212010034502040000c40006c01c00c1002c2c0c4e140c500c1500e00e00c1b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 105643039 1250 105641789 105641821
    0x1032303161a010f0e060108250e1302120604090f0506070f09050f0102060f0717090d0206010b0a021009020121050a0e030903100c17070801180c02030d09052103010509060f03060a0905030909 84
    0x2c0c0500040d01e8089030b4bd000301d1003254101c4480b81102e00482c1c0f201c0c410070002c1c240c2d40b1b4055030660720801d1401c2c04610180502c0780038200ca030b201d000340350054442c060101d01681d03020741d01ca4000300000021690b000310320a43c1c0a008002486040d40d00e80d0826a010460040e494080c9001ca07070400042c03c50005400400794040c0e003c44031143e81c1c80c03120030700501c81d000c1004010b8102c40d0311001c01891a80110051610504040050b0007114410300c1c0030a140c520710103031725900c07002804285945072103440c2181301420003440c0381c6414280402c1c0d40d41a11045071043c90398540c031180e0300c01d110f021003c43c240d84420707002955080c07001d401040d0720401c0c0107151400e40503101d440080d800c030b40b2819441c080603402860800480003a800000d1042c500140c07600c0c02190303c00c01d80c030a80f0192400340301d40c5170041c00b51070394100014011840c1c8020941c600600714140f0b609181c0ea07000845a034842d0b10340a0210b030901181c5411401d50041c0c0c400142c01c01005001d01403145109008c203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 105644289 1250 105643039 105643067
    0x408040b04081b0301200a0903060c1e02060601050a0804080f0c10050703090c031b09020c03040806090c0a03021306080a0f120801032303161a010f0e06010825 70
    0xc143c0c6610070405007200e81e00507503209018030b04820014080f10840290142d40500c2c01d2100d412682c0c0c1c1c4a40054440a0f0300c01400144070300301806c81c1c5240e030080b02080044034801080546462000a0103d2140c80300c480144552100060200f10382481150a0b03544901605902c0340c0d0780600c0c4070755030080ca035420710300c0d6400c000024858500c24890103c01035088010400d401340355807544800084100c040b0010490010408140100d0301c0c00207000412400d4020340d030365480c1044603418028081d1002c1c00d150090040c0c248107a48000180b010390b50100da440034600002111000109116407054100d4005c1c13003030403001e0007102803268510341c0c090081301e01c1d94081d4413001c881b41d201c2404000d041c804031402c5409031521440204016111003c1140d14048030510580c03511034040d10120344060031481c82d00308030034a03070751a030b401041140103e04c0e00500b001d40c1444003443c010a5241044036003400140d2030072860a54290b0403003a58030b9a0145c445408005203000700c034100c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 105645539 1250 105644289 105644323
    0x90c09050909030702030d030506011b0c170708030415050705060723070b04110103140103120207060804030903020108060a21020411180d030c0b0712060f0612050408040b0408 77
    0x1c0b601c0c0e03404412500c5840c0d0040241203107500c449420381c02840080c004504002c0a01c8101c84041802c120810825005003030441e0301b5894849003120b000042c1d0751088180d0048007040080c0f18000040d107080d186081003151104485044c00c0707903103005248018101e4400e000920a01540051208824488aa04450747d03070707512000c8486a4411400300034002e0b41e0280004e808191902140c9404ea00e0516000c0b840400d42c40c14401c40f10400c9e001a01e044002c0011840144d80421001d0020049403c0210346498070352405400c0446234800030b0305012a5500080e2643c0c1c5285c9104090302c0000d2000c00d01d0800c01503188650013840108902035490f01801032a40c0c0e144405076400114100e0450030001c0a02003446000340d0248012024005d501d200d00700010120204288200e181d0355458030361750000481c0d0026100d150f4000c03c41c038028070360140401948000c0009509505400c08900c9813a140303490300c101e01c502e511209059402040110782102c0105603500c0e80580014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 105646789 1250 105645539 105645541
    0x3091c08090d050702030a0b0402040e0a03110f0d1e051308030c1006050f06071103060c030709060c1203020318070803180a05031c0e0301060f08060a090c06030f06090c090509 77
    0x200c280d86038401c13410301a5265000c03080902c00220f905c20410380c490310142001c52046000d445d824500a0704500840c08140030180e4410000700421401d403043e50030000500c68001924006000d0440300d40c1c140107c2049000300d486000d002d41c0c02c135201c1491056010182590300d00d50152250410306d10000d482c000d0300b50704446041140601425600002c061810b10744910f01000b015900810085562607a88100b213809545c003880040d1040d15110300d00c0380d0301d02e06684020107000207a005817041c4600c070f12101000c103904021408550255060042c0c1ea604d4180070042e40e03c41190000c9600d02ca00c00000c1141000840078042da070100804101301d0140807010414003180c940141074040c0c9c001c1c92104419185c003400060400c9003810000941044500403a003074820503007105d803d19335102400c01c84c52000304a40d030341c4000585c0003000020780d15500c010f9111001d100f66070400d900c4100102d1411055030102001344450841000524a42180070708102c213184212072040340050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 105648039 1250 105646789 105646813
    0x2003011e05010e0f04090f0c0f08030a0509060702210f0f0c030a03030213090504060501050f0d05060105100512090601080606011701030201140d0c2712020603091c0809 74
    0x420303035000d94405850b42d8518026960501001007003c1d10003960054440940d0004584d442c00583c0d0315a001e8100c960806041c165643d502c2d143c1907018030307915030003046042100395100382a500000001c96845035601c01c0c0c1e000080c1c2041216003034010308200210114100071000854503c2d210000083d07a9019403c1c6206c0c81d00c42d0346c405075250705a0025820031001038441e600030001c01c0e503000d654603400d90300c508150301140d008450864440d80e46e04014445458210115000300d681202ca80c044c9440c039603a46500c4000620915005290a85000510700c1c050b80c191003c801c4411400300f000e2401028a5a56000c288201606030050340042201548151240c0038442c490395018480c50f482c42d40116429003620941d0380140c00240250300d4001607500601003007481542c1da044d12022200240c0001c400704d0740c072846109030100010400000c8820000391402d40413502a5180d5850580242c200b14030b030080d0b10f08e20b00d03446c45014040340e00420014011002030b81215200c00c40c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 105649289 1250 105648039 105648089
    0x90b06030a0b01050d050f0f10050112020f09060109080d05091e03120c1c0216051207030212010905031215010f090b030405010e0d0207050405060306130201080901200301 75
    0x90140500311104000060115085c8004125000c40c401c1007110f103045112150305051017000c0c0b0100d11190040c041820540b81c1c0307070080718007401c1c5201c61100311001c1a0700007403090605411580c020500307840011140c0c1c1c05002118010700681040d503060060306000141643c0c0184003081c85215030103183c420510960700405030004000e00207141510100001880d185c02c001020321803407181540d0380c0304042c1c036080c60700042403045d0010004609864030101c103140c3c1c0c82e0012030041074080e41d0001594800105e41088a40507a0071f5940c000c50940e440f405002e00d07003030140042c88005010090204145505440340042c16800d101100e0340800440d411100c0820b01d10000b41385035418803100e9410401590803a2050b400018201c0b81202003c0c103000501d0800001340e002060b00b0029400d09016540d0b00c241c0860181c01d5504d08281d400c0c1c03001d0f8260348044c3c10402c24034002115580c09500441c4519402407100c0e0541c25514940c0c1d025a100b4014100000d8815200034107c05c08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 105650539 1250 105649289 105649303
    0x10f1d0106080408070c0b07141005100506070c0b0f0307020f030703050304120c05070306060501020106080309060f0a140301030506061e03060610030609020d1b020f030d020904020708030a090b0603 87
    0x9580d5a000341a103c64460183d1900142c40a481c1c0090400c3c00248402010b4005c101e424401c05107480d220110040c02420154000e164480480c10041003102c000307504060001902e10032500103469003903030704000300c40207040d4200000e00d8070006656020404200027562003840e0650031a218541107452050b01d9000b9010700074041502030011600252801203040500b070402c1c6420f40000c6261f403900e0f854800c02e603100b5140720355a44402d100d00d503420700402014001a400551812203040085a800d20031860900388001011507a180514800c03240c1d000b502c05000b00303103511386d61030382003c3d0b46812003621114810369030501e41a00c030500c1103142ea014400d00030081d124607566801805020130540809804045d610701d00880d00d60181e2025206076205e402e400648032401e01c40080309178404d04580c100b0340d406550740ca000b290000003100c0356400b4404025840b2154600860042c1c040e8480041070580302000304420800030750b01030521070380110003c001c10f0b00c3d040c1c10f140e26200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 105651789 1250 105650539 105650549
    0x305070503070e060d021201091103011104060504090f020903030c0705030d09180506060c0d030614090c0f07080d0203010b0d06050a0825080a0f030909110304151103010f1d01 77
    0x100000d00324601807424905c4540081c10750a80346420740403107402c543c2c40900032140040c03080005c1c0c0c034034203091243d011032080303000a172440d207402e0090140c85070041c0e00c11825010303121040400d0040f92901540c05090380541102d4551a015644c9a11481c050150b01e01074403c81000ca802984180120303421508075a00c1c002d000841c441900e0082c14000303151a0b0086003c100e003030001c00d400c00000300048016900000c070700c1c2c14032401040303c44125942d2031080b1814414002500b9a05040700c03a410200c0c00d2082e5520f815141c00c008500440c0d00a0f000c0a101200004080c1441401032010755a09501000703c5511401000b88c010301c1405a207080b80d0140f22015417941140118101140e40b03112406061680c0f010024900503d50404851400c42030900b481010f070000304240240c580c28100380501200c4034000001c501001340040d10340ce111500002000d80107501050300d02e07040e03030015035481da12146060200401440340c403c2280303c1071015030503208a0040541030315 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 105653039 1250 105651789 105651809
    0x80603011802010509012106060816082404050403030b0f041b0309060e010606020109030f020c090403050f070c0e0108210a030b03071d04021003090201021203070e1207030507050307 80
    0x1201035001121340d500106451414001604400300c8680103604e04458180181d20300070421134100030000300310100140140301003500c0e4007410125250441c448541c401d210007164402c143c02e028885800d20b0000c045503810610f01004d202c145030f41500030b00f00200c401d1341c1c04094040e12405101c1200c00c003015018041c0041940d815050b4440d40007541c0d2503002e0074002c20703264070002c08542118220340c03114025030355618001c003c164018560a0000709603001074640080440080350300e10380014802010800f0001c1c12001c490441c2003641d03c1c00e0341080490403101d8072071002031150102030007484424401c1c014803404d801c0048048007590545a07840c28204100100160050004010358a40c50b0103007034030100305210002d02d69182810341c1c8480380164141401072042e0b00a80c0c1034400201030402050b00d0140c0d070001080e04101000908041c3d813035807031140403100420802c4845c3c1d44009140c09180e107041b03001405a01740c80c040c0054800c500d035281c0416690b540300d44207130072402c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 105654289 1250 105653039 105653081
    0x6090601140d02031603060507050304080a0302030c070609030917030403033e0a0c0905040308040f0212150915010602060c070f06050c0705060c2b140c03040308060301 74
    0x161520340c01005114001c1d00140c0c0c0e80e42c8590000782420f440401900e0300c265014020002d120b0540181e60b001030142c14000c1c17a505054560480a01c10346e400c0c6011306400002041140c5c0800080b03814054000c6020422810310380f81c0102034041c80e1140c002840030b42810010048400f100f02e800300d0307074503841d40d1050500498030501049180082c81c8180c0901014814040c0303c40302050f44000406009822498164900365000c4409500322001302d83c070301010000044d407c000302a4000340c101802c0303200b0b114148000749214403040400c0120303010f44001c0000320700e955600c0c1801191414151050307840f03c0d01d212690741d80244105030040c4d003d040461081c00c1c561009004d0a4002c6d40002031a4a841d00c0d44c20903104182c0d254030721484001280e60905c2002d1041c640c2000d01d20342c540d1b140000018102e0002034019240c469002c25080401c1812a22035100c02d03420003040700050a503103002044d914050700116030980100c1c44c904d00003080c0b4078040c4291421301420f1111a101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 105655539 1250 105654289 105654299
    0x606060406030b1f0f0813020a061209141b18070c0503130e0702010b01080f0a0b1c05030702011e0903030302070615080309030d0309080403081615060e06010206090601 74
    0x151100900710384d0401ca465011030982162050400e001c0d03000758640480243d03008000410380003000301400b041025920450f00141c0d2441000011102e25282080f84010b032824494020510480018140c048400607500c11050120343d0f42c1507044c01441d448502a100b42c184955023200c10446044a00030100190f5481d01465101048501134012203080003401d03880c0200103c101d41104404030045070030401c007d44d09000d02c0c801c081d000e203028bc6031420039024010240d8406446400069102c03032103552261124041224804207400600c4800e4107242820703600c9030b000403c142d002800101d102c0d065804099007403402d207040d03560351002ea01c0c59070714100c00035044500100c5040e901d44001d44e145c030755031100c07100281c6038180165554812987c109450007250080b8002494108143c0780045030300070090303e08881d005801e06039101070020030312400300280a00105000006128203442c1c080651012040e10b40401034403410303442e44001a69550022603030001198485401400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 105656789 1250 105655539 105655541
    0x1801050303032815051201020a0f140706020d06090608060112060903110610150201062301140d091208090303181e160b03040804120f06050f0402090108060606040603 73
    0x82160403040100c036420114070744941a01c0050190722101e0140c0e1390244598600300c0d40034024010000d00851070808072000103403003080c02807801801e06c9074407206408050042d0044402c00c0390f000300115550109414868001c084900944400c03c1c0340802c041001c0c507002079007505a80c1d103d1142d90b40070525039103c0015040c0e42c1004c0303040040740510820101410001540500d4458440c09905030603d08014284a1b001d50400c085a05140e000c210440042100341100081200e40058046011340141d41501c203000c10030041718000207229110340050b9000541a0f03214241022034050501401c41d4492030a40e41e1460503041040826900b48100407041c81d00b454420544441d00e010141c00b0402100281150040d50009503c5410316640148a40058103158510b40e0940c185511200b41c10301640c0124041140100054003c2c0402002d1448a02e9484001840300c3d207000c03030202c0403424068030100c0c010f141200020031040404103101c0e08c41c0b0401307020740c0d0400d850480120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 105658039 1250 105656789 105656821
    0x10060c050703120516060c11061612060e09070f0e060105040b0d110a020309040609051e09010f02160201020c0301090809060901050702040c0509035203030e180105030303 75
    0x240610108010070005c0c5051940107214850140c203001495170700d8028007410058045c03001c800150084010001048005071412014481c2c070701d4202c04019030001c0c000020b00320385c1c01c84c09a04d201d4200f0404003013000140300003619400070304c0b0200290303a5000f8400c420400e5403154007041d020712060150765007104c05054203014a04002c03c2010b0f050154070b00350352154208a0058100040414550030070b8000c40c40104070040c4100030910300074268025140c182c1c2003410704100c07500d002c101e070700d102504011061500c0e0700017151340d1a4040c19070a1900c2c50348100300c0c00740c02404181c4243d4034061048092182e00030440b40c0c5040c013803104010300c40c1d0041034024140103085c412113000da12607100d00c1c0310410581d110f441d91031504100300b520300540c03110b0845072940c2d00414040c82030481c040001c84002d05c0c0c90000c91f0003594482d428510003410042150008911034004140350344804500401036080d501003000122011250b500c180d000d000d0700350598420030102d024640d0811910b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 105659289 1250 105658039 105658073
    0x30301050907230315060412170c071202040e0303070c030e040e03180a0b03070e131b090303080106020a0c05060901260105041b081503030d1410060c050703 69
    0x7003540e00d41c0209100e00d114440d42c201c03c0f00860b01200700700055001d560000d403114000c5440314101480d00003041031007031903803d00801d900d4480c94a040c40000003420f54441005041c242c600340c1c0e8961401d480281c204900507032149042c0b03c80c014907030307502004076030150301a5a681165441c10b0349007500d001a42807910f035001551740f8070792240d00400f400a441c07507182d000065860201005e040003090442c0d600f010110030320130424441019001010100030031402e0310050f2052026010a0004245410140414201c04980380c2d0354264010b0312041500e1003601d615040366258402284d490b502c20300014000b0042840500c020306e0710502404c0c8003801490b040e21a002c0c3e40725800560070841c4800d06400c0f4034600140801d140c2400b40718001119950141d0b10020b2a08004001d00030240850f00c0000d19000c07107051545041c012100e0701074a005052011003103001d240c10481d001142c0d00c41c2132851070100801d1a40c821200030440e2a04000100400c03411605d408251070011516 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 105660539 1250 105659289 105659297
    0x4051c02032104020a06080609040b0406060e040609061406030703140c03031605070515090d02040603120c020a120c15090f090f0c09150509010507020307080a120c05030301050907 79
    0x340c41415500d40c50020000c2c503486509000c81e0034648148041469150081014840307a003080107159101c001c03800d54016003203412415a603d40c5c0c10400014100c03604903e0101681000700700070301402c0d070000c0754464030852040107aa400d4403081348c06400d00769440c950641041e50200003240000c100210300c6400a0299201141503400191941c0c0c0b080041c0c8020700059524a001e100007881108010301c0141c4401c403541d080039000d18002c0c490303d56050701c900005070650041d500d0380c1d40460050b691190006401030008030014105480e41441240300d00c0480401240d4800440300a07500350741c0c8102030081c15803e116022115020a442003003c102c258180060280700000b21040101020000002c0f040310f0000e041c415142124802010f014910070100041c4e04c1c0d100040c282006186032458980441c440101e8440c0305094019502d40b14510020a0178840803034004100c03440b4008040c100503040c442079804282251001c0e14a4205200412103400c0c0150170542c000004d1030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 105661789 1250 105660539 105660547
    0x120717011401030308091b03060105060f1611030d020c0607030e010212030f01090614010e06030c0d06090b0405130305180d0605090d020c12060c0702060f03010305030a020d0804051c0203 82
    0x194401c91000268800d4001520b881e00b0300c40580018044504203010022a0310004c0d032118011981d10841881064050304001403141090f0b41c0c50415982c1c02e0b441881303d940ea14466007000341240c021022014802e00919000c13140c0c04e03000084020310138502600090030302d09141c50070f0364800306034460303241580203404086c00c1d2014800f00a40c45030010032500e801c0d0f5414004100704844068014101030301c801001c42c2e541d680c00076821b000da50402c079612a6139a489550110b902e0140c1c00301000305504002000c03440b1a4160000c202510040e2020462940c402008060200700d081014000c11020485c0d03503600d81c100902040f070b040020306440c44041242c1d5401d4100e400468840801d90400e512030100780f030381406003003100001201e1490544140c8203a00ba110407018044140d18840000d095085403901d4044d1101c140d0401d01c00d64496949051494595010600c124014000d6043d500e5455000c0d54a4030702503504540140151140e0480c0d0b00c45513500d601c0004203510040c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 105663039 1250 105661789 105661811
    0x60f150307060c0302070e0705090d2109090b150708030c1b030309150714030a0b060a02030d181e210c031419080c0d0c08010e0612071701 61
    0x80810020b001d035550b50401c406881c03c0007828134840b40c01c20f404400800043c00700c0c40754804159000000110fa807400040a135240c100607444c104441d0f030380c2002d404012040080d412118420807104000814800034604e001040172004260f41c1c00341d01054248001004105000d0140d5804038201c0916481c0030446203c5503440b514003d11080154400030403c06695010311100b00035111600ca0040c060804240140841c80c00c0c43c045040c0141c044009001c01280d90000d0640c1d400c050241c1d9581c2281810094a0760f010806104186050815012600c900c40f0841a040e035009910100042e02050204071450810101035444050081d218448202540000060081261913422000d580340c40c01501542118000f0540d6540622440c10700213464211000c1e91b50701403074500d140d41d45040300460380b40100d01f44440f089241540403044c0c15000340c9024143d508800080394181c1c0c03000f040120a240745544e000450308441c104205c02c09446070b8140440301a40008152000c80c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 105664289 1250 105663039 105663043
    0x1a0f0c0601030f0203010f0b030613050c060a0504030b090c010c06020313060f0c090806090a140f0d0201060918050715120e010b10020304080601030f0201030e030a02250503060f1503 80
    0x82e0410b48400006445120071454240303d1400e0095040c1030030b1100148400003c1d85448004106e5108104403007013410400c0701c2030154101c01400208110385540c08200b0042c032541007030000300c1d040008100803560384400040c032020840300581d90010031030a1980c40c02d01a40000e464030812180d90900d01c40010700030b01a81b606401301e1240059164403201c0010400b000940c86240c0541188091000c10780e008503c0381d00d1641c10214034258034083e014468980001000751100501480781c4a441a59040d04140210350081c2418000c0000c070314104110b000c0c45a1000b030299004035402c01001010119074110b807071260500c6594002e0b08081a016107150b80003101c2030f40d5680704100da0b1803402e071b28400c5018080388005e505050074902c03076541e03030070040c000503203146805410141160b1083c0c010250319003001080e2602c44400d50006543c644c142d086d00e0401580c80c9034030483c10810360586004854001f80100b0098172881d1040d5034009010301000c00880101c01198126102 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 105665539 1250 105664289 105664291
    0x10051204050a05010f0209090105062104060606090b040e07030f152c0f04030c0f02040e0c030607030e0d11010b190e1302060304150b041806060b041a0f0c06 69
    0xc9000c2e0907500c459242a0f0300311001801d500d01d80e00c1c41030107802d0068030b81140581c1510000e6070450340d6101c035482e16088100c043c80074292103c000c0401c1004020850304110116503003511a4502d0030b885000200c01801180503046004841400050125200c1e8200c503441c0d45102c0300010380960480b180c1e66410b1415000303042c07215070981c004c1c90043c2450707100010502d00b4155403495810000b01850002c0f9000c0c00140802c0503401d000d5050225520307014003c560b0050041082180c40000d0a48411000c80340921a006050000742c0c490300030300038400e84201c140c000d0045103080500a40e0003280c42e01c10b000c4250340c1d07010300100c1a140c020484848545c0020701100103458000c00442c4141c0c000c040c4400c0040034000100140c880201b03503900030341d02c00500040326403404c646000409000d40c1d5581d005007800c4e6107a400b003010b0b14203d400140100000d000080d180d00c1c280c0114070891150400820510040703d00c94910180070f00244012205400e02d4904004c0030b1900d4a40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 105666789 1250 105665539 105665543
    0x42402040e0a020307020d080405151302090a0b031e0f12090a06030c020a0b180d030209040c020a20130f0204230a031401021608130611060610051204 66
    0x190024080c0041070036000556070100b8101d0b0254078601d840b41c0029110f0030b00c0d03800c9105000d07220000c03c04000c0c0c1400115004105082c2c03500c05440c1680032a0303200920018245e00030030515021807801e5003030340900700111a029000f040a40c03e4100c40e800c4000e041100700c1c8943c01005210708203414203215005440d0310364003566072100054401c001d11180c0507480300c01454500340030b40c0500d40d00460360950081d04100305023070640e202103004060350b418107411342490040000c04403095070954050700110806480c10003410107040e00a903510205454080c1c81c0c2160b40c00020f050300540c55425000070006442010131128031141102a1090303803903201503254010409000806407090001c00340b1449540003074501e08228085690840d2b00d0002426803c004035810110140075011500320b001829140f01020040d81040b43c01c0e41c0003000160b80c00c7d40c8a24000604511614400740d05542c50001750070b46440390b104010f0961241034010041c4a000e02140d15024042c030b40d45071043e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 105668039 1250 105666789 105666791
    0xb0907180903020c030a0f060c03020403080c010f0b010c11060d0e06010e0906070504031109060102012301030b090d08150a0f0e0702010606050f16020301060803030c19021908030424 80
    0x10700d4500c0c1c0a03082601900078a4041c0d03119039800004030b000b5030007040015400c0080001c000070303400400ca01034401c0e40c1015007a030b4800500340c0c0d0b8a00c01584501c0c5480c45134801003110118100c011180a0403100b03000d0403000c005501881c0c245400340042c000b0780c1c0b020308000303448101c0741030090518800341d021286060604080004031a01801110752218451410908e41800c607034031803280e071a400307810358010340a2000058807a4000d42c086000031024020065201018005041504100340402c841e8603003040d004c10f58400b4002543d425032400394695040304d903115404442040008281c2950040307040100203100c00350b540740e07000685000301e00f0b55035074030704500081d00755242640001d0422400308200a103141d1070005852409610b81d40d0440580e005000180c007502d8240c2181803640800400d1208540102008006032895000841c8203801d08207c141d03140c0b00c0e85040017104000d5001c41c000001d1080380210b500c548200d00580d6140603440c44d1402d07076111194508406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 105669289 1250 105668039 105668051
    0xe0d021507050d02030f0d0c090306061815030c030206030a02160c050f0a050108011e180b0a0801060807060311070f030201051e04110904080c0610090606020a0b040b090718 76
    0x400b5003031202000d0620300d40010340c602501e0201995051141d0500c0700d903944c2d6101600901d20b8890880f00000719002801400102c3c1c0301c880c1054038240780c8103115451413408014480070302d9256400d00440703030050301028110f8655000e00c01680d00c01400003201c1a07080083c02403c181c00d001e050314450040c0e0090042030f040400b441011052504039a129100e0f41c1e9041001d030781d100110030306480303012000c1c086003116002c00203024181e9170814020060506030442c134181065001841c0343d14101c0f91048120380da007500500305c403680e0043d0203544e0004031060108a019400c40368101c00000038441c03402c3d01f503844600190250150450050b5142d50601840680d108a0f003902001e9008040c0b01030f090540d107004c7c0366514102c42d540035407444000601400034107010703203681421810a5811a00e010300360320b14007040e80c0c0110b4410925051000c1601407000415480b404d51154181c2000d858030f4564807400c4a004056800a21075a00080b418540c0041e1102e00d009000b0004284 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 105670539 1250 105669289 105669293
    0x1c1e1a04060c170105100201020d06080c0a0e09071a0c191103010c020a0b130b040308010305010501140f010e0a091103010e090d080f06150406020303040c0b0a050a0e0d021507 77
    0x241d806240311a4200050102c0c52824454150300f028112002180c03e800c1d079208240c03050307019000d207908106580b85071030800501d021010455a264800480d002c410306030319407010b00da41544c2035440d0042d80d03010060034441c40c1006442c056071049012610350405260f40d401c64a462040410b050948104400e0001089030707007004000b0404048000384402006503500a50720883d14201400013110800842d0340c01c42c044000a0610b60001c1c000340e038910b0a41809003c0850a20040340c0942c6800000941d038800400e24000c0d508004081d003103500c1c0742c00c004540390250102d1003680014102c00c001003506283c407074070087c07128032031a0a07240d40c0f500c0790b0109014001052911590000851584c00c1944140e01c1c65200c500d00c8a60042501c032040400c06003040c47e00b035034402c1180003502240080d000409148900d10800c0111000c0344c4800a1007070700d014526440c800b25006000440300c1e01e0042c10000c24401000d40310b0901840079800041c1c2c4100b01c1c0c0616010b4030400111a01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 105671789 1250 105670539 105670541
    0x1e06053a08031f210f0606050901083708030a0e0102040807080f0a0305091c050d050d0c0207080c1002010e010510051008010605040302040f0f050709141c1e1a0406 72
    0x1041c26000070440507074500b0301d524450504000003402d02000d145c4c40c100300141d03980554003170000580380604c950b03110107620b50344044004003101007480381600b40b4030070040d0b10249012130089130341041c03850701a035881c00300c160409044048a40d807900d185400c0c80e5002d2014000410107180105551440e0402203418070100c403042e0003081d00070381c080d00e0100b50080100d8240500079101800e0030780a03085081101600e18070f000300340b80140c501c03620300300e50311101414125204003001c2050902c00c0d501a669108a03124080140d0440032841c0301e9490700820030908002c0600000c0342c04400c01c1400c500f1508111034510341c981a40a0521481c00c0215158500e44030b50b00b00b0020950406502914500031440003d1040e034072584605564004c9804c103500d1000c52440500060a0001001d008620030b0301600f581c2410446010390315203854128400c9241e04950392030044401a22069180e9181041514076102100c2c0c8c0040007842c60034044a40c0318801c08061540e08003490018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 105673039 1250 105671789 105671851
    0x11011107140108070909020408030304031704120810030204061205010507020d05090411091903064208030f03041a0402060901030f0f1e06053a0803 65
    0x55155200c0d41003400514040074440307141c01d209003804105603503240001c803070402c1c894100e00502c40c0080380c001002d408c0003000c7c50085200341c031940c000c1e504004400c45109001c0705d010b002c0c034200c0390101015a0103000d0294102d8200780b0b8070203406842ea00440c0c1600c01c0342d84840704210401c010042070040a1040b01d800210fa84080c1400804908004200b402000340302486103036608401c40c802010305085841c42c032000f1b003205600c0d90000849036010f003958032083c0c1e6481c1c01e04c95042c64401c900000490600145240c4005a15030b01e84160824507840080d4991095030035400306008108001410001708001003407550707450149001042c001012251030b0b405800c000504c00160f076400140c582d00042803a0004c1d2415410700d05d80c0c0604030241400c11107515040886102c0304081e00410000d020101e81400b03007580e039006020038090b52508110080403d603190f1615003d500e882c1100c0008681541d00501c2480c0c0c448006560082c4e6450740c00000514411800c10040415a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 105674289 1250 105673039 105673067
    0x10120c0c02010903030809030d0c030902010f03020c03040605070503040302030303040813050f010906030f14182401050607080706020f070b090f0d0522090524031f0e0a1101 76
    0x480321018a80c0d0010f040c5281602004041c05046030002d80c40c28800c00a4910310440c0d003209200e001048a0040d0041c6000c0c1000c0c0d001404000903500024040d0007125110240c030402545003514121040300c89410030801280d05000410000000d80d608002840c0160300450740c8a40c2c80d0b400c0707142d41e442c03000f081c1d12280c040d9504ca110031449a07044502d010859409060200b1402003190103040101080101c00c41244408030501482500c60300c1c007040c00c00c0d591000c503040c1e00c000e80e00e1810131403903051418907040700c0040140000c6c2015005045810300c00c20401d41000c400d603850200b070ba0070924a0460340301020801c0f42c203000d900c40010781c200400390043c0040000316464280c607054050008001e0010000f00c0e4000181c0c000301c03640181801c003031603108542d00c40040d40040d00050390f0324140b9118180708031941c00d4240d0035070f8070380c00340040062040818040000045012200e4500105a81c804034041d130ba98040c01640d21640c03007040703440c10010819001400c02c4d02e815501c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 105675539 1250 105674289 105674297
    0x302121609060303090b09040b10020c1203040509060f0a1206050a06060c0203060610090308070b07021e10090c05061305040c03020c0307140708150a0f1107020d1110120c 75
    0x100b00080b80d00040c2179000d64203400700711580c80903410701240c003170a041c0c50843d030444400b55107102c0c0d42e40e011404003420042110100851544d01d031400750b4030300542c006d82d07034007418400c08100e403440c2000c40041c800c007010f003240c10441e581b940c40b1303851151200f106440041d02c9100308422078003244105000b82c5490f0030100c4a840c4a0707000704c0d503500c500514550040903c0c208a5425600a0100000542e404200c1564800c0070b4544100388003015502d80015203e4440050151038114245100c0541510000c010500c1e03c44400c002900030030106840b5400e6922011403152110b50003080769221001003941c54910301400e00c01299003440c000806c041c03040c0700c214061813001c400c6980468025050a10000b194203001d8181201c03980121490700c60103850000060500f01d01502c2801c0240c81000f41c4055101315a007540c03031a2240b0355001c3c1007001140014030f016014400c0b1980a0b0040754007441c992804a0203045210341d1820210b18101414001c40100f4082d01528494a141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 105676789 1250 105675539 105675551
    0x90109021507260c0102070510060e01060503070c061d0307020906040606091a16031106060603010509040b0901060f0b131202060a0f1b060905060f0f0c0a090302121609 74
    0xf5140700f8a02d40040142d440611034504110001c1e04006941c0c94100c2000210b59880a078a02280c3e134200c40341b8000041401c020f030008824101e240014102d4107640c0303503103181d603540711411035030b540548004584103aa26820b589654800c002c105920000010040d60b4030605401040a1000002d11003031203182031110a100b6682d0101000d03080341c00c5481c41c00004050a03544e0300c49805069219210312442040440501d60b000c60038054100300fa81c195175040c1c58200502400703100900945030040d0300e0602107000244090500f40c0d000c1d115000000d001d54980d034281605d00f82e5507218000c0b02c400881c40311015401d20440c5070003840c4402203145213882179404140140900b04600091250708445541a103008030200c9100c4040c48858041c40001403600074004c1143d03103410358280c4146000500101c1401c050280140d40351003099080390ba8800e80c180c0a03034095500c0b40100010540300000603203415106943e910120405010f00c00b60407072540030031f60b400741d00070901242080c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 105678039 1250 105676789 105676793
    0xe010501111f0b03150a02120108010209031906140f090c040510050103051e090d200709050c070f050c0f0105180906010306051e0405070507030e0907030e06090109021507 75
    0x2941011008a2100c0c003c41c0c12070704440000d003060060341840420300390050070400d9011041d4020686400002c4044041e42d0721001c6c074608074020b40c80f8554240d80011641d11034040303149a20641c0d40d10170607012900701c17581100b0010420090300c4034548a942507083c08840746040c4a40d40c0c0710b000075501040203203002c5021194003000d6214240c181590340d000b0802135814070f017041030b20a030004100065814001701282e40e600d016182c18000401d40c0005c054030800c1402e50410011490740144216800c0042900041801802c240600c4000b00500c5000a45241c7d503603220030b0182014007540c42094041c414140f00ea82c104070304200c001c200350f406041c4043c9580d03003802002e81d0700021503500c0b0001a00203248981100d03078401180f0304008080800a503520001e41c8040c1c07424041070700e562500343c5a82c0105131000340882d09500b0780c40700c03d0500188050b40800540b50104403803100c2403600b81046015200d0400d07036516002e04e01c1c00e5040140d1003180300c44607040c2c00d078a004859 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 105679289 1250 105678039 105678073
    0x803040b180a09022a0f060f180a05031908010b030412120e07080f0f0d050a020a02060705030a030c1407060209041508071a0f09040e07030501021309050c03010e070503040501020d05010e01050111 86
    0x14a50184a80b50300c3c00b003108040440c011400b43c0500d40302b1610b44075001d04002c2e549030407219020b0130440e56000c1c03291181c0d11a400d02d030304985182c06000d08540fa5903450b100c400b18a00001420401d48140d0641c409146000301615803401d8006072403030714201b5160606200c072502e10000b1aa00050034540075502c0040e03080f10301200e91a165072a001100c10403418446021000303940f1000201d5800d06104000c0000c105040a580302001551004101130381c14800740303002a065110103001c41400310f84c0700e40041c13443d080300500010307034908242d0740028801d010b42c20102c0340e030340810340600c5458000e40a2118000c015031085080c00c40f4581191003a11031850540e001e951070301c12424014204000400180da0712000964880b0014402c100c24590107101e20a003503070524021850030391488045905071070103520309803403550f100c603016034060380301070401c5620b03660030000118404207030b01c41c9501170300d00c40e40308850329454a400107040142d407081641c09504000c2400c0190514 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 105680539 1250 105679289 105679291
    0x3100326090d0512040f2102030d1b14030a0206090a0209041211010c08100f030b0406020708120405010902040b030f0705010e04060b0f0d060803040b180a09022a0f06 73
    0xb1180c00548400a01c1c0550801c0442021952a0400410003003100090007404400362110144059050381c608003102e018006200400381d05030700039490244c1181d1040c5400703105280c82806030085e03030700180d40c3e86074002c155401103505a000454040c000a034148400f54214845100520441e0a1600090403107031010340024501241c104a15a42501981d8040031441101c80204007825040304050002c1d103003111041c402c3d54840c0c0340170a042d604002c1303140907690880002206991281da5180080d0b000b003200391148035082c0016000c02d510f84030403500c07a6101d0300020500039000d1041c4400d8130051544c543c420b401c028960800601e00282040807038409180c005102d4000c580418020a1141c100044a00c800a8001784900c0920001e2224004540c010052290741d188001d40300d020700d002381c5030094070410000c0c030800d4099207042d401410007001010141e9031800004100d90000c0501062503880c012556446006402c140851644042c054040d0b05083c0940c0c43e101c000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 105681789 1250 105680539 105680557
    0x7050a12031d2101050f06010c0305030a0c0509061603032007030c0809191a0f04060f050405090103061a09060a0e04050c09180714090403050904090803100326 70
    0xb140c4400d109955990742070b1070b080d0802800032201040100c0001c1d0103000100c80200d032051070540404c0c046c0d44551482e10702c0c00d40594070603095407a1440d519018002070f02c40e803020010300303009490b075542d142d00082001000030380e040300610249180240588100950f030820b10030565001e0400240500102c600c0d6560514106824039142d207011000341c003e030702406400c0342c2c01d40310300e03080c220000b42243d042d1494020b4000500f410b40b08441120b200d40c0941210385030050108211080c0a024140341c2081d243c00c2550a1a86404c0841c2d0411002d80c401d8034034039129440803200c80f0051800c0da50b46a4162401c5004d0304d03280740420b13181a5644685078840258600046c103000c2c0c00d000514520707800030001c10079800c2c50400300348035420205c0c65103210700641c0d000003014482140d04a10701c4c480500700d682160380b50380303003500c02d50402003d0681054403085c41c0700c0040d272484015481461300c5200d82200c14118181040074040000341208042c0503144094040c4070300c1c80c01e80b08108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 105683039 1250 105681789 105681827
    0x911070804050108090721051515011b062a14180109080703080301080609010606021207021f03020a030605061305060313120309140d080a0c0504050307030507050a1203 74
    0x20300c5d2040b02e149051490742c45120108210f450340c4542030414040909454003034411580e2404111041e803020307050070303151116026404180d01e2210350045101e04200d440707100e050302080c030007034459005a902410585407188115103652031400002c02e140d9138641141d20b025071242b0300701d0307070080c0341807281034558400500c0d0502550a180c0c440c003d004003600c070007000c1d80c08641e580d2400b00c0d0140c10030300454025000702c9000680540c014410401120784650080c1803180080e64441c401c0c0d031151005036080700130304803040780211400105000d2207095640050755080003100c010100c4506400c00c91043c1c5041004054042c4000740100594070300300c44030399407a101d8150a0714184801e82008000c411442030000031941c142c0e10002000b40107031824650003c41600c21925003445041e50008100f903140480c40034101e03580403401818075400c00d2407405131500e00187c40c0ca0b055901c21600703584008010300541c201218610010302c0c0400148240c041c855034090709000712413800709420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 105684289 1250 105683039 105683041
    0x605030921070f0c06030507051e1e030708040b060d0b0a020d0b1008040b0a020a0804030c08041a0c07091b0e010203070f03110c010206070c03030e12030108070911070804050108 78
    0x8a4001101c00e1683e00c00b040b4000d1440e00e141a401e181418420900031a15190006600130301450440748041c0200e00083d0018204182e4200540c0142d00056000b0310072032074240410704084001c600503660303911100194a030903c1c0c4081110700c01422140588501c140900006807070343d98035908121006005070303d07052544c441500903e8568551980403440703105400300c86070085d1529010710b0158134002c000f9540c42400b402a44200790440b00028068000a00428070503400e004080f4803481545180955907905000c103001e036107440fa40c5032540090441d0289408010304802000046414030000c2000c06101314400c1415840c2c0060102da0030181c24540e20074002ca0751080d40c0314a48600c0c43c480c0303060040c1070124262007c0310a00c81d01450304219070001075000d104040554a001c02001c05940850182110300300c000100e1280d450510b0700a901030001d18060044c000060200703620700010700f01a1800080b502d2031070581001210023103052003003281c0a550081c01e064080d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 105685539 1250 105684289 105684343
    0x4090915020703080f0108010b090f071101020f04060e03071413060e07110c1918020c01020c0f1009020906060f090d2004050112060b120d021606050309 67
    0x5840e5240148821440c800654401050b13000306000780903900b0b1002030051a0f0b2249940b508032540b22102a502c1403031540060002000030095076800300c11898000341140050b0238040c26030300020047c81d442d400208060000640c491310304100352000710010043d0604d0010482e000d010482d544c9409500706400c0841c40ca030098100300002e103101c000d204102d280449008001c1e0408110610190113164103041c8907240c848030085146104504401500d4606031181c007410740c0c4814445400f603000d10404c4a0b885003031010348011003410005d00030307030302d481280c45d1305050200c2c05034407486144c11111800750302d910a440d54000401e451060340c07041d2000307101800340280a10268880d8016142c5d50800441c2d032104c007a0084c0c1002108a0f12440c1c0e81044103503682401030505609030702e8024408541160031120380b10b81c0103070180740c02580340e03140d007400d0003504080e181c0540c0c011080300103080d80044510004044078070304241181448bc9181e0703101ca100180120040300b4205030020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 105686789 1250 105685539 105685553
    0x3010903050a030c2c150d06151e0e03070305030310030308100e06090a1b17070504122a0b030906070e06070b07140a02100609020a091505040e040b0402030c0f0105040909 75
    0x42c10341246c0b9400c4d6100c0c500048048090002409100101d101c0c0386400040d1600030001925540c441c0e0a1160400803211f07030840c1d18001e8290a2a8107209024000012810500045000d400b0b0007054142e09810b40c2400b034070052018001551803c0307946010418800c3c107140158203d0340032140b094132500c842c101d120240071800c02019503224298803e00103103030800c0c44a80d11200440703140c1100d6449100550f00350050f8401d002d1101c46840c0810001811401c0ea03e40043c90300c203c040d1401d12180307840702c0500d100d070005503451400000380509a40704210300da41c041c000c5d1130311301c10403a2030a0109400740902c010040030950140041500a4003e600d41c0c83c400c903554988a4943c00d440c4070003565600269100c101c0e581c078002001c04c00216034002c032141071035143c40341060710b07141030100e00c1d1070115010700c042001018000411702045c1103120034000c50040612018600b801e0042500f02889000750301c4c8140303148601400d05903000000d031001c03550f90400c001808045030038644 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 105688039 1250 105686789 105686809
    0x60503010c020c130506010e1c022d0108130c0611010b06040b07150e1f0501080c01140a0509090106030c020f06060109090b0406080a2a030b0c0309030903010903050a030c2c 76
    0x55400a0413154050004043d603271442c021034002c88030b40307120718840840d01e81e1002802c00200c00c041008004281d240d4020840e0f55040030303600c1c103209940700594403440700c0301e0500d41060000a45140b40d815400d0024022048803032811141c6074900340ca4080d2013074051180010050038034514111607070080300150f010080e20314040c800e0340d082c2e00d4400440606040c14564420005140c0070001c5815840010000003aa0060f1200004010362294101031900400840010003070100885a040d444825840f4002c08117928049125007030704501904090011031001c40590040d410096242c0e44040c4420843c0c460140004004040c1004503024040d503030007604442c41a0030740c40c0c081100f0403a000c0007105c2c03c2c1e042c0c0056036590740e0405240300400c0c44081d100c54000030104400100300700042d80c2200030a800c80b4608161080401d080d5050400142d02080c80490f000e0034103901809541380d00652880d106540756044105500054004544c0f03140302c540c1c0c1080c00519403a255840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 105689289 1250 105688039 105688067
    0xc08030a02060f190e0304090e03040302061b0307061109090108011e020c010b030303011d0f01060e130b030607020d090f05031902010e190f05040b0603040b07140c01060503010c020c13050601 84
    0x602026600340170240e645d511501c2460505458811440d9110001109079415264000d02d4140703446c441081510410310300c5240710308680020040d0500103002031058100b40180f03104440e4a8108842c104065600164807030006641003c0202c1c00020305410081d550608200005880c1d80901716060300428030f00340815050301c000800842c88010f079102001ea4003902c0c5000300602d6454041044801d003003803103400d0120380400c96400151070180c0050203c201105000110181030710006403500b5410356022016130000d0000d01d4485074840d03920409031400076540e072600303850900801c0c0e41d281520f82d10441e400c0850345100c21680714070700e0000d403000e00510a603517441c1d54070150340f107104a0340706211444480b071100080908140c02421500c1a00410490641c2d40e540c696030b00e07a00c8000c03c2035007000710349003d102050031400090944001c034140001245401c2509141c02c64500210150940d800070802520351303550121403aa0184050f44c0104043e100c074001683c0c5c0328550221 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 105690539 1250 105689289 105689291
    0xc090c040f0608041104060e01090506030a0c0306020d1b021e01060902030106090602060105010807140a021e0c040501050f030703030f030b0301020d0e01051503030901050a180603090c08030a02060f19 88
    0x800150b00340d1000c1c4040c05103005e4090340f540d070142a41004100c42c25486807208220614004001f17407600f56200300e81c4003502134161041c01c0800d076908804004a500121041940854000040b610074801e010101c20615100c003121505040080c3d80c8103008030000e5405403410054032000c000c290400801807400d014255203a5868100160000080c0d00030746005109100c0000341780d6100d07441c0b0307038042c03042510798407a2442d200003851120f03441450484158070816500c2e5481c241d10400365422401c052020b001300c00c10020420041d07d40c103070302c4244120041040282a0f68007c1400012650300d8200003190355403c0c1030603006132130304e6071380795516520102d44682c0525550b0040d240f00b4500324002c108940d910f44c00c0b030f1440c08602c00e000ea0507500c103100044081d40940300500014040c0c0c244442c00c1740480800c10320444090304202c00007900e9003043c1040044125141025000d400040c60074008110700007540d800004049008040000e40030032040c0703011498640b154845420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 105691789 1250 105690539 105690569
    0x7060207020d030207050111070e150d0210030e0f1209040b031207030c0b061f030b0406050904060603051c0e0f21010608071d0c090a05030d0807030b0a080c090c04 72
    0xb40a07403104240c0c401c075408242c2c0340110440488e400308003201a64551514420140c440500d0b5180e071540d00a80180c110300c040d0b142038050f030f8840340c078014400e43c166000b042441c180b209660a128550b044014140d10010324800614029010780b24000020366001030060a01400a4680503d10500c80460000000c25206142c0d0148036102c40310701a40d480c0489807108020b010028a010584000c208060404010f010303209400000c1c446200034000300c1d5203602d5034002450340c04265030840c1c18a5561108000300a02071042c0300240003083c1c150348618031410006845030700b4071004944145c4020300300400965070b8009141c2401c1d401d505144007904d03043d0810307000384040e0041c06601d1091220000703031202020360007201070303084407901c008a07220202e483d0040d81040d005a0b501105646000c55151020007854121444a41d1440b405d4204000068225984900043d008034080c0300e0030301000710300007681045444103903800d1109a4030750300c2c0c01d000c5000f9500031000340b01d0040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 105693039 1250 105691789 105691793
    0x1c0615030203060109060c0b0f0a021e04032001230409020307110705090106020307030806150c03030109060902030f0414011d07030c091515050c10050a0e0703051207060207020d 78
    0x7902440c800c0000381c07a4011040d403a0042a10b99210504008000010201c00190103050318010580c00040d14440541003644c0326410090080350300c51a913800b924040380410a00c401d0350408441da45034103551841101c1a100001c20300c0640001e05160000d980c0300c600007102d800c5040b0f41c01098011411516810709039002000d440f02c40e251256103105111010440f0f00d450302c0050304071040c54004624120069400b0b40d030070343c0020030961b8800034101480060301c5840c0002c00c41c4840d6000655940c2d0304080e82c4c501140c4003500100741c01e620500822000510340040719401503000020501401d00340720b42d5034050891005c0300041d0b01c0c24418203102c00d4000042c800c0650784105c40c060400d0741caa003003900c2102c4001c8902e03940c0d031001000410044a41d40d02c2c1d59000c1e022881d003076182199070384002d840c0c40c40002e0807600c0c09580c0e03010040050360900c103039001d0355003007400350501d24a5038231015500c065040642c100030000268110030441302d6412076076540c0d8050680c0c10b06881138 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 105694289 1250 105693039 105693041
    0x120e0307030305040e070801081c11100219110a0803041115041802071101030b030312070207050f10020705010e040204080105040b04020907050703080112020409060f051801020408031c061503 84
    0x144188903c1185c5100410010ba00401d03a05050320070040052004240e1540d03420170106513001c880082c8030320040b5098402c070701801206464008040056506e43d140c5400d0382004103840c038400f0404c0889484083e0400010800b00348031078000b0fa185440e9140c608043c43e21006028003681d000700b240b80e003103030120300200c09881217417030840306d50b0446070703c5001d01003d03442030200003890300548001c4080c285d0301070780c40341000390009022281405481400c22006000a603507840c09a4000d90b0b042010b45044140d402e6622826070741c806510208080213903543c0003030300445042c484180b5007500c15071a1503040c0c800418030b0400a020f181820304102c100c1ca0300580f4146e020301c002c0c10000b4296130064044400f19035056407580d40d0b0768a4441d02d800c4284609408a13440ba40300c900c0071010074000d0240d0020061400b5001a25081c003000500c0d003070f4032042e426442a40184001c00c440d00021050703410342007001c04520f10b5948031640c0c0e07000805050300508402e01d1201440c0e11503a80c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 105695539 1250 105694289 105694297
    0x30b2a130e010602010612060e011d010f05070905011707020f0d170c070c12050102070c03210306060e060d0b040e1011030f01090f0e0f0d02060c04060903120e0307030305 75
    0x1c5841c07000c656601c80008078240c0340d00740981006020301d070040318001600c40e4010035014859000018030180d4854180300038462221180781240e4503510f034104411024800c20741c206480e0b041008400d49000000380400c8162184070804409003c00030302c07414028089410300f201c003e01600d2110080b554090034a007a000c804ca0030011151000600103050308045034042c5402c41c50000d107407480d20b01c1d0051a0010b0b040300720307460b540a01c8200001003083c10f03000b014501c1802c40d040e003125200126004000d2a0805000b0982000c10420999800288440c48140c0664801e6a1400070072031081c06491126005a00107103401951400240b020501d211068500d64003800f80100d010708a87d8a4003055594086040101004000510940d8413082e480c41c00140301180340d914283c41da900303002a0301841d1807260000071843c8031895041c4041c0781e20103064104e8a042c90304092000342100014000101007038442172104d105207020b003603202c4010b0300007005c075100513807249070050640e00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 105696789 1250 105695539 105695549
    0xe01080d080c030601090e13060501170105060108060901051c02060c0d140711130b0d080307020c0a031a040201090b040b0405040c17040201051c06080a0b01050307030b2a13 76
    0x41d00d40301103001d4a582c94112030050030140d580004441c10051000030404014001d800050308900107280002c1340c03802214000c01c580002c210a14104065050940f0001400141000100c5040202c0c42e940d00322100d040d90313020394800c4450030700103d65854082030084081e500ca240800e8820040034001400d103003040c100d0b600e451061040f481540c8083c0242c8070010709400f01c02d8016142d80c103183c034040061300107000d000704a142d0140d01003146420300e00c105031143c400020412011a03010012904800001d40715821843d2444c0c03604c1c2511040440034140d07d41e81d003070119041d60f105032011805041b0011100e0f684035039900d80941654414440c5030b0060742000f0040d08a640243c200e0204410b00d5000c243d0700356607940c011219540217444d0610804a1030301003c0321101c45105820280040c00001c0c02c54000d03c3c100348450520585c0010b1080d48481c00501c0007886090441d038002a0070305881000e240003280610310000c4049185c80702402c0800d401144d9401d64100c2001c0b030b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 105698039 1250 105696789 105696797
    0xa02030a060b0a141317010506030105060a14060f13091a010c0b150a0b070501060e150a09020906041205060414070501020d0c1109070c1101030618150e01080d 70
    0x1554855a1104601410740410b0201e10000c4c01050362851500082043d604491040d0782c0054481008040003142c1c440000744d5a9941c404110403402c0c24804d90703400540403942651014503004052031940f0110703d03d80c0c080c42e004500c90f1140981c8805480340c1c64528165001300c6929003120303200400d42004021092921141000c0711940682444060b05800500841c8103680340c10f541d0000305402c0403903a42040d240e40700003c0042d224030240001c1032241c0300204a1614094403856009400b41c01500300c400b881c410b1019a40c3c400b00c03648102d5000a40140e1070303041090004800d40200d03802012091080310014042101c0442c403240301c0c40c410f4540254644460040c580c2c0c3e01c4540c0285409640007039070002d1250b000300b440301100d903c181c401882c0a022074010542c07504095900c4004500407804000400a040c0b000e50060701003841c0822441e0714080106c1d1540e040b580401034990781d0780703501d8040710f8075a0107a0f0300903081c090071403542565200c07041640c44c624000000006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 105699289 1250 105698039 105698051
    0x8130f180f0213030b130203030a230f0702091b0d0905011505100c060603080d0504051903080f09030d0504030e21070312120606180b070b0c030601020c06030a02030a 73
    0x81d8081c0c070079100c400801d4040020820709503034032000380c800054803201b4884494083c01c00103903001c00c01000381c1c1f00b40b0796880307a030382c0380c01d141c00d11050070420b101d03000c58003080c4500c254400b245402ea40c04581c04035000181601d41c4944081c0082d00c0c4040361003c01400606050210000d42014000900c5040200321a80d840b26540482500c1030085960107600c1080980e2424401c1c0d03c001d02040c05000000760369030341c951b240b1600d940300c0008480d02c42e4483c6e00304800c0c88018402d15001d0884481301203059003a0ba50020400320008041c5220341103480c1c00701c1c207084010002c2d61011622000300700160706080c10050650080d04200742c0c465001d01d5503c44600482e0300050706500c40b807a0052001c00c0c01c540d24070503210009503d21702000b40f480c006015092640c042c0301d00800b0f194075114030a682e2a9002180c0d01400d0b0800f2026500c20002d85000030300d0141a15844084008000d403251a24070040742040d950304030803a840709000c41400090046c1da4001c0d400f07284184020000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 105700539 1250 105699289 105699311
    0x50304030c0f050d0203100b1903050610080706021203040f05060a140907030b0109050a091a040302100b060910020c0d0320060f0c0702030a0f0b040b01050108011208130f18 76
    0x1d103130000c0002900f50300038522401c1c4410050700038075210200181031040340081c0c10303081c2600300d50690050321a54003003001c0c0b04900303868584100103040c1d43d40c0540712007818030300c0289d0303600c810b100b0180e04908000001414006d9520001c00b45541c02402d039945400c000e41050301410070341401c429050f174000c010846800300054a001101d40c05400a074290380380c0307900c0500a2500400a4424540314542c00c0000b03090240c1b2014241a00d1512480f1801d0500700245404a60341c000b44605142c850310300166503524003524003601c011610a1000d00c0c802000324100781d400c103140e0340c201c0c0c840d00d8240c0405030400a02c500420404c68001d030f4031280d4543d081d81d500c20039a18040e0f40d44950010400042850f0001c041103070000d012610450304503518003c9010401078184c5000100505200400042c0000507004100918050710359504010b145048082282c600414041c000554a442170140d81085001071654940d228515590303046080c0200002024005419107800d000e0b0070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 105701789 1250 105700539 105700549
    0x902030f0105061606110d15031e020f0603070c0804090b12030708040501110c0307030b1602120f070c1205030702090907230103021207030209010f3603050304030c0f05 74
    0x9409070110013400c00e0828180c4441005000c41c030001c84150400b000701400c080114002c0d5070005c650f54030a0f001c2079155041480091030500c80d440011502000c42c0f4006d6a00d50000311b80140e8101c446a50f48d4031540002c0d20030718003a600c020210400890002381c107000030b40c0a40f1602c641070f9480000d0699140c80c1c180c4901c101940107109010074002488954840c8006485510101044076034803130990001030b103400f0049c3c1c0100d4a001c030701c0003003081034004440c02c10000d020718001818040001900018113015444800d50b020901064400900c1800410040242400e40c40c01101c50070504080c2d0b00ca90003460164001e92905000c0b072803400c400943d8500b141c060705400301210901c90114060b184898015604140e024014142040702140300203000c1c15071520010f039504d2511001401041102c8000d9080c08101d801c45076000c440c03040b10089640d1821034044001e0000184108004d1803a00040e002d44000701d4007200704642180c85005894903400c0303090501d03556208000b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 105703039 1250 105701789 105701797
    0x70c0e0709060207180c090e0907030611130e0907050d0503090a0f150e120d090305070b0a0c0f0606080a0302060108010f0b0f100e040212150103050412110c0405010902030f010506 79
    0x217000c030030350410310794905141d409015489103900c1c01c80030721503503400001503c0364242d41342889600849800c10400050344115041d9504950640741842c50003c1c01d903d00074010701c19400360540142c00030703101000602c40b08000e004d00030081c1041c00018201940e494020700c442038000c0388102c401080800c00160a841100c80340c0180050080851f0021500101c1100040e80c1100d041d13940300c000214140240c1c1162203943d521020708920398204585400c40581c00103001c2a4204220403100754468520400380f030300b114013100013034208d1424000406981d800700290b4001c041080082541c0415414101c40103e8024440c40030090344c08030817141e886441c1544448420410313082414600510600c11090b130901140c0000000007240517a0b100190226180700c0b044e00304240c1c0e45110812103100442860100b0241c9840c0d070b601c1c5910a0380d01015018400f80101c2107440e0441046042c95404000d4018002540c0d81ca201d01c010b508107075803007140c2d004d01c1c100108031707420300c03200b42c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 105704289 1250 105703039 105703049
    0x201204140306010f06050c0109080c0c0a0603020405030d05031003020405010806100e0c300c0a020f010203040c0e0c0c03120117121b010207060204060801030b0a0b0d02010e0303070c0e0709060207 86
    0x903040181741c00b070705035040c0d405080c000c1d00c1c4d9502e0b0701850307000c1014200a0240040c0c0e20000d8501044594104407000350706030000e00505105000510103501c0000d6640c100d1501030500c541c0d00d407600100f080100c01d41e907100960080c1010008900400d02040c681d00900c042e00406040a41380c803082c1c254101c0803039545051881c1404040b81080703865036501c1c402c40e41552002864181c0501c040170b0450120b6421801010000d400c22040d50f040000000c0d0303081400085085080607079514807400a540328070341c0c101da00c0c40080f810488a000440304030082c074200f100e555030040d000c20754622a09104414034019a2002c0f4070040c2004105503041d41c514480d4507140540301003207030449407a241c2e42240691340c02d100100028075288020b201030b04482d2500d500a6146190464110070b0040180e00344500f4441d143d505600e03601e5641c04000d60900300500c40621440109181d401260400740003003800010001d508214001d495009045541d00d0948945d201d040503070741c0781000d22031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 105705539 1250 105704289 105704309
    0x1060c230d0e1807050405190509011403120d2007110603070c0519060c0c08040603090312150302010f030b01021e0307020603010906050a06030e03070320120414030601 74
    0x20745801c1c28400e02829407440c0000303084211900003040c9010401a04607000c00100714001014021882d0030f030983c00710004e110811180d82410300c0d000c0f900200041c428410303460f00602c03965404c0d9406100c80c0d06400320941c2c1c0303e0385540c00740902c4405080c0e83d502d2441100d03e40d41c042140d5840004c02c8550040d009a0320301d4105040c0380c18800305030f100810580c01c00225884c00c10004034140101c89000085280340c0901002a080480484103224682d0b0305000149000000241544003902d080390120b050025003641141270030358040c0320044004450394640840081d440600d80e500f841524001e0782c440054442d502000c0d8200c039418032110380076078080030340c04800f0044841c071205208640740649041000030f1340403442507002a0403045010303886071401e0001781813401811006150038a03060002000d420003007510cd110301c0c40090204803a44540e2208034015105450025144c54126841d11b0102409891290058011003c90445840c9409498600015440d050700c2400e45 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 105706789 1250 105705539 105705553
    0x1202010c05070504090516050d020102060109020c01110c0a0b0108030901050409090204180302060f060603131511041202030105011e060503280605010806030f10020f1201060c23 78
    0x640e0036601465044800d480b546201040c25120b0b806020160740c499401000380b20406014040c1c06169900501c0c02858809007200241c6e900080b000e0444002540040c1d6650440300443c1c05000d040c0811501442d0015824828450001d80410b83d80d014006d04d12050741c941603810b403070b48540c001e0940010401c1c0418080608242d01101c1d40c1e0b0700c007c0000405046881006480c0d6880b01030a80140e0042420041c0d820406400d596008004442c4c00d45140b0307000c84402c103000060880505141c00d250704801c0c185070380340d000a10404000c1ca00b90385642d41c07801030b407014100c5001c089000e54281800003034410842c050341c072070000d60900c0145a240c2030620481d100d41000700755601820005a10740381c00f003c049002c03642c9a48a010102c0c4c02030518001500656024016500a42c030802d52403171007403001301c0c141c1c1c600c4c0e000410145e075440044002007550302030311942000144044000113840d40d00000041101c500c40c4c45000d01001c860343c030788445a803101c841c00328143c2040d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 105708039 1250 105706789 105706793
    0x110607030e030f091207060503180d02060f060118081c0c08070b1012050616020303040302070e090a02040e01051602030a0c15090f0b01320d141603020112020412 71
    0x10b0203411440006891001c0d10103217409071030303c1c0140ca030380064082000041440004a510441010120602c0e07006010700c54110340c0096071094024002e803807441c46640441c803241e11815100030b007280422400e02006440300141a151400750030006040340ca1901d2642840d4001c4400301442a0420700640c01c0035455211041800001440c00c02d148234000d4005c070300d045241c2036000e045805030009001d680380010304034110306124402c03d81598014800c120020381e0000c4e8090581c0d501480601c1103841c2d40d000640360140300c80c0001e5202d03045c28171f28518440150f001c988103c0e2000800491510220b4080c3d032280300b0b0840d0000001c0039191248003141c030300743d441c40940c61000c40015294299894040201c4a281021290040c2c407a004221202c2448031803018031a001c00300c2c00c0102114000d03884a0100101c000d4000e485016440040c0003220510940b404030b884160b403c3c04500d20b910030944200c0c2c0c001203020901e50b6800b851940c450b842941d041e901c800740d01092190142e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 105709289 1250 105708039 105708067
    0x702010e2a040c140301150801050406050f0f010516081210061202220308090102060a02130603090609050d02210310140d021504050108090d020a022e110607030e03 72
    0xa002c5044c0f0012038280c030309485401c0001e60080c821400b01c5d000d560541d400c002c100c80e0701030303101511075401c02006000c00c2c2e80d408504120410300300c401210541018005988501a20040821030007420070060140081040240171001040c2d8403080b00c1c0e81c6912422078081c02a026120000e02c20746031403108035200754020408000300e03100c03031441c90707100c80951002240b9039001101e0007140416851003550301081025000a01c1180c25030030141181c00d40c07030011416114440c01c050700c1d400c90a0900040754004a80141c029040d00c400171040c01000c0c0d550101400c034031207502e40e20942c0e0360603e01000c0c2600e0007200754119800b0401c0c0303030580c0c206200801c1c40c1140d0f4400342c4006050010b9548480d01c1003115000c03650b00e42c0700c47c03402c1e0026100d060010131260036500001807100689a01003144195154100c9a051209002c41020300b90321034030380c00c404100300001000c1c000064015145010303007400841182d68690312003104909503440c04d1008091780d442070003500324803000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 105710539 1250 105709289 105709301
    0xc070b0c120c07031b0611070321030207151b0302090306060f060903100f0c030e0d140c061005041a030705060a0216090c0f020303190504020604030206030702010e2a04 74
    0x400030485035400d8072a200d500c00e403c0791005c00d20b00c600c44c3c030b1400c00103580c20401c400c0c0c4124050015000a0b40796440300708607803000810085240e4a00007a0940f664000e42c15118030a801080140070011000c00d40b078000c0c52034103902101811218400c141c154804d001300d4210300c0c40600940030f603403901c1c000c5c05103501800018030f07803200e0b050049803001c0d1005c211040f031001000c040030961415469288013162200c006900070176082005505501400054034890361003d4a002c2c07405000701c010130601401029104070700345c01040188851031101c1500101a210229405c0003021048003109014040541c0c00340e8064001400c20070113403502902400c2c0e800c60038019111081c000405000080100341c1040c2041683d44d800040c100d6480700c1310030130350002c0740011482e6007454015070100b1356100321060070b40c0340ca4074001421500c40340282c0d402903034040d00d031548a0400d0710380603000e0000c01c1100381e05072140000071607481d01131b580d000c207040a5585003041d004036a41e00b0b11003d041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 105711789 1250 105710539 105710557
    0x15010810051b0d0f0b0d0b0601080601090605030c13030f0309030b060904021e010e030109030207080c04020408030f09031e011d06070507110d050a030c1a06010518010c02040507050c070b0c12 84
    0x2940d00c17090141910386c0b000c0301c803006110340880c10b003d291480002d82585006401181000580003003440360b03a402c4012250840b080d4603400b506c4600c010417950301003041390002452504c4044011007015002003148080d03e00c121050324907942c0d40021b00070a110100e03070280d400b112000d86841c59207160300301c6000c6810180751000c03100320400086401d541600070107c0c01030340600020080d965080c004414090b600700c0e410340c90070b407a104940e6a64020078076070900340100010000c803e56010000d0102071440012015807400055041c9070090014180c0f0042401440090b155461008121107104a0151700c03401d080c20100d8032918070440c07815402c00e030403c00c21896240031910401040c05924030070b40d039030b80040005140000c0180106013a120580b84800d0902c1070503a006000e4030041d0302a8000c1c20303036044040c801292040e1710002d0107504586003005015003143c0c060014007941c1c042c01c044a0a2903a0f40c1d03403400790b5204901c2c1e05035194101080e09243c010300303c0002d201c004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 105713039 1250 105711789 105711791
    0xa0e040201030b1c0b010905040c051905030d080106020d02010e190611030a09140d0f0c0503070b09160f030b0406090f150c0e04051302040c0215010810051b0d0f 71
    0x110540100f04d24100382d0303400c035600b1640260b01008000704645441d000d000c00350b105000342c2c1041e54800004680c1d5008a6100c0c04001807103006803010303c20400010301004088840c3c03595180030203450302d0310078000c440060182401200249005000f40390581c000c1c4801080d142c0c10100c400951248060803c49903640c40c1e40c142000e88a140e000303940503280c054000035030454180f0b0030b8808051213510010a035001108140340098110004402c1100360b400d15803c011446d1400034198403c0f810001c00070b00140c0240440d02d500000c0c0740703403210359440c00480f40d940c841c01100103403c120710000300a0981d50300080c0014649810000800e80b00d04000000f0016070703a21040d445440e41010b450095840f204c00301d009500c217442081c50002618100102d00b050309403881000100c15020340030720b49070a0031701c0e4039900c00c200381041c082603054020107a58680140d90f13190750b180c1920074066402c20b40401c030206e40781200b1144180302120043e2400401d400c84a001d016164440b001003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 105714289 1250 105713039 105713051
    0x30a060b0402041e09061d01061b02030307030c11040905120f090a090212010509060d0201030c020309150d0501090c09030303091707060509070605030112060b04090f081c0b0a0e04020103 82
    0xe0900594210341e02c110035240324144a0a202d0044c0071605154040309a08039511f640040301100d0020301415580d00303151503000f0039919400c0c03e502001080c0000c3d090300c00040c1c1e80c014903510400c030b80303940b901c1900001c2da550790540c00c01059840c1240f0140c8160400342c80880c0303c0c0d00c150f0082c4024990f9110644c00e00c0008000074580c000ca03a0301181a240d00001c894082d603a04140c1c1c0c2d400741070b0807655a446410180f011460070801004001d050545da030400c610014020026905800c2e4014000c000c0e10302c00c50a80344132604010ba03000c9509040c41c00100f06500a0300483c541490b1543c2c4442000c0c0c59600d041f406001c040e40c2c1030303819440e400c201c19640c140c42e0b4010105a402590013080c0d50404110007442c059299000c2000c0000a0006200c13558051b1070a4110b160010710128080100381c0000d4001c00c580b80000740101841c440c034804001100d8040c14540c07800d1920083d203201e0300ae403048140d5010703105203a803000c2002018004e00421054140c0c2050040c51b002900c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 105715539 1250 105714289 105714299
    0xc030405090613061d0903040b0a0e0f10020f0f0a02091b0408070b18030610090218060409092003070608070e1504050a1e031e050105040b04031409030a060b040204 72
    0xca584caa040a0701810341220b000c141c40308002e500c9500184080015441c081c0381014078502c5008001925003001184984c0101a9690602c0149201c2004100040c08034002e44040c0d40e03105a2a002e4a040c003440c0003443c20b080000c40c4514005401500d842c046654540c0c80300603842a00c08544081c000510000ca29800308001c410044c0160008980c0c1d5180030100c13480180c07095010340ea00c40d6218004100841c5410003106088603c000030250700c1d1810308142210f810b01d4001c8140d00700c01e0104002a070000725803c02c2c8103603405007448210700c0292140c130110050300c1c3c0c0c41e42909984100e4080100501c2440407560050051404d004010185000120b07160348003079065640c410082028400c0c0c0c0380070142040107003541090052824002c4444440c4110a8400a000c0711102014140801d0b4a50000c81d035813540302000300034030b1610307117050602c15409032015400248039070090342c808422801116a82a001801050b48501590342d2402070b14804004540080d028040011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 105716789 1250 105715539 105715541
    0x3080a0c080703090f08160905090111031005010806060c0a0213090204141609060207030212070e010b03040b010b030f0f0414070603020c0c03011e0f090804030503030a0f020c030405090613 83
    0x70b000c40c8a5501c0000700c44c0303003036041402c0007541c1d00725854541250b0610720080c1c040201d0781044401c0c4600100329070740d800851500610200f0107918900301c0000401c092981c4c1b4200c4c08083e035400740c80300d003d561101c9051003900d00a002110290f580031400700380261501d4002c0d480d031000c0b000004200c1d88041ea01003400ea070301e5061411400b285080601ca07170201220040000140c0c1031030603441c0e0340d261142c001e5440b001032201902600f2742c8005002030300d00521601c40640000c0700008410359407812941e0546e803040b9002e031a00006030002058064440d0100ea0003003800822410103030b2240d19034610108805001101c3c245805e21086c00c8501c03060014800400311601c0058451180ea144281013020014116109900d460040b00e00640c411280011402c0d03402d5000407000407544143c4010410301001400f90348020400004002e4004011407060a00c05020310442c070b21200d44c0c00603806803440091164200740310510050504000d46a03000e03000070000419255186c504d10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 105718039 1250 105716789 105716797
    0x60f0c020d150f0f0c140f0408010501080304090f050403052709190608010b060a080a0e060a06180603020105040b0a090315020307090b0a170702010924110403080403080a0c08 77
    0x942c66601c8940c282d140a58602c40e0324401d503601a4140000741c1e50303510041c0000e007030030300c001c00310300000c9003180302e6241031000e0f039001d024803d0080000f075854048140d42d941061151025060609030241e00000300c0c0e02405005507415140d181c00d05c811000c544007128442d80f4891118503d20350808404e5903454050b038002c10f0030f001154000390483c0180000e540854000340c45036810481461070b50b464440850705400c101740b0b40500113031a0000d545003c0d042d009400074462181e4000e020020503998091400c9405080c006400c3ca52201065401e0710762510020b80424030a101c108a03a6800c0c400034034600c0c075039241c414601c54403907807103c1c559400c41c0508042c095010042084840d00191194054010103d455060071455030004004141c180c0b17580780040f20a00c08507000d54005d400601e00e040e0b1150442030728404034024082e00d8801004005011410020401e0b050300b2640d0440d010f694010900324075107415910740440d10390054501400f08811b400d550004500c03c08050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 105719289 1250 105718039 105718073
    0x1030902040f051f0e01051504080a03050a081e060103020d0b040f02030406060f0b0304060c0908061303020c0a050109120203030f0301081b100c0f2303030a05070207060f0c020d 78
    0x2425051480c200c0520311400404040c04d10040041403106521311100141151003c440320f8001390500078003141280110744c0f0541c6684510000300e01015007000c05442c03101e8040c0d0790140656124a0b18044000301c02e52207074051030345640400c000754442c1d0014000040000008600c0200300d0380454221020504000c4042e40c2c04411f2008210b031602581c80141310701c0c1d0380300c01400d0400841000700d12000d84001c0070103540b020389140b214050300440c002044070348203030355440ca050b20411228080244003100140140c82800703209107400c3d00c240060700c0040e92401c00c964140401600c000d01d4006040e6810300c01801664400160300d0000c40c00f8142c0c00d005000710040c0c200440001a00e00200c90340300304c640c40b4485008070790043c01e1880054000014514109480c1025901040c0a01203048990b001d2120b260b102c45002000318040c81c80460104119550101c08076240d8005010750070014504d41040018a4464044003014600040190700400782c2e958415418a110101c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 105720539 1250 105719289 105719291
    0x110a030b040b0303040503100906090204051603050709080d050d0b060301121205070213180803160801050a08120309120a0f0f110705150c070e1b070c0605030601030902040f 76
    0x110010604080c0141035502e076081c0c00650409062400207a01c40d09001c915000d002d66a000e0181402450f40000850304e8001c1d008011034107003405a40303080d020100103640444c4c100400b040f802442030b03601e00110303410071010f003040c3c42807420102d070194032990a01c0c50031038407810303022542d41c0d81000850003400000000e0603031806a141c0408582c0c0081c0301c2c441446020b100000c003584600780c030300814054060740050a8414180c400d003a0100000300645200ca02004221720b030111848401200f18983c2c442c01035681c1d9030020004410914016180c003030300b1096510150309a480701942d04400c1040a6410100a500240308150483c9a03100c0018a091005640180d0401d1110080f1826803400301c418641080419507030b10f246114071401f4003004004c44080040c11010303101211190710541d00b030560f94a42010407814180d50034519050700a40400b169490101103071040342d805620800d04a10300300e02920300da0401402e207810b0546805940e401a51684032381000d42084000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 105721789 1250 105720539 105720551
    0x3050d02060105090a0b01050301050f130603080915090f0409020d050d0503040606150905060310120c03060e0a1a0c0417151023040608030307030608100504020108061201110a03 78
    0x810002c07050103171850104500c1c0c613190a08999205007101e0642e00c041c5e80b00429016400041039402c0102201409114138110010003007044030b500501626400301d07483c0c24107502607500c6142510a40d501e540d0b00c00c02c14054800366042c0b54006000203030000b00280200f41e400d80b00e0713509144400720001c2c0064400020002001881d01c0750401411a091b100700140d080504003800300000c501407103101d00000710005085c2c0c540c0e00e421074040c0800e99003503003441c1050f151020485016010071a02c0a0600f08a1020000001481001c0c82d820002c4150210401800c10080c06009000003207010420007010400c4e40e00c1142d02d0b820200c080004140444001d202d00140a1001c0c10100c52803031a40740c1000502900344544003100c08000025003000700c0340c800a0000d050302e5010010901011080041c80ea80581c00031007180d02c0c0301300f500c0401184100c04c00496100b16802800b01e0700708000328070582082c44005141c03032405400000d0020030392342407034034076040700d032203100069250a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 105723039 1250 105721789 105721799
    0x130305060a060e010b070215090a030f021521090c0d030f1d010c03120207060603051b04021201260313060e0d0b070c03020307060903030207020f0907021b060403050d020601 76
    0x403103640000c014110f401042541068007400c19403040900103842a10f0f1302e0301c4510b00e13800e8082140c01c0398000420040035142e0b20321303100c0100041c00030143c6c0f06003a082466158802120100c0d0001140114000307540d074081d2a010150300c0b00901009564401c3c07928624162b10755011411056000340c680030500d4400c514000c0c0740140c20018590840c1000485c01c003140d80142002c3e01c1c071645800c04100d01c135030702404c1c24002d005116000c1e099a0038081e002041c8040416804822407410644d07511a2100c43c060105034402c80c00980c0f40f203008000104001c02101c600f1102509403032854198a032034000700340c0d145410089440703d040306905400c2019941090034081004001c1c0d80c001303c10080d0740c640401c01e0703600078034000c00d200982e103000007010b10074422200010b03800141003241c00d166040080081d0010a0100c1c00b034801041040c489142c1075498074401c2070181c0c000e141c103d28825640e030700d80c03801f0900140c10010a1001100041d000d111412121050b42e006128540c500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 105724289 1250 105723039 105723041
    0x15030f050703020403140a0203030d230a06171906020306030309040e030a3506010903150c0e04150b09040905120306030d05270111060f01031b08070306050a02130305060a 75
    0x211040140c0d2107c961140161404070544050600406000030400500390541c01030106140450220300210b40800c003140c103583e0300610079600401c5480c16120010740915940b00c8501e8440c1844602004102000500940085501090140a03242804a00750103d410b542c0034a1180540e90404222940c0507a0700030b0fa611004e100d006010811035000b04c141d01104c0b003404c07150030783c4102d0403c0080d0300350340246d03502001154045600706440707101c8200003008103502c84580300040c0101140340a00e1070706010b40c50211a0f80140f10354000e140000030790305980016500c0d1b40140d16002a0700124409101000c0ca29034507a41e50340c0d0707900c0c0c15002c050400309017030b01c020248001408803042c45103030138105c08041101c5905104c030f80030740740006035895a034000100400d032140a00708107103042c05400c100d048070b22420240b200a580300b903a2000c620b8060084000310f42c8420410008074055401981d0040d18140005192200da084c114510380081d4100340d03015444902401100011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 105725539 1250 105724289 105724313
    0x3090b150901051005121602011a03060f06030c04020409050610050403080f07030e0a090e0c041b0507060b0d050303040c05030c06070b27100e0d0915030f050703020403 74
    0xa241405488814000d00003402000d040c0180c6004040450841a05500403c00c0b40c0c0c414411019000c0385140040c010250203101640d040d00550a0002c1115100610a50200180801800f40c9820758500c0c1000f182c415006012640c5446403a20713041e020b23145e0344003c001070400c450000c1600c1c40d040040c0010360b62940c110f8002c00204000230804140700b00d09440c0c2494040003481d42c1d801b176a040495240107140082580113000ca9000100c0c480c0b290310070040b421842096030002400c19042104451078440e2040700401e0300c40420090501c620024070955110b000002402410800070841c400c80d41c14084402c0c1d4000401d00c4280b00c048040d1600429044000b800307042040400306506006180001341600101000300724000441c06c0301902d089001090004400ca200ca18075585080e441049190706141c07041400b41c0070f4000ca40040c5410854407881ca56501c0c14014130003600c41c0300314180406a42c1d080e070b00300c5800d05001d030900401c241c1d0340140e01c40e82903040c40d20080341 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 105726789 1250 105725539 105725551
    0xf03010605060a030c201c0c0813050102100b090a0908070507030506190c230d0c02010501171b0105130e07030b0f030309010f08060607050f0f07080724030b060a03090b 74
    0xb0702ca6840c02120000028102095800000c032481d4020a02c2e4056801c0203034100000c1c09c0c00d038041502696494502011021503c0c01d07800c54602d441703036051900031612140c80c1640c1108804000032403290380c58201e41e06540c42141d4152a0019070345a403428481d054204484a422001c24065220440a403000381403101010412501c8040440640b414264881c003226060020683c011940700c2001038403140c07801401c01317002c1000080c2d8002d0080c2400d02074403d0f10004504180c40740400003c10100304ca1408560001d01c43c1d1141c01900c503030308491851043d900500700d001c40c0d045240f000c614014066501c0214100c000e5500b040b05051004582740e009a205210884040e81d02030080184032009052000d452f13140c2c0000700d29030f480f40703420140c0b131031248038101a100300c0300190880c00070b06c0c19800d031800e003520f07129003c2d2180b49130b101d00f491307e032a40c000003691080341603540f44450a803070800064a004074070120f0500d4110414143c0801e5403460088280328500c800954024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 105728039 1250 105726789 105726827
    0x40b0a050c16121101231008060402040e1f050103030831031101061d100b0406050c15010e040b07030b06040303120209220c0206010506090f03010605060a030c 70
    0x20a09445482c00b00101c8001500d450b020014014003d03010704a600750614982000b0f1100f10401007241184014080c0c12000b02001c0d140025009281c442201c4143e48861025011986503502007101404903080501c5043c000c0c0358440e4450362036220a1480c004440001140c0c942c0b441c01e0243c50f8080050180c412032031484204c0d4140340c000ca5400342c40ca0030078442c101c1482c0103402d08031380d141e141c204425090340c680748001c661003042881010410042d000b01c888103698001040e40004120701c19504c4042050106002a5000308003078662514400200c5017002d080b5044214816001c0c1d202800b02401c50302403105120300c4051143d031210a40c203090010004000104545101300d100103410040150031800c040501134040700d001050003840c1e0b202403410760819200000180c2c850444061601c1071a94005001250300d03412980020882c3e4184402401884005980000c1d0140c1c19540c615011031280c0d5400007030603080c4103598000680c0324032003002130003507801041403120755 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 105729289 1250 105728039 105728047
    0x506160309120c140303092b020c010804081603030b01081e0105010507030c06060801020a0207060207060e09040204151410020a0804060309080f0f070c0b030f06150f03040b0a050c 79
    0x1080c0307151804022840c161510403907100322030130100080030030550304040900000050020400c000100da0059002d61804100300403440301d0b001c211403a50103111009070304880048101503000704543d9074082c0c001d61040340b8111130308035103c10215007100d08a000c01c0d512210000c00e03591258007507610030b82c1550350580c0c05006d4821701d00e4203039051183c60704110340051030108242c440c02d8107280040d40051709004494507109914082d4001c4000d00005100b0382a000035650710015040c4211216a15649104c9000e401806600100107100384c2c0c22940710400340d200481d03198620030040804031103000f00c0100324010008640704104900086500500d40354000c1800b041c2118201c41d580d080000380602c0c1d43c0340150a50107410440440d408003c41c400040c0d229410003401901d225000003004217480b44100c01c0307217000603105080041c0450000502d14207024400032401c8103002c80d8182000185402c00784103500442d000c4500381c940c80240105040341f4010360707810580040c3c0080c14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 105730539 1250 105729289 105729293
    0x20a05030d02030f0c161401020c03030f0402010806030a20010c0f110901050a05090a09030e030a03050703090b0a0c06110c0d0c060b04060b0a03150506040603020a020f030a0504030809060d05040506160309 90
    0x30646c0e52210241c0440c80000342d542c0b44441c25411500c0d031040c102e05803a144d11b00107901c80b21100c8115000d030b003c1035007031000070510315001c00d8440019a0040c065240904400301c9014602c0900c10818148103100036400c0c04554080000070685210f4102c00e04149205030521003070100c107038452801012201e0040c4016500c412041d5031002842c00c3c0000e040c05d050a00b118106640c185294050041c07055000078542d11800601c80f0500986600050541c2c0744003404603803180080d0400010104001d440000380e240c2c0044840c100354035230b0103003001044600ca070308100c40364484001040350442440d04014440c002ca5114400848080080910304102000d01d0320411494008040c1e4600900d8508204020144007405010b880300d41c859446e03120281c02907010b41c010700d0140c458a4400c44080d2400402c4640c03001442c0c0e209400c04c0d185690300b447e15005a545541d00041c18091700c02d12064511a4070b100741c4c0030707200030f110340c2c2810200c0082e1103d000301c0c502c01f0181000c4030000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 105731789 1250 105730539 105730567
    0x411031501031a0103200c06070e1e0607240f0e03070c06120f09031205060405010b09011110020c010222060504030809010c0b0f010510110a060b01020a05030d02030f0c 74
    0xc402c01c00307081c04141c0c070b011083e060000d480c6880000f40080300c04514240d01c42800a40b051251480f61510ac08c0381c4151b408100003040000508442086400d002c00200e00302000a00000d6208940c0d0841e440041400c1400588402580411b0b1981d204500c20300740ba00f41c0038a90a001545000d58a420501d40b0307074070641b51540c000c2c80d0078020400d180d44288285644000628072211030204011801031400a01c1440b4906001c0034050402003c1526441c051050314101c606000000f0325214000c0e00640d182c80c12510303407611318000c048111030424610f0000789505000f03c8001030fa20742d44581030340112410840340c81804603403000280300154000080b6400c0e0b90f0070290303083c2c86a030300d4030048405201c50b03400104210340c2032007031220821405480314141d40c3c0494010b092310402100448034030010b03010008050344849408030200c1d440d984000e10340c1a042c416210040c07840e880c2c2503d164400400c6001140d40001000750511390707a9a5140c00002a0070801d18005888181c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 105733039 1250 105731789 105731831
    0x9030c060503100315020307121e0c020a061515050406090605070809030a2105090303090d031106010e040c0b0301120b07031517070806040506070311040302041103150103 75
    0x41c400004041510000000d10741c500a66021018244941101000d40c0c065001542d2950101301e0004655922081c580a085c004030038058449080020070b0041d00c2c09010b40c0f1b2050410350045002040110710a400384824001e540604a030045103007403001c100e2000081c10007410444c00303100034804560301a59500890703144d407800c2620b81c180340c00c0041051040d031400360750610510340302e90208202c40c01d40b5042501240203000d0202c00304601a203040c422110304581c1a04200044e00d114076050b02c50900c500d0003440d144220036080840e491500340c3c05e030003014050b8a0794007008200300302c5564240190042600180c11035240582541d401c04000e4030092150400c0c400003400e23503209a02034441300341d007140c0040300c940d502c1c480d00300000d1022a040134280604a0046540c42c07001500d1406640d02000422150340d80b110120000c0c025080000300c0000e04200c0000560790f01e0041d82e203031100c03a4039030079039030f04090180c2c140704200000001d05141c10500c0d040d01001e85c1071456 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 105734289 1250 105733039 105733049
    0x2010c0809010216060e0a06020102030106020a060504050111031e060f010c030c03020f0318090c0403081b0709140603150405060c09010e1017070801030f060207050c130e070609030c 80
    0x21944440310100141d00f41940f00000c2c1589000d2604e000540d07076482000e91050107010346002544540b81c020490a07444240200801f41e405501000c001030816440154450301820002405800c0740701701d041141d20603262030b0240003404c800501d54070085000180c00c0102214541c0c0044040000641100b00007440601806150f601d254107250007405034002c808205400c0e00d5a490b40411b40d12013030b51408410a0145106000080d80c0d0241101200d00b80c03600140c01e04d0804400c1b41c032003404120821484800f80c00341800c00661a103090080307000c607404000310308800e845c20400b8107190200d0042c6101c204055042400003241e004101c0079041984c54010980d0350401c803005079002c556407100c0c190000150b04007400c2c0341d54480d11035280c00d810105100e40c143c844580c01c0319048400e01018000042c010080c9000510720b40c0281202480358081e10a05809400016910030811041602581e161201200380e4207051260744080c24150508460f07443c02d5032903032407a08041e4062 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 105735539 1250 105734289 105734303
    0x51e160c0305070b040804090606020f0a0206090a0801090605010504050a09120e010c08030a060f05031b1012051305010e12070f020a0b0c010b0301270b042f030c0d02010c 75
    0x1544041c140306504807482690007404410060a05281400d015401480340c2c10311a442c2140110b4a03500c00b0803604048071481e00148103001c03041e02009826072006141c0c503400f155030400007a11030b00a0003a400c0090141400040701c1d1315117024081030720b17801403402c02002c1c50910240d0001d408480c1d452070210301c030f107042d401004c0b89000599100c0c0c224400070300455004010010050101e8100d041031b1500c1d101b86503000c5079600309040e0707500d03d0782c10b9034030a11007180702094150070f14007d0b20301c00e071683e4500005ca80e09861100000c45509484100c5503446c604c421809001003402545c2280120500a254252421901c3c10290047c000001e003510300c8424420103650301c4260800290142c4441c0b90750740d9040115440c002c07e10400c005020b0b50920074401055640a100d640305406c020450400e02c01456580345110a0014821944811415000c00f40c2c42c812900c24142136005243c0750030b002c160034041615003000b05126031b03c0f80405074a40070050340d01054070080c1d281d100c18 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 105736789 1250 105735539 105735557
    0x180807030305060f040207050a11010311030f190e030a020d020d0926060c070b010e100b0d2009041119050304210c0308060a061d010e090a051e16 64
    0x8001040d98904540c3c085d4031a001050759002e04c180440c0d4081194820403092001c03030301400c0103405551280c50703c501503220600000c1c840e8036034907680c1540446030300480b6501400801900c0c0c03c6075220003d4004039070022030552840387d010803102c1890140f900042c03000000ca880000c1903004640110300003100c1042c125501c1501030120481d50750780b50402d9030440c0c40c2c0180604a180c21201c01a200f54180c0c50000ce54800f0104206004417600a04160841c1c20414500585e40c040524048800c0c3e076035059548004000d001c000c00000215035403035a40320000201b0041d40e0f00000780300d1003407404001c41540b1040095800e8801841d03424800d450340d40c3d5041c552206c03c0c1d020801c010851400f210f080e0810f80c0901c00447c4136100781c5850315240c50704030034000001b40c01d0081c84045255040c1c224000540f00c82201d103403071014940300740c0051012001c40c3c4080c605841c0d8441c01038460042c4601010f884000030b40742e40c42c00b01c1f404410310340071b40901d0008004d980c0000521042c81 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 105738039 1250 105736789 105736801
    0x2e050a02030403020303030703140c0306091611070303080106020c040204050609010c05070e0901020310080c010f030b061605010b1c0f08030c0702060c0606030d050c0705060903070f08010906180807030305 90
    0x2105550040d134004054a4403840c00e0030b00074002c0e040c1d4154403050140d5040004d007022000c901030320300074000900303001c2c1555102007a162400880d540f0950034001e5040011007919802c00c44040a0361095584401d95403414001a2030600780c0005248943c1c01030000340480d803907000c10340d0140382003440d0520821000d41401c6050141c9a00f001000b002c0c0e40003003008500c2e0540081d805000f0901c240030f0302c0c40e5942c444c1621604210402d500080401c144207035030a101c2d03004004020001002c81e81340c515403c1c0300c1c10102094210071500703651900c0d40441c40e031800d440c240c0c1d09400072440f200b40c44c0070241e80c0d21062109102006103402404004034030704921100580750550ba005d00b15030f03520740c20a00c1c800d645030303000c0b54141d100f485150081070300a40300b1001d0340c808582c034400a110a41c01c0004011054200114a64062281d12350004030720007001d585000500d941400014081c8039410180d0030740d0089461807130f5150558504000160b4100102c40116406180c000303041d44480d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 105739289 1250 105738039 105738043
    0x12050c19031a0a1107050d021002070b06150904090309090b09040201120e0a060204031b050402190507060b18040309060815040506030715020706091a040302060310080d0e2e050a02 79
    0xc0001c0d0750395110101703881d01003110015088507a0345403038085805003022403000209902c5003001c01441d1001d1100403a000f42400d0f00c400c101c4400c4140124105103884010400b1660a04400c0d400105811000c000c05420707031080711840102607800e40071501d03040d00003901a20b400c01e007040c44107560301c01151200070b062106807900341d03110341d055680344c0d582d080c00c0c40104190780304100c00d68614680010180360034030864202072a058548000902040b44c01d440540011105444082d00c65000340303856611103400c0d400704041c2e40b460400d641080c0c2001460400e01d60019400e00400b0018450164440a14846100d000700d070086030964031b00c00402c0c03e101c100c0e4003e48090034040d10000e0055000309440f002d49000d42e0719040003680e185071085480c001d05143c82e45640041000380050304156000f036600c00c9254107000d1034030350350f1f480151400c0c111300c0b80c803400074101c0710310010790307180840091801d41440c41d081080e1400096200c081d84a424424405014001442d060242e0003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 105740539 1250 105739289 105739301
    0xc061602210a0816120909050708010609060c02190306060e0a02090607060c020a0f0b070e0114030c0307050f04080102190309050d0f0201150f050a06080411090a0612050c19031a0a 79
    0x10205c40d5112001504001400c0c0e0000c0303000e1030650034240800a10f4540c0300b401c20504071081a690b40114501d0001c1c213a0764000d00e110140d8004410007041d0140854a02c4583c0c0114410310f00080e00615190f102c1040510152021091a004015959040d40c802d0117a03200e8a07049070001900101029060703140042c00413004010180c1c03191444c00b845069000640f0403956034603840c0300f0105040044034014200400e509143c1c00a1010810340a4030402469000349103041c03280c03078101c441c04465816006540044010f80d000109814858285100704440c03070002d05080c803035400142c4d292030316450a400c0d80742c104045028003a65191007500041c00500b00950140790803034551200c000aa0221f000d1903000d400b48100000c5c4051050000300d100d141c21042c0303e5511100c00c0c04004c81d160004c0c140025440d107030000894654101041500d909210fa07004207a2400024103110030070f400d81c0900c4c09820141e000400103e100826172052842c841c040321040ca550740301080004040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 105741789 1250 105740539 105740543
    0xe131704080f0c09010b0406020601030602090604120c03020f0f060306040c1209110a061812020406051201020703031a0f060309010f0e03070606080d090302120c061602210a0816 78
    0xc00d00b0302c8148840c4003c90a080619000c0e115240304d80e0f22401c6d2144584528810180168003e07001000402d0680d0f01030640410014a4189850755a0080d0b11001800d40c07425a05142500e000b0000c5141810400507240c03404c2d114244003170040340002c2e03c103001c014102c90186866901542410323126840d0521000c40070705d0108441d076014105a0110049100c80501620024030042140e50003041014241000d0b58440501242803d8481a00000e081d00480e002a119100400c0c0da5459029418110481d81d00040e25200c007030500500343c0f00340c201001818042c501c41d40d40a900c66401d100c25200041c0c81d11542c9072610034078a0f00403c00c41d6512100280350400e0f848541c0320200040c018140100e0b4103001d0b00ba00c1d04c000c142c880003401d04520118401004c2080181002540c0300360014038070096500014503103000c03500d290301207461407801042e40304008046242480e5000110f1810610194201415107507441e0f07603844041c2c01502c032040c00f0882c00f1144000c001041c40c119 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 105743039 1250 105741789 105741793
    0x20909010f020309160b070231020304110f0a0803040501051e0a090e0c0301060c030e06130f2102060306120a05070602011e0504050a0303110405030610050103060e13170408 76
    0x8500980d4445d140c0e01c07002000c051240300300d580040e605017440c0590f9070a43c1c0040ca050800042401102c005400d03807807580140c44418034103803d080c645403014621643c0140400d8480b40c100c0000c01034204040120a031050341c04031130901001c0c0002003039a0654000f0300f815a070f00c0e2050505c00e11400800908103511603400510701c40d540c0d6006600004540554042480503110200c3ca02c02c10701003400b4910005402c0407424011038400c08184a60003c050107035864109440c50710340e86080075400c0040c90300908081007007200780104d114500800c28083c500041d145aa000800750b01c009403145100c1c25201450070310402082c0b000d11030807a403100c1111300080c0d96000180c043d0401860304010072030003500720710703011402c1d004091146905c07202502001110341e406500501c0000607000e030305907051001181603241003203d03501a40445803146401440c0c075000400f45c1c0c816800c12001c0601d10000d22400c19903500c1811640c582c004140415034804607007008080c09964009039040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 105744289 1250 105743039 105743041
    0x6060839070204060f090c05070f0605041e050d0f020708060a111b0c0a0f030305030a05070302041a0c0706030c0203040303050c030d050c07020906040204062001090804030308090d0201110403020909010f0203 91
    0x80904144002c007106c020b0701084c030509032183d000303882c030380210500a040480000c4840d000101b460344010362280c401e00b03012590381c10a920360440b99014000c201c58542c041d80002c0f0155130000d0040114443c00d00c0181206800d00c05455168103016080381d4003117855058031a0000c4090003500c0c9001403891015102c9041c0360001e942c2c614904071444e019039036826002c01e6020003401200c040c1ca0305501c81620703544174414210300a0900420343c4003090f03820b100115141558240c0501104450609281c56128002c1c030b260074903c940c2c0c4024245440c01100140041d004020b841c1100c1d01410302580b2102c04c0b4481c02c2c114814910040381d41c0d880e20040140e0600480090035007503000b0742e4401819030f201c00520049101e503016210104240c0103444860786048149598190b40c00310000c50ba0031500c1d83c8030f00c3d01d90081e0b001100450311250030820f10307003000c00c03003150810013500c0240450383c1c5039008491130b0301c15404081e01401504001580500c425005503450700c184070707021992 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 105745539 1250 105744289 105744299
    0x30405060a0605040b060f090d08030901020406140903150405150109090302010e0d08060d0503040503010603030e010f0306050a030210050c06092107020a0506070f080309010606083907020406 84
    0x16403500719149140c0500d04080402c032414140304203c1d075000d0150140d46040d10040c1d41307105681108154960002c482c4414000040c039480c040d5000f80c00c2c0c44005030300c41342440406016202160440c1c444044144105000c070340d0b000640c0240000c1c05040800a5244e909095041c044801c0303800c1245900380c400056404500c3c2c2c08880d480340280d008000c0c1c40042040d00e0b0f107510700c02e0306000002d01d07506d006c40d0903444d03e802d000b8103261052080703914003640c50001c41c0c00c2d100198000c1c5d000c1041024600c0700b41d42c002241041c6643c6a15040104605202c00904a06034030300010707008075940b1041d00b89440c001c800302c80c1c5241c088001c40e803031880d1030710405a803849113850101841c0180c004800e900b55007181510b121990080c183c40f142e50501003403002d181c1001c0001d50300035035540c000002054070b072130003180030f040f504001140d900d00742007000d40069006801c58140d046040304a01d10720050070660206c9081001c10791034500c0d0002894035050082c450040c0d0b026160a2000079 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 105746789 1250 105745539 105745543
    0x3011505160320010c17090a05100c14040b030f04022701081204050132041e060509090609070e0312040e0c03041502090d061806050105040b060a0e0f06030405 70
    0x4030700c411010a1203c044801c2041400d0340c180e004010080707120040b50503040304d083c11a00e58000d044404840866000c1e44030189085043d144540c00030360b54078242d901c0d841c0e00c01c1c0301c130002e0710100032040d15041c03030b0100b42d12030b6100c01420ba200c40540100428119940d0442c01803070741d002c201d5114414601c40c4000c4000400030703c6107280a20444c02d411211105c2d03002904e0407500c1c140c440145e000010741000804c0824031030300040d025064000040c50340d041038081e0000e8215168903112480032690b10042c4103445402c41d2003030103030600c0010210750b182181c140c1c4c404003c1d55000f065480d914026607031510401011641401a5110045406502c0003d4030480700681d01414170703a1034140b24081e6621041e90040c20089000c104420010091380042244ad01d01400c0c000390007540707856031011980d580d00c10384616900d50280900703100c52405541d0160104581c1040b0341c02100c0c002469911407800d6150070700008000c52005070b9500c042407860764401070300840c1d580c07910345030650f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 105748039 1250 105746789 105746807
    0x2090403030203041b0617460204080f15130311070302040e0a03030b1906081506031302040b01141914070f120e06030c0318070303030f0606080606030115051603 71
    0x40440b01d03481001401784001d0238803580120702c8130b014802840280aa421818400140e40c000d9095500303902008183d4032840240002c1c103030f400c00341008465040c002c901f00a0b1781e9551b103501d5802c4c070061007000041c10320721100c2242e060400c042c414841080f0b260511960340d02c0603500902c3c00502141e0b03580041554620944265800c01440444000b0070481ca95900003c1020401d00c40080c80703100c0c001c4030280c0d001911301d00d0008020a110000809691048854040c061900c440038011414903008111030340c0340034201000003074107021030b034000c5000704000802c0c2e5080350a1103405550141d000070340c0031000c486200d40c3d1101c0340e00b407e402160030380300c00300c4502d090702d0f958071106880707181c486510580003005070f45146c9480116004642001d08002003804039618000e0380d443d010419400258407035180403a481034000d02c07820490b003441c2d009800307000c000c60070880301c0d0355004101d81c191049180c2c1071450462022048815008000e01d00e1080840c0210350307010b01d90081066 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 105749289 1250 105748039 105748067
    0x180b03010c18080f03220806040f0201030c050c10020f040306051509100614030703140a06060219020a031502121003020a06050c1009031b0809090106020a02090403030203041b06 78
    0xc16070399442c642c0e41d644c102c800c0b034403046800034803851041c1c6002c40c05021100c80c000d4071510029480d44101c506200c000c0d00c0840714540720040c28411940c00d0700030b185030410a41451030400d09400318042d2102c501001d601c1c12558000740d010b158003005c1040d9400740d50400f10810a519100c08060700d9840341001582c441c03140d910018010182040d07030041a01e006030b843e290901c2d20302e4105d101903080540300005140d19003003003400c46044031480c1441019150030200e90301d880d204000e4144403d084d1034050f400240c00d02d01025881394a0140c040760f42c0844540d5803022291a64002401140c00071406c81ea40b45003400140c0704d60515980603280200c43e40200300b65540c03816a241d00c15810b90092680049201d543c0056403079004101c600e00a05110402c1c095045d454842c005460408841c015004204c0c8407407401c0c80c03d2002d016250500080c007807101c654000410f481c00080c0009c082540000000301001400718544001c1e5040355400da5100747c4840d00600b00390541035031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 105750539 1250 105749289 105749327
    0x14030c0102031012020d060510092c06010518090c1023180907030b130606090506041d1b040e0916050f010f0201180b100803070804180b03010c 63
    0x40344492100d004001015030044c0752600e11107081c1d40301c0740032300002019011400ba0501d00001c0c00460350140c1c44500040050f4035400b440900c850704000c0d20800f41c002074560046c8010701081d2030f020300090048500d07600c80c0c02c080d510844624a84444e81000300d41110944550709000341c1c20904610294070310910032021440b1280c1d4094550040d2041d24105018044501069081c0340076400e810032050f14020408ad401d4602040c510354400103400c02c0507584000c01c21134141e00c10070b15406800e013203c1c610f02c0c01d8a0406441d031107000c0d00d041550102d00701d201290600041074041d95000707401c0c0c2c0855072500c1c4c0d85e0742c0ce80c11000c8100e5031441c0360700800215030000801450010305607900102400b4100700c05900440300c01e9100780741102550b43e034044103445507810b50300070b01c48240719131404051440c004150700e42d605800d90040115a0003402018005815401594162400d0700c8802104440c00e4884d41d000c1c020320190036405500c0e00400d650082e5201812059100320000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 105751789 1250 105750539 105750571
    0xb0406080610080606030a03050702030312010303080105190e0f061c0303090b0c03090d050c240411030a0305070303090f061d0706020a020a0e0a0e0706050319060501081314030c010203 81
    0x254161200c804a85003030b1b050300405000702c00640514089d04031940040c1c00c490600040d010420103602080e001600447c030100010441c610b8541090325580129418904e1240d1800190114140e8040e01c03241c4921071460006509894010b48445112181c4021032582c19140c1405002030503e00c0003074a071205050001640350404404403401000000001d040324500a07200301c07000e80098801d00080d000c1d410910807040000c80700440010000300305221581440c0c074001e542c400703d01c0000341c041c1d0001c100340008250000b003580e4000f50542000f1401da0205e01c0d061014200450008005501c0e010000c4124250078142c100c16240c0003084038401d40e141c0000781e0340c038a20b9050080d80311044107803c0c00030b040300c0748442d41c000f070560b0008103188420b0100d080c20001c003a0032900008801000700f2079103040300300c03040c0090034a02c0d01c100481400d0000082c84503400506940402d0500c00c070000c20402000c1009100214241c181c0751941d80c0c203170900d03020b98810f80c0c001c00d550381805 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 105753039 1250 105751789 105751799
    0x50c0616020910030201020d1413080115091401150201090212010b010807110a1103030c0a0f03020607030b0a030b04021504090c08011a0912070506040f03021206060f010309060b0406080610 83
    0x10f0460000d03241c050300104045103030180229088a1110b01d94007240d94144501c0d02c04400c800b1501d005803800f4000410041604003500441082d254007601005041c0760170f90b546a520b00300f0443c1903070340301c101029119070000d80581c058020101d00940082240c125402c0a030010b44c484502d200c004d0b81d94840342c0d100c4400031284059091700300740c019080b0410000c0007880100403040c00160203000d0b40d04003418060503500f020080c0400341e030310260000c2a00708241c0e05009640d80584c45040c01c000246400c4041056455140401803255101c05c01007801d558a019154079407101d503180e0f43d9501c1e9203c0c12900060a14a210500801e0391400082204d404440303194154a0365101030900784000c8108118011441f400c10700006e00400901280303135110305000f4405400d0041c100c40c165491441030044040c1a00c408030138030f80001044c00456905c0c5145298504001d182c08500400d01342031400003808070342185035001e8a441000250502c022030341a1080c039102a04180e50b03030ba14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 105754289 1250 105753039 105753061
    0x9060603010908270d140601171b010512390a0e0d06020327030a090b1803060108010906290613030b070801170705030a0609050c06160209 61
    0x600c1c006050781001d01481d842d640d420700c0c012859190807a1312080240d659408500254881d003803e0740c020302d100380001c82442d4100301d81801002e0f130f5090040c0c0c4062010712141c8801e8203107a0131104003069461071020380e2040f0195121800901400c896a047c04000c5180d6031407400c10805002c2c001442d14030041c641c0405d290620213502401e24179044400d5412101d00f01da081c42161f000d50305160b51030209003d40302841c45005000741d4000801001c3c11406841011405012440c1c0c0c001c001000c5403d0340a000c0740c0446070b08040342e03620782e01d90302241d05c0d044c0010100c036601445039400000d424481500b10002040c05001d04100c5503840b9801071a1020001d845000d60321b1480040700e401d81800c90081880441728082d001d445038036592010315014080c0c0d104030004030380358010300201c483c1c540580c81d03800580e0300402d0164a0100805e0310f51000d00b0001e40740c55a2110a001404410305c400c0c0c1c032407103000307241540e580404520481520704141082e80540340ba000050b0541401c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 105755395 1106 105754289 105754301
    0x612100609050c0304050a150e1005040b0f1e1909050a0b0603031815040509070c060e070f050904020d0b0732030103021009030c0b030906060301 64
    0x41c1a00d5a000c0c2c0c1e2002d4040b41620301c0800511000403000605508000d9000703000d510882540803c0360010f040c002d0054007580510303170a41121400541c441031156100394185000303a22a10340c0c13180140d004a510301d1001c0c40e1411941c2c040301107405d501d94440046d001b008103100305403605105590b0812021501507204001003c104040c0009299010b0001d8000390305003c8a46824090104041a450700600390400c8821780090b0b8170701110082c110280c0204000d051070b640060000300400e009a40300d600d81f0050030844600411410101c5601d003004940140c00e0104102c1d00900107402268403041080ca85400100c5840c501d40c0f160714030361500460b081d001c0500ea0b280701c0061031101440c4041c1260b2240000350b5101f03403819603170150303440b804040c15018245c6e91840c190300b000c0e11200411000194211030368000b10b00c1010342c0d10a96005840c0d0000f03050981e44 = true := by decide +kernel

theorem cover : BRFrame.Cov 105575539 105755395 := by
  have h0 := BRFrame.cov_init 105575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 105575539 ≤ n) (h2 : n < 105755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
