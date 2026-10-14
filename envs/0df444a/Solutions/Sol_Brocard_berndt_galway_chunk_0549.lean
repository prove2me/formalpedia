-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0549
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:23:23.328909+00:00
-- url     : https://prove2.me/submissions/e7ddac0e-a88c-459d-b932-3ba2e8d284a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 98561151 ≤ n < 98741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 98562401 1250 98561151 98561167
    0x13080c09010f060e0d0519030801050301090506010504050c12190b0d11040504081e041d0421030b060c251a030a0209030109050a140a080a0f0c05010c0c0611 69
    0x250a4001d4848a03c4d1008880038100009200d40001c1c10300602140541400350089244d41545d03080c19074041d0b1500c814a0340e849040c1400c03503084071000780c5141c22000052005160941003250800b198807143c5040c00d80350300c440c604410065503aa64004281030b04546210f45a02036400c0c172040407100e090842c0403d40328400a501c82089040c400c0e80c1d900009020428080706032104510b2040e602d0781034203a52528001d8a5005026010f030a400d100e04842c09c00e820090458840c03940181c0740c10110581e4102400c0300c2d602d1b8041d050903d61203101c00465915075401900740c0f40384040052989210441e070134052402c0200410f40001040742051010403c07012107501e880718100041ca50760768410401100902070607000960550070410342c8000c1c050001600c00d6058000d0300550030706030482c4110b903503511424000a089080501c4403c00d8113004071011800801d0740e007028074a1070201c1e5911030848001c04051004502c1101e5010f051201ca44501003045801504083c900008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 98563651 1250 98562401 98562419
    0x6010e01061d0111061920090d0309150801031406010302030c0607020604091418010b0102060a091b0602030a0e06070c050d080d0f060e06060313020112060b13080c0901 74
    0x1900b00d00b4400c20020b4914890183d120305000388540b402902522040d04101481e0f414038480c40003031111103800d024824100e9550562903a080403c1070604921300001c0310107020a05070310711002c1d814041d80d4100000c8822040240d004103d00c145d035000d8040d0f0440c54101e0070101504012861a0b000400501c016200007808108100c000c41e0403e488030f62520003c1c0700e1f84250b802600043d0300380f240c81200402c010a01038002c0320b10750aa00c014280c03180c2510300301d038201241c042c0141c0c80940424608917441c0e1220381c1c1030f4020314500710705400004202e10851900c3c1d20080050f03000013080a4400e511003000302c1d406804858080c43c140c0d20b0344a01c4e80c04401801801e1042810000d842d0800451108440705207410742c106004511007620301c500140b95030f00c81c480d85112103000080c80c903c0c1000072a4822900c1000c080195403c40e001103c01d503090001035a0040d60340c40000c01d0000c041d50145c0786020366103401c1c00c110303402c10503840e080203c18001030340204540302c014016590 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 98564901 1250 98563651 98563667
    0xa03080109020f0d0e0a0611130902030402040f0203040b010608060a060206010e071b12090512060406200c011e020309210403020a090c08010b09030307140a0209010e04030206010e0106 81
    0x1507100d002d80c86401003192003001d445030800880d00c0e5481c2c0001410606004100d45a02c2800ba2200b0030100c000c00303440100c20b00c240f08615034000c880c601c0502c4020300c0740c0d02854100b0700161002a0401c1940362940483e03101b528140d54881c50507004000c00e5070b111845c41c0d1300c42815911410218075202001e076887e4010301031a0481800c02e80000c0d0802e00c0340740305191198501d00d00890441450500440e0303034103c0300d0710000082d240c040205550030700000d00c15400183c07800a28041d6540e45031030008046a110188800d525940d41e102460b1581003d4250034110750000154140c40910403d0440b0004101d00340c079034014007c0024070030003c1400c100d40c06481d4804000b07494200b041014a03c0341d604025449600c44002003a90b040395880b81e4003038031054407120407690b02d840080d100390003506440c5916034810040e010008035600072001e44910a03a045a20050a41e40014a140b809070403490a002c007103400c0000340b43e81000720600400070250010b0080d41050710040004c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 98566151 1250 98564901 98564909
    0x10209060f0d18030c060507090b04060309170c0c03060901050402010e0d030903060203040606060f02010908090f01030605090a0b1503060109030803131a06040b0307140415030c06031b020a030801 86
    0x4007010895200d0300526401081c661002a00003446144881c6000340c0100a210400e075201c07441c1c1000640788601420040040d00c40621080d81020f01e0070b40220060000114101d0719485141d09600c1041c0c803e80c080c004450400c405003803c104060141498407400901c5203034640c1c1071005000260340c1203080c000107408151103181007510700c0e04041c3c4403c0d449500060500b0300c00001c00c02402103503401441038909545d10b100b48000412012400c0c0d502020015159180400101d512403410300070b004001e1506060200d18190790f000018030000088400b112055190307000704446103008403000300d0300d01c5c00d182801d04504003c80006c1500d121800000d2003c80004007040d140700806404c625421b50141c1c2d02003695001c90800001e041d003d407801c03030190382440f1107484e1610300810600c0a42d035409444481c0e1340c0c1c0002c03c0201400150761789030340c80c0800040200100e25250705500c0a80b07450b0f01c0100f61480031401201c1140c802c0a0f44a0864101050010000c0ea1241c0080c2c119 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 98567401 1250 98566151 98566177
    0xd02010510050d0f120c060c050a3011030402010212040b0a050304030e03010504140f120d0b121002130f030503090d02060c071d0c09060304140c0d060b0f0301020906 73
    0x918943ca0308520314020740e02d001d1702103801818401e000c9a880301e00b5003070b140c0c0f18a90502841c00444c40c00e032002e000d8404000301113061200c08841801494030302184291681040705071050004140704101d41014a04000084e4001f04020642d60100080046801207404645c0340c14034001201800d4001d0030460000c010300000030401b85441840e404e0402d040040c0204114102450712550501170141c091030340c0e0159041010700114042000c580300004598114171380720841c54003c0003000e440000720f0744054640c4107216019010800400040d0322804010ba65210309011141d018200da40300e60100442d20a043c80040c1011054440202040d80c000340d114039144000340050103086034601542c17045003800120150080c554856105c0140010b8241c0e40396801000340342d1042c1e81e1650341100080010900107001410040885840f41e0f09440070303480003800182d1044401d0006032400c1e82c590030030500360b203030822070809001c0e82200210324000d0341c2e0010414a00400d001004c1d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 98568651 1250 98567401 98567419
    0x50403060c031d06040c05060f0a08041401110c160f0308090a03060e010204050111012d09050616020c0d02091803120903130905010b03010312030219030b030d0201051005 75
    0x29460003500103d20340000001c20205403507000141d565180300454043e102c400340080c0005c2e240c24080b040742c071420b1905e58118907240c1100070030b8030300c064058400c55000740c0c00010742c07002d09820310800c06403400c02203003540d0b2800305c441c42502e0b0089205800c1283e078800c0e141080041242000c5804032980103080c5900c40e600d071000140003490b85d602c0900180c1c10407400c40b03c4c0550640c010016218262202da15045244518900703c3c0c40c99140f000b05071100066400800a0603c1040b103074141e850b10201c0d0620712a61018140402174504480c140070110490302c90f26010701200c0e241d0602910046e00d061525000119500000b85c142c1440300300340200a212008140b00f220389000e004c3d03070b0001c483e003004240a6034a500401011040d444c1040010800350303240e00a16049820882409e42103900f1522840c2034448254079007400e16900f044041400b03001c1d2080d16103001c80d5500c00040751101d0340285800e1840007449030003164500020010034809003115442518016144261 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 98569901 1250 98568651 98568671
    0xa06080a020702040c02010204050a0f0e0402093114010212151903050a0b01170703020103020f04150e0118050d060f0608150103050d05090d033002040f0506040605040306 75
    0x8000d100380b8030702030340240c100b142006040e6015001403045a10649e242c406047c0d4032240d400340c2000e680103584940050101080c054a403d264241d080495100d408085081c0c4008007006828130341e00b800e10410030345461005010f001109040c1d0b525802000798905650200001000300d00140540014694000d00e4080c039200d070080340e0044840a45040d183c1e80e180d05000e5a190300c40c00d802c4031100c5c003900012030b034501d64240224024008400401285065070b0054000e500500c402094801d011b000000340c1a0805201e84000741c03260716000d01c01d41c20040010b000003c04080d901c1111010700c8104815142e40c81600207082c0c0000b0001001016410303240050400c0780d00c00c044030b04c107003407401030001e4000c5807950499104c0c4089841682c6210401d540038050300b105194040b9003e610302000c240220700201800a054000c0d2000c0d07100c0d642e11700c031801700040c120f490469004c07d040c04181b61141041c0042c0c00e003110414189440c00000400602c0755000c01001c0f1612940c0c207607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 98571151 1250 98569901 98569921
    0x10f020f0102071406070c03080c2101030f030e0f0a05090414011103190c09061d060c0a03020105010503011803110f010203190b151b030708030a15060801050a0608 72
    0x4600180d04800940d80d98049080c0f40110010090b031590f01070117403a01048200e8094902840401c5d450b0700e60745000d65407078540003410b4001c80d11000d13203c0000404c50300c10b8044404880c2c0694032403042c0c1100d00040f0b050051600a81c4d0764040d0045000807100c0f145036840104200803075030b0440d82c0148035a42c601c0c0005500001c000309542c2903003011585406822078a010314852400440480402203910500300d040e9980d944110002c950b818106100c541c2c480d00d400c02d500101a034510b00c05007400d5021801799401707820100300702d400c5031202104040d420300405006110450007480454040c0b9008d0a014040500090a025460307001007481e190a000c0502100380c40d800840d280c0c038090440202d860101c0c0342c9103a40c149007200d45011031400b06210429184a1480c0c0c60525942c1c00303d0181c60940031101d8850b91200f4840d0382c00099050300214881c070590343d000720300c01401c3c50451002cad4141e0740140081c05200001400340d40c450103043c001b102d030303c1d140440710358603220010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 98572401 1250 98571151 98571163
    0x2030f0a08010816060801050d050f0f0d090506030f07030b0102250509070206070903081305090a020c16060c02311e0b0a05090a140405061012020f010f02 68
    0x416408404548900400e81211115040b0360700c400c15210004503000708554007040350f005600105084000510031420300400081a89104800721588244c103d44081d00d0221401803155080c0d20613144401c0703031684150310600814043d21000c0c25401c182040b003000e400d004202004040c0e45041d00c00e116031003005150104c083c2000002d16401d4480003003003808603039010b80f60141d1110b00101d1600c5d44005082841a00c07a60342d440142800d5503610641c1d940001552000d001c4142800701c0c4503035030700d409c913800303480070480040c0d6402d00c010400e410004131803600024803030622020040b0740d03008a60018042d0f03045070101c041401c40050031000340490a0b41d61b104440e90080e200d2561070540c8090f002d1515034504000b4204070607035890555001040c0315800c20004030042040b8184000c6450b04404003020214048130008503444e40ca0800311425600f580c0210f00f4050500d506c00f2148001c2c0103ea850908522034580128501c25555421941007141682030240303042d100344a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 98573651 1250 98572401 98572417
    0x30621150603081603030c05030411010807120c080414010509030417070b04090e011409070b130506190f0e0913050106090513050c100c15060810020406030518060a0902010203 77
    0x3c9803588203984020400d01c48159044000c2403a0071034501c0e1180c003610030369128070b40c03007000c1ca40e402000400441d2030b114050681c4060050707038a43c50340610703454010b10b8043c03012a65544640d20305410110560141a4030614090745400240106000701100f26000c1c1d031020980301e10303414455a0071526003c0c2c55889288032540124002c6040c0071160090403000c3c92000085c00804103880344c88441c803000307a4001d11203502050f4208000344a41c0080c100c0d00d050018010b000c4c0396240081202a4040c1980e400015120030010b030a107034110054125a00b11454a00203c00010000c80e91001c03028042d80c10f08580069190108030302504100080c185120061010f8188140075040e2071140c2c54080f503660060301a080740c00d00b080c3d0f05010380c02d8503603500c5041c00c0c1c1c21030300c4d0072649450343d2028400301f0780ca640c00454015010051200380701c00050005a540346000c000804603000a050340e070b190b410084c0e40654040c3c00007601500a01c00001c0000c01400d948011b0785180324040d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 98574901 1250 98573651 98573663
    0x310090513061b1b081308030301050a0f06050301030206090409050a080c011a060909060d0b040c062c010f051308150105030f03030708070512090607030621150603 72
    0x10410311080328080d005032180b04640910080390000100310203c03180420010029082c07030f1001c1d07125110442c030301081c5800340079880d01d03000010a902e20340c01400c1e00a41181ea10000c0104040d081c84110b60380203103001503400c0001801c04030003c0c824441840003a204140101d240d4200d503030745a000301d0180398010112074001c0681e1500343c00e40d4100c0303070000140754600759002004a03408585002c4150f0028101840d0200c000d0810a10040140115412900c03102c0000001951144550f009a0042c55100102440c002c0c0042110030403036900388422641c0001d50440b204043d1a101e0b5900702401c00f140f80c8101214221854080c110703544800034107200001550200124052020004e24501c02c00325a0300c0d0018180d9400050501c2d0700558020000215164444d1090a420181ca441c02c01c0ca001803a901c039559600302500e4403409504900280000941c040c0710360001006419039240c41e0707040a1175549460b4060300800f601128100c504c007860000d07641e0200d4051039001c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 98576151 1250 98574901 98574911
    0x3031611040e010f0c020705010504060c0b1308070803041e0b0a05070e040f0b090a020a050f07150c020607020c01020d14090d080712090b0909060111011104120521030c031009 77
    0x20782d10010b82000017404003d40580440420954440c00880d402c1d0743c0c00d9203580600850a5a50000b2a800100620000b556402d070010000f00e00304007c00e1400c0c0550312507a204c0c01c0c941050134404055500180004801116100000344810265944564252400101e540e5540d00544e149248200c2d003d034094035103040401020741e2030b03003d5162100c00f034500550f10f03655440000100c5c46444600c00105a052128403003070410000109029482000a50f4112046a01071402e0318803402da1000960012420001d80a074100304203e510b80c000d01c0107100c80401100c01814400403140c04580143c0001011500f54417aa40007191050344201407171f030750300400d080002001d203480e01c0400c001080c108001883c020b0080950b40102d80c0103107805940d446440044d03c1d2030130496500c410554903031004582c01406c06000d0802070a266110311020004e600c1e006052180504500d00d41c16003142c1c1943c06100701c1d23410f9179800703444024481d580f0386a058800c10300d486294403e50790103041c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 98577401 1250 98576151 98576171
    0x10603020316031403090a05060a030f021b0609010506090a09020121020301030c12170a0e0d0c050102010c03050c07060506031516090501030b010815060c061303020c03031611040e01 80
    0x410307009046134040c1424100b00e540c06004c154072071049205503640302100001c240040d280c05401411400c02c2410009140004040700c01c013030b6005140000003039680003003150760010302400000c0d403001c0403000800131464808000341d00f451020f48a101041d1b6112500001c41e402250b04016004808000011441e682c144000103075100340070443d00c0d500d1b81c14001a0119030000500e49a0790f11000381003480b83e4641800c440e5412800d049030801090b4513080015480b507001c02d01c4050700a41c4840a5a03051800290030764180d20345400406103041d0400c11490f00c00d42c00d442d01c480d8403d401285d02d44070100001e00d08210101191900d181c09024030203090f01c2505144130707000c080e4030b036801c59603910b100550031920b0315401039022070f20f00e4000404030500c54600c641001401050242007071303c070a2019203132040460b01c00a05400c050b02020926804000c090204c6900b2030065142c440c4120300c505007042d046100611100300d0000168140d0b9031038014030410700711000208200c00321 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 98578651 1250 98577401 98577433
    0x2071e02030d09030309030807170a0e03010615091503020705030c16210b07140417011409030f0d020d050f04030909050c1606110a08010303030e0303011401110106030203 75
    0x80048128420b116820b0b6691000d80680e224a00700c0b601610349128251440e110507610f0340c0050002c0790442014031045232540c0404019092841c1a0790310741060000c450203240c211855030304030340000c2100c482c98000c0564082c190324156042c0aa5074420400f420109030b020313006014000348175000c01300d203140c2c16410000b4011410b011f40381d102c150050b5952420381c3d0055109000795044590443e504001c47d203002c4a00344c2056082c03401c0d0010780200c891180d00c41e00103400c140a950800c0c3c203040c2006409018079200c201000000040c5402d0442d100c6541e44900e9801c19103904020803901e01c05101603042ea100801d001509000c6442e04007514032400000301c030118041946802d02052000c02842140d12400325292140c0c5080c100344601c050b144010401111065141d0142d40709aaa40ca0050098580c107070b100c3e807035554103500e07000d000c1e14151010407089078010b00c010000c1000720350340408800f0080c2807a0208240b103042450240210f41c1010750107215905c2120803c5c3c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 98579901 1250 98578651 98578703
    0x70203150901050604050c0a030515030d0f02070806010f120303150311040f090b010519050402180a1a0d05151206071107050f1507141e0c09070809010207 68
    0x5140002040756613200010001100da0a460648543c01c0c1844002d0055000703070b1066400441e9000022648034224001034946280c045081c00062400c04647e851980c040003040e0141c00c180c4050712080d130601760445030044947c810145801c9844800c0001c2c0b44c02a401084500d07100c0d812142c80c0e035124184511801d00881d1814052450081c0904800303403075101e113084499115901c40e025034070300320410480c00b289032700311300d40c5542c48540024241d8451004210803d019100c0e24203030700c2580100051054076034418002c441c80070786403940a40c85102225100240c0b003030001000e807542c00a80041c04075580503981c00000360001083d10550015030240309031000c0e0b855207001025507613083d444070004d1150340d0300244204910078451400b0140c0e00070039182301010a05001072621003000304080002c0501c0349401180c400440200c40b000300c041241d5109005050780c101315004a4801100148001c042000c1c480c0402d99483c020b4044590083e00b003181d030181c00b01110b004602d461 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 98581151 1250 98579901 98579911
    0x90905090c0f0306040f080306031002390703080f0d020a09030c0501180302040504020409080a0309020a0b030f060d08161104050108070f03150b100807090e10060302070807020315 79
    0x2c2e0501400007541c40c000600e64403441e40f1440007000324241d59609a202d4001038481c5070b15010309004488120041c0c13020344500019a210720346000010400341001e9000450364000126850f85c2c04401c403400001d001007280e51140c002550352481510110541c05290403007000180005003465505d070380804030300241c038064a0305038084d9503030b440151881c81c0200481c0b001d00b500c2d4542000949040d5100079413150002e080400c0c00303c900c0d42c4c2c0500c0c59100e08090800f00b692841701000b0350505042c050040c2c840d0264403855401e05288800d44231600402c40d030300c1100074900420801405105449040318540700301c0c010381c6124508000c084d00b80c41d64141c040e9103080d00005207064000b41c00c404982422920902c1175041d070300c0710503d0740d652b101c1d504242520307540700d4143c40c1c60b251002d00188080b607984806504203c840148400301c203038030651716010780c0001e2041044050103008120307191410016968400f40c6044411409007140182d4180100c1c802c241d4904441c0c0b04040c420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 98582401 1250 98581151 98581159
    0xa0605120109020a0e090a0212011203091a19020c03120c0c0f09010302010507030c0818130603020f060a021002030115090e150906060705010c020c030c040605030c01050a090905090c 80
    0xa0b0380301c2d102c0100300d02a410100c2d0014030b04400b094040e003016040749401c480d080e18050300e0130740f4851244881e01000e80c090030403461044100b00615a1002d40000604001e640800d4a013107000d19100b110b015120070010f1412421046038242e070f008018041c1c00301e40c0582603074500220419547c5847d00544182c21050060311810200b6140072046c002d24004001d11800c0321b42d0868004441540042c881241404041204480424003039400341c030324299031401c00c072168400b540070304c10009080840780d44024142001072005a031004000350944005a4400da1111a240c804a18048040005d088114070000c000f08520303040203900c912111894441380901d980e95111010f280401312140b01c0105910310003580540340c040c0d81160042e00c0182920f003000c41e2a2140f83c00c6809034595400175a1004c0a5144035007000c1c0402c030000d450171a420030442c0d151a01094582400001e618100000000d0216541e401281ca21006d401e11441c01c00c01c902e8100c0041d80d552116207492482 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 98583651 1250 98582401 98582437
    0x21002060604110c0604030e03070b040e010f05060702030d03020d02090603040b040b0106080f06040b0d08030a1401080a03080a05040303060312020a05120316030e1011071401020a0503190b0a0605 86
    0x95943c001c1d0454800c1100c0400a10166440e84c400b144c0e1054401110740c0d043c01800e400182c0c69001c01e014102600c40015165515403501140761034a40c4150300c40ca0091805119580250b5404100c0c4980d0b4803c030700740540d60b00b416072001d0000f403281170440c1c1c0d8403400c00710501003801641e0352001e00c41d500c555600549641c0b91781040d038042c801103070074070150580a03001800c00e05258000f07140805d000380c0b843e0030501c0d45a640308807d40003150780740d04441c1c1d2764400103064400106014010103205c405442c03004419203004016a81c000c1a2149041d241d0f004103040501c658400c400564005459100400600200a4543e030300204d05403039510440009541d01201c00040b0b90244d007400e81070740c0159a01d14400d03006403c258484070480d01401c8003000035000c80380140c2c404688554203443ea10316051800403032a48601c180041c0c0f5170702c103000b90500d17581c015049a4000e00c0811040c125a40c10184a4010f424044075680e00004020300010358250090064000c034100303a496584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 98584901 1250 98583651 98583671
    0x60f0614030d110a0c03030203030a1d030703051305030102030f040b100e011e03050111040f0b040f1a0903010c030507020d0e100f020c0a12020306100501080f070507021002060604 79
    0x161040c28410640e616030805810114628042e204001c041d07032036001529000c03207468440008074440c9074416009a000041002549000c9104510b0364800041c4440000002030b02d1440c2d5901414500805011000520401c038002000c025070080200800955a9180000107441c241d1010f580c22180c08601c84082450340f9603052501c01a51341d8102d110000b0307071800c20300e00d5108802c02030303040703e41350031080102c081202030041c541c00198800d4442c0c1d65038506199030034202000d41c401c0340e104509210601009400d50a0034017114040340410700c8164540e0014142e922610a85603070544c40e040e010613102d501500075510694168003074400783c2003c0b036400c0d1503c0c141c286070941c0c41340c2c0f4010030709016401084450f10070348492045440700502000401d00840091708902c1000c907411940b401185410020158010307002c56058041e10701d0500060290311303014060900d608903c42c00079040c9881801030b6000c80340c00802c1200001402c86003e5250759058441301e0095041c1b041d205 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 98586151 1250 98584901 98584919
    0xf07030201170f040f1b08061005010302040e0c03071e02010603020f0906010c1b03140a0203010c0f090b0d09120e0a060207050f060a02010603050f06090c010c030e19050d060f06 78
    0xc0e203e268070000c0501980c1c0c0703954030300041c041d0040742203e14000e50700c06a1110741d14a6400005080d4110062038942041301844800c090151302142c1098010042131046040306803403650000c0d00810081d4072600e40c41c44c04e95000062820141030050128248040700c0e5054100900b182d0080d0f42000f40420502d0600c4100c000031642e03039020880281000b40010110b03040c070700d07181000c0e40076251402c1d200d40e5450000c00c0003005c42105a030100c00303000c0540ca0203105160320071200c0e00740400c90b00000e01c1e0203403514a4910400b00000c074080b50403600e94265070050540c00d5031010304000484250380d4045c0204106116141c0a03d2445a0104255000042c85001d40d640105200b5440c1136140c01c0045c1035100e250704100319525290000006801002812104030210000c0c1c00ca07803500f01c080a161110b0f040004e0304014101e02c85ea00403907041440e21280c07900948580c190040b00c071104543e1554a0b03401290800d58501c8240280103055000741d5803c1c12451040c4946c55071030f4154 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 98587401 1250 98586151 98586197
    0x80703020a0813060b060c0705040e03031e0c07060204090e01150609230a06021b0a050109030b040611030a09021c02011b0f020d030f0e010801030b01090c0e030f07030201 75
    0x110700400c00e074501040080c240d00000180007442030001003910901c440201d4410340001c040103040381e00001d8207100900d0700340035030700042810000441c150305d4a410210002031045410015904500b8086030000c02e0034000c60300710b1500038400f90b40d15a80c0f2020704008009005980005501c0c0419014120000701088030490b4082d130f840c4c3c0c0d60941080c010000c821401d1750400e211031490400e80c000c54071414050350050200303401a054402000040c4c0135050140d021051191001410a0040380e03080700740e080980b40c200b0707801a6695650704c0c0040003003041e00841c20307852402204101c40e0454640140c21030610036070311804c198003a0f20558580c603204000c000d01245c03042000784c00500300100311940d114012403180c00b200b207081c1c0115403450515a401d90003d00c804a6444500b5044002c9a44e482020f2904c0b640c03945c075584859642000600962152549404283d13240300d2081900c0204003200905603244109007220740e69858401c0d1008030f0100f24607c0c400e00340c0502414070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 98588651 1250 98587401 98587417
    0x315030b092a1c120302040501090b0406050a1b0b090c01030e06010b16150207110a06080f0a23100303030c05070c120206121515090604090b0325050108070302 70
    0x3600b07040107122420059142d8a20180700c01000080c0c41c40c0000c108040003103450440680c90041e0b685017400001095203a007a00800c06045042204014035984142164201303030407440d107013030006d9022607040551a030124004d03203116015014403500e02804941031122040c01d880410040d5030b1300081a403154003d2082d150340350740501000544204211400e02028400c0c100d43c1400381fa4240350703034202d0700401030650340d07a07802800c104498105441d41da00680752500b440c110031701d01403101107210b1200030080e12102d6100c49038020260f1409007600c1c1c140381051805140c03442c081c0d40400d00081548004d40000f42000e200075034080c083c0c1c081380c0d4080c1d04620071660490400b845c24000003211b02c0d00700c7e0800b40400c0440c4800c00c200019900490041800106a815042c2041840e82402c15620b5520380f01704a240c05c0790755903408a4003100c00c440004209481034000007820b084c04c00c00d400c455130049070b58018121120005203c02d850302621015083d0700c82d0f160840803030003104c0c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 98589901 1250 98588651 98588713
    0x6010e01020a051c170a020904181e080f0d020c0607031b050f0f030106020102180102010b1e0a05040c09150801050907050306041d10140402030304030b04030315030b09 74
    0xa40130b6405a102880d80c001c110781041c2803120001051900100412100040140e40c04540740300e5034941805110200702d440c61a0751194086078031003040800c4100c07c1440b294104811a034100444035059a4003038034110041903c490485010034080d5110440c0301c0140d008400010366140c2c0280b140c48072000510a1200d440c0c408103a040d540c0d540a008403404038001813000c6281074403130b032000314060143c590015840d418000e10310030058401410701415641000c01c00f8140b91980d000081d40c0e1301c000c010511402121002140701440d0ba504880c0d08a400c00340616441c94022145008a449032140485003403002171080358441002e0041e264080c000002203002c01d440b59000e540c2182c001400000d090001d074dd401ca06050701c860010001d42c004110300c004d004a28440d4951082c00c85034680b915180c1036000076143d2065001c020480310200c07000c68213052080d4403251015280d41400803001340c0707a00700440b44035000c50344152540328100c0b12001c014083d04088079040c041c18 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 98591151 1250 98589901 98589913
    0x1020c060105060a02030c1c030f0e03031f0e0f0f01080102030f0703020c16030c08070e01120609261201170604020906060705100c0e03031306180b1206010e01020a05 73
    0x1008501d92021100c401184800d115501c800c2d641400040b9180c41120508d02d00c6007103038000a070a480515007400a05850281c05500741c1340302200301d9911051903004c03400d201d03403080350790310201c4d40f00d401044040d0118010020701c5801610042e00036556515804416071380c84201c0c6080c1e01c011554508040d183c1004103d01c18081e40283c1200c8080c101541c40200d8801070a90704025282d105842070744184008002c3c64005201c1031010303201d14103000e029981024000e400400c902c090041810b5a01d401d558144220102184105a02a00e165100f00800910107120303400115010040248a130000610041d80c003c1e4080e0388411000901280e80d10f135001c00c5041d0300c00605494012000b0008500081c10600c07050a0145420400280c002041e1100400401e040b002046c0260720401c40459010030750100d82c403c4035118501724900700c0420801c9000180c60768071107078150001140c92458080910f4101e4460710082e038950703500e20030b554012607071500000400ba0054000d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 98592401 1250 98591151 98591159
    0x10314091f060918020901080d020303011a0415030204080c0a03020f09090c0d0305031006112107020402070b060f0405100314010b090906090607031505010305040c0e0703060e0901020c0601 83
    0x559000604072440960000d070460b511400c0700c05a4411100c0040e125000513503450852418101c00c0d409030840c0030051107200c50307029001e5601d07c01030054038040300c01c10402540500e6443c044074017405081542e00000d04000b003014011f034209000c1d052842c09120100b04541c10018204011650001e00c12440c0103221814080015800790000d805070240400010050311114070040d09180f00b80d59450f640e10b410281d41c3c00400300d5400c030404021111698080d4070000161800b060040c081d594541c4011000076914a4800c01000035081400440c800b000d000780041d4092040f5030540385d00d02031050b00300401c81210030444100e15103084031002440483c0071305011509803040c6000001c3c1480d42070001409200d012100611b260b0702501c100f01103100d052104642200f40c606052080a03842039040c08107401a000c1c203410076607240e00040503c5040c809460040083c8036201c04141040e1304c00a01600031805200c0e4600742c0f40c0c0109078921014421982c41000450203050303584d0030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 98593651 1250 98592401 98592433
    0x1080601080c0105220b04260f030f160f0c230102031c06030b0405070510050a020c0111100c030606020c18060603060112020406030902040c030506090c09010207090509010b01031409 80
    0xa0b05403c039079017403ca80108030301503060010400f0b040e40403a0b8079001c005d00f400584059510406031034258100b1080c100c41e0b0b01d0000150384440c076410070a03a40b110b0050114203010451940d014016107681c0b40301c0024040040c481c00241c4a6496002941c0380001107405000c3c0640300b42070740103034804c02c0300e1121201070703c1600d0b200c1a034659000c20340315501c0d141c2809111041c0c03000c3c1d903c0d0b046111b0401c964502020448120403003800c00a081141521000e0348800203108005d040c0080c852000f0117144040c4800d03c0b03000303510201000005841d0314003c1c001c001c0307030242001500c9005208621480c2c5031418079810a00b84040c15129640c13802480308a410140c42141442001d54880c0203c0e66540060310240441d03640000d600c0e4034900402060f104011640818107240500780802501c4009080e58801032014800f030b60743c010070300102d140c020987c0c41105110329110a00080c0c0406400000b50220240d80c20f22035801c3d51080c20881e030038240c0b02140d075540072900c11070101107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 98594901 1250 98593651 98593687
    0xf04120314190617010e0c0d0b01050f0f1905010806011b1407080f0d0806010804020303071410060306051602071d0c040b0d020a1409031209030309100801080601080c0105 75
    0x344482c041800740d910354002041894074080e52249035101c0341000e00f480300402c050782c00c10b0402c6a5801c16943c8070740741c810900106000d20750060383c036030b880e040b1551281511080c0384d000283c0411800342d00c070301801d00d6855250103503500161005001c16065072042d0351800215440744200c8030324260300c2e914004100d1003055140310301d009600001510240600c1380301109081e00020b000550641400240301090040149040c03045800900c405602c3c00819160090390040c0340041c00d9003030180083c50075a1940558180d00c0c20108040108a00c40c0c0203580946101c4a50555440c034121059891380824040e00c950040d014500e42ca03022080590142c21001c50b0b0505072078503490b440c00e40c4079070748081c404441c1950002600c4403000d500c10581c0341d03d209003800c082c0c18907030050700294592130b41581e030b500c03100750107d89042143d40920484900751001003843e03c185a01903805008c000d0709114503003550240d880001810340d00410040c4c4941c4c07059413058540340203900d108031703500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 98596151 1250 98594901 98594941
    0x313380d051503030a0206010f12030e0105031b030a0207020406140d0f080409020a03050601180506030712060b07032f330c13081605040915050f04120314 68
    0x4942c6802c0380001d03450070301c010071a41c240c61340030f404150f06002444d03105510562141d00c08100c00c020010100e13510004c04030581209203006556078a503080d864401c2e4500d0400008251800803c0c42036540d215070040009a10949081c0905551b41c441a001c1d8507603d80d115802042c4ea800610010f440071481d410349510907035080d4106525403101804036046100f10304040380d980d506001031503030000e020404071f060300100c5811460800000c20102c3c08050701c503006000502502042c47c1c0a60342044000e0003c002c186525009241001406286a040c0100e175211603000034440000750076510fa42d181d03210000a20002d40d0740c42c8004804401074004421410203444070f80d1035a0076803007500c1d002d4180d1388241d80e11507402400a015030110f40d840405a0b61004003aa40c51102c1d13103c0d2039046036011100044c001c505420075a9015600c00c2c034090340e0701d01e024104601012908400360140740224034060900d240903409404540b04a08090091009440010210107441c400080c1c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 98597401 1250 98596151 98596171
    0x1005090c0d09030201020d18021e0f03010f1a0a030f0305070f0b0f040506090313090b1512041106040506030f180d091503110307050901020313380d05 66
    0x2404181e0340030854048103030460050b500000c04003403040703c900030f84442d800005940114a041580042c4620704202d03403c0d54034030004025400c20f581d132062501c0a124010f4028440b0440030000200100b0100312140d841944030030141d070041c20410300c1001070303e40c021002c1c02800c6203900d080d205600000d0382113300b4046248000c0020380e02e42d0710b56000b0a1400781d61003180c10301d0701c3c0117418454010b04842069000340715103202e07103007820050b808842e510300300094981440700c041400f400c00303640e035600c10403400551692207229102e0124410f42c000d821000801301110f040104605c00c84c0700701640031000b80080750000d40044030580d000081e4100c905004450b005010741040211110071002c41c001c032004028003041c0280300d04519070386280c100519800d141294689000180c43c05040020204002c2d206034020000c6403036001c1400c0c1c0e000056550742c00000c1c4040c8400100c003103441e2240280d152100703102c18460101c0844098010704012301841d50f43c00820004001640c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 98598651 1250 98597401 98597407
    0x70c0f060b04060e0f09010203191e050403020304080601050d0b0403120905070902090f030c09070807020a15050601020f0a0c06050d06030602041508090a0f08070809041505010e01081005090c 84
    0x9a42c1d11845000002c1c40400c1030040e040c9040700ca9a90300c00c2c0c0080c42c260199004001f00710407070000a64040c82c40d4000d03a000102004c051056000b6045001b441065a034a2300e01804185a00000a00210703001041102d5981c0e88902c00c0c410790b1501c1641c02406810715001003400070b0f0181000e4085003802d0305000036a182980c407480d2a1502d01d5005428060303002030901143c0c186101c0544000c1020b90007003600c07441807000304000d021f004049200b0040c0e840b0106100341e20900c08410703403940003000c40c000c114054002c1d000425054800350702501c2001503001c0142c8000c507e490000d900446401c094902d40300c3c0c02c0c2e920380d021208440380b480e514840800011b1942c80079102600d185200d0008807091484061300c09800039150801d150704c10b080c00c1e0001010000c101400c0f55024180d65102e80f41e40c601503501d4000c42c04619840b07800d26050841d0b040200500004a81c0300740d0300c0c1181342c541d0300011740350344000351006d5150781521807050180381407600c49a0340000841c201145 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 98599901 1250 98598651 98598671
    0x30d031109102105010b070308040311010f05014118090d170f04080a090306090b0412090602031b03040b0310030606050f090a0b0f0a030f120503070c0f06 68
    0x30303400142503402000c100c105000c0380c100c01d00803c026038800704503401000380e94100361125030207010f000c40080400048000007010503100b25405005098000004c3c80340588100900c0f0103071409006468602c0b00c81001403c5d0503404103600400d00c0030103604907081d00c06202c500084034403070540b801e404c8420640f000001c02964550907105080040c0a0003a190314150f000380000c0d892401c0f1000c400d140c4003888090f400c0552807980140e40041c9246d594032465201707031020b490341c0c0d102414061600030040288100215842d00c150b100d059146a8a002c420307041c0d07600301d4540110300c01a030007440340c04441206e00d001581c200c001041103030f04180d80c5082494595104036411403a00c1c000030303810000c20145010302000741c507040f5030001c41042c1440105014080007841c40c000140c81d01c2490040da210313182d5070441d0301c9024024002403500c0c2e04101140c410308080407107035034010300541c1e01c5140c440c01c01e1300c0c01500351750750f895420000f90300d030052191402001543c2c0c01f42d40d00501c078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 98601151 1250 98599901 98599909
    0x3070c06200c0601051f08010b090d0c08010f110a0f050903010e03270103020a0c0206070c080d0525050c12030f130608070309030504090c02010e0a05030405030609070302030d031109 80
    0x70412081c2c00140f0980d8149414460110f0809842c142e0080c0b00821840c10980c104000c41c5c1941c05000d50300340c0f142c200000040032003401c88005080b502d44080082003032041034100004003644018140145564140840c400e13118240031000081c200c1689d49404510401c000c002c0c0e91801800441c041140015a43c190340c0844007100091241017401d41c001c0c80300c1080c1111400e82400c0850030401c0f90349001d030031280c44a070024440c2038009030000c10419280020f4020f400c0c1242224040d9904603000b4029a000c5081076400c000b000c182801d640c40741d0040442c030264020003800340303481481d051088900b80c00d807c1415034002804082e00045100c0c02814840c10b0004052040500d00740c0d02801c001c4c00509164109820100e41401007034001c0100e43c00c40e4a91240003522204503032089004084c04020b600c5030b4000c110150341030000020280007650030460583c1e00720348031003595135620a11880001d4040d00300c141e0703400351240243c0c00a07500c2c54a00380721500c0d018440e4002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 98602401 1250 98601151 98601157
    0x40902030a0606090b100f050a030c030207050d02012301080c01030c0512040515180d0e040f02041202030f060f070503060a1d010e0901020a0c020d0305040b0313050c040203070c0620 80
    0x1388651036480590905915100703520320f0703100410f801d00c41405002034030001c000e4402d00400d0b009160b1140c0351281c0c4144070343e04880a16030400c0c26501d1031050006d0090103860710a00c0c02045221203590301008078885801141200c0d51403000704280e001e07200040d009403e440c001e50040c800d0601941e0348094032604103500c10742c0b184000e0304501000b03030840c64000e0f40107000c018409540546400170704900080007104400d450411200c10000c010020740030b0100103040040b05070000c10005a011180e01662030220701c22001e40c0c000c0c825400215960744022901101814450800300303110501400081da006900500020301407611250045800d4070656500281003810400401142a000280d136400100140080d0b02e005420030008088014072800640303d490310300c0c0d03680100750061044030300508032400d000c0d840c1e10f800f08880c001d05003600e0080d1440d0080719100101071409101b240c0c45100b09484929003041542c50f070100906040404c2c0c03e0113960105070510402c060405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 98603651 1250 98602401 98602409
    0x6060f030403090509180c151b1006090b0901030b040c0302090906070206100f0611010b090c0c0f030a1d130f0902040e07030201081f1203050c150105030c040902030a0606 75
    0x40e1404079494881070014400d80180040d0310aa807500030000c07040400702e01c1c0c889603c41140c104000207044401d06401d8440c402706203000c9240030200d0b010140c03010681d01c0100007103950403c00e841c0d50349200401d403854005160743c00840d0300011710000321a480c5850300607024210082a03d6201c0d03010803000c40c420b4400d01c4895118404201c14940d0400a41d94080880342841d200303d894411000c10541d40c0e80146000c0c0b101341c0e40d440d500383d4002d500c1201041c200070007902e06814809060f20140e4402c98003a801030003100c0340242e00002c00012101c01d00c07a6580d1310340d0740d03c1c124400350a1059040035a950310080c0216080f044814500803840c00703100b170b00d00010380071040348108000c4030203a10103401d154000c00c000b00090707a008485079501010505c0041107804421040120a14213038100c075081c40b0003030f04984103055001014080500f04c0794103c070001d91031844050801c520910400381d01d90300c410079003402c0f41029081f0b0f1488501c06422030b6200011a038603041030700c01c42c1d08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 98604901 1250 98603651 98603657
    0xf0403030302180d030e01050a030209090f01030c140916030902130614040501030b07180b0a120c230a2303061f02060718091407080714040e06060f030403 68
    0x140301d22003112412050303c01603000c1311806040d141c5540c0261808404c141071b18140030001c01d0080c0401e000303804480388140f004000c00501d28220311110420403080c00306032107400c05078001090760000442c40302960007000300108000d998610108c80c51780c842c942d200e01050345404580006850b1960340c402d24114034003000c10350300d0424040303552070b410001a00c1d2040b03081a0040000c0f40e503480046030001298540494a001a480c5089643d000399004200580c00010849185944140f44e019021042e010a1000c44040c0804035400240502c0810300303012004001000d21105600038016804103007491710150400c00f4020960709120070b4500003c0c0c800004120351884e1456110f410180e40c40d00021090289030002540d8100081070442842a5144510034940c076000404000303007444441440048045081064030210039200d0b540800d201d071010622883c05007000214002c4a10f00c6141441c0c540842105000c4001d8103903a0007820400100c1802006903005500ca00e010391 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 98606151 1250 98604901 98604907
    0x609080310150c0206161703090c01030f0603080a030e0f010608031b0a08070605090709050705070b0601051e13150c05060a111902010b1903150e031c020f0403030302 73
    0x1142c2d08114122481c0420802010700ea10b080180d840c02d0540782031305005220442c4140a038038221465060b21a66406404030100800a800c0d03000100305041110a076024408140e45080b41c2d03041c0e610b1342c0401004100140b00f80f000d074600c40c0e8809a01d107012107046503440201c0c5c2154a08440e81c0b50001c050f241c2000510300b502035270b01c081c0108103040100040c4050850794640c20740701e0107a5a4010078868a9001080021074100150b801516514000f00038a0400500141041c0e01c009001c4410210200000d509503000e1f02c242c8a41040104000801941c19080400a80c0c81508407100c000d411110209481d60580c072707401112030b003039240c0c20280d15040c01d0580c42c10308018407141c11f03141418020b241c40000541660301c181003682d5080e10000403030200341d0161039100300c1150054440d030a122032910710108400e040300c2c080c00f980d40700c1c4001c0c181800c4c16108112000c0901703034400c120002e210301c403085103146001c075048001414030706903008100059001e40e00030380001e9008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 98607401 1250 98606151 98606159
    0x30426030109091b080c0901170a081b010c21050108100e0a0c120c120206040501120207021201050610020a0206160f05030a05091203090102060105151b031b07060801050d0609080310 80
    0x1f0682d142c2c0034080400050300c41e0158907008542c2c074110b0a20040484d207021131041007240115403a81c4440d00c491000307101700001c8040040044420449410003403038a0038002511219521640d8103030751154010780309640f4016440030291a10700315146441c4941e038210300c0410505060300c0050814400410361103031403420038692102980d041040003000f031103141740050362032b4022681281c100307080403007111010403a4400280201240a50440040c1c3c0008001c0007041d400300d07101d00422158526580100c0004030703a1080e4040c40290000310800002c3d0741c84040c00032100e0301d1031081e2400d00d0010b5240d0359843c107540080701d51001090010a19445901d0148882c8000000c094010350808a000700000d659640603c5000c0c0203c02041207640d011640d042100c85003401d010780720341100c041e03161040d91303940642002241114048141da104400200e10707030044852940d10010143d00f84002c11846e1503900c60b08403601a1703651581000514070b9405544240001000883c841e8a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 98608651 1250 98607401 98607409
    0x418061401120e0a0b0f0a0b010f02030703031a060a03060326160203120a02070305071203120507022a0f0414010303030209130c0f0206010605040f060302071412030426030109091b080c 81
    0x8c6840b07241840303003c2d8800e415165000080d41e00150300352034040b5011850b28068449200c6219115421030800204050141c6d01078104500f101d110380d800c0394411100d40001512540c031000c0014000d41c0410402d0014079010100e800924002404e6402d40c0c1140a440d040341c0c0c2c0118484030141e003008004100380007003030001100400d0759606124043c40c00d40e074004c001d040d900c40c0743c500090351100403031035980c403c01c070b004109800d4040c0041c003001000115490000c03a165003620030510400465482e0030700d405810316058141d4500c4000c0e900313660381078002e0342280c0d8000c3d40141031110f502d0420011070081c00c82029868942c2d01031017414a800074108041604488184402000108101e1252503000300484840345001070f280c180a00d0701032481d40d182c081d0a0501d104007001c40d683ea59200c401180600c0c82244c80e4159240641005400d40440c200d00341c05001080c00100314052858000c1183d9900c6190022111310009520308804906a00000b40aa00c462000792072420 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 98609901 1250 98608651 98608661
    0xe090c010503061804050c060a17060a03050316050a020a12060b040903050a0e030f03030903030907080c060405010e0d120e01020f011413170418061401120e0a0b0f0a 73
    0x2803a2203891440c1043c003141642c2c000501e0b9a4215144900003010b000c020311900c0342150b00208000e944500e0709030000c212140400749a100b60090b9000b2440d1454031a001101f107039030110185040200040d50f800e00c40006039006d6a190003031512480060707440e410b50350080d01484448080e1581103007400c1c0d04441040781124044c7d40b410a0001c046600702d000d854000d0107914011554015100119040244125480c1098031003c0180300e1619070200c0038510468128044446180c2d440d0701e0141c0d11290b00c0015500088100000e0001d54440c1c1c1070001d0311900504580013480541da40c1c008400540c02107440007540141580090390b074184000403144480d40024462815110040f46490802078102070300c0c1c50488031150100044815903d03014060610b40c0d58681360340300001000c07017900340311030a0824540140428900000e0111041c0d100060352980800011401f0140041040000e0182c89104840d04c040000301e210300f0544c0f091050501d00389007810111030a005450b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 98611151 1250 98609901 98609923
    0x19110d0f02160204020f070f060605040509030a080c090406030f030e0102070603060311040c030b03030705070e010504050103031b14030f130b190f0e100e101d0411040509010e09 78
    0x503004010902d400714541c0b00c100e041d641c04480050f40c070207144601c2c07a0984910a0000c00440481c1e4440f0180042d551004044036000d60303060203603903603400c8001d45900c21038542e10086402c0c240800d0303100041d2000781100c030b41c000e000015119104d845000c40a00280411800201416994869564180038190040c501410b09001d018110741c0d1300c02c00e155410036054000c40d078809003004001c2c03081e000048080b00c050140c994464031800e10580354020f0340100b0086210348400003425040a03c41c0c3c40c102d982680e262036006040c550300d002d6020141405640300b045800311241003000070b00003400e00003050700419a80ea0f04018011502c0184d5901024400c0402d01071103e9859510514074480b00240c601103403260350781602035070800c44038014140c100308100f1044e5403280c0c100d400e03000d09480c1121030f03000c0500340c50300c00c842c9510f00c420b607440f28403406211245182030540207040c1010001c0602c80c02c00d0b44420128280351000d0303000c07040e0b14200ba400d204000c442802500044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 98612401 1250 98611151 98611181
    0x50102130b030721060e010810060b161b0b130f090c0e01080403031104090b03010506030703030f110a0614011a030106080112060209030f030d060503060405100519110d 74
    0x10316240c1d81c05004e0250342928114030190721202e9034004070340f40d80040d0107451800c00251a41d40c648110716030b01d580c4404000b03282441c06101080094980d400c0e90900000750301c01c018502e41603076820381e444d04560b8400d030441040c82c00c080b40c4814110050304031004811a0104002d00e8524640303d00c05041d07000820441c50415220042030340414003500c206405e090918058845150807401409804070002d6114404500410032032441d80014400ca0f10407002400306440c3c820406440d0340075844000c01180c0340b203141801e400c4c004c5030f035000500b012070240c030001b0503940c45250680b0440342c48486851040300043c0070030f00c2da42c2a2412011070007219542151306201c0f01502140040c0200450f400070384440804001003070b0121081c2c160041c06980305c508503558140d84d41c0e0000c10903222182c2c10080d0105032030800042e07051003590050000d103101c0c401c400c440c0c402450050a00300c0e100354060b210440c0c8181c0c41c042c9100c0c8040d1000b0443d52410000404000c039540c20051000c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 98613651 1250 98612401 98612407
    0x5060711011a030a121e020109030905092809020a080715050a0509010503060409150603060b03030711060f070203060702030703020714060306100207080d1101110301080a030f031404050102130b 85
    0xc00d8500040070748040c0d17030010041c0540d00d001001980c5040e0009a24240184207410954100f507040d04102000ca1194071042c40d125212030400078141811104e003040700403401c0004001040c4001c0c80080302c12130320400110b1000f40d8000c02e4803821681c0100d941e0303070300c004010800105510401c07030700003c59240403401d00c1c9505000414500c00c400c1031604208000c80480d0b810f070303038170b60106468541c05035010200e50fa540361850b014103164802603c6c002d140080883d018180441101c0401e80c0c801d06441100316a40e04000c03da82000190714000107041c0070040040e10100915400340300103800442c0c4400d05403030024a005001d0304211048090362144c05050745540042e6034201e01c0c103c50300c884500014100701d20340301d40355100240364880d48072030203055030f0010098000b24201500a000c0300400c1c07140141d8500c801c0c46100102c0e40030029031800300e840341e8034182d031402e868900070030001c07010039000b18043d0f01600c00350303030036540000c04009140800e404440100408260541 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 98614901 1250 98613651 98613701
    0xb0901090302070e040203071d07020c030705010f0c0611030c040806090c0a170f160302011206030b0f0a0b03060f060f180a020f04120602120f040803130501090506071101 75
    0x1488000d18031680d280884c0100100d011942c0034005440a400d41000b20b4101c0c0d00b16859400c1d60682c10b848081c09401307400461022810042210350607120182c46520030310901c02e00403603e000301c0c080c041d00c960380d8580c08043e1a9421500070341c055820301c041261514140780d03186003031240c06131031882140e200d942046210f48961500b501260b06524054582240c1000404e00303180890b1201556030241c104803008000c880010300098030300070790345e0588580c4070448020403105a8000a0000000c400000c0d520350241c5409a5112440e101c0c04170303c034017515000c00e00c1d042003030340c0758a655440002041624148903400901100c3c0844200c10104072101000d91041405000000929000210384140352801c1c0e00701d5000b80401e01109074076030854100b22009401042c2c007040c02010040c04580c404008001d400e0049412050480c6991100280e00c2048d0108a4080f2015500c405662001c40c0c4144012031055215845e9005029034a5003d03500b116110130004c90758a80303888110b8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 98616151 1250 98614901 98614903
    0xc02030709020304060b030706020f070801020408150408040b04090c120504020d1403091f08010e0c09010c020a08030a2a170a030b030d0c03020115061b021909090b0901090302 77
    0x5801c44a251a00503a40e071220f003400405022102005601071180c001d002031400d81c000b40c1006400b052005440c440750311118050b00781c2c407952081101c01d80c0105100c0120440300440540c0281c891075626140ca0707aa6030b500111a04213502c1864030f50340d9511b9010a0a411814035208408041800c2050f0728055001500c3c141e01d03084050034100d0040303940b4460010800403030740c5415005082481c0d0103900242040010b41211384c03180001c840303000004100b00790302c01090180003240c48240c14041940011926843c40400c02c0e6400714417201c00080c0c986091000701300d41805a07894242040c0f51142408503800340c4100300c456000c2203070412002c111202c801c1038040486c0e28441b0703910400d1800484c0a0440c5a42840d4140500f5025000f059000f00c2400c0c08507100b41c000340680c04000c5a41c2c120007200b07104107404100e05800748801800503200d01880e55100a040e0050840c040c0c525202d0081d440d00180f150642e255140d034248148402c0e040da001d0116070003400340d082e542e0340007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 98617401 1250 98616151 98616163
    0xc0d0c0c032705040f0e010b060a1e1701090b0f0604140607050a050d020a06050601140304080307030f18110604240e13020301090506090621030c010908070309060c0203 74
    0x20b07200d0503810b0005042e504608001c00c018900104240100e8000300107031002040071000500581d8a41410710440d81040e40030b559645100703451f00380c106282e440c107141c601d020050402c81008465a42003147c0480181c07650b001e4062048002103800d1041706000707513004515101031041d00140401c2040040421040c0d40186060321000d0b00c40d1158606180b801071004402031940c018403845022095001a852030140d020350030900503921020010f54042c075154040d40e8908404100040c0072540030402103800600070300c1c0002d13001d9840c4c203124040b00c21881e0304107240703403905140380d081c46000c000645200c1c03001c0344d90b02e203450b150046001e10124a42c0982100002883c4c140301c03094014000380040b8035015010402e040c5580c605c41c002907209000d42e410641c60400811001d0500c0b22250388a0310300500110380901e01c2c0400400310080c102d56a0280344400c0001026015013801400c41d42881000d00d05d80341c900901c1c0213001d90b11aa08068204034100e045500540d0f00041c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 98618651 1250 98617401 98617427
    0x110105010e1303090b0c06100911041403190c0501030c0201050108030405011413030c051c0209040605090a140102031515040504020d24240c1403120c0d0c0c03 70
    0x8582d0941c0d100d0b00e8240c0d03400f6495405402202c1012801a52200c00401c2d640d00c540445035000440a442c2c04d0300f00100d8104070184500740c001880b0611450300362500c17480c0441c0004003110004818029045030040301c0540031691140c250703008114550701405030300035041d22400244025810718018540e2802140300d1030b0704104136401c0c6080034003080030840e001e03284241510203210791a820130541500452084a0180f21642d4091205800d0400100c60460340248140415103070340d190729018ac00d02600001c0580108042c2e640021f481038802e02075900c075000003580328640900c0c06600a46a00c0700240180082403c180410303841d0700c00ca070141c8604440050b1902039010b40003008010050a040039540003540c0249640e07244410300040f00c009160194040e005038031080b850350020301019000c0703815000d40f000042c0003100d100c100080d001c01228101124007652008158040d113a041115000207031101c05205c00d0301a44d28020600c1c240783e40c0391b904681d0010211490144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 98619901 1250 98618651 98618671
    0xe010206060913080a0503060102150f04170c0106080a02040e070503070b0d060b0406020a0c0b161509050d05040305010507080106090311011112090102191110110706030903110105010e 81
    0x100880c0c078000b100380405030040c4c00143c88201411014045600544405016100746070380380900c442c000040500c00e0271840410540c3da20345030fa03101456901d4481400f4006000d201d1461160001d114400003800050010604400c11780103206c21604400b1403502c868000035014083d036100007800310700707d03282140841d580d014902800b400038825a0000c031021710002070000360b00355000542106d1540034000843d81b0f10b40e100048040c40c800d102820744c2e80c0144905039008624a5840740b000741c00112400b1843c0c0e00c056681c0b84c14a0516a000b20210300b0116080c0140700091081c541c1c003200b142080b03049541003074405444440c044c40002d0041d4601c0c5190002a4840c403201c1d10b40080c1901203814030090380c000c5050f2908404c54542c010b02c598000c0e011030058422811150681200314006682d103580c083c001903051016646042c0194103440381091079080008000512440e500018180c0240c903000300408800d605241d116814040140f02c20010300c020300d41c0007203d82d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 98621151 1250 98619901 98619919
    0x30201050702011115040b0906090705011d120102030a0e07080c060702040504020f0a03081c02130b130b070b07030b0f0315090a0b0c030615040303081b070204020a031a010e01020606 80
    0x130360519000444080d04180c50498040c0300400002c0641d460084d60b91009450683d41d034410001d590740894032070300d030004840e15410401c005115401c0e01b0032100251000e103401c0501010103003641d005a890b240d61699035101a22038110a10100014108090282c21610001400035604e8001c00320040c2c81159182c010034110358030103114000c0c1c194003618507650b41d0f40d241403003186604110311074200464040d40c5800d41c24018402c4807201024615400705483c1001c105103440e4201034140041c2d00c0d804980400e404504402401c81c00e441100c00c5841c0d031134420707002000e075146d4000260203004803000001c00c607600460310b213084c0c101200d5100d402e230360b5071200c680c03800c0b040c00806000c1351102d00502c840505258004c51283e54190303468070b424860b5101141c480d1140388000b50018095a0204104007091180c88180304560f8002da418048541c00040c1281e1007054041d021a680c0e000c0346819102005074280300000900b01031101c5240c8400107502d4030b1700205414030501c155 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 98622401 1250 98621151 98621177
    0x405060a0b0d02030613030315050604032003070807030204060501090608160905100302070203010b01050415030e010f0608030d05070905060a0e041512030e0d0c0e040c051221030103020105070201 86
    0x1840c80750815a00101150006d00341003070380a681c2c0c02c4821007900040d0802c44201c0c03200507038600d03074000c6a4020b081240340514503154007803400011038040a1416001d500208545d4080065802038440c2101800200d403440c81000f040b100700e98801414491b107900108443c40d04100c1042d44a452044a03201803142d6890845045005030400b80c0d01440100024140560540c0a880d10620950080240d61900d4004bd5014000c0d0300c9a45000c040e0100e0900c030091094214401c008041000807500200e002c07680410f0b10781030740007400e8540c004596410301810a006840c0c0294080c1401c04000d1708010200360310384034406c1d4150901841601e0b0461030b4950b58011510400c0c40758040c600b03030782c41d5100d03865100c006400c01d5000500300b80f0302c0324841c0b80441000461540c0701c0965049189440610b2040f41d034010000d5901c40122440054151660342684084491450141103260300c02c00c110100c40d9203044a03800381c000244010301c0180d030001c044943c81502402c00140c01c2c080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 98623651 1250 98622401 98622409
    0x103110312030a09110a03120f02120313030f2109080f0d02130b0a1709030702090901050109060801091e140a081c051b0a020106090608030307020c0303030405060a0b 73
    0x1400c040084041d400070801c074900f00198040202c1510442ca03004550380b120040000484081c0006400905000701e0060550300030341d580b600400325030050703500c40322048400121079042229101200e00340c1c1803a0f202010362013074101c001e60125090980d1207103409040707407010034070031240e011003eaaa08400320500000805a4516041b07044030190344288861464020703400244044204410000b00407404a10010942d00c501e00c2c40c0e84c82c030b00c2910311103582110382c0401401d82199800b08111a401603110a10050701c1a450180013080704e51414408a080307030f4046d4050300720782c2d00d8074a2030303800070300104210000e08107401e0350311300341086506010310940709500c0e40ea0160b2280401c1c280420107008041c11114070114401e031440030220700c088050301d104960700e83e514408060340054802c1450b018103203026483c800010415200d108031411581e0a4001c0b4600358800f004103d03c4035170400c4262254482034003d5811410140c0e40d15544000c041d140b8007070320303407a000d42c0021034031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 98624901 1250 98623651 98623663
    0x11060a021203040c09060b0a0e040c03020403201504060804080a20060604150b070f03050d090b01140301110d050702010902060403110406090b0f0904020d0501060b0d0501080c01050301031103 84
    0x9030200000d03980f4103083c0b1300124140710038840c190000e41000800a03045840d2001e649114500d40c58a49518070244100030040944020503c141942880b022010400003104031a12120302e461082100c0214410402d45151600840c004104200070501c20a588101016002039100c8203031074a0b8014820103452500c0d1615003407900700d6000031810007480d00060414065103058400b084484062030103800c00320b28a014120702d014042189000052520b0503400881c1d0003854801c2c10282042099015110914803e43c3c1d9411100014020f00c42040110348110340218000c0050f00e20451000710386025064024a0090340d840000e00d50500030b42003a0502580107214a07910b50700e900d002c030224005050840d0241d4a4044041848100d0744540c10b00400d000f0186e40e071546114041080800c8000e104070703000501c201040700024000d0240d00d0191107084552600e9170358400d000002c80c0e40503841b5072a40e82c03080c14011036907600802140e041d250411440c01c84031000b00d0101e4a401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 98626151 1250 98624901 98624923
    0x2040e031309060608041205070303110f250b04021002100219030c0306080c0409020f090f0106020607091412030712022a031005100b0408060708090a11060a02 70
    0x8040021091100e408208180040d07425405041044640300c80b41150381381801c82c0c6c01005031401c840480c80c0c5078040d0000d006294403e1801207600303d20071500907042c4c1c210498400c411000801c042001e01c091580d0b29590040b900100b208a00058a601c184100040c00180c0600410003203000c086200f4003035607042080b510015541c580b0000c64503003500130103e0361030000a20f00701d50042c07060710a0103480d00700c50040c0018040a8001401c00000303044d4800700b00ea00c2115001c4485803512043c0c5114403c26208541242640c5022000333410102c00604100c208080100140000c41a5000003c10210141c5250f0024140340348564554819541c0c06410b241c2565007070070715281d000880890440c0a220880c16004032000d550304c1d130b91000c4210551541007e00d0031645405180d00c1240c0c060340303c28101003c0c5603a0404002d103540240c11802458020500700141c83c0d4006d044590003002c0c0342c00903d8020000d8031140d10000700b03000070505c01c2c000000c046008a20800c6450703210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 98627401 1250 98626151 98626153
    0x40b04090f080a0512040b0402040c0507020108010306020f0c0709061d09060411041805010608070504060f050607060b131a220e25050a0e0603060a0e03070f060b090a020306061602040e 81
    0x179041c5801c02104880d0115012417185061807400c81d9020300c1507081d0b03100b0f2641a142e0004d02d0342965140f20194129150b0392304a981c090041c0d0b40310791002c10420303005110400b030024840341024005590300b1641c54134a81d4800710340003481003000001416541c00b0b0380018520328845070f00070014000e000316603803042c01c164242c0b1000c0107002044d131003901250031140c1255070107a17940062100782c80b90340c0b0503003450003d80c800400080c2808401001d03280d02c035440c006000030541002614500d910540c21140310758070051001201c01c00601c185056108480e14444516000844540c0741d011305204a03038140c0760042c00c0360b2610100270900c03c4d4030040d0f40700300e4524410b000c650042c1c902445010704c92200d0100014401d258196014014000540a002e190341c4180d0310b200030f800390030110700491004010807000310b00e4404a182520348120301c00b04001d000a1b041000740c42015000c000c3d01d510400900c002942e40c04201c030104200e480c50500c44507040c0c00060001d002c5a40070390340b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 98628651 1250 98627401 98627437
    0x30c030803060a06020606010921060c020f0c01090b03070c021305091f06051516061a2119080913050601090e090601060507050f0a030e040b04090f080a05 68
    0x4000042024610460b001d5030800711040d95100102c0c1e446006441c214041905c0c0407050181c141c00500721440b8001d0041c28840c9003c82c1c1e0b443c01e080701d880420260050304446850119a0400c0c0607100003d402440d000040d1410004481200d01c8003400300418003980c003040c4000c5469000024034032110798070040000349448100c0c81e840d4007080c6e6020480c1c2007034000c25500081c051085900740c400c050301e11122180441050012544070141d140007a417920402c6800050884c0258444010052581d4003078900c09003e0101c5441c644003140070450050318030200300e82000420500410014900c0b5131242254100070705984a1000204d030001e4459883e0031000300300b80c021a007d00800e0f40c4003902c0b542e441484401402041ea150001a0001c0c401009810b11540282800d5401541650a0320901c41c080920f0704140040c2140803e03111148841180342ca03124180d0035010566040c08806c1c0d039551a00702e200c0c0d59139002401000301107418815540701d070007921507040325640c0b2810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 98629901 1250 98628651 98628653
    0x4140607020601090f09020d08310603050606580f0902040e07030215030c07080a110d020c10020106080a061a0306100315021c050417070f0b150a06030b0307030c03 72
    0xf0130740c44003400341cac2000c2c08091b100d0f1104d104080e0301d410444800d03a0900481d801d04108501804028100b41e600c01401c2c800d41e2201b14140d0034028031282014130314544000707100c40110050440310381c0c070350443c00110607003001440c00c42d2101e6103228503100c5c0000e02500700c083c488010512041c019411910b06101c00350140c0c0d0000f10501030301d00072142c180803c80d41040900c0380703100440b20b40c0d03c1c01c0802e12020000440300b00c0540034a40381c1e410008013603040d80803458070f0800020b01c4900164045600042c0904200c2e180342e080d040c0c0741c030080c44841c1c2002e0350360750740b0416070800600300b69880410944c12442070a0f0040c2001d0010140e900703c2c00e040b4001d0240310203501081d103440c4a014483e141c074418500c00c640d80c04803824a240c186541d00c4814030014080140240d5079100d05003900103010130600c00801d007180c8150131104181045003004940c0300ca005048110140c1c2000c4c100c000d0750748110780001140c42034600802c101d4000d0740802d0410485920080c004162814048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 98631151 1250 98629901 98629913
    0xd020406080a0f02041503020702010507060906050a0507031b0c050307050111031602030403030905010e040e06090d18030203120d0216030309060c090e1b07050f0604140607020601090f09020d 84
    0x94020380c8031000a02080350f0030b0f400c5600300d2145110f000c20020028040c0c004503130280d006031040d0f80c01410024203056a9440d040281c035001242260040d0340d9a04111311404184181034018005280400c405002c044045021588000ba03403c244003d81c0f80c400c00f044810812070798000d9101000b0b06c030504078003801c2e440070f41040d1001c2000c0300d040707410710f50194030001c15981180e4250f0741c0d0701c48142c5400700664115040201040d0000e072640302884d5540000c11080d401040712a000f0444c107054140024104c0b02d0004040d420041080b4040001da0ba002449100000344120032981e5040351484e0000284038115014a007428072061803024182c143e44100074060166a0601000c2c019003022640012140200d5202c0e052010104802e0703031559802a88108000440300d1420000751240e81c80c000c00100c00008e030f81d2090040008020007d0304105480b0001002031180d401c0550029403141d1050160b402800d54404440300c41850580081190b25005807022644040c942480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 98632401 1250 98631151 98631167
    0xe0d080705070303090b0a090501081f031b0906080709020903030c0a030203040f0905061302090111010213170a0f2603070f1d0102030405061e0c07030c1406120c0d020406 75
    0xa502082c41c020700002c03c01b11030800c03500162041d60303a540c04542000d0054403030b0040500102c041200002090501031600b0021402450141160642d003012104580158101c983c100b040303200c3c200041082411300010381c1c0303415108000d1000d6210440e100200340342d40910010800300340300f4050301c00c05050300440100b0590342e14480c0b51101c0c1e900d5010f000d00b0303544203661f0207811880301c0d01b040413544103a6000d84407104052400343c1c005540005ca01d42a078028005c2c02c3d9110440710010000700d2480703100d01001d41551400703040301e68a80d0b1104a00d4010075113014003a45442c18844640e502e0300140801050403851005450f07080840009000410717000d40500803a10030300d20400e1003841c0d4800d58010785030590055141900340421302200f41c01c5004294410f0030600d14403004043c2a078080c02c0300001c0e05004001a91840c203012049104030780c0903001c4010390450100194440c1400c4844c001394280311a00d203138585c5103840480f13125050008009520204004c600e04c0ea00c40701d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 98633651 1250 98632401 98632403
    0xe07030b07210c08180d080901150902030a06060309030c0b09150406021201171e01020d0203010312031a0904110127090e07120b0c07150603021e0303030105010e0d0807050703 77
    0x2d00101340d03280c0c8211002041002c5c14003803581c1c064050040d9551240700c40c0341d13010b0014000828900c4000d100303e03014081e0754200c502020780100170000101d20b0b80c80390a0041c441d40c03134140b10588194501910714414450083e224007080c5000801c1e020040140e810b203d10440c001a0f101e20705800d0002c0203400004075030760015448800014405103050303084500c0c42c0d100c4042e200007100028114240141711a02c0c4140c0e540a0000a80303040712440a90300841c0904280459140020070080448210201090002c054041d84044c5a150030808541c01070b0300031303a5254a54015401030721081d9058903107031881c98400740e01003501214841c1c0d101c00c4905040e000e001c03809243d100d854035200e290049034001040c1d000e81780e0101d0080c007401e40d041404103280e00d10300710032501c90038801c00e031000758010751540710300c030420441c1032014210300c8241902000400c0d1304051030000b5120310040c402c960402c0310b403000c8180380740e4403030000c9200145e00201e517aa541300b4618050341c41e5101448 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 98634901 1250 98633651 98633657
    0xd08040303031508060a09060e010c050309070801050115030c17040606140609030604020f2b3f021203090a0b090f1c050906030901060504050a0e07030b07210c 70
    0x1400d489030040c0c01c0040c0058541407000345c0640c0c0d8030203005100a02c02e1100c25625542c1302c0000b403d54100038801c07403902c2500c680d1029940c0c507042d08481d10f42401d640c801596a8581001080341d80c0241900a94901540c074011030201500c281c100e4403805202685030150700701905000801009500902c00c5607104420003008140f640100450b9010700090301d44c050708004002001481c00c000584e11701400200003854511521140d03c048013407040340012a1426217030541c0900480303180341048204000480e07042c2130308056510301d2080d101e07403074008000b01d08104100018001c0c4054400c2426203d0a19228039140300d4080c1d5410030000107070ba440000001140940c3c1002ca0b03800a44182d600040454410b03054103c2c0c908104001c1801c1040710031700480e08280d8503a0011400340602400110f01182000100002c50310064030031901d085c039000c9041188540890303090110303600040084141d6690000c1070324000201382101c00090a0709203240c81c2c259096001c0c4e044980706507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 98636151 1250 98634901 98634911
    0x40320010f05040b090603060a151205010f0302010c14120d0b0901151d01021c030b04051006140903030904060807080105010902070b0c1b0105090a0510091707110d0804030303 77
    0x8042910b4a01c100e0040f141110410013200c802e5041c900011600558054403200880e9900c1d02c1c00300f01c000220040c0c8001501d40c5840f0341d4001503500800b0b025107003600d81095103601d5680080c08582d060700009052182980742022101030500c0003403400e9180803802ca64401c088280d56000308010301c40c030703072280315280004120021850b01040c85c984007500c030044a0450500440e40305400203c0d0941107201d40308030405454034407035202d072001345242c80101e104030039202080141e0b80c5c001c2c124114800c640d170302000a80d51010b000b1802c030a9042030380d030b03a60710f030074001c00d0840c41581500f64001d424007800083d50503000032528111150791000300101e90301c1d01c84030826803003040d02c041c014941140c04240d0707014000c0014000c100700034040d00801030120511500b5648229020040c40d002441040d051200c02d01c030960200c07515400400034181d03181d031130a40440208142502402e00480c01808104503000d043c184007038014030628000c3c41c14503200b0700711742c000d000480000e4100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 98637401 1250 98636151 98636177
    0x904090f02041d0616141318050406050a090312020a030e1606020f01050610030507050d050c04061407020a03030e01050f0309010b04060b13060302030613090b07020d0503040b150604032001 83
    0x2003805c910583e02d2030761805a1942c805004941641140350303880b507001d1086000041c0c15001045011a0b452060f8002c141480d050820800b203d100910103180581009034900c0080c0d07201c0403001300180a0000141c444500c040114010b08e803e03803116456104440100e841810b9000c401c0c81182c140d43e00b104c6680301400c1c4040d01fa00c0041e40c6030354000c4440c2410090350381c007d030032184c0d0101044c40c2580c102080d80d94410140c83c41903c0741c0030039100c0040c0510100d540654480c40c03c0b03c2c4940018600380990780882c0490001c1d10000c2e0802003801c0600015a100d507041300d080f05007140d001900c070308186100358020908000d041c0d00c40ca1800c50000782182d00030059030154500004061103031b5241520a401030340c001844280e003c64145200718201480c0d04c10548268002d03120054585049100a8070b0940080b68207402d1110620400c000940c01c080102e9020508010303107600d500c00000030030b8481c01103400c000c241100307040c8031584800051110401400090f030725000700c0110707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 98638651 1250 98637401 98637421
    0x9010501050d030509060a2115060905060409020c030403080f0a02061602062a040e01030b0f04020901060309051e0a0c0b03010f0509060d1b03260904090f02041d06 72
    0x107034030000b00401c80c2849505c4062034507801901d1540300b54109002000030795614400c10f25000070780f54910b5a80c48101c0228064a0a001c001030075850a0060820b400c0c980040c40340e00a80c0309006480e078000660b10322160f0203105450082d80d0008629441d102011490b10054010940400051251000049460303d0f4001607440e60f00e00344d0003510321501e5003090302da00780007619404517403d020301c031002010464001c020002042e4114104034594190310b0040c013a10000380c000c2213011011010b00015944071030482d81124558240001d2800e880c0c45c2407400d28850040c48840040400e400b002401c50105400a1a07442150209455a03e400940955000a0040031079280c0c940318280042d0820440716034000300014084181c600c8540d807200d1210304210004c00341004840303420004c0110b142c0c00e2255000886400c1140c1e034030015041d00c0130340103070704841d40300c0c0ea00c9030311100500401c510f6000c1002e4003c0e0007446185101c0207010a45445400d0750040c41c40307048001441600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 98639901 1250 98638651 98638669
    0x4180c030504200307150c060e031e03040f02060301140102010b0d05060126010c0302040f17060606030415050106051c060807050907110f100f1a01110a0501060e0901050105 76
    0x588010480c45815050b01100e00380c940903c8a55054881c0303807000704014640c2c510081120000e5518500a285030740346c4a01901d0400c40f41c041541d009000d41200c0c5190608084c19400080c101c207510391350389050400381002e80c504040d40124002001103841c95201101c0c0c0d242034020380007400f42050060500c00a0f62060a025150b900b080c001480016078101e0083d0400f42280e591565900c8080b41580c04c5130750380b1444202203540001c1c00c003c032009120302400244003c1c51061000c3e107030f6081c2c490700d580d0002c0496104010004c0018208900141001d01c020f200c82401c02183d0f8540b01b000e4481e610051100c0072604082c0903110a19440b402080187c8500c00050401c880c60041400886840074180000748030036180a90f02100c070400c0048034a80851004000310005a64032404682d2061092007001e41401e040d1a010740e228241000e0070341c801e203442c040c41031a0410300c60400c81e000c10010025428600c2c00149034001c14946409a10b00300d0082005903615820008090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 98641151 1250 98639901 98639903
    0x512060108100308030a0603020405130317101e030f0b010e0c210601020118060b0f0907020d1107080f0115050913030f051303050f070b040b04031401090804180c030504 74
    0x42c2d06200c00d00001e020900503503000212410007290a540329400642a074508454a0440c1d0050352070703841c103241e480191181c900c6070030001c03047d107810000708040b42070b221030188210510a001c1c0f541c59844034520380700c0040d43c02070303150300c01444586003010000341c0c00e1140c2c80805030350b000031504039070329034003121840721501601c880c1981e100302154150f81801090700d41555a03a12130718141c040f004109030443da04c901300000d0b02c156520b0810118503201074602e07020301841c60401003119000158101091024200f00282e0f403d1140b542d860000d1781e42110342d030760044403c42403804005420001c0c2c101035015242d03000c10380320420310180c01400c80302200e00d0a41c0c042480080707070041c2090020400146400340c07030301c4e00384014640c8048081e80112281d0380050b05070340040340c5c140071f190060142c800010349404c1c0761409401d03060143e030002600c4104112030505231204258044000d095211100139180d84d034450500c080f00103908510340c0e43c603083c00c04d40000d0314842e01c40c091240d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 98642401 1250 98641151 98641171
    0x31b0c0f090405070b0f0d0501080a0b0f150a06030209040612021c080705060403110609061b090607050601080105100603050403140c150c0d151410020712030512060108 74
    0x445400300410005a401030400d644078026540e0101d0020a400000e1180c2800090040c2d42e40c118180b4110486070f05901c020066080002c00d41c1c0054400d9440542040041200103034a072202c42c440c1600c10a40340515a1000b98507200050094260b0041c0180b030b0380843e01040600d41e0b41d403260060b0384000c080294010382400e40021102d8264044c0461741d8010812141801096a03030380d882c007403094030f00b640407980c00041800d01c02405c016040d4010705100281c003550400c12042a80385210320b5050a62a20200b651001c80d10b6400a544942e03030000e0495210307503034034011180244800d40ea000d4520007000804941240240105c40c021540351f82c40d8100204c1b40f14a900c640d40002c141001d03507006694050f00903510084241e40541d4031404056520840c0c0441c142c00c68504001c000d00041c54100f040000d080481e405100301c03541a038a4a1691454480032800c20b00c0c140c100c40a241ea500060406140d400b0000c1c00040300a95244d04c844d448040054130310110071505682c41e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 98643651 1250 98642401 98642419
    0x40b1915060912020603160c080a030504061118060c1f05150d0b0c0d06050d03120f09020609090903040806011502061509060f030102042c070819020723031b0c 70
    0xc8042c0701e640691f0280340301e241022190240341c0d80d8480701d5000855410020740c9031002e200600c00300d88143c07810401d040c1c01d200e14201501c0354090b18035001b41c2c5060b03c11a400302d001642d050041c004600d1170b9842004141c90317080a2a080c0000b0401034a1600d8110918521000d40d800d0030502c9582c0250480c0c400084e03a981c582c1c444d151740c2d01640c40540c2c09504d40034006090b0300c030040c8900e244d46c400d0f120801000907140707032181100e03040c4441400c010708206d20700000d6110f4008a912100e81550070400c0345c4d1350060f8541c6144202d03801780305107228020000030702408040e080385207185141d003550240d0322240350b0743d21020059085a0351015445020034000d1601c92683c45440c013020700003609240d61803060000ca0484140e101d04020503001c0d185e8203500c00f01000c1a8050501d00b40f80d130050078601030400b0b0302c3c0b541c00c000c00301c0640c1c0010004140140c241055185100760409001d0429034203010329229003000d110240c10303040700c250405031a900850400c64810001d044d180e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 98644901 1250 98643651 98643661
    0x906041d060f01120b0a030b04030809160b1e04051909140106170405120307020106030204060b0309060705030406291002010504020f06071106040b040501170609040b1915060912020603 81
    0x205103107005c1650080c01700c0000000105d0241407581310b94045e8807425800d01c2c00c04000c0b41801c0140d4102400d008285800303001c10755241017601e10303584c40400e1064601064484c80300091041d0381100c1c0c0c2c4042d0344d140500034400c030140c2903016281c0070344040c80340108645c2c111211032030a024240100d003480c415001a0035840d4240c0d54054015000c4032545440181c1c2076915034070039554000144d468110600640c205405140c0080840c5107050303140d442c0c4801d1254035800c02401700b030208040080403d05111681c1c100d4522800364040b458240100305815048100540307280c14040c1e80c0180a40f680c01c1e0041c41164030540c0c024105e40e0354004003004100c1e0503032141d041119041c0c0003110404147d100e000c09400586106291035079107904000000d080700c088410000d83c94490442040410744440c0241c640050b4010761004241c0c40b50140710690300b07070204511403114501400d05281b81020341000040b00c01d103407600823a81e61200103e62041d0084180650454010000f0079 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 98646151 1250 98644901 98644937
    0x9032506080c1902070501090b03100b030405120a080402040501080a0c140103020c010501080a210e0121090c0e0903071119030c0801090b060108010602100b03030906041d060f01 78
    0x19400b0a04181c220b1409090707240d503921a0383c0070520b080c01a0711103d03040c01703d541c00c131441a000d002c142110a00310314000820030010117142c004c3c15403c500120100b01041070410480c0001030290b1601c0b92a148007000080206504031400c2e8855030500c40001808d8001285c070344004c6800203080841c8604040d06c4e03000540d19217140c181055801c004900512900380f040c81c1c060039000010b80b116007454186901000c0074081201c200d43c000340030000d903103900107007107820390302c0c003820410100480303894a1300e000010080700c10682d5080c94090f00401059900c9142620311030f058481254035100c101c1d5540e030081510050a4544503004050a443d001c010400700c0b00a81c0f0700c05880c00e81781d644131322424440f540101c3e01c40e91145285001c100e01c491545600807401c0ca48003c07190f00d4a0f10080d507858010082c07501280c0d032808944d00d04c0c2c4060044031041e02014200c1070361941d9072005240300c1480310103110f26403180700c0080f40191500a40e4444070060503502c8104050350b03510a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 98647401 1250 98646151 98646167
    0x3060402010309031206060306080c031501030b0a060b0406030e120a0504030303111e0309010c0f090b280c0323071403040806070c050d08010e010b09040908040b09032506 75
    0x540902c0001c00342d000311744500e4003600b005407105660104681d0301d40b120080c901400b10b40124483e80103003051783c041100312040d01e41125000307034600c202510780c0780c0a20010107440d0001b810080c00014081122501500b01c2c103003c2841c2c408461014099030702401d4903004080c8440e0020318108030804c00b1038130030340002000e5070f43d400c501c2d45444401e580b0768160f0040e801d0340f19140c0c040441000706250b028171a0303e00c0340d042030034001d0488003995002402e00286000d103034807152010440424561000f45141502682c1080c0020b110f06103000181408549940c203c00040c0004602e840c0940e0160304440c4028522501d1820f0842554805c0c644001018059180d44001d020016040c042008a07a0103030f1419200e00c803074900c0508005050090304c1d40300d64244403001e0010040d000b080b000381c0b411200103580050311810b002000902134401340c040580600000301c0c0c04034942c4440c000403c00c101d411070413a601500000702030a030f44030b21200111030904042070200915401074101c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 98648651 1250 98647401 98647403
    0x301060c021909051b030105010503010e07120c02030409060f0f050d03110601030812070f14091203040305010f0b03210a0c02040203150103060501020f030403170c030309160b0903060402010309 85
    0x40c03a4018802d01c44401281d0115a000700021034681c414809010340c0998107400150000c400d80385550304040010702584010710507441109010000241014490103200c14503005d401401d100c9100010b000039030380d07042801540a901d180820001d001e00c0c6000010003121800105802c1281c40d140c00c03c51420000c1e8000e0b4103100baa00b103051203118050000d14040c506c6281200c0c6c0703070f00c0403866a29110400a001000784002005010702290b000032003d807070003584010311aa01c00d02d18010400380c4001c03540e0601c09110120700032080107010b40002800b82c401c80e03001c0007880001c1e4200741d698840c031004003000e203528903c80552070361a007006102e0030340c150410003007650256012808982c406c49000b8502400104031070410360f80f500584000b06400d10040a4448540002e1a00c0e48030b41d220091401c02d00d1f2101c1200400c20304187c40c0e81c030324100113890b16803070f210001603195401e6110540f408075a042d03000c0380d09034506c010b64084000c00350080901c2c4ea00d540c0154000c0100d044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 98649901 1250 98648651 98648659
    0x7030b0405010914060103050d0c02031b0a18320c0a0201180f030908010203010b090d0606030b0c040311010c080415020a0203071710020f120403030b0301060e070809060108030301060c02 82
    0x40c50000c04c5800d01e500c52020005001001d256146041c09800c0c0b5503d003c0f51010003110034440d0700982e07400070b01300c2c556010020301120010001c00c0010a4000c15501c070301302c0c54140600c0c684000714a6404244007942002c446e050301103a03001d5107255120180000a0364000c003001044407400e000c4090800880d607400000785800003a520100181c2c884041150300c507000400c544205039228210344e0007840c4030b10003582194148034400e10a4051580d0050080181c41148414000540c201c40000c1d42c00045a240314102110b182030349a0250206840c2681100c801c0142035114482000c04140c00c084800e0415041681c00b00c0f402c030310080b4207003c51003007004400150b0b401740041e00040c134003222800c0b94080396074003040c1404c4588102014591060124401240e0040c0454280f8a59990841215659458140c00030000520703032582540c80d24801088507401c0183e1503029003465142c0100583e240c00380180e4035602406291629041030004006040c000d03500c1180c101d01c014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 98651151 1250 98649901 98649911
    0x903151807030f02011701140114070c0f03050714091501020f07090f0f02070c03060203040f0b010305030a0e0402130504050c04030b0901060918032f060a05070e0109050307030b040501 81
    0x10507181c020300b504150b03100c0030341101c00801c40d0b8000204588401c401d580b5070aa540c94a010a01c1c4048900300c9241440f8801d441514601c10240448040e0f40c1d00c00d070040c022a46405a1400c40318a90004a03154461440301007580d8034101d5440340914001484159240d40d074448500b03035805005005815445003101c4100d480b00f0501409000d041c4500c00019203840030225002618508024540401e104100c40404941a8584202500d4002138007607500d071a1841e281642c1e5140f44800392206120900100070000003000034000100f150751142500d103440002c0004a00c42d2100d103401d5001e45080400c031a00b0690403040c1c2c00811440050300345641c0303844280d80c40358200e80c0c10b075007a599034005020020315072140315146d1524445d08805c00d40d00350380142030040c840100e40c02c05c00700b452030582c281c400740c030034420000c041d041039030b4803414541924801303003c00341c4204020401c01d00c00c0e20804e500c03500380e100031110700600030300d0341c10301d1601c0741e811b40d40c0042e2094035503540360 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 98652401 1250 98651151 98651191
    0x6060d0f0b04061505120c04020a091502070e0c2107110307140601060e0d0b06060405040609090501200403030323010e010e010b0f090402090102010608070909020103050903090315 79
    0x207010300c61049004200218150074045000d5681a1540c0c110328422511122140030711600042c092070382910039900140d0320305561b00161060b40103540008548490516240d91182d80800c01908440c4108051111134903601d002002c540949540b503540042010205001c0c000e60a40307468200e01c031070610407401451400420300b55800914180c2e0140d030342d01490492520300300310b42c0b03004051a140885460b101000007400c00f54144102038034010101000c100b240c1e454208960003442c0040c001c21480340e0780c0244030054030509406a69a501c2d02c0c800c034001a4003066802e04000c1800030142c5010700315a4260000e101d04621662014030002518641080b02c4040340d010b82005c1a4465080d85000400d042c0e00f03205804c41f00c04030006001e520761700c903c15015110b242d04101c80242c1c82d24a1000103c1c0100034540c042c84407407250b040f00041d416070310340c081c00a060007039030240056903401c90550750741d101e203105c400d406601c04a176510806955141d415044203c11414420013269 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 98653651 1250 98652401 98652413
    0x228120617190503160c05101205070c030207060f0e0405090609070b0a0c0320060103031e030902060304020913060c05030a0e0a0209010b0a02010908040f050301060803030906060d0f 80
    0x140d4101003650a0803000a600c480030420000d10750402c0188124070780c0d90b1650f9400d803213000d21a0b803d250100786164080c1000100c000c0d50024003006840060700d0020a46d000303004003080104462282e00d0078001c150310501c81d90a4007030442d00354008011107071800e01c00b2600288044101c10170014980540a0290341da802082e01030074013500281441d003000030740b103801c0c042c0d143c0c850f4013030344c9040004107983d40d00140e0300c040e542d40609042d06400e201130400c1d0380502801c601c030410307401080004801c05801c00840082d510300da0710800c16800d60400203400302d070108070011b58000000e000090061030008103280e44007040c64a921001d03001c0e91b440405840c2c0720300704035000c1080070040100c03852075440b5441444007214000c1041c080b240d00030070312040040c00b030195a40000142c4100d054001d4005c10340d91940541c989540310ba6500324041c0f0b01000780101c078803e5090480c000384d6500e000003a6401101190041d040585884c4100000380111010440d414180103164601080b8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 98654901 1250 98653651 98653661
    0x2a0607081902091e010305010b04030c05061c0c0201050403020601080a0b01032012030a020c04020306060a0e0f1009030506060102060705030f04051504030c02090a1a040e1c020f0d0201022812 84
    0x82840032039900c20b513201c0000d020340f4030581003c40404014881080400c1d4101c900a089800c01d4801c603942d48041581d84a154204141c0e1804042c10a42401109a41540680d1040c2e019a0030750f0000d90720340001e9501e4250b5940094030344a04600144081416040032182c04014480f0211401018801054454000f44800300d03050b0808100f2024040d014880d540c04110100d40131861850b10800045003405141c80040030040c04c64400711b155160074007032094120004050320f40196000d80b00074040d8a10b40421a9540144400308115500004045024003e0703603c82c5070030b640c1c440c00140c41d5140018000d881512844540703c0212011600f9540124002e41d81e06211420038018803402c0c2501414081c40c00b4900322001c01440c060001c4401007040486002c50400314004195142250741c00366089140340300c9000b01c580e5500010010441e10725a4180c6e800c098506c81c06900300d00414014089212a011940c60901c0301c0240751141c078200c5041c0071060204018054085031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 98656151 1250 98654901 98654929
    0xc060c0f0703030228170307090302120327091b2109010c020705013507020d110105060d111305240603160305060a08032a060708190209 60
    0x600480c1100810100c85d464102480c282001d0702c2d40700360040da6800d004200003141400c28404040023003000288201c90b00c1005540050150340c0c040c0603144401e813664032030f003496880a02d51800462a80003800c0d01c08103c043d0062880070a41c0c1da00380441270b4003a90301002c1144100030040c0ca00d03a44c0f0071007000070b20b195083c800154140b80c803011003800c40d10401c001c5e40c2554042c410820081e81d01400c5115000c107080c951030b0351804e0034400104c02c0c1444036500007525030200b082044050380020101c070249003507a5501c800428000703160703003200c4080c0e034140d0f04002c4240410000c507030100750164102501a00541c13681d801a000801203c4091f20480740240c1c0b400c5038041403104641e154048100308642c01031441c00c045265101070050101c0383e074103041c0c8510000c2c8940c0c0c0c03101008002004904103595640c8000b004c000048108640400c036010101c0c0700300b038075480300080c190b4842c40041d291b10819071250303000041003450307a00f8005c0005800300036048450f01c9190b8144100cdd = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 98657401 1250 98656151 98656153
    0x120e07210f061802150c0616110106171e120f0d050a0506030c1e0904030e130c031103090d0806030c030a0803040210030b01080a0c0909050c030402030c040b030c060c0f07030302 78
    0x12481d0f43c810005010854070600b140c40400b4440010b035500040340e0700d5089000090700071400d8440c3d100c10703501400d04900724070595190410001d00302c407a07074540100b4095460140e801c04040304079400310720005e868003d052584450070800c80014404000c00a41828403c0c080c1403401d01015001035404c100c40e0048016110410300025080c20040e40d070b1010421520000c0003811b010751020141030740c0044074400c2c1c1c83d00300810189405854500e400a0003c0c000e06c1d00310300d00b218110090300c001d14544c00001d2030500c80711000d2103110160fa0155000201803e03c85200c402c080ba004031000d09055454024502c1610741c0360b40400041c4140c07403003241d103942c0383e141600400002c0c1281200302405d05042608903540c585e4008802a8000ca2140c000034811800a2013180c0c002d145401400c0c61502d000d080c4a41c800c42c6d82d024601c0790f80300b20121030204200009203c19240d13000040f40d0541e001d40c0d0722590324a0840c0103010f010ae42d000469880300d101e42101850300fa81c980c001d07409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 98658651 1250 98657401 98657441
    0x50114010b180108060a030b0f0108070b0f0a23030a0b0117090a02010f030f020f07060f140117030c101d070b04050409030e090106120e07210f06 64
    0x1806199844450060a090000d0782c105044501e607000300c00d41c081002410040318800003100c03690f485c0080009150000449904da181c00c4002d8121400203020b110303c14842c11400155010159088441014500350100d051180403071f0141c9032451900c86041c981c2e10101c9108800704903c001951043c0c041180100704075a500001604c007903111656071502070b540c0c03001c10210846c0003800da022f240e030a107800d40c02865500412070080401c20301e00608540000341040e00f40a0a00207005003174010380d0104020030009011004031421900c91104443c80754004014034002d50003500070000a00042e80e00d0b1a010740c1580341091074502150003059550491940c11805000c805c1f880a01400d0050900600702480a1380368043d9100c3c040c86a900c134512401014801d0020681c0b035100a014070b061540c4982e0050710a251f01040702c0b2406181200821045c1d10024104084881d4800ca800042c0c0007081415107500c1c042c0342c180c1c0d81291a070220000203184d407090048444d0000c2152031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 98659901 1250 98658651 98658671
    0x20721020316090c0c020901050603190903090501090b07050d14120108030a030501050d080711060405030610060210020a090911040308030717010603021903090302071701061802040807062a0501 85
    0x3084950481306541001100c01300c140050b1079201d02141990030480c1c4003901e0356551346503150f0300e006c0341c03c41e441c0440c10203240c1400c15400520040030f40d4401d03207400380b400307071608007245850054480141c16507015807030440c0000c2c0100d05d00341c02c20316541a40e600d00b24011081c0c203040c1c103082c0e00c001c100d9400081c80030b0240368548155805000d007240ca03468105c1c0d02c0c5e00e800c0740c01e0149aa012301030f54900c5595201c55034585040f100207240c098284c940516041d5821403c1c0b401d1442603074050300620a101e8804141442210340f04242a1909017003035043c900c0c40b01c001c101e51a40300c14000010031010011034aa54080c2d403140d440c682c1c07017009000310074111071f10311b00040e48440b0605006110340491070304044070b0105800000e06e00040e039603507941422850600c1c1988050300e07179400581f410a86100c103420070b0040d500d4030f0883d00c1d0941c2e000c0b07102d0341c101c0c886c52080c1ca07c9600a0541032043e11b00c15604850000000814100c400416840c10000100f00810440e416176454107064 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 98661151 1250 98659901 98659919
    0x206090606010f050406030515090108060603010c020f1f021308030c0d08010f03080c0106030606090222050a0b03100b0d02120708060618030a050d05120f0106020721020316 76
    0x168414802e18107019016141c10001e411340c050307402210305160312000091b0188a03108000c4503030890040000303a065a6801c141d545980301964554001e50814080a0319640002000c0c910f220480d0010407940c0e99481c1c96150041c1010382c1007604940822150000e0f000d504008030181103020051961101c1d81c4005502d00320340d201d103e0f020300130b140d4010803410415034450402c41e0380140416640e20650702c4054010701c01500b00400123842c0241c04201c2c0c000c2980a01000442e0075448030b03203054440c01c2e402c9622503512a0380c1d070108800005100e1182c14101a6130429418888044a140c13a0320080742c0035044030401c2460f09a0218100f4031080d8600c0e0525040011410403030f01c142018004180d5038400c026142e50165460000800245c80400c0080b46140d0410f0a80c2e0b8ac01d030700284001d00741d07441039040c5840011100c0109074000003003200f03207040320019001010110f00d800f40501c0010055100000300000301401640580ca0a0101d8a00000c640003d0510541000514 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 98662401 1250 98661151 98661163
    0xa020c0405010f060f021203190915060609050906100309081201060507060f05070c0303020a11030313121b020f1516060e120d05040f0c08010203010801050c1809040309080d020609 79
    0x4a0455200047c522104040a01243d4010050180388034626040780b06600140109101c0240003040c03840c114184040fa90b8007000507151107641e5040c2280d6198200b001c0b0000c00d42c0e80640c00744884041040e00b074025840307035842d03900c182c14050400140c201c29400e40c6009a01c9a4081f400025400c0b0070495203104147c40c00081c2e40e010015414510070003801c0343c0d0540f10060074154000f5100300300500800c1c015406149031000c0300d17501d1820311070124940060010403248400d01840e402c1240380034685503034455410024210070440381c3e80810051110031001150068075903a5000021a200b40081424581c48030020b9115105890080110380403400c504103190000528045044040c104a903d00d203584a0b000c100ca0b215410400104d00c0b2140c0c00502c0c05612070b80010304140d040d00518100ea122200070000760750ba40110800c18843c40940051042c082c0b102d40606103001c03405503070054040d1902e140b2294440090a2400d02a41140f60160f03004000304a0041320421403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 98663651 1250 98662401 98662427
    0x1803100902031027020a0b04090e0c060301181e0218010e090705070303020d0b0d0f0311070302090c070f05030c0304031407050105030f0c0705120309010507030b090c0a020c0405010f06 81
    0x82041604011404e40d4025060018200c10080240c1d00c00425550f4008000020308944111aa13460b59100d070128002c042400c15490f10303011f5010030342c04502e07200058074100c9031b100300c1440c0301e10311100c0c2c4400200046078090b241c00b0345072036040c0c0d056021440a80f160300181c0d101e03040400041000074111841480980c1e12843d000410090301c10342c0a0150380c901c40e4507050268039141c1c2d000c400c0001c1c01001c000d282c2c0280e07aa071315003414884c3c0c3c20640b02e0100d000b40c076100a100c0140c0708440d152040b0f03020117508144250003140e0b0000010307000701407883c00741001c4d882408a540e14241145c3c0203454003081c55201182c2130051200c510781000381441080020583d075440c1400113070050200500a540c24100c050000310340e60702900883d031100354040107440f0643d0310605001415001035698400a43c44c181c00501071034043d100d40040020010314882c0300c0e42c2da2203400c601c01d81c800580181140984803106e8503589580c01090f000e0a60400072080711410100c004140b1506c604c0c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 98664901 1250 98663651 98663683
    0x40212010c0e1203040e040506011e0b3109020301050f010203091003020a1e0503160e0307090b01021002031312050a0509040c140c010e0106080d080606180310090203 73
    0x40365481c00c0e03800c003603003441c4102c080d185000e10a4960341101d081d0700803940004d002144110070801086404114a0706032401301c01407004c1620082a5208841418080c1d00b2882204009004080000140c010104021598243ca0480002c40c070300181130815400418025000310052196141c000c0300c42c08011307428402141007450b0400050440c1030704480d40760500d0ba00054856030548074004540c2810041c96040d44181501d0100405950080f541d181000f244c080380c00c0e060910030310511083d04d10040060845e503041035513400c0100294150035040d0b2080c03100500c02c40000e0b00155102d40703a004030801c50200c0e642840c809402c00307500c1c00070800100300020912182c002094882d85001564005003804012030306949603c00d2800140d8003071004600520b601c0d00c15000320450400d490b0083c00301c140c1e0740541e191742d803258203500e81c00b091180001585a0a00001500e450031288180c04c82082070000840d003840800c81c1c880b180d06446071114420340c2001c002d040100303c0d130300c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 98666151 1250 98664901 98664911
    0x20c1f0908040e040204020906030c07020a0906060f080916031b090207020901090207061415010f0f02030f09060405191d0f0115030f02031e0906070f050a0306081504021201 76
    0x2607501c1806200b1801800e6024200740c02082c21764880c0da05403030b0100c0003e0206980c0341801c0b03028032a503410141c02240300d1102901c01140700b21050040e4812501c09840301701182c0140d00040d525200c00401d5485030384100c1903010488122810404000c60042907404411900240407080500c41e0390000e44589004206180068480400701c43c1112070b0520010b80312280c7d4548a07010344038044244080b4440e10080c0170ba140302c1c04455080410090701ca240000074072034401e480b01e558006080d4090f0b04240701c043c6492040c3e4004040043c401440e0601e4251110001103003ca0400c642c4c4800380c0c020344090200c0c4120306d04040000301840c890b01c98030702d4881300340e444059050140c04410881d603210442154042c0d0003040a98031106030541d00ea103000d03604820b0413004012181c10000224011400e8400040780982c0100c00a5a416207000142c18040c0c50582c8030000000030966101c50008a000c002d0003403544107280c0280311580e5052900402c03034410480c2032100144d901d45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 98667401 1250 98666151 98666153
    0x60806060906130b131a0103051b07030903051606020f0102070c0612140c0306032b0c020a030512090f030118030f030b090c040e070801080c0f06040801020c1f09 71
    0x105003030962154048401182031001404a840900380728a842c60f007103860b80c82208070b980460303002003805411a2501d54906c5041600440c19500e0946050144084205c080d02281401c03100400900c1d000c1c1c1841c4030b01030750b04c0e40c44903d01588010000c107280300c00f59091080325410300c00f038480145031000035802d055141c0c0f107445000b003c9124080501940460b02400132649400c200180a06000384400a00e4412440415548125101c40c842e004614801c01419001c00303078024103100200300c2c44854518000c050b21a403403865410b0360301011011000000038010009a8200840c0e02c030b0843d140c9103401d06101100685000c128480d0b410600c076150440003200c441c1742051340514000b068015241e81c02d50051110310742c41e0760400500410401d0303191020740108100d03903104049250554030f80e00708950800c002c1c0580ca0903a00201102c20b1949030040b031507141c5d0a4000c8c2682c4c03500380d40c1c03030a0034220b0740b15074803061513038001142c0c1e00d40c8200d408a00c901c419101403000e2094a441d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 98668651 1250 98667401 98667409
    0x2a030b0901180911030d0c02010201110f0304023102070215031311130c0c050c060f07080306061908071716050c0c0315100f0513050601020a0611040501020106080606 73
    0x500c001814500d683c078180300c8103000003150845a1200c0140540707401c031a00a41c0180038243c0d51078142d01560900b1100c0c0d005100d03181c100c40909951261300c1d070441d12180e08111580459080e0050300540150000c0d015030740045046078140b03540e620040e581c010390720500040c0c041e00c13400301121000c20b0042110a11424490120b0346a00000c0f51482e242810002085151041241c800c0149012203103640c07079801000c20300c1501d001c1c100301e4121008074401c1281610403140c004401400502812000500740400340d50416001402d041c10074056035451241070103011003101c00074030701d00181700c800c0e6045496100030703074018001c000091801c0301c20f9200402149540c1030030070000092a160541d810310110300112070050943d03411003102207010f0a40242500d499104a604500c00220350002104100441c0c0c0054141e6542100c2c4003001002004014200d505502036600c1000000d4403500c1030f0009a051220480e0316203040070002800c65031150440070f0f841d4043c20500c030071540c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 98669901 1250 98668651 98668679
    0x6060e0108070f090308220504050408040308072a0905060103050601021b0307030b07020106080f0a12050703031b030e0d022406030313080604030e0603040b01050103050a2a030b0901 80
    0x7014280240c8031161003400701e03411130040c1c3c0054106000801c140340001e42814940700b001c2d01c50350361061a60340b0340003000110380051b02c000340100300c208401c00000b400500a002d501e80160700d0502d403074030251784001c6d1065840c0348030400c404170301401b030180ba0010311501e0b410240a1808110b140740c0b8100207940c03a90481c8440d154950142005002594100300c0e01d0003465105800c01d000742400348010780030301a03070b001e800c00d64051341c10300030044000003501407103140d0810180401c144040302c050329190f000382026000c05440c0d060f581d1300a81d00395142038070003416990000d1412140c50149060041122842c0c003150000707041034403985141c000c0317000d1420b4205140185034844200080c95849024460415099a400002640361010032854070540c00389d110001e40b00c031545c0030004c1700c0c4070440303004214401000040c001e5510990109a000601170400180f82280d80c2c81420803034180c044008565411071150310340103505000c0c0b281ca11805550000c0954105200c18071142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 98671151 1250 98669901 98669911
    0x6030203100311060705101d03070f030e0a092307050f0306060f12040f0c0504050c1204050313030b010f080a0312020c07031707020915010207051c05010c090906060e0108 75
    0x40018502c9000550b14441100c5145600c06d0888004191568007000030b040e14513040c060075034428072403402c0408080102e4608075800180340c180d141255030b0981e444088002401d4000140f010042400c1045110f0110f400401000016060b80c542111000c003500c01801e0604000c0b05114003005100301030160703500688215241c64980d040d0316a038413014050340890f01c0c0c450780c00700300b800140001300100400f403501401101d038186031120180300540e60140d9064454003800c01c101c880800c005140c00d90420700c01e406880c50201e4030460300740c2c504072a030000e8428400500041100191601c10080141491009001044034603180900440381040c0c4000d1140d030006280c41940f4000d00040c0060759109154441e01c001e8100141c1044e08801c2d822401880002c000c41d0b100c5008960040400805034010040c003402c0600b80a440e10306500c8a0100c0d01064994500041c001c0c003c0600801c0307669203120a0302e14104c540420307100c80303500031000d020b000041a4450703680030400503404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 98672401 1250 98671151 98671163
    0x100f050705010f0528021c0513080c0c120a080405150d060906080609010b09070c020d060c0507050712020303030103030e06070b04050c01120608100c02100606030b0a060302031003 79
    0xe4515042442c09490b00e02c0485505520340410004454a03117040400c0d06220001c848000e800c400e40035030100e12a00111000040c40302d40c018140304010381207244d0003084580021094007859590350f002d9040307515030309801e0700001c00c000c07164103003070801d05081c0c04410010300317191045480c0c0c00c98610031402018003400110420510408403031089441003001120100001c0ba038a1140d0401004a805015030364014080821031400c41401200410300c4010424802030302d030542c060340d1a42c00118101e81003c00c5000180100e54103205008110b040d80d01c4056681210b850000d08103040758222101c018400c40080015842c00010740303065960600708080903e804e580000c144e80034070380000740304541c3c01040208200010a2540350900c0030380300d140340d151481100c6415510781d4081d1500c240e0042c840d1038161740c0c198000c44a1145940180c0301c00b100c0e110508019241141c010320301090b02c610602d01d40d41402d40300d81c8001e20302460b0460450804042440504141e03210103080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 98673651 1250 98672401 98672407
    0x60112061805160918050d081b12060307050a0317070204110d06170309060f0d0e06090607080a02250606121b0611030703030e070e01060815100f05 65
    0x40e01000c0505800316400100302c40c803041114402a140c40311074003072043e15030704000c041c11610354820025000c440d4401e001d01f2101814940c04c5500d0240101414074440e643c00c001900c074100e1000500011000d0980e8000c0d0b45040002e051400045038083d5020710122007041000c107240040343c01c1d40d045032051442e51a030745400020702401015900c8030441400069082d121240744d80484210385028040380700040711002095101c0c01802101a04014200130021180c0f841000500d41d03040d1248001403515480000140340000403558a00700f6071100043c460400e4101000d2940420303220002d41c581521103501013202944249041c1c0c461054810030b80c204006e03a08a28068607071001e04202c04109030503e422000d602101e41c01d03407010752400108605118401c0a292100e106005614205142c2e40481c010001c504a00031140552400451101080c91902d40201001c0c2c0d91051a4100404105a500c100c1c0c600715108072811044101e2aa82040e08205200c95078101691 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 98674901 1250 98673651 98673671
    0x30c020607080408030c0115140d0204060f0b0c150402010f05071a0705091503070c080708040b0a1d04060303080604090302030d0507180602010b0f09130209240306011206 75
    0x652801101d00050070150046404140c0c800300201510b0240c1480c4001e120031080e03000c205244a43c94000d00541440c180d41d10101810010080803c26201406c00a4550391350522007140c1d40a9400200f04041c00041003084035004110800040e00e20f80d0700c0030a1410240c1c00070300207c0d29009203105200c0b02003414004c0c40045000140202442d0012184034074040800038101c1d4020641b0a10031800c00704964001c0c2c00300c0007030340e200c0d4959443d4024054642c0e00c502c11540c0085400f00c54000e8104030200740d2030714220140c40d46242c0c507180e1142c0a0384c0c0000d511400d500a0380c003030380201c1c604481080403942c403074200b64000d0810b131000542c0100b141400c130b0452150354840181d00c2e090001740f0803c25407103050044021300ca01c0200c059141c503840224280c4900c2510355920008181251041e45811305485400a11038035943c441446180d01017001d040b000c5503424206100141c000a4400c500703900484a081c00b10094900c2e581800c54200301007802d038002038080b917680c40304c0078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 98676151 1250 98674901 98674909
    0x3030903170106020f0d18050409051204030602040603050109022107020a051207050105010b03010f14010905040c03053709054603231b0721080304030c02 68
    0x18905018400000e0b40e1580000380d07668940051800c2c072031103458100a0010702c01e180c903180a15a0003d03c0c2106840c0c40308000203002c0d10304059400d4040d030b5407600302c0f00480000038002148980800350321946801e81c041c08444050703101040c500e004012038020000c024108680c0c11b81e41c203500020588a0400c22841c4c8000c10400500d241b1034805940e4864003040050032019100e20003d0003980c2e05c6e07104a92650100307200d5444088203a000910106c0301c2201c092201b80b806241801c18140c3d188006030640754003040740408650f4402c00e1020800e50840d0300300c100c05006035107429020a0038090340310341180c500c2c40315403207a0317420703e40007041410310403140c0880e06402e029010982105164008512001c01c0f0103110f6a00c242035000c00c1d44c1c06541200a980544500e1042001917044142c1d0700194100104000c03402c0144406140c4003611010b000742201c0000d1002c1401e181504040c0300402c0700b40c59001240380c10041c00500306e541202c0d80b080e030601c4c0100c0c88011301c0c4041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 98677401 1250 98676151 98676167
    0x2803150b031b0d2d0e071205030d0507050d0b0108010501020714030a0501020309060702060906010510180b0409090b06090f01030816020d03121d07150e030a060b0a090b0a0303030903 80
    0x128040303003444900c40c1c58184400c00192016284113400091038a454040c6040310301001d01c112494203c1d401c2000f5550803440000b011034062010760b40b034204601e04002c11500101d85103400f213200803400c004000024810b24051040071b0034280925410800040d5a50711140704584840d400d0640300182c2e07840a120311947c042d4007500a40d228101010000c0c0c80e07001c11180340006100320300000d6090900040d0b41c504036030010300001e590f0304005108980000b0305034074030444021000c1d8002410005200180010821400300040702003244c40c000d403c4d0b0901800c880d00c10580c0c041031100d10050b0800c0745045130b074003100269455503e10380c0041c00304c0244c130020354000c5c204c0c031035038003856040600845100303940841040302c410080a4001c041860041300348055214a100f0b0040c6244075284511961050410600394151070001070715201c840c00e003c0b100c51b612441d06a6980c184199084041c1191440c2880354040c201e000c141081903c2c0700113401c0584451000050500500364 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 98678651 1250 98677401 98677417
    0x13331e0806070c020111060402010e120f0a0506011e140607050a0602030106030f0c0807020d0e0d050f0d0315080a0210030216060c02070501030b1807052803150b031b 73
    0x3521018a00100b019240d000852030981c0440e00ca010040032480c0003082e0603101c0c0350305840c2c02e4620081d020500001c52903540c4407103858801c00d0510705c8009800c12402019600c2540100032070f40c1801c8180c0d03c480180c810940b4400d42c1c0c0c2d042401401130101644002000950b007550321841d041c00c0c1540343c480f00c25001b904c054400000071600c0e942c5a04407003c01868284180051700180304101c84214007280e541005810940304514102d125400322288602c0080c0030000344c2c1c0d069103400d0b04010142035541180d03482141e40c07140194150155202062540b03920903581ca10740103000d03441e00c0c20344800a1007004010205205036000e070307041d22003800401192000251a0307150410090440000302005441441030018296201c0e01807985564000f610060401c01002485625810050002020312500b4020901d15260031000f80032034040b181200c0c0c0b940800014058200e4107024000d0b200000300c24403d000c0c12a01c1c0341181d402040402c107406005411841420182c096920 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 98679901 1250 98678651 98678653
    0x80613021306050a0e0109030f0b0a0b060409020c010c0e03190314180a1520030906070b0406110310031b05040f0e060a02041401050304080913331e08 66
    0x220200b02c29078404060102600a5120f0840c01c4c04441d0056600100313a100091150300780034031000009105c0c0e40019005500160041044c148110015a03540c2103500001426540481c01e4528940240070302e601d4001c50781411503c201c94500841d4540508952025801d5407034142801018840c04009895683c2c1c40105034a80078113030f01d040d62145019241314455450360700d0102d0f0f500f0040c0d101e990b00e662141c451030850b01e40c0d5035140822007400d8082408501007030080305400d0b2206002084400e01c6015000d24914051402c4030486001c030006248840b0140f0411101d0800c50038040c050700d8000240d005100d0f603450700c0d031003800c009420407070b002824250404841500ca030419104e100d9184181ca0387c5981d0f00e1081c4007240158403c03245115a000c0043c2c40550261004541190040140c90b00d45403589002c91300d02500044660581075581050300c58903c0c50803109020040050380f20360281031044100c1520440f039015044403041207100c00c2d0540d0740358128400003008400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 98681151 1250 98679901 98679937
    0x50909070c02120106180b0402090d06050115020309010e0d0203240123030a03030e15090607090602030c0a120c170405090106051306080709080f0607020c040b0108061302 75
    0x320018180903a1540490040600866400d4040410701500d01511003092401100440100c0100c0c06454018000d94000390300300001600c82d100d4941070079076240075001c041000d51400d0001043d07103101050384821034005200055840c0c0c0c0c0030311000f42c50700342206c08650343c80303090001900300402e940342010703031b00388034140d4010018000c00c200f4125604040310808a005920b0001c0c0865207082e60158035401040ea5500003d001c0e82c460382e0400140e070300710303180791080444100700340606540260321a88910108400c00ba888400000500440c0c0b0195052450031130440d9176070b10380303c1c400a0102c242c0c507a2256402e48143c18407002c00750040a06001182907000008044d44a80039650060240c9000441c005000d4001c484942403200307a28070350a8900941124001000f500c0c040401429107000035010108202c0344140c0300404025050504042c10040d140c5039201c412180624180b15100704242c0c2c00104440d030101007038440c0e40c0044030840026009105038840840841c90701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 98682401 1250 98681151 98681161
    0x3030905010c0821090607090602070b1e13031e080316051908040c05060f0f0c03040b040b0306091008030f0304140607020d021011161703132a0510050909 68
    0x4c240ca56000316a88400e81d04c280d202c0760b00c01c132200c01c980c1c06100090380c4103003801c05c0f01080c2d5500a00c020001e5070410b044901200c9100c842031340c00400701000e207125243c2c0500034460400103139000001118812142d4510300e540d115500e0100420303140f2140c0f0922250b50015000d10b0444040620740101820140c1c02d0040c080d002c0502584c0035910036a841d44042070710b0524070111203000074460a20317800c120f1002040d83c041d80c4002071000d01070005110000f2711001c220080d00c041c0034511140ea4691400001340314036090024004003041b60b480d502044141008000c9071104820004515900d07030f04c0c3c0c202040a00081c0c00040000d20075481000b40203a808108940381915a81c03c1d545c3d8a01c00d0b501020554078400084a98444c04100310002c0700001009500410b1140e003d031161080b241400f0350355600222203801c1c810403650503d0040240714003084130441d4000303868200300c40c154440310911400b203004460040c440340c0b2050030310078010003c4c1ca506003002003d1001c5403400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 98683651 1250 98682401 98682457
    0xa0b0a0b0d0911030105091e150a05150907091401021905060105030f0a050c1c12090503070803160b0c0f040f06080a09051203070525050c0105030103030905010c08 72
    0x3a502e4241d076810150710320009189410700030b0301c0c0286c01e101d00420740d550500380c84d18080500c141d61124940302c1c05100c4074221301c22116061054009450019051814044e0203949880c03600304284501054003c1104a541052421054400386191b02d0460006480140d280059600c4003007804280354050204124000860a050712401d03804d17a401c7d800841c002c0c5580c0c0305840002485034002240c00c101a003800d900c02121001d1041d0902c01100680e03c0b0344040d074060048010000e64003050501c014242003285a00410484005500e0301940018910740f038440000c0c002c01ca2188039002c6610301c5120b0382660044012004907030764030346e40e808403c070525a40780720325000310320508006100c103000340c8242c1499940140107040c2090b440480360016500041c514010300100780561020038540d5010030200c6001008070004044140c10940cac90a241240400c0c10000100014030000c0d61110204048810a00b801c842d507200900e0318103500e01a8181c508032881c2101440800010307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 98684901 1250 98683651 98683661
    0x6130f110711030c010207061b15020714010c020c01021f0204170604060b0105040e07030b150c0a1505040507060f12090f061a0303040e0606040f03081c0b090a0b0a0b0d 74
    0xb000300e0898110090030401079850342c0107071050a01142181e4030004109518529060046200f40d051071100c81088065804036000712105070b80e0300000515034849000c091056000008050004001c402640c400003556104031807141041d080c03142d0b10f50f0b540204603806603405401a005070201400040303020940e83d110440e800d5844504183c02c40065501542c100c90a039035074140144095904c00d802a001b8044071111590891190f0704080c500c2e0074410013031710716120306134081c2102c58800e040c02c00d9540c04005207045000d1503c000d0000092001403403804644480c105284003411450080d60407201815030201030a0030038050300c0030060a0024800700a204182c104005241d42c00744a80130402a4612a05513104210074410341510500d80e6030300440040c080380c0f03010344410043c2800d02c1c0e90341c07044641140104820508650034441c10b070810b460400100b002d0740142d4006883c0c0f00024002c405e000350b59400a400c551517109030540640b181c130b00c3d015034034040d40400740c0081c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 98686151 1250 98684901 98684933
    0xd1802030703050a1716060b0312030a020d06150e010f021c03020a08090f0304050f06071203020405090708070c08030c0d151a0717031807080102090a060806130f1107 73
    0x90381105407000d01e01c14000c00d0305d08101a08800d007100051b00e9403060f00500000b00c41c171350f051145080c0000102910703001580320f207d0140300582c4030041400640c043d034040e41c000d882c3d40d01c100402c8041d820341c8051080b24140c2c0c2480d00d405080d20101d0700303904248401200b6141034140c040da034400944c0540050004031602c0e51003402a40e03c40513a00d07110b40d0741c0108140180c04c200404c104a103001d446d9050351440c0240001e19045180d6184074240c5d480c102c0d07201c0801d8000c0303003c212500e0300c5842d00d540450181056012450009001883c0d8004600010004400032001c500c40c141404151004268042000c0010b01c0107114650082e1f145449848802e1101902d011000000d10068648880d0b00420103c61031402005009079600001d08416229004500c07240050600700310301c400a01d100800140d072002c03c07005000c000013f907044007043c4941c1d07406010f0507840303034600002030188540c400160605250407080160510100007403e004e4049040c009019042c01d590300c1407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 98687401 1250 98686151 98686163
    0x20403020f180403050a14070f03080f0405030306040518011401080f010207030e090a020c07140103050105180a2408030c01050901050709090c0e100c1104110d1802030703050a 77
    0x20400030801c044410828000d01c60b00d10401c0218001130b0181000e00302020761818415000c4851074440f00e06504404403e031140d0030102d51030024160003100d179542080c44070688419920b02602d40503a20301c40a0f00e2140511f80d6100090007105100c1e440714081c02c416802440304844070b2803080d4604034280540d0b2540d0084400485148205201300d58800e581034855120f0590401e04000103e071008000c02c200c10340822850030880c109101000140c050110f8074810f9050501c0010103c500503000340e4042c916220032900c0088451900903800407051101185040301c04940d00c900006000e1500c4005d40e0101c000704103450040007030034074044814001c02050795502e800d0713400d0354800c3c2ca4403404544498803d21026006030003440c0421810300302101c8030044240441e03d4010580e4000000942c42c00001c410080c010007040607440701268288000001119020294440c00482048440c0e07950080d058203480c00840003242500141501c1c6c460380d4901700240c444040440071110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 98688651 1250 98687401 98687419
    0x190501060509030c040506061603050c01060807050a05041802030327060405010f080c0705071413050105060306040e0f030406020f06090127050c030111090111010204120803040314030a02040302 85
    0x450381c858015103105000040040804c00050030502c030041501038a1103030802d0041041c28011100f502040115070300c640d54240c0c6e00d07010405500e003180c1301e41d0421419074001801c1080980d46081c140b90540780e0803100010f14660bc02c6010365a00d0300c4500007909404081603010310099030200034102490002e070495802406e00023006024815030003940c0c0443d0603059420800c2d03214a1070281d204459905161030410551640380c0760440f540d0001c0d01041a04e410300c80c5c641010f00410252143d0300100f481254105800903409020050400d0f0140fa91403c290f10b1000d8104151681d0f035102c0341c1603a84c0c1d50703102d400003900d402c0103c2c0380c1c020b07901c15100402c110310414031807140040030780140c000d42807840080020300d902880000740c90030311500304804426036084c45606184481030301e1442d0380e402500c0024001d4600000b41c03441991060004000a840509000d400654010040c584e25035542c03a05035081000c0c5c02401003080c00110030403070b01d07034a26070081080d00d00031500a40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 98689901 1250 98688651 98688659
    0x15060501030612030c14071215091a0c040e0108060106030b030708030304061104031e030207210809010302041206050108060f070f080601020705060a080a11090d1514190501 76
    0x401e40302c0c10700c40c1c2c04401c5920910603011074170882032142d50034420500c500c0508541100c10389414030f2170b0400ca804c840201a02403c0008032210350514198006045c1701c051856111144403411a0041c00c01d40390310040080c0d00400c2120881d000340a20b00280450381d41c4460f4015510502401188042441c10300d0810032450001007060032902d01000031461365456540c1c20f800352081c803c080f081c80c1010b05c40480064417020741e62240d501d000100c003a0660b00d900f402440c0080079070248480c004800340c00d051000740b1100b00c541e003542040d1060b5803401407800480c000d04c21580504c2c00d0841c0d01c860b00007001820b4000c1812208050f040342e6194482c0032243d0b16800c82500c0c401d000c20421030782102d01500440030a80d0026050060398009940c80d000706c2c082d907000c540c89000040021040101b4042c542c495040c06424813010141000c10b040f01040d0398030f800e00006008a45e00c1300c3d00d600c4120b00390f0032083c20341442c02c05880340740c100102c14881064079460b0a40815080000100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 98691151 1250 98689901 98689907
    0x6060507050712020f0411070605100f03110a240306051e0111010f06120605091605150d0f0e0d020d14180405040503040515030402060a030509010b040915060501 71
    0x840d45030304000035091261600014248507104072400b240c000c48140600711050755503202d080134004210a05070755510a030701c0c00c9001c8a00040909458040c460f006018005003441920709680d48442c07070a00700c12081e00081c46480040d4005105030604004080a0040c400c4c012509115140c409024060322030041005065280d050407400d12603812460405604c501e00034444811008000a000003501e2000401d9a80680016840001443d003040400800d481400e40c800c1844025108065280c011300034401076074860f042c4503241d48000d034040e160041c0215444044001400c210640500c02c501d0040d004941000003140100010345001034001308031150360b4111503a5603102a0071004890b120b40c0c0101191040425034540803800a884511170940600c0c041c600a58585280c0b07400c1007040313408020b9a118814080c800c0c0030040e140c2d0000d491410060b1304000c00c450741c801015500500016001503405401c1c6030301f900500c00789000003640440071500c1071001640b508015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 98692401 1250 98691151 98691157
    0x51204050d140309060f1914070e180103020f06130e0604060603020c0c060d0908120a0605030d0c02100309080d150909020d060c140409020c100c0c030e060408120904060605 76
    0x410180e0050b400041c00400100c040036440345102c01c0d28542d4224a001800c100c23003050072000429983c801c180017a1a421080031081c5140807140385503000300d031190030044101d06120090059907206102461660391100380c0312188400e0708401041550307400700c01d0040500352200c40c0607901c0c085012644a00c20300850704207450040082c407148100d0300500a441d40708600620b882d596444500000814543c01001103180c5103c09507011f041054036001161002d40c04140720754040c2c40390f41c5100d508100d18126054048a542064900f102010307000381c10070040003403a001c00050824035040e8035501c2896403007009500e03040841d40b5282000c04036105220082c6d4041070047d41e1000007240d54001c10b8400c400c44c42d020303a0070190f10701803040b00e800c59009110b489401117070992101404204c0b402a10840010a1200c400c0c23224020b0110300d910342015041240c0c0781013800003900d90310111401400103008584150703614071030010454000c980c40d603105506245000400900c20030035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 98693651 1250 98692401 98692411
    0x715050f0a05060f010e1207060203030405010c080112030503090a0c08010c08070809070515090d0503041a0702130c0324050315040203030a0f020c0402040308040e06012c01051204050d1403 83
    0x49802c0d000401c00540340c61404039103059001c0d50040c801f06100c601481500c0052482d500195100e01301443c0190942d030b00b80c0709000401c1502001008080c0403000400e20790b03501814207542d00d8a800190500380810343e42c4c080d082800d1500c0000c1c0741401503014441609181c3c1d140c1140c0c1d198103100715080e00090f1036040380303640310f46024042480c1822620b002c0160720f400d01c5103410440c1011440420004a0a07241504003080c20004502210141c0d49021000c00c2c8072880c01c0700350b90004a050140084c0b1480c1079980b80f1103041d40c18042c0d48005003528405a1942d0001c2a154461010401500401d40280900c1485840205990340d003540103a42c002c01542c108483c103001126031501020700e4808601c81d6180d1004d098440c1c1c8002c0000d1401403020301e680d50f0074115a5000800041c01180c100650f03200100d85d468440c400f501083c0d02a002007410a01c580c00040ba124003410200742103105c2580b080c0420030400086075050703802c80392140000501c108800d40000c2c00200c0d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 98694901 1250 98693651 98693659
    0xa080a050126101805060714160503090406091b14030a0207170304060903090501050304030c1b23010311070312090201110109030f0306051e0d080715050f0a0506 71
    0xa00ca41c4500c40d10804014803030103000c81c3c0414080d0900d580c2558504c0380500380303074020740d2800020f00c02d00340403003548620f6606104054500e00010340e200d83c030607890071400e04e41e02e001e10902007140600c00c0743e0344100000c3c000d00c4125150b4411100400d8041c80c8401e0f8030051808211401d03002d01250002e600059a900303045690720840c0e1070217580283c5c7c040f60781141d0030941e04280002503020350f000b80e004000c0018114241c1c44d020340021b0494200c80d05000050080200096010b101c80c02d00d1584108603619480749808243c007030100540003600d00c0380c2002c85041418038803070580909120240da003800f0000400038082910320030004040d0000e010550000e0308401140c10501d1100d02c10714046004490161230b440c00c40360b082d00c0481c0002d01504080020070b615008190161004440c4982440f5036024002d02000c3c0445032140603000d02042c0301c017840724910965a0058101080f8207100720800300e0f1600a0000712031b030760030345010b140200d41c14604600c01c02e4803030b80e0090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 98696151 1250 98694901 98694929
    0x816180b030102070c080d0f0c020303071506090e0c0301060b13090203040c1206020a0e09070f03050c042115020f0a050702041d0a02130c0206010513020f0f0a080a0501 74
    0x20124805059558003440c0c0640d020031a000c0011208002d10000f8030420014000400e401c420041034044034021781400c010761030902501581d03010045401e00c0b41d02842d84c51246801c2da03070560240c0a290700176025075290010618036402d0100e8440700800c030441c020400c07503071112120303030b40d078042d0074004d060109a107c2c0c280700c0000710f50b00031a04180100788140d0340e1603035141c1c0322500c0c444002c41214410b8010036080280c5410007019400d8134400c946520749841e1071900204a00020441ea60401d6103801c0426500e41006040720003900307200b2144c1100801c08940d01d842000003d008881c420811501c0440480e0f0318402d031004a50800c03481464003d1108045403940c0010380244c1e2311541d01c3c04030f400d03010100202009624660005064118843d004110310705038581e612403801c9050000e0760030340c65070202d071482c191203044950191018202d00080d000b40100e22500c5c1143c400050206030320004007024042540d40c0c0c2c0d0310064140c4e280100c0406840c804c1c856014991404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 98697401 1250 98696151 98696189
    0x105100e07120b10030f05100b0f16020d03080f0109020304050d05090f040f060501030c0509090f0408040e01060201060e0924061203031501021c08040b042301060816 73
    0x26080030014852a100042983e00c4084001090480584010b0b00821743e110100f41d401c50700b502480d58420440e1b02c1c101c0109203413502e2481310344100309543d402400b0009030040c3c558194004009250340180004c100c954483c60080d0403801e041d600c0e03d890054503000000c0c0843d06000300d074810350b8050082c1c031240340f041200b960543c000f010032590207030510700c8c0305030151624422000024207814000c10414904400501207410784508002007120810150f41c1c0358441201c0030350841e03070301001c000c40d075903a500382030b41d650059170051100488a803000040e9150705410100603107641760040e43c0f0329105d2200c42e55444001c40043c1d202d009803520700e0719070300402d140f10075400180030305103070707920a03003000d0240c1160f2084800e8949814007842800441d6410800359000042d516111450710484400107003019500070300040401805000042c10841401a40311002502011848c10184070030300d103e010305400c0c014800702c2d1003003100c0040b0b01031441c030b114004c4800e40c2461111480e21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 98698651 1250 98697401 98697407
    0x2040501080708070522240902070206040e0a0b03030a020a0308010b0423030106050409050f0111031e0402010302120a0c110619050c040b2d0405061206120106080f0105100e07 77
    0x5034603840c6c0c900100c0704484c5180382240b40111441d5125101c06100b003501181401910005160001446588140246401038075084225401d68041d180d82001c80da5981c0b89141c007030131078000610307098007010415080080d00050f4400c44139100380c490040583e26140385101c0c40c02140b003a0100b80341c852680e041c101c107800c0c20410001b00080c001040803521400400c1c260381c1014401c071040c5d803018414a16810f028030410105613214000603145061401002c84203078042460407050118500200302107a0090b0704481e504d03050f03c00c0e20b01c0e807880d02003a032900400c6800d0b1504007151198100c0d604e03028001c11543e101d014000b080030b03902200d0f00c5014004100007041803140c600e0402000c40c0c1c124548000d0418980f51045045000406410b12100b4440c24217900d03001110601041c00740c0e54655003078071000170200c8600000d50741c0340000102174944039401000e15502c1d2203004600602e002c2a4540008402d030024040c81c2c40d010000c100110203841445510010b810104030080c0c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 98699901 1250 98698651 98698669
    0x50c07110d0c06120b0402040f050105180d0803061804020619020a02060c01021314010203090424060801170307120f1101050c03010504060806070804080d0e010f0207020405010807080705 82
    0x60007524541d4400c40c1e580e241c58440550b81c2008011500300c0202601e88240c1d4044e40300e10b50340664055041c18500000c9141c2035080f401024144100403481822401d032440c4034070500c200c004c01d81e81d2120702074140781741550710030789481d8001c14110240d01e049840c15031400740035582c040c00b8507282c010903151010012215080c01001c41c01582d503007001596841c8080c1682085407000160340d0349034207030400c00a40c030580c00718851030b0050360035070066030300403098400020702501c0209040b614552035003611909445c51002e000b10901c804104941d0007141d181c1a10f01c40c1c0350040050f170250362020b6490140600c0145072411044003401d01c1c0f44181003c102d03110785400c080316200e00e041303080b9003964402c0322401c0441c1800300040083d45494000d071001000c0c214007501c00c0b820251340050400c840100302030f24901c00014808009002d5611080c0c036a80400000c010094076010082c01035401020117130300c2181007000125044c040440c16000700c41e0740b8802000542c0c5080203003c0c0880b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 98701151 1250 98699901 98699933
    0x9060108040c0b0c0c15130e090d081b0d05090c1c060b06090a090e0c120d032f0403021302031003030c0c0e16031d03040504180503130f050103050c07 66
    0x3c0188a2030305420303211541003070071b5803c0d0325a079107844c1c421600d04030300c5071800da40c444010b000e045404d109521501003042400a402071824220541e682e020318600403c2490b60004840c100103060701c002445da9101501070799849090303c200c0c00e120000c2224900401541c0503c00c00e40140210008000703920616040c0400f07040030f800c0c103030b8080000380500810760000010546900e003003038807003c007072000c0c0380307146021100d20140003850080d480e0755445940c1c0c1481031503654803a941c0107000d0500c0c100c0c003407144985c512042c00c410b820f03281c0454005102c22030085400700c00901c0d21309800d00035244a800c20300111908030346541c5044401c2c4400c10402e0380c071106000c40204051044544441c4030390311082c0d2061441c4807110008048412a2001c00e0100c3c7d40340781210314031a00401202c0071208115004155140e03600e41d005a07070440342400400b180303c00904640702c00401202e81341101c800d0040416207030360360750040d03054803011030700c843c0c02c030208000c100700042100c2080d860034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 98702401 1250 98701151 98701153
    0xd02070501091e03090504050f071d0a06020f0105010803040305060609180604061e1b0c0804081b010216180218131d0a020603060105030c0d020304030e09060108040c0b0c 75
    0x311071240c55080c00400c5404410314596443d00d504414581c01001c1308004140a903020041464202580125500040c3c000e40400082565005001c200c14002c211b003940020100301d5010381e84c2102954030080700a034000d2075401e110001a06a03008001c1c0c131b0840c3c2d0090003401296441100308458024000c0590a41c050303805620301e4205030070056640705030301c40d80c80080d00402484820428180c00313899034041c241000242d001d000c1c210b40900c1018282400c01046440592a1421050090f60441c5000d44281103c410000120041544000d802a0281c07941352028441405052000b401080a09c002840751484021400d070300605040e01540070842d403039030017440064175604071030081c3e003000c40c1c9400300c2546214608403030200081a1400402d0000307000e038081a5a8040100500c0c180417011000802d107010f4101140c003d00b101c5441107540b0f2501c0c1c90047c0140140640c581c0c000c00403240015982c1d4040ca0103540182d400c14407503503c00380b914160a4150340a452100c6030b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 98703651 1250 98702401 98702411
    0xe1204150819060f050901240f0e0303072a030b01050f0a0513050601260105060918010e0405011b08040f02060f0d0f0b0402120a0903170c0c0d140d02070501 69
    0x1020b03090788a18000743c00c05100071100c06203400c04000342c40d1010b80210702c00e0780c00340001c2e002a140a50440c070389026107041c803d800011800d0b045c0e03607454001041903050301000070070340c00300100c00740020088400b03451584d0748200c4080c00c0324401c61413404020301540740e0030014802480c101203506134dd13a6004060300c80154503907010940600e00044003603207040e103d03005e0200307940e0002c10300f0100e03064000c203000b161035000740c2c2110341e01c1061003041d020306000520f20540d900d400c0300780340124100b140751480c00e594844000440b0901242c0c01e40d4107500e440c103100015004000142c82c4101c1660311401161120349031640c0207890190202da001d20108084600000312001800f020301c4d005000242200069464005030b41f03201004038440ca01c1000f00c0301c031144411030001e810104050700014102a030b8982541e0a07800046106e40c071070000b03010410b20307011400043c5000a0384c00251910004900000d482091840d060150000b900307001d440c041c114181d0140000c24040c10010030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 98704901 1250 98703651 98703691
    0x3180d0804030b0f0604020a020c01030506040e010c0203070b060d0209070e040f0e010c0201060509060a0611012702180702030307031e050411190302010c020f0409150e12041508 78
    0x80550702640c0100c404950100411005480702100254403030403c0e01c0a500e002d0803010003d4442001e0301040c2d040c1603a8402080c0141c45561110380342410110003040305080c071402c0a55680c1101c00100d8500eaa6400010382c54186600004160355000c4c10462083d25850700c140d840c440e40e0310030580c00c155200b8014842c00d16038010040442e80200001810002e03c002c02800e4030415001030f4050b0818000380318a9840d000003c100716187c5140c900702c1581102c201c6409420a40b0801c05d5904000300080d110843d551841d900a601c201c07456440303c1215540d030302020204945140c00342c1c00c14030028000601a41005a40c0c84500080e0b40707000d01c0b10500001111425107040e04c08000c40420300d015800c001084032180001c0300c5440080b00d19550001302941c0605500074007907803050002c0201915180c00c1401c480360b000300c03003051002000d002c01000b01002c40c1e541405100b410048401040e1a1088400b542e00b0491a28441121424291000310f0702411072030b000c54600103229 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 98706151 1250 98704901 98704913
    0x13020c1203180115060210050f060d020d0f06060e0919060c0306030b100e0702070b04051003270209070c02090c030402030c0a0303020114070305091902041104030b0a050a0e03180d 79
    0x200341584d1902d600f0080342000301c02403402d01d000307000c071011916003802c4c08070a40c1c80142c6154003149c00c80b40701480d40f11510109841001d043c01c000c00003010345c0004820080310f5048a82940c4c0740070701c00c580c0381d40c4901030148d60381201c80d50380b611014203084a0000c0b451030340007a142c040e240c1c00d004c141075540703a54140340f081d011505082041000203041c40b030a19256121504800c0c98401071190500b0000e10390242e10030392003424800c4c41c5030380281a180b40280c2111104000c40c062661485008822046040e000310b24200e200e1400600060300761030040e02e911040325000b5140300f0070b560307034885040e90b20390021300b060707a05114420031543c203130755004c4601c4007640c402e50000c01c850301e02a10180021001610311400c3c5810041048821640000e03160300302d000080e400c0c0381c80019400810001c114a5148080080000401005014812900350b0007031780410340801065a51542c14411210910714160306500200400d80c418564880f2102e91900c00070302c88500000700c0d607548 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 98707401 1250 98706151 98706161
    0x3081005060a080613020a02060118060b0309010914120d0f0f0603030c0c0603050402090408031009050114030f0a0803011e0909210f080a02130302030a08030613020c12031801 77
    0x200001441c00002c202031410411401c6041c0561744c00d040d4201286000040e480e0241405442419401d003560321403481d4a0f41c22440040001000940d40c9050401940c1d0107000c1c403120130307600e14401d29146480301d42c0001d1600500074034401100c0c184082040303402e000c2c00d41c607003290030180e44850100c483d0240c01e10604005611984540c84544180c3c94001e482d0002d0354400e00a140c030301010000962038213480700da8030a82c000c81e0036540c6d9550701040400104d041d04240d90b9149400004182607034220460b840d071000882c00c40f851200f030044401e69a9a3340040184140ba0500040229005140322514848001c00c1903c04080d00c80182100b152603a000c107850349440b483c2c000d10449446c01c2d078211540007628008803000305440000e00340c0d001c0a444034241e5680018034040a8102c00e02c00400b960340182944d00a10389402e010107070b500b05440c0988103510008451001c04146d00c2240c10180c0f05078094001c1140c071551034000761300300411260b0040c8042c0d942c980606401c3c072038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 98708651 1250 98707401 98707417
    0x3040f06020601030317071409040e0d0917011803030221040b041703040203280503030903030a05060604210c0b0d050f0105011107030f080c0a0b0105100905010c0308100506 76
    0x81c0b44962450a00402207070809250820421074407003032008090b48225812951030020740c81503520380c5400c02050050500250f0702d21203004807400d410440b40e01200d968100e810400001c15040c50002c1c00d0b0f82200d0018070030014007000f40c0c0301440002d0203600035242c004218510b000350014a60164a041e02040324101c4144004100f0007040040048044c6112101d035a0014154030300395001c42c2d52020b040c2e4508402d0000c040880800c0181e401c48a44140c1c0d201c01580d80300e05054041d130360b90750030a448180546041c00300040003402d06406450880b030603414000b203a90302c406130076412000c5a6000740c620822900002c0764100c180b10040c600700198820025040c03030b0a041c1d03445460010303080a410040f1080c01401e2030f100000b24803080e01d802c0186070000d03a0180c03902407024400c0007a000c58a000b54080a410310101801c05d504840e815900d90760001c03030240e001c580c06580d60155501095620026901192081000aa101882709869145a92204001401070700b100c0d01e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 98709901 1250 98708651 98708653
    0x19090c0e06010f050304020f040f0b060f0d0c02010b10030c121a0a0602120f09032506031103040f14010b190f21021c020d060e0c01080907060e0303040f0602 69
    0x2007488590b507400050b54000e03407044d1400341c0c03c41c185640002c01600705e00e99a54840c540f0781460340503080c03e41c1d004181c0502e00510807070b0360301000340c2c422400350400c0e82c41c03143e0303103250001f6080818010b01a103000840d0003400301d4020b40420b4420380c020045500c0500c10440290350003954854980b142c0518101d441040120950000c001c1080c1d0549541095085401045901c8000c0c1d203824207a0390700400c1d02d00c6e45500e903681a0082071409545e408408004002d01c2c170b589020002a403820382c2500c400356803d00050310b01c640040902d02c020b40307000f009112000c510300d000c070740040383d103a00710240f1000100d03440781c10100040883d415405030588a0319031810411600000158560080019080c4030322654014400c0500403045892b001c6d00030740000c04041d604c01c0100c0802110103500130315062404440c0d0924500a0000c410340f0003031441b0b600180700380c030340c028801d061140180c0713402410301c0d50405c00c0883d0454040101550580300c18040410260340086510340640102c0e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 98711151 1250 98709901 98709929
    0x40f051905220c021b040b1306090207020901061b03080916080318011d09040f0c08060a18020901060e010c200316081b0d020402030a090201030509010b010819090c 72
    0x100344404582c0700e08980c03c15540701074400354494030b07400540d240d41c4000701e800082c842c0141010524800766180346501492404802151000c0350f07134003811225009440780c0340141c0c2c85000641c5c002c00e00401c22025082c00c80c02c0540020f1240c540207038042c01000c180e40c14014200d1007800c03985900c0c1c100b1403480d000894680c0c0e41d100310810800041c0d80074602008040001d00c0600c0d48801c1c8c42c0d041e5401804410000f078140101d94038107103003040d0b010040001040c0d41d60140e0341c480b0820365210031628141010003c880c984d240f8010022900140751041036443c01c6010b07120f00701981e1030641800104442100482c20141c0d013001086050461002ca0f00303021020141080000010301640f100c445200740908030b80000c1141c03003400040020b0004440a4001808658607050001e600a000208014150341c0c9904a9201a4401c4e2000d120070f89408030020309a42103d07080e44e0000c0c4803540055107a503405419040000001a400105c13031000391111000031449401c030950504100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 98712401 1250 98711151 98711209
    0x72d0302100b0108010e0702011107030c0b010b09060313051c0e0f010c030207030b060a150f0201140912072d030e101403150406081b030102040f051905 67
    0x144910301c0310398000c003020800b15005030000780c0001010702440044000000c00515024001d40c44090508110418640c94a45a01d001060405040d0080b1070902000d130001500c1c040306001e0740d1400e0402414181569108140500e80680d0641c041e58a40b10b030b81c1401c1d5221280000030b14002489507115540b00950b11300740050b8022605000341004000d08200d0b01199000c5000d03401d0b29030100240c1807a40f200400100030882c90f421007480c00b180c424140a072141c000400d4424015a80c0090201d5100019084034500701203940441c04e4001804544105007840c0003002c1441c8110320082d141c6200d200400c040410307809030b00903c21409201c3e841070507004403c154226208813588001c03400c005000070105a49801c125420500120108402d48016045400b40c0c0300007a100b0061070317540d180c002c0c0d9901c0b540600026854180543d82010381018001c440c240e0315107180355000d49141209002a940810043ca0743c90b904460000c20b0ba0f40d0b454030804d080315045042c0301902c0c044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 98713651 1250 98712401 98712403
    0x603070507060b03070e0c070303060f09050403030b040501050105220e0408092d0108071709010501051005070512090a0801060909030f18050906030f0102030f070201060b040e040602072d0302 84
    0x481640c85120340e000880404c54408201b402030341c00361822a0280d102d4000b03107000c0e00130700b2440c1c10130001c00381c10140c00700c0c00c8045070b8045407140740a56422f2205070003c600344003c0351028041ca0340041e60800142d4040800000890558114250465002517030b5800d0001030001c162000c448441d4001101101460161400c485007451001100b404040c800c80000f040001801031605000307540307000030700480c01507005c0c1c0030b034103002d5031a0403082c500209085d00134102401285d2081811002c01c03981244581d094481880e882402064ad00b40c0e4002241b1098001c400c5181d0f102c264914080fa4070002809000014031680c2c3d00814120800d103005041020320045610410110101d07600300214001407a0701169810f554180464403901e01190400c80c11201c00c0300c007580000144212180d0104042d0701c68280355000300207180d110010840c09105510943d01000845000300e80441e401e0350040803260b21030046070388000041030f03400d0407a140e4003507110843d8905264400c01c0c590 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 98714901 1250 98713651 98713661
    0x403051501080d120c0903140d080c09130f09020d03050a0206010605070b04030e01031b0801030203151006080a0204031e02040f0e0714030a0c03121706090c07050c060307050706 78
    0x38040c80504000d4100f060004d003034181c01950314100740e0320f8407501c040e414010308100c070156401c80c007210780c228a403402e1280d4814440011400042d45040082e9180c46840144e6044a100404105110030301c0070b01d00c0041c24081030303810070280c1d541c2101d40c016990102e0709140c0e28400d844003900c4074060840682403280503440304043c0402003000400203514402101d0f40180e2504042d000c0480100049004090040c1200904045030013480003003a000400e40b4101d030700c04c034110380070110400f07042e10040e00195a15034618416550502c10030380505601d9074821000c00f00142030580d40c4c0c03150320840c9211020710301d805081c0c544000540c2810300803201c500c00250421b004041409441c1c40d61207049204005a0721014901503016690602c50021629002141a00c101e40c0703c1c144040010080164080800d446a5040540c1e8010700e00c0184a1500140070003850703902e80c040c005141d0700c151002c540e54040e103a800c0c101035650601441c042d010741e90711161030b00c9a0345020000c4039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 98716151 1250 98714901 98714909
    0xf03030906240d0b04030309061505130b06040314030918010819020109050103090201030e01020a1e08040302070303140c070f050414010f060522140a0e06180711030403051501 77
    0x141c2c021501200303a00e0316400b400c000781d480303020306403c1c4c0d03550f04003180208a40790004190a081c01290070a123000350b1204003d441e8200c40f19484200c0d0840901c1c1195109511035410440c00e2000300045150b44190310480748079041a2890110440009010f401e81d13021300c074515807280401880f02060030010008091a00d580e10700b540b04450700085c0180e004c0d44103050402d921850444116442500400b00e0b084403c0020b544980e00d890010341440c40d00e4440d82040002901d0b4014501c0c0314041845c0210780580250841c2811510304aa04a08440c02c62514803020000448410400c1080700c0082484911004c80c0c0d50500d42003109650702c0c1040070b8814541b0381c00600c050803203412a43d04031000da0600b43d075150300c00c144a011404074039a200da4143c3c0719100c00100d109411414010310301c01241c00c4a2020384420714400c50b00030542e2402d4211004c00c0101c1c5a4002182c0240e8100d215405c0003660152000c1d80a891984103820454203500410708103043c10000c808014050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 98717401 1250 98716151 98716201
    0x30d0c080f0403080c0306041d0c0301180b01030f03050c030310031b14090a09080406020d080604060308090405060f031204090c050a0f050901050702130203180705060d09050f03030906 81
    0xd420283c50060403030304040e01403e180c1c01c000020030015030302c136880644014094901c240c01c0241c60f003035040d02d40540c240b09074000e50034180f5001041070b6044001c0c5a5aa111800042e9a400e54891285d224200c1c0021818031000b00054803054000b04051b6101d101d122105c0303505a0b00714074080400560880d0550f200610b011010301c0b060701c0001400c410f0510a039455042d0350360750384030326024103094003018215242c0003401184440e4085030800e00190360303031103000180d1240070500044800328840a0440802400700c80f0b12880d00c0d80005400510041424000303e1810001078180315101c5100814400e0002c0c0400c411100b82c0542228480c2c58281302e421302501d11301c0603080a41c1c01500c13104102c000181c40d200750380103c0585a106401a202c1000d0307203d0b6203461344c000d40c8141c0341d0300f108201440202c0300d40800002c2000941c5c0c0c010b003d040c03c1078126039a000c0a00801c0c1001c03281805426280500e03180304001840c40341c9005001002d444c00d01c031141101d204c0000302c8244070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 98718651 1250 98717401 98717431
    0x30911060f090a1509050d020604260105060307030c03060213080118020112020c06130807060f0204061805013c031409010e07030f0501021306180b030417070f05030d0c08 75
    0x401d5042807654040f50710587e802003900c0700c540b00042803803045401c502c099840e054080c486500c8010711003c10748940341c00030461074036032400b050ba82e4400380c840204500c0f1094010310000344160043c140600201100006244c6c44860050a58000c400110017074200d00c40760209540e4010045c000c52044600b04524101c03c0356409a1a40002845c0851000e01c4101d6403040218007012035901e030343c00c45010000c0301c000310000d00c00f1394020f00c56040010000d5180d0b5004d8a070703100c4044121380d016116040109200ca801020114040d050b503985592210b400d1204898903203c010060380d8555800900070301801c11030003c9050260034280c0a81c90f01d0001e5150020016120042c2c0b50402c80442401c1e08504c1c05902911821a0410000303801c000002071454011400301c00b2032005511003101a0384812003030329540400c540c01f03010080080b00080c12040048010402503000c2e0485280910203500e52504e0750784000c8100c05002e0341c420484075840d5100c401541c000c444100c507210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 98719901 1250 98718651 98718689
    0x4020405180601050c0f01052e090b01031815140106050a0e0a35010209030c210610030c0b03090a060b010e0a1d010602070305070303030911060f090a 66
    0x540d50703400050204103608180820007503070288098075480340c0301c81c0464400c0c07100322144038085c0c0010754200f03200690895603003407803825010500c915210440c5503044035510308501800a07082c1a64014180356903406810030540144900080c028001c540e04000c20b0800f00c4000110303842884050480c0c8020801401a540d01608031040ca50503450312442c10001c4500296071003000b94000c0403480c0002241d9902d800100e03008440c50400d030551460000f81050185090f449005203082e0300d6004107884e016289440d000179030480c80e00c1d1014000340010f4a0701c9520300281682c15240c1c0f403505200c20800c016081c04030f00040c00003000c0d42421402c1402002c3d6981e898800000c1c8a070391140300103041a48160625880d4038001001d000b886640c40c0c0d4400310b600c15901944508508403000440c1d00d5000103031410499a121000745003031460b42c0c40c220002c4ca00c480c0d04035140710070390031240c44a9490300090b05001c030201403c103030741d806a1400c00c0481881c541c41110441c2500c200b4107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 98721151 1250 98719901 98719909
    0x5150105060a05030f06010e060705061b0c0703020613030519060b0109050603010308030612010507030e0c0307030804060c05011803050c0f07140f010e04020c06040209100305100e030c070602030309010b04020405 93
    0x1c3d0000c00160b20340320a46c4070400180d42c842d25400351560040c3d004078001060000000e5124001da201c108000080b05082881103400e1003100511241c03179000c49020401030074214000c00e401742e0700090000145859640b5503062030f01e00c4168400080b420300882c400c1c06070f588206030740c0348800d0078401800d520342000305160b4041403001900f0b404010000541c0754031032045840011030a20000c114601d00b1581c00707401010000300400d1188207030310200c0c10a08000804105a81d007140f00503050034603001d400c0b180301e01c049004442554890841200d081d442c0840041054802e484864855500c1030165180c0701920110084aa11144007085000c07003044966102d00070135692070645154620050710f0405010030865042840010f40040210703011498034007540c400c560200b100d803201000075100741d540d0b00000c0c040740c01c406446244008641d02c414901c2079444203482c2044500c0a441e41460b0f4140d100750b015800c00020445420400e1042d90b40d101812182141003604002c045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 98722401 1250 98721151 98721157
    0x240c120e030a060e06180102040e1810090819020d0804060c1b0b0402090c0c0303360d02010608071a0901021e072301020307020118050a0305150105060a05 68
    0x2080910508032211151500d0500802d80b0040e0440c00c14003407940500d00d51543d60000b16101d4510740303440240304d07411400c1802150225000c04490141680758007009444160200c44419154802c16030292098103803401690140d600401c1c85644440140c1d60b101421400310100d2000c5400440d039440c0b26503000601550066000f110015603240415800c1d2440b0042500d4a40004080d803590410081500c440c18800d07071090320345000035103c940f020881401a0300d1010a16002032000503a040d50415800c082598120f1014000307110b030620005000315a25421125900328a072a04c01c0300703409002e00401021030320001c04c01c3d5032910702082d0f445d44002c0302d481e2042400003415400b0360f01c200300101c0b410543c1c18000031907456804203e59204580c0c480c00328050f000e404102c1c821038540a40c0003006030181c01070740c40c0503456401180c4040c000700c4003150852180c640440c440d01e540e810700c0040d6211304000e00e400425504a19100001640510b06c0752400300849400303580e1000603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 98723651 1250 98722401 98722433
    0x918020d0b01030b01081306200408070504060609060804020609040e0105060405010e090a0204110c120408010b040b0d060c0306170a021e010207031410020d060312030911130e07240c 80
    0x7c0480d89001c50701e4454081c0004400d102044882c00c1e41000500904200800c1141d01100407507062a65900c07d00041d00c07018401c040c0860300b04541088103a020303100199205100030000f6103042e90500001d400c0740c52445d40c5000580d541c0b41001900d09051091502519000c5200a42031404201c080ea603000075000c001d004944604072640d24403c5a02a00c00c58058001542d211a0071a82011510303040b44c8140c100540c2840c0da42c0405045c9032040f020b03203002c090910f418280242d1511400713401e0071403030481016501c10780043c52400c00d0040840d502a5103011742185d418600401000c056000c2030103221000c40b8110691583c1c0000e101000c8070b90042c121071444580102d20f90600021a030400340160001034401000809035004100b030b00e00c107400700841014007240441c22690700c0c0400500c12444840468428500414988008202600007190750500142118140082c3e50b1082e40c807040e58100141141400c0d03c840d59140c0070a14080c103d50a2036103683c1c540c087d0000d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 98724901 1250 98723651 98723671
    0xa0206090402180301050727060c020d050309030706260f0609100b03160915121503140f0d050316200a0b22020f0f010918020d0b01030b0108 62
    0x280600c90505030210080e6003c000038020030040c94407042c09400400c082d655183c06100180d040c42e550b800c400410b4054902c90340c0d8400c0000030f00c1d428072854640d44002611742c1d1101340440c100c655002c00c035400c00f911455550444170400e04003428540e10041c500d28007001502810080b4200360320074007690010b400c54040841c0e0b25008407444c200c000c2900201400308000040040c2801e07112036100d510582c0d0344d6108801d543d500900018100320009407400034017040603052104015400c400c46070351451401b645016030301d0303031a4000c0e0841d1440c0da40b4190031104464002960500540040143c503060052840c50103400381e100c4010180320190030f11001c500e602c1e06818803090202d1704500300d201114a601d4560405070030407141103407504d106200c00d032445040d1200158203c3d8185038050030240c1d03031a5184007000461203c800ca918100150120006400940c15a00440c1c00c40c8031600180d44052112184066908025406042c07604084000e0203a0740e100c280302d588002245 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 98726151 1250 98724901 98724907
    0x302030a06050a060510110c120a06090302100906060512010c05030a091707031205010b0c0706050306030307120801030b0f1303050304050a020a0f050112060305120d060803070303050411030a0206090402 89
    0x240c206801040b0340d80045030401d04001d4484021a0042d01b040140d841f440200c4007590100004c0020314000300080403907039005103104000007681500003004941c4240141d80741070075165420000c4980c08602512000e8481c0000c104605210303403040d010f81d182c28004d000d03410690401801c1c0348405040d801b03020350b8914003e018000c0b41c03110701400303640c4201d00641d295010700340180310000607052481b031103242c5000020380e948030104503a41100e0101c0607205951030b0510a482940000b042c49405010800c19107001891040c68521070200c60303259a80f00394154288030310780c000003c00d0b800c501b401d143c0c2032001c0041d10320070314129641c0c189001039507036580f441d03c2d90410a581c80002e4025800307800201d030704460001c2ca00d095407000e076aa11030b01d1403405104425602548009081c0c1e4224a01c086010012100203044c3c1400c01900850300682e1003d560749140c4c04030380e040d00000d03550310901080002000402c6100301c812401090014815000141140715508145115907800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 98727401 1250 98726151 98726161
    0x150904080a0e03010203040c03020405151c050718020c060f04030207030210050706050f33040b21100506010e0102060720070e060f0613060c0804090c030e10060302030a0605 76
    0x14a942d102201c1c0c0036000f503440e400c05141641956070280401c91165080a000031940032002c114840b0080c03004103001301108141e5040310000071409016141406454004a240020303c5041c41d148192403c0059590003040616030411002802c8000c0e000041014400400e138009a9202580e804540e844030444480a00784d40611070f2490003071400d414601040000300301c0740405403060705500d041d00d901c1001203650405000701100c40070b000d0f02c0a014a5202c1d410302c3e034418051004041d2031901c008240001c43c80d15a03512018040c001c0c0d0140c049080f280309a8040c4640100c82800c00400c0b45480c44000f03903e5a0004001400304844c41c0e010825000020501a1342c0d0202c2a094446031900c2d80202141d0180c02c070707459800794010300d421001074100407040700c00c140c46410034002e81c1400d204007101e9074102e031801a40d04c070100303102c0440d2901203841002600c11542d14002921007134001c409003480c0484041444e80b905e418410030150301c01044d0004019442a4002090343c1c403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 98728651 1250 98727401 98727407
    0x20d020616030e100e0c010f0c0b07050c1603061b020a031d100503010e100e0712090b0108061b04060e090a0609090302060106090b040627031205040e150904080a 71
    0x20f2094001003a01c107448900309611400e61200362828203190644082000040055030710343e060700c2e00440042d40100350140490560200c41c2d811940926100f03291142c206038551400c0c2c081d650460001c2c450841c10010005544202001300021403d49000c014030780d14040e46568076104042d003407001220b0329000140d5415241c0c40c038031100030310307a20309044240c500a006800901035450b002212902040c0100c4c160f0921108503840310b030f5900525900c1150031600d051b401f041003c0107681f600c00d8440018042003c0b90b000c1c00b070710401410300303151800700c1c1d139041c00d01c0d240c07031026519080100703100055010b00c000407540e900f528201080c1d102c5050300750042002da4485c041c0710b840d0600c00070802d94040f69290480300f8607540e0210301d544440d001001c9210300c3c803074040495940013919002d51007021641800c1d4002100700e0400c1c96aa13141d410303081408811000021701c00040a002066040d031a442e00015440c00701040c2506400104104020291018240a10106034000e403144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 98729901 1250 98728651 98728661
    0x130201050307081b0a03090b01080c06071401021612080f190b03030706020a020304061112030a0b01050d1b0f0c0c05120307050d09031203050603100e010603022e020d02061603 77
    0x880814459900c541c2090b006000301148801200d681c1823420000815a000086009060400070000d600c0c0070141e0b59600c1004150090002c4555001e01c072146450303046a00c8070403254000e840600040e41d0508008042160080124a02c44101824813501c0c044c0f90b01c0c1144c0300c000c1c450001a44620b0000007910354010003070002c05031400020300c0301e2000c0c0d01001034022103026031151560a0460038000d6156201041d10300c1003100b0910009280540c0e68100b60307070b18001030400e985448140d59080c1c023a1040000007040b040324415040740c041c0d03844100e01e600e0060a2801c44460389240c0c3d070b01e804110030303489064450131401042029943d001c0c41201c1d10b0981c00011541a01450300015118018511003602c4084081d2041c0d40110b00078040e8510422005001d000c03203841e0040034000602d218058800f25650300c03d00400162a03102d401c2150310700d1030259048ce40604d18100509000c141ca0450440d003001501c1a107554001400c507800440000481c1d12100c065242180100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 98731151 1250 98729901 98729941
    0x7080a0e01200c01061203020615010c0204020c070e07050f0f0702010e03100e0c040c170a0615030b040b060f0412050a06050c0c0f070501090605070c050a03150513020105030708 78
    0x1c90100a4070b91420034010051036460300140080c04083c2d0b031403ca410b4034107440100a40980c20000c000703612260482101c51000c20141004003031001c0d0f42d004070301207030004038146005920000041c85003502e1804010745c400a0381c40c03c1482d0041c810300100640c0280e1a0340c3d00600301c04980d02c0110781c0110f014211540c1b002d000c4540c4c030f4415401c03003000b4104442c00170616003e5403402028a04180c06070300064181d640b1482945038041070794000c0008020040d41c04680d9070f0318040340c1d11256121540e500c0d40c9581d000702d050701d116010081141c04519806120b1641008100b010620004c03e030b0302189d4020441c1c00140c0c80608141d4100130647d08000c20a42c80c1104018000c4551006070030001d03000400c44603600c400160403562682e1034041c89002c07910148041043c18820b02c000c08600e84104010000c256480d0701281428140c3d403c201c0301491804141d0806078203d1050b168001d89030010385005071200e07000a0020311001d00110b0401640308001000000d885141c40c59803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 98732401 1250 98731151 98731181
    0x5060d090816080301090b040b01050403140f0f030408060a0902030a12050f16050d08010e060d0303090804060e0111010513030c020409150c09090506181803030c040311040507080a0e01 81
    0x2c1040751411000c154000d0180384100351500000c0103040c00c1510a4841d1603030103850b903600d042e04644030f0300744181503803400b4001d5200c1c0075200300c00100b0074804000078090180085459900b00030b440381c103041d001004542000d191404000c0940d60028605090a40111100f4000002000d04880310b104002e9421301e0300400040050207141c8000191500780c1c0140155222a5503115044424280a1045904024549000c2001c0b86000701003d03000b10f103c0c1c01c00040400c401e03600d04120740c006a000c0b0b070100d022a5008912135170041d480000032000940200050310380600031401d000f408400c00381c104403ca590060131034a40c0c0d840041540e40041c0c90b4040103041c440b882c0c000d810f20101c50b10010f01c4410700010f501340c40c0e0150b030340101c01c024000310411486015a00030510010400c2d212504070340f4440c000c50344140001c60080c140034916540d140d00b0347c1002880c100c80c807031600380918908001c00c40f60a82c4440c0141e0070010500d00415034400d90b810f190b001d010ba4088961070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 98733651 1250 98732401 98732437
    0x306050c07050a0f0c060509030714010e03060f0601020c010906050a03051b0d06050a08070f030b04020123030618011203030b030f07060e040e0706020618150405010e0f060105060d0908 81
    0x5004900113030f801c43d01e200d070103102d0399241c0350a4115841e018028100d80c00d0b6000d1a010f111286c010321011219035010300d485155030b0034010003e0300e000410358504046c50224000d0181d1941d06211302c03200f8035028241b0748119860240000c01c03a01c141905a0100b5964030041031650b02d5918040d400489200b407456103030709c20000e80a004020340d00c240c0d40b158150560018006601240000c101c800354a005001c1901e15159540d1710000107000b20704102c01d4500c00101e0403c511081e14281c0211082c5c2c1d0f40380e140c0f0380c3c28040c244503d400384034201046a0010002408400e901d4500b1a0b41880e0210b803c808902c0820b18040d80714020000500548a002c604070707901071102c0d117140004440512007906c121300d1064a56110b4010a001030b0030100006104141031020401c00d03506403030458078000e040c404014104803041e2811600c80c1d45035121900c1c02e0908016501e8103500300d04c068442c55250100141c039078891040140507040c0c5034030165046c4026030040d40c4e5000c40d88000c0d090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 98734901 1250 98733651 98733653
    0x409050d030608010605060406030203100812030103120c02091512100209130b0108011205030c010507200105151e06160b0a0209132f09150f03010306050c07050a 71
    0x9100d20340e6400d40300001c0d203850030016070702105010b14012a01c0c098501842c0c941010400c80280d400104100410380d240c50001230008001c002c0180404c407410303030003501d950541c6000d91280d09a06461401c108140c0e81e00b5000d82c1e0794014241d007148802c00090064109800417444e031842d959000021805084403050480000750001c0100b81c60440d04024088800304021085034080c1c001e150020310800700501417000030900c801c07003990060007180d08050b4541809801c0d214126450740015070403681d8031031842c6c1030501401c2900c80c2d900003070009240078a00c064100c2c0207440c2581c03051440e40c20b0400c0c59245d000c4c5101c1030043c0a00015550280c02500065805c1c0d1135404940341d290000002d0100400d078030998010342002048140000da0100b4a1006003c00c00c20504d0031441043c0c240a144201c0c054020444205403412603d032002d0108100e207000c1d0031811800d02080030000840c600038484102d0b03064a501490004460711046d115100b0380c000c01c10010118440c6c015103030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 98736151 1250 98734901 98734903
    0xd0810230d030305160306030503031b1608070309091802092208090a081b011d0301140402040c050a05030c0a020a020d05070e3102010320030906150627040905 70
    0x14420071703e4200242c03000d201e0342d1007241140c0302403002414940081c030218040b1440a034010300d600130385000e103a040075008041074204085185040384c007040002402001c041d0014130b080001c1c07070b14060030443d8483c00a100030340c0e0002000001d1156800c0d400064035200c050a645800485021044c64440200d00e4500c0c003030360142050602c00c0c00700e0100084c01c80c000080e0380000507040401c50741507111050041d95481a0b80e0304c44c006418101843c00c0f401d4a0900c900f0102280e880d107030100a007044c2c014001100c071103001180c00c01504002c02c54026030401e040300c2e00300040e01c2d500d6a4810365040304031b042000411001794000040b806030005d000c00012000e09927655905e012482ea1140804d8524070310108504003050703001c0540380503403400c4441a842e0100c0c01030501040b01800c002207550090303e00841c2d00103c810200500c11201000c1040b01d500c900c9160300e000041d00d80000003030f018001d060503801d134220414a60a11012603100c05441c03040068028042c040142c9805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 98737401 1250 98736151 98736161
    0x80f0a09030510230405120a030f0c02120406080c12010303051201050102070303090905090708010513050c0d1707060f09030c05061509011701090c0b03090d0810230d0303 75
    0xd5959110b600550700380485684a00b006030740d0310f01d8081554031480045000d1810307000313005884a002c3d1f1000a100704400c1801090007909a550001c0c00c01402c40102c0e085609140071a421540f255018441d960b002c10102d40503a0f9036810545055540e40281c807109101f01d44251404101403000041019086409800030320300143c040b052580e00c0c8c0d801240c0e03e800c20301c00640025000700781000b0201d85a84601d4000c140b840a9580341d680f9081e07001c0c291481561a0700c100028030f02408240003050210120342e9400b00caa041c1c4400b919140c91b640410207044100054400042e000f08001c41036100b004100c00f2048107100480341410083d2450340503c10503100da01a00700042c0d40e0f000300f9a0819080c141c0100719801603420f1003441803101c001d000e04c2d08219036a90b2880c1000c01c02e0130514400510019090340c1d5130741340c52703c941401c01d4813208018041c06424414049440c0115030b00005803020000c007460143c02601c40c020041102c5e2039003039009510302d8101414154540c001e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 98738651 1250 98737401 98737403
    0xa020a0e0402011b0201020c060f070605010605130b0306090c160f08090a0617041104180507060306060c080a0e04020d050a0c030c0c050307020d0f02060307020d020607110a0f080f0a0903 82
    0x82c131101da888100500303480c0d40720148002e0058000c40c49a10ba1490080050412010307000c01c81400c0140f2a500c4d201111020f80001c0003081000c540081c24205a101e24800b802d24020340d2400d41c2031020109064100103860044080000302e03041142520301313811051010780100c0c40c688007003a6401c08000340c0c0c0c05000003500132350a0820100d195801503500490342620880c0d0a031041c0c0d50358440c2d013100e12010888590042c2c42c0c0b00390f041300c0c44010078a00090750084000d80000e40c0b5101c4007074119106680920203121142a03081d003c40e050130141e0b502c41c00c05003003d04100740c052001074001c0c4601e00d80807a00307526000034010011400d0340300e400c030f00c0385030380f800c10000002600c140c030101c8c170104000b041d6510400101005041030b4645425248c031501c848001c5111070f90000f803042d0000c40b00600144c1c450004459440e40c10400640c00c0364090403c1c0d40e41a05001150341c6070b00301d40c030b00501280a90b61a02c804c10000703c040b184014001b958060b00c4140c5080c0013041c0c54000d100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 98739901 1250 98738651 98738657
    0x1150b1306031a040504020303090301230604050106080f34090602120f0f0c030714070f0b0409020a021006060302180909031207030e060115020d0f08060607050a020a0e040201 77
    0x18001c100140070b07104000d0740c410341c00098000006040e080001a02004100f01e0b0140014440b480c0b494409005d05603030f01e88440d50071756152084030b9021001d000000c001a00c2a41003030010000c594121410703680040c2d850503018103603581c2e14108100e401c0b0384000c0641030080c10100302c0e020030f8110007001c00c401c805e954652066036991001c036603a1000c1c45507455400d100b000003114a0706e10400416610007201b9600b402d10703603806801c500310742120300143d540c03441c89400403016450511a81c40544060040c42c44102c1c14405011901e0140780900090b099000445400c024000c101000c08060903441c284400e5454090017000394100140c4201c1100c4068001c110500c1c0c4006590f1140032103400460624000c0e40003440008005407071b020a05668803003804014034103110407400f03000d442001d10302d4102d003804000e1034109149c016008022345401d50307040c43d0364005022500030301e0844005440325500c6c10194244910144001e49c4003007181c10004852140c206c000f03205a000741c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 98741007 1106 98739901 98739937
    0x1060509011211041a0f12130209010321020a050d05130906030825020d02212b05040e07050d0b03011401230108010308090301150b 58
    0x114a10301076901c00241480b04607441c90221140d800080c0b0450b21b00f1180d80080700d002c0c018032007045d01140c00c1c207001c03d244201c0300b805510030303a0300101210b000356034a19200c000440709646255a4501e50440070207001c1c00031504001c0160850060710030300104c0d6408541303940c4400000b04c60020075502c00300c2c1c1c04809200c1c0708003461003400c8042e5214512052544040003801c42e011403050f40043c00700040c2c860b1200322400582c1511813112401c0c000c10110348610030341003023104038032404000d0114286c2c400c0d03401101c4800002d03081021030740303020115454401d40c002c0120351081d19001c1401c192281e002000c000010030070000d50700e004440000c3c05d666211300b12080805000006001680310641a006000040301704690454000e40001c1c110100c1444060028840412101400d031004e4100c80d241000200c40c0b405a5030310340240c20f089170807143c0c1c1102c1c0c2404074 = true := by decide +kernel

theorem cover : BRFrame.Cov 98561151 98741007 := by
  have h0 := BRFrame.cov_init 98561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 98561151 ≤ n) (h2 : n < 98741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
