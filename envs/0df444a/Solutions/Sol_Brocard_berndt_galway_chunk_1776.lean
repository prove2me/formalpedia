-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1776
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:38:14.472684+00:00
-- url     : https://prove2.me/submissions/bc78af59-7c70-4237-94a9-8639d3e0dcc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 319244604 ≤ n < 319424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 319245854 1250 319244604 319244647
    0x5010c060e0d1107061b020603090a05100606090e19050a06051905040b0303130326070602091302090604091a180a0c02150411030f030a11010609051b 66
    0x1041c0c039050041c0d070001501c9034501032043c0080e405000e01c0070416900c60704981034451180b080309484110302d17400f44600e0341e00240c0290880d00400100c4408030350104003114001c1204d4034009441c0f40340400c01400d084582e0808019800f40b0410300142c0c54041715070100502c043c20000541d912004842c0703008110305c0d0b0025030414034031248590b039080c11a43ca541142c5080e101070103001c02c1c103010991207218440080b915428215800e1002c6051001d511030f04ca9011189102000c11320800d40c4540e401c0b010342210030755000268141c040c20f0448041161346002802503060000000000e425400303640510026075030303280c030a040c003070503d1141c5120358003000e08400b20400d9003a601300300058040310b500c9141c0307007044070310440d0303d10002e00000740c43d5203640c1405c50b80e151a51105c28102c442da411690501c50007213201405182440102542500c58407160381c80d881040c40c09003554050790001d00c5052420003000f24004414040035460701090000960324956591365400400700c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 319247104 1250 319245854 319245881
    0xd09240e040c030b1512160c0b0a020c0f0703020a1e0b0d090201230301060c210207050a0504020705100c0c0501020301030c0f2103050f040815010f080708060105010c06 74
    0x902e00003030441c2c00d41d112502d0030b142a02c1e0f0a0b100340c3c101c6442041d910035803800c4c0c440c400d02240040d41024520400c2c039000000e500c0d012038244080d0311002800d140680e0030315030340d9130300080d9540030507010802140051161005003044901d150000742540b810340c07040409074130041e2002142e5490b00050800540703074402e842a111030b094200c80c0c00404010720101e0129001c00c1c1c03403208900c113841903140b110b042803003114990783c04c2c4001240d6802c48031b501251700c0c0b5200f100e00d01124141801c1c070030b82036086a00901002c3e107010100314039042c15610043c0160302c104403901c04550041601705020001d50404500309122190854940d13a407400d003d400c1c1e52001c0000701c06c004000350036100b01c4e0844200d0002054695444600304403030004000c06031601c015248002902a2000d030030007080c092012800d05c0c0c2e844444a0810307000000c02480580c0a1005010321900381d2a03410151003010000d044040c10b080300c0995480040c0159810303c03541e0310211040000b6074000e404100203d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 319248354 1250 319247104 319247111
    0x60e061e092d0a0509160b0f0f0705010b040b0103020a0c12050405090f0702060c040509060103050411040906020403060c030b102f01020702010905040b010e0402070f0c0806090d09240e04 82
    0x403200e0602d02004141c604061030380c10300c004500f11160000d141c0384a555000e44001c401490066040200d0b40b03e4440219102402e009107180c2d00a0a030141814500850000c1014203c070410881100c0b419094941030510600060020661203201c0000d0303150700001a62040014440c02d0300c4c6801280d1106601109030010881c0347c40c9002501c074041c104c0e03902102c00c1510352000d6880c40d03002d039008007034100399518000390f001e43c1b007900050381040c061040302e0001c0b1000000718003502c110702810f45201ea000a0100200282c0c2d00c0380d045601071600e03040040005610003d0003d5100203030034810000b074640000441394541f9500d00c1900d014000301211503042c0280e07107010750450340f0140d021074112400003400e801c0c0b41c0104d03005010165640c1d0313400a941020403001390042d20042d0741d44014202450b00049a075485a03024005404c020b003005d2078942c2a0301e2030484c0e0720034031204004290004000c10180a601c3c400ae00e00f00514068000740c40404c101c0d40d01c8880204c0980c002c0c00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 319249604 1250 319248354 319248421
    0xc06030c040e0105060a1706040e1e060a051006080a0f020d091407080304120609020303040303020109021c020a0506070821011806051c2103060e061e09 67
    0x45800040c42100c40c101c03078402c01a80d8070b404000340c6001e86030444001c0341121600511000000c0c62255010900420001d000034800400c10300c0d221991180101c8100030f10b0202c191514100803056110041110600551504890042a038403007841a0018850100c010038031380d00783d0360000051180c1d00c000840d01c41c103200220b14060000d01c041501c3e11400010400780707228002c900300c41a078409030700071403a1524242c148040d04480c003e00341c030000c1e07542c1e18040040c0c3e000d10081c00114029400402c10704c1c1140104010240f28960700c03603c02c26071450240060310789038400d400304c1d10101c1d0050f494a41c02e00300760400388030700400c44c1385075000c880110f081182c2c4445541d0680c0c400c410480341c040480000072044921600426038400c1c03c0140309502d20b45840d2440550350312512201d040c1c80c1440500480030021800d10101007519140140301c0780c95a564603681c0000c0443c1c150340c0c40c0001c00102100c82c4035006ca114003c0c0b0b08600000c44142400003075816015110300c20810004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 319250854 1250 319249604 319249621
    0x12080c04030f080d060512061803040e0108070503070b1602060d0b1c03031a03060c030a06080708030403030201140f0609040501060b0414030c012607034d07140c0603 73
    0x2e03c0803902c41e404a05d0400c01260340d00301b038650f510720480c00d00d00030b00d541d4440e8219000742200c0c14114103800e200401011403500a0851800d0080c000540101001402c000415041c1040703078004020001090220503c0301d500004203440050301560300b1551b980d440310919002c0d20300350401c141c02c400c03200c1080d245130700701c03c002165040c020f98040140c2660205200210002403a20741c3c0c0c558400b0010840c8200844020f42c0c0002c0036000000b402940c500c0341e642003110a0784410400d4101180c10002c0c5502070140d940000c1419490f07042d00c2c544481c1081c01e0350b402610b07007401b5484e1440000c4c01c000c0d007580b00b4405002c580000380d844540d1107030304464000301400d036640280101692081c40d9401840c441407401c4c501844003030301381041c070848210440300a11050405032203140d1011200780c8960000060041401c54100b141c041401100c4c4058075142071860000d803002e106030f0380000381d1003070314807295210a095440403e0184402d10385a0811074095008100109001031103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 319252104 1250 319250854 319250857
    0xc0f03060324061008090a06050a020c061303170103120e010c06110a18060c030c0c031a06010f0f050307030207020621090f07050102030711221e060312080c04030f08 73
    0x160b0b0100c500a000c00d01c0c00344d0440c1ca00d1003e5410b400194072011030b0200051881d0811a4440a08100181482d00d03040b02e03940f5081d01618a240d55101212040040c19070142e01780c0034060f02d800c070701031403545141d03119041d0400b1040725504109540340c450100f030303110700040303c03500f900070740e003032050007102c5190401c0c0c0d030700c04440c050100f22107800c186103200c8490310840407281c441c0c440b00c1c2c10b1480c030f443c16903944003024011513816000b200e01100091150903840303120240194145c615161950002d00480186080c08040c009842c90344950315034010300b1290b10519515002d1707211000d0344045062405511441540051110400b5072007043c0800503911503c003d404075100c50020207901a1540100d00642d0b00582080113654041040d102c581022241c000e0900b0032407805500c00b10340c441400050600009450b8061151002c10100c0c840b03001040d0903a040080718655500c032998501e046409500f80816900099003520ba03403010ba0300103507000b100e1201e04482d05e01e80311009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 319253354 1250 319252104 319252111
    0x40308070e1809010b01030e1b100c06020a0309030e0402090a0519080f010203060411030405070e1918020a05031f051b07050c0306010e04080909040c0b0f0301030512030c0f03060324 80
    0x40c0c640b040d223408090000594484003244540d4600c4440301080c1441b44010100618600b800000044030700014014030044c250240b543e5000200226507141c02130418400703001407803190303006009800c1250748a0500b1001c483c411100d2241a00709204005984049035218088034041d654000e4002c2d40c040d0011032240d0000c6408104003891983c403820140010f0301d0203000e43c4c1c0104801d22140c1d40710001540c020801e001c10403404035000701e00c001540c4072000c51180e0f00d0030362405a000c50078003000040c00340504801800b03001482d00807064030b4811010640301c01ca074580c00451614118442c10301184a0016a099581d40706820080d42e40c7c00f8034000103000e80314160000900c5896012118011036014090310714069159040100d640f0f0054820b540d01e0785240c0000440218003401412808248000140c4961441c00e000303080000741143c42d4040f01080042040c41070308c949c200c1c0c02c0d5540d03141e106134507900c411000c01e00d042c0c40a012104070684110b02041030340340c01100d0034030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 319254604 1250 319253354 319253357
    0x70501050f0a110d02090a0f031a150d1106130e090f070e04030f02012d0501120506130c081519060b0913020d050f160503040308070e1809010b01 64
    0x185070711080071103401c072091004007003210752044c02010103403101c030f400901300101c0060040e0300381512102111185980b030341c000c03500045010030710015900701c0264170f0380c04080d0034404080d007a41c65021410000d07045600500c2c41e04030400b141407660b01d0109889000094518010045071680f0049d40c642030151209903a92103003c0341300d401034000080304410780c0e801c4010001282c8840d5410340301480c4c8c40e5000010b654031822142c951845c5102400c401d10b1080c03c610700030700d61003030980003242c01c181c0042040e50012984c41e40481c0d0300050042e08040c0c2c6d1550940c50180c50708107a0208110358000c442280141d82280351031400400c2424001c4e110359504c10352405080001804880b298490800d4076101844403117074506e0300800d203c48a803c0c0c03640242c03902140d01040e8084510032903915401e041d50306c0078400d080140c4a0030101001503030411a2450805440180840400614007010400943c009a8540d100c040c07100d002620211403450903403e00340c4460740603000740441e260 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 319255854 1250 319254604 319254631
    0x6010e0906090a0317061206070909060602150c070f17030a1a09010612020408071805060102160e0c04230405060d1a1302060a0f080a060305030a032007050105 70
    0x24800701d0081003d02034143e05450b00c021101d411141c414421600070320265100c4040c04060106031824810303288107900319564401154181800d0740b00700d840320381200085620101880c0303003032002c500c1c2007508202e0a0720010313202c50b01460040e940b01010107008026400e00b40e034038901d04034071001460058501900130304c090541c40c0e01e0411240d84014090380c1c481c2c01007004024050240c8502e10041c01801c0002d45415114000941761804a600a90354628a044820349451552140f070360403110910190017859000300f061181401c1134020142100d94841c04614042c000004030b034020720030300c0003000d01c091204424064080710080c060340994280b0300000da1901e03107044e2000219520500b04144104401c1d40001000c0d802402040010140c1c6030020260796668003820925036a0f54906545101d9190000c0005d038000d0802c511890505500b44005540070054501e156024540020b0482e010030713107040510148680c0e00940b10b000200308003801019041240314100404042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 319257104 1250 319255854 319255861
    0x170a020312090925181707050a0902090a060f02010912080a05221428060e1c08100902031306050105120d0f090e0a0f1b120b1206010e0906 61
    0x44001100c1035010760608800c80310100c0c403c0d40940070b00c1d43d1000034010a05040ca80306c078481602d46240d001e1105041c0c1c484442048145031018165000e444a01000e50a00c1401c00c0487c41007007180c0200c1d818482001c483c800518804d5000c7d031242604803520218400c078041c00605520b600f036078810015802d001c0001e5829030002d20340c1c4644407503102c590349040e9803902c603020718600da80c1103000140103032120144410344070360032025007070400107491028205604e407443c2100d02501c40003030150400c80b54484210140d0130b094901441c030b410304000c10f0307840e00b0f01c526010940790000e0543c10302c0401031046000032010403584807403060308104220b0f40c0b11810441d421180000c0951036174403844107903200a02c948998202d41d44541022124140c4600729402480021612441c48aa580e8408009084140034440440c1c0d801c40d1200240d118030007008041c480b00501010007039444a54024054443d018048a1404400152006540c4480003044070a0040d40c454080e0301c03907a00803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 319258354 1250 319257104 319257121
    0x29010608061f02060105040b04090606030501140a0504050613050f01151424280f1d2d0a08010c0f05040806040f02060d0c03270804170a0203120909 65
    0x416500b49501e40060802c3d030704c0c010070440540300d14011030350800d451703401d0000007540b54011304000d107101e0400454400d01c03441e0840d04280005000402541c100360601000c5030780414019000809840b05c5a40842c180c24914504481140e201d1a03d41c0f800000c410340004020112040e14a1450384a2074100d0410411140d91130074180f2950704c0b4556000d0f00d107601618001030070541041d21503090100b07403242450303150070b01c258100d10105401d20658081580c2c000b00341418013584110036810480041c3c082408401010000c0d121140e0640c0002c13940000c44c02e040319842c41c000c10510590b03448851a0340a000d01440040200c0d1201c2d00b41c201543c081c1c42614180c0f5483c1008154642e80c648072000300c4401400240c0e004082045001c00c000f0190040000c141000d440108142140c1c0c0d6240e103803400d00102113000c2c054030100210010f0108421502295100c0c200381e11010030031041241410350046009506100e8407107615110a008405070003500011140760b9540da684059 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 319259604 1250 319258354 319258399
    0x30f06060a0b091f0201091704050a0509010303050d0b031e0a1a01180203040f0c17100506010c1b0f260102310302030712050c0301182901060806 64
    0xe03220752044c00301c5410b48944001014444600707426100101c0c1c1c0128a80b610465100c089048200c03909000400f400b40f400d004596400410040d02c40b2061503145440c014101c1c050340c80390400300c40d00c910351601c0f40da0f420440600b40c0c0d0007582443c2c01da15002c0a1865031608100011114968100ba181c00c9070710580174881d04944801c07140c29191500455154025440144211888600301007440701140d2086041c10280c520b081e1260308086050010500e40103100b86040e99581c1040f040120700d0f6448009445104c1c1c0c08030082c034031200c40b01c0d81d8114601203500b2511074500030003400610020300c001800d680202045e40a500820443e0200c0d00340d01c18400c43c51858140b400c80c1c00c441c1c00c0c0c0300c0d4007802007100025000c400c0a40720b0b0300007070508250380d1050100500020b01e800900034180000c6041d100201c000b0800c083d0140200400c0b04481c0310040e03d182d94092404450a101e803198116980000f510322140350f0b1240c00142015000f9108503018164046060000504000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 319260854 1250 319259604 319259617
    0xf0913090b010e1e01120209161d030102040b0c010c1b050715020a06060b0301090c0801080c010e03030d020a091a070b0a0b060d09080703080c04180f020405030f06060a0b 75
    0x804140359a0f00745000d1000c05480985940301140c00400da0603450510081454041c0010411191017898540104120b00e03001801c01404a2040824080001d801040307003088501991381524141310107000080c0280603035400101240e600040f1800180c006511119080c4040c0c0c6600482800300f17501600c0000803544001c200f81d100d22814418032b1140c2946082c1502144101c4040000950350003054448079400706500843c0840140719080c1e0a01405d5881d805034580040e4542c0b400b030303200d5650b03280511100d05105101080e035035662014001c6030b40440c940401990b980520100c0101043c4151150b061007240c0003000c600c88103003003801c40708902d070402040302090f103a40000400400383c0c4031001e580200d0400075041c0d03250040c000c41c2e01071401400d0ba181c540505042c040c0c101c0c0402003031483d801c1d004102c00c2c0b018000d60180190b84040c0b100c4005544003148803000020702c1103410950303161294088a092100c000581d01d0b12071502900e5002c081c030f5072100300c2d808a0041a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 319262104 1250 319260854 319260863
    0x2090c040317030a0b0d0c030c05030a0809151215031011030a05071803050f120a1202030604090b012c010f0315140f04030e0a0b0304060513080f091309 67
    0x2848444060b18079102640c0c002e074100c000002c00d00300c003000140c1c0410f5000c4080300c1400d1000401c105200300c200b05240144030950103040f03a85460b03038404c1c0052045400c031a01ca1130032043c3c0d45a10b20003d205441c5c0c81412504488103c1c00c104600c504000c1d04035403024441d1084071520323504400c0c103009442014407a09400b60039602c03903041090107810000c02441c00c00030410080401340d04040700741c0000f10301840191440741c981010350703400d00440ca140c0c0080c203401004220700c900e0340003150550205140d40c0068494440c440014081d102a0310086c0042c076624002048000f00d80103255026928814501046208001c100c00c01c00001d101d41c4d4620b014010042022031001c00440c104661503044c00070b01c6c2103004074103500e40542a03d0961900304000100410075402c0300b8661180101100d0f150440c41c46c1142c0c1031003a200c001c00041450b5103c5000c154003611a4080410f120317802104162600c1d402c07000c10f0742c0c54009440302482482c0501002444500038882c289515400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 319263354 1250 319262104 319262123
    0x405102d0e01110a0f030e0a02030a14030f0d020408010b0901080705041d01060e06090f010807140d0c06050a170402060921011a1003021903110d1802090c0403 70
    0x19440c4000410000819030101d5480b10b4942400b1551036006012903800351700d80d03005881203924000e0881d0400300c42c1104030380c0142c0d940d401603680040d00c1c44d08603074442c04034403000f100582142e066000c1c01181007440c0d40b01250307036030f64201c058020f0001d0301d450340b000304035440d41c1c4820001c01d0902885100d0894009480601560502d500140180402c0c4070402140c0a0364074089400c442503035000030039480b80042400a50b00d4000a43e40d080b00c4950064100c6504082c40c0030f89841c124440c402000b50300c43d51070103042d105c5c41d800358070181c0c102c0010300b58250f4442001e8a141e004290140001d11750504a00da085024140140603d0300584034505119403c0c2c02d1041055a4000046006043c0800031181c00001d00988044014800c0c1203101005d8200500000720442c9019005044c018043e50010110540303440003007038400c0c43c0200d0102e54000d078094a43c4152080f00594509101406810603031003884180102d100f900c168a10742da44400c20316807030040340802024070b442c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 319264604 1250 319263354 319263431
    0x1703041509021807090302090103060b01020c0108040c23060c0f0c040905100b060c2b030501080604030c061d071a0306030a0308100504180c0501030501050d0303051e040510 76
    0x89229010303504c107055050051050351280c000456144003648100d8000340c0340e1a40c00d609503814065a02d01314400e08100f05a0f003840d41d10556132910382c1c003d44440c5003005213082c03031660701180e048131480f00c050101961400310190784c540326000d4240c02c0c0780a200b4849090441d080c03511a040016400c03002034042c5940741207214001d4248072035125030101d0b09000540301c130502401121103002440d01d584001000754080541c02c0174540081405140c94540100500803011811591040d410704c4e025203000100d00c1c04100824000f598000359006188444103180c4001071504156a200e0402007400b10500c049400701d40310445189800d0742050415000081c000c4119903080751105044019142d200c1c404201182c036080420079150984401c0d40d001c0c000b8244d090005080f0070321f0140159030401020030b01d4080340007002800c1540e6400011120000d08411180c9160710800030b010504260409503504c42400e0786002d0749502d0f182500c003402c1c450414004090307071000300001d940c06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 319265854 1250 319264604 319264639
    0x60c19030b03070305010c020303090d05040b0a0318150b01111b21010f0c0e030106031e0f0618120302090906010311130905180303010b0f03070c170304150902 70
    0x8481c044075010b00c1014408030008030203005020200c0202d034021074983c03402070b41640c0b82040b0f00e204c0e4018400200402d203d1140074408585c4901c440d8180440c028455102a1400c49501038025003c40b9911659030230b91141074005010610090742c40602d202500c40c02c40340c0351101001030181c03644503487d40d80010b00309030074407080c1701070054900a11514440c2c441402d4480c2c1d80880301c1e2003039075003280000a81d00310303e0704045840141d0003008240e0030350350380d2164103100a46042c00608441d05150800801d21005a43d0303e600503400e01006020349070780e0224900c55002140c000f00001e602041d014800c0c4251511008014015a01c40c0c59081c0150020b11101e440d0004031001044028400c2d404514018024011520005818600030079450b0300e84058050003812034000304010411700d21480d055550240da42120b1550b262210700e801d65031021048070043c044101e843e02e520200240c10702851243d07024885c400340b11084044240c00701d600c1c001000354031a100388801da243e02c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 319267104 1250 319265854 319265861
    0x151a060304060504080408030f040f1409010e060a0b041502010c084f020a0b1606020c16080c0306010509070c0f32011103060109090203040305040323060c1903 70
    0x42c3c050400149055107c0e01468116030000111076014640000c0c1088a4038003040542c0040c07180d00a001040c000d48070003d042c408044c49001156040080801c11990300e061140d80100201040a5601d80da40c5081e101082e14a98214004d9407038042c0d0510781038001e160451198a4103200e2112203180e902200301c5820380d407254581c12000741c8101c1e280d8000707001504003451005554100e5601018410484191996001441d440e00c00740041d241203072a0b080403103c4d65611101c003503190100000b210b40b800307211084107201d8213102440090400c0b00070401841555068080d2201d503030700e807000d00c201c42c2c10139503030400003030701c175050403008504040f0f08003002130721408443c5052070803805042c0c40440c5008204c02d801070002da005038946424400c50300c07500c10910340103066250202c0003804005882c40b41c044000d0700080002d0401d4419004c8070040c580c00300700024149000c9008900440c09018030000a02c03400c4081403132101d02505a80c0e580340b01820f6458140c9c55220108c019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 319268354 1250 319267104 319267111
    0x503030106050d1e1406100203121302030a0c03060b03060402060f16051606031a090c0a02100f0f0e06150103020a0e03030c0322060c0605071b151a0603040605 70
    0xa41d960340403c2c400014010041902d034410240c0c040341510718035141719011107010340813902c07880d4298644840203402109481d04505048505076182d9a00c00202044c028000d2000b545070288001c010100030816407480c0650380604003c000001300c04040c16510201600c000e9030086051240d086441480e50040030100c824101281d83c40400b903444a1820000c11484084042c48107814424140c1c9441007403c145a14010110f01c83d03060310200301c82c13030030181020450200000e040f04040307008200c07051440401e84020400240f00da01d41c40c0c0141100c0364819806400d04510410503040065070034050301d480300708460342d5226000158000e6015001100501400803c0d001d102c1d5024400740860000c10350196070b4940b0030704801d42030039140c802c01c071205400040081c0b03e4035902c4001264410360001002035541c44130b050a0b600301b654220b1000800a40d40c01d010304000e05c9005000d441a05000c06000e101c20340d1000282e000d200e800301640100341800050b000c1881da4001030382 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 319269604 1250 319268354 319268377
    0x70609020d060606030b030c0603130305071a090c010f020318010e0310050c030709050d170a140c0703030809070302060306310501050a1a1b010b120606040f09050303010605 76
    0x100022942e89906070b40f940d034013400110741d66018100c0103050500140f00700f0081147d13401d00e9031408000f0480c40c0004030038041c00b001000b08418003004451084400c4c86102d110903007403145048102c803680c50000210160004442026421700c0d18000406d491030b440c5d81c01241a000000d0500440314582c0401c007040e418491070031110000c440511509015205244410313a4a01d041c905c0a0480701095102a0081400c803100e6000f207040c4410071510818001040c5030740c0c41e00b018084940d80341880300c070103502000285081c0c888900090384021039102c0c0c2ca407801340c1e60b5228206511680e880c400a034002ca400c10000382285443c400240100d01d043c202401c03983d0030a00e40c05d0441402d101915130131941d440051065190030140c40703000f018044000c028003504039034090824090b181d101e615041c00390152000f07152080d00b0000e0403500c00f500303d01034074040390803003031350f450041c2d896900a614103501c03190039000c2070041246031f64001b001185542d103401c4089480741d115426451 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 319270854 1250 319269604 319269619
    0x91205060a1e0f06050a0f080a080a020c04060803091801080d1115010612200a181e031505040309061d0603040c060824040908090a09021e04030807060902 68
    0x5a0b000701407003180c0400f80d200c5000035041d42404244600184183c2001c0751402001e13504000806001802c884103035440031143d900c0c0e80320000240c1c40d007101d2420042e40305003404c401003010b40d0004007034041d411003250b442c0100100500d0b02c02c10030b00c080c021030019030001c40b512103510340201d50324400480a0811648603a8000c0804d5401c0c9000b81c0040d4002040030150110ba40701d0f13401101407501916a8691028007460000b05a92041c131110724180480390451a41c8540e125013000003c01039011002842c011079403004031010724500080741d9803061030200813040034070b83c07080e64861580341c1c0752800d0726403e00000f0399451055210301d04814101c02d003510500d4651901030343c081c9200740003e000d0b580c00c11601400c0900c0051540c1ca821100d0103d400002c03403040b00c0f0520a05055070b0006030420f01d420114018420901e29580045e089440041d454000364018030355144601242d076640310400350302010600c47c620000e27205003414066040459129442001c807644024541c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 319272104 1250 319270854 319270901
    0xb100f06110a0b01090617010b0d0212010b040e031b0a050a08030c04120804180c0e09070210090809090f040b0a020f071a010509010603060e0406090203010e1606091205060a 76
    0x1903c06a0240c000100a5440700130820500300041500003000040701c0090200110140124101001c90b0a02038425a00c030400196101070a5016010600e0042c00501c01290114032840d502d034401302031401e0515220494401c030f00c802094001d4590b9012001d0300200c41d250311074071243d0b00041c0200c101c1c2c10080000040002c9011600242e99103d200d401e030320340b0b04d4016650080030160007001d10507820401000c41c8607600c45000d030f5a02d04120380c581c005440d80300c412450603440d0008680160f00d09510710080c0600c807800741041d0076040750b200c003a81d91100b05101a40c101514001c0100070490701043c954101a0050324a0310000172429080c068280c440c3e4051910b8250b4007150060040c005200b1410300c1d05e0168007400160500f841801d1a1070825000c0c004010300140005503a55091421558217400200350040340104440c00b02d0400c001c3c000e0040814030406012500c8180c0000d0100c403421100d8101540107005801c030303680ca48001101a15140d854640c42c0a142020b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 319273354 1250 319272104 319272113
    0x30c1814040b181f1d04030309031b061506111203090a020a03120e0109050a06030b040207061d0606010e0f0f010c0b010f060801170703080d02090301020f070b100f06110a 75
    0x4911070268242c1c0004442c04d4100703140c040c28002e41041c0400b203d0680b81a040511486005401a516240014a80c00726007411a0310b0310000d00000d56400345c6119980501507d0f070030290b110410303241003911080d41d4207415203102e140b074044980c0350b8006081450704039140401a591088000055a0b011446917002940d0b051040d081215850010300010301d10b9039010140200007202800d04c1d0030a1402c0c01d001403801d180d6840303488101034848048031043d03181e54041d40d4841d50b1019060081c02401d20705001590096507012813240b046100040c0030758442c0080307803a10100a41000c81540c10941800340b03080700f481d0b07d6414440401540d100007410520828020861140d20440041c00c00c0d100078020201a4400d102d5070b0600d04041c00b07120f20110b4100d007100d0b442801203a44a1038035102c03102070b010310203605901d9440424800040b104c40300080c52803920888072100e590344c4000c0700b01d200c1d5031503010355090a1100042848070030f01515000c06400c15820031111500ca0551303c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 319274604 1250 319273354 319273399
    0x708070c0b0304050c03070f1a090d0302031207020c0904061107020316080106080c03032203081204030306171b220c08012304020304030e060a030c1814040b 69
    0x1456601030004100003e00c007045c0109030122000720080d001151816006000d80c02c01405500c080d0380d2484002c1c004901c2090442e40c0c034070b00c0504002d85c1540319050181d102e40240c5241d02200f444c8400180035244049800d41c1c00c07540c01007109856032542d448a000410201c2296100890104410805070740c0800c0b01c0410340300050710041b031150400300e03030b2829144c1c1c80d400f070155035002d044d020031240c0c0c01005950780d9101011000350b40e88101d08104c2c070740d644540e0014200303034000200610548605912103100d00e010b41c4060011554074100d031519611000c110418581240d03044082000b05d41e140b41000c071314000c1c01400400c600c54462184640c2514540f08819a1001c0b00e01400b9003083c211801031004400a004009012442040210601101500c5681e00000042c00c05005a04841c814040500020b40302e90768040f0180042107483c0002c008602804c00074240440008088400d42d03001e841e514548041400600002e040040e10341648800c1d84c001ca020000d071f0502 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 319275854 1250 319274604 319274609
    0x3030406020a050c0105310317070c02060409050702071a0a0c24050f01151d0a1505030601110106050a090f1b0909140402010807080702071e0513020316050708070c 72
    0x124503007080001f0001005070b011440444000707900b2030103030410220740c00c0509548900840242c1440701da403004030840c0c08100300038000354440307408a0040791480c0940c0c841c0d8462038082e002c961546448491040c03e0008401030205088800c20404202d248141c225040e0700c0d10501c079a41034103183c0c5400d84a041000c10b20928079070f58035410000318400e040b030300d10b00410040041503502201120001c1c111080c1d11001c2c05108000811104a41c451708447c80050400c110403414940ca42c04005000f0360050b0303081400a20700081101c02c941041c41401c045400c0149665220f03807410711340b54003806240e0248105140c0d11071100b00c43c00440c005840020001e5501e000c0d0641c00c0c41e054204a403240c5030b0b901c0b00c40952004000050b40c000c644203810030403905040c0311694444508920b441030b90b402031040110f00c0c58508011811000300318050b24401c86100320710050300030710007040b0f0008403a204416145891801c440a001d1401440400d0003a01e5a501e840b00700c0c0c44000444200d036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 319277104 1250 319275854 319275871
    0xf0c0d03030f110a1215062309150403020102150130021002070e0f0c0a0815040c03061502030304170310030813030204061e0b030606070609050c031c0203030406020a050c0105 77
    0x117181c0304003001c0d8540b01e22405c822800c401c042e2030508003c001042e03144001000365800491000359425130695200390740c50724000401000080c00c500340020282e4011340301c124007510851042082d034001c142403d074165130040401e202c804042001426411403290028050f425180304405c000d81c55081d0700840c140a240c005003d107a00d010305a11a84000a201741d0080c003085090145400b8401c00301c40041c400c52070301d40d10f1511068900030301c000c14034007051744c40751034041e042440c50303010741207070301104c0c1c40700c085000341401a58140e8480c0710407140100103820b40103004030180300b41400b03103402505540c82070b2209503e03640c801c00968404038511b5400b0120310741c2041149014094000501417814034440703582c86400e500780410141d4007030501e0340e890200018502c0d4031041c040d9151640c100c002030204024bc1d060140d140d00b1880d1405000c1c1c003c00354200c0741d803501b0400710b40141016600452641d650b0b901d683c0002d40207900f0080030018204150b00380b5150902825000f81041c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 319278354 1250 319277104 319277117
    0xe060c03100e07050a4407020d09090c021e1506040614040506011e0509120106050901030b07021f0b032109040b030307020916020f0c0d03030f110a 65
    0x1a10070000004158030015451540a040152255106040e644410319504126855000088111021a18103120341949440d45405840540c1c10440d4100358045564030140f81a100c454080b07840d017294011000c00305048550410203425540d11850212929105499044101d4040410040500505c44890364400541584c021400d8070955801250881e81000031a00c2c06404120388080341080c1c91040ba43e4100080659018141c0d48584042811b040d004080c1c12003006491900100040e9000e40c084e05140f010601052044c0c0d029502c0041101050f68655620310900c1e01c03000b4062421801030341c60b5410844a10f0b00410882441d2038400f0488810400034076261083d03040b4078540b86d0f10341046826038401c03608104c40700c06506a6003c11041b6002d40882d155100c1c0d074a009403c44011000c00030750f1101c041007000901030907401d803071006a01001d2940e5a02802c4180c2c1e60003848004c010001078007a901803048a100044080b5840520300e01c035a0403504600c0000300072514 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 319279604 1250 319278354 319278361
    0x40e030a050c0f0616080601030e0d11070e01120210020111181002070e01050609040e0f0105061903031205070e030d0e03070b031b0c07080105241806040c030e060c03 73
    0x81c008060b01c3d1050b1801007005140607100c0900002e03402c3d4004040c00444000f15100364400c1d00025060485003046071a041c1c0003100013020850041c000807614000c090021940e4180540381504aa503450130700c1c024030704540c00b041200303140100c19200795036984c01c0701050f05949102505414604000254102100000740700d06c1000f80c40c0d0000031034000c0d02041c455120401c0303040d81915030a4460a890f110490b0103e00240502080c1d036032148a4280d040c0e0344135070150031981c4a400c1c00d0702d031010302020195100040f00c0380c6000007004101419150f80245143e03600480d03008660780703031a10300c4080f15800709081107441d00c03d10b0000382c4a500e202115082c200004002011805449840c40c94040502980c1400307d10250350141000110900c02034010845540645030090003041241880443c604000f4130700604c60304d21031003000c50088030f494050084c2107003d1103414603881c16541c250820000748241d0400001341551031601000500080005501ca555100001070780ca04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 319280854 1250 319279604 319279627
    0x611250603060501081015050c0303010b0a0e030a030806090406090b07030f053d030c08010b0a050d0f02210a03030902030610050102100207170a0c03030608070506090f040e030a05 79
    0x40280d00141c4c140840b850600c00c607080c24428160490310349100343c48848035040c900f25010312424517482d0030391002000100300c503600c070b030002d14201c0c010351074401044601c00d0505481d02d0700300001501160107080090100d04090702401e80c418802c0e040004e4481c0643d40c1d80305511070564444c40004ea80ea45540c1c1003250f644121a048203d01099007034407195420b080030240310035400e5140140c00c1440d07022502401c2500e80001d0b5030f2043d11004445e40301c40326a8000c14a01c410780b0b11621070380000041d6801c0c040c180c2162180c1240d400c0d000e0343e0030398003480b0729020303002d0b130001d10850f8441401c502c4d40424440409928400e82d40424000b0190040502c2c080d80a860b55510030100340c010000d507a000518014100da0030740001d600c030990360030000c0a0f40400c0d90358180c4501d002942e42071346c542c090ba506803400c0c8251410070159803a5020300c0d560300c0c0d2a0003426040382c0b080051039840e00e0480d00f040801c1100a00100e140d41130720050600b1500004188008914081200307910071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 319282104 1250 319280854 319280861
    0x3a02030a0f050306030c041a0301050405160b120a0c21021201080102162306070806100201050c0405041805100608070605092b0c030b07030e06040203070611250603 72
    0x180107602e0201e08509010000a484400d41424240303d81d0f80c8002c126907800000d681038410341c00c028002c114502d460709140c0d4076040c490401418a81c0110b02c080348686504061302c0707031b0a440040380a110754070910007800410649002806001284c1280e50840ca503942429034007020441002d605c90270641c40b03001030001c0681007000307541d00610a9403d45000e68030003814454105050300c2030483c01c141c441d840050b00609185c0389004071803c1101490300907020380d008200568040302c680c03e01080c12400c0b06e80664500c82102010441000706150682000b40c141089580501e02010146c1d1100d1822a070b01d0460300708940c40356410005203a0500980f00109040e05100e4600718012001810681001c400b121441000781c1042060800c2041003d03ca203611004104c9003d440b4100401180b200325003010000741880034010b500c0101140f114000c9034050010010217007400019100c0c500e03814102807007441600180a01b01e05410501c01c0ba442c1c01903d203a4141c1d00b4104001d041c2e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 319283354 1250 319282104 319282127
    0x1e0c0411040509040b0612030c06071101050403090e0a06080724050304030219060b10030f24120515010605090405060d030503060d02270a06050d03023a02030a 70
    0x5290140820041611903800c40f40c3c0c0a540040926440e83d5110001038078a4080c5059101c2c52001040d2080010000640280614a0f40d103901680c030040c0380c0000d00341d40b8201e40040008406440400040d50820070950b0080000740e00842e640b91a10405882e0580c0c5500c01902ca481d6140c02071100c85040c6404c0004407aa450300e070340313503180c40c1e02e0207581e48c1120301c000e04000d611903a101003400301680c0050445100101040801c0e941b4810040c050000040340c1401c4618014030081c1d0649100111034441e098418050f9101c1d2500000c1950000400e1065955000305203000c00007808000020780a44150b0711001d03200d09600c800d0008507480108101e001d91502030310035000c650001e0589a00545c21150700c1d0750b42f41e00c1d02c04910181201d02104030203100080440e890b040141c50110322440e4074642c1000700c03940d5001085545000c0c8080030300560051422203418400c130110350100300544e81d40141c0c3e840700700c00400c404d049540f0300700b0380181c00109403d001554401815001e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 319284604 1250 319283354 319283381
    0xc0a230c060133080907050d030c11101d1309050a12020c010e040e0c04020307210902010e0607050708031902061315150e0a02090112180f051e0c04 65
    0x2220380682c0f45850f00d201100c90400c14041803a000a440100810400e4094800071b081c01002212170714015110b6803a01004584080c0a802001e4660038401c0b003075080303a406540e6400d10b850074524100c80d81c0b00184004c541140e006072100d0004d150901800741800e2144000b00f0354001d59007041d0001ca1808981041150081c002c000840e80e4003001d10003202c401200c002444510410240e86000d0000c9030198000d4004410001116004042a00404201c0c0308401000e10501c07101e41c200c485128009000c500c05140a1100d41000030181c10864801c400320341d58252501c217114515000301da2108130701c405050460100580c1400055041405410503020700c014030ba6440c41c00070180d581c8101810b0748c40d01007512580000d510702d8010004000740d4001420b107031156401179030042d01c12078045541030b20381e80015078031489510900d04c805040d00440215680c0c5942408072040800e6859100e140f0b40d000c6108203030500518050f101e040100100b400b14000d0106030340b40b42c04c500c00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 319285854 1250 319284604 319284659
    0x1202011b080c100e060c03070c060515010f02010207080703031503080f2503140d0209191403150411151303120c02060f03070207080d09060311030c0a230c0601 70
    0x1305818001036040d030850701e030b03144441c1c80e41d0b100801100c8101e08100c0c060000d03401c050900c055822814009d80ca400130aaa070100f0070404800c0503801e1380304e01c1000902c00d9108211000109100f940446440b862407541700555035a607455409050f0030031581096080400103080000340c3c4008145000312085008004c0d01803001e880140c941280f02c0b6094861036030000302c142c400d021a604442c40304400070011118031403e2046c1c440c4800c2c0302d019070001655568803030078540c80c00258224845400321001d580c40d1b907441d680c00ca009519424034503081302d03400d418a0315a000c01006014131a03140412000b40724a14100141051925000c40b000e0060202c0e00300701503140c01d4200c42c60944040c2c0030a56944401c00700f00d14040c0640d200358003900500a140c50065030280410049541c907a5040c0050302d40314410b040a4407050741c0f2405403640801203c2a014010403d04420f429081700c070568071081c403c007480c8207910480f86464141c00420040c040b01c2100f03010528144010b42501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 319287104 1250 319285854 319285871
    0x8071e03030813210203030f010803040f1503020f0403061a040b0d0f020d050f0f10020a05041404060b2a15040b130501020d0b01020f0d05041202011b080c10 69
    0xb80c030041000c2c00c2490f0810070359400b002030021941d28034658010316100b6400101013024000d407070b0f410075551140041681310000644040000684007500c1141c071158840901c2c00030f203c081e160702c00350074006042c1c09000650b80546d01d0b6002d8001107000e03083c041288080300d41c01042485890b03140610aa16012070250103407100c00c680455291311a482503044aa140002800d41e01d0b600790060051085c4c61401c01c03c1800400c0c00701100c22968100c91501c1d0740c580d040f005900035610708a0004009100c01c2105000352960100842c0c00070b07000054040d181d000310f0302650300c240d0002564130307102d4020202142000c0d1080c0c0007030b00c0120180c24403100d41d00408081c400083c0014012006a50101e000d103500c1c8a0720808040c1d004008554840000205501400b031140751980075003c1c2284c000710072440440d90200028a42e60350502d003600f0600e040303021242c001800d81c104105400c91018960a0540b114101400b811075291100609020f16103001e0b81c52028070811420055038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 319288354 1250 319287104 319287107
    0x1b070f2117010b18030a050f0a0210020c0f0405070e0306240108010f050609180403030c0e060307020d03020307020a02040f0e010b061204020f270105030d051201090c02070f08071e0303 81
    0x1e5601403480704680100003007000c00046d03c0d0100a40c0040c0c1240a062610800c00200040a44070b05100391034202c0701000ca124281d032a00d5903200566000390401010380410b180c02d0340007560088240c14000800210100400e01d0700d01c0441f403041c940000c56441300c400700c05204505a002c4024600400d9560404071107281002c000e209040c02108042a00002aa5480303a0402030040542040e5100d01d02800c00502030040e6461040c0030507200c0a075528142030171011288180f00715001821130083c1c418084000b9400108418110b00600d101e41c0300580c0d4a0141e804a80c10b10040030540750300e0f40703005030308407101c070038420b4440d94042120304500d4072510b911aa00c0b5130100c4440c414a04c200000c60b00408803080036010400c42800c7e5806030040015081d410f8a0043d400c031020000401800d0340c80c0e01c19021240e03408060480100040219504090003803031151065580641c0d65214081440c6180c1d0031050260700081014040039804d00c1c40c010b8510448483e43c035009103107880 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 319289604 1250 319288354 319288357
    0xc020c03061b04031506180603120804020102030a1101060512030409050c0a1b0611071b05030c0102101802090c03070201051b070b070908060a0605090a051b070f2117010b 75
    0x4c010715404400c00480b1281080b54080d1006116400030000310202c100440e10050480b80030482d40126946060300c202449245000d01c02e50341a00103528203100d40405a40c80010542a04000d6480303250110b6030b03807203c100c542040740020004640352400e00200c1c1050300e5000704400032008007842100d0419034804443c0795041150121154190114100100500002c190000440000295110421074683d40d581c100c41e02241801024a840d50308044d00c82c1d510719655801a07001d416100303588001030f8000382405440c04460030714040d40d580890200344040ba02100545808010441c100e0340a002c2e5a40c44040d17044880490300590041d2016402242c03c0038180201c29000110310314094041507029083d039400f21180c514060015501038034042c05164054450400410100300442c010680202000c001c0c84110605d0301c24030030307003540105c0f005545034810b0b0384000c4082000c2c449030a5480b15119445400da0301c0c00c94024000c05103c00744c0300400c0349040c00400c07400c10b8500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 319290854 1250 319289604 319289609
    0xe0f060a0c020703390806130c0b091305040503030708150a1a0c010e280507030605061507030e09160806011202070204020c0d090b07081204060f0c020c03061b04 71
    0x150fa0800200c15000350411408090420000541700caa40322822a0075102066007181c0c0c0120860317440341c4e1145103001211052440c024211014400c00b03010b42c843c0380c0061708940d4400307800b6540d00894000f0540603100207850984240d08008180910f040d03000460a5010358501e41400700c00d0445c0c004150086014800d00511844c0390340045004400c503c01c40b408070010100920040345281d40c070f2919515030845041c0700340700a07416074140258401c4035071700d45030300f18026141d294699107850740644001801c45500131611000003400b0b0860ac0e01070802c1c1030080c3e030f504100503802c205012072040007820700340745013800411103010107078807030910303588130100303203400d450050303152507044007030f004048009501c5400800c41d012001c00c0000e041c1e40f0082c0c3c2d65505011503039155814a458800c0250260403100304025044083d0007584069401503c5504001031142a001200301150004141d01d0010b80000d0000d90030741c6010010f00390000005401360031003004c8000d00701518400d03071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 319292104 1250 319290854 319290863
    0x203060a0f060608041a0631150b040308030a0605090f0406050c09060a030b0112020a050306030c040c0207090c090b0c011a010e0d0201080402030307120f020114010605040e0405100e0f060a0c020703 87
    0x1100014036076154150100508038035484800604406038500380c0745e01029202108c1000d2506c9080182000302c141d0300c5080b036202503400ca2810b810343d1136803016940b0084c400700030380751a1540001c4a0b154001240c1c410500d449034030f4440d04040ca4a2000d50700060f094110f500d80900c40d1403182c1d43d50100300c4120700114100050305402860058428034200c02c3342c48400c5101003911221190840e004500c030301c1080b002d4505001c00b40c0c0c108021240e9116400c001a40481c070709101c0d010699210825000550038802c0c207284c0d6075200440141c0c0244c1940c5007a9440301004680602c00c0d09038050503032002d080c00881c241104002c205481c088000190401038100007150654505002716148241c00021001441c039000a026114012100c58007006628101580500200414901d0706030ba5050751280d01d400d141200c0250341e10400ba1003903c050040e9030200720400302c24410b81d0040003240e400f6018800035500081c0c1000c400a1000e1420b80c2070911141e003066000c120b44041d42d600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 319293354 1250 319292104 319292153
    0xa0f09120c051c0b090c09060a06022a0d030302090f04060308160305070804030308040b01060503090d030c030b040f0b04150b09010c08041e0f0b0c0601030314070203060a0f06060804 80
    0x29001d884126282c2804084e00b90513200081c81940c5201154080b401d58060381c0e0704249444a00c00d120340c030041841280010f030015074030441150b00c420942c013030704040314840c601d503140110002080324070304000840101e50300007840c40ca0703801d0021105c0d0744660216000c0212074996100c680c140e11a4440790030a80307200c9485d9504241c050415250410340082409031116101d00e00600403000648065485604060000a545200c0c3d07007182d00c030306030036005818090840081600a081c400e00301c60285a281d95040440d92100d01c1004a02e500d21400455000c0c126403d00c021100014a6919007041a4105202060b800380c201e0344881028600f109401880b818401c050780110b4009201048403240501645155002c111050b181403900190f25190707200e034584058814600760603180c1e02b041c0c00400110b405101a00c00b00e1130240d91300b40c40c240e550b0707002a06280301120784500307640e91217060601e94000d5104030009032400341410055820140c036101c08104c00b000070264200384 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 319294604 1250 319293354 319293379
    0x20f030d091e03090e1003080414010915050d09080c0f0705130b0f0d0c050a03060906051509061005130b1810080c0c01061a090f0a060f0c05010209060a0f09120c05 72
    0x5008150f08000c2da000102c5a840742d40b00d210600d031002b10040214009290011301007180c60002c038503010410700702d8640c2454140c0c504049030240c11a0310041e00c003440c052114640b958401c1c80311250515258000d03200d132500300307020880580b000c0141c140c803451404007100b845440d42000c414088100710380040d2034200900d00046105910b4002582014a01a001040162a0700a9a40c0074854070091010380d5800c00c24020100b82098002c0d8400c4900001c40d00e541031048542140e91010300d0043e00d806203202030b040c00051185e0065001c001e00007004001000b5003032100090b520221214051007400d041c00400c0d580c006894200c000c030300010000000b8400f58440c2c00200112040c0145031800c000c10b03801290024502c040c060405221a0313049443c1840c0c890b42500c038251910701f5064182e10040300c0c0c15212650032101907600308001e103965560400940b107894044d0341c4058402406403c0245142c11983c03050540410340140580045c800b8020407080c3e80b420b4425000210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 319295854 1250 319294604 319294621
    0x30a03050c0d0c090e010501080c0a0c060905010203090c1906050301060831020918030d0e1603142503060b01030f0903050306030d050702090606030601020f030d091e03090e 76
    0x800d072030001d0502442e001080603caa0803000080460b4115132540d1216aa1741c0010350700442d00300c842003090001081240800750140d1110300c00303076005050001e2407a0103a500d66003260301c00c5d1924100d623884000140d11614000960b00104030750029100c80175403421344050f00d10b000c1800740c0f01c24861050001900189210396400480503240c0126000101074224465200e02c007002c01d0f80201c9102c1d000034040c04400c4404951003080200951400d05400c1140e0010010200714040d00e026203041801c208881d001d40c40040c5010300350070b140b00000c1c0f402d11403a182c01100b490790b80070050640b101002c002d0107a8041187d8111001007000100d1130012001403007400f00303090b02580390169102c00e040d8800060f601c510420380842d4541900141c09580c10702402c44025400704243c0b0000c0c40c1414100050740d00450180110750342c91f0507030b4001e81d007190032a00764585120364400002d8284030003090152446603a108400c588050320343c400602c070020034020721034002e600c8402702d00c1a2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 319297104 1250 319295854 319295857
    0xc090e07121109070c0b0f010e0106020a0201082a030405030901020d02060921042115090b13050102091f031d0604030f020f01020c030706050702070501230702042f0c030a03050c 78
    0x310f45c00054140949031040e00401887c1003809800a503038140340021460074000180660140d40584a0300d1b5103a07a4442140740d0075400320f0103180c420828045d54800d000c1c1c8100914045d0788110301854580394590002450700ca299131070b950456000704140141c507040072500c01ca5540e940b05140c0d480350480d06048521380715030b500c004000d0084900c0301e5145181c0207110b80c815803207055031030418150f0091410076501c08820190114034250045080c110160260411142c8640000760606464100081141c4c10380402e018070901805a6250400e0341480b6244c6a20000ca02d24070184000c1050203603130f030100600081c1800112103861000e2402000001610340c2418008d654401c0784d4400e15450380c00101c001c642c51401c00e00803603400781c00490307031509130390741030b941c1e401a4038032036540c103404031002640c00010500400c00280503894901660191000c003183c6001c3c400c03451855072040801200074900300400a1200e08904a004003c840d40a01503117400300301511600800c0f02d43c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 319298354 1250 319297104 319297127
    0x2070809100c0302120a1b020a03050316140601060c030302031e09030a11070b0a12061805060f01020c0907050d110c010501170c0d020d0602070c090e0712110907 71
    0x1075024961240c005030b000300b006100500c01d80c280c1d140070301d103504420791310302541b000301000c1091001555800300b44152010700e03980c001440c2008069803a1078041c156440222011000650f0807000b0042c0142410921014404e41c4000c1c056503142c854001c01280c5103003002420190000045030b4100c000320f004031070702d440300070042200d0f0a01001c0d00e981c0358003013414400483c0342d86500092902c40481e6100440700c0401d1868904540c031441242c9081e85a03241034500c6d5030341c020108035010000c0003445012100140025942030050402c10180c150810f510b0456001080400f0035840b04c0741d0030341d081030050600c207071610a030070300e5070014160104c41b00741201404031740d000d41c0e0801504014101c0d60310305856802e54180ca0b40007512106442d04090b08400901d00090041c10171a4507800c0d1140104030050070007205583e080700c0004140c0c8120400c1c0d0b200c0d04070750010102440310324010040800320691500b0569216902d910000c64101d01c80e524150002d5a110b01a103603000c0c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 319299604 1250 319298354 319298359
    0x31e03020d0e01020d0c020c030c19030506071805042c1513020f01090b19200f0c030a0c030204051e13050d0c05030712050d11090915100302070809 65
    0x4001c10285059000790043d002d2a03c0040c2003071b20300840b840c00800d24411a8002401a08101041d08180080340c1c083d1000c48103021803000c0b000000c90428000b0078040c850550b2000c8601c3e4041d45040918807142d00042e1140d8a0807601c0e4245556020b1004801c115451a0440e01e0408030111402c040b00820045009a1410f0800503c555600002441e062003110600c40c085000801192440d0150040c074103072070070410070001003010340e00d17120200300b19620709480c6110201d0b403091700d403074200d00303a00c915540900c40f0302e42d01e503e05201d032459009013039000784410340041d1207440e211030709071202a02440d51344002c1068400c2c00189031010000121400c2c1241c14023550300201080481d0003620203006121030414110301c104c03107250040760000001c5040550b80d844020b080600e0180c20000d104007000220390b2411180500704923a810f400c07074661206151002e102c00ba0400500c24410107a01410000c865507d03005180701070f1000307180058503072140346414a400d1007003c0a659 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 319300854 1250 319299604 319299611
    0x706390503040b130905100806010b03151f0807020c2211031e060103020a270f080a05100b180c0906071101262806260307031e03020d 59
    0x603c504d0800300c0070011103030710040820641d551800107000007452809a02e00300c2d00703c1801004401c41c0c01c0c1c003442d009007045103c3c480e06c0c800d603c000307105256025104030240360300d2000d501c2d02c2034000d020903038000c00d80d00142c0f426054440c0092190825010040000586600807100000c0e107544003003001030036603c200340d803030901e58170306040d24295095118640c809600060495403080c001e84441ca005515400b00442d10559000300b43c0d654a40c550b0051502d01c90001391000168000c0c0008010443c090420013445081c0642420319201019181c0350800c10900c0c0030b9114403202e40940c0c0703442500c80c0f540f610b9103860110036203c1d02c00c680b64007140100c0c1d00c07000c0c4050000000541c03542600e40b500d0382444008000030748042003001203900324000700010032104c03008010030400d00c0200c08100c46940307504080e0f03045606540042e00c1d0360305039030742121344a030b10304800340c810103817020045003403829941e00180b40420340341c0344a04e110b200d545c4001000c2d000ea01542d01004403601e060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 319302104 1250 319300854 319300867
    0xd170c03031f05030604021e090103080a2613050f0a060209090109090f110315040605061c050a03050d0906020c010c020d03111206031e0706390503040b 67
    0x180e40c81c0c00948040c840520060851801d19404648000450341c1c041c0141c01999215020880c0028404810b0140c0d8104032200819943ea801c111501035031050701707144d440b0345000f071004281c145a4412040d40ca8054a060688200d1039108941e000c1080407110101d80014506542009008100d03c4030300c2c0f299002e070500300311040d00600041c00043d40e401e00300c0d1b039864201c0d4043d61000358016000a800105e501d010030310f080c140c0c0e101c0c55005070440703403100540380801d02a00400c86003075440d10b031b4074001c0c4010b40c40e202c0c07015840301c10aa000c6280f81d01e0303552074031525490301c403100505201001071000554025078009489464012200315260344034501745c68040c0071b090200300d006001e80c103494003003640284903503408402c15103001400d003840403848210809010780110780c50310030385400c61207403880080b00c00c1240010001800190340303407a0002e846052028200c00f400c880c0c4409444840c500c0b1417a80b1005a804030307888400c5440d9040490451086400011000ea00012034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 319303354 1250 319302104 319302127
    0xe25080a050703200105090d05011104060c050708010e030d09050a02130507081f060e0a09050c0c07060503130b1005030f1605031b151201030c050108090c030c0d17 72
    0x7500700702da00401100c185090f01401a444c1c2519022500e40490b209101d64040c500740228190340340342c401c00c00054515600320035550180c0240d444600003c0300102c25808115003446208001d1044200900051503014801c68a0b405081e41d0400070301e503600321080910004020349011960050054610701d20482c80640180c20300b22042800f003600300700820f880e01c1c2c041145484240f000c1c103801501909142c005c8030100c40c004c0090798000d4006002041c0d1800a101c6c0030301419070300000d036a803408240e420f03605200d65584107000b40903042c000c0000745510360801e45a03840d8050b1a9180b0b555071070400040040d40c9400075601842145140514a40c1c0050340841001540f0030308208255141c0070135596418000b40e001c1c42e602c0e40201d2645500f4140301006d008800700d1a01030402d141c032001d08a1442c0264426503003580c0340c2d02c08001c2542c0040069030032070a03210103001069140070121340e0b07521604568901603007040c500042030001100c04080004001c400c0030350345210030a42c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 319304604 1250 319303354 319303363
    0x1e061109090702060f0c0705120f0415050a08040b0a020c0d02010e12031006050c19050d03110c070509060103091b03031e0e010c0314030f07030b03010e25080a05 71
    0x400c500441c031481c04244043e00000750580301d0100c041c40a42c3d0740e982c40d1040345840c1c002d018221024411001d0810622428001a05007600d01c60141500c962a10340d2080600624000841c24001c007040184034032540201900d41c05500401f5244071074482110f000000c1c0b181100808450240c030104460041d03042d0003202c592020082110301103030701c0303401800e140d110582d80a001d480b61a402084424090009000000140b2059803001107500c0000d90349920502c8084a454104100202c2c00d203405212356504071008800c0d8904209000e02000c0d80e4480600590f44210201000140e850b80b198006843c0c003940200405004902c00c44805400c9042c1c0c0422400300d1040c0703a02c2072284403044800917500030607544440b07410940030019550902000070980410241180540074041c0c00c3c4019801403441400c000705070301d0084c500400b1250745048107407081c0d0505804c22054030b4001141ea000f02c1a0850708411603420380c0725402c2017552a0b029a4a03401050041410f0143c04038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 319305854 1250 319304604 319304617
    0x90c050f0d0f060512151819050106140d060902060d0f0e070503190b040507050a170d0201110d051f08030301060f02030412080c15090307020a05031501031e0611 71
    0x1003400b43c50b071100d0401100320b20088117000170b58040780b070382d11070001c8280741d264001c4c00400c0607120210500d074040381001403008410341324009070348440003041000d1103800004c7c08142c0c0c0034101000c603d0006903100703544800282140307450701a04000e43d51003100b00c0d291341c100c005c01003240041a000d0300020b403200c0d10b0f10a10300c2c09010400512401c011032540d03491940d500352406001425540c50308698000350040c0ca85104007840441c141d1102480302c009806004021400e40e1140b4413128038000ca400f811342c04690405141c0c101440080781651400e00d560344020072030742c1e01d641d2080703600704a008458404c018501400215900003000450503030b03059a81c0d0012202161009903075034415489200b0305140340501c9a004507039906c01070711034072460000383c0307000d80a060480d86264405071070302c0c1d5081e003002038048118580000c081d4001d0a0a034044c0444d4002d200c0024414001480040e214880b481400d00c121801c141020448650080c4208000d00010010404940200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 319307104 1250 319305854 319305881
    0x609061503051003170c07030203010207061d0a03140c12041508010905010506070b0c09090721060f050f12010e2a1f0c0b0405150c0a0504090c050f0d 66
    0x20000c14410780001e00584143c0760000400300180c1345500317240440307901104100d13645008440e004001031358280000d081244c05420040744141c50f16000f130008081e1081804803d41c010600600026002202004608240c1c0b04464881d4840c15449080c440c07003401800d5505070006010841003c80151050030b140a0355650032203030707210800c0b403040310028065268001000e001000005158050340b691200001c2842401d0081e404040f030304504090761300c130780490300d040300d44401048a622801d500c0200c198060000614141d01c85500f20720031f0188a014070740424030050180c445c00c1c1c0c505000600304000300205403a81d44038039140e408001c101c0407200600c9904c0b12400042c402c0d01c18581c1c03001440e00e016289000080750000903031803280c1040c40b000c095aa0042504203d21521550240c1c000d040d40010020009003a1030005060f500320074400c0c0070342c503001a0300800340d0707041d244400c2d00080c2d0309c8400d2030252518003401e99285180705000075800d0540010b5004010342c400341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 319308354 1250 319307104 319307111
    0x1103010b0301061b051b060f16110f0a0905130804030c081603110f04060f0807090c08070c0f020a0f060f0e030c031009020a09090b04150603080904020c010609061503 73
    0x20899800c4044c2c403024005001980400303c0031304c00d490002980750300e09100902d21850040020206206078000304081c10310f00031500d0640d01405802d072109401d001d02192113890400300350002449172180d41c00f40030b4074907943d040000c000921807900341071540c2c0c0161915458a6680ca08038004051900079400503002c5d4400c000c80b401081c80401c0c5c140e039889003840752003218060902078000030841103583c1c8981c0f200340001d0340d044001e4804c8007800121018084007800c000582081c0d803034134404101080002c00400c0251641f1071403003d161544990a0010800c50b13000140001c1400d801c1851a2800e90b40000741013900910403013045c404a4030f498216010501c101500c90040491640c0c05810010252481c0d0540b5448001c4440c401459a440c650715100240102e4084210494289400c0001d1005112311405020708960412405201103411a03070340f07807880d01a0322a29401150041a010181d0704203420400107840400c0c82080059501e2019008120b040034041c801b280c41d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 319309604 1250 319308354 319308377
    0xf060606080c04030b1005060a05131719050c1003060503060f10120311010204060e0909030a0c02040504030201091403030105040f1407112e1a03120d1103010b030106 73
    0x400c0301c64402c2c48070401d0503007018650b031520940790344001d1400d141c246d83c05802161640d43c0c1d50261650003440d9a401da12000e10101c118100304064008110300c480704c021391580c0c10070001c0d0000400e4210b1500c078282582d0f900d44a49004984c405407544000074070b080d440030640c1648280d041b510103c0440c0d2054031481d01031100490309a62801e40300c90b202c40c050292660751f881e000c070082e2207840d1002c8400300c41c1081c142243c2254000100058074140c0660480c80d120442c96001031682024601e480b410000c0a004901c0e00c0c90002d0046890740c0000302030600070750080d030020343c2202d407aa448a030300414082d202d5100f40180d51099117400c01600701c0403114070940d4002a17601d0160b550540314844140c51440400000c441c052040c4a002141f091002510741040c2c00481c40c1a41e24a16054200e800c0d904c0441d08003010302800442c0c2000c40d9000100c441601c40031100040e6902482c0010402030704034000801f100100000001980b02c108100a40c102d60b466640c014640b036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 319310854 1250 319309604 319309607
    0x90501050a0f1d0402070803060901051005030f072604020126011701200414060a08240d080304050f0a02030a03032d020705010b031f0b0609030a0f060606 68
    0x1d601038036000800840c1545940d034041d404021107403c1c0822800c680d8281d100000b4266481030324100ea07038140103c1401200d040401085000d0403080fa900250401c41ea00010035600004264050207005c04020928880c000c07030304800150545000080c1c00380c4130705441c229002d000c1d201240011400c5c1d800f100c440c09200b000324520420a020403103503910b80840c10785004014040140155602e0444801d02554904072082c20040c14040303548451402800c605201001e281242c0188810044003800300d5210301401c0d48414076410500c2c0700a000c2080c03047c0308100e0001e850700080344025410500540b03401842c420391103002107580c400803a24103161070302d26550f0001d401d58451003880002900039005018140101d518084003410207810b4030080a5031034800350354050780040e0500a0201c01e0068000c03805c0241c00600c4807045034850301410720703c507680021480c1c0d9111841d005555692088410034540102140c0c800401c0e8244000303410f2a0120899541d4a040760000780d19 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 319312104 1250 319310854 319310857
    0xb03240d080c0c19080c0301060311010f02120a2d02061b091c26030705130308030a0605091e222a120804090b0d0602070501020a09050105 61
    0x1000d000110842840d9071907000903000540e4412840c0910310026240e0345071000c0c00da00700e110f0003001c003400e240341422040c1808078440c0c5980c00381c0d04081c8207101184402c403880c1050ae400707107090444452000300c120b04000280c01c110343e0620f0001080018280d001c0440824001960304524910340c0306400080601846200c0d2800b50f00314100240c80402040b0f100048521040c44082c5401c071030000048107005907200d00520b42240f40c100f501841000c1020a4480d04202c00c00e91503003035503850008040c00000c0000c801c1120018420002e580408188001591f01200d1030340c0303e0a0208a00c0040e103940d008280c02140114000b1f00c0956800050f903400c2d480030300410040c3d85990040f0b5507500c800480801c403880034940420001258a50020500c482c00781480c941c032185039080c0c50081c0c09550101c40c92024610349000820f010710111030464240c2440040e43c400d0450200b000004102000340c282c40c030204401007807100640040c0304036001d0781e8a4901007900c1300c3c010b607840e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 319313354 1250 319312104 319312171
    0xc0c0103180b1003080d09120c0308012603030a050103021906091a040b03070f030b0a050f090403021516030510291603020a060c050c21040f0b03 64
    0x1c4031540c0039907004202407641c01900400c5001d441540c040e2644ca410000f82d001e11440c1282954070030a04013400303e0103982100d8892a842c00708000b09030794900070309000b410302400580d000c0068000e0545c0c981d0b50b109644100d19141074a48900d4110100c2c80101002d1005070701484000c944001c0030101c0030b40030b8040d5000c50300c030321a0040c24540003c900c100c03c40c149110014082002250038090203000d0740c41850a40ea48000f65a03030894014241d611454480303015480880c1d007400305560f0700140c009003071400e640b4200d039a529410f040303180410203174105060f10410700c20f0200c80800d443e0051a0182d00d038406200030f80310900280e109a840748902801068903100a6143e15030350321500340e0504244803041d0800340002146824025044030841c0540e11401b184000c00c14075000c0c49080d100c00b414070300d017450589031486031141c01c45120890a0001070104c900040855000c2da8007a0840c030302c8a051a5890b011a43c41e0790f4801e4030741c00040d941350840c0c000300348005e03000101d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 319314604 1250 319313354 319313381
    0x2101d060a2f120405030304020f03031812100e060901060e150d0204060e010b0403150c050f21010e040b10050f040c02100e0105041a0f01030b041b08030c0c0103 71
    0xc108004490840032404100440380701030074200100302c4090f04464205004500070005140d0b6803c184c0b0401c03210b44841e9100601070340040c40b0f0700f441800c503517504400c21002030b1400c0d0302d8140341c0c10503642040242402100c07031915080d104000c0120000d05c0038466000340008106098403560703141d541200442e03403840c0520142d403044691b8240040010b4180388003510118500b502d80d1204001401e00740c100c00c05042000c501041400060310103001c0720284c87c01c0412800340d005000400340d109500f0032060103c8000b840b1201c1d403003000030309441e88100130740034540c2d9612a00402c02c0100d0681c0c00740d9200045001282548405114481c00c90340024012801941d224082c00041c000c1d680160065006241112400546a002e440a070a10701c100004d13030742c80c1c00d14142c2c04403880460301c115540040c1c405c204480c0c0714003108905480c3c20601e00c00c116642c524291241520f02d0004645144500308002500300000004e011700b10340c0c08040d00d41e081e403404011803c0b60601d003000c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 319315854 1250 319314604 319314641
    0x8060408070201020a0b0702010203071d0a06080c07060c050d0b01170601080712090501020405030d0c030804170c0f28260405060f0406080114090609060102101d060a 73
    0xa0000e4544802000398610600603240c0d504480c1c2c55400e071040e021182d140140c0d400000304148651311054212407102880102141c1d14040004101138801c5401000180011200461803001b04081038401e4168040803e0240c100c202c0c1c0000c0c019004104008070103414030000f190950b024114036541140c0003100b8092030380c1d030032004495951000d00302d4001d210306481c01880011b040d0042c20f01c00d034050f1001580d114640001e0500d02541140300d0b0080185021100000a40c02450103412580114940650b50200d480c480514824030106004900c124103505001d054042102c2403100c0c80802e00b0500b440c408600c04034202c0c80e110005010031a40d0410340d4903000040102d00140d12400038403800e143e120742c04940c660b030011308646030182c0081802c03c60b49038080441805401c40070080d08aa143c0344000c1130380c5841c054405441243c8000009403164401c00c04038070040c1140009000440d801642c25241240c031424180c3d9500440001640241070341c054807868500d14120714 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 319317104 1250 319315854 319315861
    0x50402091309060b03070308120115020a080f0f07030e0a080127110a0609080606010c02011e03111605010b120601051e2d030a030e040f06030206310806 67
    0x120040c50741e0001240c3d0651303143c0214049440c208891030245d4801d040d1a59217240d003903284028014140d00c8080b407640c0d42ca03451402ca40d800304001c042d0992100030705448100f04668503510f40590074816804290100b542001d143d407209018003843c0c010355a20f24156160106242610032111070355540202e4a01d19002002c504010f003c0c0c02070240c2c002010458148000615079040c551150002507040d0000384140d075010301c41036821840034205845e40121380d81c0081c20b241d007540a0224200803401807144828008d4002c0c4403450502480c1175512540c0d11240302d440360001c8402e640c00d62034450a0303002410b0040d19034545040080c0200240da2030300040003c8151002c00003e0040c9030207030012659296607408195106140000140e111640d9110300c05c001d0345a20528070a44c456500b0340301103034005220614106090303c0c01b0809006003407100740034044a40c8000d4124100007a0340c80101c0019202101c0c2c2c0103421048482134a50542c4080c3e02d4500d07020f6048940c0001011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 319318354 1250 319317104 319317139
    0x601050607020f0604090b0102070e060102061b09091f09060506030f04030c1e03030e03091503091f322202060324060418050915041a0105040209 64
    0x41c0003038a100410030002841c1c0c0c18045070840d0000e40c0f05081c900d80702d0b584011590780522040000c0e2044140300e04083c07801000003559620054030f582103000903c1070419200d02c110341101e40d40400940341005d1810414401c00d0f040d401c0e480d800c0210340e1030000c0840d05050601400040b290000c0045040d034444072070301340e6401c0380a0300c00c41c01d0ec40c14400c04000120701c2d04240d040b1042403160b12020040ca4200130341900c5040d1003105a9800420a0b803410744c0c2c1d03424103d6092100c424030320380c584d500d0030090b52400c4c0a176600d9106100c019501c902e191716061300035020201e09a8000140080d1000c1c05030030440d03c8604921118000038000782000a101d001032010148000c00c1b220445034a4004c58096402551244801000300260200e14480a080120741c03103001c0d41d00d507207403900e050203100c142c020604041000648400110300200803c1003008095030b40c8105001c0d190401385401d02095002c101301a02c06010701c0c00005251400307100342e0b0201c04c4080e210302001d001003030f034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 319319604 1250 319318354 319318357
    0x8011d01141c0c031209150c0203070513061a0703050a0c0203100513020f060c03090f0a0306020a080106080a090b07030903030912030209091501020706110a0b1518010806010506 78
    0x3851a00940300e4034104011001800d0b8200e80d96004a0665403100c1c19030920341c00503101102e03094207120941404100c15203400254051304599440c2951541196200003802c02c061a8003640e80316482038420311224407a68050300c1140e03500c0507500c5040d0700b200c83c0401c00b070245031000760110340d041c00030040c001d0282843c07000080c0300505858410035aa01d02c88c040b14001d070f0343e0203560f52000f8403000441c201038160092002084400d030307041c815140b8200343d60f4410f41d82030501940600b0740c0b2500070b8403144c0040000e19408807082d915500c51180045c4414400d1007008001064440400d000420500c500c840182c2c000e9441d900d82d0f640c00368250041d02090340d0450030199030b42900b802081c5050440f98600c038550b030f0003581d50000d07134080200b2800301800300c1c02080b05440060359280c2c0c0018040c000c407011800d042c0a011000c0c440642403005049020300200d12080810100030000c0e1150785e400d0500b1910301c0317521b40030101d1264988900340a00f51050740441c00600441c58100c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 319320854 1250 319319604 319319639
    0x18060f082a03060a0e0d02010603210504090f1506080105030a080c1906050106020d080f070c0f1a010302090f07090501031505040f0b12030c0a030302030a0e0610030308011d01 77
    0x20000c1440e5108280801c1c5032000454043c0c0004ea500d80131904401c0061010344c0c0500002c0c4000d03c610f608580b10030340c400300d00d0b18422500b0092940c15a00c86802801614001c0c8100d000800682c02c0c6144d0460207000f40c440319042002501d400400c98074020f800182c10386a0107401040101200d0ba01c41059a0082e41c0c201941c1c070402c030381019030700048280f03140401c0c0b03e04000300b079079450120040e28152410101c041803000100801441264101d81c19602142c549030140c884002030900d900c3c6074208107030261142c480100d0018864003c0c418080c1240d1082e11500386580e00e1018080d180e074802d0b90a079000400c4140e04105a6104e0307041099030480410041200c2541c2e180068219a18041038842e02030300c03046101e00500d40010808a5048503501031486c000c1c07090a01c603128041c8040003010706a003c008100f00c0081540b004c0500380102c007c49d42581012100300b010300c082c0b84070807000940c00c031001081409900c0d82850070301a440d9000001c0c2c0e400d11101d104000350f1b0380e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 319322104 1250 319320854 319320913
    0x702010311030703060602071a0f09010903020d0f02100e03211308060a0605030703080415030605092403030c0a020d020d061107060b06070c0501260118060f08 70
    0x20400c81015001c000002c0d8054070320340d100010b00034030b8808040d040400030b03071000504a444200301424000301300110707940740a0702010250b6a000c0070006840744c4405400194110b040406404108400301190149550085688418842c0b0310b41d002c136941c0750418441c5416030001000ba442e43d0a9031411120b120768115482414507031100618a040300b000e90150000d40d004500344006054248075180150400b60040c046540c2907466068592140344160000700803000c868101aa200340d01042c040d0a000704062078030f040691241005401c000d91501103d031458203594410300d00042202c066007440c0303014101d441d4a517004c0154801c0341c1b0800341c0e0021051007140c4002541c1d4424450285034240500c4d440300c0c16401c01c2c40c215004a03d190f401000c01b048143c001c41c9040700031104442091a04500ca01b208140800b46040407942a000360061907001003074203212081c002c030b2400300e80c0b441040459501c00413943c512620341300e012403d420150315548407030000b890140324100c18 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 319323354 1250 319322104 319322111
    0x519050d06092a0b071a071107030b0403020c0d0b0a0b011101150e0f15091e01032a0f0e090321010303080f06010905101803060614011b030507020103 66
    0x60f5102c0401c08089a64120a40600410308074000401c040ea400f0151498103480c82c02c2c040e640e511000c0101c520410107024820700340025030b1003807207681c0d403425482c10380742507560f15030780c901e0b0603d40100c0c155070440c0540200c02901034981032404d5280070080d0441e8100c091900d880c030f6400010805415000c4c108184801c2d10302541a09005021038602d00a8007401b1840c546441c5024041e8054442e44c00440710a061020700070441c030155104c0c84088540c090a81c54550001d903107160074403020a0300c0c4000800020500640c00b20a00040c21a0002425050600500d00c400d1045900440780900c4030503a042c4000c0e000007802c241e11201c5a01102d281080b85181a080d0a4181c0081c5044003041c10040c81007640c48801c0c50303004011809004003a0600c0000641000f90ba070040502420a40202801c000d1041d010061100c03128032141b201c441e01d90610501131728990040c2c04014600c09501609540b19008141c03446001410716030f58011a943c04582a88c050391007681050b41303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 319324604 1250 319323354 319323371
    0x80121030e0a0e0c0c06060102060c0a03270c0501030e070b040e04020d0206040b040503100b010f23120a0b0607050a11060702060d0f05011a09150d0903020709060519050d06 76
    0x3080303c0781c140560158407a0a4503040b00700c02443c82c00388002c0c1101e045412880034440000c4281c070680315040f10380d08020030903200425140144a110398440201c00b01c41c09402e80074403c00e90f10b40810340c0d10a1ba03003801441c56900040f0b40d41c1401d03104070289200700700f0040001d881d1104610703412501c0104200d005e99941d07000156541c101c1c1c0c11501c80d142000404110b186420403003142c031018010014000c802041d00013030480b001308100c800901c03190341c0700c40b481c50400692441500c41086900c079107071082140041e02100e0102d0b8592500f6103800d000380414030300b0a056590080c0d202008015100043e03035180c01c85444054100d03001201402150f0060707440300050001e490f10b1140004150060f40340710703416604107a001c1406445500b01402c100c51041040b0303900c51a007a12011140381d8039281249507032046015588220745805581c00415a010030100f04840605a06105042e21a410009000250210007101081c521001c000c0c9040030420403410390301a0400050100c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 319325854 1250 319324604 319324619
    0x903031110110c210901050304031e02010e101a190308030f1509010308031b09031207050f030c030922050f1006030504050607051e0c030a080121030e0a 67
    0x18a640360101c2c03811400304522040000801503007031608504903c00340c861022008070341c00c0c1c2c420071252a0401400000080074903016010508443c5809411307001c01d0304420350300034000d0894000c10003141c000d076100c565075400c1314040c00c000d258000089811840c02c100400000041c07071501c00d00030705030407a4004040f0701003602441c03148510100c00002407901c03048a9540c0b01405c2e0145209108090060000c01c144606a80d400b41120380d5070003c0251a0f1081b03403141c05130442640d4107214941c0b48183e01c104000241c0360640c8039004643e81c0c402c00c10071017522401400fa2095840d0700600200d007142c5803460004010304103604111461100c006001c00c10344208940c401c0e210700c10982804080900c004003d03004dc40c1c0b9140421090900f40d0307680d038860074090400340403c18042241c030400c58031640e2511b01002c656003040d56906003022083c1d22600300c4c1882001050b103070340c00022601c1da6a152103135018582c05086000480d1035800307403010400f031030380540c10541099020904a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 319327104 1250 319325854 319325861
    0x50103050606041107260c07090f0e06040b04110d06020d0603021c08070f02121005190603030203070f1112030712030c051903090b0f0f0f0105010903031110 69
    0x29401000a044946000d005010545000d8544905000390402c518404070340c4205464a0400640450400141b60f00002c4911401000a440705a029007040000e20824643c088441910600b00501140c05074103040b42e200c0808480250600d407810002030000340110340d80b00c00d007460040840600c610703641c541500320317008640c500c1c815643c0e0f864180154900486e0808800000c180760201c41506590b03511614000c2e00c070000c100300c2d241c41c100e02c00c65032915001071080321980102c42d02031484500743ca002d440251008002c3d02d43e41d80080c030b1040b07400e01402042d642c05030002c603d01481940d1356040301c50490000c1d44c00c80001e102000c090707610b10403440e078119400c06c011500c0d01c0b440e0a141240d15104103070403080c946400000845945c0010590707042102404124681900e07005099002d400d03007080081c20300002a00708240c88240010083c010848001603025a580e14074041068007428010140444c2c00d1060030000240311380388a04c04142e030b040540b900001c221113090b098 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 319328354 1250 319327104 319327109
    0x4110d020309150f040201080604050106020304140301061703040f090b0604060f0e1e040e0309031906020904060611010506032a01020a08030406091203051b0a020a02090a050106301d010501 83
    0xf802284c2c000d03c0150343e44051081c1d0080400c55040125502d894000395480c400d40c031480165030003142c072100c0039680c217511800007001005d2500303c007001450060360726517000f0f00894104d45903140e4045007116181c485c00d400103030080c1180e4070f410b040075000d440c1d0340d0480e0600010884540207028140e2105242c8003c200009020900001c50400070031046e074200c5410b0146603402032100c51600e54000541103a80808028075001481c4182041006841400030b040d4210f4107080001600b1680501103c543e46400ba00800444c1c803031004041d141c00d445541003580051903c44480110140c1d50304900b10f980500485506040300c0e0b440c0703844c2e03800843c1c05540484e951b0520009000c0c00d111441800150382ca000c100030715010300c03031100305442d00a041c00c0c0e590f03000c074500700101d000300318002e04a90010190030031827a004450f040a01002d00404001564059102d07031280c4042d8440b5a21036404410340b140c1118a00c2c2c0c2d10014403d414905200d1031241c0041041d5003420b2064901 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 319329604 1250 319328354 319328371
    0x220c0e01020f060f0c0703050c16030c0506070203100e10050a0c020105090d08010e0a0f02180f0a0e040b04290702010b0d0b2707060c0209010504110d02030915 70
    0x51941410001a003030090802c0d110319a50005810054900304055000c1c0d80700e0303850100c6540701d10a0382000c4405014200c00d114240c40303a08a0f0804400315845500200c030302c1101241c5c1030545400902056000b072200003500f42d0b01005021210070f00c15004014040c44070000c90307020002e5114a0000c2d140d06079030006005a9400628820039428003e466015401c0c5000b0840c05030259001005194140728200a042188002c81c1210120350401c0440d5912010b095441d2460525012000d80318200070600c11044410200e1080c204009044112401c6414090895a56031201a19840c004008455901c3c400120301c41240301e444134090929172841300d0096915010300045d084450306462507200e1070f00c100c99070700050321124056521850311010b805403246461100d5028901c00d82d4a402c40c1d0095081c04151903502c48119241d050003212700000f103984e61420702040301c1460b114058030b1041040341066404082e0000c41d00b006d104403c0354514000c00c8800c4d07440e10010340b43c03040c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 319330854 1250 319329604 319329617
    0xe03070b090a0503010902010c0f020f0915120d121e02121009060506030408181f02070b03070212070f15050103020414070e0d29011e03050309220c 65
    0x80700c030b0400c0540d00000e40410713002005403480d981c0000e081d04103440c40007094560340303008020840d154035a09240c1844c01038984d21241c108400c200b0344500d06144c120f802500c0010070445019000285c2c1c441303034142c1d03454207401c40c1320100f0441e000d05240d520110040022107a03c403031820300ca1004200119111005000710b090402201d48418120340c059888242802d0062140f0340d034010071203802a40c058007160761902170750001500701c14041580c5030700102540031031054820b440c084000c46171032982031310002c6444101c0b40784140030036a0000010ba102c1007121104561103001130403401d000d86419840b004140e40e41794800380c401400803400ca6120710040045007000e0103000d1035014a0752110519103400030004000102c80d911440c8681c0d10307001c1040c10b01c0014038400040c4110750404079810110120600c05150003072241d420030f41084017a00d01310a501d20300c64001c1e40c1e40304014601d8410100e04000c10300921745405550706030682580c45208015100321401461180c0710341 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 319332104 1250 319330854 319330867
    0xa0c08030c04080d020d020d050d0e0109060c120516050c070803041203110307210314150f0a1805060a120302011a040e030304060c0c0b0124051c0b010e03070b 70
    0x15400c00b410340c4c0700354040d50b1180d4505640e070307900451240c9081440d407404581b2015200c43d010041c0c03060686810b8954600840b1400380b0009410142e0303110500e480301c3e11075040040c0c0c40000c960044030203031195940c800048480c01c0c441d60061404c0c0300021f080360000c949609406040d5407003580001f18402980545804140e0030540414822103030401031818840c180e1240d030802d00c05d4500c0c80740d040c04c0c032111001c10076000f80c0c810442644e016004180b9031a0200007800480e0001603110305c50882c030940244030f4540301036a0002c0c2d0300c400d180755500101007407800c8040c0c400940084c1c1c0c007d14110001c6405440030005c00d80b44d0380242e0001c43c404586006001c0480000031a050049040070482c6108110000c02c480e0025406800010140c8030001c0031145584000340c01000259a0341c000280340c824202080e00c1d040010300707407090001004405071003900c0f1340c220b07084240c0c410220980a0513540d90001320082010304007148080300f44000a170808900744c204150000700403805 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 319333354 1250 319332104 319332119
    0x150d020d060e250509010e010e04020d0213080c2209020301110d02032a0f0d060509010e100608042d14030a110d1704060209040507050415090303140a0c08030c04 71
    0x68858000b0fa50a001c1d00c3c0550500000389035500c0b04075114140720001c46502c005444a9046a0b518104d0b41801c64449965138604030314076815111300c01461240701c5642009185c1401a040b400070b911501080694002000002410009905a91556807a1041000c8541c1000101100d80100d6401692031401c0803003240000d1080203640c01900404801c40d40c42007444044035040480c011800342c80c0d0103440c440d0b001410284c0c01032038000c2440c40000840f2607809100d5802020381c2550046a13540b1514200e41646045802829603282060b650a04220304100d0a50700040c80403002d11008068946924440c030b82c05203d41075510000b5044c00b0203521154204c1040c0c5604081c11403e05000002444c160241255403441c403035000110f0104580d65045902d180d1300540140800d261141d009401c03501302d8407400901821040d40311809502c180c958005507035041d11501c04070307004552038100c9900660303010024400812003100c003044030a40035511402c480d0501c41c4d0f075a41030008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 319334604 1250 319333354 319333411
    0x50109091422050303070c0605071e0c1b0b0403020102060f13061109090906010503010c0c0c0927080301030209130c0b03090c0303040305070609062c060d180201030b150d020d060e 79
    0x441d01003006c0b07114062f0304039070350040207030300098140380c0070a001c503143c00c0544100c04159119911116040c000040c054050406001228000d0b0240d800315958542105080802100c80d00c00c4c034044c80c50703114001910340e4002400c0c4202030001c0e900701300c1c9110106820030f400350b40c00e031895446a03004010f03600d024010311950401c1440c3c1059403100642d90100440d80e1401084485501c0e83d078140d0500d40091001c040c1981080c0b502d4911030301c41c1c00c001c031040d8421701050340540428000148041c41892102d00702c55400224000e440c0d14180d046003007500040c019604901a40034203503030741c0e5801c04c00b900195000c0d90140400302c2c60800084c4c18a00c483d0701501c00e10689507080d1140c50b035404c4183d164105085130700c003005080c840000e4050300c12080c2c0400883c1c504011204c45000441420310a14400c0e2020029141c0e01d208212030b02c0d03982d0200c1414903804025140c030b2011306030040c110700302469a001c6070094488412002803c400ca5401c4822a00c1c22014031102c004000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 319335854 1250 319334604 319334611
    0x3020f060705031204050c09100f06050c0c040f060b0409060513050c032202130c141303020f06040819030201050c070209060d030c060c09050109091422050303070c0605 74
    0x100c9032032a1062a680c1c0503201e0242c1c28096015140c03c1c00001c0c1480340621001002030001054010249840501c40d0284110750045110006003010003082944c02481202c1112240c0c0e402000b030014039a00304005020246541044251034100c00119104c803c0c018002410003824007251075400c0005002d404515007111004484c101010b001581302003004403500101030340c242500741c0e8584410501c0c04490214000d4200c206841c00e80180021613110503102c541d03540c1c80003800b00251002541c5405502c480310120380e00c0f2281000180b42c11a00803446450161090781850b48c0d4000c1c0d6400d0800ca019184150100d8071451010554288109584501d030034002c2414403a00d50045444140002c00080c0602c401038841c1007454010200b240026034801402d220110044900901200313040c0f00720b0f0b0108001c150080340c200168040c441880328421f4110324a03070703152074100c0c1d00c951103400e403100746801c45028140450f0052008610079032454a5010200600d45050011a20b004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 319337104 1250 319335854 319335859
    0x3051003020d02090a091e030f020c03100c030e16050901060305010b0901030f0b121b0a080d0806060f0703020622030e0105130905040b06031204300f03080103020f 72
    0x20809200598a500c071001d41d0603010b603060795840c2c0c2c172015080024400c1900241c03629a01d0207a09a00740f09015540c2c0d05548659220401c60300c81e800140da65408000d030b42d0381e15401c20204a801028683d00c00810f40480f4680401d46408c40b0030103608000b40c82c0d42c03a0840d038440410a01c000c0c2010118035006045070314040000e50b03d414440d8005003e9266018101610f1b0f01d084900388143d900610409100189011070b404c4140c500b6958940f855014450321b0461544880254640307207001034100c41c0114081c21844081c50f4049528840c000e0945521100c28020003024a1064011b08001482a001090316003000e80e06585184440f170400103000c01c01c0a030540c002540030002021a0341c085c24050741310311401031000da020b03090b0703000300c170b2018508020401070011a0003c5400381005a065039100e035a5103041d08010710440c0a000d050600303030705010384040001c14040c0102914242ca03469001c441e541c51050300346c0c40716400e8002801c204014410741c90005000d48590004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 319338354 1250 319337104 319337131
    0xc08010e010b040306090305120f0919030e0f190e091006140103090809041a040506030a120f02100c050310080309181b0a08090c1504260f030403030305 67
    0x1002c480745201d202d1400010b00d010717241d501d850101800b40059482842c41c58191604d6403401e40040b118041c011218802c480c8a00040b0304149110050807130000c50f059515003030207640e940103000901803102c2c40c158002e0044504201e4803504000000054480f032100002030342400301c0c03014907110055128407155441d0110130024038100494101e0604001e0801003410b22803230500101034041c200c10660820b0400c07046400100120000d403480340341c22141000142ca50704203140d59501c0080b8010800d03c40c403030030080b0080c0240361200400405104484107807030b80c0280d08080c0d032100c50301c2d42c011400c040700740040d51941e1020305020705078060065090000c60400503014045c81841d040000070b802c0003065814840d030245940340071010b040950360b40c0032008000c0c1850b104a40c014003502980b03440c8895407814400200981c82c186900b941414140a40a03c450b0001802280c0b0f80c0800080c03006602c82c00d1002c1195466810041e42d265441c50a000e0140d900040c550b1011120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 319339604 1250 319338354 319338359
    0x20f0c1b010822080c0c0a090209090c03040f020613260c0f0402041a030f0a06030b0103080c010207051c11030c0a1407080a2001030506031e0c0607060c08010e01 71
    0x2400002d0359444100003100c2194105a41120322040440400140510f070b030008820340c403c000054440040001074600f00e603556130b11042c0400f2030040e000d1465201d01104041480b42c010382000e15003040c09805109002e006c9503000a500f13500402502010440301002040054500d2810080c6040ca241d509104032203024803154591281201103031180702c280f11480d82503141e42e4103840c0a0030500070915104061000305075150380044500103241520070000900900b8035004410880368801042005642560340d0803019800407000c107a02076500348005404610100000390200034004c500d510300146201c0d00910020420000c5419035100300101840d480000608400c8550044e0800454205039200385080c051680c1c0000624884c40114a090140c0e0741d4024600c4c0c4070010a88905111440c010350a4034001c48907140e06030050811903d880c0000b25041410010701d100b40d41500c0440c400041807030304a0030040d202d03140d40300150240650818001405004d0f4031201c04515807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 319340854 1250 319339604 319339607
    0x3030a08010302120304080a39051e061902010507090501021b0406030803010e0601170f271002030f0709120311010f09050f010f0203151c020301020f0c1b01 69
    0x10010b100080c050384079841021072a09051080d50060002c50041e100c166409080160f011907040210003148035078000700100e0022074031640031070032440c402c100000c2c91420b0104210100c50440050f03951280d444031301e510340d440e44000c10700006500610715000c0c2c0c01d03602c02030840344010484001e0205412091140d40e80009204a500b0700103a00c404010085402080c05481079500040c810131000c000410400440c3c48814812202130f81c03909030300238060f417014207588025036008001c0280c0801140f40b941c460034020f44200700005803003056a50808804d4504080d0982915071580d0100510200c81c4280501c5600803030741d850030f48400f50516010480b14001183e008003400301e0540c6401c00000d080d00410b44622121408200c80b00c1141040d545500041140301c0f1070f0352900b8a85c400503809803003a40d00030804042d00004101c003400602c10400031820241140501814081006a8090004296041d038150825842c0c00c0c12100c260301d04048602c51000004000c54007a181d079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 319342104 1250 319340854 319340867
    0x30c04050607020f06160302060a06060f080604060b030109091403190c030c020904141510090902060903060a0219090510050d09052e0b1c03052b0b03030a 68
    0x6540c201c807015074a07546440011a8406840ca01c1341d040040460184900b0b08140c0654944c5400f0360207855140d5100c1089100310b03000d034050305010a0115070381d1440c103031051044591104000d00b001580c580c98801903d140c0d002644010662504c51400d807080000300d45140803052090002141082090340c520b450f551102c407603200412200c00c2050091505c0303009007599054001c3e11035045424903050410a4040714102c0030024841c1c0c03041d42004505110503140b14180055102c0070f00782c00d0004c000060544410180d9000300144050702c0d0980d414000076000c1c1320701d00c000590310500311200d80b030840509007856040c000041ca0400080d290000000f41d01683c518009582d80c031030b143d1183c010002810003405c82d02c52042d09441a0000d6009000e480341d5060030380345c0c005170414404040c1c840e040303252500403403d040080c0004100071041c1d02d00f24441e01380030b420003000a01c0344201104480100303c001441e900d2280b2315034550f225010140c0c40a90196103004c1081c2005000c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 319343354 1250 319342104 319342109
    0x120406050a0c14031f09050703020a0e091014010324090e07140603130f0317010503010b0d0206030a110f04030204060504020426030405030d031508060105100f02100c02060403020d0302030c04 84
    0x705c546036500a449540384241e95005000d144208001c541440f0500400a400001da081302150107055805128545280380304d101304809804205030170b0800c6061103117081c0b440c200c0d50616841d075900c2e905000b01000c4540131151a610444c01c001c0c0341904140a075000c4902d903802903000a0000d0040040d80c504265820328103680c0140d41c0d03210034a0580108501e00c1021b0604445002020201580701400359200c000002031903103540d80354400c00d4221290720f1491940309050a0b112801400c0c04006158070811500c000101240c071002d00300026070040300d244075485000117040c801c602d020b2180c1d1000d4807054404600382801c054080340c81d1040005049855814140088031811040084601030400603091350700c000c005480c09406032031391433035580c1d040541c0c01020600c80c4000070703064121280100280b00b03042e4494010b031440701071a094901103004200b0416400429030203407004a40e06540104024a0079007002414584100708410405004100b4804484c003540c0681d400d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 319344604 1250 319343354 319343371
    0x190332010905090a141608120d090f1a040302150c0913110f0c060109110708030901060308120103030e10050405062101030606030507061b0303050606120406050a0c1403 74
    0x80b641c030360041c0365144c44040e0340e00410b1400580e02012000da004a00e482001400302d0fa8000640c0e283c20f941131300e0b21141040036010000c20b1041a075000320640203070600d02c1c010051101a1a11902d4880c0d45403c07802039546594840710a01c42010750410a0500400c0c122035410703401d06054003040a6407040701030f054464140c1c80030116a001c9194402c2018082d41032644c1c2d40d600c41076174659116040701c0c00c5620305c1d020707020000809000b41c0c060903803110301e03003403000785003034595607130210355820240582e0341540d690100440000c00c504003e042c2290018a03c20b015132440c54020140d61920041c180286001c905002c82141c20105850070345008848450300ca00d03800d002003480f54100c2410001310030280000105011190380004252030054040c1c4040039142c1e2020341d18007482c03a000d01150181e0410f40c401181c4280d0010707130001030081c50310746055941a007503c1c40c1541902c01b0784a00b0740d40e5007400501c1c95a40f01c0e29120300a241440f8074410315141d801142c03408010040348 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 319345854 1250 319344604 319344611
    0x60f040b07080a0e01050a0605030118020f060f040812090909190b07030b1903020108011203090308030c0d0510080c030d2f0a0f0605010b07050a0f05031903320109 72
    0xa481c05529000b900e0144d00d858000c11992030052104005060603110329070203075107030103d051b0940000b000c1c00001507401815a2803400e80b03070402d0000380e920924507090100003d11000c14205003c0c0700310491074200e8507030a92540e218000308901c4500c0a060402c0b2a404008691407041d0200002d180d82a00300c5820a4147e4614100341c01400d060790a166010550400486d6103000d01d14001c02a0380c000e81c0c441b84180e0b21a044005010b800e0368024000c1120715600b040042c58441c021580100c0d443c00840c1080c640072408000e407030301079039140c03140e285803130051140362002c122800101d81d00f00d0061252510040016024610382c1900c220b607200130345044c0c0c0385115400b81203018401d400c8220385459400781040004042d5003c4200c0d112414034000288207019070040d03a841d0364100c00540340c984000d03607442d4180ea081d5241180e445c001030103139001c480050b02c80340f0344c0030345951008110b800c500c403084805034454006041400480c1195034190b003c0b40643e15055a102c484e000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 319347104 1250 319345854 319345861
    0x501030515070203130314010c0201020301050d120915030b032a0d02150f030711031c02030702120c1f090305090d05030c24130203030d020d020702060a03020408060f040b0708 77
    0x3c03401d511415480404030b040c40180002041400c00e010b011003458400208042d03003151300221b003070b41710a125040d44508800000780103c1c409054268400c001410320399030381599120141040481c020392500401d64400380b001e02da084c28084800130403140d048a0444882c100b241c80d03141e14100b20b1072400760a0b004003550454072043c032422813801c20004240c1d10380b130302c0000030000c41c1d0048070715400003280400b000d00e80c21000010b9404004085440c0281d0310040b42000f802500001c0920702107214030a843c24502c0100740040c0100403280000c0c180b501c0b60200c0c0c040c2c6030b6030400c0b1800c1000c0e10307040d000400300303902c04c0503250407010468601201600718145140743d401440c06040003801804400c0c4034101c0360000060301c042c1010030a0039140d0701c0c010340e1008001c4184003e0b406810400c03102411078001e900404802d50390900c0107060524036004104a038000f5281000441c1c0c1c0010144010780081007400e600c4070189060071140d19107075480503000800a8990401d00c41c110011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 319348354 1250 319347104 319347107
    0x50607050c03070803040b2203052b090302240c07240c02010c080601180603020c071e031e050705060904020c0a0525210f1a01090b04050103051507 65
    0x1260103c030b8010104c5501e0341002c0c01c05211150041e035403400301e07981e110710600b100c1c0421038940c0d0304c0701d415442c2c4a0401c0c00a2300103074800b00c44003000101e10345125615501c03849d401e110f0344020701d000f41d004104203074a01c00e242480c1118241c032444594580c000308080c0b600350744104c2d214568004080556420007812010482c5254955007480d9402c0c840d00d4011640d0550004007002030320f60714007445489040c01981c031206600e007922a420302c1100d003405550300a8004040451034003003120102541c131602c0032519038500101059446000c40c04006000d140054107060140c6161041e00c806001c1e83c583d44d4681c0f06102d00c1d030185501055100d80380d070340c6505442e4910341140035200410580c0c40c0640d194513100c1c5030f86485826a000c0c5038002100142402e00b61a030000d0240303203014440c1c6410b80c000103d00004c44031100392401400008034400341f0b05101c410403071000b14607541868a000c0079100c0e082800c3e40141d28140040020503400034080c084030031104d29849094482110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 319349604 1250 319348354 319348357
    0x9040902040605130f1401123002010e0c01030501150e040b0a03060b010207090509070603111603080106030e01090c03020126070f08090102040f065403050607050c03 73
    0x1000390700c20381988444010500c0c9810505c07079800c0000c0e0070000f0a0042d507440c20002c1080c001c00103165650003050002405103c00118900c0d100c10480c010440391602050421102c5c504040060351100c0c2c3c071840c0680d040040018010f42406d052005605007850004504001e0300d82070200207002c15442680e840d540e020b60701d40c29014008040301c0d61682002805040b046405500500c41c82c00001801c003181e02c10107002d0742d6a1301c040c0c000c181c602102140034000c48040a40c0032402081810060f0103030085020b08284a600c0344401585041e4004c1c0c1243c51002d08101c1607418605c1e410009221043c0e48010b4a40c2401c2501c0c08980a43d00e4500903003003894841301c1000c0360301c148020290010410340100485990740300103035613801c1c1c045082c1d020328030803100081c0c1c240c1d0081c092203004e40c1d521354010711551031150140c0c0f4a0104000304109480d4890b101d510840c7c0c110049070304064000308004aa10000c09405156903074213030380d80030000c0c405405c00c0000704940001c04401d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 319350854 1250 319349604 319349609
    0x3070e3102090609070e0a0611060708060a090b03010f0507030e0708030304021f020a061e150b030c1b010501060e1309050c10030605031f141e040f020306090a03030c050c03090409020406 82
    0x1c1c04800070035200c92300075016400151038010707144104000146183c3c81049090b110b51800f4084a0829190800b200046c100907150294555202d2075088140c905a125003481030340389980200b4540228041c150030250140c200c0c04c0717282c008204000c00341c1c5402076810303d1800c280b0000c001814245a00700d007003c1010200600d0582070207285480721b4041c0c48084030910310700304100a02d06031b074030700300d1088040ea2181e4400180c0c1400020304100c2420b01030500c00c031001030010240ca1b19a4036840c2100c2090b0084000f2071052510180c1c1ca0610003000c00040800301c00c20040b00c040d036241c1e60343e83d0800d10850f5220380a5262541089072090300003000a16015084659400b4011141c40f12944201c0d07428a00625100c0d54884590380306400c50300560f45410155030404030501440c245140c000c20070754212514543c458016202000784034800c641c250041c3c0b0307a440c1c461400a0075265045049810440c2c01c3c0b1251f24201c0340481221820704d401c50b4001102d100500c00314010f0074260b1b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 319352104 1250 319350854 319350859
    0x3080402121504050c060a14030601021e06040b0a02120423010608010f1b0912080403020a030b040516050a050603190216030201060b0703050706050603070e3102090609070e 76
    0x901a024814100c0840b0b00d00a600c100d06854266550b8002d20400303000d80e80394240003842c00881d421300f82c01402c0040d60005410710503110180000000351440740c0c1c4604d5540004d03071007034040100303118142c4038142c0c014040c0c0106502c2e1802641c1c075480107080103000640701e0f560b0300705880c0252060b10400c0354107074480c0009001e8580d035071800340e00070046401125040780c00e04401e80d90800c84001c05002e41103144c2c0303581d4005800e2101294820f42802804c45603d1820000840941c0d280840c040085106401d1420981b51910340b603810124a00d011021103014400c0074040b940d10002d004e000d80d01d05507100d83d2242d90340b400031403c80419503028803c007407002402c07900005010717400a00c2c650181d0001e1102540e9000e1884051050741400740000700b06100b000f000403015081a6084100102291506038440310f41500d14001503800358483c06040b135222032003000d6030844000850305550500b078403550a1300416010360004054522404c0c0c090005055980540206480440c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 319353354 1250 319352104 319352113
    0xe0f070c14010c11030403020607140309060f0403030e0108041e0624030c0b0301151d19140405192c0c04050114010e011103040308070b060405130f0308040212 70
    0x241103601d000f840d1809480d00000c00000065407400c0000080302e01310b1754041c01d801c0ca801c60944800c1501800c01d01c83c00e10501040010800c01c0d5108000f50a00d19400b0310300a42d110b140d85400340801d0000403000381803045580406c004a5480712078140c40c0c4885441200e046c454a10306017000f02004408491410103500aa403101100102c564090301c0c8144811860b29445030482ca5190009100345481d0300f05548844084c81c1c420b800494031040040b5080105076804800154600410004000e242c0204002044580980400f0500182050301c00300f0860501808842e11110758108465219803241c01d42c6510780014401d000581d44146038404240c42c030342c64005d4607614110484c920a0303051034001304000782081400000d6034416107a62000201e51801920000c1100601a609000c184800004a03034220003c01445104408150040c0351035001c000449601506004c0e2502c003148950f400101d5040400d6a07050b01420003090560301c034400507400324000640c9140e280103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 319354604 1250 319353354 319353383
    0x3020a23040e010503161521051f0810151e15031a280b0d0c02010204050d150920040b031209091e010308070b01050a0e0f070c 56
    0x15490242050ba041c2480080060340d0710000c1580d58112152058440070401c802004100e80410090022541c0d604040364200c0c8004c07040305014030f6a100700c00c0720903250800c2102d1111100d6204254101440c1d541340105d0410201d155210910360a4200155039803c6000c03003504040004030040001c1580c81782001003685908026000c248500d4100d44416401505524007900031502c2c11070308160307048890403411007005041207080c10320906100a404507001a0400c0b030241001404c070a102c0c4960321182c0c5060007085501c401200c2045920500040c09541d46124603581c0c02c0d030b080300000034020804d207030141c02417441d880c1c0104811131005541040300051081e0748003844007280c0401c0300150030310600d41c079503642c2005038000960401201d006443d158070b003181c000070002c240d0304405d400c1c03480301500948280c10683c0c000704045202c0c810060f071141000d02501050700e14409031490b0402c0e07080d0b00c0e8006403000028203941c6c1c00184280b4032880c0c0c48034100745c00c8100c1249849 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 319355854 1250 319354604 319354667
    0x20403030f1d0d03051806030a1d0a1212020906120103060b0301110901050a02100c0504030c09020c0705040908130f0510050306030c0910030f03031a03010b0a0603020a 74
    0x101c0a00780001c03078407164080500d9030342d031052103088800140c0460f103550000e80e07080310300f5032051181c03e064144d40d051081a50321a08082c601c00e2405200c00a0000d104140c040704840c46440102c9840e07111680c5c00e00080c01c045100c103504081410030780a06505c80118070080c1c05140586034000002241c48030100700884078043c12070780150002c100600d1403000f85800e03500300c0e50a925100b01d00b0001ca07a090351050300107085c521090f1040e070301a142141c00110035140300210303070300000d880881c1c1031040c001a06003d400901010a04600e0556054500c58403000380f4400c0034425556499800e041c031018504544901d41e00c18000b45120351581400060500c81e4050b140c0100c5994074284c00c014007860407030b0b0194600a00400391124114200f0082c8039000b001d40310314141a100000028800728010080a80300b0b440201e01106109189903140252028507071082e810018209541e8880d804160155a854a00540d40d02c114002c2507480b82d0400c0482c402c0829120b00b000b4511 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 319357104 1250 319355854 319355867
    0x210c0c060702030d0e0109030f0e0609060301030f02010f051602010f05120f150d0c14040b060d02030601030f11070212070f0f030b09010c1707031e0509120307020307150f02040303 79
    0x1200d401358108013081d400301d0000c0c2202c1c1110390080209412207159250b4500400d007200725548003c1609190003044404201d03548c000b03a208403100705854085c24210368014000b105d00131602e1410b1402c19001c1c80a0785e06000280f072019050000c0505160880c41c0305100300e5030989202c450502c1c080c03d0442c041110880c0448603403002e440124041c00491510608a02000780c02128509a4a04160503843c2c141e0704000803940c0103179602c800c03000e15210300001e040300122551005840f0b03c0c00300c0014042e1801d40c811107030014540084010401c0c400025203040caa0103a402c04c03402030024425516042c21500f0a00f1141c20090300000c2800c8075614003416030744151301d40c42c1180c80d82d21401c0d0a0360b05c1c1c4840f50010038016401c8021148085140e107070301046510300416a0a444e44d0041251f10402102d0481c3c503464104000309000100800b10601e0002c000961540c901a0390007034480c091031000501c0a006086681417107090b40d044040d01010055003103640ba0760300d1038041c240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 319358354 1250 319357104 319357117
    0x607081908010807060509011110060303090609141003180209090703060614060f0d1503080306100e030d0c0f0b0106050c120702010905090604140903031b210c0c06070203 75
    0x351640c00080f88420300031440340111402515100c0c100301e440001951443c100041040142c03003880084142ca040f10f0007028025406621042905400c011004080f460b4581110b502085580c2c00c10039140c50703030000002e1545036440c0000b0009150010005048009040650301400342028014030030f10124542007101d08c643c9040120941c0d41d81d150402e040324180f42a803185090004c840b5241c0c10900130040180207aa00003486482c8402490300c16034580c0080e03425080100c100101810100304140d281c89007030421402410801d0300080da01c0ea24802140e080284c54001c03e001c200d4070800c0401c219901c0001010b41d9a1110302c0244260005101607640344226880f07040c0c20804d039404c03114290340680d41c641c0058188000d1201081c00030b4800c541099030f03411300944000004260902031000340300510350368244102c0c403459100f0700c0c88075510b420801300004004400000ca0b030b000380382c002040101569450146490b500d000d8007001d0f030040e004072404c0100141d80440200700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 319359604 1250 319358354 319358357
    0x3030206220203060403050901050403080a1e030203100b09030c031c0f1b02210102070c05030609030406090314030424200a030806030f0a03090509060f180606070819 73
    0x1880079082542032280e01c0d0318240650150001c4011501180c4a032009020422060400d2481c269599660722030b1507114a060783c00040882c0c03951000c0024101080c07070545000c3c40c05509505207e00304900140030340c801e06000b818001203150081d101841840e80c00031004056881214030500c0320301e00e1030403400c45400018900c400800e015402084500c120302c5d51896a140020402c4d0b007803110750081904495441c2030801045403c9410900050180f18807a40034050003038074104c00d16203000744c00361003a48550001d010a20455074408183c070112a0070502d02e001000030201c501c0d00f90710541d0020b02d4000c0304584014403c0640080701d40f5038011035503c3c40d246655041030b05c43c1e11880065441030070781102803c1004030384641401da40201c0000d00380d400c0406020b16032850007920000031030208130400d2041090b03151000c0115800300090300d01c84911880f000000d280d03070b140810b0000d001c01e150800304919845100503a40f1319a800f0b126582d9450150b1201762400c041c8411500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 319360854 1250 319359604 319359631
    0x105040c0f030c06030c0c0b041506090b060d02180303030f01031109070e010e0f100906030501050604060c0308130602070809120a0507091806050a0b1f02060109020a050c0703030206 80
    0x107100c62250380c018100c0360050806103581d41002c0c0304a02030002e0300c030306608000020383d10030040380d4510041c6000704d00c20200c2d4421000910b90800540d41517034003001844e450011120b80640b5108111820080429801030341c0c0c06031440c0000000e11a10308160705480040308000000500c084c50605880c01080017407103a040000401c07402581c1101c4010004655000070182540151550700040d6001031600c03441000c50804241c0d40007523000b4000c0000c400000401c0495011321034035000d13000a540040c50581058000b40000e648008001c040024400010307000402d8001c0d140310260342700c00190754802e160704161041d40c0020f0007840c441d03a1200c40c0e2201c503034400203024882640c8000600792580c984810240280f129450409691051469601c001903142c8105442400d404e18001004480001030140c0410300c1d90203805948990f82800034103d4000654a0440e0340c04030307000d40d9504103034601315520300a0400306a0280706201c0084109a00130031014440d200c0c6004d41d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 319362104 1250 319360854 319360859
    0x190602030901140705030702042304031e0207080715020f0109050309090109151701140a0f0c0c030503011a0f0d0605010f030908030621060405280b0604050402011803050105040c 78
    0x100c20f074490303000010000d034000c210070b000600741508420900401c882092001005075000205055812035044001401d04840f0449a0300300203981c085542d0144000d0140f6401c000c00c0d20382d11032030f50190300c40070801d091b50484800e10811412040d9407107907000703112aa1492501c90796070f400a2008600c100c0c6440d0011130f0300d9129104940a44101b42180414149802c0702da4090072408000041a5500d03140960003254880e840180941c0700e40c3c20000d1480801c803c83c0040f1001d04200e07008110244181c60302190740070003900e0550b07032031207048600b25500003500383e040e201e00315070303203148281c0460a0258500d45501890803503e0a80325500100040902101284c4074000e00510203031041c4081a2103042c050307680c0001d954402207102e4140050122175160840480b02220f480e800380d0350700070b80401c40000301a03000402100000400481d42d4402203c4400101103030b003da9910300008095a11524804c3c172108622940c403c1219141e0030114041d00c0100c40540d030000702807100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 319363354 1250 319362104 319362137
    0xc0c060311030703200711040b0907021b010c0c03080d0b03010b060d0b03010209150307090e0f0f13080d0e0105090c011e0509060a05030108190b01060e190602030901 73
    0x50100d00c00074946600d2641d81e030100242c00401704881d60b80b4660300c0d44000c6621000380100242140c034000c80140391010114401c0005a40c00800742501030601c140034010066000100000c103a45003500e11b4904040c80c0f80100c58880409201503c0d40701810700c008103101e1480d008007035004074024140003440b0342c00700b45801d81c2c00545410703030008401c10400f440c02206a015081c95080200058501058000004c01020b100440442e40c458000f0600070000d400880c240001c0100c01d51030710300d038988840c0c429808a4000c084007105c40c48040050300303842c515140388444560000300700b038584026085140043c40340700904600c41d0710b08800f090140e50001500030036144141c0d00c15030300100790341040350f80150103030040f82031150500030340711550388071400b500c411409075551548030b6140c0001c0d645880d041440c400504250aa0440c0105860301d40c090306541880c1008604825100041094056185026201c07071000b501d010602590120003085040c200340e8400c02901940f102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 319364604 1250 319363354 319363361
    0x601050604120804050a0915120803060402070f0b0708060f030601081b03070305010f05060906060310060f051308011a03030c0d080402012010060b04030c0311030f0a030c0c0603 78
    0x24603940690248400c200d160500251070091078841e9400c54101555080400c1c5000c059410002a5580b144580801c2c0320081d500788000b4211500c041018200c82d8840c2d40f0340e4480608001d00460b00002c00b101400b80134211104010b038407401c0e0040a1401c0d0400070130130071303066075558401d890404d4031108500d40010994141c40d26000904486444101300410300c8402640303e80e014050b20500002041080c4107074440d13007840c01c102184a00d0300a04004401c1c41c0101801e01c950b60a10a0181100e2901501c01c203a809505003101000065042a111383c002e00b00801c0c0c00e005186d4001c11060010341021200403500100300c8881d0400c1010562a4011030300d513002e1590002002042880c840d10607030741c0050043c100410704900c8944416070900e0360051001c1907502034071440950140c0e80c80f40e0001450f0b0501d00504040c1141c0e20110040c15a100143c110070260183c10341540d801d00140c1a0142020100ea003400010300e030141026885000541e148003009100003900750180c007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 319365854 1250 319364604 319364609
    0x30e070f06020303060909071703070302010b040c1b241b170a0507050d020316020609010b030a060527151608060108040311010509010605120c0d2d031706030601 71
    0x300518150381c2c0300317424014014002080b00306a0320503403800155500240d54507400300910314000c0d69454030030f82006400c2d03400c4080e42074029803a00701000754040c2d01c00400000b0071320101c0102c2011b851070a12001909000c40c0e804003114503940c1014501007543e014180d052443c01e40c1141d03908000ca81070300c010103120032144a81103000000b42c00c0080e15480560321031030304e08103a400d0401107140c0344201e810444040d1850250045184c00a81d01006015886000030303000303114042070319020a0701e0310403031040202500d88a50118000e45420800001030400c4000c448a004100c0011503507101044146403c4034007075203021888072411140c0000c030500c0355450b400c103da1907540044945040040054040240c45803042c24040700a004290040450100100c0d015007800c003080902c41d200303110308800c2e500c0030f003001d1541d0300e614510349800ca400821001c030408409a41e8641400d040580000d400100d008000c105038001d21044009110307803031418450368401050650b200005e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 319367104 1250 319365854 319365857
    0x50c090603010b0d200909060901050a090b03030c15010e150a05090601031e0501050a172e0f0c140702030c0f03210706230601051810030e070f06 64
    0x1c00c01070014010030f2000340130949100304005130f0403040b40d455205400c520f0001580000000a42082e14075207100070743c1d001103048648400a502d041c00058440c511440359100460300c4a002008a540600a90f43c152040e90282c1d080703200c00c2c050381c3c0300d444001d0140b0701e84492000301007503101260040110b07581e100904484c0d101b500700401c01020384d40c0106594101621340c0084440c2d03841c1185c002c151100d0482010649504000030000b00640c01e4110300e501500d0503245040d81480001c40203601e080207403607c00404540056049905d104041043e4494208181c449d6800d045a00c0341d6800c1d259a0b5500d8284445854102c1e441c1c4030300d40010b981a444040b180d43d4501d0001c00052640c0001021140c0c080401310300c03205628001c00450703044882c0458400140700703241c000c00c01c4800100205881c64408000807207000000500703660304021010400350f0b1107100142008d200150b00610b2003030346894050b0010080d0000b40c6501c14240900f01c0005100032201030180c2c240c8515 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 319368354 1250 319367104 319367107
    0x708060103030f08061507050a030f020102251115130b04031a0a32070903050d1b14010207030e060906041703131e06080f01060c050106080d020a020301050c0906 71
    0x70140101c40c0d5070070140041d40c1c03040003902c0d006d2504c80d60707000400c00e562241c00034040000303107400c3c090302c020700075074110065900422801c0030940e204411064030203200000c20740c1d039030080c0c03d01030088102030900c56088001d0810b80c43c51161400003a1001202203102601c071700703444042603003081c016840f008020050602d240a81200f107580210340c000c0c1c0c42e110000e00c010600d80c00b6040304443c912140c40b0805d006220040000122504941c01803540c204110712038510703942c00c3d0340e60003101e107070000f0011617500c001c01c001100520300c0621343c1c0103180021500038443c16a8000d5024880440c0402d044581c2c0024904100c0c065420800700101200c0c101464503a402c43c07508000380000f5000e020811901003603166803a4254081c1800180c058402c10115181940700803198003d582030005402c20000c00030b281e400f1650542d0b2152a100440e507142c4e24085000d03015130b410a20a6004010710034842550000360f006005008800911540d102d40311844024814481401c3c4c01110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 319369604 1250 319368354 319368377
    0xb0405012004150309050d050c1009080a1d031e06060405011401030f0b060a020a03080901020702030a02040b031c020d09091104300c03200d11040e0f010509070806010303 75
    0x40f9101c01c00703450002d04001c900d51485a40d02c42c10a540304030700d0404944041a50900b00d101040413512a9020500420180300781d600c0f0b400c118041d600c000420040c0c0110201580d00040949802c42c09014045402c40321400c04d400b14a0420840f0011141c07248100040091606020320f504039042c81601c0303403506001000440150502d94002200c1e140c6030546480030b5100c410052140600c250f02800301c100140c40c0040c10b0b10300c00307007000c001a1300500c4298050b03500410980c1e810381e030440d00000d05401380800710741050300340c60b010011208090098954146c0216551741c803c2c00d0755443d16401030722406a00d08a80003100c000403640802d10040c441044019104000944489181104400c5403003042c3c0444800c04030480398071400800800410014002e101154150640140c44441e0740d40301184102614076805010307840609940007243e02c559100051000294055483c0820803001c0d06000c0c10081d03c404089100300f600020381401c021420f14181e80d496602d2003041c0d031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 319370854 1250 319369604 319369619
    0x408152404110906070c09050105030f060109020d14130204050703270503040e0108100f020f0306010c060f0c11060105010201090302033a09020a060203030105010c0b0415090b0405012004 82
    0x800040c58071440d210420030a4a2692004c025006041c400d40307185216a00707044000056400c10313130100d80a580110524800d4100c041401c0e419911f0101e0010f88595000c22030034040d0284d161608040c8030f290007403140401048140d840c41c24000c0e541030180f62101c1c9400c03411580f00c680d03603050402d8131421155558801c03200340c040c0c8d10b00030b40859081c2920740340d618401b100d081e4042c81c2e090748040500881d08100340a41250400c50440071070401809488840c142d110040000341041809500d01c070806c51690300400680725a04420011789000103006031150034010100100c0d4410f05000140540c414006c807010142d0541c09903081010040094450038003010a81603c00c1c085407680600520b080d82403400140860000320303181e0717198014030030307200303c180c03c0751086401c100014083c690704000d800558581c0500a440c4a03500c90030101260301c1540070a05095061825840a104001c01018001d0b40120001c0003008115070184ae80104400354002100905000400254 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 319372104 1250 319370854 319370861
    0x8030a0c0503012709121806020109030915030f022a010204030201020304030803070306030f0f140c010813210503010807170a02040b0315042111071502120408152404 73
    0x455941c103010035032105c55600c2c5284154000d280030005000c4400d1100e00c101d0518102005284a0000300800c0041e80c400900300300e4107000304492a040b0164454409100303900035451140809070440d145c0c0900d110110141d2040101c1034040304070001c65188200061080f20220381d8140c00031458203103107a40b000501c3d0001032040e0185652110b001010a407100c003004040342c4034106e55a4045503619190b80c811008040e1702d403d5500c81c0c03042c0c61950360008040c68014584510721420a10149851040d0200e440d2510143e48210700958844580100185040e40c1c410410385d00d1494440d02005001c04c16020151402c1c1c1c4800031b82c001506142c1d01078800000050262120b070b400c4020300e5001c200c1c0030b403800c6648845070062580007100880510681004600d0b011640c61f00813049180e607441c0c2030060b40f01d580001d01030102a01c0c0200704000036860500c5000c0d40352652000810f484221072011020480740390b80c0061140d0411400c8100e643c018213000e01d030a00220303c24070004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 319373354 1250 319372104 319372169
    0x70e1303050c0d030b15162402130501090b131a0712021c02010e07090f0212070c02040b011b110406080f06011508040503030c031506040308030a0c050301 68
    0x14000204104040d1503418080b443c01c421254a010a0100c2050705011b05800c100c03869010074803040c80344000903c1004030b240300203608288840444155a01004450008213245100d4a84002820701744020710700c000310202c0f0800d0322141191556500d02201d18407403040c0d0400d20784c020b65014440300e01c0034038042e118880510038003030070702c0344641e0744c0c100c582c1006403482c0143e4012801035034100100c2c07a41c1d0925280720320091100c01348064030031303544100354000c60300f12a07254403a01c1070502d4180e05071101c460081c4000320050410000c0905a420950400d074001c0741051710502d02d0794020100d03450412022094000710a02036111103d0110204401d039902c95115400050002000c00c0411049100070740601511f51410298166468004160704140101c031010031020030404800e507a841004660300950b01e0b03031080d514107803149040c421180d1040300801c001c4240500540994880c0901700410040c5c029080740941c6c1902091041c507845c50404403c0c6d1800c48040d002c034220 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 319374604 1250 319373354 319373357
    0x10603053301060302070605010b040b1605030717040e01091505130615110c090c070803070c020603041406090a0c060309020114030f040203060a09020117061306080c040b03070e1303 80
    0x4a0714600304800044000070f81c800300010f0340116101c010322840c2e00c86d0a0040c07100050741c600d041e02e440c540354402e014880741110f40c000803400c0340052180c00c3c0129982264013150006865042d1200701420303030010301604122240f600000325401d50a48143d62818079100c00d5407076090f140104202c2e010804080403404641c507a4030010340004051410000f09940e6203410074040d550810141c5048804800d65105545c00401e12141791115011241c00c40d40104420b0341e41d0343d400c80c040d05d039186801e2000f900400c00104000c1404a20609000d2106084003541d03400e031100c04403660740b0342084002501815000d01d003004014000d0748002d000e0703441810141440d8208104c0b0661a800c1203881e8500a2103030b80c108002c500d8184802a88884451400c00c2201020740001380903184a00001c0c02282080011621907a030b4884146500c5049e00b00c107100a941b40c04025444d0803010100310300a1b41800c402145c1443e000c19108156140000050076503940c03000b856400c0c0040640a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 319375854 1250 319374604 319374673
    0x9200301020d0606020c1302041d100e09030d140f06010f2a03090501020d0e0402030a0e03070309050a0f03030816030603050f060708012304050a0f0e0105010509010801060305 77
    0x644076290b03030080c03000a1100e9005030a40d607480005000310607440d090303407190311803042005024078a038041c0c0f0000d800c9201c9210b00c86a542d03c42c0c21803147d4216401c60a103100450381040318414001004140400781c0101c14481c202500390002c40c160029202c2455240383c000000e07042d54891040030302d018810317161502070f081c03c070086103581446802e010280c2e0042041c912040c50382000303260000300021f20003000320401c41070000740700000b8191494420ba40010109000b600d0395001404401980025a5500d06940c580a4410b2460b4811240120180c2c200021240c420b04a4002200d4140d194018980e45031000142d401c0d66030420304043c1599144080040b40342007040b007926018000c01000744d070408040107400c440050b8450f45c4200601c2e995407201c040708144840e03403043c05a40c041400d40754091494054000401c5180107145003450f010040141500101e0403103034141c1d1a801580d880d482064240d8181e400040c00301da00510171b43c3c2c660841e001902107003905c48403140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 319377104 1250 319375854 319375867
    0x30304051005070501050709050d200a260105070c030302070f080c0619061a0306030a02131d0c210709060605030105090702151605120406020408100920030102 70
    0x2034000300e07400c01d801c1c002407804180e040030810244503445c1c01442c28100818020300d0000040c1008444d4000240180d52018a10892540c00380345280031010080c182e0034141d403074200225246203008441c4e00006280502000c1407041845803030700825542e0303907414200d8a00d40b0160065031200320201d0720801107003e501c01055400020300741d401c02c3c043c040c050b0781c106010b036074595000d240401314005190080c1008500d00c3e07882600c1140485482141d102ea0b286400241071803190315029401551600c1c4505100086030711403a10500c4581590724107000001c2080d0341c0f003000d010004d42260748a6003c40b5910451000380c540c1d8484001143c0300c068480000d0000da8900d540000e003c10340c00b00060015190045041786d22010743d10041c0100101200508090307030b005408003580004000c1c5000803544110225107905800e03000d01c0c140c9082c42c1c81c00c0802035002d481001c500b80241c0302c00401030b068a00072201c1e400d810040b1000016802e0f400e80100e045030000d5240c2c0740d903003000403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 319378354 1250 319377104 319377109
    0x23f01150c17030405060708011a0405010f02011e06060f030209090f10080a0b07030e0a150e0a0512120c0c0607030c17040308090705030312011802070807060507090f0602190203030405 81
    0x3d40c0b0442c4650b0151105043c04000a0b1a02c081030300f0007404c602c017162031602c10740080410b130740c00c551003460314802d1502c1c0c06900341d004002104142801c940c0d030405685010102e50041011103900780d489154900400364100c0880c0600c28440740c0c4840c0440100d802140c01c5100e00c0d4010907200440814260380e5801c0030315044004030f04988113821142004032007505442080719940e01900504140406a580c2c43c65864100300c140c1c46680d07484840c0c0d042108104507050003241d104084a62a180b103054549560300101a001614124900043d51140740e48059416440703601c070040c006500c44150540242402700d0603a800c011a02c84071280d00d160040c4054000ca0003921005500d00300f00544e030b4100802030b04000d00aa10401460701d4940d10103a01c241140c2d40355032090051b404c1031168001920409101030140d86001c26490140b2206602041c0038051607101c80c904585e84000030421104240700300000358101203014269600103040d000001031009040e24a800c0e100c800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 319379604 1250 319378354 319378357
    0x12030c0e21070f0e01053021040807091116060b0607081c051e060a030602070516060e01080c090109170304051305160c0501023f01150c17 61
    0x10b0b041c0090f8032402000044860307118140075080030f9800504004840005d10784448801e501781400700a99042d95004040503c0b40700690002d5070800d40b0200da04000401d440c4d0003e000c1d5000c980941c140000d0381c080c203403181c01007c1c214103640078103003e44c0390440b007091038550200341c1e4800c1d220403003000c955a8070002003e01030b10800200d6100c024400580c81c0d1a42c214160b900c90707900c1c0005216550480e14003101c1146008400c002580d51070101040c003184950f80010040c83c00441c0500c2049008207c02c28070819042c00300103000c0c0e0380c00080318000101d00380240401c03021008544402d00d81002804a0441070421035070060b5100d502100d40e021550191280c2c1d0000b04040c089891f02e440300802d1b503da1008184901c1c1001a05080d074800364000d01c00074070182088000070400d00790150381000e00c050000c240c010507649400d01d00040e0304103242001410490b07200380c1000891003000e0685d09032141c0c82c0b02080015805a6940b0f00142d429101c0f039918001801000795800d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 319380854 1250 319379604 319379609
    0xf03030b0d080d0c02120409020f0906030c070201020d020a0c0303030e03091002030405034e040f0f0e0f06010516050f03090f0303030c0a08060f040c090312030c0e2107 74
    0x1c04650340c032014400403808030392001d00500c0464004481646e00800c100d02542d0603241503440041e0b03074400c0c81e807110020344511286141c004401204000c5c0700000300380a042e0b054001e030295944c41c0400d2130101d85404510790000c268807480042400400e1203584002d03101da0384079003160714006004000034650303440c90705078500580c00080d040c03010b4207047c003050111000040001a1a2402c3d6801ca0302c0e8a2500c0740f0a81e69008502d20000d000c80300c0f0000c40e01240c0f1441c80180d5444d00d0300c040d50000c80030b600406151000702500002c84800c00390b80544160204030000d1442e03103030301c0011103c1780d2003c0d49111007650301400150204005221000792002690000d582d105040b80c24886140032108d203245c86504144200403509101c0c13411164950340ca8640310702c16503510350000321410342c450304080c1c0052802c084004030b20f400c2904c4000790b0f4040c4006000540d020201103040d101e000c02101e00240c103d0403a0001410141001440d1042144040344040640d1503010302e003141d150f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 319382104 1250 319380854 319380863
    0x302122b090e181009050c04050402040b0d0f030f0c020904200307230307030c060f0306031202010207050105091c0507151b11010203010609030b06030c030304080a0317130f03030b0d 80
    0x4504000d40c0107000c106801c130000703d81c0c4080c403084407542c58998854a29000341c500682c3ca400000c2c0031507640d40d204502c11070700149155854109410070100080c0d44a0048000c82c0c69032000030386103406069580c480550003002403000e1303503ca070b4444901000340c040c1c188000205004a0a81d507600f800b001c4050400c00c80c15200b14042842c02d05402c03e03140c42028000c1d04241c1d02071010888190400d4240d940d54100b026999480312401c500805059002401c03080443e007401001035030640052001a016000030312040c0c54007c0f100da02d5850030801954180440420820007600441c040d242d0035001c1c21014101d00c0111200c8000e5441c0e40300c5440c00030300c680207459000c1d40c11801400400c3e013464021030456040c410302070304001140c080600345e000035200181080c0e504104041c400b04018055036101d5a0328910160f4581d03501504402080041040c02d05c482d032034a070594801e000396401f221441c1c4054441e18400300c01300341c00f030302056100c040e565610341f0744003c50030500780304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 319383354 1250 319382104 319382131
    0x708090d0f0b0c180604050a060f0c06020a08041b051309060f0914060a09030504050909030c1510090b0a060c050a0501061202150a1e0512010e010302122b090e 70
    0x1060012106503d584d080140700b4030040c401445103403030710b641020546011381055503c030400b03032030251814105480c004104600008154103016032140e07055002d01c1c4110180e8400382500c00c40b800c8444214042d283d000024028140301c2c842090300202019802090000703036029607584424259600314405440151410f00a41c018603020003046a1215001c00104500000d0395801401d62046100f00c81c400c2c03104a0210318060002c0c01128240c40e0341c41c0071642000c031102c1d000c010b0510115a40b50860000726000920010a4080e45103041401005480d00e00d040c07c0d07080d10b50361f490190030713940e0744a0350343c201c1c0001c3d0007440740d0405484030b1000c920b40342c0c24501c1001000e0600d603c1c80c800c0400d0501134858070b90b805c194100c003012a090310b03000b20f0400780982110320380200c001400207407084d0300000503100200160a41600e000350b03000b20940c0d144810b1503585400316002010320b00302100a5030b1540542d140b40d181300c02c00c0742c42d01b40c40c80b0356620101400c0c95070584484410410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319384604 1250 319383354 319383367
    0x30507030b01060203030f2a03160206070e0f06030403200f12190f0210111803070b0403060209040605040207110111280503041e080c060708090d0f0b0c 67
    0xa03285076041c01001c10344000d40c0b0f545030088022031391210140c030114030008031840c0300c280e4031071421000d000412900b01d05905e9103090b0100c000000d500508040150040304041010309210b800420401607014003040001c407868428851503038001001a8100811200c1b4942d044250038a41040d0303d41c824014503580c0c000d103502c0e0f810161003004003044800100103050503c046691482801802400c0454503c410040d090381071200c05440e0343d1045240c0156809070091450143c2240181882d4161200c1e01690a16035500c005005070038858005220800000b50b854004003480c0030084c0001c50340c684c0d1000403405136005050100c0b418040700c4d55801e82568880040b00d1260031a000410203d02c1045510f012078500d069450041054410310303606100e0208122002880180c6840c000b21640580e0301446912501400d240ca0155510224071441c000e415102c41079003101030a480c08018404120040c42c100d20129201c80300c2c0c80c1904042810b0340c203441c2c4034292402c2115500c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 319385854 1250 319384604 319384613
    0xb0c07080c0601080d09140d060b040221060a0303080f04080405180a05060307050913030513060c05150c04140f0d030e1009030510051e090106030c0806090d030f060b030103050703 79
    0x240b04143c0d5804204c0404020428030681000d101c918610948164020500c6c1c0e06180303016085204c003098000b400080c00c04942400000c403031203d070091a00cdc0300150748402c010001d4000403840041c000501c60700110310440448a64140c00ca881407107a02c3c030300351303840d004a0b00e01504292000c1080809804000031011240101503225408801811000e410200000d5401c0005415a081000c00301400d008060081084a400e035218514204103590341d6400140b600c0e102000c111024014a5145940c518000d01c030180550b00006500d41403508007190040c541e500101030540c41381c4080350b114400d442c0e00900313401582c021380e01c05010060039020302c5800400c000840301080302102007040401c0000c40c030405020f8003a540424941c0300d41c10040540140c056180c2c40c05120281880321070030056210000700c9108036902d1100075a120480f03500c480d0126220f2955412081c603011405200c2c2d03010b0500412a0380c0c0c002899901c030301d0503c009800036081180c1c941d100700800e10601 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 319387104 1250 319385854 319385863
    0x510020a12090614070209010603020913060e0720211c060f12020906040f0204030210080a0b090105090a0c090b0c01021e040b041215020d05060907050a0203070b0c07080c060108 78
    0x2130800e01051884c10000ea030204050390814440d0000300b690120700b9000903500d000e030900110320b0090741802041c3e01e4000445045a003942e111010890400b4510105a000c0380e011000840c0c40c3d020380245004006082c84243e800d0130f0300c403111802000b00407000c4c0c0a07054545009942d0500010fa000c0c2000b24000c3c07811455003046058104d104c0403032005035604c0e5617696010405031008643c1c2a2a03c0b40303500a80076a4100940c040c42075a80100c8281c1d20000f003034420f5202c0e507820702c8007408110a014081c135085c000c9580142051002070f032310108c01e400c003060302403241c40d100603040c0d030340e14090b40c0070b401c012601c43c0d00c0d940020b404111548280d281800288101c2d408074601032070f1a44c0304070144524415040301201c141a50414403856054007a060643c4030000d65441e14041c0000005050440e612441b41181c840401c01717040c0309405a170021300c82500114607200c010b484a04188000600c1e002d503401c82004888006030f1040042d180d40e414080090026505040c1c84c103050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 319388354 1250 319387104 319387127
    0x80d0908010e0d030f14070c1118160207051009030209010902041511010b030a060e0609150a0b040e030d060815160e041508031305010215010510020a120906 69
    0xaa040403042ca041803004104048034051900300041c861510b10454005044131004406002c0d003110108400290410307076413000e0610919003000b004400e5010008101c1101401050400e1490000f1796850b10341d07100d080900c051801243c030b40721b41e03a80c00a84e100b0071403501140014240c4008008609082c03840c04d015180b00501541003904000c00322003020f8240d20540200030340c1c41e0805620749020350100d540351030701906803402c4000e42d04142c2e001e4884a00342042d40c0c8650f0700003800c940804a4036403c20000281103c04640724607840b400504400d680d40ca42c441d07950f16600c0201082040203080b0420b40d1480814001e20f440112401c04000904144024003a2000c00004544a401c507000b42c0b459401d1001d101d00c1c4a002040003003443c41222401e91000301c1000c1074507400080030701400001048580c405945540c0120f840314100402a207200291800510945c685001c40c06c0140e400c1d80304a500c0c174019034072549025404c03401e215010a10888040c000190301c80407a010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 319389604 1250 319388354 319388369
    0xf23011a0f0d02090c031801180c0503011526190b06010804080a03020304060e0f0a0c090b0108060d020619050a0801060807170a02091002070807050d0209071202090901080d09 77
    0x20802e00c1e4010a02e0700c1c0006064014078000040001c0000721941078009103613992400820600b403d07070445103090041d0440654a80040650001e190318050003600b10061080d050410700310b03d85040310480031840340480c103001d41e1101c04081c4d4007004019410b003510441d140280d0b0740e840344c18807082c07040c0080c0116040180078001c00010034110011101c500404d85030069803680c590030180c000f400204a4804240039440b00c28841160008076040001d00406002d0061551307184010211030038182c10030f01040060000404c1440d00c225044d002c1400a8145440c000f00b002001c01c0a10b240c00704800803603004243c0710700599100075150301601d040d0030b101e040e85c04d00c46400f40031404002d894000402482001504490b5550140c40b5120405071107000203134003000029464811a0240241c188a28000014030f45061318040c180d01c2d401030655590b5803030f644000c40382041c1641030a01c2e9150204490b142c0ca13243d00101c10700034100e850140c012580c20110040c0021741e5a0f00009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 319390854 1250 319389604 319389619
    0xe0604060f090327030f030e04050a0c02120f070b0103080c06070c0803180a1b0608060a0506190509210c010c030206011e030602041508070302070f23011a0f 69
    0x800180d00100c00c07400140001c54000304c0c40b81402039102040da01500003c203031041404c030b02010150009031402014504a41c02d100d0755a1702001c10301110483e42c08100140c0c040d503840d004e606143e0004010070403003020800d10b0011192a040200c680a0b80111030a500004020044c03402c280f0280b0780124481c603050188100701d4403110700790f000c081c0c03a14464101c400b681001244040120002d843da00404542c85c60035030701591040c139100c80c41442d0200b400040026021b1030210440426558010700803810508800007010301c40c403020f409041172000800c2810116969406400030013013250503008580b030b03480126035080425441520b41272001846140300001e40100c4d40e141500c81184440792010b103049247e80828095901c041c0885100003030100d0150084001103400c0e0405858420445c2c4a0030822002c03440748590180800a00b619108005642d00394110b11200074a1f44e03c5954803040c1c904142160004001050810920b00d400c42070350400c401200d040010488605 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 319392104 1250 319390854 319390871
    0x73305040807030806060903010c031e0b0a0306020f0f04030606051e011205070210050a02030a061505040608070908100b031b031209010c0b18070f1805190e0604060f 73
    0x38481d900a1000040c180007500300020f0141e2a1700003130321b00c1444014002e00c000c442161024004283c80c0c1020001768800c40f4410303841c04441d01800b003400f1000342c140703140c2a2540e10f0301c2e002500301a00340401100d0400609450622000140c00614019440080c0751031404080280118040e00349800d80c0064055880c070607a0007800740c411040d100100460743d5a01c2c00d90482c100003840d0322100181c0d1600c0f040c4450200c01d80d01452203000c48800400400d51544030384c14000030400030308400641c0c1003105000e082d2050550581241d1542000e80d011620349100604124401010b0303040719aa4803280350442c0303420001c01144e4113524000540fa4100364000c20740380c90000c803d040810200140e854260b0b4860001e03815615002803180b111400d0201c4090300c0c010391503d801146221b52003002c1620451442030b00f0469803070744100c20a030400204c02a010b00002440c44030740300b5080d80848052081401120b814103044c4024016500e42031a14104031002451286a8945071030000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 319393354 1250 319392104 319392113
    0x7150f020c1506030114091606030b100e01090807030605040b1e1306060302060301031b0e01060207170312010315060b0a050901110a0819030501120206030c16120504081902011b020607330504 84
    0x183349485400c1d242c03880003190580d0041e070f071382c4003980e202c1655403081c03074000000e225103684464000e46c85000404c07402e4403102c40d0b04440d0800b00c90489a0b50802c0c0380810314118282c0300240b5500d1281c007001c5816590313600001c031140c009034000c0e01d100d070380c0c580041441f0109840c040090503c00b150320107079504004d0300135a244501e02800d20040300256031016010403c0003503d0022210344c034007404c59a1a860030314420045885070340d14080c2003020209155024006444082d04c1d566507280c00c1a80c8000112801000e500540c2d83c00e0052800c48801b04090b074006181c42c1607001006403030819045401000c40c1d01c16480035034044922881e134030040e075928007143d40003445445480c0d10340d00c9010110810380690400103100d278110001100410f60400d020b0012502c188054804050840343e4440d03110807454002030000350005011915140040180b03600706001819190900c44603640388a103541201e8a10342c035614905420180700d0100005100102031040001d000307905190b42c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 319394604 1250 319393354 319393369
    0x11030f01050708010515041503060509070f0503160e041505151603030b0604090c0906030f0e0705150705160e13030905040209130207150f020c1506030114091606030b 73
    0xc1500c980d0305030800c03a400c146c0b20301c00e48010f080e100489141010401e14090001c0c00306110300e80c05003e030280003450290048008058150301c9440e810310755512050762000940d0541621428000c20707900030f42c030350b490b2403044c0c40c00c600e14903928074603a6051108003c0d15000c64101c4082130303d402c00102101b880000520280f007640750074046a0700482d400000e40d03a00a0750402c1443e18504103181c42d4140e404180380084030015102000304005c1181010103a44440c0005801940b24a104026504100034408000b698400195007001e105980b018100301441c0d22440803401d140c80d082c80b030b9000d00180c030b58015101100d0485281d5080c3c3c0c001c0d1004525100300d03031081b130b0b02041800140d110411260709248006008641e541c0c8149442c250382c00e00c07100f85548d200e150001c09102d00c140ea200b10f0302c107903280c2801011400e00a03d1030701048400100303050703015504c98443c280b070301102020345c5004070842c00190450050803602c4a0b8408610350200d8105400d20a402001d07841d19003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 319395854 1250 319394604 319394609
    0x3010204050f100207080a06050a05070e1c060618060801110a0219032d030c0302090105040b07110603180c10090302010507030201110f0a0e090f0f1b0711030f0105070801 75
    0xc070300e11031104143c10182c1c20054140d1144069000742e40802c4100010743d0f000c9445840d00c10800c008a860b402c404446010720018929004480142110908050105800500c500c50000884e155440300c045050007504542d1104085803204418000000d00b80078032010303480540d031003030700b0b100a4900007583c0317a01c6048026146102c203d40f400505209600c4290706500d42d00100344100b01000184408040641c140400245000c0011400510900840708201c0f4141d5510741428180341d14001a5032000d4070403140ca80904034500050303150040035520466400744001c40502044981600301070908007154800c098030000030b5503440d0032260f0001680d4083c41c00603180c014515080c0d00402c5425041d02200b040031411090502c1030700c00410700d02c03403207a0b612031005000c40b003400090710090b03441c2c14074000c440c000243c01c00440c10000b41c0c40440d0b030300d9001041244074014113440d44540c50070758000001d000748000703604080084100c014004d030000c100c14913085c040140100c0d01030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 319397104 1250 319395854 319395859
    0x131a0409080318010608121b0a020307150c0c060314070e1c03030b090f01150305010803030604020705070f0b0d0e0a0f060209040609060e04030305011d0c070606080d030e010b03010204050f 83
    0x2d0303c03c5402009612502c080d1078030000f154241804260301d030385960800040c404466121201c8031004000104020480306c2c0c0c00340c001c08507035041c821890200541000700c2c2080005080304600850f24411406004281a84001170880740080b034000d0f480c04002c000d030082c0041c02d001c03007015442e52615504203801907410401c00c9a0b40f0310701200a0b00d20039008960001590003400714104200a00b14101e9586403080000c41d0003801003503003070301c0c02486095125041800003c043d41001c0c1c0041600d42e01c40d5080d19800358035014a040c0c0c4901c1a00f0490b420340300443c003104202c450b4860803c644250100a00980d0041e580d030101d420903050008102c1d0350081071080d0f55403541c0d00204041c08107210144500b54446856038807908003150140c0001e8103000c00001c0f281c0c145502c031400d81101e82c12401c107a946182d0b0802d00d5034489841121801e036100c10000780240c05000e880c1c0e09c000309590118018413134659590030343c1d4074015a00e00c6030344108410011551195500000321005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 319398354 1250 319397104 319397131
    0x1e051b040609060f1b2d08160221030301050a0506070809150c0f0c180103020d0b06030304030b0a05070e01110c011b0c03030c0302100612080c0c131a04090803 70
    0x4040341104c0205d1803280b02d100358818076000c041000750300c0101d00c3c0c0140e40b088002621400039905407244007402d14000e42026020408450314901c1502841e80f000d001814550a04040307468031030b40401503c991262940002c0014400c0b880d0a48190001b02011206c4901b4111075450b00811480b0b40c0c044c1c03030f1181c81c5005a800c024002c00003568624401070040d00c2c501d590246405448020500600d8030840080c540b0429103000c6942c428166500601880054803a580d120740c14000050060b03989880306103c0000010010940948581541c20000c80c003410b00403405000800d02d20055414001451a540504140050f0201c1ca12200b40303044220b13001c51403001a42c03030101c1075003c3e00c8244129804000d040c0c01c107203c540d103144607500715070f038103920b0580042c1103680b58000d400c9440e041c0c03041107001c161014050290300b01c00c1402c3c0d82854a161000500080e261581d00540340e4441a01078074032070614110300101c11050b9018886403880d550781070100e01c001045401d08003030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 319399604 1250 319398354 319398377
    0x509150f0f07210b0d050319091a040e07110d030e150c090d23010b09010b030105090c0a031b180b0309060604110d0204030303020910030b030c01050d1e051b04060906 73
    0x12000710417200e042d041001c0c0c03640d81502e11900603010305145100c02c0450f0b00000b001488682c0c07075081b1f0340c0c0448954038040c14039040580361020304001501c590108004099084881101481040000c50450b01c00040c081159082682401084140d540c881182d80c4108051404803404450344c9030001c81308036a0720b00503881e00c0341e4150340c40300190200007030341c05032a00d00c103005502c500201710088580c02e800f41e0782c96101800d00d00c03090160641152140307010405840c0f6040c041e01510026041c00700c1d90460101c0000b251f42c00c81417142001601704900002000082a0f01034054100c0f0310302180f03149011700090740d03180d0002d00102c0c0100e6998403460300703c88a04094640f110b6449138159070311035807070a000300a50005500284180340240207420898001d2146160307a400140150440050743e000554182c1c00102c83c0050b401d407503c1220310309001c810088000380c81160030000c5c0d6810608418108440801d4088221010422091040340d8014000008884d040c0c07520440504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 319400854 1250 319399604 319399609
    0x10c020103050606120a051f030c09022109060f0c07050a02120708070b0705191a0a021e0c0705012d09090204030f050c09190509150f0f07210b 63
    0x10400300e841c151788803010305000704003200e40c01c01c50042a60054001540d040201006850242031100920f044140c2da801c0041290300d80281055495032022109117504a5450042c409800c1740c6071308a41d0841c40801008151103c100c503041000859042d0410789a0390716584d480c08010006403082221101c4803010038010041c40c005085808141c801c0e042c0d03500e030781961035003001004440310701540c2c0320100501007507141c41000079001401c01407003d4080d01c1c034940700000940002400d9400300702518040ca8140c01c0201c03411803000c581d40c1c2e20066460b13500c1c1440344980110b8100164540500c22914030a03807070304a121a441405050040d15100c281c0b164240c1d54012000c42e130000c280003091007410010b403407000c3e00510985642c00019400c10802d6481214540354640e8214811241e0b14280d038000782d40a08402c2c211400d4641608203006281e4040300d00c1034020000c1c00170000201c0d10070001a400888908202c8003180760760148a07401c21181108094403592819070702c074603a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 319402104 1250 319400854 319400857
    0x2010509060f0a111212150f04020a05090103060803040b071b120c03031e0203030c0a0516060e1002040b0d05150904030504260c1903080f1305040902010c020103050606 74
    0x20080008819620504050f000d84412403c1d00076120501412088040466802c01219400e0110342e20050701642c9600c46c2c84040d00d01001c0070741e00a59442c05030700780740e11603200403d07542029455264460740140001416a101038001110641007800304100a104180640d07210540c410075070280da080c8200c00240d000919400403012052150100c81404020080e00065901a540d014207051018819510070008050301d2001640104001154580c00c030f80900458102883c0c107500d4000145418240303164074400030f0703c0b1155146610304002e0020000e8028088421005508052415020344058000c08440b130038140d403a200055a00c00c20030505501e0340000a0102d040c90602c1c0c00e00600702e401a020311140444a112004c002101e44480c08600d442e40fa070081080e0071302401400b8030841324880919000e403410230084005800744000d40840d5994462907906c135001e4100a00c107030112680a54050743c60850f400c40580d9001c2c40c0e40c0a119020f0030b01081c0c903100d000108400303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 319403354 1250 319402104 319402117
    0x90b030c0d0303051e0a0b10020d08070509040e012919050f041103040b090712110d0305040f0b0c0c060313120915030e060606030708070e01090306060b0a021b0d0201050906 76
    0x3401d00603170400101103080e82c0043c81300b00382a10b9041e842110300030300703982d544a0f103510b800120fa205030000d80258070070402020070441c058000b0900a800f074103141e00350b628060300a0303001c0c09920b4003504200540355544550507000c9514901c00e0583c15100c00c044000b034010240200403070071030704203562216000070403681c8803c4d865076905e252900b050455003105851030150b41c001c608001604462448181c08a540c00c22010b502201e03500c42084010801c868044040c000e007400002074401d000940e000050202d040016503c2c14110758090400c1007903840700b4843c0700140140034040354040007500400d5800f48400116a0700340c1380c10340b100c081070740c0660f141e100c0390340c4c80110580c1c4c180c00c500c0c20003102d0021216203403292001c00580c2d010454220b000910418001100307503200b00d840d0303881c10301c0c1810001d03c5c643c1c90740c448000351a00c542040d000500c8c0002d080240c164100001c84400301c5400300c040305003000d0b900240c0070143e066400b03810424085008007041e503404088030328 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 319404604 1250 319403354 319403401
    0x1501090e0106030c060512010509060f06071514011509060f05210a060509090109050a0201051e0f1207030c0e06090604050a080106051509010e01080718060207090b030c0d030305 78
    0x400359175441004001d076000c1070360446554014030000131281848204c01d801384500802c907a03d941c1c000014040c15400a5005072590034031460403002000052298400d91002c0403c0c42c00c00798100b1514284000130303031454a00308071440c18104213503580000c201070091500d2501e03a0351f40400751180d4080d528a030842d0800f10380700c60140400740040c1d51202c401c9500566034030240d583c0f001112401c032003282001818a801401d1200b00540c03281009240c4ca80720081c60140c0c41d002eaa6003030b10190005052008000c00010f80c11601c15001c00700f4583c040c07400e203001e0101c0c410b100c4004001c07000303c01c800c038001c080201c0c12100b11b40c0c8400a481c0a00006001680100d0741c51805a000e800e1501c1460f0003582c0f54450f0b14209081102211500c81c07040e1200180034503c1c50045500ca0401020101004085486000141445280540104210f9008010315804d08000360b044071410782125120380d111944034032568440c00b2542c4050307074050800150a64550b0002c440f0704140c9001c0c50f2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 319405854 1250 319404604 319404623
    0x302070614061509060a0302031e010b0901091e06082a0912060f0103020d11030102070c0303080108070806040b0903190309060510081905011d0a141501090e010603 72
    0x1114040340340300d840c070540303003200c0041d10440b0188051502c0d01c00e40703444c5038002c00c0420503281c60500030b03002581c004134000b108400710140c030810250203441c203030004030302d12000141104482d0f03442407024004e400c9805140e1a5800c1e1681342c0c4508078034620802e011b2242c0d0724002140d00781c12084000c0c04c803010001c00041d00e00c0000f400d103d00e5000c03100da180308a004c00111014402c0009003e03125507d180e2400d2312a900f142c0800070030850301038044130060036411b040c3d20182c800380041e0000c24424480d00794100d086240c00382c804001600015401da200700402c0080e00000183c698119030000051109900e85001071801d606c92009000e1808121140078078886525501c41d41c44540030310340070001621180750924020303803548100043c46d445400a100d881121103840c0301c03264440c00000404142085240c218005a5001c04005800444045062005200f0802580e034034600241c404403508080e41c0b607240f5010701520300c906960300800c3c840d20320258010405160400c8000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 319407104 1250 319405854 319405871
    0x50406180b0a12291806030a0f0c21060b04050603100207020f030f030406020705060304020a031e0b0c1312020a0e040512030414100605130906060b0a0c050d0c050c0f0103020706 78
    0x804d0401110500076004400050941010b5401402e5441c099030000340074011a171255102c190082560784c2d4140e07600c2d20320402c0041c42040e08000e05c00c90151030000d841410543c1e0625104881d800c08126028604080400c0b00c981d50124007079120f059401c6006032a00418000300380f0a10b54045060303050b2040340e410180e0000004040c0003120800d40c201c0b2002911542488a10300040e10020340004490b881480051001d42d401c44020005160f030900b0a00d89854041426000f95262003050f0b2001508090800900300024060309040480c070141c100964041070402440340f1070f025504502c5400306042003000d00811000500659815403203040078240700c1d440441803001c1e0740c02c41c8240121f10004a243e0701601c400c0703e100510340c00010070b005045001a0403d004221500b41d0b4a980100710b18075040003031720307500781c1e01c1c2e44802c80c49c49640382c05403502125541078010f10024982d00d0b40001d80019980c100c1c0d080c00e0754407050740020b000c0117030044c0c081c0e40720041280f41005001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 319408354 1250 319407104 319407161
    0xd06060503160e010f051c0f020a0908011107020f132301050d03021b1306030606080d08010b0a0507140f0a0b0c040308091005040b0307050406180b0a12 67
    0x740d40980c408194946490030900b20070340303071220a4403490b400f2810040c100b0300d04601904c0541501040141d403400703400741a10022080b28012010080c5040c1e0106074104015404401f0002030000c0c50000c010f00c88002032164241d0060000c000d103d81000364203501d490300d48205400b081c6000140c2030084490501d42420b1505082d205002045000300c0001086d19005030411400381e01500a007429030703440410308c01d03d200380489994110352490750600d007207a01032017100000d500030000014503038103110042c0c1c1824003206242c070170002c00703600500c108800c0b28102c41035003146081c2586e4610140c036141c1151442c40f038140c14a406510414521200080b60a8101d40d1066211840641e1a900d204410303020303500001d0311045061200040c6030030050000d58412a00d82400340c1400e99454410801d60b1048691000050f80031a04005071600407801101c06148141c070070a08a0811410582a003d084011400c0210b044420701000d640b43d44014003070b01d000340700c6135503481c0e08010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 319409604 1250 319408354 319408357
    0x16080906072009160818010b030d030212090705011202070204060e0a0902030708030c07030f0510090317060307050906010e01120e1506041a10110d0e030c0a0e1b0d060605 75
    0xaa8014035071000096002c0d041c200071300780900d61645400d0040d86904822204841095040d001c0c20b6685410300707006503070200800100041e29982c003690341c2c803542c4246000c0010242c10f514003580600024040c4c1c0e0781100c0d50354046100340c84016140c4000c0d000080141071264014110b07402c030181030100c2590307030b42c0220691398000c4d403c4640c0c69a40e40041640c1c0d1040503020202e60304507240a1001030070100700301480ca070007103086441e03c01c0c20030960f400710b034095034086010602c502c2402c0d00d91000c19401c0c550040b03084020700700d05854200816100880209601c2c1000038590310394505038020003070040c40e484488410411605400341c00c90380c4030f94440203403e8501c0d6000018034585800d00a90103403441b40b00d07014404482400078011061003040c03400c020305c01000117032515000d08020003a040313407043d80d841150b62030303407000d00d400c0c02d20300d191083c0181c5001c0130600c4200f210411007500000c203608100c4581c06207000782081030054a0702140042d05002e40091026403200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 319410854 1250 319409604 319409663
    0x911090f010807080a1d1c0f09030203060c0a03090606032a12060209010c05010e0127050c13020d02030a020406091d01030b070e091006141608090607 66
    0xa0303228140192510064400320011545034000505420004e5010825034000441298005c408a9024449490040e041010704000d8400065107240700550840d40900100642d10460910007002030035900420703207901c40200241020500040c1490189219a014601d115004030041091075120310b0304848104c2882c140403050319404e1014000565008041c5040b60075003505142248143da60341d2010390000307604039051020f80310700d05000c18170a010b00c082c07491042000085601802e00c10780c0d00e04d016254801002c444801045000a0380000e82d00e809960441c0d020400410040e0000003a100e185248600380780003001748100c40c08150050020303034200c0d442e8000c1803512000702d20410180e0001190842c000b120041021605004425420448500c1c112154803c0080813540203c2c0a40d4000050924600200203560f8048245a406868140d4881c90300300711051018003804d50722005401041c00141e03000d01651008101c1d080b041e44001505c0000c501d910b030101b0680c0198 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 319412104 1250 319410854 319410859
    0x30c0501051f0315021210030203010507030b030307061104080a03030b0f0d031209150504050a1a1302060c07260d030204050105120405070503030f090406050405090312040c091109 79
    0x90104040250401d00310b40c1c0105440d0a0400030341c07654944030002c0c540303050b02c20307103569080005140030340200000c68070130880104103403400c86c551301c18582140c0380100124101807410309040100c2d54040111596030380c01800204140310140c2c2101110304c40d0741d00c49215441021000020540c054001600c4c5010440301c001d610b00300e0109001c540414500300400240c02e800e81e40400c3e01c0641c0c000f07007810303004e03005034801034081c548414102e503002c0d0340641d020f51051a00401700f20241000381e0160301d600c0c085800303a0900105a000c1d842640a00030300c0750300081070008003504200301078170080507688505000300c0da11101450907003024008100641c007514402c0901640240221400c030f440c1a03440c01c1c079160070030f9074810048001030022225405081000180e65a04202802900d11001b20599a4030040c2e400c000c1100c03410340c44140528140800c0000c8648080140c0754008036801c60015140d64514017501c10104c1034010300718442c41e01c0c03401d0034134035014400341020710303001e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 319413354 1250 319412104 319412111
    0x90302060603120307110109020621130b18010906060f03021207031a091603030504230a030201050f0c0604030801060909141902090a0b03040b0708130b1e04030c0501 73
    0x802090548910f21074211000c801d0042011031101c501c5121800590b84450000040d1010103500080b40d0740d00441c0328455881a84000c1a070540c00d04003060f401090704100014200d450342d036420118034008101d4407001302041c00b080c4c03c0200a41003402441d600c24410041c0c1c81d120702c8021707a0001c4500099003d22840c805401403202c0000da01020343e0f802c01c150402181e00400340454a4500030034543c00c2e4011090301003041d40418100f0303c080c0d8070075118203446a041075504003048840c201030040c60710103050304070b0300341e11980c40c0c01d000e5903028646290f4502070302d00c082d0310034840c00000a81501c9400b0401040c10361122156042e00c1c0355a0307d082c441c40d070320311080c4183c03410640700c104040503071b201003006600308088542c0038400142025040c85803072400503c080103e41d21503121011300200b0442040a00c0407003a80c09915400d18404074146405020900114910f0040000c1701e043c0108100041800300c00c4000c8943d0340001c41907203401d203401040b40140c3c0d4002c4519608 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 319414604 1250 319413354 319413361
    0x30222060512061f05090412180e010b03130b070509040b06030103030f0c020a08030d090c0902030403020604060213090501120506010f06020a0b1801110408060705091807030605040f09030206 84
    0x200b003400c402c45444200d00416607034540345282d000c1349403131064041070035128001c002110385494408a2290b405480031141c1014800005000c690300c040c4080d252442c1c507282880a0a0100f075558150b440e20f0007080d0b10f03580c2e81c3c142c10020044580028054550040403c107000f0f0b03024000303103040d10b0b00b42d40c140003030724050047c4074050100380401000b14445000b0110b88900c1500606a40c03400100700d80007403907841c11441d0442c0e00201c0d180c846103858010003424001882402c10040910007001c500e07518041d00c0080d1070351030141004015980004012004c00c4407541500701411000c0001c100b41d582d0748200d10200306407840c04a07028020701e03000060000382c00b211002240c1094014118001c4c2c0e5503141c51200780002c02541c03c140c0f0a0b0b1000c00029070902c41d00c00080c5003180e205960741e003003d00d000d1400700d00400610402c02c0810003111a500c40408012070714220621041c06521075080a0f0090300301d6401960300075140c07003070024520505400a84096009409490482d00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 319415854 1250 319414604 319414609
    0x30705010f060b04140127031109010605161106030106030507110a0201120216140c011806120e0c0910050a06080606070b1308030702060708070e0a0509100302220605 73
    0xb0668070404805603028001040312404202100c015510145050150800383d40320f41d00400c1072010750201c0300f01103c90207000300560603441d040030040868404280390f250181c003d00d01d03c2002d8843c1c401c801032940341810170968020940880c40000d03c0a526507031210001001000103c1d41034002403560466290b80303400110f42c0045107074043e0366006501c0300207086040607511504802d154800c1c1102e20401003144840f214400c150000c000d4003890303000c2c10005050030316914100c08a0060031108100c8190046032040100320b0170f01000c105001e5900d801800d0801000e146a0820070348010800101641c55070340301519022242601040d4846400700c400300402c50b8040e030032200400c40c000c08079114040590344003132b5001c1c0718107801d141555040341030f40059030301c5400359003c041844131054200c0903141d8420769515004041543c1c0b00d00081d480a840d11072240101d105d400410003141c40810607401542c2c026007440700c0742c99010584c1aa04c0a6a48143d09480c9452000318582c0f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 319417104 1250 319415854 319415861
    0x30b220209010f0e0a0605030c09060415030507021501030f230610060518150c0a060207060501050904050d030f02040503070605071e020d060e19080904110301150e06040302040e030705010f 83
    0x10b20702414105c1c0c1107007081c50540b201d40c0040d10450020038144101c1c0c030f0702d6942c00b000348040d104e04403140000c82c0383c0c00d4003e029900b010b400b040554001403041d4450b051011000c5045a40055840d0001419410121404041034400f0042500c000d0b42d002d8004400145a0b130164005600b0004495624039040300c00703000c1d0100340c40260b07000c1c2611070014503111024404d11184000c0591402003014541c1d0702d02070420204459040d0089100410300000d84502c43c0140303410345a41c0d96601d03090751101d03220400000f1040030703d940c46c1d150030314541c210350642d806004050b08640c070701ca4468802401940003082c0440e8000e001d200d80c0d101c01407060003c614100c0d409442d2400c560700d15030b80c0c0c070060424042410568400d200f180c508a03a08200350088041c020040340356a20414400e010540e024003842c003601364000c100402800b03c030350f1141c0601e1000c40c64046841a44c02000880b03610996002940c0031342880c2110891920100081981c0340c801c0000b01300c3c40c1490f00a907400d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 319418354 1250 319417104 319417127
    0x91502070b032d04060b0a050d0204020a112e0b03211e030405060a09051b030106030206030a1407030b130e0102073e060901030b220209010f 62
    0x140c22425007000400e0300d560240da0800d1080340b05212114070000300320b0100303012448211003440f0070001c0c0003c2c8500d0340f02e0413800e6001a54210742003400c000200d441c2d5036036420028082daa00180346010750340311b403c0f40c02107142d9140941d001a40a80e0004036007130306070401c40482c071413039011581c00c3d1643d03880b03625001c10024010300044500d0488101740e00026000f0100f880504000c0c00040d5420354803848031515048072056128181401c106d032400c1001007122026502e13040400000c56000036211003100c94020401d90a8001c00c0080f038054800b079840290000404000c4c4884880e00c5d82000044045058002916665805048054503401c01145402007070f10003080c403420b480e80c2c00c200614081e040000d4a4151907640b4003c1500c101941541a880d407078840035003502e2000010300440246054840104d8800400a00704d03120310010f00d814907548820000060302d0780601150b0704954840b6220300c1165415021001c0d5000b0203902e4005000c900020881c2c82c0244a4100da = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 319419604 1250 319418354 319418357
    0x131401121a06070c1502010510082409070806090606040b010206160c1a0907080d14030a0c11060f0708010614180102010209030f0c03010b0406030b04060f1103040b070915 75
    0xe202800709100640e4016901503d1265106201291400c4034031800c0910300079a900014039442c1054080e50500100c1d08981d0082c0c11400d00116440c2e07100071030300c050640000c580c003800c0c0ca0380c0f40300b00d28001d040d0740040310174003800782089007503417010480d503102e6042a01c081c0030074841325004903210b4074112000032600401080072100c0764407420001e044103126a40c042e041e034130076560078080d04408850038041580560300602032240240401600c0c1d4a47d070420b1180c400380110410014000240a802c050b943c034188015001d2081070407082e40300c0840150f84480c1020b180312162080202c4a00b00404e844000001d40c0394890040c503914641001e00b69800c00e09010300e080300b480703204040c940c1150340031310902249030303414009035001484007030080000903040e00500d0b09442850940d0303880307146032000070000b0400340445190310690044000a0b80c3c9203400b601c0e0020654445500c0080c240071007044200801b11010902844d8031392550440b0b01e0340c4e03d00344143c2418a044040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 319420854 1250 319419604 319419641
    0x10e0f01060309030309141015050604030201260c070b01061403070f030b030304170c0909120f1e4501050d0e0102030f0c09010e0609010513140112 65
    0x70001d0301c41c0d8842c0058601ca0b242c0810114107944480c10407074111080300c030f2280c1003503246000c45111413090740c001c0e541840042901a2a00307001585a000e1448040d0600071514100649001c0f00c0c040c4034a020402c00740000c450404603e0410f15400040701103c0c180d04403c0082030050017055801038240a610b041072441c0e907242011a00c10b5038480540d014161540702031005554240050005008401c40a240006180c61100d207080c103041507140c00792031a0420f000307400740040ac4c070100c841d01c03000701e5607501d6403440000b02c414400c50a00f00e0109204400c25203211039840018489100e05030103060149456044504000740c051141c4481c41580741c80000e1020043c03d51101d1400b03050502600b4020756403030b100151f070303107401c06410346941c0003040240f0440c0005400e60040c1c910505181042c11400c000303415407024081c19032055901080015072a0311880485944501010b02441c0300b5984843c1c1c016200000781c0100d010400040045000e00224890301d03444074203401404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 319422104 1250 319420854 319420859
    0x40b01090915060305061006180302280612050f0f01140a03060e011b020f031c0b030a03080402130b0d08091c050a02011e05180307051017010e0f01 65
    0x4008260102046030382c6140c03200b850070720810500c01d21008602450141c000c516000100c03803000701c0d468001500b0702506500604040c51450001415243d040c0c1b2860007a8010002c41c2515102e500340c408000b44240c40d010414941c0308074521071008500806202e96155001c2404c2068400c1307070600c4402d0440001046604171005902c010080c2c00b901d0245141d4407038a034001510f40c03030009201d83d0313916030391000c0790340c0030450560b510051544003802d0010880780c6d00da0703141e100e003841403003d21010010740204058a0383c06100d07204002800c8074021401840c003c0c0c404c0208880580c4226070811820302c042107207000313200304013800914108080b00550340f0310f00b1039044603681399003103000c0c0c18440030302d401e80015810005000c0c4000301403182981c03000502608810029103040d242d0700c14480c1c2d9040c0c0000c01e0b1564a5003080d0426031010403280400d1a0500c107a104030b0340069a0025680030580001c40801c0f40c4003403503944241680c0f50321382203140107400d840c554030900d41070004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 319423354 1250 319422104 319422119
    0xc010c0f120c110a061a0303040b0a050c010b100201050406050a060b070b2a1207020c0105070605060d0c0f17010903080f07030e0d08070809010c02070b0f0f0301081f05040b01 77
    0x18000d105103410805041c3d44a100c01d0391500c042c0380021a0380d540e46003500001540481c1124200003411001103280030f00b00b0b650111035020b2401c245003401004141549458021b42101c13412000c050300c8820b8042042c0b00003406803800b070714243d0b186840c0a011070801d05d503a025010941e18038100352464400030f030b51011081100107051500c900507044810141d2003d5580790315404080790001a1245117250710050095801303002d050030b5600c111501d4003540d822000359004950803840021b020750b641f4001c6081d130030f001381c00100b58000051002c61281c020102d484d0945503040300004451800040301422038440c1c00000d0041100d020010782c00035041010580c1c0810146404103503c2c1030700340c405162140c5000c105010900110810140c25031005846070b100080390001e0110450203d0b001c1e450709003d01456000d44000140580c010407035000712102034072044506a5a5a034074000151518010321801c1a03030761100c00200030001250003003502864002d031400c2020b0f46054103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 319424460 1106 319423354 319423361
    0xe031911091317040f0e04050309040c0807032007080306130e010c320a020a0506090a0b0106081005130e030a0921031e1b080c010c0f12 60
    0x70000c00b10001404800c886c03c14140c1421500c0b9420820700358850411a04c0e002800d02c100c104140781d00c1140b40c0e20035403e40d9820070030002c0105c1c44d000211170046900200c101d0900a1402064000c0010341d003000c4010140b0184030040904001a1b4480104441d8165519010001503641109034540340359110b0320540310803220411480c14605049044c105400c41c041101a07400b0700070040900c4041d0008211110b03841c005004540e90b08118034225465070040000040e198024440e840c040c46098185000440c10041407001002c035040c0e1980c0c0407a1600d02ca454102c105100030800440c8a80d42c614040e410503040c252a0071103da00d164042000480c41800b007540407030040b00440341c00b000d51000300014042115980b00381c407841814002c00e6000102040101001400c135400081c0003840707847c1d150350382a220605103007240d501054510310005a40030b407650 = true := by decide +kernel

theorem cover : BRFrame.Cov 319244604 319424460 := by
  have h0 := BRFrame.cov_init 319244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 319244604 ≤ n) (h2 : n < 319424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
