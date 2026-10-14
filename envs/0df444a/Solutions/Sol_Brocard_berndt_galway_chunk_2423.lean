-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2423
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:15.386371+00:00
-- url     : https://prove2.me/submissions/bb76370c-ea1c-4db2-924f-d999b941fe4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 435611510 ≤ n < 435791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 435612760 1250 435611510 435611563
    0x11040b0a02030c0607080105030f0303240d0605040f030e06120402090702030408070e04060c0207060e1504051008040210030204081203091c02070609060f020a0204050a0f06030506190b0102 83
    0x2001243d10310f40b03807202100c941d49404080204006020b000707151083c0208402242182c00000a8078011100c0007400350f940d6000110790209090410002600b081440510388007043c0b451040c5403050303004440c3c0c00902d18151900900e1050744a9000380b2442c000e111840c00c101c0c1100c0703c903034066030580d02e0541c542c032450700992940c0201c0d40301c01214400e8040100790b280341400c10700c0c0a240319040500c4140d00c0c17540140c2c2c69010900440d00022040100481540380030040500681034000c01a840c1c680c4445c0818180500d5000d0b0f500410039140c00c1c0400c5090840107000f1310040c500c2c1c11800d041c01e261080d41c5410340c02032000140d10001c40480d084590a1162003142d0410b11081c4200c003c07003c40c0a5115000c5102c0c00c40450445040040d0b95800340004c0002c140c1641c0c0030b02140758440e0300300b0006042c00f0b04820381032a56810a0541300e4a80d12858010350b0213080203188502e0142406085051254142e020030760602e8421001c070b0b60001048011900704802c0d003032024502 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 435614010 1250 435612760 435612763
    0x10507030c0f15090606051e010219020427170a0e01080901020c0118060e0a020a03060207060b03160504060b0f0403140124060f020607020d0e0103110403032111040b0a02 75
    0xc83d010854140340103104810003c895000004540c0103584460b000c0220501d5001c00c014142030345800744c8c2112024030401880b07002c10b070715541c0c40148009000b0450f09d0b500686518801e04604140e8000705080061003182c91250b81c184100e64161403410101c5d60f002041d07000c09807002c80c18403111501207004070300d00790180c982c4554607400070071000c810000002010420503205590042c50300e09040e00c0c0c1c08004c19034903c410340251408000b82d1959840c1c1c1c0c02984228800d07501c03266178600c8614582c2e0306000308441a445807441d500300303501f803004001c203c51541d44400744a0f10308116038000b80d10400c1c00d42d0102c81c0c000003054a0410070815803800348c041e034000e5a485108079036030040c05005940c1860180c1c7d013071303555110844031192400d03641c400e825070b074000159002d200e40b624940c0c13003405d46c882100703410300d4003040d090300c100384900c0300da04503400490106004040d404440c0d038075042e0044040513200c02c00c0c44207000515003802c1520030707402400102540040c080300220300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 435615260 1250 435614010 435614033
    0x51b04020c0102070c180501080d0f0e120606040f0b0f190801020f1e1e0d09020303040b030f07020a08071704050612040c121a040c12081206010507030c0f 68
    0x11900000c0d50707110154174100d00d05829600540e42c4450b5480703080b007210182d034424141624035120052910080218007504c01d42100084a401c200326031220240e075448596000c80000680b40042c42581000b0081000783e80b80415140842c070b151a020340c00ea580e44602c400303040e44058072540c02d0101c100341070b0750041d0700c2da80046000b50300010700d80300700c55100230090842c1101c54040440806125804c170110341b0840b503d80d0540c4000c0c0d007a040c131075401e134402051b800028040004248001c0d6010a00f160003c0d4010040c1440200802c00c4905a2030308035a440350391403000c1d00c0501c2450392044414059040702030400d0f103458140c075401d0151441118041d010007000c10b603c1d206460000022040c04480484420b10320b020002000d010020810813080c0c1d20000408040303e8840850361919001081074628034901c002c0002d20703045541d40c64a240c1c0c00741911a540d02d250700c0d0295410031000e048141008003c2218502181c4d204250f4074482d42e01c5050001c0010150178581c1002c007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 435616510 1250 435615260 435615277
    0xc0f010903173a09080d0b0a0f060c0c06170f07120204030f0c27090203070b070b01060e0901031a18161809051f18030f110703051b0402 60
    0x50040003480380c54205802410802e40850090010f0240e004210780c00d8411048000341980f03000d0188500482c00d03030704001d107103c0c800b91000e002c03070344d031900c54101c000c4c040e600000c0800c80260a2105000301041a20040d007034504024207503030185003020071414001070140403900d8068001c20300c420b21640210700c100400044c25929a0b80360b04140c41844440001107451a15800d07000925582008000c3c0c1c0004e0f20107280c035440c14202032003002a00072000101d030b050059900120725090f540029000c0d89010345032030030541d0305200001e040310079842141881541003800410020b040415003c0e0b199503100b400c2152a01d42d80071400401c09214480d20607805100c6400406407000d00b40317602210038603041806812908000c0300b0858003030b640e0140150300004620510010074951004c042410030341e00181d00101c07000c440d06051042c60b02200041d10003c10003046503800004107800400440150004500d199030f032940d41c4404042001c114404101482216525941528640da = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 435617760 1250 435616510 435616537
    0x30e090c03060d050a05340506030a0c0e0904110a090501140103020c152401050c03070204050912030c041d060d02100207030602040306140c0408030f0d0603050f010e0c0f01090317 79
    0x3040010352182200f40c183c1e840d040c5841018060710401580303041c0d11046038005082e552440c6c031008402e00146c40e20f0392033402030015400b40c4160030349900d844c00b8482c50007100c04404100301c8400b0000e18400991000c440d072307800c1c4401840500c2031030142629919003400c0041c0c0c0c1c0c6200030156400d103045454103580024102c401c03c040d81d4101c106034100141c040c1a01042040800010340c0c1c540a42e0951002581c003c0c0004001030504e41c0c01140c018015404941224680c0460210350780e1088540519051000c2401c220041c003030300080d032146601000150040c0b80840105121621290010344190305c4001c1003000c8034000d1018134065500f1808c15076450781c59080000c094142e21040b0551108144001540c9071202401e0b42c040d581d604003e98030304410030511440540120402c060400d90f01c3c0d02c0003000690130448072901c1d4013043d002198200300362202d0340c10b1117070b494440c034080c621445c5884a1030383d214041005581d0310040684068804000c000098001c4841c40c0710039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 435619010 1250 435617760 435617773
    0x503040f02090f0604050a060303080103230f16060e01080f070e030a080c1b0d0303020901021f0c02070b130b0c1606020a05070803040e0105060307120f0603030e090c03060d050a05 79
    0x10b044188800d0f510440c000e40e0284a82c1c0c80d100d450b201210481c1c400500040c00040c01400014802040740440041c40104c3c0300c1c02c4a6081c1c0346905080500303207031800d103a0201d00060580c0000c4002c0c07030010112030030032030710946608002a2400100903c2d40350000e092400181c07120740502c802c1c010800c005800c40303032001da0303501c0e0800030796120402c1000310b881042c88000c0c988010004d404d0040c0e0024080c229441810b640030740107500002800d506500031300d110002c0d5503480344107146001000350000f260030090090040d04018054104882c0e43c501045807010003504540c8502c112504d00494964501c0103c0010781045801c0080c62074240c0500c40008440f81d00080c11080c15000e4000c3e0344049548a1385260b4900c01c9104d400c1d08005050010020ba1401ca80a9079000c80c06041101da00000c50f0410011110400e02040400c0d65981c0c0a20505900c03660490a080301070310511264213040d641c000302e40c00028500b40c070035441d031200d00b02040400e1040c2d034091940541103442 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 435620260 1250 435619010 435619021
    0x302010507140406050d1b0c1a040809010c0c0b03191d0d0c02040f1103091507020601120302030c0d11190f0204020a050d06061e1806080c071703071107150503040f0209 74
    0x40c01d0104000c1c0d640b048258a507001c030311040b14104ac055a4402e00140c038082c8840c00640e250f6201410035502e090704401c0008880031900002e6105403400d4600c01c16414144680004982807541c02010300c0029486a40094200040c858040309a44c01c0000035002640700240c054034111401500040c100132640e10850000e001860007025458207403054800801466080b0440c203c1e80300c0010b034400c03401042444646032500100350300920650740b401440f03a490710300d000c030104d04a10020b602d141e0011030304042405541a60301001d05c07840e02c1f0380e1054450b40c034404821000a4802c590014003400f0741c0707004a00701c1d540001c0304c200520101d80da0b403601401c20700d040c0c50b50340161103008009032400ea10648603810a20004599002618200101200c0a0700000c2c04651400000c100600225100d60084020b1000d158066030b601d24190f440200122038107001c013400e41e8007461b8144188000304003c42201c0100303140a984959072400c14020300c0b0b80c0100082d40001c021018801c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 435621510 1250 435620260 435620267
    0x1a09010504050a15031203060605310302030a0b0f090a080315030f070b090a060305010e040330090c06092303010204031e06060e0105030c0405060604210302010507140406050d1b 78
    0x10702c19040d1317072000c005462760303090107071014418031040c00020344117900c08401c40a080310942e2241d02e0b9803820b808009450354040b0b4034001c0c8003482a6840c400d2903007041801e80604800a07444100c4001400e81c140d159664202c3c6070102070001e0f84540c841e08803a04041d101040700400406c1c071030007103070481e80d580c403000043c2e903001150287c0148201b181c0400d049010b070080c64125910f8216840352592152411501c1c811700c8030402420000f030039204070410b411407600309800041d603140019400c0c03040c60032454081d05a4008020f104000700c1c1005a1610410b0440044014007600d03910f000c0d2240c00240281320b10b400080080c0f000c01c0c0020f00d160000700c41c4542c0b8500c204001c0054940765076618082e414244200e0b030b8981e02903480071442e03040c15040984c004401405042c10291100350103040d1541c580b0340e0310102099440039800341a4240501c0e50041c00a0504941e22841e608488034035209502450080c00000103400d0000700d62030f030201c000c0001c140320a0003482d80d00d05004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 435622760 1250 435621510 435621533
    0xc0227041e0314030a06030b010b0d05090a0209012108031e0603010b06040b07110a0602031e030403090311030a0605010602010204050a080102031311120706050d1a09010504050a1503 80
    0x944112489000400c4294025518010020b401d074840070840c05007038001c0710466100908403a2980d841e940b0000024081780d01841c0a000d050031469100c0300c0c030390035440c1265030051581c68294404614070000d600e40d18140e50654505c0031301070006c210240d16103992401e01c440014a0340ca0700008211a54000071a10400b40c07001c07803038070304543d00c4201c2014241d402d100d403025400003040108114814000b0b000384056441000c1a10301c0c508040d0000b001d02509500600158000007607411821034200340170b03015403805440741411420b00b910010103814107404024134481c0010305000302075400f048072544065102d00d09005568544034024044d42042c4101c501030035040102003244101030095a20400a40700500c1c040e80b156103a0100021144101d26049041090b0030000f4a2041c40504080c2c0829100c169840c505000c41c0c01c00c58089010340102141000020803407980c1d1400d1086c111103040328081a07070f8850b49203003002481da8010120301e009400000008111291003c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 435624010 1250 435622760 435622763
    0xc051605040b010206071202131701090b010b121b070b0411030c04060b1e0906130509160c02040507020f010c0e27240a031a100602030a0c022704 64
    0x14082c0040c0d890041e81e07070b440151080d40114515441000b208034242d406842000c0d800400410701594440d44580c03a00381f60100300c20709946038985c0070103110070a01000d00400071174560901c0e01d0b51400089852806c0904217030381c00d107107a440454891500100f9908915080801c444e0301e0704092414180c040c03107500034a4064000c0819020f618036161140703204450001150323510781561401c0501034001d02011840f802e1809110006c0d41d600c854014100b1104c20f0407042180324140f50811000040060510400381040d002d00401d15600c2508000195410b550100307090701c8070102681032801c1d1030000d41c0706619107000c020304958809100120b042065401c0100c002c0c65501d032040c01035a5100100c41007400c80c001c03c2c030a00c911a8425406110282c0014808040000064204400d98000d440144011250300d02031101d40c24034581160111141301c0d622807414034080d4903401014500014410301e440c99205540341c400c0c0c94000440d01401d8603408001d9a122400031030000d480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 435625260 1250 435624010 435624019
    0x2d0702010605040b06070b100b0432060a0c03090e161107080d08040302030c030f0315030a11041e020c1e010c0e12011b110d0c020d080a0c051605 64
    0x7000500b41030030701ca006101c000c044c010900e41000d6031034000b41c08030302a00c1803400305030070040001c4038140a40500083c004a14100a03420810f401016035048501ca068800e000a0102c5c402c0c01d40e00c901c215400e120050520801c82195818160b4040b407503a400000181d0300d060800942c8032200e01200840015503c0b4113500c0451011807980d14007160098072000d900045130003c515020307206407070f403007407291045918007000041118195040155414014200801800903070211100c82c44040b039801c1d4001c02e84e202594407803034040000e44120a005035076458802451007083c4070719041041c032480c400c0d542d80700300904080c1e81e1031101c4000f01c002c95040c0082039000a042c0140b1815424554a502702d1028110401c00c50489103d4614aa5036840710880c1380b6010201701d144040340c2d80c0d10340b125040ca10850560608003000042c008004008801c1001651140f0321210440e406c4900c00742ca41c0c0c1c031608161411b07406030502800c00d1280320030182780c180c84440c80d18240c610949 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 435626510 1250 435625260 435625271
    0x606020114010b070f080d180209090307120509030a020a030506062701140a0e150909010c020a080706140a02090f010908030d0c030b1005120903070f08032d070201 72
    0x1104000012001c1c003c5502c0761404102c00000303d03040c0755919004500801c0283c1c90300c44200680c10880301d18240d540400c0000c020000b0641c5007a801c1c6540c01142a0041c1d80f07841c2240e907440c2c11000f08100340300b05110011681d5580343c0c50400c9969031442e405450f404546840741061a07079240e04582007445130308008080d900c4c6a1501001c00e04194403501b582c080d40c0d092160100e0f400c508564100d070452010000000e004002c046054043c1c0311114110a00c14030b1407050000200d4000d0036100d80740e0506a42c1e00d80701c1d90020710380c00800d4220029079180c0c11300303143c6080900b4000c01c0c07001820610030240042244142d009040080c1d0403034000c0000d050711401583c003840c051050403466001444540040e40759500600e400c0c20030746c6000112420cd10303000802038a0b00c06c542c040015400700f40102c3c1c90038850600c9800a850000860401c4940d0395511000441301c03100400102021010401e034118182d03104e0ba031281d01060901211009507160b078910a000c80321900158200b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 435627760 1250 435626510 435626531
    0x50309040c03020f0703230418050604150b0d1d0601150206060d14070e01060302180301091e050c0d030c051b0f0f150c01020c1506010f121e06060201 66
    0x3c2c42103d410a40314000a03082c10100e482c25150036603545d512071880c2e603c5542d589003411846000b4006005070141010300101c4504a03602280c030010718040c010b606e44000d200102042c000c4c0300302110307090401599600000c5210001400c111304104410f80d00721001c240b0403003008200c1c40d050b01c4100b90303104015600d61101700da071054207903500703a040500c00c8602004611060712001c1c81810381022100c1041d941c0c6a03265425609901c41c0000a80c00701e400c1c11590b040e45940000160118000e01141d6040e44413a044d10b9000d2084540810410740340c5000c0000521251309950001010222460083c0c1409040001e400b901103816001d08010260940310300d15540c10000b0001d028820802c401000f44000440d100380386c180d01c0141c02c1110258841004001c01c58144207a00151702c0b103c160141921b413500710075203c8880d801d5042001a01d91f44190b00061546180c50084481c403100c960890050881d040c69003440400d849890300c104010303400c10002c1300c1c04c40c1d000b00401c8904 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 435629010 1250 435627760 435627767
    0x20d020109110d0f0b09010209011206031e030c0506070c0c060f27080105130203060702030403110609010309050f01050412051303020607020f090a060807090209091f080a050309040c 80
    0xd000200803124401107410300e03003001c403841c218903031144c1c9640f002d44405840e405402c99040310700c4d5246a4002a0f40d0720b082d40d0005000c40006100740050200c281150740b8a03940c110220708002560705540741d050b082c14440c0041b603161795000004e03628103091601e4010440840300c4001d4443d619031250008246c0c0c440c03000c40100690703a1307540d07001d290100e07a01d10320150307840b01881540c4031840c100410481e41c01e114843c010400d04e05580d1031a00c0e184141400c05c1c10040c404000d6400601042002c141800030004803d0000c95100e5a1116400c2c0140d00a250346c20001c1c00134881c03c070050400f8681544541c1c05030340285440780d8100360340d070003c807000e03c241c1c8051a800b0b0b008040410050414001403e501c0e031004002c0001558124041542140c1c00c880d000c50301c98403044104510201480750102410303030300c0c40a614001c000c0380800c06110300038000014030b012244501d40300c415110f000e800075003444010358201c1052407c049a80c1c0c1c01c100c0c83c5070722903498030000b070005500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 435630260 1250 435629010 435629021
    0xa03050f0624090a15090506030c15120405071205010509060610300c02030d05070203181c06050c070c0f1212140f03090d2a1106040e07020d0201 64
    0x3100103161621400ba0014040b034618050041e8031400d4640b4105180030324103590303a00c060040808000f61519003d410036181c10588540b41e03024030301e00e100010100f03002108803155151040401c54080d00da500e0600e01c0c1070140d80c00742030300c0d03103540d0600c0c0100039046d00001c2c098001d41c0e0881b41651944420001e0103003106000e003022542c40816404c64026050720212144c2c1d00c054192000c0303455000303003401c1d56000c113000401138000280205c1c042440d0b02c240e581212007803000794141080051110071a00410329101e2040d4a050300281307135007e481800b606610350244090185062007101440140c0101008039000d0307180d90300c0072841e847c4014120044500302c02da00b03025500c40d074540e141e0094007006440108540400d0080d40036a8050050828030254040c0a90300d24020307003000c0c02e041c90b001c030850801c48041100c2200071031600c1c18540b100c05003150071200103280e107802886144070300c0109410241c085400500c4d00792121001d44544943e0702544d03141c8040720800c0303080b1070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 435631510 1250 435630260 435630301
    0x150112032606040c0521010f06030b0a06030209040f240801200903120301080d0908010203100b0c1908090103200409092301050106020d0e0d02060901030b0a03050f06 73
    0xc1d00e180001d061407915420550044405060240c0f0f019080b00c2420301c20b03182c144280e68980c1c0800c00401407080b40c00e42060007082d951a04000820391000001c1c8145114401e078001c050b00030800150035035456000ba02c40d1000c041c010442e842860260800112900740190f00030a054200010456418064200310485000d241801c0030309442d1614101e4008084064045c821030300400094203071030b801140a04054402000f1004800b080148441c038213801c4452240d0062051182c0d48006102e400160703000c0d07004035074461454006d0540317842c4251211440d280c81c42042030f010b0040c035400501c03c400082ea814003032260703252003c050600003800c0ca1290703254100420052411a9841142100e201c1d1007080c120000141403080000000d11422901da550b81c80100102c54041249240d8086c20f404c01c80c034107403804c10000c2c0112100000181c000e0300c7c001011707955684240e0181c08103d1005001400383c0b0344030f05000781c0e20040c69203010b402d4850034010658005020b120b01d1040c0c5c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 435632760 1250 435631510 435631577
    0x909151e08070e15090106050d1503050a0221010c0e1504032001121e0b01020706050d0515060a0207080709051302040902030c0306131119061115011203 67
    0x500d024001400d480000f00340c4c0300b03910102c08442c0c1e620350f1400c0c1d03024000c002c4c071b95400341c580241e0b011000481d07410b110010301e070b00c12070074041001078000300c6c0d80801260100d41c04a80795041c00d000b0150701c002d41c2205151940303020150700c5519048044040c43c190143d840504840c8950413142c0c0c548102c2c00060006c0040c03080b21a02d07507501561035541200103240901d5000101e040724400d60348045403040e5041d03411001806000e04601c42c0c2c503500e8409100900e03030907140440140c818826a41c00c40e10003034aa900049a0100110300f02000700d2001d00419a60300c0c0100d03000351542d4a900408401d03005500303000460820034043c050142503400b880d0074075000c060742004010701e1414412605801499504e41155270140800b0740b2034181d805581e408008a460301020302d01004020a03c1908002101c1c0c82441002c03200d501501d40078200034143c030808021180ca032050b106100c903040490038001162002c0150078504a031882a158025170b000b14424020307042550000d01e2004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 435634010 1250 435632760 435632773
    0x20030306091305010902041415091909170a020a050f06152809050105040b0103021602151b0102090103060503012306010c050105240d170a0909151e08 66
    0x181c00340010b00032020348103000000f0285540d42c08201030300c030441e4040020446100c20040c400c0500900140c40c3e01c0c0442d40020f00f8074103c034800c1c84620401c00030760a90f82d641c00d4041304210300c01c00c8100c480c0c005440455100d400c4003030003d5803409081c42c01ca486010700c40c02009004000103040d400781c1c12814803840c841d101503041c40b0351880d58034200c1d030500c184d1103441c90782c2e030b106c841030280980ba5030078000ca143d42c100400d0100341c2d1100303451141058410014000008001101e003401241d0442c2d81071148030f030b940d25404240c040e90414094006e00000c160309030719015401804941d40a8030140402e0742d0710000c05080b5505107000b07108040601844444800211210a510890504080003041d1040c2c4502d421900100c40840d80d0380042024510020b4070030b00344101080046448410b07401a940c0c074445016204951800d8001020400b41c13486405440c0d100054090340b0b20070825004490080d45440c0302c00e110f88500b200c0364125220b541b030845198407040e41c1010004181 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 435635260 1250 435634010 435634021
    0xf121e0e04020706140a060608130201200c060d02030f100e16021e010204090501091b140906031608010b0a020304060c0501020906120103060b03010911061305030106062003030609 79
    0x2e948036680480d203a0350b40700071010040200c841032500892142000045190411b14042c09000015142a0321150500380080050381d00c06040800f4040b121240360600241030f500a2600c01080d040a40c450f5020450020045150740650301c82e90704920b0f0410603444ad204950b034002c03424002c10002d1140711000510303030402d80c1440c12501c003440c4111119903041480070344030064009803440642e5000201005000701c1c0f80210f501520190704100115070a200e02d090007075140041840510003240e03800c0b44000c0c3c040054600d240400750040f81c0c2ca2038807410303c00c4e1b019444800d074008240c03e1130000c54560200343c16903842107019001076281c142000380036038105801c0c0700202c40b5590204211019621104040c00c05c10210750700941440d411450601c09440d013038816280a42c2c90551985c000c142003110040340c4a0342903c1c100c3c2da814440c10000c144500c5a084990590b00348080003420546c00f038503481da1951800341c00710440c03c1a101e41601c07840280d502c55406114400840d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 435636510 1250 435635260 435635269
    0xc1d07030b0f0609010c02060408010e0c0f0307030f03020c06071a09060702030a0c02150a0e0a090b0307120f12020601080111041a0a0915080105040b121b0604030f121e0e 75
    0xe0401c0c14104844020346c40e90020700c003a4440d4010100a94440c041b0100d140d108000d005410318044a40040f117603031034001310790f884440380310141140c1194204401410b0080c08829024640504400e079541004e08012032004e65150644400c0a0b5401c0000c84210340030071064004c1506078061454403902d01001c4a0031141c281e000d03a405884000742c02d0140d1502c5c00182661590780c0c6602001d4068207081241984641d40048030032414202d8020a5650200d9500199590081c055810200604002ea07941e036003008002d281c8803d0000524150b0307000500c81e4126800e22009210302d9912103d50001401548030301001c0041c1103c1003a066508034010701042c50315807402c25031035a03071403e00003030070100542d1020110760043d005101c241010b000c1e140e0b44076001c0d9200441c500701c280c1c64a90f1441ca07140882d0b48460501c0c00000c0301ea840408a40003160001d0105980e50820300303214000f803408040150104420390042c1454407801500410700340700e217403074078806000ba150601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 435637760 1250 435636510 435636517
    0x150902030613020c0a110303070b040b07120e0105060a14130c110d0c020102070e091c020304051905091302010206040f021f20010e0307020105160c1d07030b0f06 71
    0x2107602c001080d902a9106a4500c05050300b965414002d0460750400d080c0310101c45800c00c000c0740650001c00c1100c0106082c0c0c101c4079003040c4d0081d84040543d4507114203e4040100c050320303003202070420b0258100808150002400391000f12015025603031744007a4511050000001300d80c000032002603030b040c074084541c0305400d010154204454000c0c5144500c80c103010301d40a4950100356818016002d5581c1001840c0150032400100030003420040c10803550751582c0c2005c580252070106400041c248284152402880040c201090b00321201c040d8002c044401c0c015140500d0010300090740010160100300c00403501a0042c01650300e8944940464250304802030f60800d01800c24082c450386083e0301109204070655950011240c45224258540307507008404002da070401c4425203000f60044129800b1540c2400c050fa035421100307104141003400da84000d081e0b09590b503000121044000c3d00c8040080031800e180c003090356030074401d804894081908a8000000300c1074103946050500c000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 435639010 1250 435637760 435637771
    0x105091902090f0901030503030a0e0a0201051605070504020d060e060303070201170c0903031204020301180b070e030a1b0501091703161a1906060201050c161401060603090210020115090203 83
    0x40030502c0c0c840f4404602130300004ea06c100c515034000001c0010040c051722030010300200d22000360103c19059000240640614030310100007d030540348010400c0800c200c3c8000420000d00290740b00c4106200580c001c6c07078a44503041c12403003e40005056450003004540404c5d0b0b05840d403400a07541080804d05004006109603800b0728200102d6036036031381c10405043d510074031200085142c5401d10601d0b003502d0f4620202031503100249194000903140140d9590700c0300d01c62804100c0001100002450141c650202a214a54103a0b6202c080c0d000300311044180c074070a0301e80107845960760410014810a01e0301c5c10405030014420050310a082441c0c0d9070001c4d0141034510090701501445403001d0311709584074144100b5208041b0000355003030141d0401860240003c205030300e015002e1510300e03c920020414540c0e07068007114100020202061001056030000700841605c0e404094001c20310b0003802e034820741018002400c024414000c441901242c0035180140c04d00e060f120401035040a450f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 435640260 1250 435639010 435639019
    0x60403140f0715170f0f060105070b25050a141612031e02070507150c1a0a050f190b0a051302040518090d0c0c030b07080906010509190209 61
    0x6400301c441008101400c040c000e80500304401c007a03003800c0a400c1c410304054030000071050408015040b6445607100d81d0102002100003003558a50740121345600c6070010080c0700c032924209120314000d190f248a088421000eaa0203c0c1e602041002d941c00d015807001345001070503484240c1d00c1c2ca08040d0140540d8900c030000070565107000e9444002c864503420084000998518400041102c03020825013a00050001145000b0303040c1c8038240c4441d07642c003580030240c10301c0002c4907056200340c00e50f0883d15000102c0001141e14041ca80d00002d100340d0300b04000a081c60045500c818414404901902800e10380c0148000c1a071001009044920521644001010030004040d240c424201203403445211005940b43d0801c010882d009812003540e50303032281d0000c20001a02c000103210700c4115841d0a101c101d00d03407185050348060703885400080803c04100300340f003140e5070402400340c010003050066401da0382e240c20602c600440221071091941182807105145048168024401c0140141 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 435641510 1250 435640260 435640273
    0xc03140319170a0209011b1e080301030b09070f050d020d05010c02010b030f0c1c1e0303090201030b010305070203040501180f060905180c04052b1110020a0206040314 73
    0xa2100004414601030081401d0201ca6042c0c004060030080c0d02003008a011428031030310000080c0719a5080c5540b001d03d0313219849142c20720260f03602d0301201200c01c01c25002300385158580444580c1083c03208503600040140810f00c580004a488000d45401c110245d0720145131908004201640c62400c2ea00401040003140114100b03004030307544001c164001058405031031081c546441922038002078550002028080d09544481c500b51b4030a40c1c03103007005c0f250141410300b900b00000c254a880c80c1811581200e0040641540010807024001d0700c00300a103801c1c2d180154180c4038110740800068004001c14130266000c2d07050740e401946000e480c843d501d5198012003220140781d40140d07000c07176030302002008a4a403c0b0309102c1c400742c001c588401c0d2418200112641c6002ea805514800d070000e105291640140b011101141013000d03400910300b90310350401e6001c094290701e000d8083c200032005036242c41d000181130001c944d4040e002506d4035140d901c40b40c815000c407410072640b41c003606 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 435642760 1250 435641510 435641527
    0xc07110a03050d0f0203032514040305010f0e0a2307031704030611040602030301180e060f040618150507090e0106110d03060602030d09050c0a0906050307060305040c031403 76
    0x40e22098041c5115100400a1a08020b805003514066000700004c55008104100684181090608070740700754800c04242041ca849040e210750a0020b0f01d09071014002c54001b040c028150009407440e640d40c282000401801c803c11600c0d031030312400c060300781052510a0b44510000b8800096000720100a4405145c0c80359180100909580d02c5100c805101040500c1885658440d480940d400f070440145400e184c0301000e5201d000510134011600907030a0006c80082803500f00411400890080e9500d40c682042d00b8500d40b61b00381e40aa03059454620b0404185c0d50382003100101d2604584030714255404032000d10054031303004250008011100da0001006ca054450300b0b4081c203003640b55460281c1854120340c0c0340c602d15038401805c00d4100300081048940110444030b5842042101049a81c15810150f16000500d40f803150014410300c80007621a11079440441690b408a007503880196079503804030103542c0306039005884040108801c2000840824854800041401c1982e0070040314 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 435644010 1250 435642760 435642769
    0x306010c11060a0207050f0a08070b030714030903070c06030608210706110c060f010b040302100e130c090803070b010e04050a0204051602011b050f090d05010c03020c120705060c0711 80
    0x200f03091002603030008000340128070700340407411091356003500e108084074503003811295255501e01c5140500304000011801c1584501400c5030070f40071041ca41383c0e49041ca0f541c801e0b5682d20520090f51188088500440c1c56032203806844111940c41000304030102d641068501e0025005000c805c03201c5040005030002480745c0a0010400e43e04990a074a0300100044241452402808400103401100c014801042c03e41c041d0ba00383c0c0e03019181c2c0c0303c4504900745c0a4400071350780c211456008501030107031640442d0540008038001c400340d8850300620358400d10315603607014a00e001444007004c0380052101c1d0081c135503000e901500030421509100007940209d0300702c3e81d09691034801042e58000a00419030240508070070300111030024200c030b440601c0014040d0103211b81044a542001030030303181541c2ca0098200c0c605030044c0007048200e14404d4081d000b035008600f1648580a285405019001080f0a4a041a401001602881d03444448510190784800c50888403004040c2070282c0b02c0d01c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 435645260 1250 435644010 435644017
    0x19150c0c0801090212010203100b07020402090301050c09040e0601120206091302030403080103140d021209012604050f0a170a120207150e0f030d23070302030a1508030306010c1106 79
    0x740e2000061205042e00500c1003e900c41000102c03180c0c01082404080d452151900302225001c40c10251912802d100050180c403c0b003018950560910081c000c2c00c041c0000100104141181c08000601c7c11001c1e842d1500400d204104101134a0b14144015050580c014280705000802d8844424082c0d00c0d003000f01c2c0c000b80c1d0240c3c0000c02803c0140104805104200000c45102d80107001c0041407840086d81e860401c840201400d0000ca0940c030345034004d442960b601b0384517100038401c04141d0f083d4081000022141914a80b0400f0071202c4076500201b808041c603900940031100d0500d03d002d806085501150050301040109048860103074128405040d80714450a00d683c00c1d42c807800c0001e0255100704042d03100a8008041e0002038040c00001c440300001c0b501d40100c0c0460010b03007001a0072026050200c0703904807000800000300c2c0d0550040d407013003240d1380c0c0c10040000708005201001c07002c0d00a24401d6842000410181d60181d0b820f45401d51103000702c3c031b207500c0075000441d1541d007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 435646510 1250 435645260 435645269
    0x1e2103030a0b040c0e060307140d060b0712030c020d211803090501081909020d0209130b07080402012f01180201120b21010b06030103031d19150c0c 65
    0x81e50342c521802035150600419030000a00d00e4a103504c04604800925684000382caa001800300c604c08000128403003209807642007282e010204a259a04c110200d034940c400c01c8115140242200c0100c6054000d06c92000040303160b50040401e01804036050314000b1520840000e00e05504154002e011118021407260940c01c5102244503180c91401900740009500304074188003440341082444c101e02801d0b420180ca01030000300d500c1c0d600d4000705000900725040650000506000c225a001701c0d020f800b514940703d02c0413103255a803586030440f003402003910000e0000e43d02c0d0103c944c81c9445410301d1101c01c00040c3c501c40c1000343c40140300782103851403e11814040c490b00881800d66800008400005220034014840541c0410025030602c401829013030242507800301000c2007603002d41c01000302da80301511555032540c680c02d0240c0070381c2c011640d0703004c4901003001208240c00d0070103c00c000b240c00120700c44070460a10011141c2c98203104600c40810059141141c00f090501d20312030000d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 435647760 1250 435646510 435646531
    0x5030a0309031b050105091302040b0a170c04050f0f030118060516020115060819050a14130201020d2006040b07080c2517070317061e210303 62
    0x1145986004402c020a605104409000d0f0034400c0090307036041000c54155020031245003004405041540f0020300464000e0314207054080b400106050b040f40b4040e4110961a5014405036103000600e0103074421802007070341000c404601041c803820501c5400c0e52000e0028004900450f661151000062100905880c21500c1d132051040580031103941e40c00d4840503200912143d0306d01480442c600200307100e03a1007004000720000302885086074480e10b9402c440c80c400d00c0507051a0b1090b01c040e20103105c0845003103108a01041c06640b500348250042d99040c0c0113803200c405c0c4100196960195540f200c00140c542003061010841d0a01c11584940e2103100110410b060449004000220050030074070741daa01042403040c42c8100425200c0104d121002c40c0501c0f4440e440c20300c90000311408044c07508413002c5080000c01d9000700d940803580340740b0031900b07280f0358681080014079043d088081e07040070340c00741d080780050034085241c40c2c11a0080720900040c485541d01c0300d145510032107507503201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 435649010 1250 435647760 435647777
    0x40207020405190c111207030203040b040303090503010b04021809040309050627010503040206042709030c050c091308070212070303020a0302060603150a0f09060c020c040e0f1203090705030a03 85
    0x1481d106100b02013005140846208401d6104142d94040300c003905402c043d00440c110081500c00c104a50141c4401200b454442d0751382d00d800342c44c0b10040d00a03144a9400c7c03658954150809100340c40d107000a04491086080c188014001f045102030001e9003045040240440c02d9181c00d0024040705404030021841c030780c0002c002c45d00000f1034000380b83c10410100140070150ba1940203540030340303214001d85c0d0403074220249990301c2480c036010b4481e001c0382400c1c160002e054214414900003400356050711200e038415420094084012a03460750b1243c40c40703d10714042500c000152042a1015100c10364404101c641d05d842c0000380e030300490042c0d04c51190082010740c18885650031070070507801002c3d504010304c8400d411110003400e01c4940759507410101c542080c80e41000c00d5081d0008006c2100303c9034010000c1d1140c8120311020700481c249098000b03040c5000500030008041c06011f40580300b60460f00300003030360000c2d01c1c00b01a0310030717050301083c11b59050080b24655440303501d0b42101d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 435650260 1250 435649010 435649051
    0x10e0a0806190b040c051c09050d050c0c03160603020706140c09010f0507030e010813020a0b0a030b0105160f020d0506070f0305060402090109150c08180a0e0903040303030902040207020405 83
    0x1c3d0799072941168040c0b4100f502e900c0c0c02070740213829070704000c00c15262115000802c02c101d0004228840c0c0c081c2091080c0034100c080c154102c4028100c122801059400031040748041c944d40e40180d0390f8480b00101c50040421440d80f0982c05031146d2407150802240d5084900c2c280380b0040c00a82c2d01d40700c07027900040c1c501015a00040c6010f014005803e0103400e104445d18003070007400302d0f29403503410f100d45000060408480c07141e09068055000780402c090f2502c038000d602298011181c03030b03000b20340b0b405581c0c01c0c0b030b41c060700c10343d07843c040b00c44003041c8050030039511084410421380080b60840e2018003007200007481070010620520903591040c2800c0001000281034a501401d80c601031743c030400a00740c0ca030341d00000c1003080e0381e885900603030300d82c40903401210b481e9500389001c0c20905004c82c490f120742c030701000c040180210485550201c640ca407190f101c0210400d440184160380b0400c000c2000070700940014031040d00050005040030010380100d010707601d0803107612038048144002d515 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 435651510 1250 435650260 435650311
    0x70e090147070c0f0819020f010c15050f060d0f1407122a120b06031606020c030f010e100c02100c02010906050a0e070504050411040c08010f060e010905010e0a0806 72
    0x1c01071102d00300034035400e12150b4414030021b00c80e0101074050031807428414016401209a01a40b80d4002c200c2c005003a81d401040000b803e041c0d0b4050805803081d80850028a40f10b08034000712500f04e040403c5070411a42e5007a0340e40240b14141c031060042d0702e800100b04000158003896140640c0380200400c001445941c181c40c20242c0c80e8029108011040c050268141210f084283c0d101040440b0354541c0310000e80380440c05d0300b04040340820a0400300381c00303a021500f981c06170301c290b08075403183c4221b4a0701401e0712105480c200b002e038040b031182c008655003074001c0100001580103031140021406c0c2000240e60560507200c0150b0344030700d180010030280b4440d40742d02600109080010758500860035031280c0151150301d10417900d903400305061102a0820300080040188100410f1b021400302a010207000d1140344d203040f81071440001d00c0c500400700f00007a5a4140c1d034410744241003000540d0110b60100c41d407500020000400301da4a0800c00005000b05821141207100104026684 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 435652760 1250 435651510 435651539
    0x4060608060c040506070606030b01181d1c1701090c08070c1707020a15170c0405030c011115010b0315180105091e070e090147070c 58
    0x50595001e1010001900800300941d000d03500700f1a82c00b6940c034007d041500c0904030075000a080b030b00040c80002014000c9000440103460160400d005200e02c4c03640146180301000e060201c260440e041000d41003200d02000810b003189030a014a1806402042d139405070002d81100340343d195100d07450051250008500b95001e10249802d5241c183d850b5100c0540d0750808024048914000c1000740031540c0d4100828094216205010f243e200c2990006020b031961419039078a8001c801d01042e06080100116410750380050000c004603a118001107500440341d961103c44d07070052a5621035644128a1154020080941340d40c0d04d0b1700b400a2034010a440d060341c114820396084080c0180e107410680d8450441c2d42c100c03801055a03484d000c1c117015801e000c410504920000354204401c03960408140c040c95001540c4503140b5a07240c101c124079405c00c0d421410300052001082400e9071404075082d82158043c49086411922009814034294000d0001250141002c0d08144039020703800b0142c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 435654010 1250 435652760 435652769
    0x60601092430050708060d0803040f1502070c18060608012607030506041a0601020a02090a062102091510050a0212040603140702070513052706040606 66
    0x169801120042245030390140031040d031405101c00e074400d203280341d01c102580036090211880b803600c2410240080d00000d00741180c0c1100072944520204d0181d08101d40c0140b282903009414a180d600c035622402e910402c8034038101c80c118403420900a0b100000c3c0040d000d490301c540050340442d820085440c0031410380822103901c15150040821200394050b002c0741c1160408902803c111020a001078005071803011001392034400c1100010400c800090381c544124000c420444081e002c00e0f120100d004070503200540141c1c00388003000054070741401d00a81200c030100c0c0c00203419aa6505901d81d030310031640168040b40406401c030082d0700f44444c0d810352001751410800e64006050300010703104270b035055000f0100040882e64200c83d0303008002c2d40702e8070008024820780781c96507130300002c010f019070348011840c2800e500c02141c1c1032400080d4110681ea402004201075000c070001c0070b001031800030a02d100100c406c07600c8503901c1c81511207139090007401c28080c0c41d0928050400341300741c81b004d601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 435655260 1250 435654010 435654029
    0x604050f1905060d060c081501090303052203020a06020a05100902030a14100204141c0b01180207060f02030405191e030302090406270908041502030c010c0206060109 73
    0x40144100d074480184500848021000540d038407000040b807407000c1260340060001c0d107440c03043c10490390000a15840740c8a40702084681c0c00306130f001141c070700303985120050110f401400250220345100c0c02d000003407146d4541c0d00b01e030340e0356a030002542c4401c0c641c00700c00983c01044000742880414401580d52243c540803d00c0143e5041e8040b07556610103800180c2005842e401d1072110102c00d000c49800c01e1a0000150344a5403501e40c901c090556001d00d0358450805440300c200500b11203000d400c0c104c0d0708070340d02584503842d04407a0507141400e1080c115a003a07007080100c00051452054040400f10030200580700d10f00b901e000351602d41c036080d017000103c01045812000038000707040c440005c2004084203801422610f015400381c000c0c0074243e5031241c28050049038013006052000c001c5071800100701016000c03103020504a4401807005000094100302c240f100300c007a044040e86440716481100c0ca0042241d080c14211614004050300507041142444929a445003449020301510792 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 435656510 1250 435655260 435655291
    0x8100b0c0c0111150405010506091e010b03060406081603030306290706020903060403020f10110304060b0a1211040c0807020c01030504021c0b040507080d20030f0c06060405 76
    0xa1100e503407529180c0901d8108001c2c0c400d640000c420500070083c0c1940308008040050a140c075115001e800300322001d0b806600444005152001004c405500072106005181001d034200308407a20143c0c0000c00d2142c1058580900207915401000114902403031800152240b80c10362030001c051f10f440d5402200d0101d0321100740d4424042e6585214a154140d40c83d590341c440b02840d00078040c8c0101c2c015190316000340c0040006141d00400c04103055101a0150f642c1650034100d50f8085800d502c1003014a1a01400050000707010741c0c3c8221f42040004001c550000d40e68108aa030500281208550440911f11010900d081500079219800541c0c1401c44240c80c000c030000703684805e00142c0904240c2c03070301e000c00d081d915218012407113a101d00300d80d1400c8100c2410f103a41d4080c41070320129824896800001244403021601a204d01101d54841040045550101140b60a20070b2001442d000400004410f400d4000040181c2000320000d4601403074100100000c41d03a008201ca00c0c0c060104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 435657760 1250 435656510 435656527
    0x806090615090d1b06090e0a02070c03020d060b0315010617090a050601081b010f0c0204090f080c03130e06060f030405151503060f06061c0f020d06170a080a0e0102010902040c08100b 80
    0x200d180e5540f05c1070300023006841b200300d030400f940070180c0ca82c40690011212104c040a000f0300d50011034040c20190110740048205002840750745100744510000a5443e10340000a80c400307a94054000007000c084606110340c80d100c180c01c00f2000e900c4204181d000e0106061400744039400a03003180700900b801442d000c003641000e4040008420028400c9a49900000030855440c42c131400480c0c00c80716180d00e502c0d80c00856590780c3c0c002510b1a40711030403d2000640c5c8198480068450000a85054108800c40c2c120290310780026008449502900c090100d01e045021100d0380700c0c01c1c90400c12030b20848042c007414200308014240402c0907110724108055130b221442100c00e11800e880c03140f480c40e0345c0048094010030003561401d0f580307400000e0707100704105260402c1c0199901c16148581100042490036980d04079440001e2600c43c05201d400089170041c02440d012060600000c43c104d61786600203001c450b0502036490104074407005000b400307040d0082e07002c00b0300700700251a8501501c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 435659010 1250 435657760 435657779
    0x115091b261e0a0209041118060702241b060708070e3d0203160303150506030f01080d05040302180903130806070f0806090615090d1b0609 61
    0x45900e2030034091860042007080d0310140035420711515000b550000390400322a0b600295000b0180301d0302c110304141080001c0e00380c0c1d0048505a814041340d13603169a20703078000c1c0140b9402044080e071b8001d201064030010b41e0400d4000040070100d404c560f640d0f075006c01c018404032a5074a40d2031240c0364031102c1008165500801c4c07603500148142841c0d02d082c0b00d52000502d001c4500005e003258900400c0c24210610700702d0403500c2400010b41c00c1015060b200f0b11003241d40740141d000b96440341c03000500307000200380207500c10095031420300440200980c031080844e07425801500c0c2c96480254181c0104003c100501c456005600d062a00300d245c50720b141c0004240d44002c80e030882c0301c1039001000c1080c070301d020000c035680c2044c00074492680d03941d9180d20b41e454200c2103a000003c60303880260070a64500c2000c0381440351100420a60840c3c8070039041c070400c003c3c88401c4100409007080451250f949002500c4a003038840d241c0003c09151986000610354510b074401d10511100d80802d0284814 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 435660260 1250 435659010 435659057
    0x10f0c0f020f19240e0604090509030d022703070b0403082d04090501090203060a12030c081303060e0307020312130b0a030c0e0904020f0609030115091b 67
    0x80441da65840191040001210922a082a066035100d01e982c0000e81c00034000c2682440c001345081072581c800001019a01300c800032a0403030307003c80c01300003e00c80c49429500c0030783c02400700811a428880d80503a658101c1e4031220700341080090710301c140b0010394141134440707548810036000390049a10b46001e00340a80120f0000810b16540800e14104250050300d51714010304140c28250420020031041140d50b40c814081c0f505190b05260010955400314021280100000703400c8542d101c2c5002d44c9045040380d40c0408404015402100d00041001800541a80450310181c42030303261071807a01d04111f81281210500396002403140001680c1d0203c0e405c0d01c00b2808000c120313504c0c0000c0312601c5039424240c00c00b95031558041a214841ca505500400034200292500c0c22407403003200c10002a200300700d6000354845105c940c1800c40d410000003803e403100001d4008503240c46201000b070141c50454020b50b419503583c00d81c40c804040500002c6090444030704040c1150401031846115816 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 435661510 1250 435660260 435660263
    0x2409130f11250c120f120e130b030c0411072a060e06030c09122d0604050a1209120b0610050c0c010f0c02030604031706040204050f04110906040e06010f0c0f 69
    0x6003024131030814420740c0e840c0a081c990380010403000b4400e05210142c18940713440c100a00800440640240d074109034450f00042c418010b009203012032880c020800641202100101801c1c82442070500290a54800340b03d0b603500b090086a10903210307030550701e4040c400d41c0300000b00101d09030748030b83c103448084c100c0340c0001c00b15410941c1da078050300100f12401110340a00300240f180d019403525800200038040240c1d5024500b440544242403400c6940d5502a02c2c00f422a4200c8806240092000d40340d0f402e9420b420304003076029650720030305626498032215099030700e1211031080112510701055000805074a504089043c508115100c0303588001114a00b8140b103401601311210074002d4411140b256802401c940103494142340042c5510701c2c0c03540161142c3c0041c0c010414a00d482d000f0340d020381e000035042d0805103c071102000050a00c401058180c0b000400030b5254507184d8100901c05040c1070110483c2d02d08080c1c000401003041d500700c51b81000320300c00052001449903120004101d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 435662760 1250 435661510 435661529
    0x40b0406060914150406020d0e09090c10120213053f0a02040e03070201020105012403110903070305030712050304080f07230c2409130f11250c 63
    0x20312150b40440c640c030411100c4d4103400c82020a002501603400a1440e07001070a6940d07825404841c0b2043c400904016268250641c0082c0341010282c00c203440c81c0c0702d03404030520b0074075041070308820400100da100090581e10000d4801c400c0c0424140700720240c4426400c00a4001000142c4140071100a5821a2000001094068003440040c20400c0d20203a0390020b008000020002f00c185940c0d9000060490155003030500002c1d8410100c00700d40c0d0f000c000c0b1007040c6051203100318110300400903102c1440702c48105000c4502a0380f4100890b00103103100b0001103586000a08041c034000c00d4a40605040110800400c000503400740140c07040c41c24042d1540e0340f24000b91402401695002009202e90405000c0300c0040a400082c044000c1c08291340d180c408411864048200d010000300194201e103041009990f02d0504030104400030102100014002e101088400f0a650400d10302c2000c440c400f00b0040c40c096440d10001042c80a105032400c0215025910300030703100c40c14441d10181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 435664010 1250 435662760 435662789
    0x5040615021e0d1d0604140f010f0e060901020109080a020106180216110105070f0c06090806061e01090f0b130b1309020f2b0c0206070912171602040b04060609 70
    0x2038181002c0c6181051008040980301c1d40c0321081903007183c20011f0264820310840c03019001030350242400519044199445e9012519404180038440e40038125060442d980c0700080d80c04180804050100400302d0707800416a80d207000381d2105040c1d180c21440c0c200605c1000b40240000800f51007500c060b0788641901817500241c00140c81c1c03409203800241009040c10ba941041000b200090030aa03011912044485502d0300441030350307258112000303900002c8441651aa049a040347c0c4602030505140c05085d081d1a0030615031704403020762241e940da4001090820040900380c1411000d050240d240c135013030600e00d0480410145c81c42c030541035101e5001480410080700e21044404014903589a8603038104031400c69003440528007074240c036452402611091480c03003c164680180559503451b0140d508000c12460150410001141d100b110045080a4010240013070001e0400b150000c7c0c42c505000d0051002b505c89206116101e5403a007101406610b40041c601c0045d100d04c6800c1c07809 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 435665260 1250 435664010 435664037
    0xa06060b070c0614040501082832060409050c1809010c0804080307030b01030219021f0504080315040b1c02030f0d120216051f0b04150e1005040615021e0d 68
    0x9a1082e141d18004681d10491840040e031270140c20004011400d0300043d03101041090111072a074804250090702e01c0e0158001c00c00b1480c0c10307000342201c0360040064564150824001440a0030200c00e0340201a0001c0304101d00d25000784200800d00b6642e040600481c82c042e56240c0151200520440c10705946910b500340c01d134420350503203107000c1d810a19806c0d84040658041d42d20b80b0400116960a04040d811118a0401e0b020385405643d02050280c10b40e103d1051143e12007070060385080e006940c039038036130905a840c5515240520307044659180d43c078403207005141c1000014902e2200640c001c16124080f1036100b0b0f480280450710440050303e5a034a540e08001006050501034424801d00c000c441d0040e00c1c1d914000130141030501e082100c956079406000030b50300318210300407005060500c10480d062010b07030040c0d405000a52a507080a44030360004040f1034a9401c40302c2c0c0903d900302d2083e00b6540410020240301c081090348241d124052400568503584000701d1000c00031459950344 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 435666510 1250 435665260 435665281
    0x8160e0907031505061b100204080c010507050c090a020304060b010c0302060105010e01020c090f100f120206090d051005070e0402130b071a090a1101030902210a06060b070c061404050108 82
    0x24044c1000800c00e51342c6000f50321b80d40b4404d0540c528190000d000e80a0001ca800815108640854110780050000c2c986840d0045d40c658101c04019074290090401807000d5036241f2940da4411800440c0040c0c907801c09040031400c0f02c901c034460380c0c140015401c0d0b15000ca84c001449604464091070184001b6a404c0e00407810045c11640b1960000d07941000d1000c0309004800c0c0602c42c22962902460751a9910090b801007106442103a0641700c200c0005400f6082000c005c1a5000b40a041194012036507503540b4685103d64090010f0103a1b05c60900494680c007403661060040b0450b03041d800c1040000e02c511182c0c029106990a40b0390004001c01000030011180c040a150b0007200020b61419905d1142c5800304441c044031511070f10355420f14558005e214582e0f8a60300540342d10700d10b900740001c901d12415008d01100c0305120300b03500c070760005c2c0d40c0d40503c07006030055a0515846140d18039000c0341d400b1884d0811002d004001510780121201c48094070212034007440c200b074440d00c4864548 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 435667760 1250 435666510 435666551
    0x2904050a0b0d0818090c0a05030a320109020c030904090f02131b030608061501020c1009030b0618040305030606040f03032303090a0807050c0a030308160e090703 71
    0x1e41c02c05420400300060140c1880500004070320742084004601d214420080360403070460301d18804000c20b110f12418548100051039000b41990000602008508613620f004850540c6441512545003500904c090801c003001d80104a280002c1d410b001e40d6299141d222302920207214040d5035100303034500600070003014030441182c0281803440c0384c10194031401c0c0507080f10422501c0d0020701c1c0d000b05100c07910a1041078200ca0761500a42081d032200d01c04a2404011a229581180724086a031807076540d0b2202c01d04114101910784600091a51a002c00c05047c010f000e0b612800e01042c0c00081c10703d007100e00f0350b4456454030b07000783c0c1c956400780090043d0081340c00000031000003070404820545c0042803c0018407421034070003044003e40195420074842160004450781245104100041e00c3d4006010ba4910503025290800fa80d0000310341c2b1498942d005070300151860003070040d1001d07044035907415030703c5034039100a2aa10582c0422038580c4090680402c1680d108004000311030020a00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 435669010 1250 435667760 435667781
    0x12040c0b040b03101a09040e1c051201120302070303080709030f0803061c03140c0f010e0601051302070503030408220303120c0e13110d06030606092904050a 69
    0x2032600c40d40c80719601e0400350021500c942d0301021500010a08542000e0900b0f00c06a0400c40c0b285041e0340d00081c4000380125440004c1103104003082c0030104034600000c95180801c0d540c0303aa4076012615501205104103920207610862401032002c0488d501044500542ea014200031400c2e0300c6110040f900486d02c2c1e40b01030040070607481c40000f080746980046004080c200c4090358110414082c2e00c5c0c680c80c1d0644000d0200d003119011803280380b141d50140900c84190000e54046100c907101281c25030714039000e00680d40c0c1101005101e145000c0c03c21801c02800f40d081103040105654540d6580d1001520143c0500d40214031250725030340030250b40c8491340b00001542041c40d52072801629000d60104100c901c07a0501c0026140c2c184035000800001000070203480c51100c403e00c0302001460900000000c4010030443c0e01d06058690151074003c43c4a101c0000304107140c1005181100c0c1c084a1011422410407030300c441340e102c1ca00388450150380c200ca00041d00d48a10902c0401002d10000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 435670260 1250 435669010 435669029
    0xe09030c0a060f060b091f020307060614010207080307030f051803030703080106091d130501020c0d090f14010e040c210906050108010207030206040b1e01270605030312040c 76
    0x540307000c000c09504100703129880030409009250b101d0030240b245000b40030009802103241d26209141c1c2e201d1024001055801e801581d2030948940c031000c06445041c3c101340944400380131980c0555a0401c400c10007480c20700c000e981003040d555001859055209030600400c81301003241071200d0540c40401c1001000101203039a141d070903140250050b0001d108850104a1103c1e0024918a04040b8002c44002d07801d6450029500e6144202e40e0071019502950309642c00e1120b2490385808003c01d010518140e100d20301c1c007518141081c032110215030441c424040a900a0307010590b0840511a0b200304201e4000c500c910a2440480c0d12050410480328440c42e645142200c0188a03404003103660300554040c00241c0e00d4452841c00c0c2d100301e0000500603406800001d01041d00c030032105400c402d900d4513079031103070b03100300d034001058002a0481500c505110800c40030a200050000d5404904180103010452070080084d460f070140700025400c54540500007810007000111810103440c200c80c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 435671510 1250 435670260 435670273
    0x11060d0203070f021e190837030b1509120313180b1c11090106050d0f1407030c030209100e011b150f02161416050a0e09030c 55
    0xb20b0003006218100c0201015000310100580c0980c0039080c1074105400e5040180760305000340c2c85248000c60351040c152080201400445100007524a411000c54540500d02d10302e04000c554038a042c411404040702810300d81850008076440700200d8441c4d200b68454516110010800803600860072100039002e14000003e42001040084282c58290b940f4000400905000840b5480c00c448808500d1940f00c0b01507100e09032a006d0107003451030030a2140000e031100c0e038101c44c080f0389028000e803c9540407420110380403507122800d1255a98000d9109020b00c450443c0f4044452500000f80060701059102d4141860b0240690102c40540e000604180d90603820640011310340000d060391240010120b0440100d554280784010355800d400000c023175204244521400010b050700b207604a08680c092014070103161020305105802030080e00e41e21102001285181e00b0219186006201c68844030320078031254840031f4a02080e545481034180d060703150760041c6032942c01100444403080c8901c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 435672760 1250 435671510 435671521
    0xc040e0a0b07031a031513021302030a0209090619031202030421020102160806070f1413030c0b0418090501060305030a030608010c0503071704030e040f0506090a05070c11060d0203 79
    0x584c0009401c4610b0f140000c0440a0001055103446a501c1001032540541d1b0118100d22111494000d0740c1c1d1004100d2490240a201c200c0c0580c0c00489100c0030345c56003c0340d803408070304210288a501c44c5046441d0202d003814010000c0384e100792800b019000400046d941c4907424000c104544c080e00705031880317040100c00b01c5808400e41c68081340880c011300402140e0382415140c80504804d85480e40c0151405590b01002181c038098520312140800114090244151242c0d000406010601c1030829400e40d08500b40700c105040c8a40c00f0a0f29180c0402c4100552000c2800c4060502000b04c00420010107a05009014140c160800782c03542c000000c4680314140c141d0b01070b03011109007000038007d2019850040c0d07180c1c00304030350385004562100c01c401c80d02007207584800e9200741300741403003070002c0e40580c00705085984800d10150b031903680c1e8052051514081b8011a4400005c0700107000c14680541d00a0030341001c2000103001d09100442c1072441c0c0d0320788054407a0244903901c219100d1826 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 435674010 1250 435672760 435672767
    0x4090803070f120905010e0d180b03040804170c01090b030c0f0304050c0a17060702010b060703030f1b0207091404030c0210020102090306150f240f040b210709080c040e0a0b07 77
    0x103c94100d0307c14401e183d0a0051035004143c0b082501c0c448607104168686051098940350340f000b081290745290400001c54907804d0001d03071400368100800140020407000d400500128100d40000c90617550600811042c5c04940b421108150002811240c403a295464424035140203105a142e010300c0880021940c03450001c00f00d442c01803400200c2c0c104d5226800164200c9088201803608680c0821a217004a4005e0308400d41100d039503100010101d140c8000c650300c3c1c0328440c21075001038110401c100851a518000c5040402c210503030564241007e94010f82480c400c06002409100089180d203c268002c1d070596400b00d0f4083c0c03d4611900d040303d0004e058446844000348540001681d148030750a00314800c5c1010024150310401c082c030310840c4034140c4d0b0043c1e4610541550104408240034100c1006446410420956455800860003110b050000d00406900410107d424200300c0154009000078080c42c058a00207021164142c402e41031034120040a04443c42140500080310350 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 435675260 1250 435674010 435674021
    0x19080316030b03010c0f09270c181403150907170a0807030857070f0c05010c050309130204052107090b03030909150d08040501080604090803070f12090501 68
    0x1c030355480e001c0023600c403070009814000d181581c489624452000045100b032540c003540c2d1602c01400d010409500120601944c6030058105407410360303034211100c58a0070104024242c82d4405200b060306480d25800e0155120048d11501800e604140030030010002c0510801440d580c101507000e564404034100540984410b9403d070014140c0c800c0007001d1a140312080c0355002402c80c00342d03400c072514103041207840c4401228502d104041034450000e0011308070020449217100d0a00f0f02031000d03d5041c00c6400c010154025414868007000d001d00042000c82281c0d0041c1044a0031810b00352200303010802401150080c9400504428041c04040003d0740f0410548040b2411500c034507855441d804140c920450541e60540e0050020148130310300000b40c664400c0715410000c034100000c0700004d14076640e4000c1079130310100028080c451941c0c000c87c4a580044c0c1034405002c012180d0f03941400900c00186840100300008140fa4040f81c841c50040c0d2109010702414000300480341885402004d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 435676510 1250 435675260 435675287
    0x402010c1e11060414010e1201290d0302100e10050915070207060c0803061530010b0304140a05010c030209180f07051e1305010219080316030b03010c 66
    0x290204000009240c000c2c100c1e81690366031540c401c4020308050054541010447c281680000c0503a00d1400750503007441350003410b00301c904505290480d205007907500b1014184900f409600114102008203070000745406404414800000d15808900d60041c14010200109500181440103114030980b00003050445030340071101c003e5682d229054203a03134580c418440c3d030020800310b0fa03000d80070401000c0034590040001d480400580340010310308402d68032070003000710034016040f040c4408042c160801042c500d90304420751400d5041c480c401c040350000800040160000603240e02040130306020502c42c859000000303111484c580600600030350814003d06000d0748000301400c411660b50030020707000300d800c0707541800c540c1c0395100100d1703560f40858200000709690100301002c0b260410300400712603d0031b15448042c24100f0000a05001d1400342e0b039036030781402d451404003103468101145d8000403040c540c4000604000d07015005842c015030305d00d9055203052100310100c0e820224100112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 435677760 1250 435676510 435676523
    0x4051005010f1809180506180709230403020a05060a0f0b011b020409081c020403060e0a02030c01030c090801152606150609060307020a05010f1406090402010c1e 71
    0x181480c4080340c5501d5000403000d0100c0f4011010030110010b94804e039660300c001c8480060321211502ca841ca08501030b00c01e03090220080020304660741091043c0d4000d0070b840d2501340074408210007540a01c0c1109440243c0056114021804040c000c2241b0310440354010140d07140c0d03241c848280c100600542e18070030380c5242040f210b40610741c4203c120711011070303c1c5484000900802c2d02408020161843c003152a0071040003050500380e4941c1e40d11035030110092016984c0e5086142400565a64180c0700d003240d4000440a00144d402044080d880b0740c0c2031074005805110044125200000c651200d0308552030203002c24100d02200031820203455804000c0b10107070f0a200328800f401e40110f0481115500450045000720f0340071020300c00da10710000d180c28140200d00c0b002442320f0f0320070780d50032000d41d100c4200841000002c4c0220202801e41400410013028109681c2e0004040208007030f10900840c40040c045a00480b02c10843d03680000904a8a141480f04107100c54015041685c1e00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 435679010 1250 435677760 435677777
    0x12080708092103040c0b03040501020a03061a0d091104020c030309070803070b0c16022e1b020105030606070501061d0901020a1215031e0308060f06040302010f020c0405100501 77
    0x207002900c441503112804481110b000340c02001e1030580c0014004841c181c040245c002001c443e07404c0030314050b40c0200300045e0741c0c445848001e41191200d504c50006400301d000404c084240c580c05607030045582841c0824072095505c2e111a109062200c11507200f440481c5004040b4000000b451040010100300d4041c00c0d1180c7c00e042d40ca001d00307203000b080c0a00d142c001440580b81c01c0080c0c034102c3d854005030f001607d003aa000922144c0428200740f100b90880407052a0006490103807069107225051841c61001d0701c80c008200c0b030000240283c103103d00080814610f445520444403d19000070082200584910b40b41030340040c4c03c800d491802c800f45001c101d03484810302c00c03120100503588990424603092000e00700a001c00350b440ea1a09106401d000001c24080208004054602e003001d0a8038650392801403d0300314042c000c00c0c00341c0760030070809050b5210003040b1000c2d42c1d02400c144a2203220130204901c0c1118050b040d90f0494208810b03c04605601600e61068801c02d8075142d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 435680260 1250 435679010 435679021
    0x203071d0301091e0f0c0315200a0e060913020301051e0307090513060903030618180b0c0c15040201121505090603072d0b04080a0201050d02040312080708 68
    0x80e40c905400190410080c032140040e18481340030784520340e91041c0e5000d07668042d10b880d600b466500b254015100c0400345d12141e00107407002c0c8180e12036007080300382280159091000c55881c60003401000010b12072401915215980d44100790740412000401d11400b0344158a0144040e400c203118044c000c40c146041400107440c9480c2550343c458020700104000c0303103000388007000351031f014000c2d849210300142d89002040041c000c42c5c4130b2600a84000c194540b0b0100d01c0700504035581800c1c0f040d6031600c01402040310100445214040c1c01690910b00c0e511049001005407003440c440002d20f00c01c10301d0000f14041e0170f4003214400c0707000341c0b0340e0b0b5442914814681c013550700c1d40700c1c2d0b8007030501181000d010f00d1a1504501e03030481300103422601296242c030407507034904054a0446601080016800c003070445414888000b408403501011308140c90b0595250307481d00c044400034148030000c94480004040c80e1706843c0210381080e5150300c140e08075000a40603c0c0169030403000520b61074005079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 435681510 1250 435680260 435680263
    0x61e030c12090d0e0d02060f120610050c0730050d02010c050c0604120e0303040e01030506070f170c070b0c0325090302090613050903120f19020d0f0203071d03 70
    0x58030f43d205869001c03864007007008120016050f41d4003203900c00310500c440e10059644d200580359815070844510b61600740041000069514418030b941000710030012003681c1035020560307100301c0d01455144000004000d030340030174407410107410501c040c0c58a0901424410001490a4004900d0f0000c2040d92541c403070454803449002c45546007603002e4008500054006c1002d028000c001e843c000341c41114440000e030459200780e010f04034000b0f4520040c020301500f0f001207174100c0ca8078149106144086200904061600284070300c500300d080c0f00088600109034101c1f050301d0b41c0b01e0030000c1c66140c41540c11016810560b561218400c44501e080201003144074107140c03d200c25101e1000f0f8501e1642007004080c130044c031054020403103078100b0b09114424041e03540600b50b80c1c0091500ea0f9851600341e9000f410040c607041101943c2000e005690008410070003446610107005a0f50780c0e1552101c4000d40015407081c030f40c5900c0041006482540300350130130004012004c0c2c1e0080340304401d0815 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 435682760 1250 435681510 435681523
    0x1603060b0d030e0d1104021306030f020901020705101404240c0c0504020d02040e0906160504030b070804230609100204031505060a030804030809011707090302061e030c1209 76
    0x3000310b10f050300c140010f403404d01100c2504a1103405ca0401002c0c40401140698022070b0811240402015041c4041b58260013462024170350518210f092145030f8000030740d144464400e40b80184d000210890f00d02d4410201882902c6002082586c1e9594a4041101080200c03220400307045182e04503030005032242c50165a600d401065105866061100308002503000c00c118101c902c3d4208000a01c40c0300d251542c62048100d8005400070745001d1381303103c1060454074410820003404000910004048400c003981000d2140b41401e640d6403149060b441c41c004090301200105040d0404007140744000825a100c2c101e05415078044001d0000304e101a80520b00004180c5c0c610300b100340781c046441d40d01c05603002d1401001410303526a84c0c0c81e81c001a41c0309800070744403503000040c81c46455812250303400b80f02d0104c0311968028500b46000604003800b500009101d000d00040c559523144900d003031070382d40003200c1c03802c20340d40e0504001d10b40b41a0b001c040741001d000c50003400184040300c0030861 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 435684010 1250 435682760 435682763
    0x8120f01032001080a05070c060612030216270e01020d0605030c121b0118030c03060b09060f0d0c05150d05011e060e01050f03040305120609070c030516051603060b0d 73
    0x86604c02c2c1c86a2060fa070103080300400042c200400d00c40c905012a0040c01141c000707007002c44100a01d0304650500a0520302c00300015044540311402c04c129044031441c43d02404149a4541c1e502802150801c00180201c032025200540c0003180041e00c0981c0350303001c00210b42c000c408581e54190390070b0501c401105a014000b90a403c107140c1010721851074004c2c1c420340c2d0030508d00780c084030070309285090000409810540d20308001e554240304000192046c9142820102c0708088185007182c002003138070420119039409170040c03043c85401c0082c5c14150b403000e032030020082030080424542030b20a640052800c82446820140006034843c1c41c100e0382c211820b54602c6010f5410300307006080e96200003000040f0304200082101080d81d8040780f010f076010b03500c00d42d51555201b050180c0014003031409032072075110751100ca091008654004074000501903050402a407112011007041841d03035094240600180039102c030f2000003020040300311083da4419403007008100000000d002689100860 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 435685260 1250 435684010 435684017
    0x30105070207060c0525080709140106030f0b03060c0a030b0d0209041b0306060b090127060c060902030a03080402090a0b0d0803090f100e0c0105090607060908120f01032001 76
    0x28240704040c403900c44208014058412540e102c0c252500000e5002e0781c0055885081b03120f2401404016814018540144580c18013440790703110020711070752400f1042c1700743e1080c580d54000d5103000701030385d4100d2001d90b04000d054401501d005001c00c0003981c00110303841700191409200d40c0c014a040700c500b0500f55000b4042440c281e5a40c0e807001e45812140b0b441500c1044031400000c0026040e015400282004110090b140e1501000140c040ca408100710030601c05c110b28103005070358000e24242d046038024501010306403c142004cc0040c0440040a0b41500070401c01905051300701106034050b510944041000350f481200c5c00040302d01300d074130265000c0b0384814641c0110360001e01540d0030a8422003030b600803d64407070445141c00b0641204020498994610322013030403080c48a43d002403028205185040700100021b0f04034030821340000d02c0e09580341c101d00244601c11b0b0540e03005103981e030a020700e01c0c01c03c0a404500320209100441d03c04003030079444044c2e0b0401d0a9420700f450b0041e113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 435686510 1250 435685260 435685273
    0x50303010b070f0503070c0302090703090510110c0f010213080d050a0810090e0f01050c04060909150b0304030306050a0b040530030a050c070602010c050d180606030b06010801050301050702 83
    0x10022211580b0442c002d461580b502d03003009011810034401409003e101e00e216200c010b01d5441401101400205030303006162400c1c6080e400704501246902e000991010700045035884800a03080a00981c00e54500398414032200e8a01010150300a1220000030040300b60181e40d00c4415640d00e459041100300081c00a11a507a561809201d649030041c81000b0715103507094480c840381d02141c2100a210a1a0344030442c0e0b0300c0641800c5c0300c0c0340c1e08049a284124a02400d020700601203a078548110188940e0710244100d00c442440f04a01c050000c0ba05d4142e560f00341400d009020b4071540c041d00b886103c0d10f686c0000e0040650b02140d0031260060302c00390740701000110480001d000081d48040400108045880d069070910050000d011f690303c2d400d846101e4043c0092400e0065003200080d685400c20030054150010180d0752070901040707010441802e05a0142d0074842c10000c01401c042c1015400702c1080002c0341c041d481801c2c2a070b43c200080ea80d4404050a0342e1041d1741100c0541c1120317 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 435687760 1250 435686510 435686519
    0x6070305030411040e060717130b190c02030333040902030a0204020406122405060c0c10030609180c09020c03071a0f100b0307030b0423090d030905030301 68
    0x400145074010b0091001200c14410b00700131a06885500149100a811400800000035081189020300b0071020302e46a1047c50140141c00d0070000080000c3d104640701070029041c1c110b040c26968162030251402d11021070948406907883d001520b43e03241c03061049030590070b4410b0550300d8140a2074441079000d401c034450010301004146103d0241d8142c061695000b0140e220b030300043c0000c0195a5030312500100e4041844c00f15030010302d03000115a400728401e180c00703546159038416104100c0345c05e66140e4081492a24180505010980000003c4442c009894055103e49c4c22a007250301c0900030502c90441c50010481580c6008080e502c481030180456600359000d40b401303150944c1281e29000c002c0e120080a01d4003058cc0d44050004a0200014004410b1003103400203a400304940103541000c40030780150000525071010113580c3c0d40c002050b55280e400c51035401a6000c9001d000021150182001d40d404854100981c0b0030a080059024400d10440c42510b8005001e5070459081 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 435689010 1250 435687760 435687767
    0x21207030209060904050916050909060408130905090607030501061e120f020f031602071a0d090b04230f1506030313150207150c110102030f0706021b01020405060703 73
    0x819142c0390400b009000104803611103200e1640210b1a840003082000030320b00a0f101ea1507003d42050f400fa10840e0144240f003100098142d42040d4004003207038881a800085c0403e4901d158031641280d8281f0081c44140345000c21580d0203000c990b42c051050344c2e00d880c000e460310401d24040780c2e440304801c030000458030711545d07400180003100100811651516840d4a06981000501c00c100c140d00200f40109803510f4104807240100c00e0003d40b490030314002d00715511b004010758014845200080b148800c860326840000e0300c0ea803106a000f103e007040d00b8141441230f4074080c1c0c82e03083c180342c00003840c4642d000201002c3e54016000149102000c0c2a080d5804000151600d9050720007031000864481c40501d0900280092131640e0003610b0400701c0c02403600503c3d503c02004250084607030070070264400d4800b440c0315040800449403291000c0103d180d442076180d0083c80c0080800d00b5030400100e5002001a05031810001c040c10203102c0c1036500301d1046124241c1d10000070071103000064003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 435690260 1250 435689010 435689017
    0x9140d1b061e210f02040806011e0b031b040509040f06050a0b0a1205010209060406050a0225030b100314010b0a0b0405400603150506091b0c0d020d120212070302 71
    0x81001d00800e0002c0903813414004c2c2d800c035400400c6942c20400060000401447c995a0001250050b8030f0301070f46007150b0381c0c12902c0007910108074002a520000c103540c404004607002088003820b800c14030301d868280070500a08180307080311107a040801080d01000399001e1000781d02e070700603e05c00a407480c11030920000c0144400c126061354003031003012003540e01c5402800040181d07440d283c1d9100b0360150024182440d210488081e090b081e03022281400d80761001e08152540085003804645901e0000314505141c0e500042c051071105800192020041d040b52003480c5c0107a0343d4803c0d085c2c580c01c02d000c241c0224010030703810651140d03101c81c1c080d11a50074400f114541d030203201908545020244c0300707c9614140202c1c130b15203411f4200100683c0103040462054401c00411081c10003200150020001421100003080e1820030f24030303200500b4040700d121080c108111000c110b80e045000c1c1d101c003030b040c150801165112803d61800d6899000300c0b2801d01d05070318011516070707603860164020340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 435691510 1250 435690260 435690317
    0x6030209181006080106050307050f07060b0a0303050d0b030307110409140a03030213080102070c0b03061302160c051002032205031608061609140d1b061e 68
    0x500a0704189100c02110724031400780d0544402010418209040544100d4042e0b00400400108008200044d0791080594401071601c4041c42d50710b0780d03142095000f50000d06c03100341e8400a0700c8000800c058010008100e0741d41c000405101d5020b001e02015180c0c0124207000e003606001c014000100d26140e8010a10b451183c0581e1002d0a840c0c2c21841c42c1030352464007100829400600c0c1d10402890b105420001c00305403009600d00091940d500449503c0e41c03007001c13946440440422810303610007030702000c8042507480c115100c180d954030311450030350244000d031031419516130081602d080c0304810354103e504540055243c0f454410300c69010201d641c4c0001440301e844000460a0b54042c4017980342613000c084803400075401c012102d800c0c607a01810340ca040052404001e074000740c0000350441207411884440c0702d0486400b002c60121100300200800034205c20240c1102c0300c56000c1d4210984d41c81d542c40b000702c80d40d0800454000038402c85a000481c42083e1103c11a2130041084402c3c0c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 435692760 1250 435691510 435691519
    0x15091a0406020f0c1b10050702121e100b0102010209060708090a0e24030304060f08101a03041b03020a031101020a0602040f1a0a05220806190f1506030209 68
    0x7880403c0c0c103002904881e01c0501c041d0000d882d91490a000424080060001241c4000c00c40c5c00400c0003410902c00c3c1c2d0b1009004450b42160440c400d00240020300b58040141804825844000100e58480c070310071408491280c580200e001455105200340c0750b0010010300400e1600c00d540c0c40d007215035004040d59680c000400e480115080c800080d045000310901c1054510b08070210791460025026030040e180664014081007020304c3d84000102141c0c1d41605082016454501d00c5034514000c54100048007140c495901f2412141400114030540c002c4904003841003903a66030b0400daa4291202950104424400b840461480754140d4a4044140121821030070305e6503800059030010f50107422401005401000300c1d0040c428440c100403400d1041c1071038207018101c0500b86020700380740350b020761159088600100c0b0344007082c2c0c030181586d84200d903150310700005000702c184005802800c5103814200003000e2500c0da800713031460140c1c004c1903aa520300e040a90890080d007103250401d038070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 435694010 1250 435692760 435692767
    0xf0c050a110c0a06051c0b010e04020901020109050307050601030c15050703030e0c090109150b12010e0613090506060a080f070b0a09030209040b0f07020a051209060715050415091a040602 82
    0xd50740c400010750f00900140c0c95a9840380c8000508040c0b503455402e100c0b040c0d906160500100b40e81c00107041000900458005803100170b02c0300100c0c018891104000c00d02d12000845606000000507003904a034401c0f0040d0034415154282c843e401204006034801150b81444030070b00090103074000491110441d03048403002e000030400116552402e9101d112100d640d02e001c3d041d8480b070604601c01034840c1d8040d00d440c1c40b408803d83d081441051180c10318038130b00c0201041582d0356511850240f81e035010014003d11800382480e036100e500a0b24054856101060001140c16020581c001811080405044000d242050141840d44203074850b004004400f0408001607550004580c022070084041940518004145c0300040e40d0141c1302f03000350344c003028007200050000980012085601114280c03603100040104540c0c0c02500c0d8002c28250400380050728003e45544641e01c150b003c0e403000c445d40003501c00750340121a81c07101d016114007000c07007140340e02c8400030044540061003000c00614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 435695260 1250 435694010 435694033
    0x1605030903015a060906050d021e0d02090709080d080720031314040b0f0d030509010203120403080f0604023408131e120204151a09040f0c050a11 64
    0x1503001e01d00c81c0390f21209999460911001312a40300340c0000c3c110545954212410b01e0f000640d00f04005800d990400003505242442a01c4184020398030540c050000803841c14020000740141266000d01e52541c800c0c010b61180c0184141c51090065031603807104488428030401c49100301710580e0710310202e44070130880c003001898000600d20092001c081e10090f00c040010800040d1004031140f1031144440041c20480740d03440801c4001c107a0ba25051060740d89001000507801c500642a0441c14421440100024181c111300207a104074148280c00e591552010204030413805251038089441c10131100c1d0324400c605045005c450182088028480c00c5029920350300303181d0240c0e000001c0171182c004c0410626041c407900c42422004148a10b054a041000d80b00d081103004a01a20464413a68012001900700c043c110140c0ba00c80100d280c00320100c581010325500510025025614045221340e87c60f5483c445d2180081e03141d0360b0a841c05041150440b903e110100c2c1d0b500c440d020f071028a00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 435696510 1250 435695260 435695411
    0xd05040e0606133b010501052d030f0f0f0c161502040f172b0e040e011a0a0f030212121603030c051303080c03160503090301 55
    0x11200740f042c3c0c00032010103c0d030248a40b4080329030526013070034500f0000522032a03812100741c0745c02c40d0103210b000c8001c07811b02c0312041c058010303841c080516841c00018015a040c0c8103003036600c0b489040000b40e03800d451350084140c030800d0489000007403101c1803042c41d100c4c5c01c9143d5a2b141c5940500040300c80400383e2a800022640190710ac0081108080c4e010401004003802c84203851003450058a9410f00303814551703680d0089601c0466070305050382e0107111008c0c010540e891035494094010080c0d200f6007010507009004400101d111845600000a039910300142210f0940b440306d01c00403032561441d03007882041c50381c07413145015502170000380702c4e0b14024410250501c3c81180c805c01818a165050240c119000c041d0054200b010401c0034400304490103141d00126580a8440c640d1000407403030f00d07800c5000700d0300034410440819082c0001c0c08800030140c071003500b04030001c00a0b2070f4491000c41c06ca49880f100c0400c064030801141a0212000c01d0402c0030704031848005030050b4070f648800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 435697760 1250 435696510 435696539
    0xb041217090c01020c01090303050a08190c030e013207030908030702060609060405040b1303020705060409020304020a0e010302090103030e010207052e0306050d0f0c1a03090d05040e060613 83
    0x5a1580142c6012000d5a410400d014007130800317003001d94080741107440041051182c8815001400444408282c030702c031100b0107480815000001c200421044198028003501d80086050b00c65801c254980c80107044540d101c802000c00090000c4840b030321010541ca4007a0000e22134018156502851004030b00b01c00e00031840303807600b41c0c054012441d02c103007044880710002d003d060040f07186c20f0801c0005013040a8054101403412414001d1075a2860300328500483c5400540d005500450006000180342d0003460080f4402c41e2078065407500d1f1036000f41011024840a58000981c800410210f8041c43d10420311000601c10380c8c084030b8035400401c40004200e201d900d15040500c0f440100c20803c1c4210b01d041488914041c014a071620000441014500c50040d00d1500040034a01c20011482c003c50028544410024910f080d008e084130708540048803900580c0c020b40c1000f24816104e80100d0341a56880c84c200045901c3d02c60030b010450304003448000c8807245404e00412204450320b60b5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 435699010 1250 435697760 435697771
    0x1e12050a17040321120e120d0c14070506190f020403120807110c0609060409141006020706120902060c070b0a1101090206030c030c0d061514070b041217 67
    0x8060740c9928500c0d00d040c59001180404d07018000c58100011990b602c500311a00c041118040442c120000e10388141c2030080508840b00741310000111a813000300b8580000074603c9003034a075400b9550064540c60305601c00e00e44000c0c0240c00442c0001c0054011300092406c250000c840041e6024a01e10040100d038002c1d0415104442c9103a038512352294080041648000c0501c0d1a1110308440100780380d03501e054112143c407074100811044400c2d1144000c0d500100072408040c40a01c8081040710100b00e8152002c8020190f01c52011802c1030000401c2c008481842d40d411080011741f51000000f080b803410101e80c80b0104102000301e030801080744801510301d0300e00d040d603242c0c0d20640c050485a40000b141070281d04016401d409641c5100990398403821003981301f540ca6507040c07900001407090494071250035140c02004505410002000548450b50f5262440224940c8042180e60700900c14010308400170f9000043c0011007880f040c05d800301d010304007502e4405030b10400d420301c400c04944 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 435700260 1250 435699010 435699053
    0x12080a0c0c12021003020705100c0e0a0e1b07171602030318130b130b0102012a090e06060702130609180605070503070206040b091f151e12050a 63
    0x640b0301949004003186000b14114141189407083c07607a101601c4407d140302031101d4036038445024034400e029020700f210701d080c010f1881d8111500d0348400600d06100f41d51140504c902d0b0210a0368681400781201c064a421003001c2d4030740c1e10440951981070380444004001d483d105446000140c4082010b01203944000340c80211084201080c458981045008910201d003800480b013425150403c5540f040c03050300b0b801054100d20300c80140c1c00b60281c21000c1001d40089001c3d034180c019545507c5020345640c0c0d0b5021991a5582d5511040314826070b500d41e480301c4101704800061400186072004282581c6000c01c1c003071fa0f168120400c5652402c04220b654011003401c00c10044907104e1107030b02a1140c10305904504150310000d6031032000900007401010410045007003d00200b04254481203041d14a521700712102811a001d0b00d0403038003000b41c440d18802c0115102c03030a00303c5c0c001840302d2240407075015032900c1000d12810042d840142e446020782501c000101c0c19100b5000c2d8030390600c85 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 435701510 1250 435700260 435700289
    0x1b0f06050c01051f0603050618090d030b0102010203040209070521010b041a070f170409230a0902100518120313090c050403020907020f010e0f01140112080a0c0c 71
    0x409180c00d6803c000c10014281c00c401c4011070707007a01442c21078001d407a481d143c00a102e80c0c0e000c021032000b803071194802010703141d044108200d05000064401084265a5080c4002d00c206401a0300340c2c0407c0d503000398098010750024903228840c0016141d884451116101180303410440c8110009003a00110081f0b20000340a00c81d10102047c03995000c50039007860740ca4035240f501ea5580403824004024041c110300e01c07000703041000480c00c5d100036000c410b408001501021684003050142444000a80400d02c00003401020b8548120490160090800444100c00d000111360591000c4d4145081821208a12807140c552031007440d09898404021944d812101c0721094121803164070195150303007890a01c09590740e0100507641140e0f41502c0120240d150440140e0400b140b504030003031250310780040381c0301d89000045d0b0034601c4041c2030000c0007402070a02492918003802d0203a516030542220701d00740040c00010041004d04000d250817206a5030641e61400c030f9002c542d0008400c1801e04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 435702760 1250 435701510 435701527
    0x106080c0d090b1e0f070c0213050a1d030c061504142a0a0507120909140109150b0906070302070f030b0a050f04031b06110c070e0109090305071b0f0605 67
    0x4800c0c00d0a1810100c0d44d15410b4940f083c140101110300400701410021640549070440d222654202c241d03850f07040c1c0610803032074130802c02c00c01000341110f503d10440303202413142a01351000c4204c4070a40750710780280c0004da88171104131240084031005141c01507903600c245081e200703c1090b598003800108076003030800c1c44602ca80c00b16040038000042c0715581c00300000e00d1108d400100300c680d220b40c440d07100041c1c10403000c42540c0c01d1465510150b03000c0d060001c100000d400701c84445050341d00d42e01c004c00207005400030000000c03817503002d94142c296081022025914185010308a014030070f10444040c2501c58403501d0154080f41c0c8120703000d04002050001c25507442c06616841440e480b86100145407544005100200c017081a540c41c1031816004807c1c042d45411030f405800074407000c66519200103a4640c2d42c0da0f0680306541820a0050001c0340c080074600400c10003582550740c06007052101d450704e02841c19800601c21401340e0907200012075015100b20b4030001e0605494854442039003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 435704010 1250 435702760 435702781
    0x11070b0309011109030721150e1b012118030216050405040b0c13091506020c0414040b0910091104150503060c0a09050301110a0f050f030106080c0d090b 67
    0xc03e541c02c900d0301404050a01d841c000b41807000c550462001d41e00d5035105902640720410b9000c070292180d24240000b401e460440d400100e4020300c60b00407904040070f080c0d03001c2018031040d00c0584c00030b040721540c02d105010500710801016400000060081c6120701d4200100e41070010407405600181c111461500801c1c078020000c0c4000e8609110514007070340c50407940c00000344036070f1629002003551a80c00b0840445180a0820132008010700e03030401e6040c400300c1c1194801c41d401445001000c00807420035000f0402210518244284643c48a544000880000900510080c400d582c0c0c2a40004d5040c090061443d01800d141c01064040c6801c0c0011f580c0241142e000300900c5050400880e18006482984201d00d10611901c44d880140101c4505409900599056081443d014040303003481c0001c100414140d01c8500001180490550f054000e841c4150001c1d2000d00c0100841400340100c81d0b80090207008030380c984110034246404540e003111054540810070340400090194 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 435705260 1250 435704010 435704021
    0x30207030c0e0103170c010e16090608010218060901050d0c09170f06180114090304260c0f010504180504050606030a020607110117011d0a060303020a0b0711070b030901 74
    0x2c0e880c0e8828540c11a1200740c08145040e4005140a0000469036101c3c40294040016500741800b40c03008034401c41040116041c080c020700b80540d141600c0014441c00500c21180100c00c403001800310541048104030068000341c1c82141071000c20410303070181c012a8811000030042a44801b81c1c83d13810040da42c1070f00c550b4076010001941c0811b8860709000c100250b4150700c610021b0409007082d001c030303590301d024002c810408000c040340c40c5d003440a0200c000c40900141d4220840c06e40691805d00301d66070340c10101e4244108c00d604030365032140c1282013140fa034802034081070601a18060b070320401248000d098810500007161b541c000c0c00108241400841e400c1141180141510000c540015009100700300000f004001c030303691a2480c0385d00841d00f10070318410307003103c4410641e542c00081d844404a080c0c01c0c03403000104800102d214080b4030483d0f080e203416030b0050810b0301c40c40c1c2e03424249080281c40e1600f80082d0036600903292004102a40240c021648581d450b82404682142540c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 435706510 1250 435705260 435705269
    0xc141b1903030f05060f30030d2d05070e130b0108060613090e010603240c0203030f04030f02010b03070b0a0e040603081606020d06030c0302010806010906020c010e0f090103030207030c 81
    0x60404d418080703a961090301c1c1c002c0740d280850300c0403545000c8016040743e03421010306404c048444620101140c1c03002001602c1c00740071040080c02201d014501c0c0401c024802c1103204a404c2141c8043d240c907034100c1c0e20040c0d020aa03800c1014048680d034002074070b01c2884031090041c240c0c840519503207559120800035008942a22100d003005445021440b410f40d8500038041c2d010b9a0f8a002814601d00b500040000c1d500081d104406a220304010056400c0b603c0d50354441d181489070300b0807883d1000080307074030074440d42c00c0004007512a5501140c0d00d4008240c0e0b18119900d4481c01100c665040c45444020b0440700c41107503482081c200050056000b006407103214529054081010604290031607803580700214080c6070006039071600000a0103030121100740c207031a080000c0204000c6084ea0003e0360b000340c0301e004003a0f80b1800111044002d40c0110070051b0020090030300594040e40001c04004402007230f40410010400c04500103c6c0309074400e030016403104404000b40241d0403c0b110141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 435707760 1250 435706510 435706541
    0x303051e040e152e0c0c090f061d040b0c030601020f070608090f012a23040f05090603100c020c03011401090606050705030f07080708030a06030b09010c141b190303 72
    0x40d15800c441c0040000303c41e840d0010b01c085c034000d0358108240b500185000c3e1028500030088103c11131b00c1c24004000ca40a0303404448400c0844400a00c0c56104980c461135102240c0070959844920342007140c1c00c05010f50b0f041d840781071043d068004061040c1005011640c0d607007440f070302d0400c94003460301e000754080c0425645022640302e248010070030810900303000803a4028407a03a82d103100319500c5005901c19000120480362042403404250024401c582c031700900800319540f540e003044014041030315600d034103030300c10841800001c2d803c0d0020760044100e070040d1441d490100b8082403d651850020841c464404401404402c9040c840c0a024040919001e42880f44c1d80e0f450903544c2c070440c078032442c076441d0205040b8104198801201d40da15880600561242003841002003e0660750104a801603006030020b0307001d2205114494208071207540d107418000380b0201c46e0410f54002180805420307600300c11070002d080300b0400c680000540350b10414a655003402e004007280c0e005000e0030401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 435709010 1250 435707760 435707809
    0x1180213260c0a0f12031403010b0403032c0d020105160605060a12031403220303090203010b190501030e10021b060606041511010e0706090314070303051e040e15 71
    0x2030201640130000782c44032030104000c0c1d415681130580b0352028612650306418030000002c01c6442501c4040d00480f8030a884841210a44c071181000c038015482205480c18071a5904910740d1501c694010030460044c1000c51400d51001d00301c01484e0342440c2e060790850340b81d80c1444a5401d1410310344004281102d0105140d00c100d550090580c01c51983c4108101c0000c008618192580340c0c1984004510307001614400c50a85006005000d140340182c0c42546096a0130070541042908607071501b82c120040e8180328108001500203060705024204144210760010a1030000d51008009101518000c02e100a0440c9041031801c10b005054a02a4009000401002d01c000810410314520790070310110744051500e01b107004019555044140d40318203400085c4880c2c1103501601907034014603038940c0010310f240182d0b50344e014074800180000e10030491009506680035401071034841e1401d0b1645016500c681d080d401c01c0e010b54000ca51005582502241c0d460300c0c01c00e5001080d18202003105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 435710260 1250 435709010 435709019
    0x10b03070f0c0c0b0d0c080702010b0f01031802040921030908030a0e160f05120f030304031404030b0106030c03050a0e0a0b07270306060e01180213260c0a 68
    0xc400104905070003403010081c0980300308009248070501800080c0030f40d0b07403a904149008005803e100e084c1c400071440110100e03485600c1801024010756002d0016642c104a0078011001065000481c0e03402c0e0400615403001a13a40c1e00540511902075180d4000c1c200d6240d0038003400141c3e145084043c146000c1d2480c0c00280001d040c1c80d4040702c0385d1000140724080061007800c1034440c801d1403c206520b900c022074480701920f1604152503040c1c8029401c0d44005161695540580003490013587c02400004c0009114116210301006904030003030034a5a265180c51180340d0a801c00070200e5150044034468580c0f601c9000c2d40641030000c140954041c2c85108c0e41c44002c01200030b085101e008000400280c0541101c44890200001c01c03000c0b1244403030303400f003280858001210002d00313000d00081c00030060b0345034030f040e1643c0c000c0c0010b1a402c4d006548000394000e040345108030038103400014584500c03004800a803d541d26140c900c0c140004012418090b82c0d6402e14800c2201000c00d01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 435711510 1250 435710260 435710267
    0x90f0f0d1b0b0a180602030f100f03020117270120040e04020906030c0a120b0c03091519050405010902010e030f0c01211806050106080c0304060903120221010b0307 72
    0x581102d050f000000f07107680c51390070315110707280450409000140000140844543c070004654481d1009841804401d915280540c28151881c4000790014802518040c1c00c100a00e010980080c890340041c0e005034a6092040c81c547d5500003502c1e01ea0751342c1d001090500810400c2807401410502d60b40c1d1a183c01d14400c03c04400020b04043c3c01360b1040c7c0c0000701300b45c400700445070418078001d100008180c0d65107241145a48241c50031503490806802050101c11008280c07801040030002400c2144030080042d850120000e00c083e6241c40709126283c041c03025407082c00c7c00f45025000209200c0c50314000502452195000b1901070b51240c1d22205e504000802c1090100102b40380860011603105c03801c07031002c440300c040425190302c0c03c0040001c44210803e0759412620880d030a000c3c9a0303a800064400d01c0003165460045942040050300054280c1d1000c0b030341d0380c807a040056143c80d2084540c41241c1050040018403c942c8203c1195066118106401092034046c03240c80c41c0317003620005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 435712760 1250 435711510 435711533
    0xe04050105100305310302010e0d0e09070c08040f05091b09100302090301020a030b030d170103140a0b0906090f030f040501031512080d0b010e09010509090f0f0d1b 72
    0x201c201070351040811125500940085c2c9282c5000101500844c0024850034821030381d00411409580392021206900c4004210a054800e41c0e484000e048880007090000f0407a00a0080082124076014100000c40309406003001d00001003940d50158201340c00d00c42c0040010f8850350b00030040c40507071056820702a080b242d5810064524402140034180242d02900a01d46c040e60b16500100703030001800d80c10b6004d4441c4c50070403821102480b000d0740341522500385952807038040d074007007100600200328481030043c2208498800c490702011217494014520b202622542055040102404152074041120182105c07a0b0301c05146401c1042407440c0c4284a2032044a06060300d6856031207107407002d031007020b0080c090104c041101e50310620740440240c1c81091900c440f503207880070000f050351140b4000190309802030703c0a0a541d003400208804075200400990461054001c001200c12090040788e001449150080100420408020f01307611101107400301c0d40300e107000406c000310310b07091480c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 435714010 1250 435712760 435712789
    0x609080f061503030c0a06090b070503010b090d11030d0f0e0307081b0a080f01021c0b0d020d080d11091005090a03080d0207021c0204050a05130602030901060e070f0e04050105 77
    0x7640c4485008003290545c02049022003503801000c1d101030900407103410a12403907124401c0b001d80c5964140e0709075242d0001703008100120405114060785070420034060b0388814000c85141c00e0761090000080c2c50105c0d100c0403100040c01c65005114040e410140484082c20210060014035040c410215501c8103a8081c5030701081c54016034900e00d49500c1a42c0024160140175103c91508080846000c1d5004040c640b128240f140c02c814582800c5228144184100621030090483c3c242c08100084d004080192041d002c00c01810fa13414401b4441c0610211400c45d03a81c0c0c130342c1030a0f000c0208030303c0c0364101c0106008080025040598910003800240d0b1740c08140c081d01e61481c01c03060b000901030030780020341100c1d0f1030360004180000300a449480e1803080b40c050000d40c1e03c0340344040a0326420368030b1400740311440c1c00c16070006800341c001e5a801000e4030b00000e0900d82e503c050040039442a904000815800d00b5950426030b8049001703808083d05840500095140c5008a5200d00c0460230 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 435715260 1250 435714010 435714031
    0x40b030318062a0d020a03080103120315120b1e0f040f05010c0302032707141903060207030906020f0309130e06010602010b010f0206060604050402030705040b0708040609080f06 78
    0x400064903074940c82a2584180a04180405400443c0c00f080042e2120380d5000480d10504003900311103803000401c1c1c680d55600d941c45589603403850391411194628400c504052540f1401020307511100c110703115005010b000c4401c6030b140900d0400104054015080c624002810b01c44044040903224100e60449000e80d81540c00c2e555600344440205801080140b5039401c000d644500a54550050f42c01131201000399000c1e0079188800311900b80c1c469686044a0300180810407541c2c004000d402c025000207400308411070144180c0120300001d54004480056012903030405150b401512140030708031900081c01c1d4055456102640c078025401d04502c58161400b0a1400d02c0c2c540d045820341440040486006507162075001e4003801545401d42e0004403041c005e41d070b209100182a50240c04042c146a180070f0600041c0400f950004080c0d00a10804120000c0c0100b08030000b492080e005680c06038440d0f0071700744c0c0203080c50020342c011482b5500c04d04089901e00c1001c201150003a10f40e90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 435716510 1250 435715260 435715297
    0x2010c030c0804030b0103020909061e0702101e11030f0a0504020d0b07020618120304060b0402091801030c0b0408372103060b0403140111030108030c0c040b0303 71
    0x2504a4440751203000003480c0c00c4011a0000401008080c024140c074404c0f60411b050341d80da086020340d40d0004862079404ca000c3d00c01d04c01d030210345640d052500301d8031610650300f0100291124109580080244d84180440710b0650240e1701d10910613003282240c0c0c03c1142c7c0c65070900044503a04000098440c2100d00c2d521400308086540c2d00034050504be5100a41032441d28206d0f20194035008121001d030000c01c0500380300a440d14000c40c1d2004104c10040e221425900c540c0c90300c0c00200090401140c00503406c001d4203109075038114440b200900c55580400541d811450f00c52404c1c0754a92140e41d205105101c05e1010501c0420035890080054265120660b896880d10880c540c90b00b0281c0c1d9401c00700d01a040074083c16141c00c11490808405080e00c090320a2821003c588841c464040300c010240401d0001843c0101c100b035091036007030004203680d0070045210065030b1003a0b0040416910000c0d0210084100340014802c17144212020491a016000840e8480c030446280d102880300c00ca = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 435717760 1250 435716510 435716513
    0x9070503070306170303090c0328050109080f07031403070804060b030115060203070c050d030906110c210c010305010b1623030c06010e01060c06050c07020d0b010918080702010c 78
    0x30f0303221500424110794850754000c2002c05090f1030b42c0c82525819403500078641d504c0b840c0c2c20300143d10403512080c4041800e0920a8500c2c03070000d00d0303d5207070448555403100c41c0c1c0c10120300d51034068200386044a80705030341c94009282c0904003100e00078403807030740704001d000f0001590b411008060340141c00c06000700d90f00e054040081d00500030724010800381504003002240c1194000003420640748142030f02031119440710b0070000d05140380a00100010784650061002c03a04c2001e414030440140c508488202039044001a1040074508031603088881d2445070981040041000481c90325086c00e080103c1e50500701d03601428071460032110540e501c0121140d041026881c3c0d209460b194019000070803d150004941d202d900003407603603165105010020507088070070550f0604031180c941b05c880c107221003640c0300c3e0050074009103504041c7c4414001c81c03026031107102005458601c81c40c80d05038190b040205176004c60fa8403035401d80c000c4003003030380c0d100c0000e0444044440c60f03a02402c0c4105080100e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 435719010 1250 435717760 435717767
    0x40f0207120815030c150a11070e0601120c020a020103020a05040506071412190810030209090607080108160b16020d0614070309050303150109051020010207020907050307 75
    0x12240001c14240300100211038595108942034003c03a080d68011545151100030165117000180c01586d001d00340c10302443c05e225100c03006103409007550131704810440101d0b1149003010304035444150450100010031809603840702202c1d81c0c0d5015400d00f00200d0401d544000d40d11700e8802c80090505500091441b221805001034a008240c001d240a0340e4031140c0c41d198240c007405510042d8113215030030039034440d004400d0030b803400171000d0685420741710303028901180d0120b4043d158542804030f08401001588807031584600c03c208500003032106040c0081c000700740365016401081650050034a0980c01115094540c045940d0320301d0b00351311a602c418400030601e40c444800bd501c200e032000c443c2c2c02c221880d0480084101165650034003542c3d650307400d038103032242d0b590000c3c559007041000800f040d81c2c0c0c0300c60803100903046c5001c403a0789444001150081c40402d880341c3c0455055000b100100c4140e00c3e20300c0c1e803003003400c0080d4148141540483d01c0c0d000060105e009210012002501c5a4070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 435720260 1250 435719010 435719017
    0xe040213080c030d08061008040623040c06021605131404050708010c2f0c0306090705091302011e1206030b01090c0c170a020a0212060f0f010f05040f02 67
    0x1851030050018955a030400c580e11408840e516000340201000031003031502948090f07200c2c2c240a0311402c8041c0c03440d81c0071142818000c00c03c82d00156a02d00c0c010b07608041c1c11400d10000c61800c0e1188281c03d01d41024101c020706d90b80301104652160000285441450400004451080c0c410126141750304415401826901060380c034040d101c10100030070b01100042d500110303141c0350000c00c0039020500c0d04858822080b6034100f28440310880905d581502207003107164075101c960949401084a0001900b803201c02d451400055019404c140032600d010010702cac3d000302c60b07264400d0700a00c0d2a8006000695280050a0041e0f40840407108440c000c0710140c0764440310000070026141c0720714140d01c1082c000c1c00f41000c032a01e445180000a4042e07655201c54941103120100b10f242208600e81076603003e2280c020441c01040c45030300050f00c45000042a429409003e00301c0c81c0b90150400c08443c2004001d0329441c2c6c8602e0042200c46100300f110419900242ca002c101100140010381c003911 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 435721510 1250 435720260 435720277
    0x10031106070c0e070c0201120507020c01260103081801050c0a0f050f1009030306050105161e02060f040303080f040b130f14100b0103020c3412050115060f0e0402 71
    0x814902040645030f40034071110445c6200341ca51440130130301d14017040101c840880d00040981d004280100841d8003a41d04860304603452070300400f45503010304c4039211002c9c00303038011910290082104190612034030500c24a046083c60aa820a041d0084040d03032031000c244c010304a040070041020a0010a1020190340000700702110354401c01a04040002d20b0030341019000249003a03800f0a04d984100d04440201c2950f010f1110300e005a91120760008500da40c2c440400350807890380c4401620f550014001c034070040d049650b00c592035400c000c0c1940100034022201c91060b030042000066010703081a801850040c080b5a50801514201d1108009a0320141640d000144144c0d031403000010025105880c07588103001d030050000040d07040c0d000c1d440b80039490f6040b030040482000507a0590302c074000c00114140c0002c414401c0c1402c2c41c82119048544e00c59079a1398044c052113424010894141100e1200c0c1c640300d80340c0710000300082c202c14000c0c0100078000c1040e505550325901601e2014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 435722760 1250 435721510 435721529
    0x103060b0f0d082505030703120213080705031b060d0b0a030b271603080306061608071101210504021206072a0819090911090910031106070c 62
    0x4154a080054071904400c2500701c2c03484e00d01d8820310000c501e0f80000c02d40103a01c50000c500300b1240c0c0d5002c0d100d0b062078400d1450040d90034443d0401e5141d9a000004c020318035540902001070070030b41454104540203044075000840074410308000c0d02d03000d04550810051482c009a0708403004005003a108842c0d0001d031401c40182d0034440740c0207040c0c0803001c00c800c0517140c09000c514017803525170316241180c000502c0c02401c8041000440d1440d80215072188d00204001d10301071256141400311843e281d0103039408203002c10f20030f0800c080030201c0705900c2c4003420550300c940a01c00b50044461010b98050320542c4e1900007207421511340d2a840c08030741241c10184c8010380361082e0020048000c030352a91030700c0d801e00c015010b9508015103900c195180c20800980c640138080070f042c1d01240c480d94088040207622000028507c00354458080e180f085200d5081c0c0e105200406c0020756040078001c0d070416200400200b002924942024503611815101d460b1540c196041403100c5001a5102c0a0003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 435724010 1250 435722760 435722779
    0x6080a08180306070210090507081507020f0105130201050a0c1703060a0b070213150e09060a0c021516050c03120f09060709050f0d081c0e150103060b0f 67
    0x4000c0144040c00004254100103014040098101981c1e01c00a82d156000740c3c00003800c6120321042d9402403021240200d040300d5032540d950040d0f500c1c04228500054400e1040010320402642c188070840310061100000c0c009403e00c1c0040c00c1701c03091050300003030500c0000aa1005e032140501a0f0400c42d68000c200a10750341030215503060940d04c2100c4043c40303a80c10079008100c01c40c0c3d910a0303450098000e4401c8983c103000c0d5140000814100ca42d000b00c194241d40300040c85040c0c101011300c03a42024011b000241400c107100d00075145505203c03825034000005501c0400c44e14290a540032103039100741c9003030303004401c002e0310a07110700700c00b054a90000060707030198085151074450142500010820701039031400145034450390150340344c00000d86940001c111038038041030b200b006900010440920144142c0c3d401c00185c0c80142c1c1c8001c082c1c4000304469901840d44900035940d110600075014a0f0060300030030381041d50500004004950b180319030384041d149c0074001c0f40c0490014055484 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 435725260 1250 435724010 435724013
    0x90411040903020d2a15090803330603071404050a1710050f0721061202100504210602090306010806010f0915060f11160e0c0c1c0306080a 61
    0x4031004400542008100c2030003521702caa224801c410309101d440c1d4a0961000360141d564249166240103085c05403544a004000110b0810700065001d0601c203002d402e1907030402c016044883e603844c488000c40d1400080c005095807140411aa0301031424581210990004c80003800c00b8011504040d403c0712003030320041022144040690b141d100706800311080060214141029240215a107a003441c03407181c0443c4515000b01d080901c469042403002521001b40e940190440f00d640d44401c1c2c0e001d41d02c007240c84c00e505001c184604004140c3c5401c916081c1402c00d108a00c02400b007068082039003400100c02070085a5041c0c46c903249005090380c43c5540e46030b6045680384400c0c050030201032005c0c6030000c4d000c40c0a11803400390002841c0c0c001d070300c640380210079030f1855218002e0b8800d0000c41281251900028800810411460102d2410700d5017403960328903104c500100014401402046034212190300001d05209003201c10405a0182c05104011800b8040c81d5221044910038841c0450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 435726510 1250 435725260 435725263
    0x2070807080f0f060403020304030b1504110406110111041a090604030c1503060f09051905010801051806060901050d0201020f0303010806060f040c0807121503120f0f020c09041104090302 82
    0x40090b510303501100d48504942c80015140d960940e00200564020001000080c200342c119030b40c0142008240c041ca2000030007c0b4081d038240079119546117200103400c0c4400c503040f038520610300504c0e1008004110f07000d0382d00b14007445075000340001424119943e4000c038003c00101c44100c100986600d0301c503540da20300800001b58a01802403c1130810241030354251192081004079000001041c144a243c200040e004040150040300d40c0c1c01c21020b14902000103004141c000d03c0441300001d01860700d000300104900e82c81000c1200d49c2c1240080c03020b5556000d0070241912011558002c0031240c030310041c0c1c6002e41c00001c07480c1d83d0001200000f2049800304a4030b01c114401c0e01e06003a000c0250041100f150030340c004c0d0201041554000c107210f2440b404024090700301d00c410000300720181030381079010007155031f008403072480d0b488a5030304000b1752110a642410300141490510a0600e48010f5114580b440306540940e080600050600101691200c07400c2005001001215030364100207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 435727760 1250 435726510 435726523
    0xf020f03010801140c0415031d0f06070e06070602030a020705060103030c0302101e09110a030b0105041b0c062f03060312031014181e0a1118010207080708 68
    0x80d403800f40781c10b59104c50307244060b105103881001c9619090030407096140283c1315142900402d40e56814015009444501d440b000040c20300042803007500e06800340d4a0010002c0c03c0e40208070188500c907001d89c40d80c0060f1a02d403540301e403001d82c4944e640101000240600b200144c07661080a00000925401440070700b03e49000e907098907540e841a02c00f1500b81c4a50700407405100380f480032401c500c054568040c8401e9171180c80e4020074070003c41c00042428040b0303013090720024089001045030340303030510914000c418094118942100c5641c4098029a040380340a01159141c0d01d125070101848240702200103000c520000d0810350103180e440207504211100d0f03000f80710340a5860b050301481019039101382603208200300e5850500d118041c8030724000d26190f070011249030701d030200c0d000c0c0001c00074480e0941c1020050181103001049106a6000c0c096041c528500b00302ea003004d1050768100d4056090303800010a0345903040740100c1c640740e1198040c24481c01343d000c000c544c003c80807612 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 435729010 1250 435727760 435727769
    0x5030a0b04170310080d0815010c02031608030a0207050f030c090411060301060509031006080706121d0c100e010c06020f0d050f06130506090106142206030e0307110f040f020f0301 79
    0x111005074024610986607d0b41c241e440c814202400403a40c1c2c495803140c07034010449031015095407409007062145140d0103569402001481d000487c903040301941c1000300300300030070045410829140341d40300400d031070380f2002c0c06250041c0340d504000740600c614905840104d203005000182d8941e910000209181c10044403244640503540a5007480c4055001e4032003a90300c0e402c00350040d2468500140ca500d07120000b090032a81e103c03800c030110154000300303507119100744030068a0710714040802c210125120b10340300e500f4004079114006051760700c000b04000d043e43c44500140e442c0f0004000040c68011140c5600049050904100003940c003542802d024000584005000083c2c1d140d0110a6a00840d200354103ca903103001003005600c1451a002c04142904a5a180081c00311403c2245165180c1140125001c100700f0440782c0d40c10b11400150084110240d8104040c5585103560b02404204062160300050614102561103521071800210080421540c840d071504060519030000d229 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 435730260 1250 435729010 435729013
    0x3020a110f01020a1403060f060306011b0b04020a080f06010b0708040810090204050603150c03130c0b040305070b040b34030309020a1706160c24060f05030a0b0417031008 75
    0x848150b210072100b542d001f148000c21100620900505014441c0c20050050b41000b4002400f40384014024600310a01030080030044202d26250040c0880c070105030b8003041a642c4408542c507482e001c04584c50741921800c000d126562122410000040e01a0750491400d50103120020a281402644565809403099500f84040d0341c80c2010191610084620801c0200300240010190444500155402300110040200d01c01c515281c040c140c044903007060102d01000141401409001c000040007000b0b0925128a01810441c60490030b011360b05010070400c10150f503802c3d05400d000e15202c01ca548003090010900041d0030010042d00c2403400c164061042880c0c0070400c1c070a00600880c500180707100814090f21a0f40c04809454100c4141c07c0400c44d4905000e0005645200b0100583d1030a0000403500d1041013980e1049610381d0380182e00c198011101000503490101c0d4410032581c000482141c503070b0b1a410100701ca207250240c5c4800b90f8900001b0400000c111270300d030f0030645a1000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 435731510 1250 435730260 435730277
    0x1e010c08071d01080402042007061a0f0904020d05010e0313140307061404030206070b04021e010807031e090303060609081605040b01020c041406030d0203071203020a110f01020a 78
    0x2070080c0c99061003040c044403070803241a910b0910b54050b40d850380e0014400740000035850000c003018600c4000080403078401d203d001517500300344003640c0540940700418159900509a4000005d401032407000c000030300079402c1c44001015580d44801080789250458028001000c0024642d5204e6001841c00c1c103070b00d44494000308080b000068a8801000c0180082c9030050034450140c0e03641c0043c20001c860014208000310041c0c0b903038406020f103c0e00c0b902c0304802d50f00340b5104201142ca14501210440d4008051000071a80e1100e4600d40010b03450400003040c2c8080303040b44601d0101c04031440e14280c2003507003400405905074080030031141c0e943d072000c1d201a1038800c843d0301e41120010443c4200c081c142d0912042c58541e101c2100c00038140111040300c40b01d14007203401d54a04280e049154250390f802c0185504042c003a01c648107d49101a51410200360f80d174206207401d40c41004205a40070502c40134a074043e1000700c82c254501400c440308003103500d070310324040d610140880d40080c1202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 435732760 1250 435731510 435731521
    0x4030b09010920030d170a0e210d0f15030b060d061404140d0504031707020d0c150903170309120408030d1b17060a0906080601090b0625051e010c08 65
    0x2d86d9070700340030212803018800c00d0315103e0340000640b00c9095041600e02400200400382e146031205072121142c1103a8075500c031a8000f580808807080f030000f590907035003080140c5e00d0840e018200c8400380c9a0100800c444d5441c0c55010403005a0b42032030003448907160030110b049014402034094070891050f100c00c2701325202040040d4484080c100d0078000b1a40901c41030002130605c5050138000c2009040f000c2c1009110b07000200829843c0c02d0548452603925005d2000100b07041c0d441348120040e04044803d00c0c41c550703401e00e861240c000d0341c8825142c00700105000b1102801180c4400e0900e112854070749486000c6076450380c0c003ea0101d0070152501c4014005044445d50f012a041a10385401d1403810f041001103085100c010b0900c0d41c082e84007400850408401c0c400c20024100f12030040040e58141540c401c100c81ea8042d80600c42c84042c4940310098545c200312960801d980d4519010501e140d107001840d10001c86030743d58071b1410900030b46009000551028071042c450780e44040040d1142d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 435734010 1250 435732760 435732767
    0xa060e03131a1207030c030b0303030c0f0d020c0715020d03060f09090507170c090a090209040f08070204050c09010e0f030601150903080a03020a02060703050c04030b09010920030d 79
    0xd0000e041001a0000000c0081c1000c0b030250300c04602c80702a9851034684040711003101d80c0e20850b03240d4082640d800d1030742c501c164035102d407a01d1000305030002c528608140f045041c8034000e040002c04420800034106215440b01c0d0199400d4208080c1211200740c0c540c0005d444045809032102c00500c601250305204610034000d4108483d000764400c084030b03041c40072050190840314015186031040190001d40201c3c00307a621000c0b294004044c1108400d8602080544203015103889130301400c044121001d03a44e00b0070006e42280d40009d2824208501d441d0409190140c8030000e5800340c500410070840c03080280c010180e00d8001d0b640d03101c1c1a400101000031540ca2200b14540585c0b0400040c8140040c411455030908094209034240780d581c0d03034609015501580144000079000301c2c0641c01c0c6901040b90a03040620360400f405289007050400c18140243c1c400a05142c1610b80404d10007002980700007440c1e500f00e43c0c00703c91045201ca0b61945100442c3e10203000b0f120760300c9007883c694030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 435735260 1250 435734010 435734017
    0x90301140c1c09030806100e0a15120203010e160c0b040b011703160305090d05060405010204030311340e0f010806060d03080a1d0307060b010201060909080a081005030f0a060e03 78
    0x62617100c050722901e8050a01c01f1071002d200d0b0b060144425418841f15940c3c0300701c084401400d031241039110500403658001d0a2080142840c3c1d00d0718014401805a51910005581c1c0003554011804810210003411144581101c03009800207904005200c144600003843c20f05a80020042c8902241c4210590355648141c0c040584001808042000000d1203000246080c40c0024a00306000103a6140c041c00c04605941c00c40f40343e940000c04008043e00f1210412103003c80345c0c00b812110210000c408450301d1200707540185c94482c0d01c0c100070b06292034085000501100d1040315094607004038610295102802403100c7c1b41728500004415160000003a200b042d8140d03641d803001d88032503a50070058075844541c9a00c031501d01107408200d942c2080500101c9000b1040032841102000002e8211102c603003002c180d09003450403040204105200301ca0040f001882c00b00080d9968424002c0801d00a801550340b50084280700311801c400020403c4030140500e50420081a01881c141e41e64030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 435736510 1250 435735260 435735263
    0xf0420031515160602131403010501060f0f2d170a06230f0d034103100305250b0306030613060902180906070320090301140c1c09 57
    0x18800c0000d600340c0f03500350100e4101d40e4071440c1c0150400840c0c2a51020301c4259030802141c994501c07039030342514542409028014542400c208000151081c2d000b451941c1a0501105200311320150840c078079078148000d183d4107500700005800701800d080091030a10394081486000c0c001101040e454030851040e441120820070280c03441031941c0040542210b0b107840301030740c460140201115982c80703035545214410311130340e603048040b01043c1d0452910444400520300707420340704102c2e06852100d4010340d0110308085c0c80d0180c070795032204140c1c03130100c080d600000c2141c0a50440110081091b0020442c0242848400744c9541d885002041c124041120b02c5949940680701150443c0340303281c1c41098842c020f10021030b04414940100b00f190310080100108001312400b0003005a07000e2213069086002803030103010320141c4100b50459600d03e100d42e90018a000503030503e0702e95003540070200000355a002c1044074a050080d013090340d0002c9140320386800c03403540d245070040d9940c42140640e5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 435737760 1250 435736510 435736549
    0x30b010e01030902180a06170f0a060506040e0a1401140c0d0930080601110c01030507020309090103060c110304030515040206070b0a1b110a020f04200315 68
    0x104020300110702900c945032050b60420326850074080d050820700e07034803840b46400c580c0c0030070740924200c2001c12281d1180c1007101e083d0040c80640b05000d10115210640941249000c9400c3e100c41c000070740201039800302c1036010720950401c4d20801c0882c1b0701c8040c04a4901f1b00800088022500400c2d1244044810f100360100400c8144d800b00c1351680946d8026014110710041c02c56040206a5100d1302559044820000b074102105441e50103801d07030754002820302c1c080b890441894141c9954a400211060502d42c4800000e04824400c10030b07a190030300000d100d8011940d4a040510050007182e07524800143c200d01035400d60f140c00011141100d9018000703080c1c860903101c0e4120025800b034002c9a00030810848180450040c014072806802d100720002543e1810000380c4444c4110117480009021584c0144a00369034003141c1d00c40c009070140d64813405084108002801411007005140d01d003c0c07480002500113802001540c42407030344035000e0010b48515400c20040404080d10030155 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 435739010 1250 435737760 435737777
    0x2070b0a0c11120304080412110a09020901050706090201052101090b0303070807060c05040909120e010e0307030609140a1b0e310b0a0903081f050d030207050a060e0907030b01 77
    0x1902c0f550380040d617200d0700a040c4a824580c83d410559140091500140c5007550807070004040ca180c0051502c008090b4918114940401e440018001c5e0250413030280400e80e44d60402e8041d079020300c0407100d18001c0200322444070300b0f5880407070f0b02c0e01c40280640c140203403810807034215a017800000c481c4c2140c1c10940f030381e040000954450b80a80307000d401d8081001010b010004501c1100d01840c4039991040795080c40c4400320010090030240c0914905041049107440b4420a840200d442c3c030035030b40c003c940031603540c183d0b0520400c01050000016628401c40c01e01c04103005c422032070182c1e50440c2003192090160345400c00c204003070042d1148004003040c5030403a000458a004020744410b8101c2961051022a40750300c0c03041e41044a4041c940d0b42c90b8000c010805920003c00b5500c20110000e0150300c41c1030500701c41c907024040c00350500603550041600b00f418003c00c070800092074014074901e046030301e42030002d00100c820345072240115456004269000c1c081d0203a50329071001a5101c086 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 435740260 1250 435739010 435739033
    0x20d09051b01050f1605030a030c18030206041a0f0304141504110915031605131415240909060d0302210c0115030201090f0e0c0310080102070b0a0c11 66
    0x1360394011100807401c00300300d0382440000f41050010b070004d02841e88002032070381074000000e40198401b08002000c460703030300720500c016510350080d50309507450400018000296840c20b80720621850040450500003c820041003140006502d0032410b13180e404e0300c041703128175600403200c5817098800411700c5850b5011041c0313030304003400030716070000702141d11100c000510ba0100c0d00b450201803103d8988843c0003414806ea041074031a11001040c403d0302001121802d25000300940da02801c01c992181018806030700d1a0740d140c200404601aa40800444000c0201c240701d155001c0103e0a0003801898005601441c1c18140d803581150550040c2100d000c1004050000d055402c8c002c5210b00d10074840d24403180424480e0644140d03032800d02d002c0c500d0541c0009007650826900c120704402d9844002e109000a000400780c21850440c4e10341e40366103803c100d00d400d4401d42d4120f80301a41c0301045803c144054030030ba140c0520384021f0101701210750039804031400408030386052110f0b4021440342a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 435741510 1250 435740260 435740287
    0x50405060d210906050703210b12070303080f010e06010f051b0a050705090127020702060c10050a2013030b01080d1106010e01050f03010906020d09051b0105 69
    0x69020100400c00c0390500001d0b51201c0b0091044100c00b01d0061080d100c0040843e0090404805081181032590070301d103440e900107081d922030fa11003900b0740e0520394060200c0455078201450b46207000340030259485401c00c09035a0743c4000c1c4001d5002586600218005400d844903050581d511441c0c4810940d40d010019610300b241c40e8503000422008101218020b01c46004201407140703120068402c03e0356504046103001e10b6604040c4c8500080401005503196441c1c044041001d084042d151211100e01d490000340a24640607400010026810100c200f001c034880048585c0e608040080c2e444000b030640440b5050403510b0700405c11074911010410229018003103035100c1c0c22806031103d44a60f10060598230a0344401440d44c4100001a00c564015119461103500d080040c0072645c9800c1c0c0462640c4010f2281078040c6605a4040b20039882c290040000030b6000b0409660302d100020b00768008240144c01900c40d03000d074280071329042d000068086080d18059440c10305000244000c003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 435742760 1250 435741510 435741521
    0x20a1502070f0f14300705040f05071d010f050f040b0a0203030117010c44010810110a0318050604110405060f0117090c0a090605030c011403010504 65
    0x4096115441001640210300400080070b03003ea0200d50b00c0c42450f1640111034604000c0e403c80c450b00740ca8180d402c2e0310250406094086040c4003000598401c090813a50402e007607504600d422070700b80030041c075400c080c0d500000d0154100740d850600c082280e62848030010801c01406001441c0410f100c1c0340d55101d04044d0818100c0003036001e14060b990ba14000b0a6801000b002d40540c0000c4010407854071410070340010403105900a2150415101c4020010a04011f00b503502000e8000581c1040c10071000e030b0840031800350080341a4051000700f607022090244985c0b0451302c50314020400548a900600964806c412081d50421042d9607060740a092100780200d0486100503800b400300e2000c20046000720f0280d01c00031201c10410302480b05980004100d00d000d82c1c00c006030f2070705c241d0780008040600e072014220b00d02c02d6110078460508000c407501c05240e101000c0039021030300540f25402582102c80450460790003081030001516008484000044100414401000700341040d4005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 435744010 1250 435742760 435742799
    0x1060302031b0c010c141305010f050c0a03090f0801060e060402030604090b070905090f040f020d050f0a030503010905100501050427110912190f0c030503040e1005090103020a 77
    0x2c02d9041625005482d801940020354169102d12410340c010340c21407200004d402240e15440e02c1c080c58082c0d0b9401d402c0b0341d07120f203504100091103d41d060310310a5003554814a4601c05071502002c16040041a0191502a00e20615100240095410014410349080700e030182c500c185240d941d182040000d4200604444d00a07445160150000c0c0d41160001d2040c1c00b82d440340050942007005200b600c000081402051a07041c42c2404040742110f4031020555604640c4024070003954074100341000717145410341034188a0000c10204058106001d941a51044241000b1581d542d100c02004910740344550303408501c04000034402040c40504074a602402c0b04201d00c0c0031904d9041d243c0484a0081c8010300200d4081101e003514038003079403000b00c503d010300001c040b884a84902406a040e0303082005002e2606000c0344800c00c400484064010750b00b0209580d12345594514215100401b250702c3c0c000d0f40b0324480b000c902e0745000b148080c180ca401400210110f8100f503028a803d01103c243d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 435745260 1250 435744010 435744031
    0x40920031f090215120a0f02070c0b0d09081c0b2403070302040803040e15010e03122101030602030f0109140c030c09031006090c020a2d0506090703031e080106030203 73
    0x10030004600864000c1244041000013051701d4074101100004461140b120105250f004010300d00100f0340084c0002c041c0d48010390303200c1d40c03034030129024001800982c40081c0407c0c1c0204251504c034803042000440c0446003078083c00680680d02c10030110102d1030f000c4041240d0203d00c0011869045006580e00a0f0b2a0500501d09519500681e1940d08954000a00004100c0c204824904003ca08905280080c02e2074042034a048000a445244900140c000c9000100384050000020010b00300c07070040030090032510b56100d0074100040d60048510b0354031000d1207030002443d64001d1142c241803600a020307030107080c0c9503401182a243d001820102d82c0c01d4082c0203501032a40e00340400c000e03c0580107000543d5a181c4900703c2e06885c07030303181560b00359081040c60a002ca2031008181c2d11002903048420503c0c0005a0071510f109e0041d9006455845850108102d407200000e1040a880c040e0302d03880b00840380305510f8401ca00024218100141c03426004000350340c001e40145411014001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 435746510 1250 435745260 435745279
    0x7090c050c01020d0b0a08010c08010915030c080a0215030f0402010f030f0e0705040e030c0c10020114010603050a051005060703081b07081201120507170102040302040920031f0902 79
    0x90101d07081e42c02c0300ca550303c80345a449010301d0007450030b24480001881440001d024109441c0c001610407a414441e119400751a40090854011400f8481d40595401001d0512554407440140d0f40d54101c00340c101d015005803051000000a098241c03031080e848600b0b4030b07200e659941e00440351444ca003900981419140e0b000d030500c500d1140249a022031160000340516881c103402c0000f901c0040b40c0d80401ca0708100b0401c3c0341c1c01c0001c1800d0040c0041581c442281c0010241d0890040001d210311000350304188002203015940340d000140186004c0d001401191181040070008402500c2025031210341041490300180c052042607501803c00070b001031500c540f4459500d5a58089582140d1881000030392285c0d084007030500b0b0340903040d601fa480c94500007135551291703180154011002c4203c00000c401e000301c0c10940448001c1c5034080c0c010f10440049207400c2c00034810001104c44c206130600f80f4020309050000f80843c41d40344220009a1100e840e40090000780444001681c0118a14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 435747760 1250 435746510 435746527
    0x20409050309030115080703020910090e0d02010615080403200d170f010806190609060f09050a0507090b0a0c05060408091c08040b0a0e040c0807021002040807090c05 73
    0x5106080449004401560381d41c0e46100405003107900740c00840000140142e0180401040028007405903641551040348a84806907601981200c6030302003052241892040d901c501804103080c0156489034000384415903c90303002400ca100048a1000006c03224000107010922403110840c4065143c404c3d10542ca5a0300c25440c2000100300038076000c00c162039180d80c60840846e4166502c40300644008200354140803070a078592001401030642c050f60742caa41d261008850344404c00925101c101040003607919103108529801c68850110482e00d0300c1c0004500b90118062144201d2295842030321640c01c2c20714122064010621140c100b1915201000000f4400c0202c5405580a000416110b0a8603000c01c03207400c00d0500981180010228140c0000e140c0006036810340d02d040021075160300d4251812175010550b41d039540d5003d414000f000d404150450a01c1d0701808040d420340300314028040c540e60517407181c3c1c400c0b580d1584c41144100943c042641c0f11154281d001d1400c0c0e803804041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 435749010 1250 435747760 435747769
    0xf04110d0309180608100b01021c020a12211806090803040506010f080a080a17070908010516020a06020904021606051e0c090d03120c02150105011418060702 69
    0x105504a0102c0c00c0030800344610007010a0054000407443d80a21880303041c83c0d00540c40d8102d2402601005441d40c0324103c040e0300030b11920b5a50241640484501001c42000940e10b40d43c103441902e02c0300141102c0e0344500d1084004802034401c4c45120140400200b40c628024003600903070b040c038a880302c00c04000160003030059018940c0110061512800e00741031440c1071000603800400d004c01030342000c10440c500030a11004043c0c012042684074440060f059808085010a100a2640e2141041300c000d4010146806491200c4001c10503a130b00c0000e17a1076861010211480941d00400c40d040015140fa0010842c08038007134009400c01d6060704e4440b54401c1001021034415403900104030000b08030b90010f00702c0c0796025060809a040c0941a60603074482e42050300c2c050b602952159081c9805031000901880005030200b1010a20f204025107403552200c9a01d00c003400318000282c2917200302c03029284001090078003440e0807000d0700c100c0d0420750446d4102d0340004081c0018400341c1d84 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 435750260 1250 435749010 435749029
    0xf0a0c270b0a050310060305011d19060902180f030309150c010c020a03030f06030308040204020a02071a1305060306090c0c0f1c03150807140f03060403020d0f0302040e0f0411 77
    0xaa03034070f0745512800c00c011500b43d02000c1e501724008251408c0c00420500303c2d4a4441d010700810500060150340720840050104c110020303418080c40e080036400039400600f40c4c020035030521180d6000400550b4801007056402e000620154160b006021105441c078201004681200d01c1010300c61814642d122241d095445440c5d113480076820a800c62410b154250003003004454011307a08018950643d5000340070680c014101034019903010505050b518001c200030000741185016140c81c0c805010000252544510118207200d0740203007000810307013440c5050f2801418028a2852644d41c0c603a12600507401c48000107032070b4822500340141a02c0c0901580c558000c00903c5a1140100000007034107940300000c140c0301045001408000890010a0681c150384140c560032540341c595800044428850b00031055042c0102c0040c0010581c0004428034110b1060b103811141400c9080240c00b240150311a29010050440000b48000c105000c4690302c0361064600c2a400c20401c0085a10700740c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 435751510 1250 435750260 435750277
    0x7080708090309041a271f1d2a04060f0c05151605250c030f0501140601020f120f07150b01111606080403121e050115140a030e0f060f0a0c270b 63
    0xe10b0414480c0d49846850019070b1200c9c000c55840c07681a400f031001c120345c42248503080400002c1132070350006038030901519000a070000c003201c81088584002c502ca410307007511440103900c40c0c82c00864a5a000d042507a01803c20b054540b1500102c0e184c0001001d285900211800382d446c4e10302100040fa2500351160160245000041c484901003c46a401e00c0c05000a815076004c054042d201c00400a441074118001203221925201c682d4481d8a0070f0249010040135a075030000c01c00704000700d0398005121030100341c1e41c507842e840c880b480320742e00c942e01d80801e0000321401130340c1807040b68083c0d04240c2c1c200f80f19140c1030500780041c4030b0f48412070301000c140380700c0c11028810203c0e2401640c0105030140549030549107040020b0700303000c3c0c401c0704442e00ba09003011010504c400007a003e9808400304d801103000f500c11300060440e0003a100c060488601280c090107e001c02e0100d1260b00c511000d14540c1e480342203039210108040ca280c2140e018030340844040b40034000c44c080e03a04401a21158 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 435752760 1250 435751510 435751559
    0x90506040b0439120206031f0b0a0c0203010605040c05070b06210a050606010f022107020a1203080a11090607060b121506060307080708090309041a271f 67
    0xc00300c201600c801410552000c00842c0c550005440566201c5c0c0440c0e42000c8e41210100e404852145070801c0a0b03090ba010902000e030101c1c840702c081c7e400046c0d401d800c9100f10020405030b91100200000c0312090740300103000800501c480da001962425055400400c02059202620440c4207030303800c11180400144c0ca0380d003013481c01c44100001041080d8215409084c0010440030340c0100a42c1d81260070551000c541c03060b0124a0040b0422040314545078014210310032054490b0f03405212010b551b0001c500056002000524000f807602c02c918100005010040c900b881601c10003440f600300110603100140d681e0300400c8503a81e2b2080061000354004007510081281c01d03401400294014481802a0002c0041281c0d603580005c03110340c04041c40c03d280342c00780c5481003840c0ca10700491107001d070810320f0a0090800001c03050300b032010301442210804212400c1e40344d40d440000003500400b410b0303c0e02c400400c0003d60000d0900d8180c002d003103000312145940c1c8000074842c0c00380950140383c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 435754010 1250 435752760 435752843
    0x120a080402120f0a1a07110c1e120303091c0903080d0f2f1312080c0105010605040f05011704060c030b030703080d05070504120201050a03110d0519090506040b04 71
    0x5c000c89200b01c264826039900f010f403580c41d4403690440d1181113410f891131003203240214952803402407000e418205800980140c03580904414450b98a80c81036401b80b41e64402e1074401c042121780703145000401101c0d5610120b61500d140d85044144e04000f498072851601c40007024903643d2288a1036450281c10031114111440c2008040d2844020001000101c00c00b0841032520010741501f4008850001c4111054000306040c480668010f002c00c00381d0320350030640000380066109002e407080d1031050b4101d0207550740d41e000554203202e80e9512260102400000240480c0c0745900c810158111818045445d4040c400040d0070f221040c5c00450b0341050204c1c545100c846148103040e40030b500303800c10710f00c1c282c20204178211107442c42000038100706001a00b1151188250040400032005505164039104e0891031080549800c8a2912411440040301020412903000705030003103401001500543d1140c0e00d46084c54a00100103450b180d990040051410030401c443d49400c10540584541 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 435755260 1250 435754010 435754043
    0x714191b020618030109050f0d0f050415080603030d060e09060a090b04081c09050607140a052a0a050d0801120206030c090a15050903120a080402120f0a 67
    0xe40c160240444035a4044032401401a16100121004056400881058100b100380064090104840b0082c490300a02a000082c42130001c1d05208582180c1c4540140d0604118102c505014034440c3c9880800000c4401001e10300030105079411040c05020344c0c2c9013104181c246400d0b0340c01c0c2d503c103650048494007004030180050100e030381c0111074a0303020b00080545488110035080302400103412003600044904e803d41d01450188404081a241400401510700340a46c440f081140c07501c02080701400303c0540e0f405110100c03412000640c44d00c2d42024007284900c100c4907144440400d000100000344c1030070220030014444443c0c801c41c01043c0b040203450005003c0f40040e44084102922110081c0042e907071030007070325030200c02035030403c2d250310104001500c40308450b03104d40c5000c02005041c43c603007940b00300241004181642110050b0a401100020340d100d001702e4180042c01d21000310b401460140520210b20081608440d110809034110505054607a00200d4543c00e000c4c0e420ba0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 435756510 1250 435755260 435755267
    0xa0803130309050901030302030403021302070b04060e0f0a080406140c06090f0f0d080106030f1b03061a070f0b0702030c0102040605091819020319020d022208070905071419 76
    0x34080c00c010346042d01315524554029550340100c7c080240306a92600d1910950401ca40c1983c41180d08402c0a5900d0b04003400c00200806950380e143c12640980074003410313103000000d60510841e91109825180910348042140c20140c14a10350903601810051503489000800c680780c083c2c41454058036944225000c0d03c2d1034210a04170800c0a9040004d04e180c02d1b0f42c00020803811240c90341001308404000300240c8009111072480d01c0800750342000100852580b60f4000c070300740c03103c400f0001a44c5100018484c818011141c000b0007102415050700c00007808244807907040080b900480c0d09201c5060703403450984e00a074121000042000c54603604030700d045245502a00c0d03041414070440c1c200001e41c101e980007100b40d00f000c0d0680001c04180a440d84040143d000700c12180b045407111b040f00e1101c3c01030750003148030120025450b02d100d0011402040342e00100c42149000384103091800700360101801c0002d11100a0002c2c40c5103c9500614241c000c2011205482030304504981c03010014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 435757760 1250 435756510 435756527
    0xe01080c1813360303020a1b0b01050a0b0909060d0f050a110307060302030f060f01050d020406030f0605030304240c0b040b090d0207181104080111180d0b06010c050a08031303 77
    0x10b51040003074103042142030003103e00075104250180350160f80d91106200035114401c2822940c2910011064020180000140c81e54140c90046038001c0503e5aa0544040603000300052254002080f001188107443c101d0101e6500c075114008404140c03056032241c0303051000260b000d5070b03440d210000340c0b801445c060020401074503150500714151b0034501840c16280500800450180300c3c0ca0802226980c050741c29961306600d2071100359911500c425004010300b001c46103092a160a20f80045107516003c4107840035103103c0c00340b03460308102c03910030072015844056490041c400042c1c0c0600200781e40f046807601c0f4034098880708d5028284544800e1900700d80480c29411504503450034414201c0440211514602c1000e01207121400300c3c1c8040868440c5a0100c9210740c42c090300520703844000c4000e0102c2aa80181e81280310809005101c428140214000c10511711440040c5143d8040c005042d8801e0054044a00380c4007980d070740c000307554010780340114091501c1c0a12010194080e103407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 435759010 1250 435757760 435757811
    0xd0204180b0f092b141c06050a2d031703010611010515220507091505030402010f1b230d0903050607050f1c09020906010e01080c1813 59
    0x8000895030300f04401030003107449082c0d901584130740b201e01480910030081021010302e4080c985079500c0a0710800d5400806002e042c4841c00d017000030009081ca0841251030455845000d403804c4201c80d4641c40102c1e81c4054440c180c0300721104008000b1814600200d550310744180e18082d600e504211000d8800d00f03000c180e80c4d00e680e04140410904402c62484181d403508155400240d131000843d40c0301902000400e8000c88034984003c0005032944036030032404480580590107905441080101c840b80300844000c0e010400c0525181c004511480d81d08407c1407001e04203201171051543d0b943c0700c0a1040d0000040e100c21805003d40400040c050f004214205051100c001407843d600c0d16100d0f0002404801842004950070200d40002c0d0215408580080d00070910256400d0301407000b42504507060f80104140700010301c1c154068040030080040584410840c1e40e030300203403040c4541c07180b020f0f0382c1981004011011075072180c5045034040d86c0c0031407011505038240082503005001844c0b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 435760260 1250 435759010 435759013
    0xa0806060d0f02070b010509090c010e030a02030f01140601091508130f0323070507120602070c0b040801060b160f02030f1f1406011b061808070b0c0f04050d0204180b0f09 75
    0x4e00c41c82c6100040c074100340d4102800e1034840d00e4524070003b400d0400003070000c0e4240c0210210005a00307010743c400401c1e51030f050001b168507103079400112031000c1d01d80201c0c00703501000c9082c00c004c90f00600025600c19070003802000e030181c590b907401c0d006e40c0d20400220081185110031611030206420601e80f04078108003d01d0401060b5141d0740d80e5040d0a00c5200c0b0042078804041c4244001d0750110b420182e0001e0b480140250740740c080425940c00703032290b2580d0f9480c0000204900b00c112003141d5003149103020016000d015900c41c2102d43c0548802242d2500c116202001464020320403110b10165402c03038105840303810703050003042c0c612145c0c1c103041c0c520a4a08101c640da8020054000b01040c4410308070040b10b4501c1c1900041101d03080c45c0807004003200c00c2c4020400c8600007415000d103c6c40444070302d42c495404050b46405041a00d40381d5079010f101c10710603130418076004450b450000b00046902ca4440c0f0b03c0c2120840d8070942030300d400324103030704002203141d4400120b500080c4020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 435761510 1250 435760260 435760279
    0x3c030f0914030a02010e0d062306060a0f0e010c06050130020102070608090f070323150a020726040303020708071413020d11040801110304080a0806060d0f02070b0105 73
    0x200025183c07288140028144050540a8012501c4010080c01003da02107000c0220028a407944038140c5030a05030035080591600004003a42009415549414115101e091000a5044040d2115001442e0403410440040c66100110340b1a0052500a207055200700071000100483c0d4440c0400c1c0b1220406840c10515402c4010303680040c000045408078035180000c2e884800100b81861540c0c040110184510440030092081c801c1072540007403407610689507001038030310b08152a08401914145802c06820014455900c16001404114411314001d4800b5020401c5000c2040c5005200303019998040f42c14010580c0400558010f00211401072008515002c00b017001d680154401300d000e8ce0301381e45091035140140e01070300c081c0c8039480c1040c0080c400b000c28400c00f43e0010301c111502507090003240104503c40c1e400312070049800c6111a0f180241469041c0e400210103130a580d0841010041494101d001e441509586000c000d40540d07604070b681444203a046040e04058030880b00790 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 435762760 1250 435761510 435761549
    0x10c080a08100803040905070306080f071a220f081f020f0403061d0601060309030c1202070f0e010305161503051f121e3c030f09 57
    0x400940e5086005032500c6061581e600c2502c4180000d15400f00c1e10920000c00c02041c8407003950032a501c68074a80e0b030200f051507039640804c4c0d0b482c0e0503205c2b00401604221400d0200c441501c481c4036501e40507880d40c034034125032550300c0210002c1c504c2e859242040588000d200c0c3c849070401100061003403000401041e00744508514925081070a500303000ca80c002040030010001d4402c0c5c900a6400c5a020040311100044464092407018103100340d0780102c20020804a000f8810400352940566a03001101c1c07040e0381d4207a503404070349841703c00d6100c1e03041c000401c0829000d00201401e001640c6140315490f629000b85428019041c695250001d031601741300240c001d40e04141078110703914000c01d40d0386440d10b546215815250604400780458080813881c5145003c0d075121280c400c40303021040130046100b15015084141c00200388070480d07051403400c2185540d84080d02c80300b81c01c1489182541e401d0080982e41c040c0310490110f5520f10b001e40300550031024800041152405800e040c8a0a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 435764010 1250 435762760 435762773
    0x1201030b1e0708060301090804080102030403090f0f06030b04020f0c100b010e010c031d19050915061603050c0105071d03060603030f0c010905070e0603190c0e060d02042405010c 78
    0x1c111504100903d00080d030295002d42100d080b06401c03104841d5120340342c01c0924040e61003100c05401203001c18000040d406600941c01003100c00c2180c6d4616103900b4860b04402400d0302a840720380c06502030220f00c440350398180051981444400043c0300f01c074171101080042d600d903051064140000406c0a04040e600482913010103a818a000d002240a04c2c800001c03240940e0713207060300122000c0700840e4100e144080e42c02541c508854403610f42c0e82d0121500310511243c050030f034004d00140501043c02c480685131240c81c034845e00b030150501c504081205d00712072003240c03600000340e200d21910045010304410308050340010341c0a00789900d40341020a80e00d1241c500719a440740000194948902c10a500500d8600d0344507080d83d003c02e640300d9650500100650b031251003406a004042100c41030100d00c07003010781d0f110100172003640c5031000314004070800404080d001401503e000005a41b9840391100d250403a8996412100201140019034031454016a042c003060010281c0800c41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 435765260 1250 435764010 435764071
    0x51504050d020906010507050d0f110718020a02070b030f060f2d010c080c160e07020c0d02010903060e0d080c07031b02011403010602010501080c01141903020c031201030b 75
    0x4058404503803613141d000040b00c140c421100060280e00411620034031103070740315a00c0090481070f03a94054802110002c2c0355240c0000b8480e0400010040030320394007002d015000740c0100921401540d80c101e40d47c04400b0401d1303204641c1e045a45440720100500e91420788a10038200f107040da009001d00d003d65101d070050b000c0034032815941c600d004d00c60b02c0d9568415078618070310907880100680c94400401c03503d591f81d1891800c005000c0003402d0045210500c00c09628451000c2e94020114a0b62a005000c003d14000205a0401c44400ca000c00411200e00030704545200140080441518809005114000142c10415191b501700300c0d04021031340c0301c1b5500141c04401304c2c488050400510060311f00007001d21230344076840700100000603503036010350115040f10080340a555281602d580111811780c0700320850210720743e090140780340520400d041241001c3d03050400518001e0f82e080198919000f915080c03100c03080030740040c0200000b0700035080e007242c0a2500703407207a0a55494034210b05c15 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 435766510 1250 435765260 435765263
    0x902180f03010e01180c06030e120703090b0304050a0203010c0503100b09030a0512040905060a0f150c05010e030a020709060311010807021c030c1704120c051c0306051504050d 77
    0x40c54120003585595080d400030380a21400c500820043d999158283c0f20740b03481400a4601011094002503814001e004041044041e4009098014240c560800032500a004154104811503001090841682c13006501a40c0640002d15034010603104050a5450f5045402c0c1004404c2c0300b44051000e023600d0300820b407682c4071080b07a114000900421303c2c1c8041440c018010744907452038061410700100c02441038928200080c05180c0d00e2400344080d0154500c02c60320345d280c040c03404201e40c10f01c1c0511202c14070403900d446424840c1c81d80b151425107482d508070555540000a0000a035601005068014800729a00384030842c695100c150000e50407a41841c1445510030004140c6071007801291302082e401003c040380d417104280300800070240110600086500d000d82001c0868112141900c501c0e1311102d0400062b81e416812680007a0442c0c04454600c01c4205c0c0740c0d801054030031020f0000c40c00e598009840d80c07411081090341c00700015035214400c0100000d0185444c2d5840b800b800c02d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 435767760 1250 435766510 435766519
    0xb0304051b130f02070606170d030b090403030e0c090a020414040e030d0b0105040b1314040203040209041106090d050c090c12070302090a05060d2421020328020307090218 75
    0x4546440000013a00c10403d000346160300d411008984107403c4285414003000345005c488414002c070506404684005800d20382c44034113040003400080c40307900286c0c40050407105555091031300308003054000000f030341c400e488590003150074040c002e20614885080e010403501813240c3c00d54030048940360b201e00385007440b403643c84918450307190740504211402400503070076040c1d9480c402021050328105030300540c051190040c0c0015001c3c9403030300a41e800b5907001801c503d01078481c4d648800411404d01c1415402c0001031152600c95520100d00781f152501580141010000380801c0000b01c240041c071010031080c052050250703490000d01095070021050400581d12010003001a0404032981c3c00360f540102e00003130b8400313840c0c5180c102d241d600090440c800480d4a00c141101003110b0320b0f000b58465413004040c0c4c491030812040038a15a14005415222018070350200004c031400711015a0410114400c285021400d00304810f000401a903103045042c20104103a07a0008400101081d208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 435769010 1250 435767760 435767771
    0x905010e0607050c060a0f1b021f090812040302091b0d020f0403060204061701292a0610150e10020c0303031303081509012705010b0304051b13 63
    0x20410100840650060700a140311b894000c4900003c01880e00c44070342c2000250310117812840c502c0f201e101001820707801800d1361100c0145c001454010001100c000342088112000020824824010b0524803000084003543c0d9508500500c0001c0384007602075008410b40e14029a40240f1060950740786100d070b943c4c0941e0314004c04418005500868001403c00e81c4005000916030727400a003140c881e4a00d1000d0f01d081c90303903250304291144018001a84440c030305500c0900210910317030000c1082c0240040f100c02e0440171403a244d000b4030040c0c0c2d603092440e4400d07014000c1105480c0d041400404039100c2260001030000c400516200c0c418010500501458911000b010300a01982054107400303000c40380c0300d00d03004d21a07950614100d501500403a0040380828083d2044080350140e40d4400303400c0c044141d18103441010650400021020000241c1078a4180c14032240140c0b8003c14001c8201500d90a041c18150b0420181254403441e1840c1404001c0c5161105c145100d13801e500d40b030300000c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 435770260 1250 435769010 435769013
    0x8030403090e070801030501050a0c0e010c0309030606090509070b0703020c04230a1a030307110d150207030f0809162d0f0602010e16050409140f060402040c0905010e0607 75
    0x11141410b4200c058000e0125080211460740f01c80124100c0e0f0003440248a5511107428507001c0f64084491000014407444002c0502d5025041c0444654803034541440026a04d840e400200c400e103403c60040305441d00203100d003c030f2041140c4800b03414121003452400c20030b69406583d407412107594234003940d01d03203002c41520903c204034030110034481c00440c041c0d0714209094600900c0340e100034840c124070b41d404ca000c01e801d0002c00d469032180d0001988600880e0241000314050441804503650540540b0784260441140007421a4520944500040d0fa5031141c0142030142e004102c07106550014007449c01c0340500b15022000c440c41144039984054038040e0038003802110804403c2c5000545400050a44500c1c10440c2200c00f80d03802049140740701030b8029110710708000701a0340784c034510300c041c8090300c1d0035800340c1003842c818440c0602650040314400c1c2025841c1c0c2080b1000e8200c07000b00400e500b0540144d01c0c48036520f14100742101d00300b4001800490302c50540f940034500c003041510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 435771510 1250 435770260 435770267
    0x102070807060c0b15040507031b090605041a0423040f02030c030a0f020904020408280c0b090406092904061220040912020f011116111309050601081908030403 70
    0x9217200000b600902c4140b820160140c05001103450a140d201201141042139a10511006e000da03071055841c0c43c54546018000c10380303546d007060b000725801801c1000003044020086000381c8101031074400d003007090440042104580704141110703512401001002031340f03800c0400f1a40d000c010044000307800341c606003500f4000c0c020103091507003051000901117960703031002507440d400000e000840c441840300e540d41c0f910b41c401d440000038544482c1001c00d10540c042000500302040c1c014100007640ca50310a0000241e50b1840c45c0782081d44040d10800e101d26025101c410f000010645061003c41d19003180c0850403040c8440203084d80c51703820740381c1113490982030821012080080080c4010780c1c2a05008002002240d0f580015100c1e8078a4880c10300410b0052140c0d01490300045801c11004140c007140d47c00c0101c504660204040012040541d5290742025066a60400000e8412424074003589003200607002051203901c00c00d8078440d140100c00f221300d02da50b40a0751082d100d4480d0f18041c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 435772760 1250 435771510 435771541
    0x80a14031303020139060b100c0b04080708040e0910060e06010516060501080616020a0320031210051c2d0804060302030a06120c0302060a11011a0102070807060c0b 72
    0x3d400710071207010103400402000e520174070501071711080040030046d00c100a00d0055581016000c600b804003c8400300710114a6035900c0360080500c2031404010b0741e9400c2082c1e001e500700c1034007580d4590034040550740800c00301d01c002001d01405c210242c101040e12a54413001070101e41040f9001441080c5101004080d03c1100e500c42824031855844040264a400341100c5148150703d612540c500074a1002900a01c0e441d015203c4840414200102d81d140011010700000d0510007027040030841300c500a0a2440f441c81721100d09469424101042201000107a8146498a50031510804030320404078a1505e0740c011041c64038000f0240ba845403289219200141c10000f020074002844e41e0035400a5205002400707040062070b403036a2400400c840314100180c5030700b041c9801030005090110041c0b1002c141030800c1b49620b036031304151030300b980c4286401403d03110622104103d1960100002d0000d0151f03180a045440d041c1140100120401314001c3c22108444002c90081b48504005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 435774010 1250 435772760 435772817
    0xb011e03051605040b010504180b01030e0a03021609090b01090e0c03060f1504020a170402040f062d051c02060708070605060906030303010501050904090516080a140313030201 77
    0x3078400280b2180c924841d40c2030184103040c040c50805803046101d40c0318a04850036a0b00744000c01d02200e2003410024010000860300c0b905044d40d0704114201c1c0e0a0410a041c8030070320a43c001c0049401104803900e50682540c0311155042c01d0030480000108611480c0e8103442c1c00b103a0029600c02c1e0381e801c1c42d1814aaa0041d16054058002404102003940c0e170403a1190380300d8400342c1442c000c00000d00040f0711034000c901c00091000707901004080e000b4041190001d000800100350403030100d864030708840c060b51181e400c060004260b00d40904111091461004441443c10701513440c03d4085040300c200c01070401e101140011900046540b4402590040d5800c011100e4a031111860400f00608082d58168071406860000600c07600e00041103905a0310306a42e0b9604010100042c0009030100410407602070044411080c200a4401c1c03031800200f81c040c000f41040000c40c10300b039441080350403d069161f0020004017006008c1c00030440226a42840c010362030380c030488007110f60020170030300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 435775260 1250 435774010 435774013
    0xf010f0c0c240606020325030e0f0f1302280e0112020c07180e010b010f110a0f08030708010f05060f071a070f090b070f02101209050604120c0b011e0305 67
    0x207010400030f500102030a100107c64610002e000c580300400c400d0711241c0138009000030a01c0a180b5598141007000d0034062001a2400101c29509030010b44e500300141054121a54049420307000402c40700240c0c1d08080358100d807a01c5030700b03d05100801d442500000681804852408420001001d47c1220312110440e82511920b40c2c41b125500101c03464072031a1006241482e405009030742042c03089100c0d4030416165040203001c442803d59944802c51b0110b862401002e0000010640105100320306030312039442640c0d0780ca00310310040d10b50722060300007422900034043d081c4180d48075082114101c0304060308058644c50130b8681080b0010311090f0104c00460003030184520f207900210b0791079000c0035907101c41d409941c651008040b54041d40d040a410780403a0ba101034098104400381000e072600354070b045281d1543d400000070503254913280c110744907845403041100307000305006075418200051612000d00d40403503d0390642468180607046500c5031032848800f2040c3d80da107142d03000710390100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 435776510 1250 435775260 435775271
    0x90d02060706091a0619050108090c030a05071a030c04050112020d1406120d020309040c02032511010c05150601021c050c0d03020301060c08030907170f010f0c0c24 72
    0x103864125642d00440c429100f5184e0700100e1021b240407000c800b5200d02600703a114200d86080011102600d0181c80c0041c1c034023420219032050384080c408003c40600420050255903c0d00d00c01540384140c1c10007008030071105006003c0c0300181202102d003200d00900e00030112501007040b1307000034441c0801c524012031410086c00c50a504000141c2d21031f074000c88240c61291012100c55440c0c460303500030000142c2080203001c038a0300d07041c0c0c001d4244a400b4030440e41400d011800c02411046543c11400740e402c240702d550030400c040d599039041030550030f01e0002c8014007103545859039807202c40c08201e88801c02500007030b01c0b03074420060021848801c80c44224270125040300a0103940c8000d0507159070b030040c2030110310395034000c3c001c890403141c0d90b982e40e03000c040b096250081c00e5000a04007502c0c90150110005a24451304c94505035490820060400500c2c1500e072a401c441d050940d050080c5e0a1007441e8580582010203003a055070040c034242d0b4400d410358080d100c000e49600c0c0070b8900f9407800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 435777760 1250 435776510 435776513
    0x31504021611010e06031b280507110103021303080706090b0106030b1201050705040e0406020d0f0b040b040b0616080408030316090b0304151d07140301061a090d0206070609 76
    0x48403600c1c0700b45081e200c010b4409101014400303544402ca9a584400c0d241548141c1548001d50041c50080f07400840c0a042420480f401d55580721414a2500040da0105000060001505c0780c1a10301c402420110300e04840700c0890045c2c0f10142c0b1003e004807101203544800d00c1603d4001e40f00080e80301c000d1070b040307684079030002d070003000c0012400b400790030030320b480003408101446103d000e00704985500e8100707450117008000c0b5000062003107a469800784458041c072661030041c0891180c0c10f410100b1280441810b010031a40350051461095042141120480d2548421100b02d40030a031402243c403e444c0c01e00d1802403159901c2080703544000007c0116a2004c2d042d0980a130009503a0703a80015030b1000b124005010545002d072180340c64a40151941405511021044c0d05034a6400b54070600100d00c1810903005502000041c055820010481e00e003c4c0b00e041c0141c0700380c0ea044d281c91200b4618440722401080e1001d4054450001c101c429555000700362103181da40508180900e0044c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 435779010 1250 435777760 435777773
    0x140307020a2a0902160b18060721021c180c030803040c0e0702030d0f1407090905220b070302130807051309050a0f1b08070e0109110315040216 63
    0x1c0d0150321011040341d04000c81e000c40343e802140d01030b481901d51412425101d88a4071280007006d001406c00f44264060b241c441003041c08064410031981d00c40503025079080141ca5680400e20841d4041c29104200f0408002400d001180d180540c04000052034140103a4030586e050360698090304640c0b50718000800c002e2104000e42c4100d2107004c000580715559600d03000f0380d02088e04c80c0005600180180d24043c0f0844e44400c9078805401b0000c5000c0c03130007100921022009489080004a440c038061021011501600c2e40000d041074800d220351102c102d0424041000c450000c00b807001c220046460310340710740c05940c0b24402031480395503555030300d0721600d0b9500258800c041c0101c544000312102a0241d100d101c100c81c2d0401c0c09455001850341c0d60707800e51000c2e140101e50030302c5d119201a1b0008c0704003c000c0090044c1c4001480c030385060062000001c00168002c040140c2441051000303011b104042d260444180b004400c8010880c600003000303805038803d56510751402c0141030702030010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 435780260 1250 435779010 435779063
    0x7120f0e06060a21031d04091505060a080322050405102c1f090507030204061805060f03090708011a0f120601171e07030b0a0507140307020a 62
    0x10440f004200603685410b00c145a031404080264039814484502000c240201c00d03180d2201500c0112810035004980014200d402248060f100018541705e106010001da10819420400031140f0074405464002c0c1c8070750760b1003016000c646030b0800e4a00c3c4115070740600b00780d1000e480003d2044c80513160150018408041e00d01c60000f902613901e21419a0b000c2c502c41005100100a00c61802c581c0c0d00c8406070000403200d0078400400341025000100c480482c0b142500680050b40e015907202c0c5002c000411187c14041d000c0c04042c000001000280ea4a03404c464080c41118030158690341c403045d07010b060485651044a582d401c0501c80d600750000200d03941a401c40072a2030135044c880020030b0019081805184101d0740d80280018401d130f00301d140755188000d000c90112170000381641020400345519104221142d480100140300300310041814a80c010b8103400c00b00400c0c580880018a000408000b48600f240c00102140d4510310920200e181e0070380000382481d140d01c4000d000f018499 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 435781510 1250 435780260 435780271
    0x61302222411060703110c060a0e0d030b0f0108060102150703020a03050a0c0c03030e0307081306030501080a0b15131505030705040c050f0a20010501060f08090607120f0e06 76
    0x1d858202107078403805003030424011060350008110941e140310080c1e000307240d415403002c8000c0c0c0070f10001002d490104000c85c41225591800709404c400307034013528600940180c055082c9800d04020700380b20b072651002090b00880920f00b03043c241d266513005030b08114104250703c48040000c02045600c641503001012045510366040001c0e55030b0710842811203580004103070026410391240c1c2c000c030317120380c0280c462440108182d81c036016450350f0b1035100f9030000342e00d0744a04540c06030030003015800d8032640d8018040307040030346454203480d42c900809600c028800b5070303203030304c4840e80044a48481030b402c0000d9520000030008404180c00c000b58203030151282c1c6100344112580455503007820f0058040310b480d82d0b00d600b410001c221031200740c260856071020041100a01200001501c01207500d0030094100000064035410480010040003007645d0307981c14000480c06102201e50002140c6d90300254078540940204d0340e415544c40900f40c220300104a103410803907625941c4070040749450140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 435782760 1250 435781510 435781559
    0x30f1a01050a080a0f03050409060914010e0103210e1839031803070b070306060509060f0a020114091518120a020304080703230606130222 61
    0x340c0c1d8580401c44406800d000781400340d04400c80000003d5104a1407001c028801d050450409072200401b10403214682d025009007900d030500c0161074000d040042d40981644001c507007032503045440f10b40d01da01c0c841c01e40c000100480134016940700d100354494030a02030000c3c0410400104420100780c1128160b4049000c2004245600341100e1400403002c8041c0880206003070740090254030f480c8a4100504040141c0c5810f00d0076015103074240300900190303100700301d03014250400d484028100c1c1c4181d088203083c0207003003114401d65500c60007515804e00507166a80d61368000c8600403800741c00245102c004401d440000c1c06511078005c6101e414054880c43e40d00f445588a110111601c2aa040f900ca00c50300b0116010308048840c0c4000c2c80c2d8078000740122032805582e081610320702512948140d0b01d206200c1411400301d50950000780703030000300f000104034500f004000a1070b45070100c070105994a40c002031807000054204800745640090302401c6000316503661802682003818040b03024070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 435784010 1250 435782760 435782813
    0xc0908010b0306040201141e041502060c04030c05040c05130308030613051618121109130201141312080309120c12090d050d0e0a0617061504030f 64
    0x1c1d00b0005100c0740300b035405949941460008160f500c0310350f407060410032a0700305280305000002d040080184002e21741240810480501d1000003824000040c0c800010080100402c0010425540202c000e680c0125400034900030b2160051701ca5200b2007071102d8040d01916800424800480c0c081c5100d00c8085d58226199079040448504072041211842c05034600d0b03c07490b59440c0e00c2070b184159800c016015201040d5100c03008035580700e0004104442c0354540be030340c000c40c90402010b00790300034511041c1250303071820990001c1e0444a10b07104500764500080340c3c0110100820002400074026440030410341a0242003444040d0b2044540d03031464400c03a00361136154040d180480e07514a403043c000d0b003d9101c030000f5150300c0b903100360b24250344542da0450782404142d007808424001015030300d03406200401902409105038043c0c1c442c100740203141800c220214001829283e12460855101d00809014000000180660b80000e00b404800d0342860041010174540302076220320907030311142e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 435785260 1250 435784010 435784031
    0x2121f06050703120b04020c03030906370e1c02030408010b0604031a0601020a140d08011514070606120f17031003020d1104180c09060b07021002070503010c090801 72
    0x1114480c0d2440240010541c035800005802154880000105e0040c000361800d81c1610b921450350300103690900043d0088020302001c11558514441c1400c81c0c1d40a010000c454049010000d14240003051101900c03511142d100d0b400601c4103400d000f03084034644107140c3c9000b00003544e0790051f0180040319864148a02d0403840c281081c2ca04913544100b0002ca0b03949400ca04180e40f440280001d410351150070103c0f00040d0310103112250054904d8018003c003000c11b0f400408180060348513034550b1003040e1841c60f010342c2c80925100498000600190744d15180d1801d40001c00c0c065000041003140300780350408002c040903000390700c00c1c0501602240c4400c00e0030010311522007a1050984800350700c104100504242c642c0c192928095100201540119030216050384c07903025064a1500f0031000500802c584e03d4186801360103003070400c00440b802c0c0341613803505100b4814040e104040307144c10103084504c200140d00242c10061b009024802c00060068501d0205006506003942012407840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 435786510 1250 435785260 435785267
    0x14010905060307030509120301062f1e100908030a0c030504031d011e020c0108150303040303081314031905070203060c09061e1803030901140f070609050307050610030f060f02121f06 80
    0x1035101c4810f1001d486070cc0c0000c1b190030000f01481111020501403480c3d810a904501d100d1514a00d0081c15582d540385890b42d010400c41d1151000602490310300340521022a500085180146180e003120f0340010403000c0050302d00003102d500003000420045036030340f00b882c0d0100c0c280166000a8a403080c07a6110408107044a08882d0001c50f0075900c10311041011034443c2108a42103a808402001d402a10b9111040f40c61149561102035510005006080c0800100303540c0003c40545030041c01c02c18290b0000b500c4441c05420444d0010300881c2d0450340f03948480032a444442c505420700304218200c00b80c1e903015080060b12486084c5907122003546410040121012104143c1da50740c84080c541280b145103400ca0f041000b8045000e20100000403204d20540c0041e9014600550f00c072482803808618003003008002c504000a420360410010b80032046041c40d05034420404900c03580e55565110003802400300008400001a0500c8180e41d000c00300c540188080200d49c4103201d40302c81058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 435787760 1250 435786510 435786587
    0x5120406061e24091203020c010f0e0307030b0a0b031605090a020414010c0c1205030301050906030a0312020307021903050d0c110a061503080f041401090506030703050912030106 78
    0x16030040d40380d52415000741c8400b000403040840e041c0f10013001c0d151a00a024424100e4040f800369001403d400d85640c0c001500c7e509040188c0b505088044011002c42e44400b1301e0712005180001d2000482c4031540e098021280c40640502140c4112a5203481103c510465100300790081c1d007403a001c00d150503580d00894050310b26030214140120300380001100c41d80304d00e800c25500c03140d40c1c130400304044060010030003269001d18020f503280d5042408008242001074407041c0b003130b03110222000000b90010118265071240307240050301c0e5510044281e0a211100060042c0401d4144d403c400305500080902218000090101321982040c4400c0d20300038225018410f0035800864600002074203900910a59840800150080c1340c6d607030b03109412034100d8500946421800f2038180041012941e10741c1e1141400d181100300a450600861040e10002c3c040d030040540300c05c00500c48020410942c03130f66030200801242d40f50b035680f0000300402415440f07590b01b040ba00c04281d1001171942c451 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 435789010 1250 435787760 435787769
    0x30309151308030412170c1909050a0906091d0c0d06060302041b11010605030618070306020c0c011419050705010b030706031d0c1011070b0309011a0315060f0105120406061e 76
    0x700f448c1003000004410810240c00704501001000317075000c2200c3c0c84a01c040002010f04078400325901c1e0400ca4020103071000c02815003010754030300c141a80307460300000d201c2d000540261000f42d4529628100140505900d400c06074019040c02c00480810302c00c00009811140d00740e440c07410a114a0328a0390a1324003510802d58540e2000e004100050110300303c0301c54201c03144086504056607580d846090ba0401c051340006030700411540341e03003942c1050300052012440b0043d98642030a0121040c0745109038a9140d003002001b03c2c03c6070412900b540031552002000f022244075a07910207000303001c1c0040c072209444030101840c100380b659a00013481183da80d0000c21705103543c095454102d070f0321542c00701c0608280c0f0510000050305928007008500500300da80002c074002d400320074500805d20078203800074040d40c0302c504400403200100c10718903004030049440701411111400107c8240c050110b18142040a00707050008012469000d041243c410024001015403642004450311105205 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 435790260 1250 435789010 435789031
    0xb041503020114070b090703020a080a03140d0207241508060c0708070209040b1006050f071b080d081b0406051606110301032303030915130803041217 66
    0x909000540c0100940701c1c594107210380a50803d4103e8540c1d00a5110944054160303070030101e0b0503c250b0a101d8894000b4216000003030401040740d9030010041400c3c1d9850303203005400421080c03029103e503012a102640c1000f103502c444181844912611810000307044030180c03030040b0302c9480c42036040240d000c0703841100261030b2039922000801c4041d0711104044414020801003070740182e66544240b4003d5015012625562031320018401d50791f00303543c0020044c080180007103004015510120b944407075100b044106408820300005042200300e410940560041e000365000c15680b00203054070a00c1d1800482c000c00e20101050080d81c03085000d03060024074208188226480250341c3c01d90050700c2800c1c0090218005040d1060a030001c0c0c0045134104021070003104490314100e514a15144c0e4417010354510b081c02c80d1184c1e5940035074040040c80c22000e40010340d406031100c0c500300c445608020442d07603038505440c1c103400000b0380401500214105000d6000c01c2e10100f450148074081c1184e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 435791366 1106 435790260 435790301
    0x50312180d0609291324020c0c0a0f0501090512120f0d050a0c081812041e0b1e0711040903020309030c03030c2104120b06040b04 57
    0x800f07080c083d0f0034403410f00401403194800d420803594449191703070401b0041458040f032480c524003141d4a4510102c1d549204120101c0e1450200c0350859560100b1503c03040c031200000041c1c0650b42c005514404140400e051427644004c000c0c9081d030840302da0980000400301c43e54046850b10114074808a80101103080301d0140d01d802503c0b0b440144000307174040000410480300145141240031a40d40f1324035003950180010b0aa01d80c9000130b441da01d98407504000c4006080240c10030b03155101c54800100789501806950b0000301d003400200e030514079940f5020403070b0061501a2542800b00c0d044075407a5807a4414104a01d100340c02a544804d840000c06040900c102c00341c0b4000c2c2c00c20405a04071001c0070848841d040304540300001c080d14100340481141c002e5410a08640864560910602c10000d14291040c5012141030040c40500c6042c0000e41d41c126492070070000210 = true := by decide +kernel

theorem cover : BRFrame.Cov 435611510 435791366 := by
  have h0 := BRFrame.cov_init 435611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 435611510 ≤ n) (h2 : n < 435791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
