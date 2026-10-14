-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1784
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:39:48.515509+00:00
-- url     : https://prove2.me/submissions/9d2b0ea3-9eff-42be-a1da-32e0e855e69e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 320683453 ≤ n < 320863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 320684703 1250 320683453 320683459
    0x6070f081b0f0601030b071b1202010b0d0b0105100201020403050319020a0206040b070b0105010212040b0904020412050a031707120b0a0b0a03020903060a0b0307051003062c0603060103110607060e011a 88
    0x6000610241c03046502303401c000c020b90300a000c00000c41c2c8510110048040b2540155980c03800410201e58034603407100640c0d841580b00e02101c3d0704040510022201d00c0702c9403003d581c0184400c0c170016101105595039201078075820f100100a03804100e00d0301891402c080d40041001402003400101031005180c03003030040312001c00070b990707132401240c0e02c0180d81c0b81c5401e01c090500082c4011074600c00117040d1608010005401c02d0f40303e041d140d440c1071604004407600e03445000c40504050304819244034220f22240900040e18080002030007030130044aa0b1b02410f65500c0300b10a4595030030500c01c010305032640241e0303268044440c0181c02035202604ca14440d204540c00a0185005802030310001d00b03014001c2d1003a40c0c0b8200c04d008a00086070500018543c44c2d06000c11248500c0b4184101c90707159000f00d4083c1b04881c9090050b204020382098065080100180701141c0340304100c220b1000c0644219589030200d0401e5001006004501c0c540c0d542407003000d01700520403500e44c0015050072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 320685953 1250 320684703 320684723
    0x602071a0c09150903030301170708060103030e10020f0a0b0a18150c091a03070306060509030c090703110c06070e09071b0201030908030906010905010506070f081b0f060103 76
    0x14040c04812044684500704401040805224201006084045203d0144103414101150700182c00c5410907040f0201c8945200b081c2a0107600421000307009103201c0b400f610440d4150b4400505141003001d9440c0110410f20070100307014401c0010b007242c580a070302660112100381c9401f03a0301503401d581c01b009035428100c0700500410f4481c01c0682031039010f40c2c603541d6120810040c4003e4044104000306001d8650f00004100c0c44021038048425280800340b541c81c680488040d044401c3c640090f41044010f00c001441034900140c603002c660300c11687d0034403d5403203d408402802c048a1b0452240801040041040100260355070052009131680e880c2e01c4c2a003000e1003c4a003040303a0400000d614800380090034a400c11150500600614001c2400d465a44440f10580d0068540c0c11469001000400c41c0b0583c0d8420ba40c05450708a070020318004403601d07a07580b01000f00c90b01500562001a01c2070707000c0e01e10340350940c00d84450400d42e0700c5424a0040d440d00c8020920041d24801d0389 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 320687203 1250 320685953 320685983
    0x60e0f04020714010c090503150619080f01060f1415090d0f0c1505040915030b0c0a020f16031707020a12030305060607120e03010f0513051006050a06050d0b0a03060207 74
    0xf946d50205440c1c02900505245001c194080214074010704000d8014032040009840b0600002c6c41c44050800d850080034004005030200e030071242564005540441a240140020000f40010139640d450450310301208060954500007248901f4640305da210b0a0004103104014140c00a202c000303010b07422040f4226529112850307030080b807030381200015504000078860240541e00c540801c0542d8107441c0e070f03c0c42d2a9070325201070000989400100c0880824822503569040104441a62841d03028100000503c600c40c000c0141a0000502a5000e40c1440c442e5050010913a00d019800814541d1080d607144c05080b82d5a0326a41d09500003800c0400013800e504109085480f00c0d40d00c102d0440015840000403592142180041d40c0d065403101a4410011250f0180074000e0211000c4001c0c285130f1850700500d0414151071861241d0b00380311041085030f503401c000d44102e42407400d1a50356030303184001000080030011280381d4086520b00001c000e2040507405032564034416644100100300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 320688453 1250 320687203 320687207
    0x16030311071e0303060302101d01020d051804020f070c060906051305040203070c21020706170c03040302160e0105010801140f040f0b0301060e0a060b0c07060e0f04020714010c 77
    0x1c520040940300072070300d091000c070b4500000c02c030210041c060701d0300180d100e45960008201001c182018400640181c40c07a5041e90650441d81c10959030074001020311000c14140a440f50160f00010b80c80520340c0d408030002502c440c0c040f1151180f420b1240c03551110f15140407054007a00b8040c07a800290021804074820b40120110761031a10940c1301c0d000300c07034508410000a075100400700420013000300200f00001e0089070781c210784548500891600300c15500c400a14090160340001e0421003010120f08a2000f42c00410350000c03600c500d81da035290341d6801d09034600680c0401081d00c5080c000e00c00514040b03c070440780d05a681c03da80d03481143c0d0342c540f0300070340c40080000040d501c4044005112407501d40ba6000504034041118040b8030081001c002030700b102c81961044050204907000c0180d8103030a440f40901400308440d0707240c103000c401a51076960303001e44c0c041d01d01409840f103020085962000d01d842d91103075005000359520b49281c23810201c441c0c0d0018100303a030f030b600700300c85210618 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 320689703 1250 320688453 320688457
    0x6030c050109140906151201030224090d0804120c082b08070908070b07050f2b05120705130f06020d0804141218030a032705040216030311 61
    0x41c00ba42020486003410303100300500c2000140c01c0d164091448000743e800074026002804070410134100388109507140d4012f22080081040e28a0020f0940071640d010a0516509131000d661003074500700762a481c41d01d04080588584d8109100e10a0607001031005c0201d0a0300500981d81c200003038076003141c0c1109a6004490004607030084c001c825151811001e489001038031761108561405d1030b44a0380e14400e10b0b0601c3c200c2d400c080c0b03100c0800521501480070800c60101301a271400011f0000000710603001041074255050151240300b25503088000512440a85142e4211011a11020305142d000540aa480030303007201c91800c0300d40400074410b01076036001d8085030482c0d0040c09028802e070700c04581c143ca0040c8101c450320000e400104070000200080c0c846030b040301c108aa602c04180083e407402c0d50300c0c2c112040c46940a0054900000d5000d00c26400e814080c24002401e4079607201e4011002110781c102581083c40031030300c000c44021915449070410f000741c0f01000304041410001c0301c14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 320690953 1250 320689703 320689709
    0x3030905030a031d01271406030609070503040602090907110f07031e0312021303020901091a060306130504050c10020106050f060903030f0d050402090a0912110f0a0606030c050109 79
    0x2080494042400095040b10321800c84d0701d05141070b01c0c40101c81c945008110071104407480a4840b00c0605211244486009000010084070f5441c21031178048001941420700601c4076040080c00300108040203215010b40f0f540c80401021141e9503c6c1c280d00c0180402c2600108c0401841240001e0702030210200d02502a80e400c1a0005400700ca1000000820030680c40220100b02c080d08030150b0458052001d800030300c890b200020075a44c618010064a00b00680105055a140c5400052060f040d0310003107400d114140c82c115129910f000002d4080a00c031500e05034a14109030410041040c08140c0440d10071040702c20b030315103880807a0203d080340e402e40a4190409244505001ca502d01407000c0c211110b0001c045928020b1007262402080c0c01c6040e9083e501d5840d10207101c114070f420494181e100d03400710400c0000010720f03141d5044603021200000c007400526002001c414405200144924424a04036070302c680c1c1910b4220020806c5100030b0359112840b400c042155032041c0080170131 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 320692203 1250 320690953 320690957
    0x71b020310050c07020d061505030d0c030c060b04050f04120c05060112020a1d060f040b060d0b0406080a2a0509040602370f030b0604030f020604030512030103030905030a03 76
    0x2060110740036001402c010b02094061034041c0004030040c1e80300c01500d0b00c0c0d1445581c000c00d5002c0181d5041100c0105504003a10a402011404501c982d101d1400c142d11074252801600840403400c00744024841c4043c1c558103d802e02080200c400c0d0070002c06400b50340b05217400030104501e90012262400744003c018540d422650041105000c2c444515042c10300080c05010318603603a10002e035a1000c1b0000c000c40311307080742c000c02c1441c0c80c00403405130100d01c06840c10710010316000005042442040941051599101c038060587d80b9a6404a4068090b6008a0341c1c07060f55420100c6041ea648540b0b502504c3c07e4100081b01c0c1c074400c1c2c5101e402c845010f42200103d0320b6990380c1c030010750001c06200c81030000c080f44001142c0321800704202e102428600304030903850603140081405104060345011303d402c1c6a0484081e0312070500301c0781101e8004900c3c4040b51400d1000a50034401e55002034118132890742803009658101004504803031203038440141195981061584130011300d080600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 320693453 1250 320692203 320692213
    0xc030c0e01093f05060403020709060b03070807031116020405010f03020d02150702150d0e0f060c070c0e010b091806180a1805010e100b060d020a0c0606030803071b0203 74
    0x42d1039050b425861035082600350f09144402c1155601c5401d401440209403403d91003502804185901070042c207000d02146d04061000394100300801c03005200c007a007010f0400440360002002184240c0c40840f2600702080d0b016580c254041d001a03440043c2001a40310390302e41000019100c190300f4064040307950183c091005400280c00300070000c80b2085c144000c4407002c00c1004016600e200c4503032200240060703d00d4881d0003a0944104482042d1314080581d403064010544412002807100c0c0d0240d03c00700000d554050705d283c6a8165001d03684111501d00d440c3c40042101c645010240c5200001514450552010881c1510070b00d501521001d801450781d182007003110071603000131a4030168181010030a200000c14008012150300d40644d0740740d43d5000e10250080050042c181420340003001481820350080c000b50360343c8034050080c00c0c85640082c0351b1685a0146a00c50f0407030350021010441c041d07507401c0100d59944200c0d110000250940b403000307026422410303105d1b001a0050000d01e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 320694703 1250 320693453 320693489
    0x4030f02070b130e04080c01050c040603050a020903150c041805010602120a090515070209040302010903030b040c080f040c171b040207110f0a170c090702030c060a0f0207060c030c0e0109 82
    0x7a1084d0700036109460a80d002c11150206010900440d8010000c481120390340314a800d0005048480190404050b6401080220007951340003460100e10800c102100700e6a44445000a50510441e07200300209a02c0c100c0407680c0200c65070002d4101e0f0950340a0319685003802440284a12950450101040d548c132001c0c0450300304010105c409500e098041403070011ba80d0001400ca02c41240c007200142e44900c01c6000b09a458041c0084001064806120345600c2200141103040000c00c80074440c0300302c100203030a000a00c21200001c08000c0f06650111822002403030300c8441050000e6541951560040014105807003214440d035048041048082d543d03000b000344210000424a611090764040814a144d503424003000c180c1d0750600821003044030310700713106066800074401c0042d90010303c00d40840b040007140705030380f24200782d10018401c2c0311100304030007e010f075080103000d8526103800c0300002030301507214108071a40341c1c880070041401040111510301450049540c2c00d00301041c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 320695953 1250 320694703 320694719
    0xa0b040b0703020a080c031c0e0c010809100645020a03060510090806130f030f11060c0403060e0a12030c1202030c0901110606060a11030c0604030f02070b13 69
    0x9401c000b8868419200500569204c00c1482d811400070740b0840c1d040001e01d9020031102d52a13420101080460a001c1440c42e611070b2a100d100509a25050010f81e5000a804003024080b40c0840c5d04403010400285850302c0071600380701c034203031107100b0b002c1c8201d00701350145490a90040140ca100969414443c16254088006500402e010300700f81510392002007115520080c07103400c0d24095540e0009a6441c10b083d03e850560003400c0b6a235000f41c0c1c0640140402c2809203948000c0e074041c00c1074025029900821241c0000c2e481000c8028002c640a0111001070040240110390203030600f07000c000b64104519895050342d54006007908285100007002d58000c0d00714042c1c404060500d4620f602248200d43c0580e401104c1c0060101000140c0420541e04200c03209500c8140c940105818601100031449038031504011809120603040201c800c140c082040310904041c2c54142c8a250401d4540038041802c41c018030b40240c007032210302142185500081c1c0b0388181c800440804481e10f051301c0c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 320697203 1250 320695953 320695957
    0x10515091f180504060509040327090b0a0806070e091902030c040e0f040f060f090203030a0f0809030a0503010315060803041502071a070605150301060807050f0a0b040b 74
    0x1401d8015a4901d4018000704070702900c0c01520441d510740380c031540da5005041905075040c2d00718034403940c90408288036035110140d01d00d40c807507894100903100d00c05202042e40c803404020310600e200e103c0f050020409080c030ba000315054510507103a030081142c44040154072414111800c000049200c540c0040510740008078513086404461019030140c4901e00000a030303401203526481c13010380003808112448002500c59808502000b0050443c101590303684804440300801410081c0c440c00c2800324006540e0001c51210382c0201101c0da04c0390032550140000d4280b10b92000403034103190000b40c1c502c0010040311201c104581c0c0f001d10b960b0035035494200e800c0141080c03480c1c4507a10107000c1140d210400040004d400d08038021240100003140080c60901c40b500140c401c2216000c4411402140c00d003911021030f44801c000c952030340c03400c14007184003a1000346140c1c190f0801000080c0c1d000003090007400c1c0c1e502070300c03600510104501401420742c401c2c810800d80d0070007000308208070003410340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 320698453 1250 320697203 320697217
    0x80307030c0303020c19050f0c1c0503040522050a0c1b1403120103050c0a060f030b030a08030a090b0a05070503060d240f0b040c0806040216020901030302061e010515 73
    0xe005003490121031049151803c86e09100482008003c2d8180500604000120040154030001e154003003480000c03c6c0e481c0300c00600e200c3c00302601203100b4200102802503802422016190305071003150030314002da00064101940c4440d52609020529146160040807886d404584038901032a00d0303d080c480300d42c0503d030400e1310f10685038110701d00d107184d05000420b0140d415110000d03080d411030400a0a095012404038424401c981c0100701d000d4118281052080d9241000199004000e01083c10700c01c0c5038100400c2c0c1100081007000d03401c800e900040c000c41c090b54040e00300395192041201210015549000441d0050001030030510301030903100320003481420003040490075800c0c0d800101004050444c1d00f5a22012005e40310074180c4101244040300706c500384507407410848042c04203c0c01400b07481c0a00e400041c8000c100c0d036840280003105901a241c84c102d90394a0500a440340010740b03902c1160348140050940541d51244c86c54140d03107005262013440310b070720303a450b030700541c0141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 320699703 1250 320698453 320698457
    0x108040b220b01060e0111010603150c03150611010b03010b130902012a03030506010507210207030c0e0708011a09040f140406050403090512032709130b0a06080307030c03 75
    0x403040c0381c00900520744080c024113090716842c000e00700e000009000c803982c120360072805a15040007080494400703c9051003501c840f440006600c103541d01c00b10007a01d0084450300120715400e000081d000c1e8080002040e602003400204030180750202090309070b5081004043d8840d142d01d07241a651403a640c4540386407481410700300d449208040d00705494004182ca11440c81002d07113110014141c2601640d0360042e42460824546000c0d6a0f584032851121002d107a84420702154078441180208002400b45421041041d01d880c1d41e0485640030076004c856440019a90100002d10301000c0c1c42850710003820074010909000700842030200078405008501071171903d91600000e400c0140d50704501882c0a01004a000e241174203000d012030307855a02c900d0180f0200c0241c8010744201109948103101a4216100c640c3c40e540b01d8003007001520001541c1c400002c40c107101d81c400709411a084040d200d0030844920740c4c2c40c040c40d5811204648505036043e082044a940064030820a000e5030078424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 320700953 1250 320699703 320699761
    0x82a0f0a09020309150c160204060b070b0406180f1e0f0b060906190e1003060e0f12040e07030207031107060906030f020c0705010c050a150b010e0108040b 68
    0x500000e40021039540704064003940002480703030011041c841020900c0d0000a07981203030800c1c05072401280308008251991001c9410024119036458000380000c00b100b0318015141e00003030601c04078110040d501150502d00d07001d800150b80200003c14603100d50880d070310090f4945580c41c0c0d01c07011403e011b514142c500c0b18a00040c00940081000c0c0c040a00950101200b8509a0140b08407000007400051050566220311480c580100003030006440b40c415115000d612501c560400070300e09600010225400c00200140b88000000d41d064402d04200454100203250745000c581c2c1d1045010742c1c80a80101e200089803140660010820701d4440d1410907006c100750a1010b0070105103401580015030210010000310b640750007807480c0744050340b004610308120300f10800c4c0c0c0c990303080c400c4a05100d84c12254900380001413100d0350f8016004500581c8406e10250400018520070300c1c1c00c4d02081e0201e0b2158120f51144c06410301c07039648002105c01c00d0302c2e035400e03017130195100b0005e000e03a100e41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 320702203 1250 320700953 320700979
    0x20106120b0c0c030d050106030902010806032109011407050105060a0608060303030403050309190602040906050604080304260303070903170a080a240f030201030b0d11090711010e0f0106082a 84
    0x10742c1b1800e4001c0c00f00d941c0c0000d070f4001c00d100041003a4409002103201390f0100c00d4100e40d18205201c8a44d11020101c4410b50703038805080141c0b08542655408007540b20041200001c3c00300640184c3e228100072140c2e803156075190b003003c2e80c2641060765081d8240e84140002400203018400440c0c11920f0041110021860449400390b04000c00801305d400075008113042286607428020b50000e003400321402401c00d4107085400c1d5072400745205010303d098180078200c42039482c152948408201d5001641d580e0301e00203002a003049100d20080b25900c4c40340c0401804074004006071a5402900e544800094440ca030144003d02955103018240b00d54020900b040030080031508030090441d01d140d0103200707255000140440340112000d500982d559521400020074400d00b1090501045400b99503075100c000e0211903560201280d40319542c0f809040c03004100c40052514042d045c0a4003d0000030340b940d060584403030b1007840d8000984904030802401040240542e805050054401c2003c800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 320703453 1250 320702203 320702227
    0x604020f010e1f0206010b0c100203101d010305210d150b1201081b03060a090c0b16150e0a030e2403100e0105010801060c0606050310020a020106120b0c0c03 69
    0x4810320b03846035652903030f20301400c0c039010b10683e8010401e40181d541007032412116103840e00c032450407100240d236001001030034061190078008090511500c0700202400c4812580c00320460a00003540d4610070f5001c04c612050340011300c0307144803401806460910005000c00d00180445105010b010301c207e100c0442c040040c030014142018681c01e08403255407504c001142025000c0520031150280c040d0051001d4030300280e803a8015940c00c0001030080c1d09420044c41c4201d440c6c00078075020500041c5c416513051041c16600106000f103808d20017041d4821041c074101e0300310030b25401542d005000840d0100b4050181030000c0c44001c1c0181180807031340751110754820380c600a40703c8051004070a01c00f45000c41e40c010000f8180c14600103000c0c0d41854001703044800144605010800201c0e110405c00180f5041071004103005000c0320300031020700c042c0e10003035000000c44200641c41c155000809800b10040d1158042d0065000411a1508040008a58001500003125100400c11002908 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 320704703 1250 320703453 320703469
    0x250302010608010c02010906050c0c0d1b0c12060b0109050a050103020702030c061204030f0f02030909060414010311120c1c02030f060f0a0609140114031002070809030115080604020f010e 82
    0x1c844d80c1c00081e0484452526900f100d102800555101d5014050f8100e01580040c641c0e55031407450070125a15400c03030f4654040508039000043c518400b40760006018480244001a40c601c10a801d011030310b46200111580c0100e0f1142603403100454404010550107640180b40c0c05c0e0003d4181c48408440317201140e810381c400d81c1c907034060801020801c0280b591090402c1c680202e40c1c5441144000b44a00c000c4d502d000d0921410701c40c00c400c00110324190741c1c1d544400c800c0701c1e4030384444c4104d607500e052090640204050260003aa01c0102520412402046a80040301d0007000d0000c8131044c1c01400c8628900564120f0701345c1705041d081c40c9100d004020a40c070843d005642e002d0189481182c03501902c20f1680420a00341c10211001c42484511040d01c0c190380d43c0c00d0080407001010702c0002c1c170384800b021110794203074800203005082c011144014106102c00740c000784182001e0311140ea0384800c0901c40c04007141c000d60041360051510b6211000903023414500b07010b8102102000503245 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 320705953 1250 320704703 320704721
    0x90b0f100e1c020109061701060810030609060b090a060501050d0b060705031204030e0d020906280e04060b0306010b070b0c120705030708010503060618040816080d06050625030201060801 82
    0x500e0740b1810108641e801828440507100c00c1c600000d8800020b01d85c07800c040c406009100c1032052900c000b0780701e01c00c0e0b5801035000b1030704014207001c40c0d4294102000149003001e0298011404000090001f18242c0610412160180c1d00c580c0340800c064801d00082244a082c030354407540802640000c504208050603a52110010080700350a081ca0080c0c10240340c1c00c4228000d801c1885240090b9850b5031030780f6030040d4280c0c2d020f01c0c060002951f2070030b94501c4079840b090704c0309940350106520a1202c00d452180b8405c01c401c01080c0b03c030000301036440e50244a9107100306010810040001d0000c9501034000f126645001d0a00c01e007184200c1c0750000c100c0300c0d01c0000b80080200261254080782090042005501030f02480c2030410124500a07540c400d140e002c8030121000c81d08000a290840343c40440004a240309070741d00d40740c04d1886900c01c00394181c0e001c0c10041c0128881c40e1840c12a124407025101e29003e082980640e00010180008203600b50f5584d8080020075400c01e008884031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 320707203 1250 320705953 320705989
    0x4090606030c0e1308030114030f060a0903120504050309192103030f0509033f100e0702030304030f03090501050c1b01110a05161202060709090b0f100e 67
    0x4034a082648a000e8210f00921049a200804a5000c0418004000ca9056510100c40400c90882c014003003441c0c07003001952a4080c3c401c20b0100702c3d1710b41050340b041c1c440610940d1150340c2d0241c04400c00741a82c0302510041c1113134004004510072840c1a000c10102d064002d5540e0003115526060740031600030307548035810322280c0500150700301030b4540f1442c1c9001801075010409820705d800b4144da44d003e004154103524005022640b0580030f10001c10321144524080d041d29070303100d401c030700141d000180c92200e074440c85480c011880c02e140310001c2e441101c89038025411645c2d940c030110744040d045c050301e005145d42d410300000410400c0c01400d204944140a190b580d8884000c414003104610314030100310f0340b405c140b040041c80c1000481d13520745c0c00c602c0d206032110519081041c010418060080c018902e6002400c40c10ba00030424500c1071125444110f00d45903500602c03001d0740e86c07000440d41d0111303007190070359170500d461030300d0412070140e40c81d05401c1c4043c40ca01007480c0c0942a848011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 320708453 1250 320707203 320707223
    0x15020318040e0f151b0a080402012f030d0e03040303020604020d14010c08090c10023304060c02011a06070201110f0d0e0306060103060b0f0a03021e030f0f060d08090409060603 77
    0x19220481c0104201250145d115140c904032a2030381c01000300784041c0000341003000f0314a00c860308a100043c0c80441d00084d54003201c04802c90011303686d0300c0e80198981c202140c203001c410440e0796404010340c0c08881c1c00d6006484d2503a107550800400d0350203690f04450010076500030051041003485a101c07050110b46030f0303070301c18181120554505601c20b0022441001b0f00840e28090560101b802281a081c101d80c030a40b030b4600b5601c40c0402c0000540c01c002540aa400300814040e0b690402c8083c0c12a58008001c0d003c04ea5a025264215540c001034018104110f9400194481c1140050231420441941c0141e494030300d0071800c1842403c0444005201d101008075070345814800c042c1c000c4c2c0f003424100302c100c0ca0712902c0b5030a80680300c004400040d0201c3d2040ca0316002e82c040310710500d410f4039414600c400101d12984c07035400a903404030040c0340003000100f0310071403218100d006a40091011001c3c401d030743e541d00c1132130b803200710034070b42083d15021a100003444c54090500654450030000d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 320709703 1250 320708453 320708461
    0x3030429180c100905010e0d0f0b150a050f0621100e0a05090a080d02040b03010f09050f07210615050703140301030309360615020318040e0f15 63
    0x2070301d0b00d0449a9001d2080303104403d4400d8958102c40c4004c12207200b8248a4805020b400000702110382c000c1000c1d05040f4608012802c005050032864414000b00c0b004c0d016880d07501c400d00211011070b00885030040b890b600268a00d01c6c00401402122115124a510b070740825a04038040d400151620340203404940380c24070a05490103051030f030054504104024070700d07101001a42d108800b01c00600340030b038006145a01101d503a01280e000e40041200a6034070b5a55071143c4280d20485d1241c0e206681c58030001c919406c611144c1786010b20500e40d43d45c40d4a00c00c050710540f10350303440c1942c128020b65903500010b03d620070100c98030706a26541c644a4a0b15001d04003d08084014604559411710801c010310000c1e03040300809096800d8849000d0340c5003482058400300003010303480980c443d01102c10040b144103203078100d00240c880015810a92809400003a6a80d00074089110182450079440074007900700b9a00c4110104000341c02c4030f03d000c200101d00c84c1040d0b241083c0390507001c0241c0400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 320710953 1250 320709703 320709751
    0x2060a1e1406031b0904080703090b03010b030105011205070c031b14010209010f0908030712051b16080d230405090c03070305010e010b030f060105040f090516030e03030429 76
    0x80d0300018100d40d03100c4d0704000100c002840d5207000400051801c03002045110500d442410660098010a4901681c03941c484a401006030001d200e4035002418045071a04211128081c0500510386512901c08044555400351142c01e21502000c4d808840700310707018086400703140c0c0034800d07136243c000060740c1e0968074000401e481034464160080c04100c40e010050f20384000116501a5001861440c083c05405000c482c540301d003030b85070400440850382522203e000845c0c400c001d101464803d03008207547e032403159202c1485c15a2a801300e50b10300f09049145c08206c7d800164580340f0142a45030a844400041c0c41e00b000b0f40c3e8406a6460100030807282903094403c4d980074140352a080045503152100010451000a144856041440000c28540d0340240299406880c00703181500e000b82d2107211040003080222007001d41503145035044c00c0c400c0e0080c40f48140c035030710344000b07145155903586440250440a040641c41540b601d01c3e40e8000c40d002e4040580204408203960707014090b100c0071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 320712203 1250 320710953 320710963
    0x30e0f1006140d20040b090702030c0708190201120f0908070c060813141513060b0a03020a050603040c0306090803070e01020d0f0e0a09141609030302060a1e140603 72
    0x19014000c040c0b000390104e00d000c40c9000300000340c040036104407109280460040c041810700260410311880074440c0040c1c02001078561000308a084958041d9901c18070fa03034448000500d20800381842c0d41101c01f6503c1407842940310294442c1c045903c1c100c40302c03501c08507101180c055512882c0070030200b04100015145000504407460054094140388a000c1c0204c5c07030000700106001c0000c5131883d50318500f84001140c0c1b800070205060b00b07152201020302e10740f0400104490341c0e0302e0510760702d40c1443e0614204040c1c0f5009002c5503904c5003441e0034806143d20241042c3c461507202680003000560781d0098000d4684940303100e0b5128140390001410380501000d0b040c0c19904030344407000515501820010a103252443e00c40c000381c85800204d425107e1682003450b02c0c1c1e08065420721106018100c00f8000d94001314022040c4a010404803a45540341c00000d00503000440440c0c9820b8240d084640e00b6001e4006e03000c1c050300f000041c142102c00f001036202140490400b0888986820f01c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 320713453 1250 320712203 320712239
    0x203030c07270c090501030f09021f02010c020105040507090c020327310f110309010606090b040f0b0901051606060810020c07090203070314040c1a0f0a030e0f1006 72
    0x1030000c83d11914024000510318081e9504155407420079150100213500320341350b41d43d0040e08900007446003540c070b00c0380500300382c01180156003402ca00348038103881449601d1085130802c001c2e1048500704040000038042c032a040300114482444100398540310a16000300709103116100c03179104598103081c030410300060791b1034000001114150090040c1c0c00c08000d8622000d1600004407482001c0d40300d0700030000d04081284400c408410484004015401901a01e85e1074842d010010b5441c1041030140c491130103400a40d02d184201000f001640d40050200444141000c40c28081c6001d402c0080c20003031481542d4013601e482081005107410301240901d120103075029454111166552617440000f4424441d41c4e590000003e410b1703c6c172a074001d8904500450040980b4142401c0101249030240150f100705804956040403492400e0b0403150340e590035484841c240301c0746540990091041c2420600f0a004040360108185d60600080c1d0811310420030000310507003403180003030f0440240c070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 320714703 1250 320713453 320713529
    0x7051005070c030e01050d0618060f0b0a030f0b06030910050c04050303160219080607030b09040f1e0803010602070f15021f020c010501120209071d010c0203030c07 72
    0x103018414459030002c400301200b901800e0401c0e04c0c002050049985100e540200140c507440e03e1004140000f226004200b001c1e40441d040c8550303615641c1181c1040b183c3c1c0725013038004004110010302c5501a822106a5454042c5c000403408041c2e800710340c035035004842c154021b8120445604440e0414800d5641121114030310030708113400c200200e0791300c0c031a9024441c400801c595001d8115594101a4028004c0d0310000c581995580d981c6548d031184140c4204000c0b1341004640788279420038001481c412900308400500002c041d80b29600009a910426240c41008a54a8010074400c000450080800b40c0c01030100d10718060104040390159004600304031070510f00079a07801d80c000f41e0710501c074a20a034920420800411a04004c0c030400d900c100d190350030030f00000740700190b1041500026000340e40f2040c159854076402c41c2c100d05030846000d03042c1c290025a01d0203502c52401890134500c050304807032070640c140d5021481c029065000e5021407440792109414030480c0d00034208810108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 320715953 1250 320714703 320714711
    0x110910080702070b1806071406010b03040309030b1e04082101120b06030f070b211603020c0a1b1409070212070c05040c09030c0b0403020307050411120705070510 71
    0x207400000e4a89a80703100d5118031110105048800d040d1000010b455580c00601c1d1075503580301e92908140340d8100c100168903d0080744d000241d50400302045900c16039040e910031558a00350340d070b42c04440502424110f401d5154924000825982940c21030045003d01c0146440c0c91000c040542c440701900b00200c0c040707032440e0042042240009281070340b168800780301109079a030700f000310f45031498241c0e04070b5492050640002c0c801c0b8801c4014170308184810400a4030b0082130b121520b4010040e206082d080d0201410b4010b468805c1e80034100000c0d000c1c003a03c43c050b1054841051101c0803115405444002c80301c10040c2c0c0c0123207101c04164040503148014030746040e6401079107070001e6048400d040e410001d4000c08020b280e80300000a040001c00c10054443c040d00d00508825260000321003407031401102050422030314050720f02322940140117020362814002480b0140034440350421140c0c800740070b004103a82a1051861280140b5543e098031014941000e0346010144200c15004501e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 320717203 1250 320715953 320715961
    0xc0513060812091206160e0109060c03030c020c040609021206100903030c11060f030901061a09040b0a0f030f0b0f06090c1303080a11070b1207180911091008 69
    0x1c500e00348968002100e403900e820300280450980f4503e11411602030251004002c2c1b800502c41d80d648400c032460f55444a403108940054030f048200380985c030081580f4400e4500040c1c0310381c200309105119031040d2030f0421706040115007581c2040d0401a2040e8020550241c040d60500e802e551025040755003410b4041c21003070240c071840890201400300440841410306004038a0606007541e600603020b03542c2c0343d001000313820f2140c005941ca40c6840d401c100c400541c400401c102c0007070340d2078401c802500c1c0200306030410000740105800c0c950044103c0c000002d240715941c0440005501030120764818440c1807030454082100117000400c462405000d0020f01d44621100561040366101d04a6640baa0212500e0344024513902c024040c0100140c03c00059034042c401e2a40749429204a8010689900314100b440c003070886001c5d606940c80b0300041e689482103071350300e00d42d80c0803d800c103200d5a22402080103480404035500c2c0c0c0001c0014080c2e405042408032604160706900c0e0400c4c00c3e00f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 320718453 1250 320717203 320717219
    0x120b0604030803090102040305060a0e06090c0303041401020c0a03050114070302031b07081303030e1503090303070c241508010e06010e1914011508100b0f090306040c051306 76
    0x80d901018000400100000d03402c00c0003541140c01445c0c000084071020724040c4d865002078061102200030b40d008000100745003020008500050340030003005942000c0c14900305180041c0c00d1001c0c44d045209100020920b510b800710b81d00050340c01000040b070039500c4841d040d20142809000081051310402c1000360050140d1181d01401000100032656420f040c18204c9190040880700030a5140309000002010303000180c003520b0490607200c40d40f0450110010003528003003180c400f070080c0c00c2000040c114a1080c1c4a580303815100e40c00068050750070010380e40d4201d003202030080308950342c2d104030407500b041240814028410030000b8880e03101c00e03442150311610107205102d4030405640c04a4070b6001d07800280c40d45068003040401a00708001c6284203080001c5c402d00c040c0300d20b00684050614130416885224003840351411802900d02208132900d6071021191052480003030212120960b0b00344180c901441c0076644030203003d030034901002148101da960500c5502d2420104201941d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 320719703 1250 320718453 320718457
    0x3050606121009080708120603060601050c0c040e0f0f070819050d0c02011110060512060f0705160c0b030603371b0308030f0f0403091211091303120b06 67
    0x20b6000707002140c0d85680d8980010b5900038000300030124580410011030b0b0b0034110501c28400e8900b18104d600c41c1e221480199275a1092401803600741d0003614528899060036000504402c5a4908890503101908030040c107000255800308d0b0550040b2100700b004a008005032501c03020418100c058a40a0b1750300c0603680d2400e00d5401e401d2000c0c11800400b560b0081010945285840c82681e80c21841e4040520040009001700d5100b014821000301c10040c000404606c07035044d40b240300c0f20341e4440720800c4d61031303411080300c006908a029115000052501c2d220780000d001046030151031f41040d0303080608200d0206441c845c0d040742d6400040e034030000e000c0c820003203008030b60b40b9503444c000030f051221950710b003181f01d01000562544000b0400403607000540c840d0300080140b1650b0380300c54001259011080e18068005680d1000500070040d0700443d00c41030b980b00d581d500105034001c4000c104156012540340c10200d075000320380c400707160708082402e4503458000010414080e156002407124 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 320720953 1250 320719703 320719723
    0x1080105090f1b0a210207110904050c0d060618050705190201020d02040f061202040305100b03010f090335010303031805100f06051c0b1308130305060612 68
    0x141024901181c40051143c0545103524050302d00c0ca40d88000c0c101c00a0000240080000341c01403844800400400c028800c1e211015031146403e66620403403010403070408000b6000341c0340317401290043d40040d1750303384c0c4000b01e80b4401d58001c5006898802003c100a400609020762141400204150107070701900b200d030f9008100b408910b000007800d8080303009004803488681d80360310000c0d000c109030180c1d82c0e820046484547d06d8a0925007090341d80d0302a40180d1000405a40c4600301609058689810281d10b0600140002451104c8942000103035050028254045003250b520400c0075841c22502c101c1c0c04000030301030707440c0007642d00042282c4c0301c0500c400b5081581c2d41c0c10880088055040c01c0e010700350004121440c0090003400300000b40071a9a036230b6081c0e071510b0000034480c244400c2220240540c00808a5000c540e80c650120b090f00080c82031000b040010300540010301103030003400c800c00d400074a100b0f055055203003051a20354042e00305445030741038102441d0400c2000a0034100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 320722203 1250 320720953 320720971
    0x20601061404030209010e0924070f110d08070807020a02030c060717040807050406060c030203032712031e1303051e03011404060e1302152101080106050108010509 72
    0x1d6141d0303609116a81d0049400003584040210000144111605603282c003564000d015940b605281080d007100d40d40c0542004405081c0b01c1d400600c2450080c6809122401d8606005d07400701255041c3c5818025480315500200d21260144200564421040c5512070a280001e00014003981c00103907482c1e550400042c8036030400580741003003203038007040e800002c4a01c16889d902c0da03480e0000583c80e10540d00680780102d14214001480074800c061310b805d0345425801031341c6181c55041c01940070801000f10040c160024018040001208000220702c1003551681da9840741400210500e06c9007904c0050810f000c242c43c103101490b0000445210350302d51500700180c0e14100c1c00e031508071500c21200d4006135094040000680c1d1900d8012403500e00b00125010032640e911550300c0c0d81c44aa060f6002e195442e640308407400181810501c403c3c054402d13000702410302d01007403400c4400c032440b16510840303942500010000d5800900501c409840242412846981408081102642c004000102c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 320723453 1250 320722203 320722217
    0x5010b0d0203061903140c040203070e040513051207110303030108030415090f060512100f05010e010e060a0302070b091506040f0b0d0302030a090602010204030c03080919180e0d02060106 82
    0x1c1d6076111030403070300c4d07031030421204030440f60b500d003014030129241920500080c000da07141003400e850300748203d074443c040ea6200d008000480c03e0a100041400900909900380c03617007000c0d40030030801c104a8001200d0201c2e180c1c4d41381c4040c5000050088203050700b500980c400c1c0018400f10387c0100c207441c203940c3c00111a0003458041c5004580b14111944401060307a1078510209240d80c1c800000c1109519003802c20b000c54507481007180241c4024802c845403c55908000d000e2507200300002d12401718145400000c07141c0c69000144a50f00850034100880d500003010301c1004065213080d0f61005202c2c0c050001c800303040c820100c004000604440c442c170341c0e40003076000741c1c002a4402040c900020b00540040180361034060b550354081814000481d5011000041042c07050003150f050365803042035550300600c3d40e0340f007031040e80110140550021801c0a0380d410206840c8c03103100201480c100382a1300f60320100410046403103181e814001e503000110911a02500040c00d24116492450b01300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 320724703 1250 320723453 320723461
    0x10f1b02091e04030905041802210106090501140f0904080304030804020402280e031f0e010e1f0b04020f070f0302100e03030906011d0106030e0a0f03020d090905010b0d0203 76
    0x46000e600070101c1d4102c18041c1c003403000b4154806180010b890060b1003c0011084401100200083c0b00d0304c000d52240700300c1c40149085021907aa5108418590004515070341c880c100d0b0800c5d10400d07000707000000100b0611400030724290882030f180070001d45010066003499281e0000ca8400104050207110300840403c0440d1a60b07030484034007080d29600400c2024440052407040a450b0030100e0006003400120041444d02092102400000e0300c08288000481c001c4440507040080030484195a1340c0703100390000e14244401c1c1e1840401280043c81c4126604900c004c0303402c4404910300603031040c8082c0110500400c1141d045980141ca25a81000c0c1d03490b04a1912a001c2420040c2074144101d54800240001c003850040701404143c078402ea0300c40e40200800804c4a00c1c40c1034000714030b00104011402540b0120305c01000c0d506807030318020152aa810381a4090b441100180c5c40781080c88a100d038808500c038060a0340a106210075450101249007600540047e02c0e6074641c000007003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 320725953 1250 320724703 320724721
    0x8041208072109170307050a1d12071505120105040b0d06060b0405130c0203160c0e010308070506180c040c091701151715040f0605040b06010f1b0209 66
    0x16410041c0901c2c1c2910480322070000314082c000c80c52040314044410a0140752843d148010340e8410a41c41d0340b29400d100040000f112185007201301c40d60440d510b0041a1510f8482c00807800022a000b8020318005241001c0a00c0200d4600e100608010080c0f0034011500c00110305541156000c03900800c001101d200050b0309404400350041900b403901100042c1c04844001400403901d0464408003030a28508240c0161382010002d880140c00c104030850f10100001a101c075500d0261000c0d003465601c0791b29000d05140c080e04142d1341030324041000000c100080210603400050003282c0e14850088802c0e040c1e4450b020f030700b0a40324580799180090b040d4441c030340d180d000740b101b41c20b03a207280e15000c60803600901e09503010440b82c0038100c40204c0c801c550340c50005180c0100e00c0c000c1551800c8202c0c0705d000c100b8051300c201c030062114240740c00445c4113030003524015070080c4500b070400d040450005d08615445102c001c188035400c2a030141c102c4010a400040c41d80603500000c003a5130345044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 320727203 1250 320725953 320725967
    0x5010e0d08240d051c09051305090627030a020a020a080d0903021e04060b120106050304150f020c030d0e012409020f0c031305040513020f1002010e010903110d0804120807 75
    0xb00c00d15145c0e81805100050307000c0070080c2142c0c4180c40002c01c40f400100c50900b1b032841100d4030507142c2c3c002c3c4042852030800998660003000290001d1003001c0035a1030041c2947c0c00280310a006902c2440d422066180002c80c010060048400070082c0c038032801000f80420240317200c064481c420a00180140840308140003000542c018001c208903a10360f100c0102d140c015144840000d50000008640380340a80c00300c2c0d0140e600860307049203050380b04420002404140f01c007000e200b5002e04c001804050100050400140e02c8100450710306d41084000303003150a0032a0f60001a04403140c03220b800b162106146043e00e42c3c245004d680c60503138100c000080d104107019142c25100005007215420701242d0b01d04181d0f40c04440600c1152200243d40e540280c0350301d03010b5032001d04081c52075020315000a00b80224103590001090088805841508590301c40b102a00403508404010705990004d103c0d42d4240200d6007081c0400b81400d1701e4005421004004550500c03201c000800e21007401924 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 320728453 1250 320727203 320727223
    0x5010f1d06030f07060c12090501090b0a0504090f0207212705060307020601060e040203010501210906020309071404050c040515040e071e020a0819050705010e0d08240d05 75
    0x40313505445c0c1d00e105c02020300b110010f00b602c0e401700004d6039500c07062040c0313071100c100c400580d141e07028207091600c0607181f07130b00500200007403000401000681801600a04291000303007440103844020606208031074828109080342444001c0b100f20000f16000440c0e01d20000202080030803216001c80402100401604110352144000c01049201c550010b55203040e43c80706e684502091001d0405d100a0780001e000e400d000c91041050034402d510200f0fa850030481c01d090f0046101841a220076040364400d4030034007030755000101c05000c4404080d44480f0011020b503000c0055140c0002055054025801181d10600d0150641d240b03000d068820758001d01405102d001039410280c1001e002002c522280002542c00e01d000b14012500120300f01c5c8a294002d0002d5150259503994880b01c402d2469a180922809020010120f54244929101c10768100c00030524290101005040382200170101403000c40001c401e464003241025007440c3c0000181d03000a0000510301d080c6003029a126 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 320729703 1250 320728453 320728483
    0x13009020a090f090c0f0608180c101d222a020304030c08030c060403030b030304080f01050105010e0a080a150b060a02010501030b100b0f090d02030f03040905010f1d0603 75
    0x31900c40d01c03018444d8000503038030784a514216489a03a4400789050807080b48201000304004000040d4540c94404500315104141c0c1c00341e96501c4007440c0003d444031042c0c6215400545160358242c02a41e4901c52160401401c45040c00c84100800c54801090706085d4184000b6880e540c241140d01c01c02c1044050384c0b400b00050001c04110140025500c0d001840700b51845150030b000064044408011030b040b07266010081c140b5580d480d1800e801820000c103519425100c10040012019403d0001285c034003400d00000c40c0c0755240c02c1c001003458055a076400d11501c170b104000c01c81481e000a40c441999404102c60b891a1030001d5040020300d900158113410100004802c5622681940080d059074400c0d41d200845846040c00713230034908902d020f21041c4000401c400d003050b40d02d560180c030469100601c2820444465030210303040031400300e25400c213030340086401d01c1602c61034062540503001442400702460300e001111080e010642800c19021070203840482c2094030244044150751201c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 320730953 1250 320729703 320729711
    0x17040b0d150906150c020307051507051506060403030f090b04080a0b0f060616081e0d0b04090210050310080607020c03010b09060906090a0219030b013009020a09 71
    0x44045001601803181900d142140444000c2180016403140d4002c0e180349920024804d410b0750019514050f15000aa0b40340c40f03001400120b540d10301210003801c0b0078000c001c81d01c40c002442c00a14101441070881c03852640b5100b000007949859064500710303900752800c0c01e80c1500e034003420b4030010000e40084071503150020700429015400270700310038480d00c1031003003109541d14030204040300e5200340d4189500c00c0080000044235800b0060b248551401440c040e450206060f09100c807032900c1e000108200c0c840403540f0380c00d60905200720007613050281c405000041591340044c502004140b000000d110340403010032600c9140c20214000341030114102e5980b41856a4069036a4100000552296080005003070040c01e00c505043c1c000c2c20003900160b841e445250401608960007803404a5240d400d0029400048500361050481c00300c0d47c50007d85100c215000500021070004200c0414401403902401504c04040c03101210603801e60003d1880c0c10b6200003485070001e9440039180c1820 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 320732203 1250 320730953 320730967
    0x5061306060806012d0509010b0a1713050706050c030d0203190c020102031609050603010b0c0f0109260c10050903130b2a070308090a0306050708091002040b03010317040b 75
    0x12011400c0300c0d000e0001039502c030790b000d80017103035003c8107000d52038100d0400001041000c11040182c142c812003030610140845008021400d0071808480080312401910151428040c3c244844409005607181c098600342c012211b6981c4c0340704008007281c0d500d600000081d180c1001c40c1000100c410244401c0c0720410701098024082c0d0025a42c0c915041c1c41e10301c102c05200c0c01800c3c85c0b4100e803009030109096a19110b650702207900400c60740074580c0190b02588001403428803401111900c03500c10b40c44007200ca4105080904100c14400c40d800904000c0110054800164444280c000980204a580c3c2e502e803a5815405051a45c4030f10940d4000c010a44050328006461a402119140e005103140c940c2c1c41c2e00f0a1440c1c2d0003a0322984c0040d013003840410a10340040c00300e0031010300040c1c0c0700da40e0b9a80304011140112101400915008103020f080c50050068829540a9000079402c203401c4c0041160644010b102c0141052600c00383c102200c090382064a00428110811a4949803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 320733453 1250 320732203 320732219
    0x806062e1701080106240e0a0905070906031811060c0d020f0c010c02090703020306040204050a120201020d051305010503060a0b2a070b0405060c010603060f0e0c0901030506130606080601 82
    0x8140e851000c01c5180c04001040212051182800b00c401062a10402021000d10303c14480a107248801c1040002602d080540e250000208014810341c00c00007614588014010800091500002c00b00345c03d021036440002d0180c2c40d070042c060f821001081e5a440c8c0c4000151451103254414025400b0b030240955030607402007101d10b480c01054060394580507840004503040da2200d80c0c000c0d8090000800315a060744294042c6034000350191005242c16210000a22007044903885443c0c2d00c40244075010842d43d060002e91540312050500d02e0400e10090514192011135000d0541044004800120f1980d0782c0741c9004001c01c481c80d0600e80c1c032112402d803204e8000c110301d0303003000b01400d001c519a81b4110001e0200100e03110b0310802401d05040104120f80d540c4407405101e261340d00c0b400003201040c100c1c03058039040c40d4030000020700b0307529205080307084c054284526407082607010010008034030085961907025006007041c80c10b01c00c03a403500300020817842c0c00c044000e201c0e000011803046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 320734703 1250 320733453 320733467
    0x4060e010617070311060306030a030813170408101103010b090103180507081e100f020705071806050d0f030804020a09050411131503060f0e1002040314070806062e 72
    0x2e004880c00c0d8005d217044800d2103154402a602990194480c8000720301080c40345003500d40201350b400c3c8100114001e80c40c0c0081885028006021030100046c0400403403070208481f0310948500142807214603012084c2c00d0351400144640000b00384001205990b0780c1c42030380004503029135940e031460292098180141d44014a006000761881054402e098488200300020603c4c0b8840c401030610040008500c1c02500300c0380d1420300c0c140c1e000d020b8900065414050503000d40909421451071540b41000700e41559901c1c1d1082e03000340400102c0344041400326a6204c4c25540504001040780c0b00e902c0402c89211a951244203400e24080c2072204000b142d40156038140c03800c07181c202040086003a403008a0341000c943e400020b509800410006000d50840095848400000100036120010350f5003409640c18107004540d500080034070400c00d081c03140c4001002580c1c0242045030a00b0040d5507640c038041c10301c9100d515035a0884550500070b00b0790944c0d0003450710810b8110034400c01e0242141e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 320735953 1250 320734703 320734709
    0xb010305010e0d1704030f0e0d030e01080c0a020705190b120405010c0f1710090e030d060e1b070606030206120403020c10020d050c0c0603010f090f05070804060e01061707 75
    0x42c0074000303900e0049413140d44800c0f850340040f180b003c65a21207a1301500c0c60070200c04050705005105250304280c0e619101208655400b076200e40329407412440004040100007418408403450501c80d00702e115a000074031500750360080c0c0d50180d442c17074100c150601c0007486900400024000144a04003610012140c90289210720003d0084144001040d64600080404040001c0001c040135404c0402d05480b1604044a0701800451075242c4800d41e041c1c5200040301096a840052403004043c41485030f84000c0000100715805c50608150003203401c2040c2e410800c0c1c550300850403906024144c0d0040c0700075a8001c011030b6503008044401c0841000c121001d902502403030110503411f0400c86081c2403582001d03406403c0e0422083c1e01560150882c02c800881886244140103198954100450107016483e2809440c01d10f401d0300041500c1d101c42d846407c545c01c0c401803007800c54100071040c1e0026031001003c1081c510101d070341801010b07903070b110815841180011200903040401c9800c25 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 320737203 1250 320735953 320735981
    0x1b0a05040305010b061c050711010507030b010810060f140d020d050a0b030f0616050405030601030c081011090f03160e0a0b180402040e0a0c08030a08090a030207051c0b01030501 78
    0x9241e004c9040103914020f0326503204d98144010401034910071160300035a0300100905000b60740110074036000782110780480b488070109682d26101c00166030440607061f840740c43c82c115402000d00b02007004044048010a84050181e20041280d01c203014005407900c1c590b004c04215103803411031040740003401d000e960075641c65291283d010b00c1400d011804d149550501c800400c3c0c2d50701d980500301d4180c007207021203104000b014000403a07079690520040c2c0c000c40c0a17180790030400707060130500b40c14030b0f0902c2481c03802c0610380b202da82205801c01c1c0c190340d05040c040303902000001c4004003082c2040c0141d0050924192030034400700704070001036840750107440c00d039104104030f0f821442480039480403002c0180100362150001030041c940b58121500d00b04520050f030f0740400441c0d0743d10140302d246800c00907140d040811082c403116440403013a13502490f81402820003180d1920080c0d00c60b000d60040900900400c9100781040d2000640600440c3d03102c810a0030079a96814100d00030711041140540e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 320738453 1250 320737203 320737211
    0x405090c0703090506130801060f030302060c07031b141e160b030f100b16021f080403030e0c12010b03070803030402092d0403080609010e1e1b0a0504030501 69
    0x88100c0d0315409035544594582c907942e910300d05010400009030440089544849010000411400b00a00900c0c004000090051000e00d046142c081d040941c001c01088902c0824400840401d502c0301120103104010f24820540a086082000c0e4205480409007028420401d4800c1c2c8410002c00c240030300804101a1070000d4024060b904100a05114811296105001040382d0b03045200c0c90941000080350705802043da40d841480094004041220024445e12031140030350510700401c8200c4960150452000110840042d00003200500043d0402d135903404102d42a0400704440100f502d8002c0800c0344d1451503040c050302911152003403500038000c841001603001c04c00826280596401401984956a000b030078401c2080710384800c80c080343c1c903d00030911040c851400a0301a034082da80f04e850758503001003400001803060b8404401104c40c842008059100c41c00303074051041a280100b48039403600f0440b01200c1c0b9190691a01110000170086139064003d401441140d00c248001c5c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 320739703 1250 320738453 320738461
    0x3090603050709090b0604030f0308040b0a020301230d05160603110901020d0c170f2131050f011d0a02030709020c010213030803091009052817040509 66
    0x30192003082da541c1d0301052030355400f0302c1080826001920005409402241010f560b601d0b94841c0015049007500411586814031003402141d0082c20785c400443c800079481d55240412082181820115000807103281310001002640c82c0c00d100600b0075041021508071001c0c4104080d1856540d100ba2004a440c0c0106800d0b220030940940754000e505802815070328035500f009641e410b00440040700c241c0005845003640c1c00a01024100004a507500d098441f210340c1d0100007030388030b0202000900c00701d110403c006e046000102400c5801003690b03041e64442442c20340113110744164030003070041c000c4100200e001181540b00d090b00300b000c041c1c03051100c1c41d000e2005403101001d40010350541c100c42010302c0566a03a800801d501c0d21100001450442d0552288000d1045074000310345466000090003181c0900300000721003032502c41070030072004401c0e5440c01e94035184a101c0000c0314640a91500703440c1304e00e5240c108480e40001c6110100042c81b80e402149600a01500780f0a600d03402c041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 320740953 1250 320739703 320739707
    0xa0b1b06040210111e01150b1305060f0f041818030e012a060e0d052a0c0306070201061e152109030801050a140a0b030603011b0c030906 60
    0xc0341c029038014108801c80720904200719160684020400d1240c82003200305504d4051034002d102904a0050001510b0106941c40b031074104840d901100502005000c0d145003075468588000407074100302d81082d40c4501d0107241010380d01551085d1482c2d0103003c10300294840031400500002c00f15200e0400c0800003207400b201c3d400701d054a001d80043e89070182400b607940500407500409101415035600c109069011200c0e10024076000c44500b0340f107400084001500300860541e0380181d0400c142005051000001d842d407080171120708251412070043c80c450300a0005a000601c040c0c1034550074072301010003a001e00340e28891000030407035002a004050b061500343da0203407492503a1040041e940403108490304044c56110320740711014455207802c0200395100340c0c0c000034071030b4864072134941c54182080315400c03040e40300614440b0411520f0f0300341d07502c0c5d04410098035044400542c503629100d000c40e006051908100b07440c6803845d6001c804683d0440840c10485200b035a540410780c0c0c4407101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 320742203 1250 320740953 320740963
    0x4090c050f030d02030f0706020d0509030d0c020309060f0706061a030f160e010c1103160801050a020c0309090c0f0f0d0b0f0a06031a030604140d021b0904020105090a0b1b 75
    0x491001038106000d41d00e41c4001c40c00052480c48c0c000d010140c103043c00600140100c1e44242d544c51210b610000c0c048451003500c1c007612144080c80e0000d141005100004034401d84182082d011460000103507040411407141e000c500607040300200d030449100803802503d40da500c02c7d0b07a40302141d480500000c10b1005040c08045144c0f66550305d49650900c810010f481c9001c0c0543e04030360300a9207035260b00003500c3c10041c440c680e03560600859004c81c580001c02d070031030300050524190329004200450348090008102c0d0707a00c2d1415244481c1c50742d01d03a9810300c202d00840380c200d07904550028070110801e403000c015110552141c0000c2194015640810960061000c04250440700c0e00008001d5a802540f00320304000100d04c815580700c01d454002030401c441120f080b1600390350f030007017900a550b0400c441c03404000d15000921030412901488200d0460440c49144128070000014045903c00e0040d01c19200000e0010a0399540740c0c0b10044450b00289514070ba0014a900401e01110b00055 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 320743453 1250 320742203 320742223
    0x106050903071a07171c02090f0901030f030f020f03030718060309030827060a050901140108030301141201020a171f03120314040303060812070b070c0303060504090c050f03 76
    0xa00928007001c40d9a10690400c44040c111444142485035a008500e00407010500c1805001b0040c0e80b0a003100400012490020f1924080c0580030014400500e85009104140d034041c00d00c8548015103041c101e28010100450142902000c018440c60700c0e01f0803049180300c10320b444105062500d503c021011500740c440050001001034004c1100d4811300146201c004200c2d0096041d810342d01c041c81c0d4034010041d074550016699450800c4060b40b428841d0303001441c1076091072603a5515003003800f03560340018052100b2070175100c441030701c4a075a040e59800d5018100c2d4025074907007004150141044030401e07244411910350100041006101d00c7c842d05160001580c982c2040d4115102c040c0c1030500d01c0e1402d010305030b03510020a5500c0c407100c0c00c01e01c203a1080ea000b041d5681080a168101044400c000f04180b00c14864440014210302c5040e501c440603107008034643c0b1081c00c00318003a1809502c025002880c103000c0c030381841652080202504c6054400c2c00d408501082456503aa4840d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 320744703 1250 320743453 320743499
    0x20d0311090d0206090406030f06060e04150f062111010e01090308030405031605070305010e06040b010303110a02060414040b06041203320c010506040606021b04060e010605090307 79
    0x414401c85140c01081c0001003800507105030f09100401c0045001c4501c160410b4500588920310344040250381d0081d08058a01103d03c1845030515a50b0041d0f461159829055107036201d121528104c42035501690050008006a1140603800c803190f98401d10540300542d0f070f842c184007450001354003c0c1010b025090040e1345a01c03030039142d0b440e8040075800160046550740000c101440708100050a030344c0700c0314001d002038000180385190180c00c4440c41c40385081c041e0041742c05c00006c20091035406045a4142c00d0103940360780c40707440304c034142000103000a41c018000b2030041140c4000c00e00c4030101540c00d840411013a525a030400c80507020b98401ca8030091440b0162800291103016041e0384165801c1c002c1e00240000b106508511104e150b00007500000450380e8842c100090103025003140c401e4504100c0141800e400079211903c50301d030002400843c524255090f02c0da03900c44030051445d10440c580c956102c07140208184d1004900621030320031040085550b142c0403000b101140c1ca24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 320745953 1250 320744703 320744707
    0x180a060804020f1008010510110109080406020d0c0209151216050f0a0e0412050c01110304060605041506080c1b01060f0602070e070c020402040b0d1514090a02030a02090d03020d020d0311 82
    0x80412041c003e841e2300d890104100d1024506141100b40079040d4140c1c402c0440c5500d95081c0080289032500301030007141045070350030b0f042c00035072617081d01c40d40c00c8401c03107041140745e806c0c1c40b0201b0142c0054410300100d611808400409040d050b203112010754038116800901c1c08244000c00010700c41c5070081c400d50070340c2540490005451000d00e003500c00c40d40d050850420070025040703801c51322100860412014000101300c00c01a25109105c090b140c200d0f0f08100f01e85030900c4010845800c4d020b001d091041e03071000f1520031f01061060b2900e038480350072808415a404007445003e40311034441c1e041c5031245142c022940a0020600c1d006444040101550035520700d402121000759a02090f42c005508120118416901d50001d02171305c082d050340810100b82d80341305c0040f01d049507882100b510b510b1000b0039025a840d061110342103406d040c40503840f034032400643c4000344554550a50301505030041042010b402040945212007a6005d480c0134480c0b40700290250b0381d0b02958601001d00c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 320747203 1250 320745953 320745959
    0x90602120d180c03051603031205091204090212160c0f0218010303020c0906040218040b0406050d050708060708070c2603010803091203070314180a060804020f100801 73
    0x3091001c0c003448000464045098400300044410040400e241036640742c119a006000b48101088210444042c00702105419441c6440c001c1150152504000202c0d03104d07800f07d04400020000320f0b015000c440e011a58881d80c0f14a66402544280340c80d4800741c3c00c6078006200710304088070200f15500d05032a2054241081ea45034050001110f5040303030b0003540c4c100541e20786c800104035540230f50701c40d070000c045001c0d80c1803c104c1d4800000304040d1081d401040801203580302114210100d16090390085884034a110005020300000d07008260404d5031300c0300302c0b814460000741c000c0888003101d0580d040c42d2545a01201c00c10400c5a000d004941c4541030355000403550a405909a518011034081b0700c0e12400103900d031940280d00c50b842960012641d800340c0d280a4010904201d00350000f54030b0104141d03005095641c0c80c11a0440d8040c0106001c0f58a07080e182039204180e00061400241a441e4000585000b00940b000d074003401c00000844a18104006050a202340545410030725a03e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 320748453 1250 320747203 320747233
    0x60f070b09120a090603240b1b100203040b010b0705070b030c0904060303030b010207061e0e0102190c09050c130e07031808040302030607080709050613081b10090602 73
    0x4006461149140714420100040ca410b50010748141080c55032043c0405140800085c26161030419654220303074210088440e40b240c0c078546404464002804544400441303000c00603450f01085500c00b02d0150080115003960a07500440c0728502c1121304144503601c030840c100240c003c0240040c01a404400706000e1411400099944804030a11007480c000100c03000c030381540c100382c0c81140071907111510024150b03014401c010140601d0b2900305800300c025044890141c0341c4250540500000a0445010780d10920500701c0c65003040c89000801403c0d4a0140f107065020f124a6500524100100c3c140d02955411200d14211580032900120300b0700406902042011300403c00341541c40025040344e030700e100382d0100601d008020350303a00e691450040c14101380c0c0042c9009c0402c0348607001c00608980240c1c242066030b009131405901c8050440090b002031075a03401c0305140c0c2c03040484c1e10404500003000c9a4541c0c0c4160380503d01c041d2441000c0e038950703109015210250304844100c0040712 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 320749703 1250 320748453 320748473
    0x50a02040b0d151b0c0b0a0c112401090b03060712061206050a0e0604020306160201060e09010504030e0109080c01030e01110304050a030201150308030402120c12010204090506060f07 80
    0x254000e0010035a00540d5a400fa03c002144142d0300d85251660180100700800708050440c4d44003e080c83c80803400c19a44900c1c120030003c0800644590700c400c2418210701c203d00000b0079440c510f04503268410745103182e4410180900c40702140f10030000c008940c0d04480c0c041d40e0288103003d4001d2003543c484070010380c1c054848660079030300c641d0351b40300000c1c007254140140321285015404c00191401c11441c601c041e0340e66030400d0f8419a02003014080107031000200c0c950300c088105110b004990070203074103d0140a0350b80c441601510020b09203d030703481041d8401405107109483d02c200b1068200015180580c0030b2080c0341c11600044040340d603030f5020b0f810038943c00c031511000040c00001c2d543c4441c0d80e60810344065031103500c0094020300309074091040140781d80c3d100384620b07001031469a4000d42880000c0009004100c941c0700702198840c104456a03010900402400c60b4181440c0350328000d400500c40e5608032428140852000e05103507045680c42e07d850022a803410f022030f220ba500034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 320750953 1250 320749703 320749721
    0x15031712070f0e1f031107020a05060f09040f0b0102100c050904020d0612080912070e070311071a090d140414030f060109050a1a1f0c050a050d0813050a0204 69
    0x10041003d800030181e84c540c50a00d11201c40c0b010f50105004107100014112031045203113040c2200104440300141e602c0c8291a41120003c840d002d03600c00d41b1700c0e680d484501a0846090304182400e00a28914050f0740200c80d10348020703030840d030f80c4c0080200341600340ca003101c06480101d6420800011181003070740007001e01108000c00400c85e29601c24544403c228000710a80f20744c80c0100d005161450882d020100c0002d18400500746182045880c0520580150085c001e141da03c0b6481c80760071030500c060f03d100680003800303030b0859040300d04910781c003840446110406000d003442080409000f0300401c0b0441c05900da24500340f40c02c14103020030306940e15055503030510801025840104081109901801c1c1d03101c00031459050100d909415612420302c2d0041c400c00c00180081030391121948640000f4a014101c1110a4100816a6012594900034000d40107030b003601c00910000150031941d059140c0d0fa0000c050351403401021140180030002040790304101c20003409864260819a14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 320752203 1250 320750953 320750957
    0x303051003020306010f06031506090e10080328020102160b0a1b030b0a24031e0603030c020f01020703030207030f03030f0204080c19050a09051915031712070f 70
    0x4036948a40000745803150980c4007900220b041c10307082c445190706000b001c092348000f06402654604003900a400c0c5d070340d00c0c00f403410501c2801000401a0031303035103038030b0001704a1201a02e541c0c0700090841e850341003201f87c04128910480e0341c1038010910510031140d0b200f003c0d0342020110740da02d070744044d003183c809031074601d4040d01d41907060420303803440d0700105010840d92400681040c8803002d003d00f00c49594800c00c1c0d0b210001c071304620705100000d001c0c80c68481500e0300084046101c00320b280c1c00b5050a00c00c500c2c80e07142840109c00c050300032031b1030361021b40200c131000c207240300d1540126610903260000400580003a002000000d00311b1100c081514480d080100c0d49030b94040c20715080f40c219030b0007407480d90b1140c941806142010384407000c8001c0d403441a02400f505142c04505020b00620404160681e58800501c1c01c1d07030385801606484140c400e05100c1224050401c2c442d03414030b80410780c0c041e000c080009070302e68103a03400c4558071a0302c1e81083c00c15036109034056445050007801402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 320753453 1250 320752203 320752231
    0x30c020d050303010e18030301061b0627060b0405090c0603131212050a050c03150604121b0905040b130204091b0812030c040302041116050d030e010b0d030305 70
    0x40011824005907000e4020030002c80d1180c945000c40080000d1b400a001c561500204014009180d02034140a4201d17441c0c01241c04002d05032820200401140c00c01d40c1031180e000c90480341011442c03103401c4e50507001d04414040c40c009042044101c0301c042c0c2da0800b45034400f4040d90141d040200c05540d000410340c1c081d8158607140c0d11040d41c500300c0034004000182d444000200f04c0b0308030340724040c3c0113010000c080102c1e00e04088010424800601040e10800407862407503143da45907000c9030081c00031440c481091600a00c0c0100802c110b40c4d84904108506000218041000d807250707500c0766800c400643d034a42c0f0341d150741c00a043d90304507050360400e44444223030b00403c0c081c0d2040304881e41544900e900713181c64061100d041103480f1030401c10411040003440750500400c402c9e58141c0c0d404540c0014800f942202400b09403203840e2078101c103158501c899800f40507010a400c03000c3c0300943c03014403a0f041d0b14040c40e800c80b10904007156004452030440d0000c070340b00780d00541d4800c00d240c1d4004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 320754703 1250 320753453 320753479
    0x60f060537150512070503090606060318070f060f0503090705010c060b04180c05010e030606100216060309020108060103060e0f04080c01141b070c21060905031e0c0a030c02 76
    0x5841441e918200c000400c00008134042d001c040500110f40c080e2a0f454002c2c1141000c1c0742e42c0340c4824015000c14401e00300070004c82d403074038007418621a00d00f46540442d5030082c0e80e40d82d40d2540d901da40c4500804900100c241000d164001c508484c490881c41026004090600c0d00640b050210440c081c0da441c0d070340d903010310310130b803610322850300c60100e0703a024840e81910314507008101d401a0781000f4108070080020a01c81d443c00a00b09420031411550b454140d24554030480c9801104480e136002d040e42d015000900a4045e032010850174000e0740c4104180d603a000064042c1c806138442c1c42c258039041030000700601400d503c07031a0407900c02c1c485d0a192504030810725003981c402c4500008041e000400b448050001c2a0161b080300100c00300303280c1000c40c213440d0191480300320f206031403214403120369403410b841c0e0121032280d449601c81c40c20004540c881c101a6030303c3d040b0300c0121082c5102d1344403148024001d0f8096032a01c5c1041c1000301942000d6503400c4900c0c00a80e601242c0040c3d040c110b030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 320755953 1250 320754703 320754719
    0x22080a080a140906070305131e050607060923070e06010c030e04140718050301092d0c0f0905060916030c050f0313290403030905030c0a060f060537 65
    0xe00800340a6a45e43d6102d80c5c0034601040d0345891a48100700c1d48145272600c12171141d01c07c81c02400c443d8100d0707100381c41d180130b810148040c10100000801c80705001c41c001503420305014180304035a800000301c0d00115108c0c1149141042d090383d105010603000102900001e01c03600c94448444030107080800c5c1d084c0101d0104202d450241e9891010480c1c0e0004100218055640740e0003e0404600034440c2e43c6440d00c85202d55583c1071150300d4a40c0068420748400400c0c04c0c00ac40d000c035403155501c010030303a4986110340054414094145001d0070400441c49510349a11542c0c05088000c1000b03031031103020300e41500240844801042488000c0c004014944a0900036520490446034250040446481e1079071450049001d00555580c1c03803a0314222441886100e10ba1081e494140005c00090341d00740340d45507001d03082440500f489200c100c1c03800c100031500281440640c003142070004c15214002c014540c178031b6410019040d00b152050f00b0b81e625079000c41c5004021044c8800380e0b11902c1b2144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 320757203 1250 320755953 320755957
    0x160c230601180c020303010e070c021206090d030e010e120a030623010201111e0711090709080105010b1e030612071202090708010b0d0b010e0622080a080a140906 71
    0x442500c1c2044140c0d030b04107000d00400ea800030180c40910f1866041200b805a84100602840100024440d0180443d1505488000884000c0c411650146008186107a80d800052107040010713041c00c3c070001000c6014040c07800c0b045604805024021a01c21071031a8030303007144001400309500c2d80000500f4082c00e07001c80c10380b01000048480078841c0d000000e800c0d034080000703420700e04004003ca050780d007001303140c81c0b807625103d00030940d0b03540c080742030007904609060066035001400c82d041c0540560007401d1101207800860090100740e03a500988500d50081100d500a0000d1ba0b800e400018075521005680c002c60041072009008904200c030f030328005d020f8105505008110450f2000d52a050b120240d00c030f5824504440c1e690f050180007442e0303014030703c607a012031038642032400b0032a0b000c1d8040780c0c00b00c01c015042c26120089640c02d44503003d03a40821140f4610a0440450031000c0468450107a0750010030b090b01e0310303001e42c01c225000c1c680348071040500c00f001c0c8000d4603680d0b50080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 320758453 1250 320757203 320757209
    0x150d0603080304021e0904120207030816050c0103020a12090507080616020105060409020d0308280207150c0503060114040f0b04060e0a0302030c100c0b0709030b160c230601 76
    0x500030749034030705481404207400d0480545e07130f0b4841444190140700c0c0c5d10201e03502e9205a00019260400b450000240d02d8003085410080c82c0d5400854410303072091146000341c6416010f44104c42c02400400c0055080f03100f080c030b0100c00038140300982e0700c16003e6a00002c03002071059045401003580c034010107007004400d036102e840120010030300c81209030303090082680010301250200044000b0354001000300100c04070040030702c0703180000204401200c5510a00c007600c0003007854810305107498501c000f54000d180c11114005121400174020280340304895900c1c80648031507140d07486c8c2c0b10041d1500780000c00d03011104ca50410011400e13810242052005201c01e60619855070b04100e400b91841c1e000c00603440c01400d5120341000176a1b40024450501d000a07a98950000700300d03503040b5140403001c00301a102500764420b000311958868046e8044038020364032003a00341c80e60400c1c005d20361121010500003400d0685e080c400300d55000c91544c420b0401c08803a210300400360840b5030070020709034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 320759703 1250 320758453 320758463
    0x12f010c030510150903020909030d0c051909050f0904080c0d030204060306140a090c18030c0303030b010503100e13120f1101060602031c02090612010906150e150d0603 74
    0x21007071103d0b2120100240e0050b0840c2c004503100c0c108009001001da440a1101a11881040c03022607000b007000c0c802c81e00408c192000a1040c0084083d014006074408209404200081701140b07041034071414000c0c1c00c1e500000c0400118400040c100306910101810581c1c00540c00c010081050308204106a401e410350f403005a2185e2405001030212041940610b00c0c09142c40c10044a90755a22034110903244038a1f1300142c107401d0f002c01194404100240300101010201004c018407101c000200e080340d200303550500010724031000450704e1b400141c500c0c0130b00183c00c2100b40150703010002c190303620685c12201052410b00d20b032a40012039601c80c3e0300c2000300301070404081405520252415070000c02000070303c001842c14a00a60f00d2240c2c1400c5081c1d407401a9822122155540403909074400080100742c0700e0404440300b4400305000e02c0b8451405150020005900c6103510380041d141b81f0703d40702c41c0c0d0b00c600f03158103000003000c8a010302d01d11548104001d88038400c0510071000030f10300070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 320760953 1250 320759703 320759711
    0x6010e04050105060406030503190306050607210507050a1212090b160201050606121801060303110d02010c05040e0411030105240901030f14030c03040e24012f010c03 73
    0x81c1005400c460707000d001140030303604101c01440030400000451700036806112607082004145c06080303005101e01c1e0845948040300140250510520303051543e40714151054400040000c400300f1366a0f48030b103180080c40c68101c070140700041120a030380c1b662152628103000015005400e09002114410321080340e2000918040c41028101014000d07004c1d0128002000740b030810b5000500f50b030040e01401c12a50b5406000103a80040c400d1824002c845460000d0143c141c59160280000486544800542c481c1c8410416400e105019484100b01a0f407101c80c0740c03600f0440f002c004454010429030320180c0c0c96080c284152000d1282502c14005044100c82207104550300368001020001c510307100707019820060012034084810307000b455500100c641c20f2221101c40c41ca080d40200b074001c0040b40008100014005070441c451403081c4814240c02c5403034001d40d1504161040902d01d8240060b1080020a0212100d60341d034800c44820015000b04002c11900075a0a5030b818a440000007074403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 320762203 1250 320760953 320760961
    0x30905091608060a050906040218040e03070227010608071e020c1003090c0621090c05011202030403080117010f090516271d060f0610030605061b030c06010e 69
    0x1201e0541070f0015001c80703040688524260008440c1a0042c01442c4111f60000d080700c1c409100074060320110102901c04d0004145504015440e2f420403603069000350410082c2c2c1c80c5401c001110000b410101e880280c1141c2d082c21000c54034031174010f14110501c5000310300d00c15030b10041c00c0080b010017010f81c000c2c500001e2003003d00895548481c808428182441d1121000465103105181511840d180c19031603090705884c0c054a0300350910292400358035100c1c450b003d1020460300d0b03c0a41e00280c03201900c1580110b411012484200e80c041c000a441c44014044407101460b03024103030703600b030303001040007040301040404644040c0400c44140c0e118102ca141d4140e2030601035002440040071031000c51203031042506000111512888034656501d41c4400912a4080c0c81c8407103401500403100c013403030041d20100d1072500595846204010207061005054464050041511009040c0e2400c010b404801340e00f88603200035100205d404148002c2881240c204a200d0080551402441031414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 320763453 1250 320762203 320762207
    0x3060e091608010c09050f060417010c030c05090916050f0f0d06060219030503070c0f03030222060c03050706110c06070e0d021008100b04060e1206220309050916 71
    0x7a05038407098159040c004400100d50f0005c5040044a2066402000c94141400004e22620458020030a08003c2c99500030420b0b005500c101940406500c1c1041004e04c0f0f01801e40703641c003d40300f010354411404400aa03080c1c207680c00281403d403007030800b60300f080880c0ca041525a00701040c20300c2600804540e200380b048060203100024801030000c0c01001c64201c5222048505a100c045e00b808000004602802d1251b4241200140c0121129520800c6403600030003950014030f40002c40d9500c46198004011110042c9040303e03940d440d41408410076903400c3d6075035008400c00391021544c4070900c000481c000c8000b00815901c040c060070292400c40c070050401d48840078014029000840210010784421103000b120210754100360485694480383d5040300404d9422101115a0214001414a070803002018916038121b03032548920482d24030a50392000222008503901400e05130762040040110501504030f4046d20b81003440036100e5002c107019103410b649804401900e038100d511090b03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 320764703 1250 320763453 320763493
    0x180b1f0b0d1a0913031404030501090f0b0a0b031c1806111002040e010608060409060e0d0311090a1a28031109030606011101060515070605010608010b030f0703060e09 73
    0x20111140d4680c0c3c1402e0103007016130181510014280b150b01d034004492021603c0540b40210ba200b4002c0c0140e5400b0b00c2c04621403605080101e40009079400030500101d0907000303030440c3e8540580100789840d0a80c440020010344074080005010070004200b1802d07030040c0560b00500095192400b4000703030311200ca440e1049110344084510300c10b02c4140290f443c640e00090440e45945441d031142d40751440020002c02d140d50005050900c1d00031040ca1a010228006030102080c2c0c8080003e85501911a44c40e842140303012944980c9480c41404800300c4000440324a088846c40e260400b101da090200385185c0c1e038000042070b07100350304554000d036615002d0030840700000c40001d401c12044030040795890302d016081c581441912801d0070250442540302da801010020455825090750350303c032040d00d90000c0700945038241010004030300f1501036001d490407a10011f03c400c1c695500c1011016220780c002e003001f820103072507400c005011260350082e140910001d20160140f0024500c0d002000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 320765953 1250 320764703 320764751
    0x90905060708070c0f0c0e040506010509090304050f060304060b030601030c1e060c020f03011b050d0b01080907031704030b0a0f0c031a060717030907060201180b1f0b0d 74
    0x205160b403c00808980c081c401181d0258070041d45500e0b8212403070107007800700f05500a0f0310300400703400801050007070014119040b11f000340c3d8692010f03190031840540328480d43c080e068010244c09960b4000e4200f6500440e0301c64003580000504012400009090203c2a4402d54443c07503088010710000b01145200e540b0700c800c04914040d420714051028107503a800b45d40c040d100700b10869161440d6102034111034000303184240040c1102d500c0440150058000000d900e401c90700d4000c0e0444c00b0f5000e040140d02541e624001880d50303500d19652650117a41c8900c0041c0042e100344000000a00b20200082c090110090042a03078455900540c0464414407078200400d401c040016141c1c06c02c2503070300440c40c2e1090300c040e0740c0c1e0801340c1403030b0050030303a05440300c1810032000003000620301002c10f112013500e1040d402440b5103800c01c940c4185a00110001511000e40400410600c0340389075042407200306001c084801c10f03990f5516502d40364001845400700a41c540c4000140310075500c03040a04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 320767203 1250 320765953 320765957
    0x2030c011a0f010c030e0406120b0a0905030313080d02030a1d0a081c2c060a1a040c1101050103030e030d030e0a03030506120708010f0606020c010212090d0c0909050607 74
    0x41d00705080300044250214540c40c5040c050f00c2000d590905100b500c888000060180080c032146613500c6210843c00aa290b040d14000810340215602104901604006036045401141591034480c0703c0720400c100850104c07440c6404201842c0c2da0080d5002442c8107000388440004c41000441204601d40030151100d4210b401082d00d0500141000b410f03100f070010b90008150030070030280384203001003001060341c10240391401051300c3c00380c2104d000080814508400d8581a032140d401020940d1300741d00c82c0d580d040b08260781c410300310304290b80301801c2000325140052401400c40070150031240288c00543c002101500c41110724182004548403141851134100125601c0d0b070f03216526255050001020991214081946a541d103600e40e00300070140d41c1907600880d964001d04d4028000d21001321461800e2030400115540003041c40e904460b03040e0040e00c0c0801411821001e503600881d0400c5d88800042d9a44005c2649401e841c00a008507001c00501c0c1101c03401e00f10b103003e40042c90002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 320768453 1250 320767203 320767241
    0x140303180a05120306190e1806010e0c0a031b030e07060f0503010504050c13171c05451e06040b09010909090b0a0b0102070f17010b0d0302030c01 64
    0x82c0c40022454090002007400c15120380301c1e10005400c1e01003a0030b0072000d001724118041400070344205481d004684031002006092241d580158944900744521922004c40d400050300c0b481034030f0001c010024452a0010700c20512902d200350700e0b00144035400c00690f40d8082d00750354000801c886409041c45082245c002c81181000800910050056034002c2c0d4892007c1042c2400c0705040d03805010700000841034150302d582d030000901610054514041c42054a500a020000000c0b9880e04c580ca0356450310305880140401130049190b00200c3d001c00341040e5840320100c0545480b08416010080f10120312401400c002030b2195414504814510511980b02c1540c2c49408543c12100d00e550715903121301030300d00140c0b4500100c1d88a0013180782840d82c0703c0c0c01c00c002011550b10400f0140c0c410010061480012a40c1d0701c814005c0340d803440d40282042c031055019250681c0070080c0040003051105070040455484880c240c0103c000d40d0000c00c107a1411a401e0103204115666528014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 320769703 1250 320768453 320768473
    0x90206310e0c0a1d100c0b0a02040501050403060c020f1c0305010e0601020601051203120c09040e152a0d140a0c0f0e01020a02091005010314091e0a14030318 69
    0x40d1042d04284002d010880c0554403000303002000e0281d40183c02400313004084201d5201400d111b8171051b0407100012041c0000d044680c41d48251825114103039030701403c050540c2d4231031307004204007110300301944110849015451402c0049910321140c0c0e003e0480c80321f0401c0c4002d01035031010303000203006610b500c00b008031690b4000340807411a4002c841032041340b202c000d9801d0952050b2581060700102800422040c102208010009120140e904220b0440da03d00d01c0c907203a90403a0401c010f0400f003a400304203600400e514443e01d11021201c10413400c5100412000d1907444102c42004064580c1103226018100902d02c0e5404904440f082c044001c1810000b807004c03552080c06001e0003c1040410f5240e407003001540314590f4082c11024080c01c2070b60016014009030721a080c00a410902004a14031600310071500654080004149050308000100f14903200b8002010040c8a0304590324082800e614895207000d44d890f015656070305020381014141e081c280c0201502d030303200f0003510b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 320770953 1250 320769703 320769721
    0xc020102191b0b0c031503010e0c12071d040605010501182601150e01120b060d1a04081207090510031a032a01080606030406090206310e 60
    0x384030114091501840c0a0b0b0764040c0d400309605103400141181000d042088500c0c2c407480700840c00303801915051103030500c2107410942039400000d82800190464003094806040182844075040307142c00990707900c03d44448603d0204c0648501007140f148091041c042131002610503540540b03420300c0d0848489080c0120400c05041e40c0c480c180410070f4840074030403c0c081c1d00b0701009441b25400d00074040e00000d04503840d50203030f02c0c0c05001a5480d51000018020035031454462030340358044001813496461030308000c065013440070240c800020541442d1000700c02004240d105911070308249860300b02d070619040880170000d0004051003ca1901406941d0300c0c06001102c0d0309041c0360204900301164414660307400c0d020b042e25014403c0403400e0090703064502c103442400b43c11001e0281444040001141c035018299001c0b81c210b6410070200d00440d40b6074000c3d00410303001405451412950304c0300303000c2541c4900a521001d402031900da484023554904000d0060501d10b9100116007090041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 320772203 1250 320770953 320770987
    0x40b0609031e030403020916140a020a0219030507030804080c09060904060506030c060a1d040204030206160503040b0f030a1b020c10020a051005061005040602070e0a14070e040c020102 81
    0x304079040380415401455442c20400c4401855000e41480c0f15420410070008048500350f11050100b0710302d59404015040960079200044403990043c80b901050345c00740100e8010b41e14200b0307100f051303011010010403c00c0107000c3c000c0d441546010340e07540c0b5020099042007040301030316120b038500301d080c481d0369075450483c40d40083d00404000f4054035030300d00091505c5203c8001d10307003024021450781121f9401c003c40401c10340070490381041c00d55010080000b02d11035400001d41c0301c401445250141075018100c00c010a20171000c480c034043d11489030541e01c0c1c00039442c0c40c0000500004000000c04103008410494680450700011101c58410194451000c00c040c02c1c010a10b0b41c0a6407652442000300c04a455000001c0d600891814200c410161900b00c5202d801141e070420001035141c4100c0403581181c5450f40504491401d080c400d00c507090001c0d181b910b240d91a01c030100c0392900001e4000b4000c00c00303a1980f0141e440311000b40420340c5e82e048a45002c1d6403041c048500e000040881d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 320773453 1250 320772203 320772223
    0x11010b0604060e0d0f050105061305061302071416060f08060a050f0105041a030103140616080c22080105060d08030105090a230f0a06260712030806040b060903 70
    0xf802d50720400c0603c003081a8041021020303103c40e00003009141800019400301e40981c030f094445040110325041c1440c180c1308203560294112610445901150403664041c14003a8441e03d0000b240d4204101610300d0039900842a41c041101c1040800c4025045140c806034002c036400d000100e45400400a09010960701c6510b01131403404c3c50080d003d81c8030302c00301d801030701d0025140005030004c1045142103070001d00040b0345101403c0b00c2d88000400008a0500c506035086d281840455581d50403900580003510b000b4510300c00740a4a40c00c004116082a450302c00c022118100528100c507050030344001500321400b814407403541801040d12042142d055400c00c1e213050704992913114040c0d0061092840d025150342000b091805480d0f030f040000c600414151500c084503455107070309401100d4441c810482c031070021031308458141c00305030b041c0b16441c60300e8816079060503a6038040d5501c0c410074150440010f1018001c22443d40741500c201d088601d420380d81c2504101c520741c04240d498080c0c070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 320774703 1250 320773453 320773457
    0x1051e15120a140717030a0f090f08160b04080a0303020715050103080a03060501030213141807020f06010918030c06020405031605092a070203010e030a090611010b060406 75
    0x45840003294594220008500c0a103800b02d404070801801d00c65207800d41d1814119803802031940020304500e03030403040c020300810030002d14680400c550060303a0400d0740d8020b0000740b2844810004680300810a0500280114000342904207080210f005000d10705070803049005034184000d1110041c0050009000360340350a00580d01c60b6141000c100b210840c2032a00710f00c600301030001c4108071140e000b400518803a0b031000d05c51151a00010340c01e84c0200241c0d8011501c0100c8104980a100c020200303480310040c0176040d540401282a1109034022142c40c0c0250340000d00c10781c6541405c020f44d50045c96280300410050110041d001242008a5800340400c8200b84980c024021254129401050014225010600e41c5c031a1719110b1429403281c0ca2140c07500e103000802e03800c1e14080100f4600d505031100765044018900408494004101c266055035a51400e03805003e400c00003002c83c0380c266258000c9130fa1a210700140507503c510340d281c80a0b41007000c03100c80340c1c440703c3c103a40c261000382c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 320775953 1250 320774703 320774731
    0x706050d0911030f1e06192f0a0e0d0215031b13050901210605070516050c0312040312030203060103090f0b0f131a090a02090702060901051e 62
    0x2d06181c00d460080c0c070b0b0119418050200c030420507540c006400e00500203880c1e2048008100d180034039464200407203a0925904178070300148400700712a844107007001d502401c1f8041d40c13040014103421513072030b88010070708507900050f81d18589a0080c400070280c1c0411100300307580740c800303501280030813000d52201280b050303011001c64503030a10407207680c0099580d41191501c1e0440701c58000043c1265101e524010b0602e1000820f025040781c0100030f110140d03120000f64000b15a5940009100051408081001c00d0040b00c1424031011010020180140024000d1040c95070406042489501120f080980200020400540d816101070600b00d01402d0060702c0b60760b1840140e003d0b04c2c150308000c241e0b031a0051f0200802c01058081800340c0d00e900c0303c49607035988030810003181d00d515038005003210483c181889501024442955842400c4400b5500c900c9090b602180ca500b8050f00e030600940c2040040103c0c2107030074400e85902c2510041c00340e900c1001c96101490000c0d02500c0c40c002c10042d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 320777203 1250 320775953 320775971
    0xf0c0e0c0702131505150a091406120402030c1305040c120201080a0b010210050412180807121502030103050a0b0c0304020f3123040305030c0309070902040909050d020706050d 77
    0x20b4000e401c4024031014102c25200550311b0fa40c01c08a038002c7d111000801c0c00300c42c0200e01d400c1e51500209000802070034a40c5081d10b0390103490721250009004a9052141524411890301c0b170031014801004044030120f11428103240540910900381c21620010a00d8a130107400350781e00c200280d4008504100000e24202e00300b00403414030041c2408503d1b01400c0001748030801c01d081d642454414003581da09594942e904006402c661a54421036206500122060003842d108062802c42d40c4e108038140e0702000c1c43e10b07250700d00340c1e04242d0040d00c1580041031394405202c4000241540518950000c0b4034500d425400a00e03144547c108260250089916052401210100c500e40c0415047c1c041915010f001d80d800000e03000c040e070880c0250710441c0b607002012107081c51090180b030307250700d0740c40c1150380d040180803080c1c100a02c03482e82486495400501c04015100900c0500342d03c20000c5103070141418802d1800740910441c0f000c41d4481542004502d9001068566038101d20001040000e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 320778453 1250 320777203 320777231
    0x1d011d010b300a080d05090c06041a091504050310061a070501090624090204180b010c0b0c12060303130303030f272901061202070f0c0e0c070213 64
    0x801d8030700b101200d12600c0580c0080c418400c01600c00007030743c42000d01840d0340b200003007511050001c4010350050720500c020301c2401c0c4071381110704038440c0d0340d20706904102a0400007070602c0003082240400c080c00180a0005090522420000600340c1100b4480a4a0150001c40052210540c1e000341003000c034641c801c0107000e401403400a90014424402961840c40b242030b84040c0403009040140342a46c0020201194025641140c110240c80286080b0310003103a0003a20788a817509041200d000d0081c0001200d0502d15030145c00d00c1c03483d10317440703c4649941c4102c1071009000d5501c01e074014045102c4080c40c1401c0002525414a004a212002c0c031201c003002d02500e480d004404403403a000c0811150038400c020702c05074041d1b0f0a015400b04c0543c0e07000482e400a51840f00094020001404028050171608284203000e2100615141103a01c404412001466085400702e00e485020040440203144d80b41d0801c40b03a602e1145003d070103500245040c2d0107c070403500c1c07590f195221400d07180c0f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 320779703 1250 320778453 320778529
    0xe0402011b0c0e1e040f050f061005010e01030605030309040b0f0d050609010b01030608060705131a031f21050c090403020a1506030b01060507061d011d010b 69
    0x258030807150015180929211030389070958080e510980c00035900081025281402400c01600c40c00584140d540340d0352030362400303203030911030950305031195504580b02c0e03050401070b80f0b2141501051000e481820280018003d4424458503410507060030020300042da00441140d46201c2c04a0b00007840a00d200c010030701e01038035000c1e440e5003c641f1107008814081d02094441c400c00b0964000c1003070030503200054003120403901560105904c02d02c00a107000c0c0c000c1000748820058694040d205030342d10310401070011030601050500394004018000340b85000e540400041c50301480c0c020b82d06041c24800d0004071a00054240d02000c151900000d110040c000d030427802701e000e00040d4003807034241006540c4803005542103404001414141004070428442c040940b5071002c01400c40f6444c0500c01c40d4203810103141680c0c0c4030b07900c070049000820741401e0b14514241034000032a0a001d400700d00c015010114801a503181d042004980c1117907580e041c00300c40110a0400800f069042102401c2d01d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 320780953 1250 320779703 320779727
    0xe010b040f060801140903091e0409030309150e1c110601080c0a0b0f19121b0f030e03040302060a18060305010e1303080703050a0908040b18190e040201 67
    0x54581038001c1c480a8068000300151000c40000744110000d10030220381c0070f20100d442812a4100b40300d01c07140742c43d013102c0401502e10003c42e01c884041054000034112a030000301180030070307a40c030300702420024036a681e403889401c038642c100b01c500d10580c0a143c070380700c07090b080c40c900c0d04201030307002e490501410110107410f00c80d81c100c450a41e1100c1c403141e5a44000d880c0c45200d0741c00541e00203a0403d541d070446400400800b0820300301140c120000b000005144004024000d0489071038501c14494400c0e04601c810603c920780004140c00700103010030b51041000000c1505101c2c0c0d00d001c0c1e003400000c4034120395068511079600c61107440c00304e44544001c485c2c11903a00c2034010000b106035054000354162040c5404400c200e4a800e001c001503c0e408950040c0807810350000070300c155010b0703400760350300c01940200480e4070b010940e0303051020b901c81d4211090010b800714500b681c003401d04110700d80c0b04000742c8403540a0700c811007000c0320714481340c410b40007400304108c0050116481000500d0b06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 320782203 1250 320780953 320780959
    0x1a0f07030513140601051207080c130b040905150a2d0204080d0c050709020301150c060209150c06070c03020307260301080a02100f09030602070c150c0605150a06030e010b 75
    0x1030f040c002e12540341d103002c0c400e051040c0a04030440d8040200440c0181c210361048004200c285481018000360103000b1400904a59403480200300b140c88070301410300d0306442400a424100c0803004007100340000904039242042c074002c0740b01d440000c40590002c0c00c138480032402c0303c40c070300384400d20000e44101c0d08500c02c0c90040b2100303c000c140e00900e42100d0a0700c1841507071200c1d0b44401a21003240000d11451070b110b000060300312056401a414100e03418011a4003501e05141d68010072980c0324141500401c1c106c0000e0185100002480701503082000d614142440c80c0568500039a41c0c001d1150183c2400f990582c4542c0e001c0e10480c0300c44040a002c1202a203a40c1d5443c0742d551201d5200c00c2c00c0e80074101c00b84403401d52a119010180f1019603139120340542a04546402c002034101050840d6648101100410903524201c80280341e0f424550f10b001d080386592a041c01502c101505050389401240b15280c071a0390f0f0400482c1c10b90b18203140000d02c540502d42c011f4050000c541c2c046030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 320783453 1250 320782203 320782223
    0x7080115110f0706181d060f0d050106080c090c03010609060503070c06060605030402010809010b010518060d0203010b1b0a050a030302091c03020d09120f030c0201090b03010902071a0f07030513 85
    0xd45240c000107031701002808509050000c5076141801e001141c2e101c6c1c040f161526011000545614005040e01c05442e80a8a00c0b10307500c3d03541e9900340c05c4a8058010303074107a034080c00051246d481d240010550240c001010541103524001010f0f0100e9550702a840c10b0120100004001502c0340c01c01101e4280c0000c814041c01faa45c1402030210b600594050b0700086003140040c02c004c9050203009060201a503a00345000c3c00780c00c0440d149100002096401501044000032802080c0013650282c03d620300f0107652030100d1120303101a0000d80f40440455017015100720301203840400c2d503000a40d01820003503654281600082c00e11661386014032b040c03090040f104401d155000551601c0c540e60b58850111b03ca881d00140100184114001130204130822541c1c40000d110b2800040313010700c18186030440c1519140001c1150700260059115154041117020034440c2d120001990304880c1c3c680742c442c9003003000c8004146000100f030071081c15158000f16184a40b218080e60341e45c0c0d0800350140d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 320784703 1250 320783453 320783459
    0x308090f010c08041d060303180121050a05060f031b060918180c0109080a121404080d1e080a0b060d0c0309110603100e070318060c0807080115110f07 66
    0x4401c00707140045c000000c0ca8100008043e4240001129260705440366810005801c400c01141c3d100100100d072201c10100075205204030700c1c03e0107210700a25900c40d020030b992403c0f2041c010540c100d0102c2510940c80354441ea449444a0100f2141d00b11083c0c0f0030960351b09850380800d4940b2009030034600110340800821a66006840c021520340117844142d421642c0941c0c011150305403c3c1c0295000f80e000f210300600025180406520f80303900b0307070800412410103150407440c80d40080c0e00072003090308031141e07005c00154030080c02c0003000c180c1c1161207644411940010911480140642c0d50f0716590b02c1102c00c9a51040b080d910390300c0079400c0911000329030120007006841e03095002c42c0c8001940080703510328603200d826a4841c1100700036900302c0500d440b0b141401200302409810500d6035580d9000803007002407007900ca2850103414003090480002800500c4a0381c01080c142c10000344100611540c0c41680010500c0d00c0d83d403401102c0f030011048028100a09400d034030800703104000c400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 320785953 1250 320784703 320784719
    0x2010309140a0209060402040b0d05090c0306161412150a0b1b01110403050c0904060b060307030507110a031407060209210609010203040803040303090503070212071e0308090f010c0804 81
    0x860003d1099070040d046884500c01d00c82a4000e074058110250018490b000d2074140e242d00080d0310001e000c0403a0380210701c40010905203032082e1507001c82c020011707080c8801550000c0200391200c140c1d40020b858010000d2000350384a4001c1c20a2901c0c0c0302c0f0349500c0095075140b01c1108094107658111566580014a0402504000014203892542400306441041d01c1800c1520100e81e0460007400a5124101c100042c00400420485001d550340201160300c5e25603001861081c1e02a450005690400e02c201078404040080c0403109940110750030000603501c4480c41c2c650071045083e5a03103072105490300c50043c0c000d03185d106030010354030080b8180d02e610042c1462240c801c10700580701c40d0348494040d0fa00343d02c01114007500c1d0013400c002140019210b42e0191803030b14040c0c01940e003801d5695000824403480c60003d20701d03640c0819800d21410700c10b42282550000070107052681c4520715a181c51481c022855000e203d86160000c00c1c00d0303030f4021100c0340c01107540910013690b516244c03074803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 320787203 1250 320785953 320785963
    0x504290d0f0e071409040b221101030b09041a090705040905070e091504080f0d0c0c0308060d24150612110903030304061d15090d020106030803130201030914 69
    0x302800303503c180840010110780c03000000d0142d04014082c0303a095602d64507030000503c00501400684e0502101c0d00d0300344030703190315000b001c23a101d0b4181440007582c440006060341e0b140c107011486099000c06200001b440007468a080c4803090031101c1d603580e24030a80e1403c248090344065000b50902c6507580421801051110035540340285003400e6444910030b0135924114170034400443c08518010401080b19040545862543c000074503141a420181117016624800021310204405201000030036422483c2c140d40f0040c203441c0b01a4000707003074a9402d550041c8403100c0030740c100c034101c2c0c041d01f100d031513013008000c002104024007081d41c0c3d8601c0200781001030300721341e010b45142442d07084242032a44216045c24078010005d40c21915035444e03000082014400c8a9802501240100b10502081c804807829005a04c80e0f1129880c01880c4641080c4424019008591404609100045d0304d80f080c0d9802c890300310020309c241c003a188016001803030404d10150010900c111098048070300090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 320788453 1250 320787203 320787221
    0x905030a1a0a0e0d050d02090a180b041802040e0c060703020601150c1109060102070e0c04080c0402030c031305070506181c030f0f051e0301150504290d0f 68
    0x40d04001c940ea0380080d601c00c43d5000e00d0440b490750000c9409854041c415000707050181400c4400500d84059080000c082e507a40c1e6018005035a01400c3c1e02138100094030507418919020303141405003441d030156a10300c603185914028851580c4841c403040e203003070810010282c2000a40850768810090078007a41c0e903207092240c0011030b064210000754052140c001206034540c00440600d0f201864820000500030090286045100302c003000a0044a04503510f4060030070181400c2d580c6051a90741420a40c01c1d100c010302403401041408050303a00141102d600690b0384400d0801040c2518245080074640e82c030444d40310901103042d008810502101100508041760b00c1c00b81400a01176000b050380d03007801d006d0045502c4d4030140418a0091100d100888424585130b0b15082c030090b60030003a40d0002011030000f000100052050403514107100c1c240e40d803d03040c0242811700c1d04288113160200c0ea044043d00c0c20361072194490b03c0c0011402d41e0f82181c540381080c80060001403c14005081d920 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 320789703 1250 320788453 320788493
    0x130e01290909120301060c0602120411150301181e050709050901060810180e250b0f1602061b06090d0c031202070f0b010e04020a05060301060f0e010905030a 69
    0x100204000b10000a0100d4002041008281c116841e00a0581c0d144040001c2521034507000c20003500b2420410241600c501d10540c10140c00d035084206004084510110a055583c0c00308014841800d8503101000007001082c0301203404866009803403412341c0f000f400180040c0c01c0030b05000403d500000100203440068540e5000d0341c1c2e030340c4811070b000c440a8480f203c6c0d000030400144880398120341c80c074042074040000440c00c0542180d00da49441d10301c0380c000c0c44039200214030046002c41400140c0c0180038243c0505c2c14040c004845040e03c0c070481c0d400e400c1000c25040c0c4c0380115145ca4041d59001d43c00c64400e158590540f1800d02e0f03c8400454440c034240c050300341603280090140c05000310b8a0b805a480700f030300c80c400e6002d90000b54801038050301c07265015039407640001c244400e00f901801b00c45150446034189031040c42a00401500445c1c443c0c1170600060040503400345500c9881e5a0b20301d00449a900000c0059079496019041540c140c02507501c044140b00e604031105112108030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 320790953 1250 320789703 320789719
    0x90c03010509060d03120504020111070b030a0501051f030209220207060b03030f070204050c07050d050a0801151b14120406080c04080607121e0c020d0905130e0129 72
    0x1110400549490b200c03070040120750118a041c581b01d415500c0740b5840f13481810a0005181c828040300d1400e640c0d40c1c410381c848880023040240c1360703146014150040901351a0303480c02c003e001d580504005950b40300001091f03400f14106141d03584100710b03c0c05040707481c40100064000000b20b10080e600c140d1040c2c074000d003808026904d80c20004212013180351000d0140303091194903400c00000e808040d01e9544001030511280300850381c05d005108007002c00e92207460351100840800792040d00140c0c040c50030302d5441c40e51240b001c0c1e000820707100840c1704480e540108440901d0311a0307403084c142c1e06600091045490341d016907030401000b4000d65016440780d01c030070750398044c1c0d0311410701c100d00070f0b408a508800040f07a00c1c20701407480c0030003c015007640030450301c12a0300c0c9011500401c0c06400343c90380e200c0300c10b4a100d680500021040340384030320780b08200340c3c2000041504e619002c40800605580c0384980000044207501c6800c4001c0c45c40c582480d030011400d8001c04034045408850b120f4215 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 320792203 1250 320790953 320790961
    0x106110c010206070518040f0510030c08060603100c050d0e010609110910030b033409140f0c0f04080c12150f060a05101101050108010e0a081602090c03010509 70
    0x14554032a04c0640c0c0c5079490680881d2030038040800b0801202d030050380b20885100b43c0803090088501c1103040702042d103400c0d0319504240e0815103096100f054550400c006210403a2000b0807000100640410041404a65070300300721068400d07426404d000f00e00c0d200c0204004041900244201c520804051103210803841d1103070300c07034414403040d1903008550b2004001c107103000350040b954125006013501d808a921803d00310401c400164165403101450f01c06030651100091188061300059008000000313001096008403003000c0c1030402c405400c5d00004003400c85900840361802d440202040e2035654034031917541d54540c4801e00c03d00c551a41d01c1c411405010001d6044802107100610f08140e460303806407a0709005d070162096400c040c0b0070a02041c1e9071a01c0c00b101541161503621884034070310105d1030f1801c48806800207101a41021202c0702904d0000805245094210346680c0e039440e4400011240d9088200300203401040308800c2048248107100950f0407100c2c161440c203680e5071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 320793453 1250 320792203 320792207
    0x50706050a0504090f09080705070513050601020c0108040c0b220506090307061202070803010b0c010c020706020a08090d0606060c03120504031704020f03030f0c070f050a05011d090106110c01 84
    0x403071190100081c0c0070f00080148050b0340d00071281c902c0520302c0c0040c540480d03071034850003035008038001c0e1460740c0048130400880c101a40342e07070880984d0040c01c20507400c0400c0000e4aa0301e031001c3d070318100001480803505100e0310700c8148009201c10f1003c1d41d03032404015207004150000003500d6030401a40180098241048811070700307480001005000c3d010f003007c0054482e941103440c5c01c41015401c2c0300b0b520005841d8001580039089407540c0c203407502e11019506003581e13110034000007190030040d030802c400ea0300007500075003844d44a421030f5101d100380c00208000d80e030311540c050076081c02c0c2280007c1c0300e41c00c260080651400b075a5030854140340d6201e00c1c005d0311001c2d500100011004d0700300695144003040401d810500c000e061160701c1c90202c000070326540001e4112403000703100041204000f80d04001c0c0c1401000d400c01140841480c0c08005040b07001c10307116640c14098103840c3d1040c2040117501c0c1603264400203105000c1540c441e0f400500100300b0080426840c4110080c4105c0b640c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 320794703 1250 320793453 320793457
    0x10030203120304330207060504110d151d01050f040314070b0c0d0209030604051b031501090b060c0d080709380904061202100503040f0803041e03090305070605 70
    0x40d044410380d92010310b10031880304403200c207400401c410b00c42a228090700c001140000d190b0b0f54007c0e9804102414181080b103004000401c0c030501c0b075507980001e040001d03100d21005e8a18910183e000903c02072070307242055000c0500300074402d99440e180400604000b100c20b942e011f00d019554040c00403203d200004203e204012000c0e200000c40c000088201d0786840c01400c07000215540982040700c440c011914006094408a407241c0221100c0e6040703d0a07844074a8a581e4120010840084200b01e40c600403001030041443e40d0303850303144244941e01c0380f80840710103184010440d0000010850001c04c0045c0c00d498a00019511140c009620040c031070403c0c000c40c0e01c1c0d01032101c10841c060303150010445544130400601c0020b02c01216030fa6524030a44004010000e400e1004459600c10040070550380951002030100c240140808034118503125000b16601429a0b607603a2210705240d41c41c000744065008006016005410400d030740112428120303071141040380d00b925120704003650317030b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 320795953 1250 320794703 320794711
    0x1101050d0905011b081005190816060e0423040201170c0a12020403112107080f010e07030503030f1302040f0c02010b0937020403080403050706051606150e100302031203 74
    0xd110410003402985482070108d025a992100c9905145555801103820041e0a9003840181704404900300b01080d040141c2241030a401c41d01004800c404440080c5074400070003007218214503100c0001d003164001c002030104240704000c03e130781c0c52030f04003c0c2d07404540c0302601c490000341e1688016403456000303009030b409072a442440400a090302c407081c042580c002c41c3c4490305422201c0c00c6021210400d105c2e50303002d0301c008406400704a04609034103007520700700c04102c0c00681c0000d5040010070404401c0d01d0b00b0210bc0e11800d80365464070144103d410045d540040c0d07000b4540304007904d1400c8154002d4544a010760000e0000e14880c904025509404480d4031805c14050802040c0b090081002c5480b00d206000105e900ca0f0710141485007240c0243d04225184c850000d4280207000040103000000c200901d0818a03040034840403a1803400d1501006011507140c070780010000000004401c0540740501500c0e0380c81c84e10a07108501e003d0f80d0711050340240540080c3d45400c0c0e031803030100e07445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 320797203 1250 320795953 320795971
    0x40303180c0e090a020907170105060c1f060801050a0b0f030a02090601110a0b040b010315020c0a14150408040f0602030f070209060307080601060c110405070c1101050d0905011b08 79
    0x20140780514010b40385000404491813809008441e200681e03809040324000c0c400b60351000c1a0b04a411240842079506800c10b80c803d40051000350501c0000140c140d04014181c01984090011348040c0d40103085140c00041c030650809040200909265112844880c0b045400c0004c20070148241500ca815004010790880700301c02c00166030354000ea190229510b2154215040749010380c03034102d0161011785046402651203001082485040400e01c00e080011100862a084c1c08000ca00c0c0c1e20000c1000080ca45a0074104080481c43d042c0b0008200c0c480805000607d80b0305031800040c2070303006000b00c1c0c84c00400c2031400308400b0720000640380d100d02000401407a0020079003c004070f4401c018485d40d03240c401d0f1000441c0422090042d03900a200310307102c20361030000703520b040580c01c02c41d40c0350369018501e400e040010603079010014100710758001400c40000345882004035814805c003c030054050341041d04100800c041540160b81ca165a00d601c607104a00c100b204480255040d504070304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 320798453 1250 320797203 320797223
    0x50109020d050a140c0906090a03050106060f020d230c1c11010e03041406090a1701050f06090402040e120f1c020304030c17071e030f14040303080c090d0b04030318 72
    0x51142c03001c401042d20410003080c19040c030b0032988c0003525101041d00203ca841c0d441d428104403141d0014040507400c0118000341124010404004000d001c8580304c085201c020074044240e009030060488426104040c10b42c1e0f00c0580e800651241e000340c0401c070b000041c007a01040702143c2018842d0314610380605001d5403901e40303409110210f913601150f500740d010408004600981d41c500c0705c9000203241400f001d0100c508141781c02c0b8211803009040d1061004034908000003942d80e5034940c1c3e80580d04840001d02d8800c02030240340b80913001e0080d1541c84c100000c000781c0c0f2007101c00c050480c4095411505004c2c50303008030f403042640010348000300484c04480042d400150740220261038120281c503540d081c801103407103984850000580004008018580c500d05146c4e000c08240c282402900340007202001701002c1402c14400c910010341000240310214500491010481e640808000c26025105140e820040d801311400c1d80c0860100c0c8c5800b0b0204842c900c03d0149207240e03904881e070302d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 320799703 1250 320798453 320798461
    0x203100905100801050906040c0e060f010c0f0507080a020307170c060a03110f031e01030222060b0d141b04060305060123030117011515020f01050109020d050a14 71
    0x801070000070b02103021810021030049040e041c00d1107524030412034040200114105404e1000e40e40f001e58000c2441130301c284081207000d44480d500d04042400038a000b5400b00c0c2641040c41e118161f071800205680540d010001c1c2c4484002035001541d4005c8084d07074290340d600e00d01c0c58030140300c0c00c0d0403141503003010007045a149804800b50991803007078100401c00d0101701c1d00c0d01c40b8560000c00103040003c800320904c44010800600658140c00090120603154115000510200907c242c3c00801c00145200c035000310589800607001400d112449030f40361515032105030041c200703481101c402c0351a04400035a0b840d411782007ea113140d0b006035411345803c0c1480c8045028020007015035050040d1210200c26500b160009003800d001641071460701c075410042d4060160440002d01c0106a041200280f40000001c1c4004100c8030b80240d0ba4100042d9040168140f00748503680c40465441e02c80002a494500d400600c02c0000c07181c0c0402080d510480d6201c01c4030356a0920b80c43d11240745d4006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 320800953 1250 320799703 320799719
    0x105030403121415010804030815040b0d05010507020606100e09180313050a080d05181807030e010c0507080a0f030609022d040e13110406091b03020310 67
    0x86410074001c2c6810346403100400305440c1038039050441400100809000c100c0c0e95081241d00c4942d89100340f803c148a0b041c030b520010305d0307080301415054a003002d804920480d6641c0d41d228401044000c0c1a05000c140182482d03802484d0031284040540540e600040f40f0b41303401280d4811410f0907880d41046d00070f007081072010b11480180701540c0d40007034041482c00140304001402c182003da03804010400c0c1801c007442240344581e0300080031503110644942250343c0213002c0d51748421841c00c15840707004c006000990382500001010b00c40520403018001440c0c3e240d04041c0645000030000c0c80f40144444080340e40303100d40000580140414040c41d003100e03200e0500c0d00640510f9150104d00c50741c5a0440c00100e84c001c60b060180001c0030311281701d10181910200903519400780c18241082e00d890170300115114024000d80001d400d41c00c449081042e442c0314100b54000280c0304021715501c85601c0801044030100d540300070101341d11503880c1e180c400c1c002c03248035495400e01442e541d8a00020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 320802203 1250 320800953 320800957
    0x12020102030409090f0212011509113105090c090105030403140a1d03030313030c05070918060b0f01020c01030e0c0904081e0a0503071d0a090c0e1e0105 67
    0x49046000030000082c00d1012030060030240d60084000c1c4941d0400da00c10000e4640c8030341d90868407641420071100300c00f07002c000307110112400d00c100411410310a010403100351103407050640e80d81010310380016000d6105410361868171190031190041399281c034100002e0110840f55000000410000d20303046501c11800741d40c1040c46420080d0a070031486082d14443d03084402c108000401907502c2540000c0780318500c01100506078091460741c180468104820f03203903031001406002c010581c11040101c01c01c5560002c004022003041244c9032294070054030040b440e41500c0190405e40e014510745402e045002420074141c004019900c2804010350103402044401019402108000520364880038a46442507100d6000940d946c0b00c4140030440405600c030405810a4041c0040000180c000044a41003011810001e00c103d2a140c01e5208142060300742d00c1c1c202003202030000700301c40d070354000300d150510300d896400100b04440180505a607a400b404506000d80b02060107065000b000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 320803453 1250 320802203 320802239
    0x72303031615111801080103021c150204080d09060825110303180d21020f04080a0501050103061d07090902060c071205060705070506061908100f06090203060307 71
    0x400d2492a03595402c046800da410b80d14082c450026100440281e01d4004001c04c04003405c4c241001d50451300428800c0d40850b0001c600342d80d120202d001480f9444000040c01c0284d050159030741d079214078641d500d840400d10081c01180001b00f0225106000350b0708240b103803051141440d41c0103000c05426840020f1500d2500500480000107141054148000c40c42241c002418540b0000c1d80440c20b0f1501100850b83d00400420303c10305004201541224136906c4164400942c40b000041c80118092003103030b02c80c110074803031410104100901904414100e84c0959000c01240c2c40e40104000c6014a016141030241c10400c0180f0022100380c1c0200100350002c2c0005060580c1c038900b6500c6c064454100c41d001003041000394042007010806580e00801c5442c00c03e080181315520030340d5503400079024910904030018841825040115400300402c900c8080b1812498031650810013050903021700704440b030601c14081251022030003128000c100c0900140900d0b89049041074604006038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 320804703 1250 320803453 320803463
    0x19020a0914040201230414120102040303051621020105160206010602030405090a02040308030910110708040e181c020f0c0105070f030e0607030509040b09060906060a0c050f0723030316 81
    0x61700c442030288410015001030250380c900c5079030203000c60082141a90300b02000350016801003000b8400240e00c0307400d4a00031441310011840001c00d9240200c0395840711848106c0728140508403550301c1d40c0c15040a8041c080d40d6007140c11580548a00700c3e2615002d0003068003690003080100124100318a10070361042e401c420042c10b107900c81e6548800742c1d0007a12000f4041e4440d039035200310004940324480d1910b90070781d0386a00c1e00040b40c0d10403049000c0c0703200300001c2e0424000065180042e0000c00484000c082e401d80307108080745803c986560a0035515100144100803000c107010f00000f03121041c1080503101e09081c040f00d96500d16100761003090403010009914010540d40c0c4652001d07000320342c880e0b00c84036120040709081c04210381e00740c440b991082c0310310018030050361070340d842c00c64204600341c0300d0315603e120664041c0c448004003003000b0011300c038004500f031000501146140643e0030720010b039840c80b8400288c80c8c500421302042607900d030300104040c00b241c58402c10b08208162041d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 320805953 1250 320804703 320804747
    0x50f0a110a21052a030609010b07150504050d02160e010e090708071202090a021603030b0d0b0f0402010f0816050a090503030703030f061d010e071119020a0914040201 73
    0x20010b00a079002900c416010150501c081104ca0505080c02c2010840340c44110781980307000c10001c2c00c0004184644100324100265a105001c16104c01242007450310740144994141454a41d076a0920000108014000c0e14038000c540d8800040e501d0840d100e080c10400325034244803c1c1590044054824a00d500c680301c80010b0904080c0144401402d0031207080030401040d00501034103e9005040c008890f10400516041030042e0321414178150b05494005440c3c0c40300b0000c500d4143c0d98207400741c41244020208094040b8601d40c0300c1c070551003a690401e204000c02801d8034071000a0f66204401654017a503d40d4040c480c1000d440c1c52122031800c4600c144d903e0f0003081c2964440701096001989520f21000301103028040c040040801400d1460105117a00000ba8610410b0189034489004880072480c514030452400c01e0100b4400192a80c0e600702c1d0015103440084400100d00400720b90380300185070419803181d081e8401d5048440c040d19030b80c95004440303910094070350508001c7c40e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 320807203 1250 320805953 320806007
    0xa0e060901020a0f030206070f050a200111280305040302070e130b0106270f05010513080607020d02060703180b070c060203090c011707300f050f0a110a 67
    0x10084c071402c0d60f0103a00130f8034050801500c01040c003141d0504413824490100646400c440e40311501c7e5260103005000d0341441d00a540f9000c0c090b003203100c003d8425a8010546020045580b00080c010b061281c2001d00c1210000d03109400742d4504075005405600001d6041062480b803e010940c0490345803070050450030300395906035408500b03070801c0000441c1a9001e11880c581c6621180c00c500000011071081441d10040214207101802124101300b03004c5031080c0c03003241d00e043c2c07000a0701c00d070403e4a00c28074018000950314142d50001c0c1006100701d0b404106964046d00c501d0094001401c0040c00725a09611003500c030803005812032081005004000001c43c5140c400785010b0520071014000c40350260000410403a581c1c460303021030b0100034060050141c2c0007551880e41d07540d451a01202c00707154604158550710b03561591007441d82400c40b07143c1e1400213035001d280b244403407144084042d10b0b44a1044e0443c0d00807040d81d90070640800c4854103240c003d040315498100074501800711094 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 320808453 1250 320807203 320807213
    0xd0203040c080f06011a0903010204080712021c050a0209280518060907061103041203021f020a020a0201181a03040b0f0c030a0207170304150c050a0e060901020a 71
    0x80100e805403144216000c081c00501028080030700825141401072045504204c1e032101000d84080500c00050400500d440d00741d10b00b0340680740185120030990342100e903900c850007140d15421408910486540004c2c1c1c050751410313080b0740e2240340c008000b03050054940e824887e0303032680075060404203450504001c08469000300326615404050070041a03c1c2004003003220510040700c84890306402c62000c011080d9000906142103030302034030308007688030880c0444074114881c58000c0301444060000910070316800055500071141f038100708040d03030001500d1050480c01a000201c0c0160800c07801c0b0400356110f00000d04103d00301c0e41541c403610b039031012085507030b1072118110003010708040200300030701203215080750340700d201c1035000c0324203160840500e07005100040c081c2d000c159005c40c14405200302c12252003002030842c0300c2e0075607904160402d0440b00300040043d80ba11810000c414000500c0b030702c00d4450304280307900d80300380340040c40c41001400d8000810b07103030451140f21040c80100d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 320809703 1250 320808453 320808457
    0x31b0c05090928111e09070915050424121a130e150a0912020a050c01051303060216060617060f0402150a020c060301150e030601290d02 60
    0x141d00d4600401415003c00c0c8556103110048000c0440b00d1001ca03100408144a04011201d403182241e441c0c0000140c0441c58941c0e00c1c0802c01140c00c000030104000c001504141d1950940310407803c01d590343c00003804122003520a5009043c0b0580d00102d00c5010700c640319000c4a4048914180350300b2002c2c0304141e40040302e0300c00c0103a02454600644035001030400100384c01c28140ea6440c02d01040080620780c80c0d842651054140c075444c61007000600e4640c0942c40240d0603a484810f01c2807492907040025999820010140da82d40100c1c442d2150a602aa00301d41c02c5803145410003550314a15100d010080d00002030300a03c1114903000800095100d125050280c00d40c074078810300020410322060319280b03006200c003011400c00028040543e440190101501c1c0c0c080c00b08580e920010f03c0f08909000264080f5600040c0120001c1462402c0c0d540602510050f90380d1410b0b0840441c04040d581e9100703110355100340c0200490101c41c8003c40303283c82d43d05186c03104564904200d42c50480f04a07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 320810953 1250 320809703 320809711
    0x10020a0905090c040f0e040f06051816030c0501051b0604050a0b130804051302090307080705150301241701030b011403030a0f03020a09080a08070c0b0304031b0c0509 73
    0x40c801040c207204038038091942c140c11a1400040c1030905052001a02d000d050714018030046110030030014080101c42500c000000b0360060342031245090242502e25040118203540704513005480c40e603a103448440c01d1110403a0b801040b0b0304209460a001500d250b400113001360401c1c6c0d038072441519121403c12815000c0c921500c020942082541040d800445002d0030401013200000a42e402041e814025201503d00466000306001e4101c0e188800038414005500d405004d1580001a080004580c2d0021544142c0d20850040103210100c59140b0003402103840d900000d0002c000c40f4008007428052042072030a120341c2c0344428803a22074110704242d008a0fa0000c032180107010302015400f414403800b9098004500303002e5207940c090030b40009040c0302d108240d80407840d11100c1d4801c207180e2000b4200d40703050310090092070500b0011603001d444c09803100d402c03010700098903048510490b4860350700b50380d44500e81318000d003041e2600c0122003400e84261001c00c2c000304555460b0321030a805 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 320812203 1250 320810953 320810957
    0x1050c01050f1617010311040902041803020f0d090b0a140d0506010258030209100c020303040902070c0902041212020c13050910020c0f191502030910020a 68
    0x41d140081c111050001103110840130800c5030009546403114004e20581560380c00320f5042c281031841c00202e00182103296020b54480d08041c1941910115501c0c5c00030414029401c0c3d4081a07560300b485c40d520703103c01c111880003d075083e00c02c100403c00b820140041d00c00c1460300344412072000c480603030103030042c0c010b2703c520310b0f40d80d400c3c4a01507030108025400c2030254082c10140701d51405646102c001d009400c4094201900c90505007152240200c1f0062460007000301480c001c81c0f58010020b40155240c40d02a030415681d50409500032030b4452951680180154030309820190040042d4000403011145402001c82c08110054980003501c06410b1a01d1002048076481c1000304030000040e440f0425034100200982440c2c44544180b8000740090101144ae0346a20101519200c0500ca28400f450710200d4140407803032000c104900c01e00464021551408140d06071008450340e010001803424042050f61809110140c01071a440500d05058801580c039001000303090341e008000b1000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 320813453 1250 320812203 320812231
    0x30d0603121106070801050d060b040501080102040603050f010e0711010603051504150608121605240708090307060b0103140f180609152206060e06010503130204050601050c0105 78
    0xa400c2d8028420118006000300400f0681800766001d402d00031306005440c0141c440312514420301a1541040c0310001020f4030400c199030b910200760307000350014003075540040e0070000450010503a011b04941a6803528050021580302c4210646583e525000c00d11115500c1c2c036400000300f50107004103a00180541c00c1b008061506140c80a20500c43d10740c1b08c01502d2400005100c90b00001900308107483d1500f8010b031f542c2c40010801c5450b08a0914018440d2103108252548a40d00b0055140c09100c15441c410498450400a44e1490022104902e56901c14058103001c2030094200410440060500050b000c1401c4407420381f08070100d9002207001400001d00c0442e145901c004406040c0e00e0024010f24208100e01c162194802900e810400404a006c0346031060010b65105c18607030081d0f0f02d403030303010110703d0302001506544c0b1542002002d04000900e540d401241121301c945810b92a00303002c1c495940c2048000d20020300911304202003400700c0e1100c0030007403080038010085403034254 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 320814703 1250 320813453 320813483
    0x180e1305010c200d020c0f040e0102040b07020a051005030f0a0e0303040b06120106030203120a1709010905070914063a0c080705060409020d1b05090306011421030d0603 74
    0x441c2000d2000c0d1084a6139021440c086281a80401d0100700301c030b0225020740115843e04001b402400c03c49813208019440000e00090822500d00108019803080d24040d10050340c68080042208504200c81d010078004c10001e0380c0304507048440e55002c0030001c0c0000f607503003110200030714603003088070107e0781c085c0203000784030152501200c5002030710380040007440305905540c0440c0c2c43c0c1c00880c443c40792101c4003080901c8214051322009042208424811185140007101c0300c0c0a040350300002c1d1054003c0f0348010501d18000d010300b400c02c0c4a410300200803516541c09000d0b01443c80c100c0c0d207920007680340b40c1200000128040d0a001f440c260710450095030b1600b441c1031000d82d9507101d4880c95214140c100010f8540702c0c291000c44901010041e1a1405409e400002d040c00580b0754109202c50503010507500d8004003d000d01c8041a4102c515903a20b80c03800e41881c228a200e2180c0c0100c004001c80d803518007481d54000c0a5000c101540d0800450304800800d0340c0b080e41044404401c488441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 320815953 1250 320814703 320814737
    0x170a0c06061415032508010603060803040509010312210b0312280c050d080702061b0412020604030f0501050708092a0d02100302030106030b01180e1305010c 69
    0x1400b20392002d0440d0751500000207440401e40c848181c1c044401100040c440b42003068055640a1200d100d02603040d44020002d0483c0002d01405021a1404901062500001090f00c05899000c0c10010640c0d00310f88491582d2141041002c1c104001c0461000c562281c2013121004854141004a00000d0700c00c10581040c0d2100140390150710300f803000304589940441c50942031043d01380d0aa840340400718080316012040d1001412912802c40f58110440c0e00c03c3c076a038400d1015509580454039194802d2600c070100214101c2c0c034120a200602c8521142800e400b030151000300b00e0303413500c2d03541e644c0d000c1c0d403000403101520b55964980c100304c21280c10081060740008440c0103040074500c24882c44003200d840c0359040f02d07803050300c0b01c10300c0d8141c480400c0d01811980050002140380b0305808010003035030003406510000303800d092602c4095401804a11240c80c4401328902280d8102110b00c00c000000504aa1101c81c2c2007290343c1c080b4100b88100c101d140a2940d900301088800810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 320817203 1250 320815953 320815961
    0x5120604020f090406023109050405032508042304090f080f09120703060c0c0308040b04030306090e010c030c0c05250f061d06030105060a03110f0a02010e060708090613170a0c06 78
    0x3202384030509100400c40003600100860f01d01000c64280305986840d0707c1c02c82e0b264000c090000034907901000501060408548250703c0a00480c0c00c2602c40302820b110a20040d00c00c020340040039491001229000a5140c0300500b110550400b05141840352401c000b43d00440045141e0348140c128a0b4140140209402248030307541d40c1e4100399820403280c0d83c0042418800030300c058050080d002c04581018440d0700904000c2a0714603090000d08034200803e8000d082858071140803030f00d40030034600c143d8000e008994140c0d8100f4050700100b00d5409802d41c000c610980a0701220400710000b1541c0101700401c000600f090341e6940c50132640342107030403401420b0605210700c620703001d0004000c00c1e0354000440c0c40b0003845150100340303070419484590442c0600715500c41801700204540400076415072003480c60b003400508640e11925100b02c01c4d5150b032400c0e10750302030ba508100c0c00180d400d1100c1c11901c84803440b580001c5151000e416034040241c0200200e0000120034035480b1013407200d41e000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 320818453 1250 320817203 320817209
    0x4060b032421070611030406030c03020d020f030603061006120f0e0a0803010911040b0919050a090c091d041b0504021801020c01030b0a21080c0705120604020f0904060231 75
    0x5d081c00c5000030001619a01d00541c4651820561514001407905110360103036101c0d034504403401c1d5207c2c614006501c14903003003210713218040c1c82110005140700f808084500c044601a450707605134100d00904040c040c1840010080c1c000380c8482c46603c16a204201e00c510550064140c40d840b0b50420442d00b0a59003900d00840318814180f1040c13008540a0080b6511140126801c04841502e000120f04c007200c240c2c010b40d48804041e80000e0000d02c030f508565010b0a031030366041441380e1184264480640301030352910348441000300242c000f820603a9100c1002001500d502101c0382d65000040c141e030300c4a0600304404244841c242541e580401c40b081860100f4207003889500340100100310011000d02c9800c00004403a0040c000c03000c4050000315101da0440111550380f0141040a44d59403414420310b07000d528880c20500d82c4a00105031a030040f42d00822241560036020f040110480e8090010307a1002e908100040c075165032070302c410720026012402d002c402d40102140c02c42c00f03042e03a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 320819703 1250 320818453 320818457
    0xc1f0902010906081006050c011e0b011413140123070b011403100c0e120d02071d060f011202070c0f05010903050303160e03060118050604060b0324210706 68
    0x200a00000010414902c0c0589045140c216110030080107a10701400b0301700070ac0c40300700c40102d80004041155801c100205002a05c3e40d214900f41d980345656540305900b241c2c1688080b00c801071000300714094107105600014540040001c0b8400c2408141454208440080480004480081201c0c102040d4010000b14801042c0000c0070008070381c90b0855041e10728001c0f5507401f405100da0703005400440291101a0052094035200c00d20341d595100e0102c0781c0306c0980700c0c045000448090950002081200341400100c06840d40014005902c0002103203c2c14030031415954181c030282407020744580c0f030003442c40910861070000703c1d91400103240c1005042010288081c40400e0001003213035001240300d80d10071190102400e08450007021052625414015440009280041c245041c408808030b04010845072325001b041100b21200c41c4510015000e09100089480d200b60701e000407001c0f010385180d008801c00d82d0000c2d0098004103100211044d80342c1041c154504100200b0f405000c5038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 320820953 1250 320819703 320819717
    0x405180105030d110708070e0405060603070501140901210c0f050f0a0e0d020301020a05030a0f02040303120b0406080d030e060a090f0b0903040806070c061506080c0c1f0902010906 79
    0xc0071a8441e50541080e00601141451300f481c0e01da010003a042c0101041003e4860440e111004620602002c0d10300351440d1041c0c2001c41c155141c0840c80c1400c80360b058440a040320780800c2100541d4003c0c41ca0700c0d050001d52030303041801c0e102407508820581981400056508596a4094010782000d01c00c5410050f091001c0080c2d8280001101c005440900300058050500700001d480380036035400081d015400070608414458106001c0d500809104c032062080083c648500e50887c05140320141c0011007800e282410b00000d60710855042401400205840d519034448503c1c181c127003c04030000a6071603010407400c1400f4411790341c01c149640e00038054000da9844040d4405d2810b240540030680750310100d80f840c00304008840061410005803000c42c501054081c2c0003055440d810340c0c1e4142800005011640300032199401e8603129140c80d007d98546030790003d800d82190311815101e05c50482000c0041c801700406100f240781e0448045045030340d9200041040380e940e44004d0502c461 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 320822203 1250 320820953 320820959
    0x2011401050a0512030d0e0303070906051c0c110d021c080412050306010c0b040506010e2503020c030d050103060609151215090b07080711070501020c0d0602040305060c04051801 78
    0x1da41d4400e0850360101c6520741e00350203007600d450640c4030b0306d1250180d06160030240c61f80c0d4071020000d54030420154842003406a40d407071003501c0324415504103031030792840c0c0340041142a00a41c42072940003410b1038208200050440014600781d0251805000350f40322003a400c150003000003564145150320b140500003418a070703503200301c040b00c061054000c5c04408000100300da40700d060f0312a225600048402021b08103801e04075100c16081c0242d002076000c46c2c0003d40c0c844000f0000098040e880c1c5820540124070302802c80094100400c5900e01b070004104081082c034080c01000e02a5000f0301c000100030740ba104041e412030300d001d603448030740540c203202c1082000f20f64480040300703540014940c10301200d8410f81c00010305102d04002c090080210510030695409146503106031002d44030122400c90108004d83c0d42c040300d00c1000d00527403028107030828a050440810f030005c0e1107101c002d41032944a5442908041c412141100300b1603011504010902d400d4901c200c540245840301001541 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 320823453 1250 320822203 320822209
    0xc02060705251a030619030b090d051c0504030e04020f09091302010c0f2d020108061f050c1c0f1209080d0207110a0902210c07030f11060106030c0201140105 69
    0x104083c0d000108000c000070b0030b0354590300c600494545008407078810132a00c0b403806079180c1c2d1003034403501100e104584104d452075020f5000c071803004100018070300c40d05105003566005040000c10843c100100386441c0c660390f0300c1e14006000c0e0352281c0c40d601901c0e0050304043c0a13000000900030b00c07429003031005202c09030b47c1041150f500181c002c62001c160110a04050a96a21002040040d04c1001d00c0710030010604142114405100b41c0c0c8042a54546404100030f810405865840281074103440c42c404900640041c0031400c941c0c0255405440d070a08c11001004e0f0348071515000c030701c01881140b08203600c400e440745030343c482180811031a4811340342d11080303016a810702001154000b440000b4494801c02005114070000e01c09400f1a449240c10000307504107039071041d003403000c0782c2c1c500c200b2040c9030740c20510803401e4001807401d08219840440d0000c07400c00d00c40c3c2c03e02040c0c42c1280414002440028082d1400761004218080034400090854010184140500c0e8101c40180016030f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 320824703 1250 320823453 320823479
    0x907060c1e020d030509010215040b060d050a0204050108060f01150f110309031c12090b060d0221070312020c030606040e071805180f15070c0206070525 67
    0x1a080400032040c20801107000302001c05006010b0740c4800e4800d031090816502c40002c040c049000c0e801d4900034450303000304080080c021740f0010f00c0000a0000241c0c10b0410448500c039081c095401c49813404c0240c0c003c20201d4100fa002081250041e408015110880214250041c070f59a18944440f401510000380403c0704011503004000e91300b1007009044000b002030b1400e52100070f0650340000600d00a40001901c200c1580020a1080d084c280d41c5e8065032089201c07454001d40b000000c2d541e40c0d402c00c010a05501002ca80c407d0500c003422030014445540341c0745008100c2c0042c540203055080409050014118100841d0301180e40114a91000b2900d00d412080954000c90310202d5001b5560800d0483d800c4148542012015101114550313003000380907045000c11103002c0b640c5201a592030f0301014440440c142e000c0001c0030b103240b41c081e910a910469034500f400d590016070380003410383d41c0000400c2d102c5c0d50040400f00b180040460802e11981f6035110380e9912a40781000b000100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 320825953 1250 320824703 320824727
    0xe0105070308150a0302100e010201110a09090902190902250201271e17010b03060121080c03090910290c0a0510060b0915090301110c0102070605090706 67
    0x400440351403c0b070b503122641c5031000307541d000f490100c60b80c0320240c00800301c40b01202000e005600b0100d017900e481d541902180c0c20148103070b65034a003460410080c000070b8000840200e8004089200c0e14940180541b1720304041c10048002698401c0380c0030b144803c440c5181c14524030217050904050050f81c01c078540c040f40c80644d01407440c81e1100d2620b00c4c600c07100980d1080c1d00304011607000400407194050445c0a07151604894a201802017a0035400c907180c2c20f040d02d1b0540e00000061020745c0380307402c00c440c20304410700c00d00028150a40d11405e00d5049440103403101c0d800401c0041252400da5036181d4070074448924031161a2802541c41031011481440005025481610b400742d00c40c140d0884a000b02c096041b200307101034502c1c0c007a82e22400b5202c4148031a1400001003007440c2000221124004010a84045105031502e112901e41c401217103a0ba1540d0b86503d44140f8401401c041c2610007e030900050704c9036060f0800c2020344a004100781420380007007100780892a0062050150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 320827203 1250 320825953 320825971
    0x81b010f110304121e090f0f210c030804030c0905060301090503030a090f060903050307020609010507020309100522050f0607050a03052506290a033305070e0105070308 74
    0x71004d0082c4080e6140515078004112000100049075185600041404210341c052180e0301103e030360711207506101e4111402500d0042c1e0b190542030035280f940c01c109403801401b13110b1095000d03589903103018255100d5813048507003109180003003200150b0362103807a0b40000141c1c02844803034929500c890b120700c001441106c066a0300d4030640188401c0482e55101c00354881700800c41200c060038098600d810448102e80144102d100040c60410117004050040105030000c5007000420001c01035600c0100d03845c201080018001c00b0010407441e10b03603000070903a040d01c510002d4103010038001484912450345004d04001c011078000680002400da1207690180307049611142c0321810658111240102200c4282045001d01c00b444400e6000c2d007501c860754109200809100e684020707109900000c6150b000071070000420200b040c0f0481c000e40004080640031140044445041c0040481c0e5010020503584804000805800c540340c0c44112030242400d90610490342c1d13001309164001406525 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 320828453 1250 320827203 320827223
    0xf03050a0903060608100b060406090308160b0a0501050f03070b03010506031003140d030b1005030f0a020912070302040c021906090c0e0f0702010b060301180513081b010f110304 78
    0x3950307114004800145501007018802255074840043e40d4030149000440c88a02d812070483c014a00308003110129612910b032400000e02d1610307540555000300040700780040700014803000248c0f9512040b441036940300b8000485504120030300c0700100e44070501038001d40c8a28014490345804c9000e89045600440d01c0c40d03960b42c1d85660b0300c0c0210849031f00050010041404d80400404007040e16282c40340070b96401c0040c3c01c050420012280c03020503c081c0803600420208007951306040c22180d120320408c80c054500546900403407011408050600c48a81090b00240114a0640101001103440c3d20003041c21004a640200d40020240b07070042c50103940b48144002c2000444c0c00c440200007451031100d0510f01204100d8000500b12a200015441c00b181b100540c0f802a003070384d0580340707074402040e8110b56002c0c4410007030402a240441c0200d040c07403140c00003007800000305859005808024100641d0389021820f4a1244030800b4440303080403140d51180c00f036201070300d60181c5c00170312400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 320829703 1250 320828453 320828467
    0xd090524031b0a05220f05041d060117060901050c09120a0204060b040e0603010905100f180c0602060709030f020d0201050909150f1f14120118050c070f0305 69
    0xc9650788241070700c16110049916400c581e049005001d40c030060040d030064560700d80d8542c0305c14105600941a52104107030b400e10407414903510900c2d822600e003c0b45030099207550070052030044264442201c00480c2c0546890805046c08415000101d180081c403617402c1460007201c440c041e203500e580c000e01c0c0100c4902c442c080100610001c4c0c640103030040182e6a1074044904040c0e119010340c090386c10f807500114445040501c60346c10307000e41120140000c0c1540e10340410141410042c0610000c0d11424840e030303140c100c8009280d860b8404c0303916a0761149801006420128014a44801e0007100d201c00c001041101901c0d0300c000c1d0781264034021680c01ca00c01600d83d03025201d442504100d03034000304103060b0f481c004c01c0c801400b41190303100c800d42805000c00215906080c02d68403040240c04410700041e0045001c002c00c5001440f01e00c0c00d120140096a2035004264454010b04208005035584070415200f0310350054864050a40b802d551030f1a506500a000a0000c1c10030030001011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 320830953 1250 320829703 320829721
    0x60e060f03031c020904060b091e06040b030a150e131b080f0a14010213050603040201111c03061205030a0f02010f0207060b03010c11120901020a0f050d09052403 71
    0x1500d5070454120303d80301884071005920000d40050030811300491a003100410038501c400d041d03403074078103006291192408844861000c41c201d0060107941121061101180d410040d50284d032143c501c03141300086a650640032004400c6103980043c0c100f54808090101d1a00b505003602d8002e07800c4040240409064904030704912642d0380318604900801c4030040e10f120020408031a694000c020400081c1c0302a00784500305d1254440d8040352a040860405c003e041400146078810f0050500001c2c0041d415515400d100707840804082d014103a401c550401d40e05407007400082d00207003002c10880c030f00c10340d0303001d59a1280b84c0804051001c2208043c200300c0c400d41112000001200081d910fa960398074240010300b201f0b101103442942000e020900c1240f0450f849030100d00440014001d2049800300c100c0307507500502c0d07940d045005100c200c034089100d10740079030071070361040f402001d07004804003000300755600c56004103110720220b41c2482103018002c0390054468102800c0301d55240c0303c02d950707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 320832203 1250 320830953 320830957
    0x2100e1501060206070305100605070201110703050a030521040b06040506044802030a0f230d1812030b130e1c05040e160c0c080106090f060e060f0303 66
    0x1000403800c14860001c40d207107a0114005024410a0700c05106035100d102c09040c08414900034000080c1c030a0001001540c895000c40100386c407500280c3d030360180c0b40e40342c90b410704003d0201038001c1400041c42640b80d000b41101958450f0040d501210305003840d51705c500c951b203000742a952042c0c1c5c8550103d41ca542e95540200d02245c0701503411b64402c0c840b48007034000001c0c08040c40424400122041000e500c1d9a1008030418003141e0285242c0551044155085410703240c40e00308120881302801590b03550311048182403120524140c1d01c034200030106100b82d41003004082c0b841d014030903080b000501030032108000c00c003030b5003008501d904020001c10311443c0b8500e800321440303082407140c4511010101e003101c41d0600c2401001154440000c0c1030340d0900c2107124038000d002946000540551054a081d14014224500350300b45503070302d48514440011703503004003c0c42e0359a03100810406501c1e1180d01c400c4040000f0a015840c58221001001200141140e00624151084808a035401e0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 320833453 1250 320832203 320832223
    0x6090815010b090f0a15033b0f030a09180c140307050c0604081209120315040603150b130605030319021e0a0b0f2511010218040609050702100e 63
    0x100c645d0155444a07004601c2901000d80800f0070720f407403421007660028903c4107244040159250307400c4060300110080341c0d04c0459a807980c40c02005d16045410005000800e1006080e995410444d400c015003c880d4894100907103030800d06e0103915104442d001800e100c801091150602c0d100e560310041039840e031280503141c000b50b000e11002c2004102d5003201401480c01c4041c10396950350b550700c0d1201ea4800400b00b0380c1250160501c00508084100120f200100c80068004590f0950b80da0704e00c007a85000f82912000161501140040390405003a000d1080303011980520900b464040841d4403842078505410440c9102e04090f00203078001c010307944505003403115522400e8400d0682e65152044200300301c4001e4a4500450031a01d01c1d16031080c020701584c000c6444006e0145040c0704a81c601c1c44030a018058a040d403040582d000b84040c10903000d502c0320032040713908400d081008445c0e058105518442c0b03410284102d80b54005521401c00703c09140010b8074403001055145004d00000b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 320834703 1250 320833453 320833459
    0x1d030106060504030b0606040315090302070b0c031b160b25050d09080607051911061006090914010e0709030c06030c0305060a03240204090606050406090815010b090f 73
    0x3240c0000c100c2e0b0300c01d005104070f9000c2d40c072010f9251140010000c441c8107510000e041c903e0b451108200250081d8401c0c1080d5100c0e0040314840355890040c20441d8000501d0342500e40c1021a09046201e0f01c014400554001100503141d4003208829038500c0c1820790103441401c450101e40c4585900c80080b517180e40a080100c89964601c4a1518694034900c0030720442c001340440c040080c040a001401c0ca000700e51b030751a098140072486207114403030080d021040c2c0c10019002c3f14020001801d104080c01890f8003143c558100307041c1400034004074126444081e08520301b062403000a44d2500030641550f00f401024592622a1b0300c0481d00300500b9000a0071740e401e900f000080d01c0b07406030f01003909483d80351410702c0a80e070303602c04001145546100c0507000c42c1c001d2108144072000090941d02d0740c0305103d0010f00702901c50f07003658100c4040d50030a00101e00700280500400d0b0308084407900403c400c1c0c00602d180d02c0b155900070789505040c0303c0c0c104009004200c080c0c540c0d9070501600703440c490103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 320835953 1250 320834703 320834711
    0x3100603021c060b191509031a0601020118050303011a0903060c16150218120703020906010314150a080615060a030207021e0a0503010c081801060f14100801151d0301 73
    0x2a102800c0c1c41d505c1842210500c4104031024818a03010b03000751021241c021116280d80c03020154403c20040004004a0465503251081e9094100900311303a80c100d80100c1c015512581031400000d94948510030030f94811105011340b000341c4c0d0b00080c6042d4032228a5001c1071f226940460014480300046400500116042c840384582040c281d000d0802040e84490103400c4842c08014480d00340c09880340c100c40c58004010500240c10070141458100206140009040203c4441112004c00595085c4030300000040741c88503618103104804003410800e0003600f81c90506a20342050342d01c6003404640612400305108032294003943c1541d02d81c035000340101c0000010803144140c7d1892801c8120300c40e0410482c081143d00301442000b2a89481c3d441d030042d01c2d140e145115403281446501048070f0b6403928400324040c85804601001007080310060f1850b9580f00040000306020b6280940130004c07460010008407880e008a44200540b906090170300500100d800318100d107030300c0035a40d0190f0030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 320837203 1250 320835953 320835979
    0xd060b21061b04290f040b0304020411030c0d050403020309060a0503070906090b070611091c0510050f0403081e011202030f07080718020d0606080603100603021c060b 73
    0x1010400074818900b8402c1d05141c1d51481001294500590007180d83d008801070340b51040c040003841d6031040380383c42d00c20582001141d01541d071180d0300c143c10030038a402000c0180004c40c10640100d45c1c42c1400c1c549528294542124550490700a0126207200d140d21140032405143c024000c44000460142556540755152000942a40c1c02a01d04038001200c104000030454170581c08601900d000341a200d1400040c0e8903030314084c0c540400b40048503002000f040c503540d900d0326104070741d00c6a002d035902800940c6040040c244030010718541525802e002c1040849031080e407496a000b9818181002162540000d0040b00064984c002101d01244e100100724080030101601165100310304444400100d542c416403101014845e180c0c141c0c1c02880c00f800300d0714607100c05c0014403444610041c01d207a14100010182c3e40ea07035004401040e10b00d024400b030b90074144030110b8230a890700c0c0c040c86100d296501280e2010000b05002410480440b604000c01c1500c4c5c2007040404d000502036120196 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 320838453 1250 320837203 320837269
    0xe040803041a07050d0b0a0528090504150e0a06050405011b02030f0f090112050a020702131514030c0910240813020f040c0903060c0507020d060b 64
    0x100540e015154010016800e0502042c65005a8451081907a510f03092060111041000d000d0440c142e41d8400031049000c2200d0703c039071040441e01142d08611207040a2200e07140e080e90002d5802c00410541090b00704000f0402110b95031070740407980c3c0b40024081991b10005030030240d00201c0140b2250904090106020054001004103c070054048060000c22030703041c0d0f42c0b0720541518049140061014840404041d005442e2100c810b0510f0000c64490300040c0302160710840c0c4014100307601040f206e0030b505201c0501c216200600404004800104440b0700d002c4641c0d105500b600312904603026540c0c0c03014003c203d00c440c80581060703440e0a11303040c4c0d031242031507034001c0203000c00c1031300b0740b4022a04249000c030b40c1d001191b40300e20100d904c0b44c0440c42c05848981e2800e07a0401452180d0005949036441030784d044000699400d900a401c51401c1c8041d49c400c141d0340d00c1001424044080940e941024010043d644803a0004552450f8400b282c8141c1034030701d010056180d074641c0d8202c0c8103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 320839703 1250 320838453 320838457
    0x8030f0a091e0303020717060609060a0510020102030a05070903050a0b0a020d090b0105041a0d0803090a080f0915041d22030c151b051305040e0c0102011103011415040e0408 76
    0x2074440c5e02502c1d202a124481e444195140c10a07682c2c0b80d41c00b01002c1001d03410101c580d10341015014290083c91603c500102346c01e01000405203005030760010802034941003d11030503820045c50718001c1d00c000d180d074845e00c1d911302c0c4213500604481d60210108880c43c0d00c540c102d440708580884244041d0010303040801c18031030b091081d00c2c040c82c205042014100159408000ca68200a0042d459038404d5150100707944c0008181800ca4403070341d8070000100340e501001e0b0400d103003007c070115620010381041c840310540180041d844002c0502062044c0902c404050806891001c06100e00d0b030741c0d0303c4c000920341030010703081041c07000900d03206d505060b0b03c0980600054000c0002411389400c0d001c0201c201c54503c0e034480702ca10314145144245921032002406030039070b40040c05884640f9180042c4c11070303142c102c000404c1d81c420070000e04c49580a0082450181b021840c0d541913615103113980500c1c418000b00640305002079401c4910000300305e015103000c0d020000408240b8030b0329103003281480e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 320840953 1250 320839703 320839709
    0x60c020c2d0406081507030b0603183702012003210106050712020a020301140109060e090309040e0321040b2401080901060506120a1508030f0a091e 65
    0x4034007080000085003414050041201c500700020f20600c0d00c07000c98080f8089020f03008104040c1c541c49035590581d5241c0c05140100d4800041407501e50701c2d050454a000d0304140104c128004031170404d005145080c6080003455001c001514059842d40300480315030410104070a0324000802c0d400004410000141003048101020040840b105103840712036001c0034840c02c0005501088a440005c044810385c02680d51640111035480b10154006803c0d10780c05015494840c1e99100100003402c030350701818000f0988581c0c169014146040d6042d283d00c11301301c0b014002e94a82158840325031080080f12001c80c0881042c070702007011000c2e100445142a107094071280030000124aa00d00303110480c0b00002d085076134042c0038161000c01510144401408403100b0356a410000070b294852400070544103044d50484500c914009429508a80f454007924180d2038031810103010f1114008103c0c0c004081000c517664135542d09020485143d58a074005900f40a03c0c000d0b0310a103810f41c2c840650070303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 320842203 1250 320840953 320841019
    0x170702070e22441303150506010e0105040602120702190b030403090b04060503150406050402070303090b0732190e01020f010203130b0406020f0a020d1706010c060c020c 74
    0x1d8070851000c0c1c0d0303c81c0c5094014804401e1102207040c104690041c004018030a6940700d0a04255960740316981258107140c07006569540b150200152980e118442d10401c1c882401c04904260030010000c0d0703601c0390240f500340000c5000540c1c2040d55038184180768a5155101203081e10ba4481a00c100550003d0750210041101c3e410b01042402c80b40b000d58090b54295600c0300e043d60f841040144a801c2180d1609410581c0ca41e4003181d103441d01d00003403620a001e51008244102c0c4d0f464104003410005042000f0000c41e100d80203c8402c01d1001c039180d0400481070190344104006110b90f207445418101da174254406034000d02000d170040050810705009030241c582c1c000f40c2c26102070a074030003142d4142121507441090800600710321003c9405c1800f840005081900c05485010390703511030906800940c0c801041c030b0114a50100901c084400c1c803040d6066207003041c100103000c400c603210380208401d403100b030707a0045207100300101020070800401030240d2402c07001c10b0444002c0c402e240c0c600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 320843453 1250 320842203 320842253
    0x2090a091b1401050a080a021b0d0203041707030302070e07020106050301060e0915190e070b0409050609090c030a23070303031514060d02071a010801020406170702070e22 75
    0x411513020750305451201206440700802036854100650082d0302000314005a0140111481c8038007404005100c600181d540041d65260b0a0401200c0d1240000d614070a25078030060041c070000360701050f10000c99102c1d038010860b6032640f040980c050081c1d900026007561a1260014005056611040c060700c1a00181d43c461500c510140d1400e040441d104086501d01124900e00001786501001d010721054040d50311194444508281c294021761180907000e40b10342c00d00549140104d5400e40000c5d51000400c24541054003281c1c84820b880d0001d868062407450300c490500d5240c034030220b0f0491a506480c00c1039101d1401400a098a40c586002c0030f103007200206081307203030181c3e840e204540100040d0030b00c2c0b420010940690320090b400c550303042844c2c8151b0901c0c030200b55458040c0540e44000340e00c0b1030914000a10794400c61408010214101c0c0c140b101403034012a01205940c5070348803d40903503540701000c0705140c0c1410f03108a00a25611444028022000d004034000003d012104e0307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 320844703 1250 320843453 320843489
    0x8031804180201020a0b091002040e0103050c120d0e0f090f1f1d090309030604050708060a020306010e1003020c0a05010504060e1c03020a020a020d0f021008090a02090a091b 76
    0x400e819007031500003030250b40501d185001040140b5500d981c440c07013a50440700c06580050407c02640c0103588030308800e00442c001481008014800c0d2824407200391910450500801c0405a40d1001d580165003480b090000800f40c680360425820051400a440a10380342055144441c0d50302c1d08030740b0074002e0014642120b1005001060640440e8034902c82d41c20038070720080140031107000150040d40e5511040144c2c41c100d44081c000075101c0d6000342e0190001d03d1030209001c1c2004070050007444658410000c02c41140c0c1c200494414612050391118150480f110040e00244107440c0e200c055885403814030410010305400183c0309038814a410311010120842d0b2941d10800140c10403566000101601c60940c820303400340140951703503c12507503100741640214000083c2203c0030342d0420402050403095003441100700c036081c0c02d585400740d04e900e801d1950540710003055100034401d011160101f2100d08440e0449107000d504401d21400010035503041d0b020b404002d2084404002c6151401d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 320845953 1250 320844703 320844731
    0x12140402040f02311a0c06010e0f07050901090801050a0b2b1e080409090b18030405040b0f040f0b01140906040e0903070507090b0411040f150908031804 67
    0x28a403c00354918003d00821080c000d03040342c54503107054400e241030b500c041c001a240441101080e03807000c61550305d560790450000e450f0030000c05802152400342c1d04030a0003c0500340304c1d120303640304c107461a1503525508200012124003820f54018100e43d82400184988801242e000705503411007120f0321402c1c2d0307070079000078401b0092141c032519503040400c850501147c01d800d00c0c200e12444032103105001c40c03150b64600c40389070040d40000700101e90740c0000400300f200c01c1c5c6240303800c407901390311b0320101244200c0b5660b071f81d2059000e0540a184c03241c00d50200754441400c01c8419020044c4248110407070b1112800080c07401040950006030000f6103c440c132030080040b510034040c0038002c84d140a040840070306601c0c1d00a0011422440108500404290188500c6020349145e01011411415000400c015100341c1a09881d880600f044200613600c107250f045011201c417140ca94000d100c1d10704041d00e003142140d1041c0c0c40d40c0000070b4543c10014000c460810120422242049400c51400311 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 320847203 1250 320845953 320845957
    0x80c0f0f0d020f060417010203060f0f0901030206210103120206011203080a050403120f062c0a0b01030605030318010306060c0803070c210e1201020f030c0a12140402040f02 76
    0x54581c1008007144601e000d4240500141800d002c094506498659030f0080d894082e190071a0300c0c4420b9602100f40300c12031900350740c0500101c2c011a142c0d040300b4207a10000740308440610000b1711500000400088000701002b01036410015004030700400d603940e05202c8114120001c0c150b005005010001c1401030400c102000c06030b40503600e5205980d00d0300c44650044ca0301610580c03e110154000300364038001030240700c900e2030521b0340204040c0c0c5851a046007240085442c0311407020040380380b096680c0120740c0554070a0540201182d032010550040c0d0007003009400c0740341c02d8040000c2c242c82040d41d442c1000343c003480a980070070100e50386034011039504900030780c002c3c40310104201146042d4480c4d003000c21001d0003900503801e12403c880703401440c08403035401180031411804640e0318030703d000607108221851000c002d41ca071146a500c14a26403000400313001c1d84003c08291842558800d40c0b032100071559200c010040480600c01060007004104cae0200e114504060a40c95080002c1c02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 320848453 1250 320847203 320847229
    0xd020706020613060216140607031b030213050a031202061311060c1e0a03020f0a02010f21020a0e040e1c051602060d06030b070306030b040f0201020a0b01080c0f 71
    0xc042c00064640c0c00040f0f800e00703405441598515020322030580c400c0e40c3c4050310a0107034824108110075010614255090500c0209a0400d0614041e100600009684c0840e03501c0132840c940183e030303000354012070700820a10750003440d042802c0703500110800070030503207040c403c3c600c6070201d840c140e56080c04c0d9202c00c03280c0b900040c841d1400171101095801c10401030b0000c54800c2c1c003507810009a0740040c4003459542e20001005034000c107a41070600d074051004644a4194401900c174660640e00045d000540840c4880200400c0c1040110380141104160401501c0c0d084195940d0008800050088820051540c801e03890109040e07401e0000140d0102c2c060a070000f14100c0b003100300c1041c1c40a80281c2c6282100410b806070070001a99403800034010100c403010006441030031400d204a80390340050101003890700d41842030022802442190b6802544480701c0d14042400d813004034146190074000404400300384001060303080c1c01180c07081c0c00a6080d41c4001069031820200100c070030f0710306 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 320849703 1250 320848453 320848457
    0x60c270a030f03051b030406090608060a0b0309120a1706010c03021e0c040212010306062106020a0c12020601080d031401050f01020c060c010c170105180702070f12050d020706 77
    0x8410000181c4410b20708258901909215040c501c9034001140d00b80143e900c405155080042c040c4445030700007504802914041c0307455a05490942c0100341d140780c107402503030344112000c0700117015003030704200d04024040c1034400701c0d40b15400050040c000e41c03002c400383c0402c03841020000d4140d51103044010804e541560041540c00c41060a041c0c0505000014005038041d2004400e41522a4001011110300c0c101c3d803560250f00d5800d040c0100c6026400c903c1c80c10003040c0c0c0c2207112540c1842504016600000300503a10000b5440581c1c00c113440d00002011840034101160001d074010030b00300d041362610025200580c0b20544c08404844800b40343c540c04920460062189007007d9400541140040c011210030719808400585607400183d0382d00d46980d1903070405005180d1000602c0c00d04a2800000b52540d410600001c04251141076107401d503030680c2000802d0b4620070404030004100d540301301d450341e503103c083c909914078407000b003035500744100031401507000c1c400201c0d130040f1a855 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 320850953 1250 320849703 320849719
    0x150302030f161205090c030a080c0c010c03020304060e0310110a0305090c0d140f06010f060908011803031a12012a0806060a031e060501031a06030105011808060c27 72
    0x3c002c1200104070240c01d0100c1ca20850404000e99241003241e0800070740070300d00080e00c030800f83d050249407162006210f410080c1780a1501d00094000040e0b80c1901c020341420159a00c1c2d4002280c03905030500e4002d25a64107000703400c0069800f0100030881070403130340d602b44a2a41c0380c0d000580e0f500440c241e2160030603041402203010400081105000301c50b8171050701e103041a9944c60760b1808000313030070260076011450380c100b003503503041042c1c0d90052240c10000e000c2290700102081200c0e101510107828151203003a2040305e441c0d280140e01040c5802000341049000b440400ca0080590b04040380c07080078003585c84141405051452442d5500380d80e61160307240d03580c1040c400c0a4110101c04420725407581c2d800c00c050854513240e828440c2e861800052101c2c030740400102138458500855010ba02c0e803851800b2a511030208881c107513203007800c01c4040441084000c0c190851203602c4546680100c40500960100d40d8000b0014546400c0380b0384521b280d04004c000030100c0171314140d0707801010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 320852203 1250 320850953 320850977
    0x30e0c010905280306020a1e09051003020a0201021b071a030606040504020a051215130e0c0120030304050a06061e050108130b150a090b06030a15150302030f16 70
    0x4080515076141038901d840d0f41e0304035600d40d1141c00740c2c2c01c10034114000caa00c80001c0f17900b0030b1200303580060b0184180307080c0511903e03200105a18204900c01030041640000700382500a000350100c50101802c2019185504180300143d40c640100d400741c04055078143c550080901c0c030755420749000d04c8008100350305e8a46010104030095108040344004d2082c00c0c0000400366007407401d150b05c120f140c119005802c4c3d02c2d03e810028240c1d1020840305940707141c09815202d14500180b0032946a00c20300341f01614010141402c10700c030a60b1010b045c441d220000c10030082240100d08104010302c1080b05024145d201e1001c541c0003071003944208050598903404100d1584101300e042e41001c13802e450b14000c0919500d40c449080c0c411940500d1810000000096506020000300b004014a80042000703003aa0000515207210203400130791210b403210003000c1c0c400032000700980102260000c500c0b500001e524050040e40044034101541000c00002900c41c51229038064440d441c16500d00c3c100141e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 320853453 1250 320852203 320852239
    0xd080106231e0409021c1806380a05030a0314070f08040b072d030c15290a0308090618060a05130801090b04140102090d03030e0c010905 60
    0x2100000b40188050b0303040c141c00e1807403040e00402c0501007099000d0307503490001e5188038950135a11513841d07865140880208a40804808101c042c0d5403108021460004060341103108541010002e0301c1c0707420010410b001c0184900b01c0180c940015101402860b550308105605c0e02d018040184c08a414440b003038480c0030034180204211441060060a403280715100c0031030a811039000071014240c00103003001031010100101c01e500e8407606a00740c0307101d02d042004001d0680240000e0034020703000ea41c402009404517a03c0c0000500e8201040140880300715012420130002c0342c0c240010252034540f0309403c0c0f00c0c0b41c2209072030b0401141c0349003020050034841d90380c2c010f0200c403c02502c461a44029075542a004007484c80c00c664426480703203050b11900008c03031890303407007642181e240c01c24800001c2d02c20f500007940300c1e4102c041904448152009140640709042520380c1c07240c45115100c0c201a0550b1080f911211110111442001c01b1001903c0341c00c06801250b80c000c0d2610b402c548080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 320854703 1250 320853453 320853457
    0xe010e1c170d1e1503050d0507140d020c10080f07080402040b0406180e030403021302031306180c060e090604020c0c0d060504051501060503040803040201031b020d08010623 76
    0x40300000c1c1146000d88019100703046840005072280c40030200c031a180d043c100d541c010035a030081950054101546151345540c0d41c0c8050380000001d002c00426100180000f001d90503110f0361840303041e0307540c864516030025191902002c1452184420203c40515540700e0b42c00745119050903407144a0580300c1c00c0054800d40300003041240e0043d210900d041154980d4040c00c03000300200100254410310201b0305a0075280100c10000481c0e00501c0100051307542c141c031400f000c0c0c0c2c1908006980385ca0b002d0451542e00c0c00c2c000c0192a82e4102203500c03030b0300020384810021043c028600c450745e0544900c0101c680f040c045d500b10380d0107508007011800b245003d0340240854403100007110b829441460206a108640c1003080d03c1c55030395142007205110307041c466444440a600a03080d29503041c075402038064000a440079208100100004e01164001d0388842d07220000904c3c44070300c80440d480000d6452f155860307a2000160200e00001e1140d0140c0850152115059081c1c400c00d4810b0702488915 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 320855953 1250 320854703 320854733
    0x20612070f0f09120c030503071406070c0f06090804080303090307060f14043207091103070203030c0d020409050c0a0e15070602070c050402040b0c0105060306070c0609020409050d0e010e1c 83
    0xa807610b280000004500304005c000162041a0301d650ae805500c00701424240000d0800c0d040c0f0140c030143c0c05c001030407800e008a4031640420001250655810284040d0090b0741001c81c1c1480000140540c569000000d003650500c200010b208052440d1940c400b550b5039292000d503040b4000e008203001560003600c9014500c1c03d6180c9000e80b4601042c6032202807000320056071103800c015000e101242e064043e50550f1042201864038500700014000d55a03c0010020203110b100802c1c05481e49003aa01281c1c014050007170240068185076258110703a0f4070401c010310104201215068083c03d010039920032012100b200e2504080035a20790901a50010324121103084149002041c0e0780d80d1031001e4000ba2103043c801c1134543e020140341c0c50031190081d0086100c0e40c4124200712580740c0c4070800c80c0d9a141e0003040803440d003986102080c054032030814001c1140c055542070a43e05544083c10a44041c0c09980360b00c1410100c10070700c59403883d07030031504030310203800102c007400b203041d1440050030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 320857203 1250 320855953 320855963
    0xb04181101020f1605120708070b1e030103030806120a0503090609010903050610150e09162606040b0109030b06010804020a080a060f0534020703020612070f0f0912 72
    0x2c2c99503840203840c1003658040183c46034070720f130990500ca1402c10424070244078a03d000140350b51030404c0303041969000f15104035034a502001440c100c1010300707484107604446540258940b00d584a1501030704400d001c0f1a258001d210004003140203d00000e580d00748281c00801451400c1502c40511606034001d03c1054103100301c3e0b0728008001441003203c80c0c821104103280e00461030030406100c00508ea5007504104120080b40f060b1520b030f480c2c100241c1c0050400d004101200004c0c10b00741c440300380514041c1071408130b00500004220440140b10300c2100e04440802c40b43d075a100c019550100c2d6400050980e006510000d00350754042d915980d00607000401c195200f1b035880508618001640204541c02510381c04a45e01d8400503000e8160019604404ca10174100c4440820800da10700490110b8040008410b002001c1d00a1025201a540140000d59224064403a402106805a0345240040d011034400742c010707486451a00082d11565940d04101071500b000c0103141241e0070425a8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 320858453 1250 320857203 320857213
    0x9130c050f070609030212032203140c010e01180b01030f0503042718020609010c11040908180301140a0506150a03091a0903040b0f0f0403150b0418110102 68
    0x281c18440c1002414007144140c40102d4000501d140c001c1c00c0074005046008040414030a2081101e02c0d48a201d080440c900286035410500c0e00f0103d444045a40b04020041c0b4000b80241c003681c419007084c40b078025050020b000300c007525041044a00d00401020340f4070701101c801800010054000d504c0100e004800312418180c5850385c1282c40c0058a030301051950310141c2915901249008038000d0043d003440003054503444e07801048891103005a080d0420006810791401c00c910303002e83c00040b00004e031081101900900e012112a40020403680c25001030802c80b0030546414002d01d440d50b00003005243c1c0c80e4551080500c0038082c090300c49540456466002c3d00085010806010300c1c50680c0c1c0c0206410080303040900d100c100103070511030109900c004109243c04000200d81c2281c0d5103800c550340c2c8410004852b42e0b00e000302c80381005104400600041070000c007008507104988080010404905803808000c100d07040301600d48078643c60200c2010204204082030801d10340c040c01914 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 320859703 1250 320858453 320858467
    0x30405040b0a0b0f0711040b0603060103050604091e0516050307030305070804080d0507021002072403060b04090501080609030307141c060e090706030510030b060102031b0606040e0309130c05 84
    0xc3c0781c00401020080010105441c07013401981c0e410005c00d5172007900d0410042c888034012428610000341120b040c03580710f10201c0c106460f103a0044a0594220020f00500074614507000e200350103400c400c0d161807092002e085800c2e03402da003510381115001002090381c21701e150b034241c4560b00042c000340d03150300d014000090012418414030048000559070a5550072441c81005402949040b10074119484602c09100200214078110059074041d100c5440d83c00603080124013421650300015820000410000385001036600002d050306d1180080e64080c4c0c0e10200c481c1c0e9030303010855001c400100100c40d05811503aa03103000f032000350700c040c40075003107000f15a01c010181d8102d540141e85410600d401c02a04c6070052011801600c002d1505204600b40f00d150a00004518000074000015074004aa0719a000300100c403a0700d100007000c802c42c0d184107150a130311042e04440c1c2074000d505214820710310480c08400ca90031800c000b4036920000311000100b00050001802840a000017080f4034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 320860953 1250 320859703 320859719
    0xf09030b070203040f090207020d3e01110a08030402060336071a070b130f0b060a05010906020312180a0b0103051501051305040201030908030108062502030405040b0a 73
    0xe4440c109680081d0740e00d600e402c11034400084980e00c104150303071040c4848401a900c8a66440865070000c0c0c481010042030080003504000e0011501c48006000a04202d49181101070fa02e4200091b00d81c540200c01a0311425200c100c051001407060340104000350051030800301a50b00502c8071003044c0b801c0d0001408200d100944807803455118035003020001004042001034101501c160042500603000d4824140594000d4641c01450f8401c21030000c0d240701411103c150034aa04030b10f200c11020083d06150030000e9054411030300541c480400454294007070001c5004035021a4015885c00805902901c907a8201601010082025079682200441c080021031009402a4480d28495146161051608c80440b508079049400c0380d0040080ea40e941e12101c41e011100c607c08503080c3c0e101d100403001007030800802003030b000001c8004164a1300c00200303175114a000b599140014000000c048440c0320b0010002c4005920400007401141010b4102500507500580a00d2440b61200d80c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 320862203 1250 320860953 320860973
    0xc0504020307090e330405150a0512033105060421050703050f031201090621030c020409080a020c0114030a0e0a020d06020a0f0c0209041e05060403050910090e06010f0903 75
    0x1c0fa600117418007915062a20302441115088104815210a01e1000b100032a10b13400c154402c0900c124515000c80c0034140051040701c0000c0a542c0b1052074010000035110703c4191025070011416071060b4010035681443d00458059808400c10206005904040c0300308208000f40211600d004409000001610402c80f651121050501a50716105080905501910140d20466600381000b03001c004000035070501580a280810920f80500c103103080c01d4a04441d4201c000350031614091582d000d00030804041c00300d0001b150b0030754034040384000c011a000c01609506044d0040200085464004c69520845061101a0540380960380c25000100d1510341c491b003d8800c0350b0001041004d039640081300d1588420030f410310510303000d0303180c000c01d454420007040101000e1000050711800a681c45180d1040d5501c0380c00c5548910b010f203402081904201c80d107034007a142c140490303840c140c00740420605840c01558190915a1148011503a0883e1146c1100034072000a8001c004a081280c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 320863309 1106 320862203 320862271
    0x50603010510090f0602100b03150121020d08030f060616080a0e1906020105070e0303030c07030e06040f030b0105090f0a0b150d0501030c0504020307090e 68
    0x18042d9500c28842d08030b0a0340b0344d003440380000c030310382e00055000a500700c81d50103201e84480141410381d166801e031a040d0701d10303400400500004032440a14906070301500c0d2580e5280c5030703d40109042d03c24842c1d040c1c805c84800000c120001d807042d01865000745099401e1403070503001c902001e0035150622001050001b002510220151042c02900c0c4803600003098101c1c6401c000800d2001910188185c40141d4200000a071205001d602c0f00310702d404014010703500d1680d803804c80104580c0710038021410310044900180458031010060005000000d0868210074198141000b038040141c0c496841120403c0c104103040d00b03001030942c0c00c00d916244c0410484520300020301d412408074841c82c2d4041d000f184038403c401260700941c0c102c9014030b009082c070300c1d128010702041c0d06c01100c83d1000324400b1081000b007903100b088096441102c000000084500880c1e0700000340001070 = true := by decide +kernel

theorem cover : BRFrame.Cov 320683453 320863309 := by
  have h0 := BRFrame.cov_init 320683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 320683453 ≤ n) (h2 : n < 320863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
