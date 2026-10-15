-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4228
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:55.825817+00:00
-- url     : https://prove2.me/submissions/1d90c39b-95d1-4134-9c32-a9bb10ec6adc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 760251798 ≤ n < 760431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 760253048 1250 760251798 760251809
    0x102190e12060c250f03020c092203030c050403020d0c1505040b090f0423041401020f04090f0b0a0e15040b5b0e0315060118030b0403080a02030709 65
    0x10258611640c13401d42c00c0607410b800b504d890380c4441c142c3d09041e4085019030310540c080c1d902d0215a240c1281d0940d141c0c1d2490520203c02d19840140d20001c0d1282c2c103c14494075071480c045081c9a125000100010340c00c080c21100c030005c0d40c2042061301070640d80d01c901083c990801c0c0c3e05292130848556018419145900d10030b190b1011000c8169031190300a0030341c003104040221342c0e00091121160440000d44095071840007035101c049481a050003103900e07100102d10300f242420b25050803000580b9042e10612459074580254a9940e01c64500490041c092000300300300c0b0741804102d19410070640c0c7d0400740120b051402003911038aa4010901120100310811002c00709169005160403030b800001c00010020941014621140c031307004100480211901c0915003018400c0030344142095060031509604608549205600e10103034060f8800010b0505c4100d00d00c1500d01080145c6580e0001c807841c00040d0107020600d03603c03048280d1320810060302145113003000c49001e44420441e01c40d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 760254298 1250 760253048 760253077
    0x91d0706080c0a0809071701090303060f1d0405010e0d0c0b060607110d02010309050d03140c0705060f25030f05100b16050a080a02010504141507110102190e12060c 72
    0x4101783c0042000004014a0946c94038461440b5034040b2a000c0c0920b0304099002a007000301c04140c043d082000c1408031002d904141daa103404500028255020007002994103558412045196180c00d0103e0200d403481561a800d0400040c642110046805020280a55010301488001403458040d0510340b641c2200d81e00c400840a20048029160086006009000f10011990180c3d0140c101c0325100050611039010340d0b803a0054802c0a014055002e8001d6100c1d4010500800b0382103041030b00300ca032503080482c0b21428020806030a80780c404030b900000f5a5a00305040c041e403184a4590840c0303500301c40d507070f526103041c1401d0788134003510940500b400d9190003040d0410004008621285501030b0700c960300d650030380074045d0080c20207c40a4403140c2c090b815a5402e40b00c08228880080303a40e500313441558407410740031505d402034031100400541d030030050190044284000c1c4200c070112a43d907451480e5880041c00006000c91340e40341d605900160074024180240d4003034401c045520508d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 760255548 1250 760254298 760254301
    0x306070f1803022806080f0a09260d14090c0d031e0914010503131e0605101a0c03120705040e1612060617060f060a09080105071704031404091d0706080c0a08 69
    0xf0485240c102c407003219a80ac404040200304102e0200003d0b00002c02c01007001c10015048962400e01200308030b072a19110f405c005400c09031851302e821408042406842c1101c58003200040c00303510082400343d24400310312411402c12680030040c914000702807080c40c1450842c104690b0500c400c615801d40100390071039440d1402d1400d100c00307912003851600b040d024021400c10b051841c12002040c002c40c0706100c007600307039900241240e104651b1000800c0c0000c41c603045c44500041d400c2040a000700c0d04001041100050981e119030541d030140c8640400d03a1a04204500003074481361b07181c0d05c0c011206041002c20401690054070401d1600003403510b01c1803c0c0c2d20400094070408402e0100c079840303180440e407020308541c08594601a0b0344484020000780e102c150041e2464a958007038209035295070400140081d1143c41c00c40c220b800d044003807500701074440340c01000381c60400001001c80a507080a5485504040004a000340103070b091100d07680c02e080d00528502c3c4140014a01844400f10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 760256798 1250 760255548 760255553
    0x304240207050d0e010828060323010b010504150c060e01050609060f0121090c0305072d06111606020a0201140f1213060513030e0306070f1803022806080f0a09 70
    0x40d11f5003900c10302c80f80104061a264540310960103080441daa1095903002600c3e03907801d030144618000034405031102414549451074142c1c0c0e8408a01f04030080140c07580000300007540c0c50003541d900d07222020000c00c891070034074144529620001c0c58640704410015100c0c10b2a40c00c40c6c020076000380c0c810100981b9546280b0407001414100000030120303001030380004117011002c03a200e0207440d40c0b003420307036400000410b0a020741c8464074104050b11480c0041040741c1070080c907814003000389074001d894814020041000c5045542e900480c0507030841c0590038115030b0b11100c3e8051010100445d01d05002d203182009105000e0890344485000699003c82d0f481d09080d824801c2a0742c3c041424401c40c40e120f555007001e0b880c414411404a5001c107060126440c0c0405c8aa1289101e50b503511700c0119800d80481780104454548881501030310310100c0540c48031040b00702e4104c90403c00c21120b8000324001c1c0f8081c000c640c860020400034a06109040d6554460b030754010031110b1000c00d0220150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 760258048 1250 760256798 760256851
    0x3080718080304030b040c080f0c130b04090b060102120315010c08070b040c14060901080403030b01050408030c0a050c060c07060e060c1509011b080604020304240207050d0e0108 78
    0xd41101649100100f07000041000c14000030b03200311300c56070300e0040b035640c0d809110b0341c2c80001c01da8069544c0c100c440b4003289810054410484040c4800b00480d02d5092000401c0131030300202c00642d602000c450030002c003540c04106c001c0046002c54206483c5151511000301d04e060442d680c40c0c10401c1102820080c8031201c1c059403070f400c5e004440c90300203003840d143c04404258503218103c2c262101c01e4107a0303110300e40b071019208507103410b8407108a280c0d02d0390b60440040c24900006414090184008190b01004101921002944000400040005040c824038044140481511543c010040000381c41130105030312044880320300740b69222032080340c0091141d000d112152401c4d4407560801c2000032000c03041090142102d50700800140e1000c01d50040c00345994007010303022440c880e000c94054100b5600450f0302c5409011503443d203203410b01c507100c0c81554032549038400f95001f2408506110050100f41501100c50512b1000380e4900c01c00600132181c000c0034083c00000c91280c0681c3c2e41900c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 760259298 1250 760258048 760258097
    0x605180c032a0703020c010c03020a151104030c090f062702091206070806030105070203041e031718091006180e1801060f05060f0d090b070801030618030807 69
    0x20740100700304401c2c0c03100a00807150400c200030750041c41002d102400d01c0d400355100c9038102d90564050b18400b0007135241e0760740110b5000c801c910856920705d08070202ea01c0c0280500003840c0300c1d084180304d06180480c11002c2d1081024484542c0d0316203c4100700021548920185074400454504903d00300407000d10000d00405a2071034104500410801d044e40d8041080341c41001d85441d080d055440703240915007218400c40c0c0b00130140e4820841400146065411031902282e1000d00301c103140c0e1240e44051040e400310307040700ca00703500c003242018090002540040159105a44140c402c0c5004040031141d013105204500c00d015643c1200301101c164a1255000707080d02403159501c5046c0140c2d040120707203a40132002481e510300400420700c00e1300e0908078000c0310001080907007014460000030001d40d03c00ba010110b40356131441140006583c00568900c00c0c0c900c0d1300d07080c00d15807460070900e041d152079a96004180b40201c3c0c04c2000a5000711103030f5000462860304a05600e000038018002000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 760260548 1250 760259298 760259341
    0x4020c030909090309131b020c06030a0b03030c010e060603100e030d050c0912100b0405040f02010806030f1005010501030c020a02010807050c1515010e15040302040207170d0603060605180c03 84
    0xc08914a084c54842600007030a030710211100143c201e001c00f1422a09e64403208605640800700300041a01c07401c3e01c0d0032050030141c00500b038a2401d28020130150859000c2040f503041900113070208582480c052000c1d03000400045c0c8248060f640403081241c4038850300c800b0380d00e5940c0c1c2d407000c9920400c0e82d00c16550900b501404254000e00c0d50034003160b9501011084482050801410040e40d00f0702c0c2c06031314000c0c2e9201002c1062501c1650040d1054480101119014071a0800c0b10079080340c2003000005030481c4d9140040c80b54100400182525454a0310a0039980039109600c0183d9020b500f250f481070311860030580302c144030002c050030400c00c84d5211040e9081c110503ca4040c00c0e00ba03900541d0781c42601c4800844188030140440c200703850007103d1189005200403c098282038004088072845600c61403128103ca154154560300a04031024519617142d005004100c1948201c902902c002c44411800c130030f105124401801005150301c12600c0040003141c08009d0011401c0c4e821403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 760261798 1250 760260548 760260559
    0x90f0b03100509061305100c02010b0d06060519061e1115061804200310050108060405060141030a03050c010f0606080c030402010c150e010b04020c030909090309 71
    0x510311115007000d068281c5042030a4000c00b004035055800402c010140950710101038440314040c604413000130951201094155501c44500030002e03078542c003100d031aa038811750001905500345001e11001c00031111071451020030522091043c203810403680300b01d03c102d482f4807105a0803943c0045034001040c01400c3c4591080380040382012102021003031003002e041c0d40c4642007642125042c01425011b1b80c0191159800382e81e100c01c0300c4880003608a050ba4041c00b140c040080810903002100c0099003ca092508060140400c1280901509004250611090031200802c000005580d0070360a2074061110104002d0801c6c080140348102514000500342c1c1c000c800070b0306001c0e101d0350140c817140606518000030310725141c4407403090005840541d07071504580d070749208070895958006081079040c0000240784034005804050122107010704014046540130040c003010b42075500c04c0072103910650060010015200d00002905c4441c90304945041c81911a6044542940301c1c0a0f0802c0d00034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 760263048 1250 760261798 760261813
    0x181206010605090f0a240309080304030806040c030b031213030606090207122a020d05010e100c0201050f34030b090105061305190909050d020d18090f0b03 68
    0x241c0000c0030380460f6000350303400b60950001d401044420106401a09580b00d20801d01030503600000345010300802c00782c1000201c016a94881d403003141c000321000c80014051104201181c10300b03005100505c0d0f4582400d00503540160000303929010100d050046902011402090100c4807100e00401503401080c1041100c0e10381b080c1b507029507c1507109a03001c406091030700c4203461040d0382c0d1055403080142c030034007500351202e4600a07228a2000a99028901083d4000802c0d070a1003400030501d4030750010019075415845503800c0d18401d900100c00c0da4900010004062442a80d01d94004070a5045080c403003004403072400c4052444a501c3c4000c14160101b940d040c0e015801806800011580d840785a03a0f04d030201301c0284a0b060a09403e2a00d0071010401418116902c02e271080d1440d01200c20251075680700b0089840405023035076542d00042c0d00140e03103a01070000840c84a00e9103821101c41c0c052004001101c0d070036108180185503210a85c01103030005038428982064000c040d00c045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 760264298 1250 760263048 760263059
    0x180311101802030d0c08220b0c01060311030313033f0801091e0c05041a070c050103060b07260301080f010e01181e02060c0f0f060c18120601 62
    0x2260740c51080340280b040288108100303002d00b00c00c40506901007001880e00300c1e0160070810048140a00b20310142583c2c1020075140c0303800025011150500b80001400c91640c03d0205c0b049090180c868007030f4104202025984001c0241c24054030382005090340d4901400e070710850700c10310680c15000103a4030049164000400c030507025108400d036036190352060740c9940d00d403011070346851426100202c9a01c0385100c400040c1d00704400c071a00c41d081c030320300f415521880241640900d0710b100305140800650700040051080c00d80c000307040d00386410841c060410a0280003441001c401410300f8050941d1368000403511000a0122002c200c04282c407035960720115641c8014500e41c01d403655003003510700c2507561814411115109000e8111006500058888032000c18140d5510441420360700b00200144e1140c03402001d90724082801040a4142c9030303001d500700100b06504403600c0e088a000d10030325418420a030740710301041c65030800e101075850300042d02c9071200c0c0803d0300c01c1e8020fa8000288 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 760265548 1250 760264298 760264331
    0x51518030712121821050d020a061803090501050d110f0c0f06070918182102030414130b030f0106050a05150a0509030f0a060c030c0318031110 63
    0x1c0c02d1044507040b0000703140b55025107a2507144c14113140c00360218602040340c0c880b102c40794681649403104140c402c4000392a081e06000030000440e0140c5d214000810402c1054441c505c040c603114540049095007a0390300804d03802151280d03604000011551809640d03440d400800e0350041c2061392a0340380e9540140590070780100501c13040f107000d1210030701d00d170080200b01203100e80c01c680d452000c2541000a800c00403440016144800c540c3d8000094885d40074560b40d16006000b040306009107800311040d500c2091011a6a00854005020420440200b00049107090000b15044041009da40c0c80e80c03c01031144c039400305c1c1d040c8200c0b11040860314043d440582540d4055503c000490785800c184084c0c030000ca40065408881049040401c03403044001d001702c064010192020361101d05100317850154031010548101d40d44104410701d8907014811b42c60f01c06007070301341448170107400a5591500011114064203103c01109504d50040091001c0004100702060401c04084514680c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 760266798 1250 760265548 760265579
    0x90a0f1a31150f030f0203070206061017010806041b0b09011d032b03140a0207020103230f011202060a0c02031002122a0d0c02070302040905160605040515180307 71
    0xf0101e8642180000c2840c4c0600860748100910b4008100640740d003014003610315417800c0000e00b00589500d040b2141c980100041d03000303102d010300900d414242130514803d1039001c1052189100d40080c8100031029607001079481d030190900f0410003042058603403a040c0321030420501d502d40200109000c500e100030303002c0724184038481c20314014041c20441c16070032212107014504e28043c0c400c00185103000715400511981c1d03c18940031400d401c00030036100f40c2c152106180c100030090842004042c04490703a42c107004102c0304109409459054010071298444c6001e80c4081281a003070450554500300080310215042000031552140c6900e40f620200c038065904000030001256450190720100c030595074130032446c0c40c1443c54221555000c10052600c201074400354082d4180000242c2e03518440c80e403100b40550007400213800c40c0c0309045080342c9150405024001c0520003031229881c0c41d10402520300301ca0040c996030b00c0401011402d00c46000440700c0d810f209410300400e0101010a81c0c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 760268048 1250 760266798 760266827
    0x6090e030a0f08071b1109010303020a1419060f060f091a03031e03181b010f0c170c100606090e0a020403050c15090a0f1a3115 56
    0x41d2100800c14211143c0340160388280000710711500801c22250071115500c0307040d206540513803011a01c8030210702c2c5c80000741d0083d005030b001a1940c8083c4031030b022008001031180304c0039001c9c040c050041d8194411403080003074200740e03440749222003200080d40a4000b802d250455900d515a644120354042c008440300c034034a24021500040c1c030750174000191045030704c2060040b518154401c0110308aa04010200005c50010740702d0100c1401d4140100c0b006103c1c4100c4400d40300405030005403181017075203007940401504c03060381c40203d006410340450140003d40060f60310003600f070003540b41c4004008c82d0340210340341c20000a141030b08458104200c1d941c0c1c00b9907050036540c4804410890296200181540c3c0122941c0c035058607058122402c80b04069104c14200301c2894046103070700e032441c3c02240c104200381c0d074140511600030f4030000966820709146440c5c00c00284150300d01c40301c48101c4468043d450310111103500c00b03440b20b080240c000004104121010118024010320300604107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 760269298 1250 760268048 760268057
    0xb0f071205010803071103030f04030f060606050c0604060b01210c032702060304031b110909012a05091e0906011e230706050105120321090106090e030a 67
    0x200e0803050640c0107690403510789a000c2c40c1001856241c41c9104001c4074601641400204142414608110060300c041c602580c0c5000b981400751034864111145074101409028007440001c1c4c00010010b02154040d902c09030100d04206010011f0b00e00000000072200120040500250440304650080d8845501540c0074040f241008085c014012901680301040c41590034525015081c0000115001407091800002c0d440c0c00c0300420703203405880e11046a002641202c01122450070320f00403070300314203c03000800101c0f0901404855807810600710b00040340f4020014861207002e64141d0b00901c10242000c0000c910f400d01040703110a480130f6007071041c50b980c00880d001d540320320a05e0448030304040e044180710121034015100c90301540c030051100d00c0b03071048040700001c0600150810900c1480081510f504040030096990150b03101c00308103520074000d8007400c0410302c039203100d05240b24147c090161501c0d60f10314050035068220421250500b011209181d80000050080e606036a44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 760270548 1250 760269298 760269317
    0x618050a060f060912110907030e010606020303061e1f0807030614060406120603080a090503100b091b0c03180906011d01120e0d0302071707020a090507020a0b0f07 72
    0xc42c100540c2e400340100181d01d0110030b00903d041c04030f9400c2c1701070064289242d00b10f540c40004d000e1640442e9090006601c2d0150701a08032000d018541c00f61070180003440c1145004404900d20008140442e2404070100f00c0550060711075450b02c0503c40032000e00101c440040e0b020203000442c1c00d4420f0744c0003a00e0101c00282e40300505c803501765035a000900d81454240703032000031076500c5001800b0140e00313a5100000800600e4000082021424075103e500d517140c900800c0509140180303d082800c04d0405d4140c26460b903440c0d15030350780300c0c80303c519200700d60b8150b0a80101c68041c001d1280010302c000a1185a40c8041c0444041d01d5003084604251030781e1900c004494a0550420066548101c1d1880d090550300803142004000c0c0c003040000b503820b005c800903614041440300d1002c00301c1d50005030b05040c031903540d842e16114201c10406c01d1604249501040800c9054401c8100241c0e6840201e100ea9200707128890394680c01005003030345420801f501c6640e2905c19101e40010a25070711 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 760271798 1250 760270548 760270559
    0x30703090b0f06090415150e01140d0c0303080403180801021b0109150b15032440090b0906060a081b1207120204110405030d120618050a06 61
    0x1c00c2c0a10828000d803010025840310303910021000354600c07581c4901511914000b601d00d441c0d880c070800a00c400788800701d595141184104402d00c00007542d600400f40b16002c0404904a0340e581d0040b250b1604d031900055032141811242011810b1002100c0780709500c0008412905401409070400341c0003d6120300130011114908030340a44000030035110001c0b1000741c6a850755842a4500c0340701a000448480a0750302042c526481201c10382e1104620320300a031010b04070512112048682541c40301d005800d0000c880c007880000350103841c0080f800110011150640c1608000410303100401400107404034074180b801d10700e044822803442c1c46800300080007440c00400d0712003102e0700034000d092100141207002c40c400340d01c084019000000c5d00203c030000d260801c000780c000c001d40c0c101c00070b03145158030420040c3e5010b103043e2600c100c802e00c030920180c0c1c0c01041c000d10026140c14004000d00e42984e24101900596100c00d2000c6410303c0c500550128075049540302d4529500b081000b0340d02c48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 760273048 1250 760271798 760271821
    0x1203090509060108060f0a0504020a030e0d0c0b0a0e0a020604120209073e0a1a010824041104051f050a030302030703120605040c1707020601050306060f04090206030703090b 76
    0x212401c80c0002d40384c3c0c0104210707040c010220100c071000908141110382e01e56001c502660302400501000a566610f409902d210a2210304004050381c42c0688000c40caa40740d20020b4680034249041c916580c0520040c060300410122112940c06400c2da51200d5442520000c0c1d011981000c1e4046c0010600092450388aa0f6041b215804059140c5103c00d10034214a82c50b21000d08152015484d20240715100b41c03c10021034100c5846554001944441d12020388814501a4404120b40c3e02c100d154511100300341949240c0c141c42c07007583c0c0e18981d90b00d0810006982c24408070036001171401d0f0500c0f20414864009617500c85005002401e0184c0c0d410a22101c140c06100180040c1c00501c261300c0024420081903080c0210302101041c01c544400c00101260701040440000c10105000120413110052106a00c03006500191100b50316001c007007600d4031002006e83d4030800c030f812449500c0359a660b000b01e0034030380c01070915622480d0420001d402041c80400503104410031400017807401000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 760274298 1250 760273048 760273051
    0x51504060501141303060e07060219050312071b0b0907060e0307050613030804080303070e01050c0601052101060f03030e121009080d2405030109050304230a1203090509 74
    0x103075900c080c01941d0f900403d01c990011000318256105105000000c14501d001da5400146200043c00712180746c104041d142405020070a0344060044030117030041030000c001d80d1214411000c060300580e50b90f103001c071800e04a100300601c0c0700c20700c841014181301c0140f0110f03120701c0218003118490364803001c4c2520803611000042d94142d000c2c4000744054189080a00f070502114034081d2040c1c3d48964480d02c00c1c0d081074100f0b003003603400130003000340b415400540c1d4070040034203007442494004001940e64942c45e0500485d40101120304540c007008800c00d49a90b01542c11800810009440707018060705140c0c5c51000b600050140c0d0b11003507407480d1070a0170400840003000108800c90924800e01d000d071640c2c480c25501d418044c40270202d40c9045001e4801c20041401c01d80d4070400f02c150900e0070180c0960001030090789042100400201c4c00402c41702541c408440c41e0020004411400c0328090700c0141254101109480005a001041ca114112244240ca540d81d84949070402c1c819200b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 760275548 1250 760274298 760274309
    0xb0d05010504060e151512072c04110d030203190306030b01060824010203160303090b09010203010b091302160302060106080a0b0105040b0a02070b041e150203190903020a0905150406 80
    0x103808940e054550341b0110020000c01b410000d080c0c41507150580c10300c019a80b14051041c80d406210182d00301d0003a070b00c280c030b40c400f907040d842c14240741e2a6580303a00b003203681c99401592906c2c80e4800781402001a04e14030210411181d04601d0b2409004010f000366210071500c030413445001141030b9001e0789401d40b1544005e48107a00c40041c800ea0003c10030100b01030381d419400304010949140c000098013101c00c0380252008645007a8030b10f40ba0140640091203245140d1041c001804a00d041c0c00445044010480d061040004550703a400001c1c41003004204800e041c4010b46000c068000c02c105048440075241c0c1c810681d0341000660076039605c00c0c5442d00080c0104800c1c005e40d4183c0010f04800d4081e44104d403800f6031102103c00c181e60180d008284880c0c840402c803c0d1920540103010054500350250600b41d00d24004040c1d920300841c45e4081201200582c2c1d010514450340c000b00043d500102160031055680981c0d4009020654258100461444a407840d87c2040e010711400c0b2030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 760276798 1250 760275548 760275583
    0xc06030721051806150a05010c030306091404200a050d03030207050f1b030115121703071701140d0b091603060c17040c09020d0b0d05010504060e 64
    0xc0d2000000c6a60104100c040c0701124500c0c0c4515840746040d1052074859880c04044400740c904000d896450710400900858500380203245010729034a40c9030003281121009e08060124a86d0f41c94144e0203484290032030f9510034580403010203968040c2d400e5602840c007490b140004c01940c10a04401c40c1c0e607981500713400c0800c540040055007006030780240c4060017481d0041c10034130341d0b076a001d00309038036050615819401511032400e80e01515420b6002100f04130020002d200707090741084a0340009105044449100f80510028095150060448500b021583c0343e030762300c0d0001e806400c11426103070180302c071a12100049031201601c210708140080007400d80c01c10a031290348822800100408849082c000c8524410b4007004c1c0d00003840140d4411200032034907483c0c0340b40007040b1045180c2204d454140760014070000c20180602030007176038418080569101e541e9107000e0082c0030380d14000f541210381006001c007400750641c4070301e025900c241d070207016900040080342d50f108101d00c02c1b00c5101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 760278048 1250 760276798 760276801
    0xf0f0807030b04030c1a040b1609050f15120f13051504210c021305010f1208090a03030507110609011b140f06090c060a1e0909050a0c030501080c0603 66
    0x101c42040e2141d00510034504011503541c4c2d552043c000301c0f0607101031002d40d42d511080c4000c00c90303c40f48459009c5400a00d0707034505084000d004000211600c5154002c484c001000107160301c480a00100511200010b25942d00c64a07648501c0c81500320740c10701c58030354110040f59901d150311b0300d0341401903081001132017064400320740c5140b00c1030301401c1210703003810704010080c89a01302d01050b40304800da51500c48070040030740103000d10074401c0c07040d00050624001c01072180e800030481c5803003500c0180d080d4410111081c07a140880703100d001d085650003040d40200200b0543d01c50014003070399119802410704542d82d1000d0080310300031580050301007903080c8900e0400381c00d401c42940c2d509014a8104080d424140403242c00d10480101c0304000350090010481401c130b0820001c1281c036025541d091401c0300045005201180d61205161051640c0507141005441403210801400b061a8208403a0404904181c014a80742a20341c0c0400d06140000a9a85000c070740804202c0001d0f00d0302d40b03075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 760279298 1250 760278048 760278053
    0x3051003021503280b030132040f1a0405010e011b031503080a02011b020d080406090302030c07150f0203090f1909050a050a38030106090212010f0f080703 68
    0x6400c001c0504a80e81c12036032a140e1320001a0306884603c840740400002c11408070000c2c10f095070812054126148281503070328030114140c40460011400302c6c0501c40403901c561501110140da1014003030040c01995007801c9000003c0c1030303503034011072098008121340303d00324001350700303907102c500342030f0080c121490044140c00c8c06608080c10034203222070614241d03500e95407803407400c0c0c108080e440c005039998845d5080e81802100a0606100d49000800b095412540000c0071036500402c02400c05c2e8440c5036400c1014000c0040e00c0c43c1d80d06501c182c41801c1d40710406d0110490314281001b000030b400c190040d04ca0b50001c400c07101d1801010b0b107911410320b0018240800e00c1d0002100b08106407845500103404c0e9603a1046a010701c08880c00400d0034102054080d042d01c21101d054400810000050101e42c4030001d5201941044440700c1051040802c0c0000d00422a40c0d00120305503000203118100c41c00b0645060381616103601e00c1130112501c0d9a00c0c250004a40c0c01120040c1c1d010310000e101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 760280548 1250 760279298 760279339
    0x100e040b06090a0b090117010e0112060914060405060a020c031b0a0210030b030d05030c09010e0102010e0d1e0f0f050304050a02060403050d0e0405060604050d050307120f0305100302 80
    0x9200d20207001c080c54018484080b9440852681c02280d25100c00310340303c030866900c0040082850030540302ca0240c1d50408140740c11082040c840e5240c050f00811682c0c00b04142074101081072034004c0394488042c80d02c0362456031103040450741190303240a0a00081e60350140d034425128801d035041e0085040102c9010f88420403000b01d0750030380044c8280c014460040c0c0d140300c580420044be56a0100b940a04482030500d00510302c1896400e0000c14401c00101d0b00c200f9098031a810300901e4100d40c56482c020040c1d0050092090015403070141c050740c540010b80008000700b05e0942550414168107001a007101c0d01c0c070001203030100045080d410505090301c80d40186800c14025010b442d0300b2091135001644551055000300e91503004600700c60401c54101c0348000b00300704280c40900403440e1a400103261481180204c5110318800c0c80c1020074401d0800580301c03a142c3c0800818405003800d040502201c5500c209200001c0c20880000c041c00b190006900c21684e0240590705130110a412813403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 760281798 1250 760280548 760280561
    0xf04150e0a0b060a0b2703070617100b0f07021804050d050307140d0e010e01051015031d2b080a050a150f061202041409090a06051e06100e04 62
    0x15031081d1070300d002154041001c00208881415000b9a2440b00c201083d00406e5a00101d145403007030300101400c024542d005a0001603d603255a19001d13241e50b4503402d01101c40c51900116001c0c100852482c1140a8140042c08094000c96103500f00e4146007510b40a1440d080303800604a4000211803010307103004901854000402d401d00780c021500071000c1c2030f47c03134210760008460306032a01d2011544603401c1c07090f11241e4005e40004d00992030542e2010391340211501c91440701e40000001c1c0c2c03000d58440c1e400304540c801c0402c1900004c2d0b5058421039950080801e92106060a1807501003001e000c505000c3ea1800c4203845118156895014107001864010810700800c0e0729180c403c0100a2000401c8019145003940c4038091170030b0420041551080d60801207860b0700c100801d1108a0b03048074503111806084030102c1a50341c90280e080c0c02c10074503c0c00104a02c1c01c1009102c100c480380041d02020001d08c500300381091340c41c0d004006000c0c903080a0030010030701c90001e640c15414a60040e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 760283048 1250 760281798 760281811
    0x30f030516240507020d050a030b030105040c05030607020703120c1103060f011a0406120c0e0d06050106030f140609090c18012102030303130c0e0f04150e0a0b 70
    0x1424050070075100411808410021900d519a80b0440b050020400100a100e42801002000580f9040070060360382c0403280c07900c00a0005c0403d103100c1c0203203e60441c54400b04090b00a200a00b4140761102d44e0001a00849101e03018050015030031500c0000c200c0c0480e030b0000c44200c0500c41003007042d2601c20030340100b038a041a01e03504039515034408200c803031b01030403c1c0040e2840707543c9010818842c1c803084140101c0d03804020481040407660040c0000000305180e0000a02c0c61420117042c1d07060070824020f503800050700240c44c001d04c46998400382c1203071180d850600140072174189501c100c0f004c90301c4c14580103204c2c0c408203146092400d22a81c1c49801c0104540c11001424002400c1d4014152500e056000d000010300215545c1c10300107070190182c20041441d080150f00003038aa0000405845110b109220560705122081c42404c1c0241100012101d40d400e25855400100e84121010303140603500c1d08072100ca44d1743c0340c440c041c0c82210240c060448040395a80b551a00380c0c015025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 760284298 1250 760283048 760283057
    0x21003021606020714060108070501020a02061b0f03070309080d050d201c0b0603040503040608101809020405070c080406050a0c1506330e0d0c08010507090b0f04030f03 74
    0x3000403000d1000300340701c1c3d028982150036218061a500e1500d641600004923540040781d040080d41d03000102da8020380d504580c0319071544000403c10351300c2d550038103100c4410710600b1701c84516818084000d00406010ba07a441941c65228104540d81d002090514000101c042000d0840200a03500c00107804035001d182c80070001c081002980550000040c40b412040c501c0207410040b401480790003e207800503a030890552802c0e48070a5104c1c0210712400c0180149a8001408100c4061411000c1c201d1141c07800700c80440030540320001c200c8008100c0c0554034103404580140d016000c0340d460268030901e02850241000e400700c032241c221513012800e00c0501c1c1443d20004000b0341201c01e0600440c10300081007172420781c405d45c0303003145c2c24885140c080e0503104411098111001c1790134000c0050500904540f40f41c0003040f01807128040280c401c01100310040360044064120134051103156407208440d50300c416400005115001028800e0403040100700700090129440111143c040d042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 760285548 1250 760284298 760284337
    0x9060702040f060906120203060412020a0c06051b06060f151c0b0a1a04060c02060408010c0f09090b18041703042d0b13140d0201020910020a02100302 66
    0x81400d582002c5a009040360300c4500920450659201ea040248001b40d0000b80ca00000c0c1c005c00e443e020050b1001d0990305651580404c214020020320a803558404110702e2040c0d610240101580c01030000001441c1c0c1c1440c61000700758001070205c1c0a9003009181020414021082120807140000c10600008082c44000300c100e9901d88400d200c10b001860104206a40d00700700039014916801180445405208075902c2d07140620a59080d40d403182456500c07105103000042c232034011544492078a40c2000e0340040020360007031000c80040c0158850341d501d00c1d00c5680c0ea1050741c100384415070b0400a080d90410152041c4102c0c00c4e0018041c1075005a400c1000d8040a859441180d0546c0c0d042c601098241e001c0485ca02610f4a590a40803030540041490b92045030a441c0074220104034030490314041309100d6040c40c0608036400b207a044500b5401e02e550040c0c041e401020511748610303403021072107003164000300354080c2c416401000e82c0920b504800060f0001e400c07201125000f40410380 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 760286798 1250 760285548 760285553
    0x1b12090106120c0e0601170a02210406090b01080c01140f0417030310051e21011a010e090c0906070302010204030812040212010c0921050703080a120c08010605090607 73
    0x480401c807440c01599036550740c50900e004e00c14021006400c0a042041c103c0d0b000c040e90a0180ca125001401a100503a4071514503103c40b00300418181c1440f555503030141032100300503160340500320301403142c2414002607a9a10840d9102d50b4110308050104900c44943e0f180d0340c0b02440140809010308154905090b2110608106481d0300410494698400810310810100c201a203000904080320b0140d00740030802400d6800b55000d0603080d008851810600d46032980f2410818443c40782c550080103221400ba4652070203868205c031003804150409885079003418031030046031050346208a070700c0c030b400621824081700354405881502155400c1c4804000246480000d110b40440380c61404800d0134a801084044504804c864100760716004001f945603070442c05030400c585500b610001d426001151450600e17249400041c00c5005005010003041042c0001e0115404150341d5500d11030310356001c62086a8101100d0008503c40ca0010800e85124100800c0c12140150013a420f00d089039 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 760288048 1250 760286798 760286819
    0xd0f0507080a0314070302100504150e0303060f01020a02090f0714030405030909150a1a04030b0a0221150904020a03120306090b040225061407171b12090106 69
    0x1a0010801c03a004100c48000b89a80304400c1a0f010802c43ca0240c5840380e00c2d940a940c0d01030882c2065a550789400000d07043c081c4c651916039041401040a00c0805254100b07035440c0c7d841199002d1082c1c0d8860423021043d440002d03031a07540c035400b5012a41507218420190b804000c020480020081c0040e24035240304441c20146000c3e03889940256102d10403441042400c503001004014032080c16182c00d1081d0b035844502c00c0c110340c1c02100a48100101204a1499200307541024040350111000d00200b0711407035004207042210282010249223444800c0e66001400742c0d04208484003901c00c2d081c2c10314000c61500d400c148020541d0b1234865a0360345010318034403010b1703046010035628001008500460701441031004803c480441c074000900300108060741c04088030121104100c00070008100e16075001d01454510500c801049151590000b0902545d6001400b080d24803500400e1045000b8143c0c9860071000603820781c109084010040001e01008241071002d40d03c40000007903148c0030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 760289298 1250 760288048 760288063
    0x30c1707051e01110f0319020f040305100b060c0714011214100608010803041403010908072a03150c1709160b0a0912060b0604091b0207050306060d0f05 67
    0x44032140b00301002507105180c02c6035100d803050400514108040407003800c14200301c07540b0040e11ba21025480060490765402030081c0348026100031030004011007408000101c4804e609840300041c4600c61400c01031242c6070140301c1d00c4c2d0201c1c0e8040e0406101030490f82806441549041c50108101002402c1c20300680c2e0960b07c020181e126541c09001d0010540b0001e4030140000382003282c3c0c039500d010b00c2603643e44914411101100c1043c00300da0544d54084d009094103d81101c10507403a0551030414003a01d200b50b049071140b401d104005c0c42403940c0281c48400c200d84c1c11050510050700c3c02200180982800b05005e003c1000b01c2e02c04e250301d021300c2c820490154a40c2c2c4000d103c1074101c1c6030790a00c030260a0700040b078030913400d110001c00f16900130207100688003129003440c5403000f00d2800c403000e094401c030b01d81da1004003c0340c08100b81c032080e1301540e1303400041000790402905502c3d081e81c441d24140152034150300f102c4001000350602c1c80c03031190b080b80b086240c2c03542d0030426220305041a14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 760290548 1250 760289298 760289323
    0xd111204090e010e0f0601060e190e070f030b01020d050304030e1005190504053006151017150f0301060e0916060e04090305251e030c170705 62
    0x60b0b440104460b181d003442640445140c201c0100b1200c030100c030b1403540e035900501c24001045210250808651107044007555095400c010302100d0715142d040304a0a421f04580703003000641140398030340c07515201e4010000c0ca090113030042c14004007000011602070788010300940a204c01028071002d1600c3d4490301d01100d020035902d4580b1611030300842260317419040b0301c0030704000042c48244020b40ea584040c07021058014040340c160420442520f1035aa0b4001014502d406128200a260981c9105551441004440c5440d640001c4c0704240c1e07081003034501102010170018001100c0f000c42e4100304806c4c06000b4080c40d000d0004400181c00d5684a4206424045805007400220042013002c00d008003081c900e28099141031100041c2502c280e134440601c29600e58400f2001e0601400849400d181c04401d84010f000c101201c40108500c2410100e50f000d0340801d41410084a29806401196060356446140e440e161070303e0440601740d01c0c0325000ba031800c0081c0f0000610400c540d070090b03070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 760291798 1250 760290548 760290551
    0x303080604091e12032d14010303030504050c09191509020c151506030c0a05040f0e0601090806070509121203100e01060504060507021201060302130e06090f0d11120409 74
    0x40d03180380c00b013910050302200c40c0c245405c080c40c0d030003035440032845c80c51322003401c0990003103008521803424007070314004080c403000500c60030010041c1035240e08400d105034000c00484002442c148248105200f007124054a0b00d0380741a08204c4045036508020181410801040040360700c0c0c88484049a00015014000e6440040786030317030b140261803003107a02c0103248018041c2c09601c08046070441c400107200e0b03c0e06403800614941f181d0f0140084e038000e0500c1481412005840d03520740044110143d590b41e011600180e40080c45900024003944290155a41c8504048111082c0003410801c0e44401903180038845e0300441c41604000a50710494003280c1080d461803801020080c80c9506801402c10040204000d0102c81d8201003124000c40e070550b40090744d400b40c494120b004000781c0c3c000940c4440a00400c8031070100c2d94214202c030008a100b921915140c15640703550311002101090415040340c07038100a0355019030002d691054880d000c1d11410311203100140c45680c4503800850806 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 760293048 1250 760291798 760291853
    0x4120212130503120f040b03070c050106090f0e0a03212003060114070203060f0606120c0913050f010e09070807060c0b06010305150f060708070c0602010c080709030308060409 77
    0x24603080000400b0741d001145813520b88640b03041188003030b219a000e481c0c0420707000400700d02c00c0c40c801c591905407180c01c40001c01a1949a030030f030002800e9819480c0c402e16091812060b03803030101103101c032031240e031640b94072010740c14442c8c203800e03000080d5800040a0b40d031022604804100c9050840071036245030b582550724500800050724000b040d0700008008881800003000580300003c010b50032020003004002150341e8000080e1b83e602c41e401814102103502428001c00f4400000503001010341202c02900d81030b01d414004040742c4040f50601070481208004000309951041002d4104031a94256001c090302d5203040c03460b180703455000302d0001c0c800c00e18440510038811002078028009180600030760130507501580e40804001403140c400c0085120454056403800c01329143c050b40a090032b5242c40e0b1074144201c16240314407406c03025500700b10b841400c86e4820105c01c4e10908568407007144050458038100ca01201c001d20701900280e40b17024500101e2000181c0c4080c445182c021000701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 760294298 1250 760293048 760293059
    0xa02041b140301080d051614070501080a0b09040807050a050712021e2404090f020c010501080109021003052206020d0b030c010207170307060e060901061a030412021213 74
    0x6201d01c000c4011070200c8140018040d165020a00441440380c130300d096a2248808161658035030703050f030401030400024003410030123560089010011074000343c031030380000d80d5402c08500550711031006096200f0050320010740010100c4000d0071645016108a540380140c03580e03220314024142d00309984500480040728110f250550754440e0f00c0a5101d114410450365501040c0b8000b400103030820151642e0306103994804565060320010070f05400c0038400d00c3c0d07260451034001c1d48030b086680a1542050004960310300c0c14000e403150a036029241e403c0152004801300c0080401505000814400c40e034401c9184050142d40640a40103000043e038649140000d1403c4990000c0c0050280d08006c14003011a030700413644200310740b9011103c01e0549246041d00b425803007040070040c0001d02c1c0038140102008002145ca101710303800c00c001c00800b80c07103201015903841360300b0340198224405c200041c0055520b10000a235481d0900486101c2001c1c81d8a480403030300008004502030390354242c02c104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 760295548 1250 760294298 760294307
    0x11030708030c0124030209130b13050708070e0c160204020a050904180c1e080f0717010216081b10200304020901031106040801060806041709030604140a02041b 70
    0x740200c4c1d400e01510b124843e04106215040c16220183c41040c40200250100d070a962000c581c041d84401d910702a03240824802c801d55003688025034941c8034105010508032400a0200b0540d5a51704100c83c09940b070144150069010f1522505031510001041005860701d0001e049140d40e90303258691a0b140480902c811280204140900007101440744004130380d07880220800c1c1c07801c208050104014001c03550180c0c03406a808451a0b1040e803841112038030001c00c8bc1e8040e0f07001c84402c50400d01c8440780b032500781d0181350b03003a40408420f0903039400000c80c064010701e407848015680c2c22040c0d00d4001440d0030001462550b40426803641d59a000060940d00b05c0c180d01c0c4c50790006a429401e0a40100704680414000100700703030550040f114a56440a068400400c01e12000703021154840401a4a5140691301140c651503694045517829403503400352120084050b0003040150340716240d00b001056008004140e902a14990402685460003040510b0f114518021744a00c41d81d80b0040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 760296798 1250 760295548 760295561
    0xf0705060735030c0a1b0b010b09060417100608120301231e130207030503040b04050109080703050c0601120201020a151d01091103060f0106230a0e10050a02030d0911030708030c01 79
    0x41c1b1a142205405c0024640b114036411345a44000c419240c08002c0c0100e0920f201d85d400400140850300710400c105000025402070b0002c4204040c48099640c0c409240d4030135000003845405181403005100305510314000110022400501c80d0220210350301080401201702c0c50511a4401c4000c002103a041040700c000501800f008118500f486680b001001c60202030001410300000390041402e06c042500031502594104090305ea588204e4a00070300290b02403030740c1c0702950054400000d00c00600d20b4a814160340c0607005495200d60355a1908001c82d6290300d80c006141d83e850446001010a0f120810607201400c000a4146800c0c207141c507110540b010424865880f55040011210320185698116003203800d00a40001d03007500b0700303a071943c0081c0d0401c0c2ca03072001291a15a19501c0995a00a0141910900c400c2502d180c030444441c40380707079000405030f031040007400c660300102d030702165202d4047c07540f207072030005070300c3c006400e21105a0041d0303020ba00100d0100c411503828850700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 760298048 1250 760296798 760296827
    0xc03060c08150910060e03120a0216050a03081204150f021201050a0f03081e070b07030b09310f0602070314090307120515010303020f0705060735030c0a 67
    0x31070f083c1c030f0000c0003614401680d000d003108016a401001c01c4a88003000407440b14600320440c1c40c1c581c0c2c60824002d6a0320060701c0d42c8458804c0f0580c0001d8141442e4a2420540f908044024236159480e0700c07508001c1806403049403a00250015004080300034852545c890b0f4441c44056961002c0c0b0078294402030040e00018407800c2040d004011507191402d000c412264001a100d0b00e0742602020351502040c8100d40d01e2070791030001100c108011099401078840c0060351810080303107807084184562000c5c1100d40042d10741666141012459081c006541c441024404a00d0481440d607035869210007d52012501c0e5500850700c2d80c101a0000c1f024000c0c000d404a00a06007081400000d603100258890441001c4404045200341310742400802121114042c01d08a9540d5030f00e402951280d012561204c0342c020294041007a240c40f200701c0c2d0342140c101e1600f40000d0b1038215119101d903284056801000c1038082c1c100036074818040039500c59040b0703000e4a0349a4103215400781c080000d05284 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 760299298 1250 760298048 760298059
    0xb030a050706020601052b0f02060409020a0509041416080a060f09090c06110304090f09020603040b16052a0307020312030702010605010c050d0f03021c06050f010314040f0c03060c0815 81
    0x9400d490820f804d025a151074108c0700100c0c020303045002248413841a41c0106a049000143c0500f074203800c10002d00400f002918100454000c1101200300303440241c40140d003500225503258421445007d1444d0000042000001c68a0340d8245551403140b05a00040600c1d885080500912540d0000b80c0002c1030f89080500c1024694a8042d440e48140d001c0c0482c03a6980d590b03040740001c116440b8400b026806410745942c1d003458101440d1064084486a1140e0a1282600720203481881030301c0c881220b030b0824401c1c41030a6800514460185500d520042c8030600081025a804022280d51450f403421803650341c0c10080f2000f03080d1440340d0400c40c180510f110704040000c2c0c0014030190320310f4a034030381001c220445400c100d003e4400d400b0203000015a0038412103c40c0601e074092000c44200302c900c82c400042020054080c1e510b0b004000b490901e03813000080c049002070841c840c0562280b88112929034980d47d078501100d5400800000041c0c1d40402c001240c03803024034040007004c003200c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 760300548 1250 760299298 760299349
    0xf0b0a061e0302130b0706062c040f080703090321050a0806030a02040c03290631030b040b1e0c1e0d0507090e010803030103060b030a05070602060105 66
    0x409071400c0300e250580a00c103500001001c1c2070500c29810f513042c41890700088481c0b00d50700c400c18a065000303502c0a5541074604000000e0410403104100041507850a070410045003468420245150013403094075101c03120303021b5200003003520009045051294a907a00b81c81e046040c43e440c514010808810190524020030307072203581060958522044034901074046690b9200800e04050742040c0007504a8207090846200c250103401603005c03000c1c40d0003651001c6401c15141111208800c806c90f822200411128030544400300c10b00f941c0d24039404034851704810b065890b0b21003070080d84c025a91846807038140420003101c0c0d01140e80003001040b60a0500200310403031440e000d005040680003250008007a0042703a0008480c8c4200028100140d40310340704502000050031040b20990000703144113102180301c10002d82d80718140d0308188015402c5a00359500c110041181c1400301e540b612a00728107a001400c02c00010001e81141d50140945501d4602482200c1c04e90040d82c40c84040410b5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 760301798 1250 760300548 760300559
    0x16080606090f0103090c06050c01290f0604030b270102073c050c01091e0b2802070512610605040b090d05031303060f0b0a 54
    0xc1919185072045800c20012001540107070003d00307071140024001e841da01000101250014080c00800c444e01000303110805203070a001c2c4801c100d100b80c210f01080301200c0c9242509180310846416600075245520b89612619843c91705070040f90481c0144408007103801103003c644400c5819045400f0080d428801183d84da0484424107558a65841c50b29981400034a0501061540703c0c0c0e80c2e91071035a0840f162070a01685412694076554040307150240006141052040c58520807204542600102e6041101e00445070703010440394070540310b40c444104102103102217501ca1141083c0c00900d1428a0039003030111001804412104a800120f070b44c1d41170094400840707500001d441001c185079000d034110020240c1480c02802c01712030328217414100c9200400e565841e80380016540d114465030304c40046070fa070f1146000701820b9070024443c040f4903080c65159400001c0c468000e5a00304560700300000c1d01c0d942d031070340280c60068a0304001040c224441c85100d13869941a241000c0003410130 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 760303048 1250 760301798 760301809
    0xc0d0914090a1e0906050c0a020703030e03101407031d12030a0e07062a1707060b040c020705010311040e01060810080a030806040f0c0e060f0d050f160806 68
    0x1600494016507000d00000d070448015070101c80c40044030615007481c0021032001d90b008064016044402500e050701088032410080140d45811200d5402028040c2c156075040300c00900880445400d40f1561400f9210f049035405070011980380c080d07081d01c2914280c94000c06640141340d060707540061503041c80500030804117040107035150307102c0a141c1d00d0300c810503090b00810a08855070100d0040e468080341d40e903030042011115690440d10b01c1e0302d0014050000007a0704203030314010600c0b0406010100511004170107030001c0360180700c0004610141c0004a01030751100c1d1005070050301320382d000340000c0d80c041c4130300d50840d50700d004241e0030942001002d8140c150180202d03824803218100207007086c3c041345401d4010304040e2099420b0030249280103406000c055404030320503404c280c0094020000e51043e6983c189140e42c070b001a200c950340c1849441c1d4400d0400c03544482d0100415084c00380341e801101c0c00380c2c064281400b460719000c0503440385980c0e078800000402180030140030159441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 760304298 1250 760303048 760303079
    0x50d06271a010f26040503030f070206100501110c030a050c19050603060409080d0f020a080a150302091f171501270b090a0e01051005031e070b07080c0d09 68
    0x50f0130b001d4051100b00b144500c0e0324203511034040c1400c0f00d000c104402c1000210141d40200500041c0e500703540c807559826070306c403002110303c00440600304604210940c80380e206c8400c60b105510a4403082c640d100c020900304165242c0030b881a600c03c0406400f10700f44400141404403609500840460400000860a100c040c02c298495900d0b21007060a100d0004200c50700f48003424420000303040d055030480b0280d0000100800400d4080c000107803050554001c0070076542881840001550440c3d003000480d050103010790500901c0800100354032000d82c000007001e880703070041c3e003034003041d01c151003526000c4150000f400070300c00a4010400c00502410440f51455030740e455218030003500000c2001012680f00045c0d0048182040c00510b6295512800811160310700900c0b8039542c0d08000146440e95228150b0180d2000c2c03500f91202400105448039041214150388942c0e94401304110b4640080d02d0030783c6e442c00d0025401350080e404100020985143d420b00d8400a8900805100209003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 760305548 1250 760304298 760304327
    0x30a0c111b12242806060315052d0307090618112d03040b04060b19031137061713060b090112052407050d06271a01 51
    0x603404042103003441320088040d0307022072841c025500130260700c2c99040070701014820700010901e4540d2010703d0121010000c010b49d20b015220381d155600502560084200300c0458144208044d64100e100303a609001c2d80b402050003040220711142400c2c5142c0f0001107880242407030300e16104010307100000e1031050b21107800000754030720f024804400c000680d4a405401d040311700000002044208200d111401d8042c03809040100400c3c480041881101d401c0d030501840b8141c0004002c0000521001662811300c1d030140203003035588500c1c4100c01c0c11680503051041c06000b400b160050081c086103810000b0444d600c0c09030390740a00b02a018090005c0505100783d000d00a40d00c4209001080d085804c1403200035044400075a03541c090240c0000d140801140d031401014400c2e038041e0500a14061015081101c03c0c0b020313140c02200b1b40345580078013002000036880301c0c40040d801041c1d07441a003402500c0c0c0d402d800b035191210b1110b0100c45261050301103c0000704003040d0381e070341d2040d483c0c41c0188 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 760306798 1250 760305548 760305613
    0x10f09030e150d0624090614210109090b0c1306050304030201090b01090c1d0f010804140a030f09051215101214010c0206010308030a0c111b12 63
    0xb9050203110500c162000455a28185074000035650000780e80c1060005075400e0401240b280f01030126030001952040400040b038404104140d0b5039503400030f101d0380c0449155440941005a1901507011099001800c40c50303903140b840060011824409030b0003002981511f14150749851340030001201e0703001c2c200402001000003401c140c000d5018900a80c2c2001314402c00c0d6079140b8004d4050a00c10700c4d600e0010b0342d0751000d04800f8a01e11034001c1014401800b502c07804500c00011150000d0041c030940d1a01000300010150000600150304114026552114884038213000a40a40486d41c01107000f0403022045000501c1c010486001010001000302c00ca40c9506c4824002d501064100d20181c0814181c3c0004000200642610fa8405640217001240c00d129060b43c845009210240400c0410800280b61a8803039000da00d119582d810000c4000c192401e0440c604540c0c11011200e01942014040c2c0520b09401400a000000001040a0a442d1b00e02c110480c40709071000e00a03a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 760308048 1250 760306798 760306819
    0xc0f0301090f0f0203130c06090311090912041202040630230304050909010b090106030c140d02030603061612051302150316050301060c02061e0d0b03010f09030e 71
    0x142c20035000b42040c00300c000c0c015074490a08202001800607000c42c211140e0700c246400107407283c01203401008a076088142c1c1b40f40c0c03491403001d208092500610181076809240c018502001141d40035101504901210350491000c0c0c1c41888110340ca6500040d0400ca800700d0401040b1001d90840070310541080b400809100d100d140016006403244158108072510042d204110040040a04100d03071048603006001e45a01c28003600702d651510246170003042070310040c40103500a40010f101d504580c07408105501841d83e2070600d03030b00803a070b04240c5240c001007444840d1034204030450f00403180c040018a07009110001820342600c0c02ca8195516888500044c000392054040c01c14143d005031a2b040d0704a01c010914070550f00480301c00c544220711060165501e4400c000360380c16110b2075216914050003a408010075030300f0603107862058140820705480075641385d0003c0c0c0010104101d0101d01c14224400b0142503030707150300030803a00b14a010007103808681d001c00e00d410403400c1640c00c20b080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 760309298 1250 760308048 760308071
    0x60318010c0302090a210206040803090306100e070f0210050a0504060f0b01080721060e040507090c12270c05030705030a081207110616030e0c01090303033201030b0c0f030109 77
    0x114694406c00380d0300c07140124001035049008002405201001c030140c482c00e58600d030010141c42c10b140100c0c0303403940304c0800203854140500e01c140d10b5401d007170046520b42002d61420b8000e43d0422620050000e84440c140010440341e030281143d200701c2c3c179500303200781d4415000003403180400411000401403000d2000000150388807501c00360440324501800b81c0ca4644183d20b00800701a01c0459040c0f14001d800141c071160780c41b407510711612660701c601180d1140000743d0040c0a2213031440b1a80c04044021003401c1c030001c0c899645046c4280c91100d40d2034540010141002c0c41548200e01a0b00180300301800918164200c850411001ca42c0521644031039a04132032450711150121a9440740c3c0301032041d5500e82811800301e000c4156001d101004078a0909074442502c41303191404651221000d00000307009420010303540024080710018a101d40300b0000581484c4003000c044200040014004d01010700c2d41d0360303801000b0540061030101640c45001d4503100c14420704041d15500c150341d410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 760310548 1250 760309298 760309349
    0x3030f170f15130204240e0402090a0905090706201e0f0a150506060c0606092d09011407021b01180806060f0102340302060318010c0302090a 62
    0x44030b50003500034241c3e140b003400614004d40c0304d0300070301c081554003428a440c5415121449041c1c601c5503640d5450718500e51003840041e401108115034001c0010b100490049103910413640709520b807000812506141c000054280c44c0a0a4204072003d030441c0e81071a0008005440034031441e02511419581c80d0a414840c204803656681c2009409511041024821003003d004041d00c0d01c207504021035103c5404000307084c861103541c0880340c5c009000213455858614030007540451025007502400a50078002041542c081e0504a02c090b500070500c03001210911405001a0042507a8200307402e0880c1c0181d07448202054140c90340d00f42008034110f60b4410030810349000710720318411301d4507030311101d02d143c4600003200d21a000c3d124101c5244219880090348206034814940d00c040072038803a60009810302404c2c00c00f00701b40c140c480c20010068076000c0081d071040b965050080060f14035010b140e400d440e46100d0070801c140c01802082520346d5034403038003411a6011744903800003442c1a019000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 760311798 1250 760310548 760310581
    0x70f0c0f05150703180f14120423040e0a0206070501020d051003060c090321020a151d060705122203020c0a1a0d0519090c03030f170f 59
    0x1040750048401a070070800c0d22511080c000ca116450502441003822200c0840140d20600130388a10180850171001c1003c1802080c0140c804d86e0544245000038041c0c042aa03202c1d07402000322507940b0740840450000903000a140702412a02404011400040f150b5106080080640310b900002145010003a0950482d80e000303005403014019450502c0c490403009489202c1a11054200010b82210500c1100c505065990002c000041da0003082d01c01242c9811100c90341f03040d44a840604000309100882d00200c03454000008980303115000c580340034101343c0407491811540202c00703001120381c202040c0d9240b0403400c43c2e05a400e5030740c90010070041e600b250469030481e001d490020140755002c582c42c2c109000a44203842c20396910025507184018208601e5284241800212406162a0006900100d40001c000d0441d43c1a29000c0101c0d04440400c0b40c0d6404078203010010150004808480c125982c10004141024082c2c209a03401c002070000403000008400100140c00f03410f00358 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 760313048 1250 760311798 760311803
    0xa0908010e100f02090a090f0204030602041e081b01050315180a0b03370212060f010506091008060303040b0705030c0708071208161401020a080f070f0c0f 68
    0x1d000c04100814110349440841241e03400c4203040c040386080c0d0380f0090007240c82c0c03a400034002c0141d0307518000000004000c800ea061482c01d40030840040884d0060020b0000b8020b44501113080700701d4024100e45070290382e40504042e800400180c0f40311501c2c0030060800803000e0900658a40d42c1c040f400007102810719205611400c502c004142c03002c0c0024403203208016001003084210801c40c201950f410100341401100038800f030325103030b854074003440d00501150701031030300d070422012076000414003146031408941660001040001804c5c004040030700400044d168145402680000304d003400304411500b1003403108030004a012503d080080750024218601f8407925201180b40080e181d134854000901030307103c1c442d0085291100441c20074100c3e046001c1407102d00e481682c8941c2e9035088103d1107500d40c8440d19400c0003145142d0105181e100039400010b80d0f6007a0380078003178068100504101c1c00d4000304000c0015450300914030b4180d0142c2810010031031070a030300e0200c5040c840181c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 760314298 1250 760313048 760313051
    0x3030504080702040e010b0f1f053a0f0207030e1c05030a02030a0905032e150b03090d1110020f0910091a120112030e1e0a080705060f0a090801 63
    0x129100c9040d1f00c80c0420b50004c50320b034103640c8001070410950032200540d1103c002c0c1d2404040c1106406007000b803e10010042880042c081404003941c1810300d0b002044001804c2c6040c007045040e418420030401c1c040c42d20086003042e0103601c004100058540005008d00300400340c1e80d0489400c414160a6190311800b00d030786e60004480025120740016032000d003c954100e00100c0c15280114100b4500c85410005000240520f0715040500c0e880c200016500c913170b41c11200030400e00700a0070402034100701034500d58070b091204206280003038103543d0008009442d00841902000410340b1000e2551401000d0b031a14000c0c4400c040c50311940c951181d205014089182c0d0b0350f81c00482402c122220005003510314804100100d06600c40e4078100202981900018410349807015a00c1c80114002d00d44503280d0320103540842c14031104496030900710580b10604900300d04d00740320a4030145c040600a8100d803072a00340450030341c1c02480f4a5940200000c18024141841607003071a0051544400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 760315548 1250 760314298 760314311
    0x1404110c07091d0c060d0504020d0c120c0e0411040f02090402041706090a08090d15020c150105010e010c080a05160f0303181e0606080706120b1504030303050408070204 74
    0x60380080c100f00e5040c1d00140019000d0404000000c03a9034140494050055417414114025800c010306000b4404c0382e00c08000341503640401e011300c20305c4000c3c0001201e45c562520035400c09644003003441d840f81070941d98010070440024150808400c80a00a03a00841c11440784131200005c1c2c040e16003411340023032010400240d50b218201c3c42e034080c50303200706c2610450740b0392421135515007081d428040c140103c1002030341070710b003008400220b9160080400c1c900f8a900c50100c1c1e0144c0c0d21142c0c1004490780880c03807071105804101c0e4180e00420003400e0480e03041861000280143c1d980c010701404002d00401c1100e07080303004008480181440b5610031612184a152103400c4400f541000d034006881e00c905001a034207081850950250016202d0884004c032000b4556842001b0604a0702d240e03d861000540306d0081180101905035600d030303141d052088185400441d000d100000d445468942640b401c01c400300b2003146d0a898252402058603a11401c22001c03a21802100a421519110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 760316798 1250 760315548 760315559
    0xc1205010b090901050708010e06060409050a050603010606050c0d030e0f0d05030403020c0109120221031305090f070e0d0f120c0b06040903021b1305090a020a0905011404110c07 78
    0x40c4401c50304881210520034949488111908961049030182e0100d2200d5005001511030780a105078800c0000746014645500d9442d90420760308107580001c11203803680103001582c035082c0030340c0c8042e20440c0f07008c50600400c0606555141840346800d01030642e50000500d8081c1d0138480c038114000100e080350128619090f00600d0355008aa0580040c052250326100c0c030b45c810410001107880b446204203034076020390208807010704c480c040c900307500580716905030440030300f800904480403100c0c00740c490013450b086c10b225188800800321070107042d0180c100807200380c000c103400c42d141100392460002602e030380c5840032040400f4440174218911300440344210607444100e04012510400e450402d5840c0c07582444250b4407113080040143c0c204c01041c20580c01549080041884001c2c200c2041841203034100e0100c6000f5a08e120b001e810250752482541084803040b0024031044100700b180350714000c0d4900c160100e007203401d031085485400312050105140c0642c0d00b0504800259802c140d03660 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 760318048 1250 760316798 760316801
    0x100503040308070804080702040c1b0b010503010e15040b0c0417010c0e060c07031104090602030f04140a1205131d061914060706110703170a0b0607030c0c120501 71
    0xc950440c0002c5a520000d401030f8452806076014070361180340c8a04101240d803c00024000700606c40e410490369070510806080b541924003121030080584051a50400b414107003036a8a680c42c001d110741c0b102e0360314081c1082e2041c04d594016001400c01c50b0503110003c9141c1603109691229020100d85a4901080382c010f5001794899000c0d602d52880c809551818000031717001b050329a0f201e07034100420800c0072492841040034212002840024140b5240c2c0c0c1d076600703c0e00240c51400340c08841800f00000c0182003545192041c0c0030a00031316440c1c1d00b50b9200f0425541c043c140b00d00304903000c140c0000c00054950090040e10040c10a01c2c44604144420b0340c210500f1540a0301c108801d8031245410003c410414050b16000e1102d00302c044501c030240003440d808241c0c11112103984040e011014040711015000071842542c804010103103107000c4012054016003024201440d12402c0c111941c6c0321012a100998141018000402c060820040110140c0e012100c20407011010104202c1d06 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 760319298 1250 760318048 760318051
    0x1203050f210609040503030a0c02010216080408010b01090f03030e0d0b01081b12030406080907090212070806090c0403061a21010e0303060a0314010225290705070c05100503 76
    0x300071260000e5441d441044182501507501401e580c10410200d038034141103800c030744011005400058500590707a080440281000c440a40d0340780710215060001b00f00078028041c1d1500240b03481c802c4203080c6400e00b0b050002c2444000c090200056000c3c0803034903141d6004801c2034010890107459070f903a070102902e070a06a100c0e89612065800100325034034240400b2a0506104001142024208942036401d020041d110981c0d6102d00e07440010701000b81d0000707000c0300300c41d6262a0014107010300d01514104002c0e018038801c640480c04c2000c52240070040c0c60490f60032242c003080900308444444d90078584608810b801266031030034210700107044806c0d034019009480c001c0004040c0e481c1101d88900060b40c020746d2001c41e0080c10000315201c044055149500ca070001460b140e686281c2c840010a000704000319107807225580c000b0312603818504404010b04510344040190a49940028460f000700404140200032452005204824040700c0107018042c01d030b00c112801006029059400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 760320548 1250 760319298 760319347
    0x503072d03122304061b0c06030b120304030f0807110306010b030106020d0206040c292d07022202070f060209090106020d020c2e09030605060307030c1203050f 70
    0x2405111400b60410754540400c0800030000b8101303811300c80101e40c0403042d031182c14490144024a5804500d2144020004000640f00000d440d407884040c00074820442d40f101c401600705100c00c10104c0d00d0000840c00070b0780c3c410249070342c4d0150b40c0f5050404003a6100130b1505440740170300100c3c03454403440007503044e1610b40d02154411045260226618001240d0007012001c11800c01c0014440400300d0f0140f0041515028484000100400c8201c1e0803d054440710501907070b603800d003040c1a00400d42082e142c0101100d00d0036810360040b0b20841203149165074101c40101c0d01c02c4040030194140c91131241d00201980c3c41c40b2880c1040d001039006410424400c00402c000043e140c2e000140c0c8082d0100f2030340190070b00c05030000404c140111407408600807100466580b00d29290b8180030b400c48503074551200310055085007025002c82d032009001c2e0f4065800350105001250000c108001111044604019079114624040320380b80204005060720020204070300e0f402c02480b10b950f014a0301c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 760321798 1250 760320548 760320557
    0xf041725030e1c0605061c060b09070c110d0503090307260309130e100e0a05010f060623040b0a0504030b0604110a05030403180801060801060f0503072d0312 69
    0x641d044204005080c525403d030f0f00125418203d070000480342d0304034941c08100204900b500040402d038401c454840e812003101c0341681e6032007820561414262460b007040540c07900c04400505a80d135281144107842c20340b40304c1c194a0701a4001c2020800446001d400080c0565402d2580d40c02e0f2103d14084280a14812a101038030907000a00004252a2a07040c0144800307643c22845810000400c991042c2280c40d00503420300307209008085c0038400c0407110820081a05061508082c3c1c2110270a0384413400d801c0c1130001c00c000e030541c00641d641e80700074a454104000b184803550000c45118641c00000706c04008121160820b0300600680b003240d004802c055400e903503000802040712081c82200c00075680512941c10114440c5e00910f80c8148a8100310007182444890110580038641c0140070903912800284548107080c003c1c01c1c01009507007441d541c0c1a081c00e00194444030203000703500c3c80c80c000c803904154000030f070395002540351103100051a0305501e80c204941c0c8a42d540f5802800f15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 760323048 1250 760321798 760321817
    0x12100b10020a020d0609051515011d1009030b0124030507020d030b0303070c150914130905070f0308040f0e0601120b03150a061d0f04172503 62
    0x1030a182210111140141e409401058070540c20020540d511240544505640300c0e040da000681c01c1186e1a410300788030301444074034500040584881100c0e502006d041000044040c04182c0d0300c18050403540000300c8944e0700d85000c1120441c0c201c0c1c4154409080351241000004070010710701420000a070660800710060381900f00103a0981d84181c41c60401a4050300790700048074800ea0094540c0c250013400d43e45008543d44070b03502c880700c0641160903c83c2d000c10301c412500b50080409802464800e10401c150030721180060380305c4a0314019110a6522a0500d00c204202404814081c26502c504640400e440b410000200e400c40e010715400041604000301d803050b03150314001e114800580da002d0003c0942050701307001d040d03040040c0d07800d441240d0020180041d00d25026100750150344001444034501201d80559903100c04980303c1c1907094101b48124510b601800380c2d03000d0703041803a00401d00c0c100f4007104464801d914a41c280748070502ca12425440202c0e0914180d03e0181d030310322416 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 760324298 1250 760323048 760323071
    0xd090b04050c101b080403080a17240607022407020918030d0c03020d020409091101030606020607030509070e1602010b120d0315031406011d0c0a030e07051210 70
    0x2c4101100302c203004038107a00604e10030454212800d1011070710541e295424559030f81c1e070759841070f04444030140104084104c001c2080c940c0502c0c150380003410001c045440c8555201c098003503074038a08510b003d039800040c44015920380119001c000302810b024144160180b4010301a6a0801d03c2c0482c4101c5004003c1000c828418449041a0240c50055481c080320800008014082d2a4014091640a1011b108011058409440140807980780440d41d4429464596055089018254141031a2960600c04e00b9400117030640d110f0214180066241c95201f2514545000b981c40542c074210781c0340c05c1050b100b03601c048542c0990019002403108446102c00c106c0900d0140641b054035a200105001100d03110380c000d24680b14016260310000d58a0340c80d00701b08045104d00d142c81c40d501a00041120b41448500701004144a00001105040034540300300c80b48180240e00341050b4852000e40790350041800923000a04008001c0d41070000c07040d0300c0d13030345502003401c5c517021051911418164 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 760325548 1250 760324298 760324309
    0xc030303010f120501090b01060f020f0d08040b150409151506050a03110405041d150f040807060b12060a060602031e0f040801060308090a12120f02030d090b04050c 72
    0x60b607809986482609040c6060040141100362041c1c5107507407180c080030042500e040106010341010b03560b02860036541d00c4040d241007106404052301c1d42c030802d441c0c03001d1507200c411281c100e9031103050815280c651031400f0707124031569030702c0390791041c6401c00702005c102561824400808840e203050224500c0001b203a048803042d1721540300419010043c4494043c4a40e011010003c881c036501030906032103101113030494138400c0403038400701014810500c00c160b003009458610322501e27428054034908031001242210380030b00010814a408200d110030450300d50045240d03604013409002078101070b200300ca50b0301c0310180e071692030862800d00007058162001c0103c41101d2a410790141d080000401c01c0c000507448480d0407094103e040c080450304403020f00a040095028002082d1941c019100304581e0b68013684c40348220500005000c8000780342c07804150b603003a00c1403c00400c61800f0b414164190b01c035141101140f986040041e104001c095620f9601a138000c038119001c0c002c5da1000e000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 760326798 1250 760325548 760325551
    0x506030607020a02220501180e0f1c11061f1d04020f0301110c1c0509010f0e0301180f0c0b0918070203071703090606150405040218030703140c030303 66
    0xc01a0007510481e0054141120000045c000301c030007428007022408a9030040320003c0e04420380c00000d00344010b140d85040c0c0611000b10b04800040c002c0070340a84a044c3d983c0d480c5140b0f001d0182440b240710304c0088c0c0240340241d0311700201404c0c0e440f68a030040c02c62105040008108080c20210b50000c0b0349000304000800c4c1100c070341e0304100a2034486408000e80182e02c20003456141d9200d80140e081c2125000c081d00c601c0c051100109510301d4292114244e18169140c21410000c062040d00142daa000083d003c000350740342000038103035901c00d01017409080d2010a0b107030359465265606040210303c1b0250382c003440c044c14815262584030414000140704201c60b80307900c041080c2c441707404c1c03000d401d100307a41009003401103920741903107640d80c0000d019880342c0044444038040708105a440d01030013442e0703000c681114214040002100b904030103010314020980510743c0429590301c4c000219114840c100d03401001c50700b0490303036441c0030824050808403580e20b40c00354031000050380c1070000507603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 760328048 1250 760326798 760326811
    0xe100e0a02060d0e010c02100609140403031d010509072c1602010b100e090f04080d0b0406090f0e070f0308031602031303050c0f060408060c130f081005060306 70
    0x10580303040c80c0e030200a4140c2003042d8040b80c1c1c584e00c0450380318441c001d2142215012141c0c0160800c0e001101c00b44013240c50f0b9500c080c1041d0b0070303c2d41c4000400610001c203980315615040010b400006007940e28500201e001d05508150f03c1c10003030248100b00000c10104450320010a400040030318103e40341c0d500a418603031700d40c81c0d548001003402c0401121607100e45e402140300010700c40810400181490541c0c001c04c0d00404d4601c00181d00e80d040840b00c02d50300800380b980e10000f9060a41e2a00042d2040300c0c09031031010350360242c41c01250b441c0d800210040000c0407051150320700b48210708008001d0704da041000c5114000000820701c80315100401282e070410011429a41c540b030a000c0c0d000e90030f001c11002c6020402c000c5101d206440821000707940114003c08405c19000c09001401c1c40017034682d0300ca04010300041101da0000554203034007400740000541c44102014001c5500101600061540c81c0f40000c007003440700b4001a40c24060464040a000c55111107040c56100d603000d0307901c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 760329298 1250 760328048 760328053
    0x3060f0605220303030203010e0c0304030c020f040b06030108160e040c06030504111c0623130c0e040602030603010f0204080c040b190605030a1a011d030106180e100e 73
    0x2080110701800260515124004075149802c0c40361404450041041d00b080b40443d9011005111949070307142c081e58003104032500e6610b5410a41c401410204200e6002071060000c1d50704070842ea2900d4015640440d0080c00b81da4903940c448a00c55103429844418100044250700c0004681d060140072500850f0072841147c0068100035045014100c010029564400e050030b00b15116114091460300020400c2400c0d00d51600924048051710070100b06101e1100030580720000c0c2030b1007150400e410400080b002103034003406152900e14014160311000f00d91191030204400d0007140d4004512a640441c020048a452441100304900842c000c0455951024840980b9810168480c00700e0180081c030680500c040160104650031080e0030003400504040300740400c080650007a00c411102c1c6e21400b0740c0085c50400024031900703107508501d40052440ca80701c24191000e601c200003400030030001d8507207412021354180c0036114481d209074581c4551116441c41081900c14020742d8400c0202 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 760330548 1250 760329298 760329329
    0x51f0825050916020102092d03030f0412230706022103040308060307030618030e090609040f06180c0e0601090608010b070305130f1a07030c02011b0b04210306 70
    0x280b4150700d0000c3c00d010700c195942001100303c070740d444409230120207036540d040c141000f10f110b401c03c6c203070300b11099103900a17030090020604004210003501c090703801507500c04024001900b01424400111410003910710384480e01c2d40c080c01400b142080c00d448481e001c50705658016212074008400206140c0d400c01d00034000300e00068420004103403c2000102200d030040c0e04c0352280c004490901c104400c00122501d0380104050300403074121001c0300115854603062a01d800807401c200e02c0100010800403240304a00100b002e20703441074120001840f680507640041d4a418850b410180c014070341c00d40190000140c55601c0b548049099034503d40e503012542e480d00e8094142500310705011030920805000741e0408903103c03944000205031842ca9005424a03041042c0b503c11500a81010034400411514011070b800150301740d40079a080c80c1c00b00b000b608520324402004c405400c000e05007902e1805010a2015418091580c038240d020794042955400f842502102d0143c89000c0c0c10805200c2d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 760331798 1250 760330548 760330561
    0x2203080306041805060f101a070303051e010902041802031303030b180c1902070605120714180f120c150f04080307110405010513051f08250509 63
    0x100041a260f481d51000903c40145a68540c01e1400c1100e4004510129108002800c00d54104100051908040341401403400c021500e003544a6804042c041c50f403a800841c04503c40034500705123280c4107800650017942c40c0e1081c0406580644240140c1401d141c041d0818042e0a1084a008041001003408204516602030780504290200e40d540107003020103c00015000381300c01c61080021180050741c4130300391420340030306418154441007158800102448001d821604035a1400c24840c055102d0741e072803050458000d010100008088100840c449601c0070003108070b005420800c4400904403190b002c180581c00400d400f208203154400780d0245050304042040c11010072515000d0b034580307804105580d09680c0550b0064009500001d407840c18005402c01c007420803101250b040c80f041d45003200140000c0071143c00c94014a6075040441d444500030000c103c156580314011980c3c141d40e4480e942d80301c000c42c00c0000100c80d007086280301e8003800c0c1e80b502030940c0c1004001c030001c0c2d1180d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 760333048 1250 760331798 760331801
    0x906030a15120305030f010b03160503060f0a0303020c030d05160f0203011503050a0519080901030b03070f06030218031203010b0a020c040908190f0801060e24220308030604 76
    0x411044035080c071154010a0541e121034420078480d002c0d849066890800007017440d440035050f0300400c4a01c0c0207200303010f10503076084100003c000140c603200b500e13078440000080180b5081c290041e44040d58040020805801050301d45030603d04405592107100103040940d01c6e4030400c5040402ea106240801d000179091610840f0344900280000981007040d42442c00721440c580c01c242c03100c0e032145150904200c0100210703091502c4141f500da600242c01d9449129502070294140c5c14141c42d50421a566202008080000c01580044080c2d50743d42d064080c009600030072192465480d0900e48030498100000d140c0c01000b261002c9600e10307880d06c8108030031500f0140d000b604501840000094659035030041c01c040c81e020301041c2d41c1c0d54150340703200125010104084011b000744009550311068101c4042d504448142c101010a4045400003501c6845a4160303100d500440c02c21100411100c20302034070000800c80844544c1c02090750740400c0742e03003070340c0300050807883c3c1040000c2e41800c06 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 760334298 1250 760333048 760333061
    0x403080106201e1e0304180c0c241401210203030304030302090a0b1935060103021e0912071206020d0f021b0d0f0215040302030c060424020906030a 65
    0x350300560f0046030052100d03020a4001013102400780e4008241407114540d10304d9040c110f5802903104202445140300c4c013800543d00f40001401080007419010045d51002502900312000004200b00c400c640f00d01d2a0780c000c1080c003440d03144600140d030408000750100d82043c02c40741c0007801181150340e01d0343d04074007a40c08021b005400a0071000c0000d8030380c100364044d00d103007501950746162900352075400505d81c044900406000c100300004026000203201801e03441e00101d005000031554810005030301902c1a218004100d2030b880e03040d2185070385010090001501c00301e9944142950b10340600359640312600034100680c0a1302d101d40c00168160303004007180c807200040816250f83c0e04955508903003000403e0000c0d860f58114a210210080c03021111312030180c01d044100c0081c03654001d654102e0703108041c0301c03007030810049002c2c103000300700b91007072130f03608908443d100e103818900a5086203c0032086403590b095070210710b02d00c145900035078290510203403103603095130745110481015060 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 760335548 1250 760334298 760334353
    0xc08030a0617010c0305071e0f02031c1b0c030503070318080706050a110c0c010e060409110c0f0d0f0f0e06180f0d0f020d030e09040308010620 63
    0x240c4400002d0340c1c018101074a03205000c0e0310000112104101805019603000a16100400ca210700507000c0c006aa0605420b4404092500401d03240b03009200b86c1c510f04c104001d841032100450350300096110b00d034000d07014100300d1881824070901e65210a481e00307103007080d0040100c1d400b032001a44032441b0344d0140c030200041c030458442d400015102c440e0198088502a10003940b10410004515858040c0c98607440064070b089241c070b0b450b5410b03a03490340c0303001c41d020303040240740b045c414040c1c0e684400352409004800320400a40380410403050442c0c0c4950721107001030042c0070284001860105091100c0070142c0c4805c5c5034410342d5241258030880c0780300c0c0601400700650880e0102c0d242c00c4081e00003003600d4504030810405500130006030b050050320340740c414441081c01e5000611100036045034075034142e40801103145c4616060f20141041d501c040d13048080402008141540010454101c800c6503d4501c20042c1c2d07007849140d111281416051951300005030301c02e0b42050800104034002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 760336798 1250 760335548 760335551
    0x5041512080906070b06120a050c01030b0109030506012418120302031209030a1701031208041406041a061c1b0807092301141e030d09140d030c08030a 66
    0x80d8000001e60780c1d001580195800e01c0e078a0704005150503d242c0400380010760800400b42c2414070787c5c9e0300b03aa40880b185030b181090303143c01c000d88040e40600c110728055580308040d69034568541c0c80c0ea0310314a01c60900440d06540000d5031051050040040d04204001d0811881d40141421074842e0b075a85109030450442c402005002e101192104005001d1a8200055556101121001010602449481e00d4004841030041000a80303104e104e2482000c2d60515005941d1642800000315003141e40c915514001c0700d003048100103410340c071034062079000801f081c07075034582c50306112008440030302c0c0c0c0d01c4107049043c0c0707840403510207201c03181c01d0020b000c0c002c250175480e10ba510f0700f0b1403080d5004146d00c9454824111008403901140c55640b00d141c2c100c042c01d58902202c035004200c82c080c503240100c0503c01c04080c80d007084410314010b610050308561480340d6041006094100b41e210780d000302d201c01401c0110fa858003480103200d0301e07015640c4c902515666100c2c11010762001d001c51083d207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 760338048 1250 760336798 760336807
    0x10c090f0b2a0a03020c22050c04030c0810060e01030201051210081f050f090d0c06020702181503010b0d140a0212160b0f0423060c0102070c0504151208 67
    0xd01034140b0b0081521004000e003201420924000c1e2419084481c2c00b44640d8009890881403500b06c1c0510014010200c80840d40f42c4070400021024411508050488a884840460302e07020000d0b01b400082900c010820040d1340d942c4480300e9030442800020b0004100300b112140801503d041560410500c4403400f03052590f032101c0c540390500169505401e130300d09026980180459208859000c200f0031041507040c90b000115580380e11b5021080401d01940c0f41c094020b110b000c0c3e05551074258040c1c9542000c005d400011115920304a8102c04010440c041d80c0d00d0781e083c10301400d0a058405800e880500180e9510102461010089860b031445010f528102590350740e2040034544510743c1c094000d880c2400d012202080f4550007202c1d07840810024240c1700b81d03500b0f003264220b9822610185504c00908944041056113041403588894081400c400d0b00300103500401e111840303460003000d62690345040c0000d84050001040d4500c06410701004601d0610003c0c544c2c40e44901a101e1a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 760339298 1250 760338048 760338097
    0xc14060108070603051602120f040b1c0e1c11280506100807150e030a110f09010f03020402090d0b0702010c030c02032b090203030f0705010c090f0b 65
    0x10024240e2207030429901c00642000b64540522801e600664445a50801000c01d403c001e5034070502e842d0040302001c0700107640c02e40c1405403001c3d5405083c2c107118140d03940820000444094441078211114103242580f1040d16850000d1000c0068191090562103c1e040c11000ea500911840c0c3d84000c074002c483d850454007d18800d400c044440c0c0e01c118818140e840e080c42803a200c0002c1141030300c6801c2040030f1118000000e401e0f4201ca0454418031903207507042c0c01c02c669080b412000c4a42500c9050000800c100011200040b941c0d800c1d140b0f502d0300140c1d130b020414181c07802c0c810200250744070002440503007450b4000b02540903000d88044180c030401c0d40c0d80f1b61074100840c5d416006075918402c0d8500a0303410b0080740c10302407041c4001c40c1800403801c000806104480c03103d10412240700c005048602d5203800039940942c009081d030741c0355082020b4121881e80442000c840319440c100400050034050310504040d180c1d07900c00340c040641003100f4103e0079030020301c5c00880c20f0b00c0c04405484 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 760340548 1250 760339298 760339303
    0x90603010803130f0602070e060105041d090607021b040c0903050307060204050906010f021e0c03030a030f0b060301150c1e2603060d0201031d0304080610091505010c14 74
    0xd00212000b5980c444640c2070b10289a40c8940212440300c95058007001000d0780054000192420030784404400e8640100584491244d030f8402041403544440b044a18030480b01041c0c480e030041400c0da129030351009000ca84400b071009000400100703000d404030071030900c0d610010440d42c03107040c00720806480341c40341451508625002c44e42a500010184081d0074440a503036000030342030801e4800e00002c4074001e9114400e0300345030400c4980e0b185203009040800c00c2404200b01c00502a2a1b480484540c000c2c040d000d0600c170240b0140c2801c91012081c14003904030781c100c4000d0a100c18150052510890702c1c514140000e4a2944400d10740203281c00500c0011920075104560100c180c0c4070b8841e8038440e83c19548040c042c480410b204003e035171f40311404400c52441c0d092800003001a9034002450100700c41c41420b120f10322020070007141074400080e100e8001c95001c1a0b444a2903507840110301920196010181042c8807a8820840c0754004c50f6085a485e108081030704030a45052080351 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 760341798 1250 760340548 760340551
    0x31506030106033302090d060209040906290901060207060804060b030d09030201030507030605010518030a0b1e0903040503100b01030b190f0605030402030604030f1b05010c080106111b06090603 85
    0x422079482c2c0903486105261603485130008401c50544c20800308400040340c0054144014080940001e014861607545030700610110364807107401c0050ba48503106501c00044842a90401c442c24410300309200d2404818141c100d54031503000741071449c28a4400c55003410f0240088502da91039454011300d40c8e03001d0082c0030355528140d0720744e100c10b8031307500004065030f10144c584401d00d440c1550520407070760311204a520700d035440311141343c8500c440c40c04a450001940303c060000c2c0d880c641404003508c0c0c40c800c120741110070700356007650304c0e00e61544d542d4481c4154031403264964482c80300c100400d41940c01a001c207410505000840406400220301d503c60450742860350381156403403c0c0100350401d00c004001c5e05451803c2411840c1990119a0f41c40d4064000b43c140701f4004403202e0098807450314040548070f003d10440c503450705464002d020700951805640810609400451032a2090030007201e00c04d00e1070001c0408507402c1c40d0039080c61030350f002c0807a004a0100f013101d11640b929001103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 760343048 1250 760341798 760341833
    0xe030a140a03091e170a151b020615040b041d010e06090106450603050712020d0318150801150302040609140a0909080a02061503150603010603 63
    0x1841c0003001c07454010007241558000f0380b80d0006146102441102041c058010345032942c2c800c0b4604602181c0e0589803c420400007050a000d0103500b40d0200c510741c024450309a0b0b040c0c1604820501500d080c1d0b06e4110443d401209414140106511440c107500034480c807000144c00003d0343e860650803084d44003806031412200369140c030150020180d0401c9529804000384008100b0769007040a8400c40d075400e0605002e29142d1001e10040d084020010003080046944090000c0c409452000016048038401a605409010f0f0000388600600100400e603503402007a0300e400001e01d40e0300765290041d0b82040028003454840c017181003043d29403070042460461b1074010031589081407404a00b50b02c42c440c40205401032004100741c9801a4642c41603d460740140101182c4000120303a40342e170264059404e060800b41481e003030010103801051484419030039100d03107a5030400e42d01290b542803100070350590b1140508246521004e10502d40150004001080c695920b485441c0c01c50703452500c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 760344298 1250 760343048 760343053
    0x7150902010e030105060a030b09030408070303090e0f0105090c0d09080307120b0d020108180f030f0901030510081207082106010917060f0421021b040911010e030a14 73
    0x640d0b03002808a1140c00c4110000d00c040d10704a00412440f22071480000c1070142c016001c500410f20901c1030740d02600c1150211800b80da03803804c00034080e140d18803900c00c4403000d00001c100300d800d40411490507600302801001850310343d2149510281e000d122045481a603c40c41e06001800180081d0b028803031540d14050701241c10340340380c070840d038031a40307030754807d402052400c0300603608040324540c413000d0340c3d0401402806a600f81810490781c0c014407410b0740800034400900b0305801000e820705020030380c0d0402481e03a9801500a00f00024080c6607001d6001e00c0396203c0514144004000380352140030101c3c2040b240012400a2038554090000e2000c2c4e410308204c80b6590203a0070380000c1c00100300d01c1c0500d01894803031a840b000050715035038130341d245640080c052000e070440540c118140e04031a10000120400002e4491005200d42c6408002000102c09180781600500e10400d80204904041c80b4000c4015200090642c01403900360080c0341c054804a03100c102040d80058180b0007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 760345548 1250 760344298 760344311
    0x70807200a0b040e0708041a01030803220c0306051f030b04060b090c09101b1202010e0a1a06010c080c10050a02040303020d0c080c01060b0705071512050c0715 70
    0x7008026411a0042c1d51a090240400c200006800f0358540e0890980c4c20940350a880e03c0c01d06021003520a0205001848036000000030492103034011840f82c0c00c01240d91000103940c030344440000385000c101400700141e090052001c252294000c03900701110800c003110064103c02440300e0300b80d1070f501c107a5506812008100510619015030207500c10110789032019441c20102c0d08105004203d4003500450700c40c049409914064410808005101da42c02e0030700c81e8003850940f01d4401690703503002c0154207041488010f4031740041c820710000d52080c40000d51a110450300b240200c401840c407410080c110308010041001c4000401044403400c0251040c110302a9a42003034910180c02c680c0558070410080000c80e50204440504250615161041940f030b410314140c14081d16005402079481c180002408400010061100c1e900c590191000d16139140152180d903051101c0000205500c01e00802d621a03490303012641c0500007070301d060b04044003a00c60fa03c1d0303644481c90003408180c1d00c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 760346798 1250 760345548 760345613
    0xa020406091811061b1c09120305090a050d0309090b0603062b0204020301121103010c020607050307030905060f040209064005090703170f040506070807 67
    0x1110050056841d080c0001422110031808001e5112006010b040c43c002c2900031550f00e80049480d0450441c414031031500d5405060350b228900900401200200308140d801e07024044d14000089458049a080c481c05064070240e0b2540d109801456001d0703040740001c10fa0f60383e0407035607011181c000c4e41e07510050b0342407011800c100c03a00140320612641c07051080200950754041c102c2107100780d02e051641c00c3c0e0511001d103142c6913a8498020b5002c5d00200003c240c0c41c08200d0101d032807d009420368038244850307800345402c0712000011400181c000c9400a98854026402541c20011500e00012800042d480c0d0600704541a034500f0440f101e00d20500c025071824001c078030f421517000ca80401c6200800c507030302404003a403842524022100ca501442e5000e041160141d1400030a1501b80940d282290165440b046180000c440a6000e14003c055043e0907005a9809243c44100645818180b40130460700c1e4000c2c140c1111544000c0107020006601340d84003201030080c440c00500d05100c0d12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 760348048 1250 760346798 760346801
    0x40b0c0d0801081b04021218011d0a030e061b03040e0601030b0d0b0c120901090b09061303080a09080a030c0207061103180f0d15060e090a120e030a050a0204 69
    0xd0448010004400300602150030f0200303000d40b4030190032003002d039003000200115029001d1041d01880d82c1c0c00680402a508a0795241c83d0910107911707001b04486082c0382001e400352040c81502d2030710356001e4115180000e01811115940302e600802c22400c0174072180c00c9c100c034000072032039058242d00041000c0050a007248261900104e0900b003e020208113000440d03002c3c3c3e84280080d100390390001c04580400c00d500b00b2900094080040a0014500641d030309018106501003218410b07101d0000544491020034010b000318042040d11000074410385007100d00780c401030a0702e440a44d03620701c1200080c100030001c1c07894a84507100030078540201d01002e07003040d51580c049003e200007015039101108002c001c48142d440c50512003100001c0820200c0d681001c09040c107500b02542802c0a01445021a5111804840400103200150311244d10001040090703502e941c166100c00c90140001c3c0d920500044100300c00e01e0210f81032400740c00004e10b4601c000000344c0d55500b040110400b5070809 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 760349298 1250 760348048 760348063
    0x18030611070f11150f180118080c09010e010305120c190b04050705060a051e160f0c120b0705071103011e0e030a021213030203150610020111091212040b0c 68
    0x4484d080d42000d4880142030b915200c0e400030b40c02e240c40c66803003a5185078003031000f0307200640500c1008000103880c2c3c1090750f61110302c0c2001502c22035a200000440702c8c2c004007202d050765804005880c201419403031007400da07084600403000354064032480f101a04221640c0c24109801050b410302c1e04e00b020b083c4582800c0450704800c2c0100d10400001a1164001044402c1e1820260004101c0c88401004002c540140c85a270074010340c2059842c030500401c6035040c039115001d4004200b603543e0f21441516520b510044c0286190240d00c001000350b40200041d03e40da9025040040222101c0030000b402c41e509144640c135813000b00803220746030035414410380724200c0b040d00c000e525016000401070741d03c071101c4151150118002400100040b40c1e14030340f000456014044a103038030341c0e0000000c4c59a030200c40c0320740103480700d1000800030381c414051044c0f14511024840c2c5002c10070028001224620400e018245c404c00890020745415040184014007410361000c1d02d5035480e01c0c40c0340c02c2410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 760350548 1250 760349298 760349329
    0x1201060806011701062708010c0908030403031b03051903020c0c030303130b040f0b070302031e06100509031509060603061f05040c1215140118030611070f11 69
    0x4849264040300300c102e60b1141945c5850038202c00d44205240780360240803401d101034190601c680000141d40380e05400505c5903080a8940d204080d854401107940d0340036901c0042e0004501c50000d14018102d41e0040d501940a45000380c50100800c0802012101484117a00026800180c0d401120340c20b00c01601100340c22409180341d800c00c008604c4c8a45038444018210134040e001040c1000100900c0031400381d40308401c010b072450f0501000e0025007044449410141c20f00d1a00c0d50500389048045120b00030040299045c520b40400c220f481b9002010140d406110340e0701e00c005d1044200c00b40b24480c41d0140000c01c50307490103500745800c0a8001e410180c0c0702c07042d00b2007400d00c904108180022b480050303078005158207001e102100c14105074500c00350349924100c02c45c2a03030156200c4200903958044c0304642e001e60f800740111005040310402400001801c00180002581d60700a000c0c14001d10f090343d410040a0b40b00c146480d248450125040c06400b10003070080d04092400c0c1c12a00e1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 760351798 1250 760350548 760350557
    0x6091b05040b0604140f1801031205190305280204030620070f1b15020105010f26150f09010b0d120e0312130f0b0a050406050c12120106080601 63
    0x82182c0c007041d4107003c2c40c0102c6800c0500f1541c0040315840b440c0d0000d18000b4014400218642c4250724a641028280800d5558100303503a41030080500403011680d0101d140520300c4070361450032100710002e00c001380a070f82d090750101d0046e06061809101c0c40003100c080841c016a00c84c9180b400300d0031035070a000310b41d4000c10420b00946000100d031069607078180d00440031804903882480c01d03555042c0f4680d00414542420040490540d18511b41000b010a49400800442c0d072a003040c003065458910406a114202848542d103080039a038441c841403c0f240210380a210902003c2c070811081100d90b20a4183d0301800c0001400c0240a40c1b0040c003802d5a5420700640261902d95a03a410843d0603821301c007205400d1034031750b2803c0054072803446d030607040703551124080541510001c203107201d002400d48850402003100b545100484030b44c01d0300354644600e094034180741940c0e290020092090b40e800f4a40041030700b41d480d000142954003100c0c070201601d40c14204042c222032009000c10b030400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 760353048 1250 760351798 760351811
    0x60c110f0c0303030402012a0c14010804020f1023130e0f010b030402031f0c0f02240712050a0c03061211060d111210080d050a120906091b0504 63
    0x10b8401000f103940194081c604080500e80b504002e02080034190000500c0d5403a0b0300045042c00702002c43d4005a0f15008010180d8040362001115055015980a90300180120340c0c0c0c0090302d41980382411700401c90030032811000a01c80d4074000070310301d025400c252800004000503401207c02074140030384580c402000701414125150b4902040500030b10304407400001c00300c1d0a555040143d9000031080e280c0083c864149894490050000000c150000c106c00403500e0a1003400450f080300c90314847c1c4542070580000c124510000c0380040c1c014030a12060f06e00101e1451414003c1502c00e049144010404120080e0024212140c50b0f0104000d503140290703841c0000c000f4011315031880d40071120f643e00d070041c40b07141000500e0132400b0709840395800901c0b61003a8659002003807090300300d80c01c074250459444c181140c8902e070107070250b00000d00c1046404082405140141104528003200040c003000319950a070896102900640e80c0c900360000e440040c0c41d0003039409028010543e410303c0075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 760354298 1250 760353048 760353073
    0x1d0405010f0e06092806211110020a020d02010e09070f021605131509060303080604060905090303040605040309151d010e0f01270e0a110a1d010903060c110f 69
    0xc500b40d440c0c1c5150801024080e40c0880d20f15801000c0035020004c01099007107035245105807c201c5552084070880354058400c45a45401d503010f400320162074010784108005036003040844809800c040b8144001e41004000649840d01c86622038041c5480d0075070b008801800280c600482581c5602003242c08060604c45900d4209a01100724410b00c004120b0180c880500c511480312600040c2d0b80b680340038030000c28103511005450262509440400c50503480b10504025520100c9207c249641704102040024100c0c2c0c0c00243d1060180c508983da40d42c40d613110004045954484000144081904c502d0300707d0003030740100c0c3d8410309091140c40741a08201040381c440d4185810b9040c80000400c20400c07080030f500c80034140c04070300014000c0f5501c030380039641225000d64660170102d20f00b42d40e80340c4131540c100883d41010b501da01d5a604602e00242d5040b80400c280810904000012800000242090003410200711458645044000f56a4405071030141d000b03071000b185600000d1407000c0e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 760355548 1250 760354298 760354321
    0xa0927113621030c070504060902070203030a0c0f06050a0e010c2a05030904091a0c0310050f010314191a0a030809010c1208160518011d0405010f0e0609 67
    0xd0100090b80c01e280c100400c036142406500e590444003540780000a00300000c0d1402150803000c1d203904445c10842c0d5500c40c00100124003030254001e41503801048038112070b50148205042c0c051281d524140c000300159900010b441c000d0740e20a611903151554544050428019545c142c9000d18101c01c090311500307103071150704c51410350b10140181e552a01000303000d4148111680400003400034400d40f070315481c1004100c808100b6481c00e00300c102c000f050001c10001d04403809078403054000c6042c2030406e0308100c00c4a5180130340f0350504d903851000d03c0202004c210340a2041d0b6240350300c014800103080301300c3c0654503c01240c0045001a07640e030207413540c3d42030010054a0300a2003c584602c0d000005854644944002400640320840040442640901c21a1047c000003105c00c4850700203400a5a0034058210700c4d5801816480c0360381a17951061058034a01c002c0003d00e0300004d43c6002c08202114804e82003d102090090010300001c0c81c81c901150704107000b660805401d00c0d0059082c079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 760356798 1250 760355548 760355647
    0x11701140601120204030b10060810060206162c04060b1c15030b280501050d0b06010e18060f0603090a110a05060c0c150a092711 57
    0xb418401c0440304a41c9034285a4140c501666000c65420340b03d05120289000f40d94061042a001a28000015158441c00800d000455070150010140c5841301c4141d0f00e88035440049035410403089919403100c2040340c04914581d07442264946412443c007005000c1a07841c5604144982603080203000300c1040454044244814003440005540c41801c40c461001802944050302e081340003020322402d0b24101e040d0810611040d240c140c00d0344d01190a100070b80d1800d118065200c00155440c1c0041059128007a6203e01c051500e02224054200014807040b40508110138441102c4200200743c01c008991480f001e6048a045083d0320b0a01c03881c61340d8800500e801801101c81401e01107440e00c41e003841c0c002030100101410703120790401540300d54403103040548500c2601d082e810f5410f000100021565011201d50703401c028541001480401e14032540380c98820310006590120b03000c9031510132110803070601e0106a9071640e003403500c0d00d03481c02415a8070030159401d03080781000002081420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 760358048 1250 760356798 760356811
    0x180a0c26060c070f050a050a20040b061207091a0a0206010803041a0706020d0219081612020c030409090303050702060703110a08090a020a0f061106040c1e12050601170114 75
    0x1880d84c60b00c5280150810b007185c0782c000c10034841c2c4803c01040001c0000602440c1c0580c07030940048024203000c200642e011405110f400450802210f026119030018082d4001c0c43c07424443e4045623103010580308500344114108002c3c0300841e103925004e40c14490380d0f00400c0c42d40010350400e41009200e0441050300d603001041c0c40c000283c0e000800649405595007102c00110440d201c2502c20013500590003046082d200040c402e4000990001a10840e285c1418072a5202100e03c121501c00000a6104900c01213440c0b01c08d100009081d4518050b402200b0300c242d4020410b4288020044e24104000c0c21070300506040141001405080304141d03907031a0214070341081c0359281c220005040080d0302c44003a40184084902040c00341c1302000e002c044850036901c13021040f8a00c008983ca0b002c040d40e0050078800d05100c100300004405899041c40700c2c1046450407802d40d604810024081c0440d4100c4031608020010466985240d81c0580d0103101c440c020b12901c0024202c0d51886100102072 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 760359298 1250 760358048 760358063
    0xf0105040f11161a0c03040605060916030b03011e0c0905030601061e0323010e01090b06040519170714041109041d0a0303020403120203040e180a0c26060c07 69
    0xc14140803085000000c0405130b062100c2e140c3c200510704030304580c0121015600385c3c0c10b060101c1d00508003c54102c0c46510b00c041603482ea600000d000303e0140c20b03244181541992580150842c10050904030783c2c0c103038410200041c481d011004007411044c0117511107446a04008010800710381c02c5903504090001e004194151711030000c800703500604101920178500420b401c1c614000c3d1006101030760584840641c00035503a03a88012281c01d450a13a8034683d0000c90500c810402030804d80c55489191042610507586280c846c42080e4004501d0802001150f02c003240802941410719100070001509907010f101d400c040c03681e0440a0300c6581030260207039035a100c00e41d420b102882680d05060440c4800d0f6086c211681c00c00030040c0d00640000d941c1d0320b00000142c012140004100c3e0211401c1c1003580a6035901d6a90280e41d104002414040f103000703000030500092503000185c0082d0441144681c00d00703091780c03841005035901e006002c0c19907014400340020081030206545582d03610412 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 760360548 1250 760359298 760359337
    0x20a050703171314040e240603010f09030203070b160504270c021b0604150804050a1b060f020d05180f0d0302061b0a05070b15090f0105040f11 63
    0x3402074203031007103c1d06115101e4141801080441c0701c040e010100d1202164244500800c1c480c0107a01c6081000f1001c551010003201600b5000f08850b0b0b19078840b0000300005000c0e03825079800b1003070722910a07080700160000102c1070300308052325403c641c2185070008011450f0000c5c010240882c4174501600486480160965100030780c80c01058078015005003080c80291060b080c00307982c90002c541003070101030f080340c10004103080c0641a1001c0310403070319181d1590490800295038890300030b00242e945025006141d0041603400400c95071403041d030194004204d10309a07000300400341d0100381c1c03021900541c1803524102c3c0c0c0181901c3c40440902600080030134102c00180c44003595081542e00000d07d00c8511080c56000304030035200e6501c807201004201500d040b556168400c10000c0c5010560501184001c10350510030a80d01c01d28990070340c0050f012550025101000481d0180812000c020041c02181480d000e14200c1c156085002e011182082100c003586000f15140b02105040112 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 760361798 1250 760360548 760360583
    0x5030706050a0c0b04022e09080303061507021c150606020d09150203120c0301090b030f4305130b09010b07030327120f02190c0f0b030405010c020a050703 68
    0x801d1f00a00240c04140f00711466224441c40c203002a80c1070b01c1808600c0c05200080c0030720300481141c0c840c0c20004c042100085002400140b141c20400040e6001041c00c0d030607004490b450405100080d0081c0d80002c90074000184c01016140b09411a20454008280c60310b482c641103003121040d120741803541c4070381e1820424101d2650040040c0304045051481c14410a4411300c0015416240031110500c030b520ba014081c560b0300d64408406100642c01641005001e81c540900742c010003204203900160030030b00c42280050003210b03c4140703202e5020540b0800092403c4511141c102c2c10340c4900780400030501c130000d122541d0501c00c1c0c4084c0c2c0000901402014826449070715080340f034100800c0d07168221161054180e110b60011200f034003400c00c0b401e00d40c90151a150740110283e038007c00303000368409003840f00e00c60110411600801800400f1440301c1240c0102c5025295885c002500ca20740703030522500755900da00f414001c5d5003004001402103000403840340c06132508000740b1044032124a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 760363048 1250 760361798 760361809
    0xc0c0321161e0b0105030c09010e01231206100905090a0b18062404152303010e030d05010e01080601030201081005041b11010608060106030e0a050d0905030706050a0c0b0402 76
    0xa0940e4000b02290040081115520045040c0c0748140c3c11a120804c0220901c03651060a0080300366295401703004206d448100e5a40e07000d075440d0000884050684071020880646200507000102c1d0442e10030480c1c0008003080243c000e05004c90f041c0710904081c45800d40700c50340c3e00c00c003819041a000001e04803901142d00350046c8007000341100d040e0718100c0c03c01c0c02d4500c94001101c818000300410480c0c2440c1600480040e60824884928094909045a8051902040d6540a0340f490301090340141e40c4c01e214200000303424074065550346140200e800c0032601c050708010a50308041005128030b10002444606407582030038003010f2074403000b96105c0b91011540c44a03034842d05003030b009450000d111166907114111611500c0a00d208540c204d400d0f24003500400d140d5500030740041040c44e200f90428045030948000b5140d84101d542c031807a061a03401c89545006c41c1d10903104004e030707003801c200c000000c00032880d1484c01c10424850091112600040203003196904902190a650f03d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 760364298 1250 760363048 760363073
    0x60601021b270c03090f0102070b01270614010905060f0304030302131e150309020d11060c03040801020415080108030703030f02090607050f070807080a080a0908030c0c032116 77
    0x4414482001d283c51a0140803e5004445020180c000c0b10001d00302074030f0500a1313a941640c4030540055036030a002003003042d01414803611142030151101d614002c0014800d01001d08949118105034460240c000342c00c8010550103640141070401040362002010390591f6005a0b25113000f590303030b40c2852201c030519107035a0044e001030308188480c0c0914501005c4018211103408448030b0705031400c001d0a4040b1100b2078000703034100303002444490006040007542d09110600130105802d00d6040b80d00245582c00c00e8100003010b07980000d0500c40031614180d04007545c502840c103204a581080c24190b01d900032610010281500c07010381d0078807101c80340c064074030041014060907240e60843c203001d640d469201a0381c07103080c0298400820030200100e901c00c203031044c0c20014019084690b4608001c0c1e40b00c810f9000411801407400305141005000802c1d60081d000d00410607650300404040c105030300c0d0306042401220179040349a01030541c1060fa503107003480100d501c1c4584030f1420412101c800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 760365548 1250 760364298 760364359
    0xc020a090b04060f08010b030c0f09190e0307030e130e030d020906040b30060a0501121803020a03080c03160c110301050a06170328020c21060601021b 66
    0x1c130322401091028056101c860301590072812651481c036940240000f41c50b01010840d000075050f000206500241c480040814070407080014891030704014090a680181d00d00701c00145411101400503e800c0c05130340c542c11000c0034100b012002d2005007503039034801c20288103862078000c00d0704038035a510281658010b1107040c2c078455175040c0207401c00c0341d802c111080a40d031825603100c0c08000300c40c0d008081d5106110184c034030000941004019200000c41803100030905440f4580085003040b92480803100030b00c2074004041c640c000d1718015040c1e07000100b420800c04024000c10001c5600080c0c811200d883d54203044403c1a86401c0c41410705001660481d05503080c9018408a101c5541c0804103c810180000c500e200c0880155512441400510000329450160140c0c4131304001009038801042c500480d010018408003085900440b2514144c01017488902c1580c00700080c070550398020006d02c05081c0c1c3d000151085564504060000c5004401c007038080d08101c0c0200402110620 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 760366798 1250 760365548 760365569
    0x4051e040906020d0e070f0b0f0903161a0307020601052e020706030b120a0318090906090311010c020a060c02070806090106080705011809050a180515070c020a090b0406 74
    0x59410240701030344c44a015907091074544030343c3d41526200032039003c05542c0142e4400030050328007000a0110f42207031003110081c140030454001c2c2aa07040044d501240c00701c8041d402401d2070007075040318543d04418034000080d020402c110710785501103411815038108890381c81350f0035440b00d051042900d4288007113943d0640005050380c001c2d000240d0604a41c010799081c060b0480003001e0000c4103580110b00728160b4400200080000d020340030b03032001551615900009217603540c41e04801d41d03040181c1911072940e01c2c000c20040c1036010350302e00e0810440b40007d000718040000003d6548070b104002038541982d506580c2d030b000d8800d000714070050121008443c000e003801300b0740c0b80c024003184c41058008d100b080c4d00001c055024940441a5414100540905d2850070701e5800141100030700c05012a5500d2160f03d00302124103a01000040c001d034001c2602d0703440c0c24240c8a6002d0050039690a000d8043c8142e0700582d154404e030b10555254500c0402e9054946002c40c0140209410048001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 760368048 1250 760366798 760366811
    0xb04060f110d0e0f21071e0807021807170a0f060e1009060f06050f040b03011212080112031d060a0810050103090305070803090a020a170601081204051e04 68
    0x1a00c01d8000340454080700342504d520050700c0e404a607440315200301c480b04400f001c624016a1303050038005016424001c0801e10070b007030085054010b48101d140f40444480202151040075410314190b90701e11856440e140c0e2816041c0240c001c1c0094681d881828402c4001e0300000d0288051a003001890312041c00741031000c2c0741c6502040815081c00c031344404020191700030000718001c080c000c8400f110100a200c0e55286d040450231560342d40700d0101130680c40030400c0005a1000b5a6001314020002d074402c600380b60b1410706d05000c002008059000400001c40c00520000c2c0502007064851641410003c22915040114a50016041d45041e43c046030214841c0c0a880c0c103c9800e0348110600c1207a02c009a0311fa60064045988642010f8000303102404880c0004411030001e64004269000300c07a608070032540050342e030010542203c945621801001d0040401c00c0140700d01601103800503080e40c0b60b608240c090a4080c5203e0b051043c4503510250306466251513000f00011030140003031016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 760369298 1250 760368048 760368067
    0x15031e0f0206030c041a04030c12050a05031b011b1202130e0711060106020d0918141021110904020a0e0f0105010801120201020607050d0b0301290a030b04060f11 71
    0x550464461114001b04c00360b00440881046800c1760256076102159141c2141021400b81d407175074040e00115401c0c03050041c0300380418410405010840500d0001600305100d0210540c25140d00c4001003c100c66402c035041910340d00840d0011040f80054001626180782a42612840303500358000741003000b042003842180c9900054142d41400404100d50069a803100220b0352600f6043c1400c000500300c3c6401d100304081c050303c14190a081d143c001c40c400c1090405010307007600580c0c40c078800c2407c038441042052140310809015000c210740940d040555511100000d007120722049100722601c800003400c540e91515503c1c0a030a0142080c280e40c501240d00c031144031001e0254034003240d0200c00008540c02c0d41d2001006079541030780030b02800e468005017610560008111002c40b00e4840c0d82007059924240308103101105003202101d01c82c480c6030b00c0c1107207040e04840c00760b01800301003600740086103070754001315001b640c0488005000c40716091035500030034000075504440231000400a61 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 760370548 1250 760369298 760369321
    0x1e120e04140a0606110a03051603120c020d1805090a0926041d0606090405040c080f06041208010501050711031006120b061e0d021201140a15031e0f020603 68
    0xd5441139140e550400c5c0c4041d001d299a180c84000040000e24100203501455200200003142039109082c0210440c43e5030b08610241c0703031039040f02c800590100c00e8242d4000d0707000e2032004900302490001c07400d075030414012660305c0320028482d041c510b403640141c408008a482003c41c91380006480000ba401507a0b8641403583e00034410680b400700a0014803288030340300b0003068001c080081c400c0c0d01c0e10302d015050201400008200b603410602010002450520601441c07400c00411000303013a261400f4600203680c040d00312198400c200800e0010f00859030400101c13030030f05400c0642d9102d00c04001002034070b008200b08060701924202000050f8420803041c034203961a2240390100300d01c3c0d175280709110320300841008403c4101600c4440182c5428030074040c0c03080600241c05041d80b494442c0319182520b03014005905002071010070007210090320701c03503c500082c4c03020740740e82260720b1510703514140141c1914103110309152003001010000112030b49801244e02400140e142c1c506175030802e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 760371798 1250 760370548 760370561
    0x1608030903071709060307030b040e010c030c03150b22180608060714040b091f090501080106020f1002031f0b0a0e090405060705030402180906041e120e04140a 70
    0x264a40850360034000b400c1034600584d000c400002c3e04a03811941d07107200460190035440c400c19042030783c07038100b14141042801107081e00242e546000c1000060120300404555203030410320b8034901d00210038024244080c0848103e800c00010790401906140c0c0b450380c0b644026480684200e400c01200c8800c1d0805400003000c840c100300584403035680350342c415940040c0ca4040381c901c58008000c180204d4649801038a41c03424041c1c150901c07403000f020b1100100152102d0480450781200d810401585d02004076405000c1c90b2014100342d034020b80d162503031340c60b0180348124a83c3d0048000b03020081c41c42180b400c42501602504a0140d41e00910b01903a8400c0d280e42000035030307048054003e401c0084101d40281d601c04010b001a43c0c440c10102d415400c0070300101c0e400540000300b0302c85146048080313070083d80118040c024a081510f40315811010601400100701400003080340485c1c02d507103071010302400307604005440d80007050000f401816014140f46420303d442040c0710fa002516403001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 760373048 1250 760371798 760371803
    0x1006060c032007150210020d05010302030d050c062202060a0306030302011d03070b060102030426100e0312090f1b150f18040209090c090108070f14160803090307 71
    0x1200b000036a0014500c0102c022503145026a0010104001d40c010400c428001a403242c03060740d007078190280c1d0900a0380d08c001c003100701315619480103105500d4184500301410307481d41480c0340b4101a16402c29207c890040c08002a0508014428160300604814180c00345c1c1c020030b001c0c2d03580078040014004080c680019401907280242c100b000c4104086e10321990b00c0c80c04003c0d030610449503a21074030202e0080c0264118041400f00003080c40740012140461800c0741208519045a0b180c5185408280d55650700305034200003180701348187c044101ca002d8030ba005400d0300c60b607840f801407600c0e00c00e40c0700c28074605105209441074a900c40d5560020300d4a0111000009002988070000305030184003032004400c03000708410118041d405645003100e180280015090400100000c0c0c40d80508451003010000d0029040c1495a0301c408030550080117418611140e280d20f00c0010171504102c001c0710030404000500d15a0000300030701d0a480181e0110146660f840d200e42020380300c1c2c1060404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 760374298 1250 760373048 760373057
    0xb0405011d10020d060f03051c0503070c0b0a09050f101821030e070f05031501033504031a0106170a0216051002030717010f171006060c03 61
    0x141c205070034040401d80d40d00340c0010080040c8610425490000d50040c100b01e01d41c599500d10000c0d068035083c130f1200c0150b0140e4094405402e8400340056088040c260480c1080001c108000040e50818881603d85400a071600344a40d100c2c0381c05001060f09060151072031240c5142c0e00c4500d000058030b03229038041e03004184070340c0401501c6490041c0700c0c803000429402c1944081c41c40782108100c8000003250503d0041001940c101a03982132407c00d410940301140c00b42c1c4284900e0404000740241c1580c0240e140e9069891a12500302e003100740030444136040d5249030a032514458031220b110302c407041c003030310143c1e2a940c1e4604509540c2e4044c801e41c0401040b2400025058051304203204c10241d02a03007495240d4640724074200940c130954174001e03900361403400300011900810800c3c24104071303554010b0792402d040d0702c050246003009005038200101c1c00014003c03046242c615000b240c00e0b80c030040d004048070315012400c1090070400d02c604030b07107000000120641c1c4401d802c0710f214000d454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 760375548 1250 760374298 760374311
    0x9080310060908060601030221040602251a07120e0703060b0d03020312060a0e09150a020f090603042414160c021207231e0108040602250b040501 64
    0x252200702e0940f0408009801c001c001404550080d00105039629461401a0b44d00c0d149002c2c10192030350a41d803d541c1e01b0390204034003503501990031460a00b11580c5003141c040c070500d940e501080e4102060b1425124002c4000701e04c0d12406880c5a00c100c9511010078854003e212841c1c5030746502c244001d4490a0800140101c54140000d182c161203403d039001c0c0d4544107214002011200340038100d0f5402c0109040d001034030510080741640600c0c0640d0181600c046038085244c0c0c6550058003141d54584104011802d04a1090455045940a86000d0f8480c0e031a82000341c1002082ca5a40100c0d62041c0d2641d456810b150b840341c02c000c00c002c890840a519404d50303000b103070140d05007141d000c2032100c003424001d444c00c1c26042c9440328001e41150419910360700e242845800810ba1480500592a16550f89180201050100c98000620390a82c10034031000280f681d84083c1003c4c15290b07000030b0301d00e006002c4400c1010100b466044507106c40c405c03460203490200c1c04803007e0350554600311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 760376798 1250 760375548 760375559
    0x305190309080a1a011a03010320090c0705010e0f03070314040b070f1718010804061e0c1115070807020a080711090a0b06030606090a090c0f2a060b01030b0409080310 73
    0x61b44401a001c100c401e038216802c2d0f5580020341c00b40b080080304100000000360006031b403280d148a106403038080740c050326142d151602c182520041603400216400021000e01c0700840081541c65068140c81c000401d1210b80c504020b5912842d049071410b4500082c400c03081c0803408060503e400e01c40c01d248400c0b95010b60503040e50f030052441e0b08c00121036003194000258803d8850740d4000e030180b10000b5141030100e4104281d410102180242503441e0640c0d0f481c0301e60401c1e11107030301c410810082c0c000d603058141d003e4010000245110f090250036000f00310040e10802045003159803200d4140c0c3d40d80c1c41801e054008414580082c0d11803410ba5000a01e2107465008807440180003a100d2401c503201c200800005400241c2c586400003442c5c000051145000d000300071004001c0d8441d5101c3c10070250700101105541c1080100c41801d0000000005140644d003891480c0c000c680001d142428034012406826041d1140e54054117254440e8140891040150f0107a40748100101c44281e540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 760378048 1250 760376798 760376819
    0x3090f01050115122d180c050d2a0509010b07020102060c180a0b12161b0f120e01020c010201232511060609010305190309080a1a01 58
    0x90090112100c207107140403542c01e0050385005484040c00b1800f080320954081c1060111417140340c070408103a00798407601c03503800661281000650b50100b139043c07419481d4a400c800f122061203154094880b090714101408041c0d480071141c1030031090402903030340741c010b0603507000c1119004251240e60000000510200154200c4a016a040e00580099520300201d4200d5070001400404091454007600301d1039a6015110405011200006511144aa8180c400d421002808412001da80600c00400c071600080341907100700210441e201710444601c0d011803000c448240080c03904014001921040341c01a10742c0f4400d801c20781c2101e0110b5000d600490a0743c8000442004a0804070712002c1d4424000600380d034132001003021000e031410512040d8181107043c1020f44002503180d40314081080003880041d400c62011180150b1a5055032182500c03582000041c082001c0141d401d002014041c2e05000d00400c14002030300d500000d141020b00041c241a04809459042c0301d00108250068 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 760379298 1250 760378048 760378051
    0x180103050a14010b03010c02151305100c05070c06081503011a150403170714070f05090619080703050f1c110109020901030c03060c0930050a03020303090f0105 70
    0x10000c0030440925121003100032030340c42c00900c565403140c85492060310300b4051004910440e078020000764104295001507540040c1121502e000c1007000e4901081002400e0100112040d20015801410110a507200d20400b8001006d400006000080850708070104600c2006000180800040240704040c00c076200c11685002c482d0390118244c0207810010383d40e612000e8200e0703a2a04d0282c990301c17201c0d4030f04403544915116520009007402000301406e1300a28800284004010b010709100031500940c0c100d0043c07074020966940016016914045446001600031111040d056280c00d203c689078034140c00192164400d00c0000f01c05048001444900c0001c0000ca03050600d0500c1c100b02e4108074641d80182c1d440d92524140340259446c401d50b070703000390310420700500c02c40d1441c0b5160060f140341c5900b400c180542c18104110540910150300f18010b03090040c1e03103241046810000c2d2400c600d41c4003526510403100a0020541c0020055000e058050111100d10361041d25150a8500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 760380548 1250 760379298 760379303
    0x1a1003050403022104080a2303070c150c0c0905150303040510080612010f0501150201051323060a0902030f0f07150e060715060503190f0c0b0307030b180103 69
    0xc14070900d01c0603103641c0006403c1300c42c200a807030701e015951404540b070001022401d13610328a500301e0600d00300d40034000e08640070341780b10059420101d00343c49000050089102d100030b4140d03040d2616640a00c12041c02c11010340c84443c0040d034980720f80a28005142c11203030030021003522002d0074030500d40002139604980006007100c41c0341e80b4001d001c4600d5040905616009240040c070000802000e00940000383c21508001800f58034190b4581440312081e51410190f91400f820301600c51502114540d146800c62204101038103a00d000302c01701c1811400c00c5105004250500c004283c4a80000031030754001c0301100ca402e0310f0b070179040b500c42e034030040d1110f4103900c4900108024408401c40100e400703810700f021807a614001c0007090050b80a014100d880301d4010300300141c00e0110380b144802410301900100b1040d101c0c0f00d0038a40ca00c840308000340902c5044080c140811056070340410103403401091203522400e003000e014000d085030000061180e000300c1900c0354024207032104e560403680c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 760381798 1250 760380548 760380553
    0x1050f0a030c05040b01110a050607300b130f022a061609030f080913061a130f17060f060d060209120f030703270b0a030207061a100305040302 63
    0x41c501070400000784584903171113052203600c85148082c6281888610700c40f6018901401080ca000003000b0090001020410b9000001d007000e4450a6000840c5c0c1a95101c10000000c3c4071030b080300015040d003010050740a0660408541038241d50540c1c0207082044203102560700106492006d08005101d00304508400b076212a00088230303416000e04242090200303060041003d51aa1982e0015245400040e940533100040030000c80c00d003107001303030035861200d102000203c1c10030309000d4010014620507440090003290108a205000007102c0040590075910200701d030f0388207070504041d200d01d0300c071005074056000011140600c40d54080e10400b401004075a04120366550072000b9040800182c0d000109200604441c1400b0080600400104002941c54618034900101464610907a01e40ca48034039440c1110202c00c10f118480c140c03030001d80055140d8105104c21802401061009001d10742000050760a140b01c80b19041c01000702601c600358080c0207500250261a010750300140181d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 760383048 1250 760381798 760381823
    0x50105100f050706180308070e09070e15041503060302030f0d0c060e030d060e060f0409261603050703080f1506030624030106030c090b0d020904110a030501050f0a03 73
    0x144034000400c0040d1240500107102c1c005404110345c40350f46807000f1008518a0000e101c0c00c0d5421181e5140707000d6044480c031504d4981442e005100c4200e00b0003a42c0108456200b50403110810001d540203498403005030305c00359084500041c05407403144000c0e07000c1d000b03000c101100000081500f0b0041e0040b9141d03510034080503a10a80240040c1040d0401400180203244003403102d80102e07402400d0302c45c1d2940450414004100081981000e01807045152410715000030304080f12440403000ca04805200b46800611a0449072013070600c6138403946110559541010b40020260000500039604d000b0380d0f650780c0f50001c083c030300c0c181c5140215030700c442c01e4034481d4600000150340c4000050f054102241821a500030603008038622001288808801800015458494898244003074074218030313545e203032003d50700e0075201e28800900300b15000200030345241c5036500070022500e030000c2401d68482800000074010a0b080c002c082c4070f02078241c800c00f018a0400c0c5500144c035001950003000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 760384298 1250 760383048 760383077
    0xe3112020f0c0121050f0708061804080d0b0a0f030b0a02091309080903030409140a05060616050c12060708011a0406050d090f05030a030606021501090e0a0203030a09080105010510 79
    0x80346904d0400200d9134807280080c4c41c58100c0d4050203009500b100c0a0000c281089000500095001031500f40143e21200000300c11980c0e08210030b0b04190421106a9a800034804000c0940724010320180c05c000002000518180240204400c07a8040c4444002648444009005900c20001c901c0d9103c1e0307202c4018566024103074041d41103648100405468200c407100802e00715000340c1c0c8010a86079580900d4004d000703094281d268858081d0f003080006241001c0050010300450240d0f01120f000c0d06041d01c10410308202c10800700900500d0407044518090200c1e643d000200e40010000302e55a00000348081c3c12403d070440311542460203030910b8240041120035812140348448100d85800c81d65004c0365140c00c620030854001c0c030107199240007141300942650b0326580701000b10f5006a0389150880c40410350681502c0e031030701c0080ba03904402d40c0c0051804201000c0650b040c00300084004c2011703040550403048a02501c000e000907a41e0304100640341c0204d0000c1d03004038071200110b00c403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 760385548 1250 760384298 760384307
    0x170103140106180608011104050a06080901060909121d0a060311040e09010b15090a09021803011d0d021204031e1203090308011e0e3112020f0c01 64
    0x6590184000000782c9990380c11141851601e01440000c11a0780d82500b4840041300f03000d4189095415075089182c00c1c94840461540da41c5445008104400c0c500460b080e10000e4200c00001c11483c1d00230701503d2030314180201400040500708003c5040d0400c94455180c480400d0400c0542c028a50301000349800c5055014000c003542240c2484000c1001240300c0300b81002031801019110300001381076000a0030b1011000c0c132249003003d4403c2c18000b5000660750308042038242d610243c80942c076500100c0d904040380f4011902da580c55400d005651803001c1e10f20352049080290724086070100c3c02d401c030f803c0c2c0c3c59a40403081130f076402c1401c01062010402c20703280b0202c0c00c1d6101c10711111840070340e00e1710168514174410b8000020307191807004003810341c030485181c050058150401c04c40800782048520b5840d1030700c200f05d410020780000030f8550300030345141d28450b1000c000c0b40c0c1103080465890368407c40104002c803424210b46a000c4070552000921500d4412400002e00000402c0e400640c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 760386798 1250 760385548 760385573
    0xa0c090e0a021204050a02090117030f18060a030e120a020319020c030d170c030601300207060504020a080313030b1005060a0e01080a200313061803020c01170103 71
    0x101d4082118440100d403c1d03440a2089010f24080c103120511032041040032041a40503a041650a0312101000031020045400f288072070a03586541d01c0b08411032483c1d89100388200781c1e00050108119a4580e051b0b0401034000003c030701a501d802254007000c2071039000700341c03030500141e000b030001c00307100d00080b16080c0030500315004445400128000082c6096500c500c41c0300060040a00c903007141c1d03802c0504c140c002d181d40d844a821440c010300028186c4079580095200003605142c414040c1c1281078811240c502881c0b41555102c026003020350242c48291800c030b001d0301c01450000341d54440403098880c10000d854600000700c2c65900d40d1402420050070401000134503840000d043d80d902c4004000540f840e4440c2c0130720445510016180c204020902000a41018409001703c0310a417003d10640a801a00c00d440307451b1303000621001103128500512031898a08051210100303a6102960341d8401c0d030032100c00e8a403440044030242c000d0403800b820040500d005100040e0401c0c800c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 760388048 1250 760386798 760386811
    0x2107030324030213060918110d02060f030a0e0304141201050c1b101e0506030d0203030a0c0201020408121903062103020109120305010f0503011416140a050d050a0c090e 74
    0x1c604c42e51160141c01c00c54a90019801007c03015000000030070000c200c20020104003185ca001410a00e0f40100d0154030070301c0800c03540000300100103200c0355a02e50100c029642c60300222900da0341c84203010102c45c03119001d501d10500007004080e400b240140601c510070b04c00d4001543c00c1c40102e01c8802e1088030504012000f40c000e910388444802d056200342c2c0601c0b880741d00c90319040c06000000c4811120701805140c000d4000c0201900c1d070341d400104607500720301d03c650001040d03081020200d0080c01103070488001402856940585200031501800d200b2201090f46000654031b04815004c0320254859060140f0b48804410301100d0b4400702d4607407107400b0340004500821140d03600341c514850710640c01c011940d40c1c00107000700e03851210303250080d001c240c00800031401111110340400ca070050240002907a032200542589124002d981100a10301c8662511860310380700160083c0c000d520030170350f011b2034607000030321085c014040d0341c0c110381807070300c076030306001c0c2042258585401c008011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 760389298 1250 760388048 760388051
    0x141806070f0501050c18120a0b090c090c03040b0105060c100b01120905060708060f0f0409021c0305030f0709060522050d0809030d0e0901172107030324030213 70
    0x148008201e003130091510504040400c90707642c1c45144030380c920040c20109100e0240d00c43d9161007083c00301c0010b02140164101c2c0300d03644942c0e41c10040c0c901e0b003100c000065410121a00a0081e50340c00c0f00003442c010340c480c42051a01d41e80b07a8040c80110b0051250181c032a500449110424501e00d52011044190601d8010950300d2070041c10b00503280100b00032215940010104520564092103440c0c101a040b24200d0020b00d1010004444c07403c150f41041c401d903520000841156110348011280380901820f82c0c6002040e810017500f2904225404d009a02c188000500d04500c2900c9a00544190383c880074101b01c000c01e603540d01c0800c220390200d03140509050104466548014851606100302049540e0701906800e26041c20001c04c03504050100445001005540310b42d006070543c3c0440420000d05502c0072403662820500b500b8602c0f450b203580303074100a100d003100c008082c041c2c02514213000401d00845510100036010a1160052000020a00052800d409070310135031107104a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 760390548 1250 760389298 760389323
    0xc02030d0507020c04271103070e040f11031f020a0309080f0703180f030f1118040302150714070201110304060503012321011b080714180607 62
    0x1400ea04548058800300b0141e8413013807111645252038001c2c4c2d461034140a01c21802c402d102441ca40034125a01c40c001c104076142c1d8204401a141001180c004000f8850781c000709003402d007481110382d00c042000b81c0700c0031018800340100b0b080c0081d10300092000100f012851486441e5404001c1d0807010600f4101070710b0b282c2010100c0c003e44007400810600040c002e07a140d0240c139000e428443e0900c48020300420340c900400501420720750b80000c0740d8100b80700f0124841645070070214030fa005100260f00c09981411484004e0003410b030248030310b100303808032200200c0402c6a203510400484a0500081000e1818028000040c0c044c000c060b00c181840c2d8440d07000c906649040d508130303401c4600040c9021004201c0d1241c04d10300702841c00e03440d03545914090910000310307007290540f41e810b00f4170b1350358018880300c2d10000b58008020558001c0404042c0d024450700203241c88020744610b80095180302026003040c0b00d507012100340703981e05022004041c520300e00780112504000d03800d0300da042d111713407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 760391798 1250 760390548 760390567
    0x19060b090a020c07060c080904050723070c06080402131a030304030b0a061a16020d0203160501120c1b0206040e0106081f030503031315090311010b090c07060c0203 72
    0x14a8036000d09806100540c9814030703a09428540070301c0754005d800300044c614001000c82c03400c0c000c81d03c902c5c0c020361740405e1a5a0314134007a10700c50001c05030b5641a80483c500190240c120384050720b44140301c0c1140c2e0320003603a0746604454042043d0b034041c2d404040c041c40c85d107441c1c400f50b10804440034241d10612560600c1e40000f030440e081130b44144c44132401c140402c0300c2882140300d060080c0802000c04428040c09059001803400b407100400408420f44402c6030030f541c0c0721042e0008a0764001c08444071008166076801c0110700e140b0595001c2031034401a03910000e018015024504881d54a130358110900141b5011004400030f000d90300260704020115004500010b25400703001c21362030303c44090503d00b81800000e0b150040303180344c010210700c043c000150f0200441c0d4225080101c0051982d41d10701f000c403407500c501901421120324100e100d108042d0402480a440d2904500802103550040d090107030340c1d01c0c02c07140141049410441314001034299400900d459010344116401d01303500300c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 760393048 1250 760391798 760391809
    0xb1507031e140f0405040b030d0c08130504110705060a05130809041503051513080d021e1801110109020f01050a090306090807060f06060e010e12010501140307060207050319060b 78
    0x10154083d16000010240880d003028010f91048950a4000785498010030300c0003401c074200050010301280b0002603c6d60540c403000e080c40003501004001b00200302000d0b81e0700e001c035844010222002e01513180000c6180301c0900ca2103208900020a00806034510f581d8014a540882c914907446591003255101d802004c442400c0950700c54001032040c507400070380025034460014812400c43c030101d0110000106040b080c0c94600384982c00160301c800d41e000e445001e51070540204002c1c0e00001c1071100c102040e0b4082c03141d41240070380780c2c01010385094000c0e5081c0c50481901940141c80050780820725441040100581c803c00d15210103030503125078981042e2000000b0a440340b1401098000500442d03100e000a1404849810000d5528014014040000fa01d07003041c10300214200141c60703912881c0c404034071140000001c00c500d61310b91542c1c940d0315841c000464020700c20380c40702058685c00060401c0540d98010001c0011448443e0305a05061510204030399250f150040078032a038881 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 760394298 1250 760393048 760393057
    0x40f020708030915160f110a060c0f021207030528020d030c110a030f09080102130807060804150f1d0609060601020a03080f0c0c0601090b1507031e14 66
    0x5408010b80c0ca040c082d1080d49001e200d0051241001c101c001480032452181108000045884c14a0542c0c0d41180009413648080301e0319a074405e001d41c3c501c4401b08900c550011300e5448543c1c6842510312080b8508036030b1912029480c0034442d400b00200800b203400780d03002e032021403409241c41d4500c01041e0384004114022074502030260f80003841800c00c59400d40200b2510410300d10342504140216038100e0307661560381d800603081c0401c0700155154144146461340c00341c04200300965441103c6c0c10061607404c028452542940100040400e13200e2280200341d0089402144150b10034049201150081405240d807880c001d0b606c22880d1100d1a603120724038040500b103408bc1c107ea141030003e00c0e080500040245045410900310400001d4001120940020f0120820703206039035910f40e00c10441c0718078071802040d03104030f00c00050030200030b801c05241d00700151114074071071031003d09040413409054001804503800b580103440b000c003001d12400d844086440e0a03200064590f145039100d901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 760395548 1250 760394298 760394303
    0x1e0f0d0305010609090e0a0b04030e0d050a05060609100905060d1e2010031104050d0506090706020303010b030408090a051c140303070507021e030304090c0210050103030e0f040f0207 80
    0x2241d2004100035070304001110300520285800740102c4d6141030041d5201e0941d4800101102421004601490300c50740d24801d820b440a050fa02032204641000c940c0c61001d010119120320a5000003103443c2802000d0314003500300d40b010000c00b2402c10815030b0107840020600360b0030416a64010020070743c2c0104051b14180500600105440541001304622111095158249440b5219000c00c0e46500b14905101440d614000905000c8580c000b0355512980d400709521621092078001480404288035000305080f07000c44032841c0c0c0d50306003640c4038003091181d05a00301050000801148101c4010804443c000344400c401544030780014000904500cac0c034210341c04160170300b00208420305004900803a605401036055203841e20300100503220f1508000d0040031744498011503c441160181100c00c401820703607483d0741d2505200707002011107038080c0d0014071920703011403003583c02c52040034140c98166898028a140a800f489108103104154540040e6107243c0c1640440442c40505400d0b031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 760396798 1250 760395548 760395551
    0xc010212070e100905010c030c02040e0d0f03050106020a030813050105091c1d01031512050c01030b041509020318030706021b0706051e04030503030910060b0a021e0f0d03 75
    0x82450009040441030398030ba81c002d640fa40010000640c1000d030303520031141c09107802a203404151800301d4420102c014001d40050425115003800301001c1403000d01b175101650b40c1450066007000031400d40e50288034840140c0c110701c2052000c80d11400d09607610480c07190322600820b0032075840c1c2d42111380859060800b40c1240d0810042d04440c4025404815081c0c50029000110f1a00c00100311100300641c038140341c0e880600380290090942421300825500341c112a480246041c22500c840c440c0500500080c0f80c4001c01c21146000d2161031688800c6482d8041200d0070006428001d50026150f41008000141d410360320400800003804014498140507032600d80d800c0c000420306680780001c450036003090707400384102a440030a0740d804201c0c1000c80cae140c1520003503049509105642000d0002c2c00004104668140001400c40020350800405c00502c0e588406141050264079071120042c0c0180c20310601c118141e68600b07032442c501d00c0965584106040810b40b82c100c411f00d007140840e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 760398048 1250 760396798 760396801
    0x521090f070906060914031c030b1306030506180f0a0c0801060906050112020d0207121d030c0f01030506150a0f020c0d0c03030f0207051302040f0b090306010314030c010212 76
    0x1001d210000090114900500405041c01c1d0050b00303d01a500541c0300d120300c5a00001800e0b501040340d50b460b4241d01d900e5000250041400034060114030102c40c0c091001c01c0022190200709109072021280c0100244c050b50b15004500c0701d1030030003010301c0340c054860710002008401081c001c0081040c803e9454542952500c42c107182511451b0b0300c050740152130030300200076030703600140a40d00c449544900181e45900d80542c0b10024090341c08068004c0000e03070680c0e03a0070f94000c0035400024084441c40700900005004240c0e8683ca0012000d801c8a142d041e10702595020f90811a0080c0004042e40e903500d040e0401154550094248180000c4664010010b11034040c440d84000328000e440700c04402103242c0b1031040c0050944002010490095000682e0601c2401840c0281500802403111045000202000381d0001c0c0203000030000c110100062044200c001c0f07441c1804050050300e6160700e0340d2240300004c8180c21554440e800200400420340c0030030300c001c00510181f003c008105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 760399298 1250 760398048 760398073
    0xc0f0c051309060e0c010909051f06080f1b0733090b0c04050913030c05060c0a030f0b031905070914073f0b1908010f0203270a0605041505070c03120c0905040f050a0c05070b0106052109 81
    0x10824041e140010843e006c100911040e1100f00b17016610250720140081c00034098c2c0f50442c2d4508014102600c140980024003440300c82d504010000307440c0560b0240300d00c00071031010100312007411040700c4c2c2c164041c1c2921602207220031207204a4501490503100095501c2c0d401c00c058964030250301101c00c08120801403c81d81000480d5691410451032401c2014890303841c2094442c010801c4045444061010000101c2031b0011013034008050b110754107003050f41c3d04040e20704481d806814044e500340400c04600080c14802d0340c0c8100700c01c2d0240007458404100c1141d0200407407000003241e004e141703100e43c0031402c0ca0040d1401a440303000000c0318400e01d420381d50101c8001400c0322042001d0314241001281d4000da1941c4011088c0b0f000244080c16038001749e41c070000c5039014541050420320040d0b2000e00a61256100d000416800d02c110381e0111812038842c4112030004202040c494014425680b0a1018003003d90390a1104624410381064210748600c04507a03003401a400b88074810304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 760400548 1250 760399298 760399313
    0x613020909061306020315221b0e0d0311070303050910050a08060f0f0a031406070504060c0f0c051309060e0c010909051f06080f1b073309 61
    0x50108100d8050b1100741405481d4504880c803511000d06059008804031f690602c200008000d02040140102480c3d01921085800d484e0600d40c2c40401782d207001c001d000000001102400f4407016552820707502d4158408104e04d84c508194150100440e80380e00500c0c1c280108903e1010350b01a0b15400d440c0c1c2c1c1d16004000815210a040008128061100c041310715002141c0130b07080039003100c01800803000e030300c04074a4408450400a51104060500009001c00e03203c059a24901c00e80c16581c1596039008280c9162045116150000301d0042041001c5641910350f042100e1251003640b02da42e58031f10010344914a40d2103800340342c942d21502d080402000d4450b10325540600c6001c1c04c02c80c001107001134905c0c0f410b8440c040480361507000156420499100c3c640300c4440c001e0082c5d140c95190362004006210841c2c8100b500d00b100e80110301c003e00101144201010308401440c5001c070395503034a00f000c80020080300c10108000c9801540244d00300703103a258100f007502c40005c1c5030b230081c2010071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 760401798 1250 760400548 760400551
    0x10111203100317070c1202043c09050a02130b04090c1809020a18020c06070315080f0d110c12061e250513030f02090c0307020d030506010e0306130209 66
    0x281103400400451340011060f001110880305000692091101c542c00800d0190561210034120700441c8401501d451f00507007001403039281d56081c40d0030701c2c040b82880901110400d400152480c2d00c41100c0c403005240001032800f0b035440c4101c0102c1d00a040c42c002c10283d5000c1c11007100d941c0450b450500c2000240d1012600c05240c180f002e101850507034000c5213183c0820301801a1070f41c4544035101d0582c1c103e4040342c2c0c4402a41044072400d1400c150020300610104000300e420540c05040042d0340580003d40907040340e020300c080d204a02d0f159206480e45c030b419100512090040c405e43d24150340e80d100c6c1402242451b000600503c0c074041420342c22040c11003050200144202c03060114103400300182e1070b01c40c1c00089500c0e040c800904010780d0745d4000c00009126041200c44040100501c10801d0100c00e8401d40f003906090321240e80c42002c42c0400c680440059100209031801140300750003440d002001810007034201240240840c1c00c00c4c000311350013000c5402074a801c404600380b05d024603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 760403048 1250 760401798 760401833
    0x6010b0a08070206061e0d0b040b0a0c0503070f050313080304051e070f140301110414040c0e060304020405070905121b100f03020f090a12140c101112031003 69
    0x2480c903481d06038001040441d03106c1242c00500c6001008180fa5100c0150690781c030f5401894204c111300d803902c1e02c803a9101c8115140c410f60303814070000304600380c01502030f81d000c2c0140391100400032251a40c1203500e1340009280000441c000885100403543c850002c40c06503002d5400f502e1282841400b041481004420450707076588041003c1184032090502d1105507002150120441415100060302501c1a98801b103414400014005195001c4c161035031440e540079581404101b01e0305109540381d20880040540010082000800502e030035030066901038510300b0621b02c455191000b08071078219805030600c440d4003145080d050303501071304855400b5800c00c885680501c0040c2d50001e000c4010301c0c0c021010300d9008202e092461003000d00f56505003402a05c000030007640e800c050762011031f40f20400d81d9612600e44040400e01e2020075140030f10720380902041ca40c0b0703134522400c54902c050380301ca0140500818001c5212898501c1c0103600900b070700c80c58201b91600b5070404448004050070350 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 760404298 1250 760403048 760403053
    0x3080d0510060e060901051b061f0803070308010b03091c030c08060306100b0f0421020f0a030506070e01020a0c03050604140a12050d0b0901080d0311040b070b130506010b0a080702 79
    0x450080e6403013030f01300c5010080030320700300f40c80b000e81e005005080540a581440c3c03034000d01d402c00c040d90b20620b20241c0d98420002d881d1140982d14203045803603200324080540040d2011005000c1806460000c640010401c000c0743d44d41041e00118400c0c0e003128010490000e5202d81c1410800380d88090000d4010108034050704003030400c00383e901c0440c441c5219414190201080b030f01c440e482c4550585000307006451000200701d000c130f2094948001ca50108070310a101010f845816810b00b02c00a2059952140c014007440c0c0791240280d46841c0c043c915079046200305da010360300185150548100030352048008040509251406109050400300403c1e00c40c0e00510000c008684000380e010700074421800c146949061960070341018000305041c4c079821411000000607144400503041d500d80010baa0104241c6030241e10819031881240b0504554103018030803071001c2091401d01a80000b00c0c04101031050032980e85050400300260f0042c1d500380310120f01c1402407030f00310103400c1d808081c84c0301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 760405548 1250 760404298 760404317
    0x61119050309061303021e0d030606030903020705040b0301021e07060516020304030318090504050d0e120c04020a050c0609010c02010b1008041b0807090506030708010c080f06040603080d051006 85
    0x5086030383d0311005100c00e0354021201c801d0f00501d4000d00980103214840c407400810801025140ea541e60015030440002030714000000030814400d204590708103516034040c200d41841c0c04200700c090300841440c1da905540c02c1012070329100310003203080240c103000c0260b16104c18040c00c1400c00c6810040840400c1d00395030740c070400c40c1c03613011040300d040d039a1505001204903144040550700852540180164500d000280400d1040005944081400311f0b41c5500c2c00c0c00b100800d000d0450744110220495610610b032891482c54540c000d00040c2101d46416800c20780d8100c00c2500e4000d080e43d1503070241c1d640740b111031f88141c0d081c0580320003458140c4401181c2281e207100145200c1c4001d202411102e04041149034032030b1805100c400901040048817180b03629070400703074020203081c1d42c094401c0c440c1c4080080d040006000c0c4000120740c0384c89402140e5503150090728203030401000d40383d002d99611004800074902c2400703008005484039000519280c154044101e1500c0e0790000c1060010024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 760406798 1250 760405548 760405561
    0xc0a030b010e070203070f03030203060907090605041a09061c1a09010e0901111b1507020309010f0e040903030b040e0708031c090b0408090a0b0c070b160611190503 72
    0x21641142c0780301050b440e16070f80c0c140d000c81c00d40c0a8180300074a04096080d469082c0365241d006180119001c03100030a4546800d04103840064451107000007150051004220100c0710800d00841d646103d44928030740209400007945560050301c0c1c0c4030074002080c945103881410b078824100c10415016403001c00c8507030800080d003030480501c142c40d22200f122000807025007007904103400c03481c40f0210f031030340f59048039928460304413002400d418144140304000030903c1c0f162500d40d01038001b5401031890940e000300116542940d40000c03406215000558040c2500e0b83d01c07451442d64029903000070346510030401c00c020750704004420f01c1e090344003450600c81e000011040328944141d07108040c0901c44254008005001010005810b512209013000140102c6000130201003a080785d40c196051344625500c03800740182c140c0000c03d5070280b1024001c24004c81c0041044000d05080300000c0c40311030340c4071010f4030804046003c031034a0200700030800c6607460180004c1c484103418030780d0644c03030101e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 760408048 1250 760406798 760406813
    0x80403120c02031612020c04110a030e1f140603160513090c030b01051801120209130503190e0d05060402040b0a171f0902030303060904230106080c0a03 67
    0x32104903010a55a4841c115600d0081049030048810250045080095800c140d4141075498100402602801c2c00c0380d002032801d4030404070503404800d0340701d05000008104600802035440285c00078402e508000e42c81d009800481c00d03210029000204000e072205201e1002c035200900b95901984c4001b10341c4844460780c60303024064450aa03241d095810031320840702e000d056034000103002444900d05c00b01c20700112414080c182c420079122110344070400d8100459400c400d1080d001e102807507801c0c000052802558250300071025507070150040c0300b141c64480c1164440078440b0744021450902c2011907801002182c2c1003e001c07101181180c500392a07494591100400003442241d4558600c50299900800034002d0803c42d00c21403080383c010300b030017079452141c000e1200c0291444d2a81e2210001d99004908a0982c00740c0a18116201d00301885460300e000b40040350140410710031107101603040c8000c400c00c2145d2078008166285070402180c10720009125842c001c8042c01000c1c800325040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 760409298 1250 760408048 760408067
    0x90503070b091c0f0f02190c0815090318150309010911120c0f0406170304090b04020f0a0f0e040c171803030415060302302d0f0d0206040b07080403 65
    0x2a42840b90f40171261080490408001068500031b030719161180c1410f001e41010345100f540d4100007101c09984810300300d103080304011511441140d004011a03ca550001150341185c200050000b80048400a00c80710700d6030411240103980e603640300c684000f0300102010203403050805603488058600192100d80d1243c455010150213041202c40b14040c5889a80c0400014000403014103940140c403c0e82c103850350b1007446082000350030071040c49140d20f824030031940f01c42d410951881c64080358079001d85802c0046071030315085c01605901090701c0e03100c6000d8038480e1903183da01d80010402c1c8503010215843d0161590803032000300c6a102215440010449412035000095002200e550981503009044980c01c0250405c65018031803555801c40d071610100900e80c60107820181006960b03a5075902401454015030122104100c00e0030401c801ca1308103004003200a07541d000c003503d002c00c2c1c81c141d5080388100042c1d004208000a101040213403503004155403824081d02d003015200200302058 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 760410548 1250 760409298 760409327
    0x21806130e101a3102040b071203140a05090f06150111071809020f01030b0a0b1303080f130e09030901081008011d060705090603040b0703090503070b091c 68
    0xb0b4400d41c0785884503c04200341c205400c01040307041403490a0820059190002c00030581d600030019070303e8150810360007503e0076202d41c0b04503641480c81036154400074a0030b160080c820300d83e4510f440c036a01045140c10500c1a40c80190214407424644e48071840d0038070605034000d6540050041c01007903a0070009510100c0340906c5d0031000001c0c001c141030304102d06588020702d208840b800703c922100c29030f000800d5080c000c84180854007094801075042e200c1c035102c030f20b1f4003080c903500900c90080c0e00300292844540d000000817040351241e03107040162740007899145c41c030300c4041000752105001d01e903100003074074041003c60002d040080900e9600c0c0140c1c102d140c18011030390005100021042d0103480286000d00080c825015110390350b0541d0a5aa589603146009950001d03000702c0c06101203a02d00d0b040644285e1565443d07442d50038080101401403400c150321071500360049032080024010303c0e0302039031a41c0ca5504101da042d6142c0504000084040c00315103a2400c0f0700c40d00640761200c21007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 760411798 1250 760410548 760410551
    0x207050102160f121e0819110301090506040603020303040303030f0b1e040c0503150d060b190f0f060f030209150f0403030809070305070303050a0507021806130e10 72
    0x54540a800380c002c100980000c00d50419041090048228100190900540e600b403000c40e04440c0072203401e001080c288041040c40600e00f001d0034032402c010f03644100000ba0b42406001ca03002d03400e00f610014a000740b003d02d8044010b10203503803244501c0340c005804503000c0100514580c0440c1d1a03016034440501416a10300400351541c030180c00103501c88400500d001c42c28160f0a030103030140c030700c4030f118a80580c3c5480883d1055900407000c0328080c0c40c00341409511030317540c8010441542d0400004444150f2500c80c04e828030740b900705690040c0f1420b1401100300030b003040042090940e01d58440303601c0701c882020800070305400410720b1400e1196442e0159a843c0c0c2000454800c0c0360000054204410005041d19504400d10103001940d21a6450b40b40c5a00d5184d074042e5603082602000d04140c12408013040041d02660051520510030300b04141003480a400040e01d0161003c025190001c680301008940d140080d55203111504010003000072a40028020382e44010041607401810f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 760413048 1250 760411798 760411807
    0x102040302011403181207060b030705030715021203070c032c01050d0e070803091008010b03011e0b0c0d140703090e070c06230906010b190c020418030e06040803070602 74
    0x1100c0e01c1d03940e0030109684800c0790031b00d0003400c603a5410f0f40d01050050b9003051402e103803003c851a010540c0c10481d98018000c001c22404d088000c2c000844001c1480250320036803007005045100e5401442c4246c031285ca0f03000c0004c0da54240a415100f80c07007240400391780c202110101d0001e00080b070f584448400e10703002d52180380c4c0351903c900a048010180c003c510440c180000d00042c004004d24200900361100034102041340001c4d180d01c2ea0030300138014400418801400310000020250311400c1c000c4120301407440e03403200070140d1540708407462034454210080000229030891081d40c001d0010528251800782d258800030708403506070150018a94403400441c200510540380d1190094002c1c208104801e00c207803c00401450801602e01c1c180c0d03450300003a184207004103500c6d048032034800480f46065485456040c603282540810f0003030020040200d009030303c56202c0d03c1e03c520014000240c40711042c2c10003030103042444642ca40f2504007088280b100a0700801039804a641c08400503031075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 760414298 1250 760413048 760413061
    0x90516030b04380a15080c0c150106110d0503060607020307030b010303021c051602190815090c010c0510020c120705030d0f05070c060b0301020403020d0b07110105040f020108090708011a090105030102040302011403 94
    0x640706d04940d040721481040040c103840096409d05904036851072311f03901800318000542e10740301e040602041303003c500240001a0700c1c1c2803e80042c0183c0d031004090b126469281c0d9124030700014280c000f51f0060b07100070740c1c0311032845a512440d12644210304209040a46c0ba440c4910500c0709100000e0203100b440300d041c8142c11030010980050800b54065460040844030044a02001202c84035402d100711184480b003540180d000842c45600311000c0c1180d520b40400e00e0020b0344c0081c250382d203103200c0c1c2048407070806158405021450b00c00c0014540d01e003c071040c40b1041e00c515440ca0300f8850316000c00d001c07603079810080b15512103502c81008169800ea000000c6d0085c081c035070020307400c44121040041000540c0800a01c80c515680310411001d504806041c2294001c0350018007802e010300c00039015602035864a64000d00e6401240d0486031103880c40c5081d940c40f1100792030410403c0b804401c1524041c440d0310701610307003030b00214109490360700001d100740d0540d80303100700514001020844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 760415548 1250 760414298 760414321
    0x61014010c050a06050106180b0906070f05030702031005070806150306040906270c080d0c02062802011a01021603120c080a020a0c090516030b04380a1508 68
    0x5401e40104d020011903944000c007400034108010b5802046642c840301152100700741040e645d5141024000500348800d0b17540702c26820f225040b046c0c0d041d2000340141001681d0402a09000010056003c42e85003401e0101610350300b40580700703600c1034440c90040b0010400c00016240c0c005c06c200c0700824071001c0c0d4146a00200104c4820b2040c2d200156130700c1044401d01c0c46070020503442107032109452070b0b9840e401c0b80c8641c4002444000500c4c00108940035140940c0a4040c0280383c0745500c0b010410425491300c1114501e17200405130b516080d0700d10040c2c840e010810b4411a0a00103084100310240040110b120103000051400d450040d0040301680700740403900707803184c2c0000c040c1d603100d142d50406513540000503800c540c43e0802c2c00021030b4200850003050f0003400b482d840d69281d85296281980500280406a03400c1543c50444505021150081d14072840b000700307444d401d203034028075058a015034a02a040c0981d840c200d0410407092004880701c0f403240c5c81d150408098030f0fa8a48560b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 760416798 1250 760415548 760415563
    0x1d04031223091c0804240f0b0a06030204030b060607030306051815060405100e0105091e04050a050610030e030909011d0a06050a05040b060f0a050705061014010c05 72
    0x503120900c0c1e00880280d020004809000d482c8501c00c50351003502410710301450b40c3c0060729030000100750002140c0001c4000040c0300d24850b04c0c00d5050031203146030b0006821501803610303400c00b068603141a205a810103061207001303080c0600d41549041d041d600e841c941480b001e0101806030b03500060030414903100741e024101801d0010885040c20502c0780c40c46c030281da0165081c0c007280c196210b071044030745402c0c4110f60445101500c0651010142ca034255080b090442d0300ba0305100f000c0002c0507103941ea6440713220f1852041540a008508550280070071560001c0039a0360140c41d25040c040c0c01d580d01c030080034800601c0c0c5804a041180b04554a0560146600858000c2c6104e00080341c44484055030125007031388540c00121079528035241303e05031801803044a8000c41d0028041c080c03420190014102004043d201600d46042100308662a80c0400280c0c000517001203025410800240803107a00710303c0120305080e802c0d04000c5410071002d525101681480102131003070080040c140f1145 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 760418048 1250 760416798 760416821
    0x51306080a23190f050c090901020409050a0507050306131b0c0302010b0d020a09200d02090901141c02030c03010c2111042c070f0305011d040312 64
    0x2110451941e1500340503035010b024025058844500300702d80075000005052181800c060314680d031070725054440045400448000342c541d805819a00100c6458182c803e5004501c604001640d0b5441e09003010200c420107440040fa0300c1c184414820100d5100003600e40040c011510341c8542000c2030006c100400f480e10009281e64010b40380b08034042d070440c2c1040a00d0f4000e800078001c00400d4810840c02040d0303c0c0009500a900d42c00510100083c0c1c0d000c1800c040ea4000131003d81c40401c040290141c12141c1403407406500092181010b0070b0100c1128010888104c0e0104240e50324030000310b4011101c2c2410728000780030340113081559010410344120100c0038008122a4403250300090260303c86d030071908051100742d166a41c0c5c044081c800c810084944d6003516080504142014010340a01c0d8070892261080d41c1140102c3c1c00d00c00002402641e0640702c0501c880c420314406400e0340c4050f40300b1000e81c03407620001000c100d0039901c038981c410f6062416041c507010a940a03001000b1a2a11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 760419298 1250 760418048 760418053
    0x103060e03210609090f151b0409020406020f1c030b060f0d0501030c0b120402100509150306150702180a1e09020f0a061407050a060c020105070e03070f05130608 71
    0x2400c200c0e05102401c0c81c040c050640d00d030144c1e03a4891543c02c5d621a1200100c80c510352068a0805c0200c14603000c03ea00000c0500c030048240380480b0440d0241e820a402c0050242d41c00142003102d0341d010010304205000c2070004c1c1c1a144911003400e000d8035906849501419244c0e10809800c0d600da204440887c0c4c0b100d02666122042254040b0040c1002d01080f1075203000b004010980020000079207807074510070320720030600d5074899081c03003541900003190341700303001042c010340c005641c900600c02c00c40307000307a81c2040d26841e000041010600a0200781c904040081140002580320350320700045036103a9607104241a140c4150600080c12042040c00480c0402d00b022142101d094002903d40790007151a2030200d0048010000040f01622554006c210f450b6004003c01c2d01040180c40e0580c0210280c642c0f060f155183c51041e2072990440e500140d40d100c0170442c41640105090040c2a000d90050000509110b40c00e9151004c0b40203035072051108065444030100c003500080c000c0e00c41d1506 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 760420548 1250 760419298 760419337
    0x80c1011031308120a02132102060d0b06070b1f032a03151a040b0604050d0f0204050114011b050d0302090a0f0329060a0501030b040b040e030301150908060103060e03 73
    0x880002e41024070340b072107403944030f0f00d001410303a4401188c0c0c0740c3ca42c1000c80c0300c020341a45038200310310380d0f05c0382c2d82254540d030b190720345001203a980f6009880c859001d8100c02d0340901d80076805006503c1044115003076402003140500100c0d06615502000c0c10b058600100f088042007803d0581c0c070020b034001040d8a007440e8820b071124425800403503d41d02172050052840c5a058200015110118802a00708106000401041c9840340c80c011401c0c2c0100c981e10141242034000c00d058a0090304080d00301d010b02010f0f240b00e0f591000d07801e40b403004001c400b40081c507030311f80c1c40c19141c49141000034201600864034034160390b42c81440c4001040b41250300442c00d603503443c011070b011803002548018803416080e001d4020205040251103240e004180207441d5040000640081c94060304894000c1e986070300461003a00d071031040c010440c040d1030003151690702d0321a140c0c0e281c00f5144030351030801107520020404030070300062941c10b40c0d0340101b0104d400300c00412000d00d180680226088201e030300300c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 760421798 1250 760420548 760420561
    0x30601020c030a051f060506070f081b03120603031204110316090b0f19051c080324060c07170f1b0f0a150c1103030403080c101103130812 61
    0x1504440541c10034008900d0f17800d00101501168018811503130448020410900014465856607400c98401d01020703040580200840f150481c0031085080a503000080c5000c80400c01c15445a211804030002c40c0341681103d80c01041200181004107024101c4200c14010399040c000c2081200501c101e5045003035031fa54001000e00b250502d01030003244400027054243c1000b241491012414525a0340414544400d01104000701003031501580645444030001502d604000c50080c81a0a10031032218440b580d4000003000140d0010b1041e0401c2000c01540c1001041c3d00781103c145ea140008569440f480e41340c202041544c80b488540118041c0c1caa20b41141900702140c21707800c0d90390b01078440301c440078021400054003440e03c0d004990300444030943c0c03003804000d1803070b48100140700c00c50303614601191668010f5041100c201c0008120a04d0400c010021484001c1e600401440701240140d6555118403001d02010035807601c20400702c05002e08001140d5241140003000c440b6881c048 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 760423048 1250 760421798 760421803
    0x607060c030f1814070e190f020f0d14090a141507090f060527040b120a1406060612100e162c0103020705070b0403030e18011a030601020c030a05 64
    0xd1000300e804002130402095401c07070004080090300c550001d01440b64540c00000841003183c809004d0107640c9030a02c803811070819001a0202e01b015200d819110a0080c0d550b106503038004060903041c84040041000c0464000b0305103a031240c10019079400d201c01f00c01c40f581042101e02c0324070b04015000090103c03080e849002c20301260080c0c80058640742e210780e0104c80c68031442d980098020220050b0140000d200d0500410101009000017414110500490207036104d0303181c80c0d4000c0e00050700e0304060048103000b804401c0d14a902402c0c86180c46000031b4283d0084580c54841d40c6407050000303001c00040b04d4080042c2803101954807542c682917549008a0003411f10040002c5e2000049003001c4111010340008030401901c07048040d80300e200118001d40201405480c1403140240000d10780c144c28000f0030103103029540702c0704281450410b0004298000d000d130030711078002c1f000420121401c00400a08410707140b40030f568980311113004030300c3e11100980700b0740e050007450080170410100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 760424298 1250 760423048 760423091
    0x309090e0304080d0c020a060305060d0506040b07031a09010e040309030501021810030903090b0d111b0111070b06010318050f1006080106080c040f020408070f0f0509060607060c030f 80
    0x20742d01203e020320362a0b40c4c1181e104030440c10080d0031800c44042401100e000780c110b0741c2d02030000742012890721303c103440b050b20305903090b00c003914400022020300c0b8503070790b040c0650b5020002c003550b441d40410f05038020448030b07407052080081040600c40031404041c400c412000045410030000d40d1a01010051061700c0140032840c45d12918161114020890103070041340391050301521a1522a40f8008a102056002101010010b540c070040c0d040801004d501900c05089240071112000c0c041113681130856500c5114034410400902803d0001681c083c0040d5103e038080c070b0041944002505041e400440e1624010070f076010f184107001201e400003482400e1510480c2d02031080541e18000c46088400500502125811187e0743c1720aa0415803c051400074411400601d041d50b43d9140385d0070019035401c50b00048035205005c00c022000b0480490181100b1110783c4020708004000603124810101c00504441d00d80c220200618003d520582c02c0c165050001d00060095050341198100c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 760425548 1250 760424298 760424309
    0x631030c08011428020903161d010e1303020c0a15080c0f0a08041a090604140705220b0a0b0426120322121d0112090309090e0304 57
    0x20b00f840101c540300449250500441140014940d40b10301003100c00741c03034420903004e814255020030895000c1d890800001800066060600002c00e040001d4404072401c0c4650001c0d14007a000e0040c4034030118001c3d9075400c001070885040c041800d40c0740aa04207461080165809402c44c9030015040703101910702d00b1003646c1551b840c1c4c496600d10038900c4840c001c501540355181d809007c1401c049001e0494560040e00801a0160000740c081d45001404d808030f48040031508601306000401c45410111401411194050120141010040348000c04d01c2054603005508603840c5142002c00c039808104c400300c001e0304050303800d0340f11110758a9a900c58444c00e1004400380c0e07200d6010200f06180d100b20003004001820402c02c4040703000009800280881a404682440750100344800300300d440304180c4100c0c41b80c8182c1d68042d2000c0c0030011440021604e0b442c9600704402141e0f0301c8442c1c10410014a04002582c0c059410100d03041c4040313400c8420b08600d0801c0002032984008054405c80d031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 760426798 1250 760425548 760425551
    0x204030c06080702010e060105010c030302040308161502181c05010515030f03091c1505090a1101020619021809040c0f0b0a0801090b01270501080c04050631030c0801 73
    0x2203c1410490807104c0840100304540c001d000103000c1907100d00c0c6082d8081d40030740380141c28252262161440ba5111460290740041034428040c00c1103080054101c10546580c4118104940c0310035804041c211095030511a040f0a030340e5031016a04949000ca4054011008000f545040500c21051003482d080c89446441609224191250300004032681040e01800c1280f9102c2d01101100d03190b40210021551101d60300c004c5103a0700c08a104240c0324039030100c01041c0d40304550405006e000a1910901d0454004004018001210320b0061100c444a81d500503541c060038100003442d4103401e54003a0b4081002000d11051065200144080e00d00d50642d0f0134000c0d036071302124481d83c407803c5480004168000d004108448103940b000c800e0780010b040803070001e81e10110707003010017203900341c0260784d121404002c0c80f0310750f4040507699028001004213440c0a050000003541c60054135894251841442c00d0204407624802c50050341c2c80c10f03039030812030058503031502c01d500302d0f8680036003800c0350b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 760428048 1250 760426798 760426801
    0xf050a0c0f0605041802040b161502090d030e030c0a0b190e09040f15020703051206030712080706061a0403060c0503012d0506040b0405090a05160c0309090204030c0608 74
    0x441501c00ca22048854903101d0b030313280510741001d01040207030000c2d0f8849066802d01c400543e04421200a04005002e101500013070384040c40c20341c1c141c070070400f01c4d6103c0742c2c4140500301e0b180d111081c164602941504201c8001c2c43d030300c40000d1910441122454001c817001c200040c0001c071031800742c0054014900d41480305540c041040310103420280d5441d500040d1640403c011410000412500700d00940c61640d100603121034820a036401450201c00040b000600b03910b00501e07003a04a41c10240440c0580000c07450300700c14000c00402604050b100550000d180d6041000603408503000f4000311120400343c042034620321510781c005100603a541030600c2c800c0c2c5034441c8114202d07811380e4040880000f100b1482e604410b0204075078056840750112022000c601070352040e0280004003a1980c020741d860b41020144059940042c3c8031070300c1c4600341014000e82d01032403107840d6010862403a000961701d41c141001c031180d2059070b0007502c070f0ba071001502009200414199400b0390700c00b40c0741d1b118103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 760429298 1250 760428048 760428059
    0x21f0302120a0c0c020d0c0e010e06180f270601030302011413020108040807111f12050c0306060a1704030206011a1614031c05060118080304051c0f050a0c 68
    0x243c0d04421058000070b01840e280d10014a00060391900ca00d010302c085501c06915000c1568000c0400c8c0c1104a004e0b2049081090f82d28051005107481e034021001c2d05a00d0030103d1103c40340070000340c11140343c6841c0010f5040301021041003002c007a041002180d800e96940e0a002c3c0c001c18800d48000112200e6200240c1c0e902a0f6a4500007010380c10782d5241c1c8103a59545810100b600880401c48800040e504c451200b503a45039810b4a0740d01c00ba080300c0a0840d10501d01a002017010805074446604020401c9103c1c0f0186068952010050702c030199500690941142c250880c000140342482615003407006055000a625059403c54403c0d00709040503051b10385503d0246d0400f03030030607034200300f0050000317504080321403140508281120700b0040d0f180380c0007444128800d105c07149581c5e2601049980d60744000039041034010007107103041d420700b80980a80c50348114040c841c0503440c2200c0350003080d8603424040c030b5210780080e0610040401e501e09262034582c01e05054541c05601880440c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 760430548 1250 760429298 760429301
    0x12010b03040c2102040c03020c0a0c090f1103010302061b1203040b010b030603100b0a05030a14010605060309191716030206070809071a07211209031407021f0302120a 73
    0x110483c0c0c02c0282c0100700700382d600f000050321164402d4020180c0034407000c200550208038101182d44201c4246102c141060bc1d203008a42c0d65103c02d038883c6050088043c000d503a6072049905581d01920803a80c0c5650880da40b1400a9501000300000d20801c00c100c900c90b180718001e5800b641c41101e01003010b0360303034500102c1d03640820f1b549160b05420084031407102e1265039001541004c5e010701861062a91200000d041010180e4140d82d0040c1100070407940110078821400a07020440d0301905609146502607600c441205104403c2828052980705008201c050149807450321600c241da1000c40602c40c00490949100840141c443c000c00b10740d04600034881c80d0f100e01007100041c5901e518121007414840d0000200180c074800821104000c90f040c44000a8020980d03880318010201d92600141101810303448184168038000404001a0740050b0030201e500d007000500d51180091700009141ca0f030514a00c2030b0000d5240703401852160550081c0456a900c00c1d40c0c0000b69039169440350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 760431654 1106 760430548 760430579
    0x90a06090204150905090f07140f0703030906050f040206250f030314092d010b040c020c1003060b0702040c1403091e032107030212010b03040c 63
    0x595551300100c0510040000380c1d00b40c03800d442d12028031003d82401419403c01c00801019121103038403000140c924941207c104250344001900d4050001c0610840855078141800005240c0741940b018052086030054403407490140d400f003191418035000d80b1025205020103c0190201d02805101c00d007042c803035100050b819080151210013407000412030385540e80075484a0100410158a6034004034080003414900016242d03114090011003541c19041840d00d00d119043c140d00051070190004e059400c2c514034502e80c0030072070a48031903010311402003404105a03001810940d0102c0c0801030140740c00345002014444510aa51040d1089001544000c9510f520791115081d01042c5686160045242c8414206403004079420741c580b1f0f0110064540006900074000d40440d400b06860070718400c0550b8507142a100c258106640c10385030805900c0d00425030051482152 = true := by decide +kernel

theorem cover : BRFrame.Cov 760251798 760431654 := by
  have h0 := BRFrame.cov_init 760251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 760251798 ≤ n) (h2 : n < 760431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
