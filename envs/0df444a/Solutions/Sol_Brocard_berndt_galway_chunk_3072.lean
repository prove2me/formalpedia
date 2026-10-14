-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:45.500983+00:00
-- url     : https://prove2.me/submissions/addd658f-2c14-4c45-9554-fd1ac9a378db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 552338129 ≤ n < 552517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 552339379 1250 552338129 552338167
    0x10518060324060312040f050f1f0c150e060a180f080a020628090c030f1a090d05070609290103060f1a040b06042102030f01020f 57
    0x2000d402c0710440c0800b920140c003060301c500512a581400c6a003482014a81400304101200300403032002d0819052519140f00781520344120761150540907004101038840712a40550303440c482c40c6d11540030f1141c10f00502484902c000440b818040492100c0b1b00500034401c5816000e038074030007402c0342d507500c0034808018440c5004852400945410304000183d00c075000f41942d40c4034564454030340c00c0940e400380c540280900780b0341100c3c440c0c03003491741440600c22000c131910440c0c010101d800441b60030f25150842540d0005044442d548000e4018480d0140d00000c3c1d80c40d0f01c24801d001d640c1c42c03100c0350340c5030320790300d507020000074410030403071000ca0000d410100f503140c050707001c0d0003010b2850321500f8600070721031000c21b8610540c60010401c1c00075030322071705071014000d20301801000d140044441c2901464001c807440b655541c0302002041d203034101a10041c00602c03044425200c8024809484003001000491192181c91440a01e810041c000d403074055401740d6a040c02d00b080d010018550500d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 552340629 1250 552339379 552339391
    0x50703020c0f03090f010206130807031211070201200a110a15180602070303050406080a1409070302030c030a03080414030d020d020409050708040510150b0d0501060f08010518 77
    0xa024007000620300d20902c1203142d103003200c0005540da0000002840100d0301d09400560554206004000c0c0c0c0310988800c0d151000d034001c1019540d82001d01d415150300c17461849008540f450003503d00394a0101c01d0041042034000d0b254552a0b000110320990a69094070b40f040e00b0380c201010b0800003070780c03034198240c094030010003c0c20110345820400f05440c40240c1c0c0000003035941100079811000304030300b08010309201e00c0546081403d6480150031031040340304800402607008001041c116031940032901e004070800c4210039a042c10481e603665815180001d92180c0140d807445006441c0000d02c5600b0f80d549610f51249130350321500d48401c41c0c008002000303448e020030071510304910032620080010032039811005071942d081000741e10484000400640522140344140408078900140c3c440c0540f00b13140e40821407510101a68003c418290b1215504d108041034204140c0303c2c6811090580340d075603507408100c540d0780310b0440c0c4d10802840313901c1e08030060104480c5800c601115503584a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 552341879 1250 552340629 552340631
    0xb180109080111130b0721031503080912061605070203030f0403061401090b01021506030a0f060c0f050403080703030c030b1e04050c07231509010b2b0204050703 71
    0x3641d036444403420b42d58501da02500d4000001440c0264209003090080a080c080070141d080420956480024004c80b6107c0301060403418050359115202e030300410525400c504070103400f50340c0c074034000b2031680102c040f1a11450100c1068080c2c450001011440b0b41201c18044019500280003074481b9030012006030380600081010100d5070812000810043d48078100004440c1201e4200e031020713000680201205a08100c003140e65681e001503010001484011a58030a850303400000341b8141e01e4581c02000c10400d121414288040d950085640320071030f40fa0601450000d0b40100c480344540c2c04024045c0009102c4800800d10a5201702809141d5080015143c05688000303075201050744680820740017495102c4029080501440e034020061030089401c0072025034540c60b2614881c10f04941383d5032103039400ea400e088104440c5958032201d5060f03200b1030800103c00c601800c0741d036103114081d10364a40240081d110300075000350040c0034000b006202085c0d60b802c1002a11016144500709 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 552343129 1250 552341879 552341897
    0x1e05090a1e0e070504050321031513140612010905060406050705120103140705060a090909080d0207030503040b060603010b03281a0a05040209090c0d1506030617070b1801 75
    0x99011407142500035003d54888540b154541400c05240244402942c2601c400199608290000e0070f81525000900b0043c8001041c1c420800301c0c3c40c0c4481070903100c0c0000d040120000c030f03a105011500d0300880c0705031200070b003111207030041307038242c5044020042665000400080220b8800d62019800032818a4a00c0c500302c080005c200210cc020b81055502100d10301000b980c0710400c224120081038141c070310340c0c1403641a90000d000c00c0d41d07608c03490080b5600c400c501800c21550504a590207081b0080443d180c0a4034140280701d030300105c60440b0004074035400b240c030714508003007031b02d040781d0380290321500d03642d80d0f00104030742505a4888400241c00c0000b0300c2801c0012800740e4900c48003943c6140c3e4441440c4420006440c01a60083e405030384100121201515001d20390380c1e01c54100281247d864000c0c400c02c40003894030403c6569090072014010034802d90641000044030025440070300705050500c0160f4172141a8170030703501001010041081180d0b0084101c00b19010305044c40302c80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 552344379 1250 552343129 552343139
    0x9030b0f040339081c05010b040b0f0412030503040b0f160e030a051c0f031a0906060d060e0a05070f0801091d060114012003030403030504211e05090a1e 67
    0x65681c1c0f0181104c429201044a5141c5280400d22040203610f0390428480d80d45400d44420f81c91003207002c1e64060580001c1c9280040034a4001c84005210b058102081c0e4003450800425a80040c3c40c101c03580d189000100da0440d80b410580c50041c0d44078103019036841c0c1d941e9000e440e00303049918225014042c4013006804914140101d117140209080700044820302c50900401c3c502124407104c0506141003000b444116000400c140c4180c4260f654405a0b01c0303c000246141c007440c104207003c5405c0034008120225002c0719140141c0c81c807501031240b5111003500340c41c04a00c07480d40c0070020700641d004100d00034461300100000c850004410754a0014080d10030f08108090b00529a0759450000e500340a50f0f004212001e00c0090f0381928200d1101c14203ca516407001502c094209502c0340c000c1b4062040240101c400313080c18008815402c1c080c60006403883c06503400c800281c400450000c16000d000c0e01c01c41e082094006c1c800c2400904199101c2d041c0301c0c0303403401c00d00205100600421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 552345629 1250 552344379 552344477
    0x60609041e050703150605031311090403021c08040f02220e1c1701060f020118060c030c18061d0604030321060b04140102150709030b0f0403 62
    0x207000c05006001041d14030b45440b001e0269448018040c60300c11080748100501e903404020380f50080100d00102c2200d1100313007080c1c7c0c40750b14102d175601e80c0300c00c8080c1840704150700041c51804002ca80710008442803181d0078241c0e13103602d049030041c01d0010b400c00d103030f0010324044030210950794003072001b40080d10300c82000c00e00f10303401c000c0f100050b5072000c3c900701c2d900d29120001100810840c0780c1041c01d000f03056416610180103200341c9040c410f202c2c602d22241ea000707403c0a49002510040c4038210b240a0400c030000c3c1070181522004207140c170710785c0b0121511601c5100358000b203c007944000d4500d0900102c4000e01c084540c04049503803180c520241c1e680300340040c401540291b54034000c402402c40401c541c2595a611a4281440c02c00c0c208050721601c42a1003c03a440c81d02c1440000040b400141d0a04099000403194512258200a40c45d41c0021490040d6401815441c080b175035007580c1ca00c0020b2081e200900410b41619140f00c00014003c81080006802d00868440411540d0b40203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 552346879 1250 552345629 552345671
    0x1e061f0309052406040507020a020909010930020a051207030e0a03050c0310020306010c120e120d030c030207050712030504080a1113051e06010903050f0607030e0304030b06060904 79
    0x540c99440203c40e0740403400801e100c00b900310804071030800081c01e026901940e200d045600090051b40e100001803400c04080d400700e5043c41d00724113010b042600160881424503400d00b4541c05030000320f5204400184005018181c043d4005c0c01032140d0f003401500c0108a03085a5000c070100840c4105001060300c0745050301e0000c6204900030a01c0703240010806040115004000d0505e510503c10483d4503a44035a821740502d4021300390405151070400100e4209289d1103225401185450000380c088800281e0641d006c1c0700c6070b03010030017109440301c1182603100315070005c0c2880e880243c00780801c00100c1c1407520300720b20a00307103940340550b40d446650070500c20400c1030f51201900c00d0754190a040280841c4060b80d41c20500300583d2400e81004a0310a01d420005c680b000c460000258140e4086e055101c081d580241c11a81c0c000c03120742c4203540d509400c0700d260000909108a810307a0741000025181500d9100c0d41040940da128018400560407000e01154405e403038451545106960b07a07104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 552348129 1250 552346879 552346903
    0xa05010603050f060712050a09021e030c0a0308071b031b06020105010b07050d0c0311100b030f01020a020303070503090a02060a051215010909021605060f1e061f030905 74
    0x20030385a145080490a25458440c0243c06070001c404001d8400e80c1b02c0c4020648151101002540380c60751102240204041e140013500b1410004022601101c110b0110310407913012800c5880712886d0406100f0803e20a1000400c641000e00500d00051410142d8241d034000c01c41071103a005035240c07075441c0c8000f0115200d280030380c03c3c0402803090030741c28042c05014002c0008118688034040c0d0b03446a4580300701c5880c8040191551200003050311482001402006500c02c6801010201050400802c14044154400d10503400c607590841c03030600071740d0210380c1e05402070b500750361300c4400a945551009019a1281c0180c090b80e400595039000908003000c09a95019151444880c19024121000d05040c0e40700402c0d0a80700c007946e038403d40880a41e1504c1e64056120000074040c41c00740d44420000130194043c0303804000308410307420803042c0300f5150b40754a01e003843ea4501e50f00800030800ea90441d0824441c10081a40d11500542e90344000000c1ca400551f540d003540355107040588100c07103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 552349379 1250 552348129 552348131
    0x30e030f070e0709081209190306020f0a031413031d091005040f060810020d0b0a0303050702090c1207110a0b010905090c1c300509040615200f0a0501 66
    0x5002c3c296502c1580340f0050142c2d00e0080c06881c01044800c0018010118064450f1110101c03035042c10400f50202001140c0c400e5041d07450303580b140340526854011000580000307292004496071603040d420510302070380c1c440c15400c00e000710700c1e10116540200e0001a10089001e0b0708001082d407240c1d10014130403680d00c088410321034101801c0106440b8905541d0100d03608012040c4031300d045c0801c0c0d4040202d003c482c010795900c00018401d01403c100420a544442c500d6000002d041d0030000800d5072510032900c04102e661041074031500c2d800703411031080703880511600007800c50340510017540d951051401211901c0f10566a010624030003604040940d9032034009112210b04100303d2403030585402c07600d001c080c03219003205c0c4100201160010b4558140c0508a007018402c4800d040d06003410740c820380c07103003c8156402500561010002c0b6000307518003540040c1c100d041d1108940e10102c03075a208644a2916150701c070400c4004680e81d01d0501030307450589550703842040b214103d070b03120700c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 552350629 1250 552349379 552349381
    0x16020a0b07090510020a030906051b071202041503051c03181a011a0306101701290906120403030612050c03210307030c0c0c0b0711010e0d030e030f070e 67
    0x7041c003200304c1103080c80030117660080c0003c0d400130f5008100c81040d01d8079480e00700d440f00e58441c03031085010300643e4841d6542c0100c20001c1203aa4112086200c000d00980d000e00c002d04140781c080c04544224440941190480101a0303841c10861154010f414074500e004191064013903004103404800390000c9510300c55030038503840f0041c3c1d0803240a0042c42c00c52096410b10000e064500c8203840000c1c140381c8a44e800900c0780f02c06500440c0050f4041c2d038000c0d05a401903846400b1112031031541c3c84408210b0113455903084001714031900311030360000098503e5042840d20a98000101005442141815260480865101a01e003403411032a030249000380f00420b50f04c0103040c1010601010b0106562417800618025100c0008032a0002c584d840c0002d92510800ca040382c011004041c014100400c40d440017a10151440c040e1070201e010305d210b6005c03c0000401500c4000d01d03110151b0700900ba54680c60082800380d4102d120008010b0b0030768590300002180207082c2840c0b070300590340445c020b070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 552351879 1250 552350629 552350639
    0x71101022b030b06032a0c06090f0c030d0c02101403070306090e030909070f020109240b0d0c0501210603050f061e0105044a0102090916020a0b0709 65
    0x20252a900d15004e0b2456440c508107807030304464110605038426221200c1c0a20901c1040a074002c9405180c1e24605980c0c81c0d0900d86040c070384806441c01d5481d180d216031110950300d0701d0302103520031905191380c0b5805103501490b0309000c0c04400ba402170000744004040c044524000070801144a60502c0c1e0740025190304006401003150010024521a64828000d0000710340310424500e81040d0241443c08c050380d80004120b02405c1c1d841402040266000740313400c0c56000503584201e81c20402e02c0284405503501e414001720f21500480904566404402005a5402014052182c0d034281002c4401b00c0c64103000c82054030b07440c0d40200c4243d800fa841e40c560586062015a400c5900c00c0c0060f02001000c44480c203c480040c065207204a545503401030005000da2241550304400300aa800d4989d030181903003e00e03c5081e00d0074072000050004d680d40b482418402c85002480043c0b0600103601e807506403071001042d0045440c190700c6030740f0400300481c8a01e031041c0d200b04059907511900c03601380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 552353129 1250 552351879 552351881
    0x9080403081812030f0d18050a080a09120f06051807030b0f0702031e0d150b030708090f0307021c02121c030b090c0702030a0c141302030708160311040f0317070503071101022b03 78
    0xdd9000c051445a42001440028900e9040d004001c0e040000441c090311404190941d4a003131210b400b895104c1c0101c00004c102c1c681000320300ca9403c6c001e00420568805409076280d20400d0303200d058002c81e4000042902d00088003400c02c0c10341c039950001c1c20312040e0b155160341401c182c100317401c004000b00402482c4d99122100d1030740100440b01a180b50340765102c40b141e5034016154000d105082001240055000c1410150766464000f00520451442101c405442e01241e00c1e1401c070101e1502c00fa0800759001c1c1c0640d1035043c2e0050007541050360b401e9560204c0d43c001100c100d0303050050500b81d00c00701f43c1805009000c0e09550300c1312032682500004010a09807a401c4000480740103008102507a17400148180e40601d400200800c610021b8004400030a000b600c02c0380113020100d00801d039021195100421360b4400c044a101501d00c4000c0131515001c1c01400402c0b59008018400c0081d1084031100007114040c011604000d040c000c0c151504525000a000a041c12412180f078850341 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 552354379 1250 552353129 552353147
    0x30f0c1b0402040312140d02040b0307020f010b0109140604080102041715240f03030c0c010207080f030a1808070311030c09010b0d09080403081812030f0d18050a080a 73
    0x32107045207428139550b01c1e58249500d007400c2c881031189510080b0105003280080b40c001c0340302c4010441d85c0c2d6403120315186140c0c00c155842030051088103e05065408144189602d9510513102e03040d08501d8104900c2c4a01c400111064110303c05020001d1071341001d001500140201c004011a8030000311645464003c50041c0b600c044600101440ba0001104480c03d00507810900b0b16648042a400030510342c040300040c03240c05100019941e2182c0601107030307403a0904426401d68240b10356036600c3c1c0e5a1200c8100c0280815003041000c4c5040f0b81c0901030200b40c541c26044103901c07456880032500e05045440e402595010004220700304145010f200403810301c001241e000042e5414042c1d00030040c01080403014015544074550000e000201040d50010342d4410f10643d83c1d40040642c00c0100c0000e04100d5018607000c1030802c60222010080d00c0440207080000c0f404c004104402c10042c2055602424003000c8040504000c0341092012602040c001c4080e0ba0b590310b0011801812914 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 552355629 1250 552354379 552354433
    0xf07061d07150f0e01080a0902090703020912030408100221040b06010f05120c0a1209140118030c120c1b150c0f020d020303090a0e070f0804050a14030f0c 68
    0xb000c0041c0d980407900258100761001013860041d10b2540d0b87e0700c4100c010503510b140a90312000c0b050820441a41c1760b0002d02d5824000c0c1d540304c90341e8240d44a22070f9039001d14084d240c2c0030340002c4410400600907134050480d2000d400714031080d6000b01151050018010307101582c424400b001089001e5800000c846200000c0c0e10f0040d00c2c1118542d02e4901054029107410381d43d480020f0001c1d83d00d03114440003405196040b0f800c2100d1425468a418555a00c510090955080c0207940601c0060601086101d5400da1601c00540d4107599441e034110548500c40414414004031440120f20140450640c2c0648020700c0f00340c203414005910100151450510104044420550002008400700700042981902c114000c0c07a001e03c0002c1c10f600840306000d802011101001841010720301206005417140d450303501208092950442d104a42143c1c050982c2d804807334604001050345030001140c0c91103000f680d0808007220340d02d8880394810005416154840e51403081144034644000c10340394 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 552356879 1250 552355629 552355637
    0x90302011e0e090106021b1008060d0c08030a020604020f010903021305090709140a1a0112200a091a0a0903020d0f080a0c061406030715031b0c1505010b0f07061d0715 73
    0x208c0e41c040c000e0800c100108200d010740d05c0c485107603040088581009024154000641b6154014008004c2d40c464003110103a03ca00045038001440d0350240340c52400b60780e0041c04541c2d4420030740840d840500700141c454501ca204d85080040c0541c071510a017580c1d041e080855403c50b04050f00c010341500c100c02c8134416403404104400744a680c21041e810100e2100c0c003004905482c010fa0090700100c401c131a100b00c1e0758800640e08001650000e42e020941d1000a01e145642d40c41450100e114022401c101740425220007041c4007501c3e1010030709820703501c105904842094141d0350445070380c20040482e004102c3c00d04c0d0310805c1000ca8050b00007a51080101c403605440c02e100002e0341c0e0300c030610079401c0f50541400101d8615102e900f040da20000c943c0d07001c201c0d8884840c0000c2240e00350141c02d8804d0201c0000c8505e0000807801098101c520b1120590300b0007004000c0225641c8c0b0040d411100070382e42d1500e0900302c0311000b000e072038208201c0024020345407a040e02508140c400030180030800c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 552358129 1250 552356879 552356899
    0x9050106110c1e0d020a170607020f0c221a0f01030902031b03070f030f0b010506071a070e120304262805010515010906090302011e0e090106021b 64
    0x280ca80740d8410712418145015102c20000300e10204030030318041c0602a411440104021031018a000c14864640c4102000c48e0340641e1849400c03a1620740d6002ca12015030080221b40c100c9203000c000c0644088075800c01c061186041c0408a0116110300250844444014555001a1404550110b00144282000d0008480c2940080e45810802ea420b0444605143c9038000540341081000054034800703803c0081103803070341400301c58100101d400302c41c0300c00188004205400c049003034519869029107002074220100c003d01440420040400003007180d003485a0300b60b61759003070026200c04054805140d49078104401d48031038070000d18152000000c410404a001c4900068440320104c41e1a06420a1210340d03060709808400c0c004040c02075820141400031941180c955104074280c00d8888a103029510a01514841d00c00c0c800a0301259042c4054440709200703d4100d044d4103040e00d000303500d2f40014800a04004000e8021a00607405080079401c80d21515024048a4400322914406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 552359379 1250 552358129 552358153
    0x20c0607330e010e10061215060b0c0105041e020108060405090f010603081909290f0d1406120a150902060a050c0606040b1c02031c11100207030203030726010905010611 74
    0xc1c0c410044401030205080040b180c8e86101c0c650302043c09401030115255032400c40302d81d020302905040c0c03810390b0b20349400301710100481440094801a82c1d8180c50f1021f41c0d940b06810040144401001c0341110700500c1002c01e41c0c0744003845560702940c801d03425a0748869020900300300b1150701203816010b02144241c140301700714072800044204214518001d0303c808201000b000e0601400031700100070040841d01703100480300c0380c000d54208130b04120320800540e00e460400c01801d40078050500c594000140000101d00d2450480c51b800d00080c3d0040b88618050740460040d40c440d454200005002080030881c00d0720030310090740c2141013210709000c030760b41380301c002156042004450724401014220030b00c1107450900a02c0da40004041400300603980300030025041e0030790707000c074482c1c18040c81d44811b0441035144250b41c01107030154011821582d901301c050310084050359901144c940e4451050130b02c02c42651341c60f400f9101e03030000130a65501d444005891003140312120700040e0001040700395 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 552360629 1250 552359379 552359399
    0x51005061903150b0705010e0c0906040e01090b1e0a02040b0a0804030c0c0b04051302031501030b1206010f0911070515070302090312030106020c0607330e010e1006 72
    0x10703812000d41004440780c24044090700101201030450340c00e0390680314001100e10001c80903220884c0076400a00403802d00b107c4150f2a01c02e6250b079994861005001f2500a00b46640300f2440418010700000b90302481d070b1109000880102e500d2015400c0c0b801c41c074041074010307072000754010022402c154103050610303501200c81c2c06071405203810480e510740000e090500c58501e030b00b80541c0121002800d140c860144110079807050141502078141c0401e988505a51842243c0c0704007c070072490004000c11308011009451550603d560007844d258110110480c20301015000344955101e018003d0300e44041c0c0300540c2d0f043e00c0090041c40051081601198000c28608441e80c0d1148017409503036030b1003070309070020700500040720340600c2115042200407109038001c40c161400c43c1c0803141d6400844040117080d104041004155081700305a810081c01c41034044401e800d040120b416103006605040c0041701c201c00c080d140e90307a4583c00039512062050000c00c82c540384001c401d102c400d003410142c0c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 552361879 1250 552360629 552360637
    0x4090213080f0316110d050d11070501050d020304050a020909010c0e0f01050a1101020d0c051822020f09040f09021f1b06090b01032d0f02060c1c050a0305100506 71
    0x5840c480300041c0d000c00a02440c001612440200108030f0f11b5500d0078816620328047d480c080c0803602c5031040c078002a82c0040d81d1021aa8141d448a141c4000905000e0188d040030b00700716020300c15003481100590f100f0782c0c5944035110384000090071110514004141c41842c20a1078002e103041e6010140d40e903480012210090394906103503800c040103001150091003040001a0001c2c030307010b800c0580a5020000300401e80d2103810481e580100f51080064144600d00c000b400b10611225284185045401a080103c8100600750a00050790046400d40c1e040c5150f1024965131075280d001140382039440110b1a142d596005264a120b0340c070041c1101c02d480340512100031040101c0010010b2a41200384d4003540700c00f01e0807a41d6541c2c64090400c48008030b902c100c0030300304200b28040031049907041294582000d115180350f02c4c140c0034407040b0303440051904014020f80c0c07110115200385081400c008a081d9480c90b03603861111000a0458502901d005000c030502c03c1d040101d650740c1800d032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 552363129 1250 552361879 552361897
    0x2313060b010e0907050a20030a03050c041214070f030606080f0105271903031b1418060c01050c0301080c0619142503111c0e120304090213080f03 64
    0x9295510000351b07054402c1e00c509940c0368a840005c1003a1180200044082c22000b074007900e00384295101c4d90b0074003109016902906c40d269210404807800303e03403800480500b007201c2005842c11039895883d03a0f120031a040e00103880c01078840000700480003081082d48180c6404000800c454201450130314041c0030602800303044420315020f2881d084400b84109136442c001c2041d070701c09480c0036141c09070140641e40030b100d114211814030001c07418014501d503680304c1400381d0901e190805040c0601010f0319001d04250f08840103200b64000b05000340b00b03880c02184040000d41d10307036140c21385807442c141d0844c07134103030040c6002d00130040d116101c8003090055400a0402d100d4241064480701a01e000321040c1d210051416031440707200003a50204400c135180641d82d04440640b08402140d511000d2030000500391030b9039580e521185114181c9a810707044003c10594807166040313020303480d640094100c0c441050303000850200c40f0110380f654800401e5070f80080c00841945481007900c90103840c1035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 552364379 1250 552363129 552363137
    0x90f070c08030a0b180601030b030307030c1b0801020d0501090633050c060721091a04020102010605040f05010e06030f030304120509120a03020106060905132313060b010e0907 77
    0x3c500104610b03045000e041d6000b40005032550b40600d48020100c8040e10b40a000c41d1500303611842504010089541843c0c25483d802d40115565984900c50301c11101b8103100c8000030079001c14031790380038001030070008014007010610f541480000e1044407855440046903815001c0010188000c00103602c071858005104801000c85c800e000391101d10420140e880301e4001c072000c10050640201003030805c3c5000d01b04118a0310065414502102c603032100261040c2c10100551a08401d44007242e03621034818400825a0769a80c0c01140035100314503d00790400e07889800521507030581851407507100704110b00808011003036042040d00c0c1e00c00a400541880c40501c5401c41c075038062412692240809040d10392a008855441c64403281ca1901c21401542000c200151b00351041045900ba114001c0920424988400703500c4001c0140c401954078100582c1300024142c014104800d00c01c000f040003084012202d85004412100720302445818080d5801c1021140d88620016590110326410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 552365629 1250 552364379 552364381
    0x11041d0c09150a03060501030203070903022101051006020f0319050310030206070303090501050a15140d200a090905030906160b09330c07210509090f070c0803 70
    0x110540380c82800c981c1da030040710b051416492100224010b081026490750300b0004142c845004405030712090b6000800540800002e0001d4500200e102000b001c4030242401e8880804c50741901791036003117030510300400302c1c81001c001d0581c0501180b11031115050146261880c0800600fa81400038040d070420401c0c00700000780002140010040a1500180b010751200302600c0d0007030142c803801204441a500f4507000c906401a540a010b0002014a2007070b89214140303245c01c04104403105410764400100c0e50030f60041024195a0400e07152502440b42c2c2d070344c01c6034084c0010070b030556001c4020503203040000c402044021090700d41c448000c0720496521324400c2c05d0764807032074140640030348603c00070303410301c01208000036038103440b1201c81d5a10340c22031900075290386d200c01c501c0b101c2007816494100060204020007000700000e6204140c3c0c0c402401e8007410b2403090401003850140800e0340046c00600c180f503c2c0c94488ea0060400103080c216150602c4000d085454444005100700c1b000301c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 552366879 1250 552365629 552365641
    0x1b0d05030706110408010912090603020c120d1404060b090f0c0a03150b16020a30030512100e0c091e0f0418020901080a0b0408090102160b0d11041d 65
    0x804131001010144004c1c0b022002604143d076030020308214200c08110072000005511740030f40203480348000c240000d00100c0442111644050b4494116049030554030744000d82240305800c017150086018050000320f0141c10404d01400c508003400000031b986001c41040114402c0804681810740c6614001c5810110021507008124040e08051f20200010994100d00070000000e05400390003261030000803581c8080e294404904c41c1c0840e0b0807081102507051128080385554078880c1d1007440c00e10320381000401240c642d900c06541142401d10b40706820010314900c40e0240b6041200c14200314a0100302900151664890100002848c038084001c035910b540c07081d08244800c400070b0000d002219580303000154110f05604201d100e021b500d8000b00d00040e0000780e240c4d1165102070b0b1030030940c40300d45401300c5a0b00910b8645d8114400d009200355418003902d10a402000c081800c7c549505540c0105000d032600400580c500324005e2000700001203154500b0780c10901c1c1c81c07c404a0a842c0c01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 552368129 1250 552366879 552366911
    0x1805060a050c0726040803191407030e0d080a02100c0525150c032018090c070f11011d01050a05070302010b120a0c090605011d061207021b0d05030706 66
    0x2544089001d0000814009076043c4c002c0020f0450307070b80c0510b4441c240041c01c1c4041d1414002c1d040010300752710782408004000390150100b00403014000303040d803d168419a5855285501885080005800481d86803400c224030340030310b6000c03950071309100c0d040040c0e0012600c00f080030b000c1a040c202402c1c00c200c10074414800e07204501541070210030f1040803081107001c0c02a140002c2480e0b01c964224200d88580b01000c426544070380300b00010885500a60002c111032607a02900503106504100240d50006e0040d1828120340c1c4c1c45000b07840340059442c0e00140510705440d061542240b421041a4072aaa100040b20448a0b480c2007040d1074500c40d04013203004080545000350020301e02001c1d464080000600740c85560700c1740109030440c81d1180714860695401d03203c0c6c0c0340803850040310a668070011108550601070b02801450503d00628465009043c2c00c0d1103010158110341e42c5020046004542d5410188096803801040001a6201ca03a64441c483d000341c030456030342415030000500c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 552369379 1250 552368129 552368183
    0x309060207020409120924030203190216020a170601060f0c020301060b032d040314190c05010b01021506120a050313060206010e070f0c03030b041805060a050c07 71
    0x20780100301c80136881c9841948485203854803004104100800501440300ca40d80706c0d80c1d54030402034a420b0419812041e00650000362080c454400541030388202071181d032000c0c1828035015041d138496442240180901c64010385c01421100036601144820f20a0010700c05045408078642a041d00502d048110b279044c8524100075459402e210340000c0194240001c0e50050320301101d64620b0b05101b6596106290701d21784404c0c10129840d0014001c41e024510b00c1c001050101e64032850001c0f02a80b580b00e111501001e41d003c1410100820148032091191328900102800106200d01c0c182600c1058900d000b400c0d01d1052441d00080507102c501400700003903e550000c21291a10004901054000064040c1c1001803103240700001d1209200043d060242c999610b030f0340b8003144c52031011654643d40c0c90069007071544481408a00e600c4d188940c4045040c0d00e03403000c0d00040986092820b0000c00340403e6100c03401e040c280418441c20a040300d03c49684040075031100103100c4265180440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 552370629 1250 552369379 552369383
    0x2f0906040b1c1514010312020606031915020a0302030a0e070f092301170f0c01094103120304031b0c0504090605182a0303190f090e160309060207 64
    0x100341102d607001180484c81444c1664400c0714038a070f10050b0604100d030b40302d200b00d0b00258582e20040d00d812542d000345c00207070310300341c0030307120071803001c1482903075001640d01804140001035030020030003224821a220301d41e04400703d1400740011901e02030a50040580d00d0192450300c9949043c072200304140390311072801d45201114090341c10340c2d55000741c103065030701d4040d41c40380350007000781e28112040041801041e20b80305031101d00249080890740314200e644650b41e06850181074004920404c88a46280010071544490315100540e10003410700344a1400310b54060402c0c280240400250440240c1c03a40032188065074080d0900ca040884482d00c00c0d0b44855000ba20f884402c02c103001603600b06511400101291000300112189165504c1800300a807c1203030381c030b83c00c800304030000800036059510001012203080c81080d045951610483c094448003180c003040c041c162040d040068200201045051a0b034585000301b446001c1c018048880c400705565210b40a041103407540c15585559 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 552371879 1250 552370629 552370631
    0x7030911041d07060c17040803031501121b02011514010c05070b030f0a23061014030a02041509150c170309060106091502192f0906040b1c15 62
    0x941e13540c3d4058410301d004c00007690302003031000341c0303004280c0c0c2e2900301c0d011640050000d46c0b0315628140d44011341030701d4014241c1009074198010b2403d943c00c2c0510302d1000c001c1c095a4030781c0983c0344406821940350801c250303050800c45000300104501050b01c1110603000382040c443c81001403404909000071038000f030300340a10200501030700c04110b800701441581c40d21004c1203024240f07905003584016090310100f140c0f4403000068900c4c103040507904404006818494840c640112403008560022651140023550200e007c100034030308000c850340890352320701b0b080c034409041880c0391401a014884100c107101030f111842e401c0143e00229408505244a0400c2d01d81c14110142ca40312a000c1c880c060009801c06400b2980414020403000100b0440e002442d00c05051803e4100006001500b501d0184290f01c004082c1c1030320400c2c5041c07203583c5030705ca80d01e1203c005003001031046001d82103a00a6141c0480c2240c241c4500d01d024141d03060140f8100745ca60320b1842c00c0844680050303000102c035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 552373129 1250 552371879 552371893
    0x603060307170703020406050d35040305060a0b0a03030c06050702030405120c0f06031905060d060c080108061501050304110a030c0f06022802060f13031a07030911041d 74
    0x94002007840300c00d42e4421101130001654238010810781c2c00000c18050907a802d5584031110414510b036060410100d030700d900381e0900408103d4940d0300c0e00258010350306034021200f0031001680901ca49a80040b041b1a20f43e603850850b200101841d1b5210307001800641d5603000302e50001d0081054034002d0a00400c220341c0c0d140c4420790a600d03109040009401010341341742a0a65140c08401c0d20f03c101e400d07480100400703015005c88000f40c80043d01c80c1d5001b44003c0d000d40e000c00d2803400345801208803603c0b111541e52404111600e0000024050300040ac20640e480d4003580c1d02408580d00309030421402000f81071502d0005412003031660000741210746411000492140c40c00340300042711320503020760340d840e5011900c80c1007984540702140d03d4030b80041c590100610f0100050310080d2720001c01a8244400c210502c900701842d500700b030342c650b40060700704a14403410048056010000740381c24040c841c0c59076191940c560034290a24030440d1524001903c8043c1c045034000c101b001103007154a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 552374379 1250 552373129 552373169
    0xc070f02030613060e061605210112050706031103151c15150b0f0309101a1e030706080c07050601090b0306220f0609020315070206070201090c03020603060307 70
    0x1000030050f00c00c0f01c00d1030130207103400320750a40071400c2c1d80f02d0700e1540300e04109298002401c07610b80d0f0045002c01200c1560341015105c098002244038080c00400c0e2844601d01c0b203d0a2441c40e045031584030004040c142061440107541450aa07608800e213075504031000348a1000290007544c5851140c4140710302d5440701c400744003459a404c03500440c00c0604002401007558440c201d4106802a002d07a20307020000c5c05078031aa00001540d000d114038083d201400da007494080142c8802103402081440c400b0f07000b5100d442d11041400aa003816120701c03c0400f00b20340480e480700c001e031142c0400d114941001403200f91f80c03c001c13030301003e5000c003e40e102580c42d460540010405804924000d10412000034000c4404808031894a40d5031407000c0e810650540c0c41a5400000481c00c8891548a080500058a0401c0980d140c100c0301c2d85500400d180000c4000d241000003080f10046a04000980c00030032513205083c0c1c2a01d40644001d50389680e0003011030302e040384a134804400444480c0307401803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 552375629 1250 552374379 552374401
    0x1207081e16030f0801060912020d230321130f060e0a060e060114011d130207030e090a05060604030209060f0a0f080f0a03200a0605010b09010e090106080c070f020306 73
    0x210031400c0d840e4213240d82d0329428115688483c5014070100f1030380036071841c1c0140c90441040620301d442096441c00c8036201d10300f441d22070480e12308c20a00c603600c0401c803002130b0100c083d084000710152142102c2c1c0b902e0b002e410075840c0400c202003e8845280c0c04103100a01c00c1980211900e040140d00f21040e409885c1b41c018001c014191902c800c9004581c008502140c0c0080751503048030b4160b58541945811201c90402540d01207503640e80161420f040511035022400a004558040e0321040007200b990024441103901c000d0802040d43c0c5000204030590b624801581d040d6074064941d00d019544840100d4650725860000341d43c4210400800a100411096620160b0310b0520544000400190481d6982c0134402001004241140009400c0008030f8201501c86080030003119000481511410200c0307000303800c0030705c40050009880c0b816580000159400100a554007002c2e5031505000130302824000d4007240c88200c00203034070001d0141c1c4c00c0801c040750740c00030203450301c03800c100c142c0c5a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 552376879 1250 552375629 552375647
    0x50903130501031806061e050301061401120b0a06030603060b0d1707061d010618091505070e0d0308070201270201050a05040801050901020711040507021203190f050105031207081e1603 81
    0x340c0300340081f80049080c0c00c060103140c041318a060020411020800c0042d500650303081ca28a44196666035a4803069880e20202001080148c8000034201d01390304040b0151280880e210380a20015904000021401400103611024950f615501c0b010523280400141204050324401c03110403620035641c09e041940030380c1c00c80d045085501d0b450360803130082d14280c414080700a800340642500306910a00e4036000540e222101385002c0380058079190000d82000860182a00080d2140b03080080f100d40911555411450032140146528100403480f01c000803486402410000c001c908842140e002d1800c2c1d80203860108002d0155240420600e4002d421010082d190f00081d0103201c0024203282c414640155003980c040e10744c517001620514003c4c1d001400701490303a00302c42d004011400301ca10800008200105002c14194907010800d45040000e4140440004040046200082c01001102c0050541c440940241c0700000100101d0b4090700f00009a4028180c0d1683d0415078411038207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 552378129 1250 552376879 552376919
    0x3040b090306090613020d06021204110a06020a02150f090604091a0607020f0409112106310606050603040303090b0a060b070308060303090a060c030305090313050103180606 76
    0x1150b40b41d445440e00d981e10001039844c40c030f0400000030f261001d0300b8009445100280070b03003009850841c44007043d015250003150196131389a4001e14580d130074941130141000400041c4001c00a138101500051a005445010407503500c40c00138045031080403a0054a000f14001000b45444651314420200a00a209a01603640300300842c4400f0b186440c90648506070b8015000c00c610b50841d40600004042d014426101c04a004013101c3c0c0b00c0e41c5020003500e000200c401007283c01d03820381d0a66464407001401d0810007550114400c1c2c81e0100080580100c4d41c24080124243d0096040181c000c01c0b1541006800880000400c070500d40c0540001041d03e2181e80c030b01e442589e407080684200c50281c000c06805000800c610000719105202481d04080002c3c1600d160001210019004004a50198020031074020b060000d06806103d46a070014030304c40038514044011502003905101805440d05040d074540020b00d6a4090002001c038407980705a04000142d1582060700d40c5100403000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 552379379 1250 552378129 552378133
    0x303081008030a2709150608010504050408070b040f0512030f06010905030601230414010509070804030c140a0b1f12320316210806120f03040b0903 65
    0x5031621000089030010a010b80d114201c071161310400028084503103d40710f00c040c90007940490034454600c120f440107003080303008000392460440d002d010003030142c2c01648520f142100f0040452081ea04850b0239941c0304546001e01d5440e480e104462140c00c00c00a402803050044086403603d480006601442ca4064042c02ca50390b203000444d400001c2c3d01a49415400c804010041100079400d2b40442c1c0f42d055078850041d42c1c8130b401040071a41142c14004802c14070350010011800e049030859046103451914152501c1d19490207419400a9000104880c0c035031140282801024440d0040840d404144162242049044083c000e903610501c40c540301c43c04000065409980d40c00594810b5028003c2c0d00b202e22110744844080c00401407080c111190101079011180043c802400c400c45809408840007a070b07803d2000c0300301440e4840c0d41401822001380408160000d03c051f50014003150381d5002980c070300350810306165513090499194840490040761440f806000340c84141004c2d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 552380629 1250 552379379 552379411
    0xa0506011a03091203090f120901031d0c0108040201030b0612061c0b060f041509091e201f0207050420030c0906040e07110d021b010e0f0901030308 65
    0xe4101d5140b106650600f9643d100880070300f203001c034a0303010b035520101403070503128012800410541030414065440404c00c070001010085e968051151294500102c5c0e4001c1c3c0c80185290860f5031b40c1081680c9605101c04400002c0031a8440c3d040b1410701038001e0511604c846034107102c01049841501d800c3d00c21200c01c100180b21200d01c440784000140c000c0024141911220244034009d0008109103070407940b01d07032100d405140700701d0318400104046030300001c40344c40c1d50404120001688800440061100d014a8089030b050101c400800c50300c3c6003841c0e0b5000102c1d0018211064000842c01500a0031015511141e00406d0400c102c40c030a40f030600c1800b80200340c01c0d0000780c90b040b50121000040c008149140d03a8640500701129020706480d207415214403142c2c0b0070b14403c9800303030f00007000002038881000050000c0018000c0c20b0004000f0f200c1002c0e0200ca024805002003410040f0701c200110841e0350741d181142c5e901c40041e0010b840d41d61242402005024225441041c07920100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 552381879 1250 552380629 552380669
    0xb060d05160806011b081e04080705010212030a020a030b1309140a21020a080f03071805030c1306180b011b080d0c050d0f0c0f030203011206020c07080a050601 70
    0x1c03002440307a07405a40c5e000c06105411a001c003241d14990741520b0701c0e0001d000d228048000c0750306800c2d8000c040802d081e155841c00841500d00f0409800c1030381150010360501c03015004407400d40b9048500c5410158440b1403240089006210b1f1144090b0310400e1264100285d06095000059990192000f540742c1c004440c002ea69885840b000104941d801d1780d000205080c0149141c24480214030682d034500b0b0103a1102e503002c0c0c002e500c01c552068400400e0002154002c6082011000d030305001c4400341c0d2900c000241c80c0c18015120a020714907407070100440243d05c0e481440582185905180d100008028070720051204184242c00b241340840100e2190844034043d6001039805140c081c43c0000071010b260180192613291000e100301400810b4600b00300c0c3c060b40851203140c400c009201445200e000341383c051281900b100340340c8100011300091040314601c804040d0031650144c1c3c0d8905200d0340b00d01c3c250b40c592088265010303c0c00903a040140c04139016040714500c82c01481c02d03110303103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 552383129 1250 552381879 552381887
    0x50304081806070f11010e031f020a02070812030f0609040f060c03061d0402150901090911070c0b03090114010e1317070303021306030e030d0f0b060d0516 68
    0x984000d03280000a000a0040014004509a50001c09403080b0b09264142e0740b641422080b00b1801ca0f204c1e03400c015181e61950b88143d9072500c464085000b0f050310b405d580c0306128141d0241d418142100e40014081000300d008008280c014401d482c02c40d00402d42c48031250440303030000c2d01c46a0224585401282251410980d1319002d80e8105c0786044078403840d60b0340c440080c500c00307040074249078480c0000200340303210248151040b40d201e00f0110343c91501d072041250300c12148d118581c01c6d2009010940c0c9030b9a0125103082903408071a000a0702000d030084081d00b07130180d410018160f0340d12602c00300d90a149a40a14010121704000b4040010701c1c0034000480b400c00d001d400e00c1c400c83c0c400010a01194090018952401019494080d8001c002e1115040e40820001e40120313400241c0d00d0f00303030b042040352000249600d18041008034081c4101603124826042201d070700c99140e83e595030b44200d40d50300c00c01403080300422030b80d65800c04d0f01403c409488115110f01800788105203007203c260007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 552384379 1250 552383129 552383131
    0xc06040b090a0906060503070c060902060301080f01110a0e061e03010f0f0905070f08250c050c0d0210050c010e1e01051e0c07081605030403050d1407030f0e1e100503 73
    0x510341b5400c0c219501c44104aa030718400c10400c2e40e0711034483d5000d90258488400642c060701074035020300003050340c010404c0d003980c0b03103d0004d804031072081018803d140d501000411000300102ca5266468000c1180c403500b407000c900104054050000002503081c50003100ca80855001e51441d1351020394460303004045031021905030002c03503142c3e1280e11445202e014000d500c40c840b6800c1c030000441403030405080c0280322802c103020841456558041c070104201d44051440c080300c003a1401541607020840644600400e03c003444004500404440c8007904112020003005040361102c145403c0c0d948044000b08400607115468403000c00c8240042481034001c40080c408054030030b072110510383c8480e5000321401c2d10f09010a0018203024090400400d84040c0510000e548a41c1141401030401c803074005510700340110340540c0d00000e0600800e465495402d03050144401181100c156031800600711403c3c0d204952a4208940b2242c2c2c6807500c58032801540c183e848400301c0ea80603240c1d07200c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 552385629 1250 552384379 552384389
    0x5120f040b0a030f0606030c031103040218091e030a1202030f0c090402040906090f1811010f140309010f1a0f0d0c0b07050304030515040807030309050c06040b090a0906 74
    0x80100300501520741500c0080004906614000610540c85540caa089400c0c0b5042074001070388901e44c145803103905016402020500510040c0307907080c542d0000d00026206120f007281603002e1000214461350500005500d10703400080380d0013003104d10655540300d0340010644c85c0821007400d134107a955a560300c26a0b01c5014103458105103a11003240c1c40015400c50310303075076502c95000c01c0007058400c100e0043d2030080001d200c01203991054642c684050704c1c003441103c41d1104843c2c03500c4010034180712070610010003c0c24001446003851504813100e850107505a115150000244007038036905601c445000510340208100348801c282e10582807a1600485a0340483c00c061014031030314000a103960032a00c2008492030f103503a249c0446056030045001916160004242001031001c00d01100c0890b0303200341c1c0282a0383c901540c0391100f60095800281c10580d07101c50000030014100103012401c6001080d03c0d032034603602c0c03200c00d40075030100b0700c4207019641c0103400150040203400b800043d60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 552386879 1250 552385629 552385657
    0x2060a0606020a02190812190201200705070b0318010b03120403032a050a0b0f040b0a0c020f12040906050d050a03051c020a090e1b0301050d1103030301080a0512 71
    0x1905502080b40e17040c22038960024696000c040081e94040410500d902040300d071181c04e441c1c0c00c490b20301c11003d00c08600c010f015641080c090f009801000a41d0480381084a002c4c00c1c0c51f01c0c200d0070714601c0c01c003003034010340d040f282c2c0041480b408201c000494030064a00200901100c00a4402e154a588044101c440500d40901080c0300080c041c40c400785203c00b42090150042c0c03040d05000703990072202e40701034415800c0075410b581400320400c0c403241d0003d13001070084114140396a07101444580102030150b029903480c8180d820754828000c00751906039400032900d102a00c0080b441d204c1d800b52064051080c0303009800502420700d000086030040c2c1000c0500294034068400352442c0d4468031045d00509031094071134140d001c03d48040c1912400070798841c0010350900b0040030841f0b00240111102c0320500f5141590013407400110b07030540d40182d50809882c500d47c5042d59016842801090b4103001c084004507403500c0001c1c120144074001c03000ca0708400d00e10b901d401c0c050321a00740360f45005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 552388129 1250 552386879 552386893
    0x6042402072f04140112021c2a06020a080c03120f3903091203040c032312090604090906020c010b060a0c020f0f0301050a05060109050604060c1112070b0a02060a060602 74
    0x42003104050702c4070240041c040c20032825100e1a985150f132440342044490507014150107072549c1e034203c003084140b402c48001e100054102103000c1e6560400c580c000f0004013001814080c0701c0c0c000d100362458843c3c201d0046540e41445151514041400c85007000d500c1105000d1060444005ca12002c40c1404030f411807212900303a03451034a5681c4001e07c00c10700d034400c01000000c0401a44002e40c0708600a1a03500409401c500d0020b106840503964910500b1100c0c03100d219100c004107011000041e01c1c100c4c282d45904000c08503085000c0c561019220615101c0c0c0c000602c041600101002d60400008000c0c030010740041220500482c0856000254007140110050418031158030b44248000d10810b16040380b680000d0070742e43c00b201c0072000c2503251014481c440d40c00445460190500b101c4540c205401c088001f000e0444002002c0d003c86100d84c1c01c100d05e502c0d001240e560110f0f2990580e201680c4800980c11b01d640010034250051041ca0002060f2142602c9000242d500c1540a1700f20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 552389379 1250 552388129 552388139
    0x303080c07020d1202030c0d03090203060633090a0f0e0f09010b04181103030a0f050f0405030f07210b0c0a020f060907080f06042402072f041401 64
    0x150407202040360850329542e00d900c045031000309002e0160a01e0340c010b59550349035500c0706081c070b0640803240d028981040c03d03000040c1e80c042513065015109980b01e04914519003001981d202010b443c4461105030300440505103030568009010034a81035941c50f809660743e404003c200c103124484d600c00c12658001091100161042c095004407510f0004074103130000400185c112000e100b0301d00c80021560a1000c00c01101100c1c108640c00210301031401d2000e2040068121540100310704204240000e410f0701d48094070080e1b070080d00004c0c081301c08440140050303c2e40c441c220f010303815000c08843c0c01e030342c0d403440050f03081002503174888034040c0f242e199091a1140c03a0004c81128096009031054240a94810800688680d00090003081400d1525144c0d0b41049090815080d09411013010080442c1c540040b44a21208141001c0440740c0011030131002030041100080075441c5140c2042c140c4a143c1d0250610641803d40d0b04c0e2010a10004010854004040501d007803a58070004201c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 552390629 1250 552389379 552389401
    0x140a091206020903100506030d0207061b1a16080901060609050d06140c18010c050d0806010c060204080312090c0906010e012303150109030309140414190f06030308 72
    0x2103544160000b50034004610000f9041882d0700f1454000b41d6510750400100b0314040225540c0b181e15400500703007c508000b002000d4000340c005001c00d034060742c6101e20411440110f208555504c840595100d07080101069015142c50b0100e00002001840494004407042c82444d088072600e0319081100d80c500014030540c0749407900191640c0b03a913803203056442840072040d9485043d03414000c6640704000703c40f00e010781c1011201c0d24104641c0001031030024500050a00207481c43e42402e6103195240d5004031098180d008004002c10b0011800050000c0d000002d05a404c00380c41020a9565610414136600c0b150140010f0348400700f4800f107100e035401421540410441850000c120701d107002d5800300600588240e5416158000040000044908507111080002441c041d20100d2440e03c004144032080d00400b1084030403c0c00c0104075607200d501c802c03440f81c041c0c0703200326a51501c0039402217a68404c8026603e05810040004801c280b80d1181100b920b5040c2c8a1000503122540d080c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 552391879 1250 552390629 552390659
    0x32407030605030a21230c0708030c030a170609070807050417060a0b010509030d030c020a1a15090712110d1e150302011b060b040e03040501140a09 65
    0x80145a41c44601040545060200222541c000c07001003030360114060302c404c840040c2800c40e00401c9a080510b9808401c0005606034440194a40648071800241003d007030200ea44e00c2002544800038401c8903058010014000c03000003134a0f081034401d0040f40c01200100210754069111407040300142c0c025000c0e4061039086038440c5040c900309516042c81c0c0c940752a594000100603071011003000000b2405005400360b0043c00c0ca0581e040a0117540800c0e66101111080014951100703241c8111030310030480700e108243c1043c1c1c440c131884560075400c8030100701034901408916080880e050f01d0309020b502103000d8511580c4080c0c8a1190750000001819021003000c400c490410400d18500c250b0f005520b10b010030303083c25007019100c0005980c100c510000481c41c1143d40310f0402c00142c1e13007040484c1c040e0800c01845040d0501d40f4070b050001458505101d9070f219161401051154500001600551f202038860014961070914680c0141c010691200300103182140305115014400e03d0304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 552393129 1250 552391879 552391891
    0x6060702060c0708030f04180b03190f080d14070201050609160c0503030106021f1119170f010501120501231504090903030b01030e0c0f0d08041e050324 67
    0x180c0c1e8401d03102c3c2044d030f0441e0300000f558041c41d0800b040501c4111600d0203c0783e04c0d01c0342540d0820070503203c02d0100381c43e492051003a401ca01c0d86c030381400341402071030040c0203100381c1c0c44044a592002e000c10b02c2c8005080342c8a0321035030f441060000642050051103024044d860040c02e401407980d928080b801c2508824490008003c448010000050310030000b42d40604000c0e000b40a4842d4241d500b40458441c1204400050333052804100c090b09040d0b088a0100e500c0700c042c034501410751307901507410f01c500b039913540c1d44a010320040011046c1c1442001e4140d502c00da0f1030091409a0a18600032755074280100c400d010a010711500a00c002030740301894414020f4804a070160003aa00c11445400691102040d2a2030f032644404055151044e48242c070404d08007008180000c800050356400810f8040c0d0242c802c040d10844c1e169120401312a09644c40a07544d540c0b5925030b1002001a15100c00f0780051207100c1001140c00d113070221301945403070504005100074082c0d0340b5500b01c1c500c2000c0c00c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 552394379 1250 552393129 552393133
    0x103060506010509040207060501031a0c0a0f0311120103050c0d0506360106030203060a0659060406060807030b06040f030f032c27100e06060306060702060c 69
    0x4d803032096102d6002a0100c903004050000d619031440c10000140032180c00103a00c18140201017004050f040c81c107175003491156142c85024820600d8041e0300804038990628000000403841d5210f461000c4001416a0f00c942c054442c14403250701844001416584010300c16041180020b020a1a02c000151806480c3e100c144c00000b00c0000c4041e0424100030920680c2d441d05414405c4d402c04000c0d464110b07807004001c000b600d2030702c2d03424008054500740711405d92030034a88030350905008207121140d080411482461200c3e51010542c001003203580c1c2000c0c0030f4450f0300014001d00d001d00c581011916982c2741d5400130b139035102048006000100b000ea510900c00d20001c980329090b0407508001d0341c807400b4014400d0b1214140a442c03503003d1210300300040600c9109001000d4560490150290142c92086503414010a00c40a00104020350404d05615200700702c0d0090212946400725100252000900c5c0c40e0201070006903c0304491268200e0400c1040c0710041c01c00a00901c40900d032041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 552395629 1250 552394379 552394387
    0x14030c180f04020c0a26030a0b0d1202010b032104052403070f2d0c050a1b060906020c0d020609040b03150a2f1b072606040b01030605060105 62
    0x40480c4c00841c5203103250340c0580751000401403264000c5188a403044900d40c84103520b106644410710004105d803010301d07103a8290313004d26110516800c28059001d0340234401320706400802402000b40660340c1c0c0c480d214421045034000340094003401480c11449040d8649402c001c24040411090b17806442060301d00d82d80c0006048607100598020080c50b0303501c40e0301c0e100c0100006c5c041701c441480c06000c000307440d03012103035511052075400c2c8958450908000350803070350a0050402c01d0328507000d401504100002807148581600352020340d003244c3c684411480e1a444102c0c2d83e10343c40710b03400b40c015001c1548000503103466000741c51819001007012030040e000c100071070700340340883c0b0b2040080c1c038004080c411516824000d0003c40c008644510b448601061400d1842d01c0318840d5000d1032040025101c403080b110981e0206200c030080c0300b15510703169100c1c54001c07505140390000540812284260000324004a2864021500140c3e11012a403c640340c00c030041c43c02420340c0741484030401c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 552396879 1250 552395629 552395659
    0x806030d030b0111070b0301091a0d0b070309020901090c08011a0f031503010f2702030303040f030302040e161709031e090301150509100602030a110a080c06040314030c18 75
    0x44c0f019140410f481d87c5c0742d51400400c00280c0d0324542004513641c10f8001c01a00685411102c03405550308010350200f41d49985030b05400030020740c00007035046104080080382c2c03206035802400304030f52503551700951680c0e1a08244c1d505200c20102030740700c58003081000c4108242c0c401071034001d03080751601c03900300881c50001380c00c48800e0300c5501c0003191502e1804200c0c440070009018068402c0300261445111940026241d01c40200020034599607242c00c4010f15201e41c0c140c601030250780c0311030720480c00d004000202d00b140c0d201e07040000a4460089000c030101400316680500c01c110015400d104184650321504c60140e44400803007807003444280d005903000d0080c1d1007818481a8000c0100d03003084240304030403034014803075a04441144c90403c6144d90000803035150007060300d0081100601c09107041e080610400c80641003480101e04c140e1480c0c0c0c007244040c0614030944841c940004100c5d007401007400129a402c50488081c000d01c12004944503c40b001040c0c001c1012440711090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 552398129 1250 552396879 552396883
    0x9160c14070f0e150f01020d140c0601030302060a0509010b15071410090201120e06060108041a04241a040f0f230109020403020a0311030a05060a0c020d0806030d030b0111 75
    0x5034041e240008050080c0509011309a032a10b41008059400c0e02c1940c8050300041d55504080b003220040142c000410140541e40e1003e48014068501c281d4205503564100290b8401054840303074645441e0001180c10035030140700f1001e8a444c0504440350070408051400340941041a09880c040080740d5065807041080c042040a011900300014a03000d0703600004044005c51200c400c1c1e01850700800d041881000100d0950140e824600319030035a41d6072901500c007141d24803840101400250503c0b0402201030300607003c24410015401ca1a1846c8400c04199094000c18034085c0510f40d000d075000342800d80202d0300300d80c24240082000c841e02c81126084458561044038100c00200001e0803486034150602d0040005c480300394101402c0d44c001030401c2140c1d100003407100503070400986098506224400d201c94000301559414a80004010040c000d0086010b00500404100f0840280100b00c59405924007400808146514840590080c1442254141408a00d14a00d206440c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 552399379 1250 552398129 552398159
    0x6040b0909062703090418080a03022701120c111b0a0602070b03060d020f03030d0608010b040225110603160e1002030a08070e0d0f0209160c1407 64
    0x700c100918451070300300d0000c0100d4140031610142c69284440d219941d1500106580e0700c403000f00c400140282d02e03806044030584050100400320300d4003044040c07005406501500d2000190012010281a0318818110780e8003040012804102c40051900c612036031a40043c4030a101410075213840100401c641c0c1c54819030400c4100c00c000c00003c04001c0c0d003404800c0c4002000750340020061242020110401400010143c40c020340001200f8410b640d1030060103a50400080e0940b90345054001d0304801801260003005041c0d0709100c0da00046050906c201c5640390514084200e001244102c02d052880d04400260380074004c40389a50f11640c1d400b401507001c0c1810389660080c40744280780140550544400861098251191024444d90084100c640c0000b451400900c260340d13560060b200700209414094000031130303040450402c441c040d01520320900842d83c0340401e584589103d100d0f4150304801000149074180001c0024221b610004041030302d18055852441e103e0b10441c0500417 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 552400629 1250 552399379 552399391
    0x81f08010614090103050718020d0c021006050901080c01050915042d0e04030804060f020d140c0304020d02060d0b040203040308041a0c0301150302090a060c030924030506040b09 78
    0x140d00c0808200d608682c41e0b08604030b660950302d80072258510380b41c040d210040c603c11501c402c0e131b130311000524a0324030354100c030a141401001041407050301d6030004d50711002c00300c1110980d4908440801c1619183d030701d403070403a04d00384001c0c80f91140300c60044400c0c2e00640901500424032207003c09680c030307000c400780c0040c101c1c1c240c10380c00e42c40d9044038130194546141755461802140100900018030a1207505074002d802d824082011b460382e00e8020014070b00710728100ba487d840403503a43c200106c00c0c0c05c24020081c01c070b4601455621181c2c0034401030312041e18025404015a16648010b00745000689522001d180c0300007803001c5000e000c1802d0b83d008032011070006481c2e4080004100890406404800003d000c6000d6841c2a01b5584550710060141c021458510341150f0743c801d2094040710400c4102800342e0814541d41c400142c1486803c03801280880c18a850124070305030000c125286030110001c6030031400030900001d400602d4003400950300503480d0400600c040d01c4000407240615 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 552401879 1250 552400629 552400631
    0x25031214250206070f0209010b0301030309030303090311070b030603160f1412010c031e0203041a06151603022a0607020a03060e0c2106010e0606070c030503130f15081f0801 76
    0x400349104102000405811027820701800340018004650710460040c242d03603150800146407003a40c14241d604503031250112800744160740d0f012a1103e0000007840c0582000c2d81181e00c15042c01c500707941c060076603000308070082030220000c020400320f802003002041c0c009041c0107404030445d80203500b9142a4009080401c0d00c54030350b90211400001d00d080d4024818908504504003a42d0700644440d00b240034028000404002c9070b010790313071007925084824412a10355075034071000003a1206948403000c01d901500a07c011000340d03030001c0304900081160383e4400b0034041c0707880c002c0004680125909a03005020180c021000404501c16000310030ae4000003004a01c003258100501030b5031a440b680e8400a0002e58850a408005949415100c5048100c4003542d62080420303a1806001da0140c41c581b1140c40c00418040044024080314400000c020241900c940d08904901c4403032266074804041241d0015099100c0c195040e08a0f8190740090303503152680040180300001c58001024030303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 552403129 1250 552401879 552401903
    0x80c03130503130f270b030115080a0b100e0a0905071518050307180b040f090b012d0905180708010f0f110a0f022503121425020607 58
    0x8072070103d6681c1d00070184a00020202c01c2417004038004400d000498030051900c400c04c1c8035059400307410005520850f4141031a016681c0e100c02c0b5501ca007656400c6e5a020820350110310301d400c482c0c048101f92006003007061056240e11424800801c412182a2228016030b00f010800c80c544004c07112090f1000d5071400d500030100309180301038041541c08644240d001000802c103c408083d5000035041c0002c90002d1042c4604001c20042d240c0c602e0800403030b600e0b0001c610100200d1602a5043e90100780f01d4020291004d030700040d403d001031403d220030400300c5004120740c5400341c210380d40c06035a183c9044904017042d440585000401d80003218980d44806811030920720612550803030b1900c1d0340080c40b41d90b4818803181100e12910315504100030850b2800120f00e8020004480c2c0c580000c15a41040d00c2c0002038464110390310300003248d00c2ea8070005503128442c410304500300103078a181c002502e85403004d0784107500341410754004c0d0b080c0b03400540b501c005a0340c0d0310068901c2c14001c5107504ca034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 552404379 1250 552403129 552403139
    0x90915070f08150306070302091306120516230d0c0801020408190c0b0a09030b0f0a0c03020c0601061d0303040b0a0905010516020d030e030303070207031104020901080c0313050313 79
    0x24030b8030043c241180002c146000380c030f0590340003c2ca01d8001005040059550b442c08020400c0c08139058541e880c3c0714101440051808258042c041c0c03410701810a0317841008000e070700d10301c0388070f0740f803180612020030306a0300c0c800016108054a030100c0c00411070a0ba81143d5982c540e040941640040030596004c20300b0400d644080c0f0164802d012040c080c0a4082c1059a441a000a80c2d0081d058000d0740851070340310860242c411340d006075030071502c01100380c40c3c4541039154090040ba5070104141c18443c038444464002e0003a02c0315150350303c000e03100720380c205031080742d01c0c10301d000303000210340082c0801500307a40b010310040000d0324001c4412650303030701d04a5028200c0011503004078108030081050300d84040f028107030004101da0494952f07566030100e09044601200300300d00254140000400c1c003440f560000b5520044034464400240c520540d401084203e004030950b0321b002c1881c0c0310000704061900030040d80e00ca028481440307404100b40c3c031090720319040341400b081d60940000003030203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 552405629 1250 552404379 552404387
    0x51509010f090206030f0c120c0c0c0d110d030909110c06060616060209040906061404050604060b0901200a052b050405040203092b1d0a05090915070f 66
    0x40c5040c0818072100c80d065000c01c0744e40c440200044504100c55010454484941040390702000803109a0740f1941013804143e801540540c911000714070500b803034001107003455080c1c1186250006d401c0c501e4424404140b04035050701410031810840c948a0100d403203a214403601d900100c4403502c2c2521108181d084a1400e900544840e10402c400d101d441130a1200140558619900641c05a1121280f0f40401c01522403031000502c1035044c5100858400c01d80885413164003000c88088c04141c0341c003014082200c469000d1540b450001b001001055400380c06900e95503500c4010308141d440016501a051010010040f1090b030001103041040705c02c1c00381c0e10304844141e01d01c45003440103c1c0c0d901a100744594032800e0701450b00800040c0e4000401c0c400324580c614500403820000103c0341020390609881c00744900487d00c103100d99040a0b4200440e031022041c040c00f6a450181860200603003020014801d15492203009000800d20700302800d95030040c06207884142c80345907240b1002d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 552406879 1250 552405629 552405641
    0x90b041b0903060608010506150a02160b0a1815031808030c04061202090109060c050a210207090209100c02060f1606050604090209040308070c060e0709060609080709110705150901 79
    0x1c161f0400d4280601c0d5130741d170394000e030b03a040d92003440c3c9a0700c003050744060381440c0030041ca00b0180a2034442c0080c410005000422641003241e0b140851a004800c1106d0740501d1402920104518661038450860013a8844102c0b07441d245040d86007200c050380d032a105540b0854000310030560100d000c205094201040340d072071000243c015414031002100080041d910f600c9041d04009800421605011090000309041170304500c00154000e0344496214020645404403001413161110026030310391244242d604000380102040d21100345002c08442514002e80140e070312075001c2015100003d14038006140c2c4101c128813512074003015003808404c540f4018943c500035800c14a004006a848a01d07550f40964142000320039600c0c1ca01d03048401c0d8942040c0104050b00e4103001c050300714400100c5404640070854248011600c80c0f0084814010510500716168040c1c5000c0c04041840c1c1c0000345000c440488541c00c1840030f440d01481d020b1402c20a143d900780300010b200a010081c0520 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 552408129 1250 552406879 552406889
    0xe010b0301150b07110d060c090f06260603070f0801141e0a0f0e100603052103010e0408090409030e011101180212070302030114100e060604090b041b09030606 70
    0x102c1e4514640588000144240b00f8010901c80c042d00d035071308075030351080c070700103c401d030800e01c1000481060940604003120368024000c00682907a000501760f48510101107200c800d00300031070800003944e003146200c4c42000e00720a5142c0603020021030090f51040c41ca2004061810000c40c140c0c0440c0c40400b174403007020700700c0e080070006c480c0340001c801400418103400c51440b100000c0d11048402e07444006200c0c40741044c0e024050307805242c1c40440d164102c5001d490240060382c1e0160a04040f600d04280c40d11042d84945d2810310041112940c0c0a03034481d4040c0c01000c4041c1b4122500000a00710b40b298503045021410081d121081741d40e00075600b2100c011700d4002000403003107070300c1201120418018002d21a854a1003511145602840010300555019000f4814080a0a01c6900c0240e042324203403070071003001c400015070014240f4103a0041202070400e524140c20126114054201040910303001521061840f1003e40605082148240345584460995003940b8100c8240c8030143d01c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 552409379 1250 552408129 552408161
    0x52e0201060b0f22140a150e0108090c030105100e070c0c05131107030c0b090316033203090f0102070b01120c080102270916050307120e010b0301 64
    0xd000452103401290040410102019150300400c0c40e100c941c207500000d0080803086603c0c000528105c0307201e000054401c1100c050781c80c02c0e115900c209540001c56038000024140d4100094154041c0619641150b2010107503011044044086400d5450542e04880d0b0051100720070003100554442045d04403c85180107c0c0c40d01f03c81d15405038502c4140105481184141e008003046503160f4010348000310721142540d103500c202d00b800307013a80c0e0071107501f5519a411080055030880e000f00844441c46010581820407050a807002c40c4c500380e03550070714036550144048191204071124200f00545000c5010250789203465040c00d8104a144034401440368010321881002800b41c412150650788003186c0c2d8100706041c4e0401c0b881d02440c5a2055916510002c5d60b074107030355260f0000e00d51400d03050f034440b20003040b0b081c1030085c1c40104841011110000c02e0582410521502c02144c2002c65881d0150b002019800382c1c05c202d680801800c2c94582d91503201000c0780c2020b01031240c0340c806440c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 552410629 1250 552409379 552409391
    0x50306040c02150109180f06200c0706200a12020f0304031e050102090a0306050a05010e04260415020a050d020304060f1119201e0105030a06052e0201 66
    0x1800c550709801030081080310340e03c44c4001b043c880481c0ca01120b14070741200c0c2c01581d0031400d0a00200030501c5050000d640b1440303402c810b580c01c80640840700740c003604a006201062510743d00b03c8070a408e0000b14240512128482054880d0801801d00c0f0140240804851040b011030081d103070a60015621403503410074032080012030f0f0203100302d020810600c442d8100d001c5c0146005030091003012501c9a10610700100070050083c0d41d81300f40c1c404c00e000d42c1c04102c1030340c031801500c6c07014608644c0101802c2070b0303000b115000001c68000307031a41c503042d03500103042c19114001c22100000c0c442c120b01c0164022500c0d6414414200450450300d64640040c52400381805030040841c07901000900911030140340070104444104950807001d103d2902114420710b041c90201d2101804140717034440801c000c4c00b005424a04460202040200020881c0001800b90019100781e0402826542c0300e41d070714500010141ca401c582c0f0786030b698007020141d4804142c60002c80d5682d4401c50039908580c9040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 552411879 1250 552410629 552410653
    0x9040c0315051c050607080a0f09020607020f22090b060a031112071a040312030e0316051504080304260a0c21110d02010b0d081c0c050306040c02 64
    0x1c1e00c1c1800303032001650004080858800041901070004800400a2060404100780b480e40301c0c0100340034000201c018480d150624140d1800e54020000c0a580140200b00c590018945440341605092002c1c010381c0c000c03004030100d0045c1c50285960f08081544a68801003041881100c0c180e0001c402c42d050000141580c94500341006140d007441d000300807400003600c6281c410070801000f00010b000300c141003c00145600c09903009840115080d640618840700b0441c02801107815042c1e83c41c00560420720303105680303040300c80b103244160768a006900c6e46200e00f1101a030110b1240c0d000e8402c90b039880c201031506064402566800d580a40c680002c0000c0183c1c8220444900320700303514250400030801c2c1800c0f580654044c40003040000100d0203003004135040201645016625000d40b03a02d001c900106074241c412a000c0303568000300d2840c24000248048015203d40c01c01484010782c1c1e02c001c0c00420b02114402d0a88201207080802040751358642400340009801e00b40c400f500005980e6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 552413129 1250 552411879 552411911
    0x601020d052104020d0506010303034b02070c032907020604080706061203120c03021303020d06111602041d0a0b06042c060c03130308041506080309040c03 68
    0x555210318100032100820f00795526910b50b4030500741c0003400e84800d96541d10300a0700a100c400b6152801140040b0034207030791060003051403447d9031104445a501070340180900320031514103400d42c0060b45c1c2030005002013290444035901541c07161030800501c42081107202e140c2d40c18a900032a417007003c03100b0842c4050707000c00e000d034002d81e022004640b60301a03403a180014101c180c0014503010440c010364070a25902640c140301180311000c00304840042154100c0691203121644030400188039010070040c10103c907400c620782c2c02260001442d501c0c0300d031b540d80303184d0100395103144051480075500f0075890280b007110940d0100707403040e00c1301415103920141c42c0c2942070070141112b0308a1000910907203c981100307001c502c10192803491201070b50f1000c43d95450317030101810b45120350320000303035034407070140c00c4070b000c3e808040340146070446994040700c0c0307210010000c42d40d8040215103d409014103000f0407010b00149030207181c0703801a50003400200d40e0010450307403c06082c84a81215810700c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 552414379 1250 552413129 552413167
    0x60b0403121d13050f150a0b0d0f06320a0608100306050c1b010507051b01061e0e07090501120e03071403070c120218180111030601020d05 61
    0xd80d08108020104481c02d691010412882a94001c145800380c2d030058030f0076500036407081000e20f00e102c56a07151084031503000c81c0300340c440341c1d00070b00300a0050081501e0103020f418401400700c0d01256108182501c2402d4860740e42c446041000e2071694500c501a541c00070303103450001044503c1c1c080351700c04002082d13200c0c640300d40e00c284220100032400310039000020030b02560b0801403e200e1800c200780030003020b5003c44100104000700c0103801e50201410700500e0300401040c2e03111402d0403030308082100c4155800c3c00061196503102800512001c40c02c00c1c3c00d080310480047c0d840c02d44e180840d42441684014048010000d2055041c0301907a001402070a1002a004001489003035440301c3c40d02d14804c140e800360518035201c41e502c01c000300000041c10703054420403a1b080010350302d41c0244480c0050315002944043c0011854000b01340c0d41c44240da00000914000101e4020403013030310308440d00d28070f0310344201030b00000b040240d503010004065109540d140081c94200020300305520781710 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 552415629 1250 552414379 552414413
    0x1503100b180a08030a0e0303070f06020a110601060f0f03050702061812031305120c0d030b0a240905010c032a080c060a1a030c1002120406030f060b0403 67
    0x310115aa968100e5401c030044180840603102c201003075291400e91340c0d44d410a40c0000d0000340750002c003079524200801a1641550b201c02042600c00c000d5480078060341202074000200000003a16684100342048078034000c000d561107410001490312001004074103100c058500740742c20301c0203001549078001501d55120300e15071000030304d0101c3c0704015400d000001c035031a89292808420b01110100300030300c021849108400321040003189800801c0071b40280740f140c00355a04004480e01d076a5020f50800c1e031500c1c8000745520b04d003e80798402c20000015808400c101294000da803c120990002210300c0500405d00301685658566a0000c0020750204000e40022141c1d11580201d100c404844002980c0d00000c01500c0303880740703410350b030351103500f101c6407481d43e410505001daa0269550f0f4016003690090081e050300c003100c1c01403061070940d90201400318400d45000003915821203002c0d001910345690042500c1c0040c070403c0302680e800c0c0d00081e00c10001040f040000906c840441240c20b2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 552416879 1250 552415629 552415649
    0x7050a020c09070522150912080c03090a090b0103050601090f03080c0c10020f060a0902060f0a0c020618030c0306070f1d03010903120c090f14040209041802150310 72
    0x250b111141121613005500c090380003e064000982d00b41c1742d2040d4610306a500b0354140809680101e4001c8a0409082c89100110b085c118803000118805000900c03030b8050502c00c8a1800c02441d0108000c907000794030030450300b40d441c0025035096a0600410ba044502440c000800f01d080150000c0309008900c00207001c4080010500da07050010701800350440001020090000c00b09000a912152828107a460b1b5000318000500000b5581c421002c0707485d00a0300707181c2071002c1c1c6900200190302a03109103042c0f1080c56014070050707640f00001c10514540d605211246050202450300c0c0040302083d1911a0b0021001c0000c601d40c02028088184254504881080c61401c4588040e00c01c6202c525015420007040c3c070141500000c0c0310503140f90803001040707654a0460704a454030518003950104041c1d02070100036401e0a207007a40d420b020b00420040c85c100101c000030b81212140f64412100c0049402c204041d445d0900b113074008011442d94441c90341ca8604d8401d141d03500c0901400343d0311 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 552418129 1250 552416879 552416881
    0xb03010e06040605032e050403050405091b04140f030d030b040617062703130f080d0e01030c0e1e040621020411160606140627040b0a0b0a020607050a020c09 69
    0x3a290720f65006d42d269250703410040c505207800d0007080d691003405914010300d03060020500d43d11040200705a100204802c2c10308282c00e00e0380d50600c0031031050125501c0b0003150030001a41d0b8061001d5000c4003025100095030001400500c0240c94050b401510112100003080c1c40802e070104100d54420000816041e9180f2130070101013201c101d0388041801c038440841c0300e4601e00c01000c208000c0e100c01542d00c09805541d074035040d40c0c0710b12148001d0300280b401c0440a1165000e0b0700820000100b9042038009110081d022a481000300c400101201d070610a4102e540c2c00c0c10b11440303002d00308085910600c00000c00c2e1420795480300c1400240600d6989030b0a1108071165820358030010740ba02d00c1c4000740380590800f0005070146016018405d5504c03440c2d000d01e843e01e041195095402107400403e5a0440380d007402c0042c024600c0c40d50050f48801d4043c526641d09031060010300b11001d110f580310251030b00c000b4a046002051b54051003820014400201c5e0002182c10b5200c07000c961086032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 552419379 1250 552418129 552418183
    0x31b0301021303060b0102010b2205180111070b0a02030705030c0309070e07020c030c0108190b03070b0f03091b151e21100303080708040302160b03010e0604060503 72
    0x20b11403000c101c201003414481c080204142d58200c00a202c100b68000c0c00383c0e0021800300310f28404601140c44110300c11994410b60211240c0003280c0c451011100140035031410400d003400d4440740c50b80031b545a640080d2840030452840b0000340c001c0840042141585041d030750141081c84090446681108040005001e240702000b1000141c1400c44054615042102001e0750ba06150107100d031203806454440c80081d4859550127200e180302800740500784600020040040c038000110380d40502490718045907002122000b0180d0f029460040c903502d10344140403034100f444102c4040070905070003268101e265600b150903542503075120481907441c0b21540408a04815046a034060084d0208842d50600e04540759290b000b1140c02d89041c0c143d98044284815215501005003c00c0d05000411445441001e1180e8000d00c64011107540d409002a607101da14505d9001a181c000004014842c440d03510384001e400203010b40701403103402d0824000a40301c1040ca170403070500313004c5201d04083d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 552420629 1250 552419379 552419381
    0x6020606010c21120f0e0d0c0f1e050d03050c0702100e0916030b010206090a030f111b0f01020a1709011202031503190f030819021308010b0d02031b0301 67
    0xc1403400f00c070601d40f000d4141e03440190040500d44100e40445180c4601e4803000711190049080d182d03101c5019001c1e50007040000d40f070f810107000003a40c07164035140e06900000c003001884002000da90718041071401d43c0d480d140740b904600300c00150826080c80e06100815400c00107850f980f5034100c80c000d202104150044030f1840810060581c0b01c0c07044010300075100d4242c04041a642c000c0d540a00120030500010790741e401d400c0c0c0392902141d010003903090100307100d0010b9071190641071500e201c1c40051400414a84152480409010080c20401d800d080c44d21802181c0d8502c001c2c00580320920094a40101d2a08041c103840101d480c0007e541e08543e2054245040020f030341e4108544908010269266040c42c2c102d40c9030007031107141201c0e401d010f11840d43c07810695020016004010040d6400c0720400c8000d40042e0740d5585c1100c000560044900140c000030081d11644240245040c0041d425146040c4803680500c2e200b80090000d41c601040c041c407055508151130505182031400f1034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 552421879 1250 552420629 552420653
    0xc10021b0d1505250c020a0905060f031c091401050a120e011103040b06150f070807060204121101030608100504080d0912140f03070324141906020606010c 68
    0x34032000e26100404c28a400d52003101490b80c48515502c80380b6000c404002c0e2001990003e010750300c0403080004024580300ca410190b4000406010081c00b001840042403500f060340c201115481c01082c030100b001540500e00b0001088451b025180c1040c251001a141d0301c540c0356071008000c01c0c041c1012100489030842d0140407040d1f4020018200f0189115000790002c3d00c0855940e41e031600466001c1c54084010b80c4001c0102c902146805103025010800e5840b02e0821100e0620900c41007002c5085403001e8002450302e5030585025180c9031074008904045084094141464801d00b071000220010700c0485a04035844005629225800d020819000703100800e000301e41085048801c00c42800b00d542d415584503141c200d0b80c05528503110b100c500800c0c0b40f44610a405000240c1018440d80001030610600103030b140100c1202c400c800103c0240d41c01c01c4d450300c91380c2e1a2198032410040000d025961710344603030780c1059003031204c0203443d9036028004c00d0400044103030010034458084121 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 552423129 1250 552421879 552421913
    0x6030c260c10111216170304020a050d15060f0612270503090607050705120a030806010e12010504080a110304030506070503091c0906030e0307030e040f021b0c10021b0d 74
    0xa62100b94105d02e00004041059084030010511145800704a1a92043c0c0c0e005070b41c0240799031101030401c0d05000b100402d000702610300e001261b03004a04100207219600142122a44c3d00c680c0604200000e0901044010741e03040040c904070201e0034612800d6090699a80400d402d088242e545040245c07860144600c9954407080000d950000c0100c0020850201c03003044c0c0d8641004003a000425460f005c4002000c0c0100b60400000b44080d0f04c01c0c1c001c4441140010710810b041d42040c504203084810484080768a8880014404009034211402c01e10458252008600d09400d40c0e5541c1d4441c07801900d070b48103000020011a941c603070184001d606543c03032242d00a81224100700e00500c00303811880b508000c80d00c3c1000d03400f81480f000c02128941ca815407a409100714846040c080188094044481c405600303114541e809d1076000851000214500c00a0a01004500c208001100d0202148081d9072080680d03111800405950180e201d40407240c1613840ba115042c40030104000b82c030f41b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 552424379 1250 552423129 552423163
    0xf160c08031005040c022e110c01150f08031b0109050609010b09060105071110090f0303020703060b030106150e010504030c030311011d070504020c0106030c260c1011 73
    0x10814194040c00b8031008507441140d003407200340c10349030080e81c0700c841030000c018800303640103207446041c803020000001c03449400f0800510031080011100040c4c10003071402a03170740d44810083c0441001c81c8038031405010003410781c400b26031030007403607940d02e202d064400e16491203081e03400d8030300309400c0d4051500c103900700b0103441c41480e24501150007041c03001e4070b0500c00d000d1840070030101c0d442141a0348540754014241d03000206d24004200416404586600400062400100340c11b8540840030000714441c0d00117010440c194508601680c0da8051141e001c1d0303150030020461f003185008602c04d401b1440c00e0103c22034001f4030040f1054800c580000d840c800413a94000101640304c084111400301c1140204400c13912aa40340d100c01c0e5184034618050f501025007800989415402460203000b2203000107010b680d20364806040510b183e02065034165900b141c00d200d4440841503102041020000d0041d00025800083c0b0400c0c48440ca4010031000c495000074100d41040046044842065 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 552425629 1250 552424379 552424381
    0x61b060b04110708071509020108370b090a0209010c020d151419050103021012060806070e0a06020601050307260f100f05010b0405060c031b0c01080f0f160c0803 71
    0x502c4c0036140e10202003115602c1012050948030030301c1c1e214891865a0594070030b00103841e0942e00750650741d12008080d00074007a0200c07003900307182c01c1c11130960304220300080030544802903001c100c0c2c2d140c40100959840d0b40104144003d90703038000350030308103240d04441c201121452400c05081d003811164034096202c0c0750081005035510502001d41c85006039408031301c81e64aa0042e030b40d0941d00203100081d005203101e00c08129160040d042400d2250540f84009045030781c0f80989450103106540c01c201240ea8090480e60750306010150300040c207164001011994540303008a56500080e102d0010180c80b500050a25038074400d0a030281c4a416404490705940045449615030404440d4032484520f0128540d000b80700310f000d1030381254441011181070500d070400744401c640c0454521190740c0420030580c47d001d000c0c5158550f464502e030000b0600b40c5007090000d401c51b030001d00492203103400e034000c01001000320500b496001996010394603822a031024141c0b4215031034000141a07001c048 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 552426879 1250 552425629 552425633
    0x306180702030409230a09020d150b0a030c0807050901030b0601120e030a0e0901090b09012d0b0909010f0b0702121c0e090f04030c0803061503160306061b060b041107 73
    0x19400e4000443d448002c5c440c1e032074550f221004c41d6083c0c2e40c02500040d824620001003507140c1c4041030351000d40e04000c80d449501000190480c0525041264084400c00003840789400421241014000545010800e0b50558648041805000700300074100140903100b58007056503900800f6007141400b0031a0389582c0061000f8058151f031403411801120160000207101d4518003446e20300b2000035101140a034241000409503800102c82c000c400507404001c0750610013040d0300c42c00105130503062075446200000c1041030700e68041e80030f44550344003100e090002c482000b0803220340c3c50b0704854600e00c25090006860a185100142c0200c1d4210052400112508022110500c80003280c044a542e65540b0354401c5100064801a002504601e43c0320005417210008580080c0e0003042c50642c2d1340b141500e6407483e8021600b01c8e01c043d2850890319281074050103808087c10702401d2142100000e6204440050a0b4100203031035291150121040c070f850b507500c406c00c0034110035a4580e8904140c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 552428129 1250 552426879 552426911
    0x60c02060a0510061d190803041a030105150a090305060109060602010f0c02030405010810030f03031a01020a150903091203020304080714011e17090d140306180702030409 75
    0x201c0c0d611a5060810780000c081e0910f281c0098241c034016104c503101c1e07800c0b514540621000380759405400911045030f01040014110904009002c20002917903250b007040c0600c000903640000da81c010340340510043c0659600c0d10702c00ea48801d022440f9988a4011040446141c84242e001a08a00400001140413030300c580060040d51300340c4e0001d01034004006d141e07608951040d440840180c000f03220a0180d98030440d403158100c1c0c00320542a407025280d40f948a18158070341c00440100ea980c0e40e06501c0c02581c81c01c4002804030900150002240d00e0311880500e08460740e400760003580d40ca00c5401010700a00641c005488000941c982140d020714001e50789a1080c01419003610a200c3c0c005001e90380324403640f0040d001a915030400c1c0e06100e07025110707031070980d9159052003040800780c05c540d03507125455846000303420001c2c5030440100c0805800941d0079043c0c6800e50204108110310380d1140c150107030015070548c0c80d112469542e20302c02c034150b00807038201c800160304080e80e4040d841c6103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 552429379 1250 552428129 552428131
    0x80d090b060f1f0f050408030406020105060f040c020c040b193f0f0204092901080a02030c0d1a0403020f0d080603150403230c0c0405040519050307060c0206 69
    0x1998914030021400c01000380c5842e041d1020280c803118020303c2282288101d807000d0441030a424024141034071b61183d42d055800540240005039500c90800c1824689241919007944003528100070812402c203000b5203d40c0900a040d0155480701e502c204151500449d5070b04400012038001022911003000d4421102d145420703101040c5040d00c420503042c00c10a0340d400d80c59491039950800c1030942d6519040391402d0900781d0b4081e40d1180c20002186403925480790840c54101d420880a180e000102050041078002c10f140d0fa0040c0340c2400180c80004103448861411205040c100f401803a25045030b00c0721103d0a0030105186043c8010940c00246418000340c0c00e8042d5689980d282c1021901e014046900700c0d456880400c50860700c0320707480c0990350814000d240403c80d030750070380c0003004640c0c0540b6480a8501000540105100300500c500c0c1c5941c2011613081c4018105601c40f15500c900081510b19100440b40c90a410410100101d0b0001540304009000042c1302510103901c1d40d42c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 552430629 1250 552429379 552429391
    0x9020f060a020717010c020604030f170a05061014040b0f09060403030206220b010902071b060e010206150108041203090f11010315230105161437080d090b 68
    0x138100c581d07074034650010700401d181a22650300034a02507031151811038038050442e940d20700b840000c20140c4064040200c0440c4140c2e1284004651403e240060150b04480e811414081102ca454440d0300507209d0003c075400c40d40780c0f1103c9610f5900c03071100090303184030780054168002c0000800004140e00826518030609003200c440314917010b82283c050441011081c010310000105005020005403507001d00101401031b0340d1103469015a0312200c843d107942d9082000414410140c1201c6c5681c1081040d500003c00d500603231421001800181160401520080c0050310078040c0d041c00a00c0390340080003040d00286138040040003400d203c4c00b500b110700c0703242c1d0020317040421489440c42c50098403003c49414003660b480055100411380c601164030003000341040010031805a4101c002880d098000e030044d403980e550362450350900c0386045011054045564085400b00c0c181050309017041c4c070075208000340d114130207500d40340a0986100b41c02003480300034685002e4509100094054070b1040e9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 552431879 1250 552430629 552430649
    0x60f27130203010602070b0a03020d1505040c0504050306061c240501060e03100f0b130c09050913030e0f040905010501090b181501090e0903130b0c03030a09020f060a0207 75
    0x100d505041a0241e1109028400140c0d000c00c0c0c007004800500d800030030810320f25280060412450b2802e190903144d2212480c0c01d25010351009200501d024800d160401c5000d0909500e0949408042610b03400c0090032140310352034000f00f00311383d102100158419558450080051010307484590309040000201441e8800e10b880004103640780035102c82e9018010044c001d01d40c0301444480040503110749060580f02c241c4820f840991078480c42060000e140c50002c010984510b04c00c001003c01400d80d10482c03054800b4401c5c0104081d00c41e0280400a40502d44000300883c90008504403000c1c3c86101c9401500e024810b400b03201041d0300c014161340c14040c05003c2440030b0010070041e140054000040c10410102188400c1d44c060384003030f000320042c1070410381503544038222420781c3d004484d0060a071f040001c240c43c200da2005403403130203427004400c100d04040d440c0003565030741d010003040e641043e5a07410441c0309560703903003046000c07440c0000d050350b070f4448451500030b40310042442094070407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 552433129 1250 552431879 552431899
    0x51005090c060702010507060b0301020d09081b070f0315020f0403050d0e0102060c040509090703050307051501122f0303040801020a08010e04020603040206031f170c0915060f27 78
    0xd00d0514103c40c840c68050351520305005454460000500c2182d1406e581994204038020180e00c081c010602524042c500340303621507840b010087c0309002004600303c055000000c05119041200c2d48100550f40c00000b0250f5400d4010040d01c002c6c4611035884541c010081400000c0060016429500c1003842c0d0b030700282040300000580e501d01b419901c003107500300e0600c000e1103a42014080c07154484403400441d0b898644c1c0343c03291402d55104010684003070304200329a03c40e00c0103030000703a0300510750b10100c2c002c0c060990b1501086c0040c940406080c0d4034094a80702f43c2110b8034002001081c1d0018143c030354559543c62070500170740c0a2041c0790040356084000148403c03540500714415500038010520b1643c4582c20800c0c0c80e40300030a8048800c2c1340c0010540480d070181404405805201c800380c846103600c4109034917010501920a1040250000308001c9550070004250381d03000a072005510782c0000303240c6050310701403440b99613104551402d068407811000f841d43c00c0c00900c240c41070b5040f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 552434379 1250 552433129 552433153
    0x306120c080d08061e010c0206030103061416080a0209030c1504090b01080c0a08061c0c03060e0c0a03110f090405010204060311040608060603062205071404060c020906010c05100509 80
    0x401a045503038a0303000c130194017004004800300d14aa034400c80c1c14944241001d0180e400a96560000c0c4c005441c042d6540c05c6032450301c0e1441d0803c0381c05c19076441403580c0810007113400401d841001041408910f802042c6107210751020408002008401401c0c000b09100108106555070000d1040b03003030b8a82840d00c044445e50081000c940116034800710319152400380300e815507100c040649010780201c91081c244411145142c6a881164070400c801d940807465810110103131292184544030a401809001c05d155590b5030512040341e030300007150040d1900075000105802140034580d604910090204803c001e010b5008009550b100d89081040419070f4101144034001e038003520300802c00000c007040f141e243c01000f40da0710500c018091088801d0f801000c10440213003043c3c180d5003d48807400e000726260051350511000c02d915a601c2e040a14104008100100d503072006805040d082010901c0ca921a00d18020f0701030f005800c48094100a955490007003500b141c03404000c3c01a04000c0340d07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 552435629 1250 552434379 552434387
    0x5180315071e02060f04031704030903060b0906180a0e0307080702042f132103090611030a11010e0708160b0a08150406031203020d050a090b0f070306120c080d 70
    0x100303022190340140450303502c5840f074980309170020b002a8140406ca40120210714819410144164031039540e101c0550b2451070101c0030340700e030340c4205846601c822040140c19111344295511645081c0071003055615000001e10003040e1060b229410360100052403020b110703102c4001d01c41c0030b10030f54082080d0500e41024131f00101c0c0c0501104000c0390b00d41660b48540f01d240b4044c01102c00c072440c0403542103680c3c00c00c0d81444240e10720390b04a0002da40e4010b109040c0c128032703458000e041909040c91044003198285440348605100c000511078040c080030740842007503202003207441100048650180d200c840c126a515480b140388404510005400b29409040e102640e81510343c9896004150b1210a03c0b0601c950002203041d4003d070350707031500101050300760700086502061a100142e1300c80d054200001600c1e070060111400c80e080014407000142c056030050703800101c02210981c65220f41d4030480107010305510900842010b441107406005000782003004640c1c0e0402107440c42c8029840a80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 552436879 1250 552435629 552435677
    0x1b080f030c0c010c051c170703090809060d02040b03010905090d05120402010f020f0115050f0d0b0a0b1f031e0c1e020f1609110408030403030518031507 67
    0x2410340d80207000302d00100c0d4014a14075a000307101d401a94001038a20201c0419074a6220b4200009000104424032258240c0c0259401c4a040d02d41403225900c40d4540036914440d04a44601a00b030001c0c82c030160f0b243ca5030540740500803000d5865a41e5035514403690191106607a035103d580a0195800d00982c064003c0b60b0030295118a29801c03550346800540c0d2590020a5000030b600034440350403507001d42880340560700545010424a55820401404042e0450032182400b645844035298041140c0032542540100702c0f480114200202d003000c0392000c0004100e540d841401c1d503640011503901900440004500005040e800c3ca420441407410b07138140704601404205143d600b4400c00c1007113a00c030341c41801c0e6801203d20720548000064900488502d5940e0080c040e804107109a402d5400703000d541c042801c2d00241041d040182242d102d01c682e200003800e020740022000414a50003001510840d4014133545180c40d004040810310142290090001380900381c1100e04a100c0810308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 552438129 1250 552436879 552436897
    0x906080613120e090907030308011a0d0507050942071103281b1a090a05090f04060509070f030609081315090807050603060f0a031b080f03 61
    0x4a4090040c645500d422158400120400c10580d100e0307110300c1d80c03a0210924042d424175401441c64500c1e41c02d000f0000d81c0d040c0c012001c1050760250f2240fa08042e40d09030b440381141e040001038281c541c0e5200392803910403141155040711a244a41d0b280d548400764a1700510040c12019507441007020348134103211081682803a180100303004020100b0501804002c280101070200d403a2214015181e84030464000c0142062460b0144038004100c41c140048883c004020f01040c545070078050f59040300da5118264202d802c201144290311236a030211840000e00c1c0c040c00311021420b20b03080c42007007841c0486081d20000c0c2400046186c00000244030710480d41744a0504251a085a5446000d0101c4100550322040c0c28400c1100d44070140341c4003401820102d210b815036240c0719201070034400c015406494250080d02041110762141022298415002ca49009070300c50305000003080e43c5405e410240c8410700b042c00c3e107514600209801800d40d003482084801c0303d08003c458581c0c0e44154110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 552439379 1250 552438129 552438151
    0x100e100f030b060307050603150f03120301050d240204061803050c130609020301060f1107030302190201120e010209151602040e0a06020a030c08090a030f20030304080409060806 78
    0x7040402d45030319086070002002015504100e58800004440d44c209952400034026501c0c000a002d1420a40c202e00b0b60388150b0140110108075843c050850005105442c0584000c0d590301c000c2202d403100202c48883c9a0110f140d0440b086008070b40290813070f000c1d040108050421420f4441e5610a4800440e0752140c014605501401c00344004c070150034140b20621600c0b240045a90806400074502034030070355440c2445507134001c41c020301030220141a15816003051000f1300200350b0104461950200c03031765032500d610415100491303403c100880000c3d4005c0c5029580c1d11148019001010254400c46116404402c950000c9403035114002d0a80d480c80d0480640c4801800d00390005294031074990155402001c298548a007a64404092040003a540d08031440e801600405040c0e0403151840061060741c4040d9006084105050b2465041c800001c00790b281c04110300c03600c80d21400300001640d4072070503c3c0c54610035942240c052400c00d9030070100c000c10780c0400001c1040c41600d42d210 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 552440629 1250 552439379 552439409
    0x509040b0118090c090504030201232805090606030c010921050307020909060403140c0303280e03040e07020c0102030a050a0315030308040204111c0e07030506100e10 73
    0x801c0d0140c0d14800460110294940194a010071035440341e40d0010807a03580c5c0071030580707001d241c0282114403a40ea010b1444400640346880380142a03119644416280c086122129041410000880002e40410211400c0004000303800c4d80200344540141001d4085502000e030000040d20f04401c280241c1d001c01c0c45c4034100c0c000a00d404410032032107501940949260503519004111008802c50f64800d895010780140001c00d6844840382c0c140780d4400c3c0c0444c0c100540b920403ea1240300280001030744d9403001200c0905c0c40f21508101482c0c9840204c1007000c400303640e00c03240d01d0f90000d101340c40b04644044005003000380041b401d803e101070140c0c0954a02862004150380c190003010041d410595100c1410310851251a13100010f54065101c8808501d0140b041005070f542201e0264680301d001e000b02d0080342e41400700160100040714000c40c00d02c3d1318009840c9044200d82c00540640300750001e029135550340c0c804100c2030301c2280402c0d040540e514010a20604510b100355015000c4800d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 552441879 1250 552440629 552440639
    0x10602030906090f062a1213090c110118051204060f0503091c080603010f15230901090207051b13091e120f08040209060d050312040f0c0509040b01 65
    0x10031051001e442c000c10340360900d6a14401c550041810140e0058406021b0720480d000c00070406c0f1416070410301c510020315001d07001d41c1d04c200d0443c1034480c83e20304986170349400141c3e500030b40745001508413540003000448040244c035a180c400c5004180d429000300c0e00c0500120300301008440a945958440c50b4541d00d2000c401c442c55440240410741700d01405030117040c100002d209400c038522a9650300041414003104043c219041110802d00e490f180c00e5800840c101003100744000c48414017007517031120660902104d9800815486203500c500c10b240041040d4885601030b1601500940898228038601c07007641a00680b000c500c1c5900401008103e42c0e0741d41e581d000b442204e84525200b19a40c071910821001e80480d8100c01c5606020041800c0d4603258001c2241c40b84050341c7c039107031945087ca5004215034130380c09031041d4000c1030b815402c42e003030000c2082141e108014100c1e00e5211407815051061002c0c0300c070417085445000d5160005424588900c410303002d1a004404c20714947d284c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 552443129 1250 552441879 552441889
    0xf0a0b06210703031b0501090302071508100b0310210309050d0c050f06160c0501021209130f0204030203030304110a05181f1a030f0c040602030f070804050a0b1201060203090609 78
    0x54803002c21179141c00400c10000500070b010320501030f44281c0040a5460406201c04c102c01c1d64001548100300f18a010881154980e0142d04201d450712241c041c1e40b9110010030086c2d9002d150001841c003071522102d81c1d0740c1c0d4503280c213250a0324000c1d0348403f201c5480f942040104140440090141d180c031081c144441c0c035140e1254414202c005200341d14124166070b500342848103118041e200245140740820141d6010f124030620b61891900c00341c6008104d600081027840c2c000540a6130340e965440c41c4d811000540e04a402558005007203d41728500707858035030455003400e0381c2e45008a4010030001020308107600740d8101c2c560110320000c000d6440040255a034200344214800c01c40e80c080e00013902d42080c0c109028094801103c0c40e0b9240f038600e00d0919009005003a041110b00100801c011840d03000c8240c8400c0d0116901042c1d855045040008070781c0500e401881c3d0007005202c000a070303503c05100410f86821810707004802070baa80e0b1800e030303168020b030801c0541100d020041c1401902d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 552444379 1250 552443129 552443147
    0x5091606030b180c0304110307120f26071209031101050c15010801022203080403240f060303030506010e01080109020d0e0f0724050f09030f0a0b0621070303 69
    0x50011410003100c0a6024040715041d00d041481944c0002840f01340102600d240c0d0b801e60003a0000c0c50264913101c505612082c1112018028001c0d030007802042100c00c045100ba100c04030441c0106c040d01407a43c02d1550b40c00284100c3d412910750703226122030350103218503070216904002e52450f803001c0c050041d1565440100340310401d018182c45403000107503600500303010f44008000140c0700c0401145900340880c1c288854005243e20701420000108881c0072242901d0340451000203d0700d6800e21034000318020288044c000d420a0072401d0f21003419803007034080302c4c0a95018005038482c0360055500401000d0700600041a101c0180521f818a400516400700c2e0800f0008810154402c21801c041c0307a08204100c1c2c0e0421001003100218450004040c01505000c203140c54805071000b0b0114440e090b03c548101ca00440c170005150b4041c8150701c101c00044003900c0c82c5d0750080c680750040003000c40740c0038031980100c00e501990f4140c1c084404c1c9600101001000c00c0e50035a1000e6900c3c600d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 552445629 1250 552444379 552444401
    0x6052203021e0c090f100902071115281403060d080f0906040b040f1505070b0615211501050405040906020708040b040f0b0c1525120509160603 63
    0x4034201c43d5407080e894400d580b5100e00c00b90f44140295040c1500d0680c4034280030f911140c010b82c01401440041440c05c076003120403210494444910026103800e5001a026040442c100031003507400c00030002503c80108a41801c05584003295140c90350301d24241d41c001a1403440c1c00144401ca000c00294090f0010042c003004612000d041800c2140002c2c031541c40b03030f040302d82000004607041003010702d2418100040c1c10284840c0d00740300d0610000424902500d0009001d052445021440d561500740521001010400c00c40344c4d00c0c5c0411003030300d05190001e502c04101b03000b0360000948090b00f0582c1c0c4400703001d059403000c0c41c082ca07000801019060b580015580c06038204640c000103000c8000a10040070082d084a844a207040716440c480704ea20351001098000c1040740f10704000c4085240100c4c01c030f8a10050740207803a0400c10701d011451081c1602440211282100d080e030b5004040600780480e5401e0a00496507580f040588600311209400040074514906008080c0260824030f40310f1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 552446879 1250 552445629 552445633
    0x1503051e0916060c02030d080705030a05060d020406060203030f0108060601021e0c06031602070602010207150903090503030a12241a0c150a1409060c220306052203021e 74
    0x4102142d40d001992156403140010800c3e4041050840c1800e01c054219440b2500380400c892802400242842c80001d00c0b801c01e00760348078000740d203a079508603440582c250003900401a0f00c1c0c0710b01010750b482d80140d0b491344213440d689000141501c8001b8a25104004c1030740070b0070220240103541d035400070b20700030324000600668092203802d860f200301440c411015039680d525a2404048084e050900c541c105008690042101501003110b0012014850100702000111010542401c0300c500000350080790381030100140d8040300540c800b6070003c0c810134002d02000b00080e4108600c1c81840d10100e00c649081d80440c041240c0e1a415011540c0010300a41681c64180041c83c803e080c404414220384c6900140828031190780c46c24030801060460503d00c101d0641043c207280c0c0c0c0e50340b00003001090360010015031180003e202090003420403400c1051101301c50b40303a10b0b1030405040c0841d04440503249400c1e100b1641c0c49805104110950181c0282880d126042820585030200d4001c1f800d0758 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 552448129 1250 552446879 552446893
    0x90302010f051e070206091902180c0c070906050f04021315030f050906090703081c06080d1407030e0103050c1903060503070609140402031308030a061503051e09 71
    0x80e070007101d200300300081140208070090f4040145151002d0081400c640c40502002808000040c1500750f044c400d00d007614a806c03861000820381c1c8071840c6051030031080d850a00561a651401500914080c01e041c2e0b00601c0d203608081c412510369100342a0b0000460462808600301540101810184001c4ca458420345a0087c0d400711900900280c0000759581480c103a101c146104103904100254042d1000b0f0420700c01d1250b65180601018105000c00070b6103400502d1400b001c4403011100745000d101c02c40d41c40d0401511050302c10342c2c1d00b010070f8001403000803605020f011a1000e030390586800b03104440d903000440040c1170007808074240c5d180400c5080d440f1071b24954064030207049a5000b046003424030090600303004140d4011410310000b45400e01103803004001d5103072000015240140c0300d80e2000d80720301d50042e01d180c0c00382000f64004148541700031141c1181c4103488141c80712240121100d00200d0856034210b500e002e95004006104185050301e8005942154603203040f01c0f05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 552449379 1250 552448129 552448151
    0x6020f1f020c07031406060406050108061f050405101107050108040b010306050a1107050f1b0a1a1b0304061d0a060c0f1506030b01050306151201020d0c03050612070605090409030201 80
    0x2a01424040017103603038403000c00c0009525080c016007010300420301e424000c904100c0c002c130b1240726154910f49901001c2c07500302850390b403007582902d00601004000b094070201d10710001c4d0580d11405e1640c0828082c048020445500406c02d15000d035038005509000b613860350f2254401030034040d2990400e1515a0701c05404600284050025180034401401e6013031110400b0320300d04224402640021900c40b0139229207555100c240000b02c070060407145c00106202001c501d076601c80d18040f0b034080307652681180014800040070f0b00c01c0d41e02a80300d601e81c8400d00c100c0111010784040300e05070b0240191000340310451141c54032200c1c0310b00c10300c40207403181030741c0c0c1e980011401c0038031060300c00c25a02c040030010301020000c0c0701c0c0100425030240041e41000410b40d45450100c00c54280200801541461096000d5040b0f0303181c1a0841420000d402e900f40300280901002d54519105810102003c0c7d03080d9008640301d0b0813140d9a8403580d103404003c80c2840040e001400c402e4007595610303519200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 552450629 1250 552449379 552449393
    0xc061506050a030501080f1c03110f03160c2003010b0901030f12090f09391d060301030f03020f0703050d0806062106010905030a06060611030711090c2206020f1f020c0703 75
    0x100f61007401e0053340380d142ca080f070038a06030381000e030420811500241603c041901010340b00062550341d02010000c94003000860b01410003074820a030400142c4000009101018810720340e120320034442c0300c021121343d00d8105c0d84440b25000d0000b500540500811400788154803103c800c50740308082e554400a041003505000c0a0055000350303455040030b00614180d40012030904a8442d201100181c42001010070800d01050000504582c414015a8207042c000c02450403030441301001c9a110740d4980c90b19907141c0652021500108003074801007000c9141030402e4600504a244181b6060180100120000000541594140024600080740e10344051210f03441141c000c85001c900140b0b0311034020204140081041c48a0b00203110010000d0940300100e244203108413050022500c8002002c0001e12070300310108600c03800403104101920b002e041420480c2d00a40a0359045150b13101000e4803414200728042207401428203440701e244a66002c0c00c99a4114070441c1c50060320707555441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 552451879 1250 552450629 552450637
    0xa0e0604030306030c0933080303070f14090915130f0e07050607020907050901021e0606120d0212071401050705030f1b0a0c061506050a030501080f1c0311 68
    0x180c00070f501c5540a000703000345488203000a04100302e080008002100d003003052428100c00489401400c0481c1c154100404280c010261501c941584c2e5a0b09000e82c000e411155504505c6010504094103107480034640010b9440ca0301c40500446d05039070356200c1d42c103100348070b01e164180d20801c1c861104440c110248158400a51a48000a180382c90102800c0ca48141640198440c220411100f001a2500003046401c00c940d030038820788494100f00142d00300360103142c0b64500c403148903003e407841e070760009084c03170044009890300c0070200d88800ca21900d8070303032915100000d40d10890a007000d00c000e0720700030510b0318003981c0fa60300c48080009810f0300b500c500b51a04000690b0105c1031014900f10351800c0da0f00144640c80030b00000880d01c0000503140500c04640342032080902c0f004081c0b04058006100e51910f44005801c0c154070f40401411a80115000c0c2e40002e290100100d40b00c03500140307038001e400031000107003d04002521012000364076040d82c8010942c940c1e892400b4410306001034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 552453129 1250 552451879 552451883
    0x1d07170727050a0e031603090b0717030a0609090c03110d20030c100f0801090c020604060c0302070b0901020d1817030711010507090312170703050c04050d2108070806090a0e0604 78
    0x1b941e120206400c00070110040350b0015100d0281c10810071000415190310a03205103002d50100b5140d40e07907000410b000308403079800240e0340742c1003128100800c00d0b407503407030000c0d40d00c83c1c662400c1d10ba08200601412a044100091820f040c903c40250511072028000d00050030080840c0c4068a1840200358100350354401e487c0894103091260b081160003500c210302512003c44100000401210001d6440b0000b40001d0b000560340c4e252442e220707104c0d070111a07406070008009810303401d042004070f000350702c80f0115058541c074bc81c041480b00180f00010a020035041080254554280101040300e640f0180840c002d10110001805202c003082c015103101d031042d0b0301c1c1c40d02d40500c3c50078003011031200c4020401c02c01204081d0035050450010560303411010a1800281903034804100d808a841950044da500a46c0c031045907041018460300030301680041c1848a40c415840401540d00020946090300880d905d0303000545103041118441da17021046920108140d058400030302c0c2055419201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 552454379 1250 552453129 552453157
    0x80c010b04240b0a12020f071e022704110f09040c0305070e1e0402012007180606020303040b070207170a051b131d07170727050a0e03 59
    0x94040e5a0b00c034000356000034400107040e03070f140003007400c80106080a00c0e0400d03c0503d07400305840a010f61400e0688440300d5101c09625600e41400b0f0080d1864503419008a205002c00d46180c400100601461501104104400c039060344850707540c0c100c0c0d410f01041c90f603000300c956801c0508a550f103015040c040c6008401d1210424118107045003803074019004811004003410500c401c50300d85070b1040e0700b8510903010841c413030b855505c0120341803c12070304c04030a206841c204080c1c800c00c020a016084540051000440da0f03645500101518400d10803c00903800500014003c07441d000d00040e8020b19030301c1a64000e98039441145040d40540180203020340c801e02c610400c1150412009000070700c8001c02d000701c10000707400507812040640c003802d0080d448041c0c840c0c00003900c0c80500001c50030242582c074001c0e03c03944680881800c080c0c20203017a210301c80d0002085096050751810320700b103021070f40d0b020185011184c40541005051002c0c0141e41d060241c461980a01c06088240a90300b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 552455629 1250 552454379 552454421
    0x120105010e010c0303051b032706060109060f0905040c110c0d05030f03041419060b09090d050a031407080912120f221b0602120d110c1b040515090103080c010b04 71
    0x300e0389e0100d000050b40065641c2c480824031401c0e80e0440121070486a00303150540c6404000b01c4100c0f02c540c6540d000a800074108000c02a84079041010389282013048011121500c0702c07902004815002c081c409480754104001200b8100c1003000115803181c05082d44460004c090122a8900315508040a802d0010707580c0c0d0104009040c0113001c0300c118101c400380031505203107a9494503000302c0c000c16014420700203100d101d1240650450070345211a0881002c10f49001759000e80051411110a69540202100e0001c0c6100540c10f850b0140c030f190030702c1c44c0342d40d03aa80c0000944035005883e072510740d83d088980d2000741c0d20030244501d40318412104842d0713008800e00e000b04940426080780040d0b411001102c02584c601506a80e111b424488020070240b040d4442d0403124415070a250030540540d101d5001d5945940f040e00609581c2a18104065030b608245008000968414160301070701d010010004103c010018001a4034850000185205000c1c0000d00b1219180e40c04859181c50740 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 552456879 1250 552455629 552455671
    0x1716061b0305270c0607050706140a0807080c070b09070905060d05060a0b010c0203070b0c060f0c0901111002070c18020f0307050c01150b120105010e010c0303051b03 73
    0x80050380e00140103050030300641c1494040141500180141e0702214811007035002d45080c03080181c00e49009000d0100c5503030351120300300305d0b46814040c01400d000c56022202c1410301e1501d81d00b1207558000b0f603500c02801d91600c0408071004d00003e44405c07420308080c012000444e0a110500340906400340040420515084d40030086c0d8100800d032902c00c401640c210400f0413404202c0f00d600141508000448000a0005803421351550314060342501c9410170120b461204c030401419101041e8046501a07a2804d80f0420704071811100b03200c198400b80007084007940652035a850440c040c1080c0c9940b8081400d1010898000c0b06c4160391140b0780e060200011980d00040c11100280503034150b00e02507600740d0400c158030014080c01c080150018281250900a601c259034003034641564505e03032581c5407554091604001c0b200240c8102c0c4500000c0d01d0b602814010100c800103031990225100c064505400500000b0581c40c05d0101a100145001c500c0c0f41c015071050214448060b0040808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 552458129 1250 552456879 552456911
    0x3190c23210a03200f030901050604020712210e0109020a140f1e040204031a071706010c050f010f020c0f03040b090d060e01050403032007020a03171606 67
    0x21401c9601501900080520000591812541e100b14582000300b61410190788941c160000e80b8007081030900045502100590404001c50080c42d00000074001c03038030b401080100f2032098075401004a120360018101c002d004403440000b0305040c2c503d82c041000802d00100a484817480c3d181e039140d655580704011454070b07920a4014000045501c050180d0f100c010400041c007410400d0700c0b038442142d00b0144c6c0c5415502e40800c0c03840190042d51900d640340740a40103640c0400d0b42d06054402403000500151040c2c204031203d054206010006459460040d80c1582500109489901400c4423030051b03c0720034060003c00c140065001607503044803492603401c003812921495202d4008201c10411032080c18150341c48443c0c11102d50640503142d1510070010046d0700f4003c000c550910042009054140c0d104910b5040403542885550404061100c0e8500c20310300000c3d030002200e40c0a001180b00801d000c242207221074542450b20040480314010f150f01d8060441e2165141d00c0e03807007822145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 552459379 1250 552458129 552458143
    0x403020706090f0e070e0d0f0606050f04050709060302090d0506130302010c050a02030d0f0204120308100b120a0209030115080708010f1a0f031014040b0f040503190c23 74
    0x10f035800409042c1008401303009550b02904102c1041401c1500602035a5204001c01485074881a01d00b1020150301e0014054102441454410303981d040000806007814062284507454503503910a180e0b041074003d07002500072448654214130035820940010b003041100e280520188090455848c0305441c000342940c2103061944200101800110201c3d07400105032041003a00b010085090300710309034030000070300855101a40071240751444005041c0c10814142c000d1240b1003c10201603200c2c100380c00c40e40b06c0c0c0c2422881030f1a0720710009003002c42550103400d104200500210b140c8a03100c0f0381415a0401d5005100b003504441010005d4000034407600009542124080c090500381c00304d0405241141c400782400351002c091948001d0b9001d00c5103081c000c0406008200c2d184130340340f01008982c000c80e0110b4510801070302145294602c0c00c0c1c914411176210307000b1480d00040c0a0f40100d136100c5c01c6240c0d004c2c40a410301c83e100088000c500c41803440005440c2040700c2c0280c990184ca4507030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 552460629 1250 552459379 552459389
    0x41206050601230703051207050903011a060d090f0525050f060304060903090509010b0d2313031e0507060507080712111603080118020405030a02010323040302070609 73
    0x642480d80700314a5460b40f07481c0da0381603030360026107132240c0c0542020b90381413041034542060329135a03e0400281d1908907018103003850003a4001c04c5200e1001a4122017091120520740d407200301885400aa15001c0d040301c1e030210b11171000801070f00016a203981c0b501c629856080c500d410021290501b250007407880f07400612007100c002800ca1410004650f9511011740007804040d20b03400c1a1083c0b42c01049414000c00c400381100255680d0f604412440307070401c60442c25107a00b4441212020142c035040101401c3c40b8584142c00398451289a42e0507060084049061111840d1120141403c5095100448015803101d0395616003919298048410080260f03051107980402d0103003403640002c81c0150380141c2000000e4856207540c802c40c0c0c3c1e02421040e000700c0e405c0010040c0805501a40e454102c0b1031801603d82ca03002001031403000d82c0503030b004554055100300001d4000d50321070f4002100c040c018455130074031040070100786104070031304880036009a0721001d0200f140c6540442d18000502c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 552461879 1250 552460629 552460637
    0x3030305062b08090d0210020705031209060d0b130f0204090f1a010f02070e270a08181c1b0b180f19090b03100605030d120f02041206050601 62
    0x20540b001501034450702e020050418000400d0740a0a91184021200c80c640c00034080036512074240320082d5544240d000c0e241c0a400b07081c2c0030f81d03e40a03c10f01600c500a03c01441e05080100e003215013001040f42c010660740c402c00000c0d00303141241c0c1c2441058030f1200c02600c09681c89040880d6401500d131000c209101013171429000035a034003070b0850409403000c002d00e4001c8001341c1c0c80034102e2400c0d150390000b50b10328114006100300000d00c242e01c200130010b10a40c06c40704000250b071140d1188447c140c042c08101042100112423820074244943d1144020015903508803c4da01020040c201120200d40c000c044942c0300c140500c03403070f500340001e1000d1140f040c60143e50000d65202100380080c2140141c000c19441c0d0900e580e44850318481d584141007180c1d50f9070b502d24641e000781104042d0301d406802011407031800c048407401298103035080a13006107411865400c0881c0d07004a03e00542403416a500100c00c01510315000030301c001d014000c1c1207084410300d800c0500440310f000e02194140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 552463129 1250 552461879 552461929
    0xf0a0b0609030604231e0106050405010b03042a12060506030c060403060f060923010501020712080307180b07230a0b0c0f070c03110904030e0d02040f060303030506 72
    0xa550000f80842d8060fa01c0041d450b0054262408542c2c039001c03402594a0a001c0c03001d890481450420790500301042e1140203020846ea80c03010320003210820b000e035081803041000001e01007030f80208040a20b41e008290040c1880b84040180c16040c001e0f0070086a951060260300c0912041d401243d4101c5800c5028118a00905000580500c5a44001400c040c1c50b6440b6050404d071a50104004241065082c402d03940b190444600102000104c83c1102c0c070041c0c00401d45500c001008015144c14880f19909015a5203400e81d071a00010070031800c0040c0607184614100b041000440180b40746089a03444400390714100c3c0000c406444d44c030b9411040081403a1241500040d4102800c0d0000000c0340d003512080d0001c140c500c114040242035003400a02c1c401002450015101124042d82c0c0c80410035045e0010031500d40e10176a000740008904401c01c0d401403800e85642036021740f0003400050242c1c81c950240d0203491056005a010070360b1041000303c5810055008504025500034103180c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 552464379 1250 552463129 552463147
    0x90103050f0f0610141b060f0106020303240a030804061407050c090403020a08220b0901020a14250501081605030403050a0c02031005090d050406090312090b030f0a0b06 74
    0x300e080c009101510501692418940507801080d1290b005880340024503504c680075406c410010704441e6214400e071042e00001511141c0300410b01e4180c9410754040c62031615400d00f0010146002c208038205c8207080940c568440c0d8442c94640001c5100d00c030400c0d00c0320318141d40544030703440c034940c2c1072414141005940001803021560046031802250001d4107512a424201c2c0707030a4504000400240b00002c42040d80148814a82030491840602c00d200f01e480d244025070501400503841d016901c109040740006e240c0c0f440c0d001180c0400000c4811010015180c0021400c00f04400710808151060174495540c0c00601158860f90030310742c032200594030700d400038a1440300030009000c01038045150f0048601c11800c6018041d0001e0884120805184144004003c01d8402070018407440400710440e07401401910200c61130364403409400da2071a12001d03107001c2449850010000c800d00042031403c03006018600a03c10340030040c1040c501007800708101d4429440152080f0070900c00500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 552465629 1250 552464379 552464401
    0xf060901061a0d020418060f060306061e210f15030804140609040c02010b031e1519020406090612051501030b12030406030b040501050904111908060c090103050f 71
    0x2d08400a00c540d541d8403010150308030028084d58000030180c40c1d003d0399201c844003050b00004195810441c030041c05641d1420300b5003c503900340c4200703804105441d0000c158521183c002001d2a1030301d0602d40c02504c440c004407044411001e01104915940302911041c8509500c5020111089540d10302202c505644801c83d1a0190b48071780400f100c250821202c140c0c40c1e200a0380d11105c0050f00500840310b45c21000b90181c1120240a402446004020b52a1998001658502c1610200034028142c0315a4081a401c0801412640694800b14803084200c3e081e00c01000100055580c82d00c0e20340c2040c00040c082059000240303149810304051061005d45034690312501a401d080c002107070300c1c079140032964220840400c1c1159000c040740c000383e0309401d0b03040320220031000c50341000203a880d2801c10000100030b1380c0c090080402e1581019040c2001890361561042004004004541e286440e81c549102103400c1610800042755030110755805004880e0441c2240441d1101c41c9020a1005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 552466879 1250 552465629 552465659
    0x608060f0c3f0106030506030604110f0319060e330403170a0e070b0c060406110d0f06060806030307020d080a0311190e0618040207060b0405090f06090106 68
    0x240201c641080b280003044003140340d9680a00d61480d50740305030859440180003a42003445000c0220303042000140c4145004914a4440c6510054400450404405010800140441e2250144564040c00007606002e4802e461950300c15000458000001090f240c00c1c8603814084d00d079001e0380c44104500300080e6001c541c0340000f480903101243c2d919410304a840780b0400600d01d000303120394818003241c0d1145403c8107511000507070498002c8d90340da21000c40c49128bd4070000080342c0000f00420009003403908a4841038071808449030414402c0d00c0802e045405810016141e6907581c1410042d580d000341c250f641c804d41c101c02035824410303603402103499091030402c001e040280000314090001d00a51000100424820400ba113980b15241c14680c0001d40d1035100010528000d00c000c0c1d6860100c00720360b6034910303049001410340c1d20601803002942002008a403690340f42e01b180441c4e505e5601c501032098030039070000e03e000202e0001460030030201501d10042d03641044000d10020301140084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 552468129 1250 552466879 552466897
    0x10080f06090403031d010e0d17221a06030105060a03023106080619020a12150302040c0c170309031806040f2702030f010b13180608060f0c 61
    0x2074a15070350385203800c0300244003c0580c6031007840c1c08003031400507840543c0308900703000041c41280d442d052282416a80c50303402125400313150b40404c000515041c0f060740040240c111003191510081007c0d62003041c400540140e549400d40c1c980c0400c0b086107824001c40390132007419a850b024980c110780200d4551005800911170351a0441a40d0101132000c1c80c07403148002c000d01040004d2901d64070007644490068900000352400c1d4103030080106524800c0b140c1000301500c50905c1001c2c1e985000c030180c105880280101a0790180002c050303182d0b4040d0b81d151107070507601d05041840c907240200c414100c10100c07481651007130080050550340001260a2000d580408880003081640000c81911498000d031140e04101140014228440c8110001c5174040490904100ea50a0450f01c1240802c0312034080e008000e50040100c5640070780181a0040b1401c41d44495039103070100c11458101490800d07003055a10003040246010510041d500800303098500000c600784003415040c140a10009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 552469379 1250 552468129 552468139
    0x1030507020c0a080a0302010e060c070b07050403021504080f0f061f05030a08270a14033c1605060c0f0f010902010801080c03060a0e1015030210080f06 67
    0x403a01081c0200310140e08940700500000344030340c0700c03450107440e5401c0e800102c0c003640c00d02c0381ca003c01c46030203d481072003030074504040c074180a982c0e00c901213000300150a43d01840000c20000c0090780b00c1420601003d0a05251659154644490207261000b0001604030307a4110442070011600041481a048107440a0103811700084e80c07450031942d80b050f401719034184161006c000800000700b024107202032102507440c80320301d0b081e810311442c02841c41c21140d100100c0d00061154142000000d80c440030060201c03640c0300314480e40c042203087d40e40d001c0d4802200300440c040e01803981d00c08200800c10144041c15464840680d00300060840c0d0154511401c070100c0c0c11110304500f080f0240b0b40322042d00440306600445054a8004c20101d90143d002490944c00804c0c3e107180020703480f481050103001001580c0d140313480207006242910820100740100540c13003d01d43c0080c0540002c48008408198a01e8598410049040024425001481112002c005400c40c003001510752142c01664 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 552470629 1250 552469379 552469381
    0x3100503150c1c141006090e0a0c0e0402030f010e060102031e16021f23071502041508060a06030b010210270f020a0e060d0206090f0d1b0b0403030905010305 69
    0x19103d03540c001030358400d90109180201e1030360070303d0206041a004100c6280c0401186071034500440f1300030701c00d01459001c03040d408040b030a60f2550343c1c004951b40c501c17498900c1f080520000018180c4e0300584289800c8005140141b21549046400c50f4004c94240021131400c000c40c64500b5180400000384c03001c4550104a004010029103641d00714580c0c014543d5004010701001440700b140102200c41c00121001c8031004507071a131918001400c0e1140100504000099840340219200842180d4056809100002e0102e51a0011095481854440c240e851404a05103ca9545250b028004041c1400150001c40e41c001c940f200c0e04c40c29400c4081010302c0c5411500c982803015000c50340d00790002c0d036035210030b11000d4610788030b02c1c520890b941d490495403080641282d01040c1c80c1c2640c000200789640c0c0040c82c3c11030040120001c003800c08100c01070000c0002d031607040c2102007035451400070190b013251100013268806c0078241c643ca2480c00c103411620000c02200b00c0d402000e042c0b40e6124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 552471879 1250 552470629 552470647
    0x304020a0608370608151f031e080307020f0129100c08030712200313020a03050d031b0206100e070215090319051602041107050f0303100503150c 64
    0x2d5804410f600712107105000310381d0340701c1090b607840c090719044540100041c40840d0758112000d0543c02c0c002c1030300090203046800c5459140807264071072080400500d5a10100c400141100080e61254103507401501920070700079065825a0302401c00800c40e103648450600081205406480000c0b0b01641c02c0428104020000e4900c142c80c1100a05404800b100700900c065100c2000803000e11203003000e211307a141c001300c03580041000b804138103442481400000e4030041c100707640d4009036000a042d8081e459594489030f0401c68103072104c03c002919082c1480000500d0700322152271545070300c000c1c903c0f450f088840d20105c159030f0190148140703500010030b0009208001061540840006040c424140310940c20f5481c0d011039000b481044c101c810300200c00e80143c060301c0e60800350711030f03181159001c1e60030003000306070b4010f0591401506020303441c08260700b0058540300d840c1ca0b1004555074100000509802c00300caa000601ca54801010b81321403520400e6101c0c0c0004c403d14485803240702e00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 552473129 1250 552471879 552471961
    0x4060807050d0509061503031801260a0204030201030e07060801061209023706081326070203060a0203061804020f060a030f0c0f140a021e030304020a0608 68
    0x45201c8601e86800d003c18082d0620003c50007a01a2440915a5100003000c100b07041d141e002c0d504614181500900803e031080d4000d0728011028807020480c3c0111240d075080c180b15440c8142c8080a10b5a4013107010f10455825104a00d01c6524480041145e90300d002d5000341002814012542003000100c44c0a4175400c4c83d4205440141e0b004059252056170f00d1142891034464940141448460702007142e92800340b200e588043d01e40c130741d80380901642e603140540d0407460744c20000c41e000720034031b0141d540038409038009400700c0000307801c681d035030748803d00405241c100090203c80c0f0340d0740704105004c1c566950340000340785002ca92800000070f940c5c500001d00704101c0324035069000b0500144000c1801e40c16400a64001403498007001500e410850454800700140480d60128202000f4840302c085000041e112000c1c90384101c0e60642d904900102480000d140308002907803012041c002180703020413002d40a4203892900d00071600d46800340142000f04000b000d480d041402801024403520 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 552474379 1250 552473129 552473137
    0x2090c0904020708030a0c08180a030c080c0601060f030b04061203210e010c1106060907121e0b10030b01050d0b010306030206031005030d02160b0c030d0f0b13110406080705 76
    0x484080e40d00c0345021000f8034040c007d4280c203440080d10000001d44082420010f40340c610360400b0007020b59191507542a50104646141030322030f1308080c448485036030f4041068502070815562940c4082c8510707070001d070036a00001c24907440386003800c005000a1041d249000002c40d007518003618041c5020300801085c0000a4000c0c4050b070070140c0110442c40150090307044682c5541d04e00b5842c0b54881111500d5190a45600d984001c1e02070200f0309262140742c4400a07080c4401d000201e5113414003403441c000042c81403044e03e103515205007205600c0c0c00894008030b100f09060900001c0d51810000340b0034030801c0740e9100c500b641e40c40c0502590344240c0c40f050255502a108980e241803280c1c00d842e00c40264481d04d03100f07118106038100c0c7c81c0d01c00b045503003002076009014080c2d00d0030800c00f00300580000390300c41040d100030300410a003002907000d140000000104001100c030401c109114941d542c110000380c295080c041d4250b18000207808590842e01646003468154603881000c942c5481 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 552475629 1250 552474379 552474383
    0x70809090711010e0d1107080a03080408040806010e040c0e09070506180a09200c060408160506040b04030305010609050d0204050606070f0b0108070e04030509040903050408120309070f0302090c09040207 89
    0x22a02c8a000344071480042da10000f61116191000c911b0100c407240c43d60303031003140607081c1d090b0041c10a2a001034025607503d90024458088641001d458111551500d80d003640604501c0800708140010302400c3c10036000607060344071144039580fa00107a1076a0300c1d40144a000d0141070001796150b019002c0a0b48070034014802010002941d680c0c4030a41c2c00b07040340340320003000302030080c08800f0364450100460701030700c500e04040c20b4150b41e01d40f1180d07840d801003810b16640f02c852041c0c260019030180034071f030300c41e9214850208c0c0604290078001c040303a40c16041401070140f0b90300203010300c4d81c031041c0000b40141e0454002c901da540c6e08000c103803a4000d048000307083d507150303000080401440c000d1640c181d50620341210030750b903603854548620600a490203070110300c0c204840c030b52900f0940c10141c0c0c0e490203820118942a602c2c50a5454465100c8022000401c04024040020410f00c9038000030940d01244055160441e000103040b128003500b0410040000100ca0340311361aa070301078601d116 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 552476879 1250 552475629 552475631
    0x81f0b0406090302030106060e1003051b0a0503070306060e010e12011409031b060118021b0d03020403021c03080f07180f051008160c0203120c010e060c07080909071101 74
    0x3654440000d01981860f0204034460b500b019004905948955542401c82d18003e10768405c51058190030340040130702070152540307802c0350f01c01184810303441c00c010043d800300c1c0d03030303c0580c4e03880c112100508446d01c03500301c2401c00002646400c0d842e07921004200d084502141c8443c1801c003964106401404408840c4040e01e40c100300b0042c007190040080c05441d050700065061140c0b20220458583d20240a403035010204101c5d411600402d0707070302416083c0f10b034981038814118510442841c10b1074152000c00002e40000c0d09008500f05886001284000d1065503c07105810b40e4001d0412400200010400099040041c4c54140b0a01105100702248424102415281c180150111282d4081d45026150410708500010b00c03038042c3c24860b406030590b070222510b5a2070101c03503034840b110b402d036854170460502c1c600095902c8014194001580e00000b41c022004850a040040007442600c0c483e00c10310510b40410303041c0301260b10794102101d20108650701c44505442d80c8c1d59004070550a9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 552478129 1250 552476879 552476887
    0x1d06010e0103020a140607030c0501020904090b01090e0102030910231e072115180504060c0c0b011e080604051e030a05040902070309030f121b03081f0b 67
    0x101020341003a4160790007070381d0a079500c0e9244c00a0b00f081d9500000d29a400000c100907580c0442d00c1006940f000b244a0400903203001ca030701d40043c060f580080000c1c0d0740d815041c80100b0119903070f4807c02c882c0100010081d81107140000c9403d4031803120266003010552113485151154031450440103900302105100882410441580e0700b80e554201c0194080c8092600402e613114014954001d960101d20b002068003040c11010304003812040202160134101c01c40042030b66901072817444110300740040001a03910309800c00ea001c1d5100740511300144078482d40c1000102c0c2c2c0030300c1450306403400910300003119207091841007107080c01580b10300f0007400b500c0244000c1142c04110b9103100168903090342510b12480c454140c59100c1e007002800403c20401040141e04c0680d006000200d0081c04c00b000c03c0ea03a82e4440900250000e80121181400d00401c18030180e0422191508a00441d100030f0140215940c082e0007008003500b1039503480f903040c00504041140307284603009440302422058503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 552479379 1250 552478129 552478139
    0x302090117070f080604030f12060b0c071d0103080307020c0d0302010b030c0105040503030a031e020c0607020d030b0913050c03011d0601050405091515090126070b04091d0601 77
    0x46140c504407041040c0140d400010b0710a030034800b210190f8a080010709181e0f29160303025121407100782c0750030381441146541c49840040e90b01c900030003091004a1696180d2418001e2401c1820035080b64504400d00d009a40248001d0082c0740c6c19240c2c4030304a00c0d681d46640900b6480c04010101c8181d000344081c05160416506400c08007030380780141c0444520000220065031203005501880360945d106000b901cac0440d200c1d0300509250f45086403020320880780612800207036031000840300180e601c440d05001c0d81c0d0b94108550084c0305254034040105043c00c1002403003088001e00300030344071000816010207000c0e0610150700c001c00028003c1010351005008414186010445801d003030040e0b0000180381d080034002c80303105042c0d00d4050b1041da4820348816980c0d840107005911040c403501d403601e000341c0302c0f4130610b030180c05070003003041007260b4454455401070505a2806200e0b005107104220040703002003501c0640301051f1000c10940125841c092503044000140b40244c0715001c00028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 552480629 1250 552479379 552479399
    0x1080d1b051c0c12140d09030c0543121b14030c09040f030c030c0c03080d0609140c03061507060b031501150e06121501030b0a0602030313050703020901 67
    0x40301c0d504c240031102c001400c0c00f07410b880d10741d0f00b64612100c1c01c0d0100020800070f41c6030f0f0302640ca9240300b401e040c0d071441d400b41c541071320f400d010303076101082d900c165051103000144d11890002903030300708001c0711551146560703060b040b00c1c0d9034807601405011040c0c01c00c0030454400f0400102e000540ba1441e0500c1e0f5402d0011418030442da2501c0c06409042405402070408008580c8034075007150b04040c40e0415550700b140c1c0403005030029000c1160135400c800000300503000035002180100130345621a480001440d0071100291b021070900c2e49080403225401170808045540015400207154403035a4110101312185450242c1d80300900e40044d00740c0070030a256012402d407020a80c00c80d1a007d00007224290317440420b000f05400d80400c030f1405203040d84a200c004401c40809000e01c4c1c10102010f0000c5150b800540e200f0100224005c0c0d03414a46d640361068000c0341900300d074258903441c54a000a51684030140400c407041c41d10300100c00502c801040614010755000d0300014440d81e454180300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 552481879 1250 552480629 552480647
    0xc03180f140307080906180607050d0f0c020d0303050903131206050711031905130905150a0b3708040b010e041a06030a02030d050c0601080d1b051c 65
    0x664054640c040008024000001e8034071075540a007404c1d250402c0304c420800d007500030001c1030041c40100c0300210301e503881b5a80070345519403080300184204d0408800c041c0007514001008810803002850f10b0703003da91002158041290107040c000743c191204141c0714110301c1140d4a98100003005080000d00c046000420b49485009010400a58603a080229604180ca18200455a03c1130185150b544000203400035039400300d080c203a2038903144080032883c00c03c1a07804a51229030351401c001d00764075201c071010001c40302122440315040c20326040003154040c00213803040404422410f08c4400c00c0f141da040d523244291040020400c100c040000746607002c112011a107452010300002004201426807071b0045078400f062620306078440c40b58011020009094a905100c0d91145101603102406107509030344165a80d41d5840030842e4200e80f0f4124180c2c07100710039900c090080f030600c640c4640e410241075001d0818403480806070034454945042104082040907101f0b40d1045a1a0004018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 552483129 1250 552481879 552481883
    0x4110409030c1e0303140c040b0c010609110306041a01021b0109033003060506071104021603030f0c0801081506030f011506030e06040201020a0b0622020309010501050306090c040c03180f 82
    0x20f00c052941b120180300d050358217035004002c1c00d006000a002c0802404080c108100040000088041d07603858010151440007052204103000002848018103007402100340500a1941006580c420240000e50301d9501c10096180d51040b04419082a0303c81c2e4596002150021100c1a0380c500311000ca5100d03201a581c0650800841041d9640241c0070340201001c44500030969403c065407500d070352001e076600c0c1e4841c03a48690f0811070003d000c0041c40c10408464026030f000550080c2a602d200304039802002c00705c0c140020b800040200a80c00a9a400300d400e1034030503070310340c0d4803081c010a14100c3c4080b02030007035500f841c0340b8020a40007908200c040300d265540601c4500ca80703020190f161441550302078016007200000303602160070b0492131900241c0240619442002d1241041c040b00c2d10b0f80b0643c03c26540001c1030140c201c009000d03240c0036140c200c003e01100c1c10642c00a0f03503200d20f4020b41c2401503440f44400081031380a0b90011071045190f00d401a101c170801d01e090030164501c8842 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 552484379 1250 552483129 552483131
    0x910030f1401140c0d0b011419030506042708070b0f04110405070f2f070e0105090105010207030303051e07080402130216020d080f0714010c0804110409030c1e0303 72
    0x6034041c0020201c00c1070050240b00400c510b0700c203441c24104082c00046d00002d042c08081018041c240f5a8800109007542201c00d0030142c4540400c2d006050702c0000d002c45105a061032610340b1100c0ca40a61b0a40c03c002013005124402160315041000340900500031700030b419420b0810101c0c4103c600703200d11680c410400040403031030207400c00c01140d40680d134800000350340d8041da50f0030030700404480c0000825001c5040d02c9006c1050741026039a003d00a401141d04050420070a041c00704d00d825000d80022904010158103001c0000e5890983e80300103410161032303038081070180585813040035132280d0b400281161440c0c003900190ad0b181c03080e82d00700d0003001c1c0c400694031001d190340300382ea14a400400c45030198048035001c1041810030040f05580c00790302040701070604048078009110040c400c0c2e001074460a19404442d0844920450354014080918100000219084241d4060103800c442c0000d10704480e050031958a100a00001e0005500c02a103c1d8032051001e101000c0d5442964 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 552485629 1250 552484379 552484391
    0x5030402210d02011803052b0f0b1309050c0907090e010b0a0f0207030b1620280305040b0d0f050c180415032306040804060e0418020910030f1401 64
    0x1752000c082c18481d0350180005009026180d00c0040384202c80860014980011610441031052441241c81141821a08540d038601c81046070400e00307151444520001410041c1b08210780b60a034903044080c0e09503208292040000e21140e00464040e8054221018a0300d410f41e11000520070300d0b03010300c08000100b0300e025003150101d1720004118068a03400200d004140d100c2d05900b0380c45184110849090180c2e0245103481c5824503460303003c0b4000d13034400400c505803041c91550f80d0030311898000002912030307000c0c540203e50032004481c100c82c0090f21059641c1c1700050120010100b07031400090309810f000c00d0280c41010b101c080d1044a00c688070074860324008000300320858a00d01c80d82880c0d500300f00030802c04202c610309030344190f035001082940901c2e0841e0010b030600394100c4080340c02070b202007003d1080550282030000b45da081070b6030420482090060800306a00c060308001e1041101d04000b85001135186880b03030056030303c10060b091450107441c2c4142005036080c5030b1246580f07400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 552486879 1250 552485629 552485651
    0x6020a120b040905070b09030a05060906060909070303020303152d040f0c090b090a0317280210090201050408031204021806011202070201030b0d0b0708010e061005030402210d0201 79
    0x4440c3c1c0042943c00701c01011064502245c859031500a00d4500303505000768055580414030500146100d61140c2010b00380516101c001c005050001030088081548010780500000e82c0000880742c0000211400342c01012078400082d00250090410207034251000f03082d41c0038031070510300d12008084211000d0004400c00c0e0300080482d90640c03003070710009940070700030000251903c0003004009005402440055126184c2807115004a0107144010100156041001e4080d108221203908202101400340210000080d61194454400f040c0b595860b500c0e5011a07021b001160001d10140c42625182c2003c50642c01c00d2640440f0268000d64100115009a0040341112403242205841d0308520340c0c40d240c0048025000403604906061782d54900c40240ea640441b46080c1501c2200d03000c455180c450340090004a040e40a080502101c1041c003140e0359411040403e82041880c0c01c5884e40d0300c6000217040101060010342d070089d040650f0040c0300342c01140541d0194000c0c2c00a1110110702 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 552488129 1250 552486879 552486881
    0x40c020118061109040608030a11010c08010e18070906030c080105070f080901020f0712020f01090c090f061a0c060c0403020f0402030910110a020106050603010b041e0306020a120b04 80
    0x70784403900300030034401001d0010342d550303000b0910151486900e030f041404050100d0200e840a07088030006d81d0000c02e0815405170b00000180340e928001001780416a01d01c0c5010700303900302c10b0040200700c4054200040c0c0c848401c000c0d101d40380030403004503810542c7c1c5403000d60082680f4041620705280103031b4080b40c3c485050046078084c2159640c1c15100c0c1140c07540840b801c5030058411025550204844515a81c1c0034005e0310721103019008004105403024000707441c000054943c45480d90400560b04085541251103900303c5a0300030006c50700c200c902118100a140d40d800000e40c00c80a101c0c00c0e0404004a07014200c0d1100e040121242510780b1071001d80c1e24002c2e444025400241400308034451304064003e160004414002c43d07042035101c403d14800c1c3c1c0c0d46106981c02c22100800d00c041c48075824007644000f0141614254a1035040440b000b07040d100c0c6014503911088803814152034880c0c0515204011034014000b15181e10314980d000302003070000d00607845410700306110385c0b083d4501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 552489379 1250 552488129 552488141
    0x6140108070902040f0b0a0207080a050c090a05190b040f0612021518010c0c03021c230a0f0215030a050703050109020a021e2805060702060f07031a1509040c0201 71
    0x1003059520f045401010b5030b02019020302140101349001544ad4820441800c3e0b2900c110091b11001d06000c0500502c58001440c0d0034400303040000344009403443c10308115610028010120b840c031900000329001d0619050300044040c40c00c400010241d141540301a03100e8400c0310707a040311030000a00020305006156414184c5441d5941e014000d600070200c01e0807440c443e80d201040d555880e000201407042e40390101c405a03480840c0c1c2d004020000400c01c401c15410b80301090342c10fa82d2407940756961084000106245155011041035560f880517a80c51124100c9030300740d80380750816074075010702015510000440d041030004100349505000350744c01148540e0040001c40401180d00d41c002ca41c5070a41c00d058011030b40803122020405008905c1500380d801314040080e210b1520b0f5140c207100600050444d00543d061041502480400c65000011460701040700c2c40301504a0315503c084411040c2c1c4071801d2400002d10340c20318400b91003270020407641000305180420042c0d0070f03104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 552490629 1250 552489379 552489389
    0x103052a1b03032e0312030209121605060c0a050a083c2a0c09060604030804170f030a031b0804020a1a09030d09230a03030302160614010807090204 65
    0x9244c04250000e040084100801c0204165030309000700d40d00d031103004000110581d03c100180e000500d107405d40c2032030000d848501203c0b02c024000000c480030596000b29482c060b04c1d1007031200140405034402e04100320003944d500941903800000740c80c46c2c0080e2aa001c0c40f0300c144030410780206c40d4100c9642c400c24104245180d500301d4210040e0f50040802540300c40030601c50042c044441818102e80f0b002d070b110f081d02020b402024080b50b80300030480355000041c4600e201313481c02c110030710001d20304000342c604aa0fa14004150640c00d4840d5003428204044610320032071201140120300c455040e0041500100040001d480021103044212040b010848020303410025480c0c00300401c2044104180d94074407011900c9052140000000b800e00400e0301a160000d8200f4805100000340e01c00d0b101c2a1341c000b40c0e12a000648130078080344079160340d84405010b040c1d021503180018114640c0006469a00032801c00c0800201e0140d00c01a030000c0c010290648150040421605403c0c821101a21 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 552491879 1250 552490629 552490651
    0xf040503040302130f05091e01020405130e0708010c1d0603130b090c0603010e10060519050319021207030b010f0903020f0a08100e0606010912020103052a1b0303 71
    0x242c115000d002010580c0ca90905000f5a101080844503070f0600c40c003400b420741c140144ca64040340132810502410403858811040e44100000c2040e9031b0ba01514064641e0161004102c0c819601900c9040940769800308000f5400e00714a10102540040d84951176440080500300c508c00741c000b880b55034081103480c86990303d9500030920218802d2840d50707522980c04001c0b159202c1d640008142c0980007a8002031860282c0d40602188251601c0c21001800082c9401ca00384440e40c561040404114000b880510030000045070384504003030b0544200748042034040d03650b0358074942142140082212080c000a240000408180d840784442800702030300d0f0f540300801d6034159000c01000400e20302c03003540e100ba044d400029080c0300038450300c410b103004528001070a15480800f64280300e001021541003240e030701010300c01c1840c0454018000d54080c40c001590f69030340e036003952110021004a902c1008a01e5070162040f001c01d0003021001b80242505080032a20010386649010680e0410164 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 552493129 1250 552491879 552491887
    0x4140601080a0b0310060e090d0311071b0b0a11060a060b04300c090605030705060a27080703061d0a03051602040626060420010215010f06080f040503 66
    0x80320b03680d0041001c102000741942e030440ca54620740030440362160f10084008900904000c101c0c0c800f03100185080340c140c1020b03c4034030041d0806a105200c1d40500402e1020032405446000040603201c0c0003801c0c1501809540c0d290910020b0029400c0400c0102c562254500003a100341c45801490200c64500c4801400e00c0d040030b1080c1020040040b9107080401c03001150406030301400707901c03441d0038090342010050710b080c800c4c010f0580e801d0303401c00390280e44040020800b507200c59085402410141c94070100c40f202002507001c0e00e207890f410a250cc0c100c50032000c00c560601140000880e4442d4000300556882c1000b0322801c0b0000803452140d80c1c020285003804a40550010195400d4102032221403c11075030000e01102c0294010111030340b03280c1001d8201030381040c11516000006002080036240c184e0b2002d1841850441c010040680b140105c04664020042911001240e6107800655a1a803a01c004101a03604c142c1002480110200c2da011031002c0c0c01501070303608a0051468 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 552494379 1250 552493129 552493141
    0x1f14010c0206070804030f02090f010315090f020a0602010e070503070f03030309083705030f0103030e0a0509090607020610141c05030c0606120706080f0a061a090414060108 76
    0x480d4964100598000740300308652000a5180d44c018000b031440b07407591114041c1e02d8018480a108010300791124041c0070340040c808501c1103841e401e2505c0d415000801c00120500d4018624040414000d41000039188003150850701034000d209949035803401c903400300703544100b0560384075030500c0b0303502c04110000e0003071000c64070a400c040301c8540140c0d5042d2030b00e50342d10020320168a41012100e070250000c01e890065108500750388501c001c041c907080c1d040d418440c00c8490054410304c001000d000c0100040c2455880d261107901c0189001882d400982c94018400341c0c440c242100c00c40018002c0400190a080003128102c054452a502c030501481100081c40003581005038081030000c0000c0196000038010401049901c0d05040900614180b000c144410351001208429081e08140003d0040b00d50140c8156400944450420981d03254421210300502d100c0e01300d040d0104002c2c20706a060b11f03c01e4002d066081d800e640400c007201310320a0b9440c403d241550642c0c0007030715420201301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 552495629 1250 552494379 552494387
    0x903060f0a0c030603020d06020d1407030609050c07020f0415090f02030103060507021f020a05070f081944040506040b0f1009050a063503031e070e0a0b031f1401 71
    0x100300c818210ac0007401e142c41243c00c100d8070604680c1e150019407035040c14042522103003e1035400256444e5140d007007007802c0c6c1c00145005610030318135005a0b91002c00031150031003000d0b510010580c41c8010007810720914400c0010b9072003408182d41c140e0516020405040c4001514140710140010403182c012522640e13002030350101c166401002824031100300403901009550070450721403840f5a40c0d803800d0b081715003080079500c0228000d0002d505192400d2050705901c6101c3c4244050480c0140d030340200c4a941028140c212388580360070030341c0800c000c0200010320140a240128496040340d9524034510301c072034504583c1c982c0c0085d90b010003000082c0c1c0d00d40010b501718200e400302050032078031206c409060300140b000320f510422180304400700300381c403864002d2041f0101501441c03840c90094a01c01840c0320707c80c10707591a03140520000301c901d8854401400f010030024039140c002503550340d0040c9513400958203001c52082a00c1004001401e603c503042c1105c044441001e900000540152 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 552496879 1250 552495629 552495637
    0x1905060a0c06060816210818060f07110a1406040312021507021f0e03070b0414060705030a0b01020d0f27080607030e240c0903060f0a0c030603020d0602 67
    0x16901a100d410108081605024080c464488103099043c1755142001e1802c00c010034241c030b0740c200076022400130041180b250845003402c2000403d505440c2611000c19030902c25000c04000c401404a0325000b040360040482c5202c5004944180ca150f4807510b18176034185840c2c9009a010604200400001c1c0766804c2c11542c82c03141d401a50112040c001c54010380304811150600143c004c400c005950415200c107100c5e800d40c036410100700c603c90149038190b07a44141d1001415015010300058100810b5007942c0c0d01000080055944034140b00710064410f40055820106003820100000e110703510004070000c1d5044150b980c20403c84000350280c4000051102c5400d0340d01500b0491034509050f01d02160007045202d00800703151906600060484588002d0501c00d81c1044120650300c20840d94006121045200194039580303c0080c45070301c900c80c9071026500350050f601003084802a58150034802e4091410620075801089002c40c12581c0a000007580050f841d264400031404a03400741c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 552498129 1250 552496879 552496883
    0x1103040b19050c01360203060103060b0f120102090f180402010806040b0409030e36090c0d050c0909070513021303020a030503070c0b0a080402040c02150a0b1905060a0c 74
    0x451401d001c43c1c2010b825680c10300d05a40e82c2c48640100000d0061103a0302d4510700c040340c41d0020000e0b407410b43c0006d444080600c006002140c81c1c142100d615642c540000321443c42c020148100c81642c800304074080d4103c87c00355849045088485039507418816400d01086403984203004ea50790351580103443c061406010a0340060340d440c120596501c40c0e01c220030055000342c5501c40304030340343d100304040d100c51042201191078244e0584203d070000580c80303009000c900c50b4943c0c650b5840c920340a140036284c001241c0d22002c1c2d05d0694091100101e00e80088100660b005d105c3e07603441c80e604a5032029603100301c9801c6802c40c21400036668656010b00f01b04d5486104001c8000c0d80d07500099041c0c10290016140b82c3c00008140342081556143c00b4000d100c152078450602120305005000004001d101900498076002c51a044501c00d102458034484006056189420f010090300c004102c6081c1c03860158400d40102e00000000b01914021518000c04461410a4405e000c4541404141c07003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 552499379 1250 552498129 552498137
    0x7080c0709060803250201091208120a0e0f0d02030d0b04090209090c130e0703020904060e07060210110906030c090a1823040203060105041d01020f0a1103040b19 71
    0x80820707454498050365009260000c021501c03495080041000301c240405548040403000e640d110050360030258880c00c0703400d20500c20000b0485800c14966034441c40890010f11041c590804c404584540d2117200150030b260212191008000c00380c86d6a440500700e80005640144100484410349070011000400040c00100d080c01d1540d0104000c0c001c20389440909800c58140386c4450308152030255140b6410600c01d00c807411519600b0381e2503815501019014400c2032000800b032041a130020884120100308075242070759a030100a4031801900c1038184801e040040c0c0c09900c803000c1c0291100304a000f041180f4644400382d1480705075010807401c076003220440e0342c00107060b1007015445460300c04506e000b2840a440c000f414000e0320f032000e4400810b03000c2d00c0a000241c0c1f0001059070640f0300503a0300240500c1074190a4002c2c6c0c0389204044000d6000240e80503454142d08050155a4003689030780d120042940b02040c0c42c3d0090b07010300c10030920709000d0b003502086840d0008102407080d0030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 552500629 1250 552499379 552499393
    0x5070302060a0b03030706060f15140901120e03270109081c030b0907020c180112020d110a030f050f060c0f0a030f06091e0e1e070518070201050f010b07080c 69
    0x47c81c1025118141d010807010583c6c10003c01804078141c611030700c0c1669901e420410016004a1940d1901800c1c1c51141005010240481740c94130710760011241c51180d0040700e85648500140c0a07000007030051300f800c202841110a00c25500074500501554040c4006e080103510118000c03101616504008081540b00c0714520420340b1080c404501600741c5601424283c180c030410302a4103205280039a60b0101980c6c010008441000e194110090341107072450b42c88451f6043c1880200e4986504540c070042030768001003000030803400519007911840035a00010040c140141e22045e00320744040d003d801c10400302c4242e412285c0108100b0285e07050018001d5620351006089030080d8200d05400c6950300352240d40565100d00c001c0758903905640038040d00d400d0f8004287c0b50348540f035031f02c210101031034071301d0b04800010300c100800703400003410140c0340c60342405400090309801c0d2008409546040e0105d00700188000d100c9040e2080c0b002060726012556440d44e070180e210384a0004640940e003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 552501879 1250 552500629 552500633
    0x1314010b01021926030a0506030c010c030e13020c0309190614070f0515010311040b0622080d0819061d07050c010501230a0e040f0206040312020109030e0105070302060a0b030307 78
    0x5085030a201c0c001e0001d9103c2c41c0040240e41247c0000e4500e41c0b2940c401d40d014001c80e03034000100c10307642e545450661082c00309003000c2402040e010403011542d600104031090b0413030002019101500c4101c1d000b20b50300c031804541d283c07510068014000040c0c072114224150090200090071064481c0c0d41d42d41c202c5070355490310741c01e00d0f0b41c1075501045c0c202508010014000c1c00b0165140001044500308880c50300240010107074030a00400d1910040402d001c4121031101d843d04200401c0e0344820f03142d507881012801007001604540c448200c0400703003038034006094980305440540340d09000c40225a0042c803c0b014840340010103907410031504021030200c540080c0038080c002d040e44241d00b1000d46102c12580402290805d1141c090308496504001d03042c207000040307800c140c100e11402d4000e000350012411170700c1641c001501e103055030009039110f554154071800415010b90307200f100e5150a20b00440e142d100d82000500107038442c00c04540420f81e1a0300050300c0b414010201d0349443d22030303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 552503129 1250 552501879 552501923
    0x105040308040c06110c01180306020c0303010504050f0403050f0f0705160305060106030c020703110109080d090521150a0b0a09062907060b0109030b1314010b010219 73
    0x4540860001c1c0c12082800300b08506003d1200113484942440ea84540d510b042d401c0d56518501c617480d04011045039030010300e90400d6418805107402003000c1d55100c14010b8160799950080c4920340c0a20701e0100058407031500c52000701e02541d07069840c1403030000c0c2c0038805c0302d407a0020030110381d00440c1002442c0000f0010080d103480200f000040d0784c205480c5d03007003190030491b050b030050081c181494500c01026502040c0241aa9070010040484100d0140121081074071a0490030007441030004000d4400d8008a2450403900101ea10405100e0883e41d881060340d02150301c814290300140e012100c84206008440e8031a0440d800050300d08503d10020317018540369840340301202c2d1b032140300340280803403080c0c001c40300105440f10419540b01c0c0c0f00e24002501c20118064403140d170764403600056a00c1508010002c42d044910a08241464201c87c922441c500e0710071240e40402c940200c0e0a820180600c2c110400140c0240030400118285d101030b44107103483c200c82c00030170307405580010200c0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 552504379 1250 552503129 552503131
    0x30705181c06051008070e0a020403141b04060308070b1302060a0c11040606020303060108071107170f0a170c070b0711100e0d122f0d08040b0106050304140105 70
    0x90001c4110001c810300340401280c0f0040e00c1c2100315000110140100c200000741d03001102c02000e8011030956600013604020b001e03030782004100d0b0b11b02c480b4409516400143c10304c910540c0e2807000000c18800403c1004440d0705100080c85c6020500c441e2020a05402c140c940c4031800b0825121404135641c00070320140d0180c07000502041d0144000c5051044070740070142c03151b209590411a1900307050004c1c0d92408024001d82c100301015000980e4a03124500052400c2c00480840c1d800381d4032808042044204c8012005440c072904c0f540114603280019171000c0640c1092009079034900d550120007190303010700c010308458858044001111101c9000902c0c2c2c0c103015001c0500340301a442c0c1003140c0502e548600b141002004402c5000542d80c101401440d15803005809031950380524080e40c1c903881200703400703488160350401c054600440f5540c2da10101242c00c10344101403c1c020b0152481e49050700c000c0c106140150042c030509004000554000d4002c0b0200301d01e00c01802c011500303450f8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 552505629 1250 552504379 552504409
    0x2090a0612060e13140f0a08031605090f040b0103290405130b0a090f02060d0e250e04020f0a03110301050a1a0d031209050601050f04020c0303070518 66
    0x10850341d81040120344039050290011000082650400d07080c01d00301c0640c54480079059680f00700080c540c202d03080003684030013480318040e910100118100542c9a400445040c807003462104084840140300b00202c8a900380d0040c217004c1d1034060b40c02070100818440e00380d103050640c1c03041c0c0070501940000c1082d01104030002d03044224a1000180400c0c1c3e207014015007050070760760003040005002c0321040c592004261900051000072030a182001140e5035101940000000810205004158101089005004003118000010300a0a107000d0b030040c80c80007282d000c048002d200740303248148601c1c1c119000600440e1b83c07100070f1001510a46c4c080d0700488180030341c0c024000d510306007802400d510144c1d401e81006041081c05202c01d206510010301842001c0302583d100426004140d0442e038168403141c100506145890120b985400038010940718030340e003000041403490103008a48502503d040518107646442000780c80640110b224040681c0b6609100a41a01c0c0c002c02169145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 552506879 1250 552505629 552505637
    0x6121002040f0b040f0603020c01021902060702010b0f010509090a060527010605120105040903020f03131e05010c0311030708070b0402040f060e07050f0d050702010c02060106022e02090a06 83
    0xe01e0045489140450342d840f002103580f05100800c0344a4040307040508540240c00d0140e51607021051140c024854240708840c90912020100c03402d0b40d0001d1914400c4041c0c0d0020000e203682d140400080c00d0409450701c1c0052401c100111082c00c0c5200d2068004501c004046801500c1d0360009041d03081800e4690541c02d060613000990100c0082607500611150401390324200361043c01581e070f010b05000d074a000313030b445141650806208100c00c644c0d400707000341500d0301d51464011580503900c0754812210000c5100000c2d8041c40403420040d030440f10140c43d01180311130a80c0d415110600501c0005450b80410701884010603810300091441b1441016181080d1425204020445466040c2100a2071070910b05200d08a5004405508108181019a02e0707030941c280301c2c04075100b0080640c5905061105110380c90303030150002d00c6c1c4440305800740d448aa8071004101d80d241340e000ca40754102031081303020070352071524042d40d160b071512041400b61502181d0000f1032008981e6500501c005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 552508129 1250 552506879 552506887
    0x30809121e0303062718031201031506060207081b0d1a0f0109090c0501211a10110d0c030507050a05071e051509011106070807031401120b06121002 65
    0x11701d03215042070b4810009030b02c907400c2038100d11418041410700500d10030b520282d00041e5001c0800070800c1da510f1007011030f00f151030340d03858ac6001540c52004c02c183d0700e1054205003011804c580040350701000e40f25194024402043c541080c40e40e400c4480ca41a0382200107082ca070000300d03d85451500131b58039620003080090901071030946040f14140d101c510094501b201c03800000f0900c2805c10308071035007460f1503801030742e00030b82d0141d409d4a2045400b451500d801e40c018501c2400415185c000d14003120340200c00c1d02c8461044d1010006800c04103440c0c2c1017100e040020030700450402d03140c5400381c5001d60400c081581c0d003918208901c20141d0b844d03408038508001143e900326994041a59405507270341d03034502c0c10010030300002601c40940d4007810701080f4180c0326449041c0b003074410f902050448486041044010b0701410f01501c21400007420007002841d220030321a80709040fa200e001c81004004420349506400e02d001070001c0c1e40c08213030f14848441101d01044000203e401c403160043e03403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 552509379 1250 552508129 552508141
    0x9010c020705010306060f120b0d03020a02092a13180e060705040b0714192108011d040204110408011d12030f100302061305011206030809121e0303 65
    0x5080d805030b200324100b6080c49400e0100c00d0b48498031450715159803e10310110b41502e02100058201c8501c0f582e00443c070b4804c00014594000f8074884058001d440003e415121000016035050440401c400000d020340c50311000c16643e180141920140b542032010b00c191a401c1142282c1a40712070314102580703c00d030054401c801400791a41040c603d0400900d403078503000180b00940a03540c005003c076031191030303d24000030050007403410500c1031002d4504030078010310308403848001d400360340c02001c00382048182d0b0160223405464161444045200011075112840c8101000000d00480c2c019032640e04c0c074020304039204091301c06080c1d9940081502e0020714210003025440070340e256225031002c0c0700341c076007414200308403600888810018140e41d41c0d54039803da0004500e034030094000d40e00141c91542c0d0f0b801d00a00d03070107030b410980c0c88207030b000003010908040d104a408054650b10b410005044c492404c0c41c06918000340c17010680c0c01c050392105404400c00148020070071281c00000c10461 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 552510629 1250 552509379 552509383
    0x120c1518062212060c0903210c05070603020c070e07171909080a030f0203040b180a08180a08151614030a05090d05070309030209070c12090807090212061e0909010c02 73
    0x20f6030075003d180126400380742d84c03030b46400f446d00180d112615161032011040c4c42ca11031589c0c03654054008085458095450400400942c40282100d0742070180040116001c442c541b15a8099425603540e10103008901e84201c85007840586490b6041c80b00030340c1c121400070705000742000d05001d102103030b403120320703002d00601905c441c00464001c061041080100084111000f1904400340d03241c002c0e6840c01586c0800e00c1d003842caa4001e000d0540c0400d4045c000b400d1206482c803030a40c141d40c81844141c0d64040b040d65024444120399203003003445c00044003140b0035040094507603818a88000401034005c00598650300955481603855261810055010710401c5806c2542046140c01403800f030054900600158880c08001d1080c884e181c04035501603c01c0c808044415000352102c0c20310741050602500a41092003020780c3c3c2d000301031000410120b14800c0e503800c800c01060702c0c48550b841278100410802c10090000a044c0401e107203032410345378100090311400894000040d00d00315200064 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 552511879 1250 552510629 552510641
    0x6050d05100c0513030803090f0f060621030a120b04060f030b070903050703060509100f15080708120c01060e100f3003030b120c151806221206 63
    0x8014400704205010201c11403900c4e1004880e0400f007000d44a071510a003044c00d00e070200500c000140b080741402000c401010526030302480c4119825118001c502ca0381c0c3d8039201c805a1007000700d030000e20040202c02e0013400000004408403030006084c29817080018116076094205150300242d030202030040001f031590a0340c1000b01410b052740700398510b61313400b82da90b030b05030000a10071902c403000f1940c030100c20001034030ba9107010581841000600e4980c1c0009240c1e801200151441e171040014000b02d01160213400e894400014140c41d1280151a40c01e80d848070b0101400c5640e200703400110040011445400f8880384076800149501d0101082c43d9101030703070041c0a81d20040c406180d03520b4040c1c0780020940385075215422403400796040c2030700100441e10302c01e908455182c17000c1c50040350100d91015449070031aa400860300c8003501d41d050320b001b201d0342c803107080c0c800e113041c0c1e5141d1600c480a006103400f40b010801888045011a00b01c0140c2c9901141410243c3e4845400700310540c0568 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 552513129 1250 552511879 552511901
    0x7030e1c0e090c07020d03090302130c08180601060e030309030708010c090b1615020702130501060f03062921062805011b020306090f01060e0106080402011206050d0510 74
    0x248065083c180d14a0040784600007000b481440c0104070101010301070b0f41c02000464009000110f040f40c140b010310090150300783d200c000180f100000444801200b1300900d05269490024442c036800e04105407005044c91200c00d5161200f80000784182c5e0303040100300c0140804500200c2e10030951440604000880c8c3c0040b401031805004814883d0400100d075002c0c103403c810003000bc0d003062041c400080c4240f48020390070070041d02e2004000b1120381c02042c102c07503c540d0b40130f1000c203a811040701240c041e402800040c500610b048400022031191000110320031001d00d52520b44410301d034600c40c41079134070280e0854040d04100034191031b000200300d02c540031102c812080f10140400c220340040c1c1c0390240d2418401d010780c02c02c20809240300030040142d80901160700500307140b03900b00d54407408015a1a415803c201010030502800780107903040f1029a00e403010261150790041d9180d6a40c07490203458103035118000141503650505003070301076000350301800c03d902a103070307802098410640324 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 552514379 1250 552513129 552513139
    0x18010813030c0b06040b030a030e010e0a0305100b0117091b04021c091e0c03020406050402071212140c1b0f030403060b04060305120301090501050f011707030e1c0e 72
    0x20390000309401000c0c032154150300001c54505036643d0800140148040180381da0103114281d8964105a041000780509071000d0302c03862901d0507000200204407071075000040482e04a883c107805600c209070400115030005050003070852140d01c040a6a11301c4c100c3e200c010340e5010110018140d10307000c0711a0b0340184292415450000e41191800c10600d510100800042e5108070840601101c180108c0940803c4041c2801340f0845003030000b900c0740240404e900c142e00d440d00003d038500e014421202c49a9100b00c40052610080f042510030504920740f60800d140c6070fa520042c0d60110020f42d038482d0000d1900640c50b800000c4124098090380c2d044544d00e40c0c010803040c1c1c0c0e5030310004240c0303040b40e5000c40042900301c80d9502081c0609001e80c030041c200d2040180da0a5440303e40006181a00c181d60020042e60b0b13611402c100c00c006080d104070703000c01c42071143c500004034240f8010342d2040503810007013200035000c8142807504d040c05810b090b1a4001079419928175901a840504151301225 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 552515629 1250 552514379 552514411
    0x3041b0e0411091906170f030403110d03050d0f0c0e0321070206040b0307020f0f12070308090f120c0c090606120711010507120b0103020a0c02060c030f180108 70
    0x3031086085001c402e04548100b000707400244044007907802564107403a41030801d02155542d400d8a016040f40c0c4013120030680284104190b40400000554048a8128000c442c040600e0400c2c4440851a0101078040140c2008003040c24140d50154081d48500e400c400583c0b6018000010088a881d4100601c1f9030400203c900080e925007070b10a190b00103c10f905583da041c41c0c400203000d44504d40c407000e164103020082024250b004609950100041c406464154155507170785901d0b0120212980541c0e1401d20221001c80d108400e250f0b40a03410200300e580c0500c0c080b00042c9030140da0000d40f0704403c8000741b5540c038000284541d031880442075540406134204480000e1803405a0341180010b100101c0c001154203204900b014400e0038820700030840c41c100303403400906102900c200b5800090511401004030b51081c402c80d050038081e81c1d19a641c0302d140d075003003103440d0384083c64558091006003c3c1d85440343d03401c0300a1441c60000465403604401c900009845160028800d02c00303084080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 552516879 1250 552515629 552515633
    0x60c0b060103050f0105131413020a05030a1e080d09050c01110c060d0c02190507050a0b03060d0f030e180402100903080d051e010e0a0b091611010209040203041b0e04 73
    0x8004c841c190391044801c960200002e03100c9900424185010451982c1007205100a03100004641caa24034000e90b80b01c2e03005a03c0703d05040d80d85c251032800800b03124812038602c10414440d110501c029200e40c03601da01c2c0c8080c100050042c0e6204140555180d0401c1026890030340c0c0203603a01c2c4110030902e000d0502000710380006260340c003a201004a070940c4520759100e2843c03080c001034814100050944080909508007260f54240d1409003500a072403400c0041140c034203040075203100b62001400190350100c65a50210107040c3c40c40201c0c144500f030742c45c0387d1560fa26404046da102c001c51090407020328040c010050206000200072080c030030040300c00d02c04a540c41c41150300c00511541c02003650340f0703140b40c10b52000300301c0d50142072420315502c008261807050b241c2c20b50081f011444c041c44114845000c018140d01c007981e01c8040174106079465040540524029003c5160f0034000605002c41d840100317044e0f90044a088450000c00b15600e100749000d1000f01c1c024254510a4074001c0ca495 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 552517985 1106 552516879 552516901
    0x5031f0305151e01030f031404271107020d0f02130b031b030c01030f0e070f290f0304081e0904110906030c09010216060c0b06010305 59
    0x124049014441906030f00b101c041e06010202e51284d20759500c090000003844022018801505c0c01002503200e1003000d0801415003a01404130300c3d000c03440082c813030140001401c0c2a9490f0410402a4207400d20544044560681d001c6001054908002c020407014030b01c000d41c050b032042c214408945050300300415a02050341224040c5070344404089000d841a8034240d015400340c2100c0c0781540c0301c2c0d00102c584039024800050214403900155041c070f40e480d00840400c42019a040103c84000c44070304855202c0c800d2014803020f54034090301e00d544211004528820344c0840880c080c407680e68211004260003402c04151000841d00c0d04200b42c00030b01950303201e1383c03804040c03070b403a460184120740c00313608010401072440e230b40c965403c0c40c6504102c041c281140705008905402c10f00c140340810161a03203844040e42e00c44145403103c0000d4004111a0405040000f400950094 = true := by decide +kernel

theorem cover : BRFrame.Cov 552338129 552517985 := by
  have h0 := BRFrame.cov_init 552338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 552338129 ≤ n) (h2 : n < 552517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
