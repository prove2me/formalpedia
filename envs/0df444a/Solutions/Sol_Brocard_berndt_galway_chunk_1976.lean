-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1976
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:21:51.973994+00:00
-- url     : https://prove2.me/submissions/405a1233-23f1-4139-ab2c-c6bee7591230

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 355215827 ≤ n < 355395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 355217077 1250 355215827 355215877
    0x1020a0c020f0a030209010b2a0f060a0203190504030504080307031211190c0c0504090f02030609010b01020d050706060f0b1917040b061906022a0114031b040b 70
    0xf19481c2901e03005030107070210f68200300b0102a1580111381c20080800440c11001c043e8012400d1a10302401d00005000c40c0c0360f507401c41514214000d07040030145c500500402242018102103e403038800c1911000c00c1944450506444034841d40d00102840d000015280342816040305a0050b0294551001c206000e070300845007001d400b900c0703c40608912940c030707070b168072601c02ca501401c81402045e0700c01c0c54030380e128005000c548001c281254408803031a52181035203018022154080e4001e0000c0c01003c0d403000c0000d440d00200d00600f000e200d408030b050014008254070140180c21518640d000c0c1548071001604613800c0311178074641c0040390b07140c00e6181d00d116800c613041c1d248041907250815155039640307581c20340c0000e08050708070707507014140c035500006014401300604443d0041d03c0ca6040941d403500c151000401390b8175519081c080c2c0740d55141d03402140d4010071161519282d40343e80b540810a084800a02420301048502181c08104004060014411120750802c01101541020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 355218327 1250 355217077 355217089
    0x190207081204030b180604030e130b030c100c06020c010e1905070909050102210a0606090305030a03110d051609080d082a0d06030b13080a0f1101020a0c020f 69
    0x8800c40c00000140401c20010760708860389504580f8045c20807004140350000f851a05000700c0e02640000c20710a149001d504241040c081d14200c026401e108000403080466a14121402d02d80c0c001c0100442d140422403103030f6400c0c1540d42d03025400795a01c1c03241909147c060842d0741d994813824010581401c48684103507244d01819035000c0050100380d4074003080b090083c0041c0c2ca05443d203540801c10482c0741c1ea03840d0021211110310b400038000300d00384180310381c0032500c00d60401c0c0e06010601134180040750000043e40c2d0095000d1801003580b00b0707904100c1d1840e0082200d002c1c88a4181010f01c20304030610b45000c2c1710340e6826a10340d8001540d80b41e0703090f039882e18280c410002c01c0404c40070400d900d20005a40354a01d04c141000346a40e04c0b40d038000c18080d441504142d0740d8580d10320090040110b8076075030350b401c00003031080c282d804115901d03065a64031403a0a624180245010103464060140820380a00305000008640352001e10601401e001e900d028120300c43e000c04252460a072401c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 355219577 1250 355218327 355218343
    0xb18010608130609050105090c060304110103090213020a0c1115090f0d050a080702040f0c051b1c05040e06030102070b2d070216090e07090b040b12032d2d19020708 72
    0x103210537030324010b401d00541c000c0541d880103076081a2503841e550f50000c1d01d40000c00c0c2100682e6540801030002c1d0170320076494802e0442c01441140210240c2c0b020340c1d10641910f0811308120340804099216000040d4400b100100091040c00b41c078818506110814000c1c0a80c1402502c05000c1e0301e090800c01422a02c15025090100308180074000c050381d00001050302030503030102165180b0f140070780441c981d5000d401c036020001c0c074006424000b080c0d6160032550410804e400944c01c02160f40e6443c407903404d008156003c407a494010001c040c0d441c1d074213200441c5142c0c0880f910142408840203456401a800051743d010f03440100145000b514880d8694330311505010b0018142080060720140a07003604143d40141c039100c480f0881d036034080c01100080202c60040d65070709440da0b00034030008030311010498000302d43e8030a50400c0207800704840200c00107c20130002c80d5201c01e8001c51212800c40c2c0c00b40260008601d00100109202840d03a05900035002c032901c0343c0e070b180c0075a41d4034a07030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 355220827 1250 355219577 355219583
    0x30f0d0f0806012007030510060f0503060f040f0503070602040b09120601061e090e10030b070c030813080c150702150c0703031e0905010b01030b18010608130609050105090c060304 79
    0x341944c01c0c0120599040501c9018818081e100e07015507a84545180090f01c01d82c284004c0c0d5911405c01818181c40c8012008040c141c000c0d10452400c8062014043c400600203440d000701072200108001040c0221607125511803070441d2034580b140c00003055a044404042c2c000c00550040300d2540e40c0019100d81201c0403507848100d0741015000c242c4000e03400d00e184a05110a00e900030880068100180f48100c2403040316a40003403840c100221030f07a001038074031001d007c01d2001c00800f09501100c0345511181e8a0307000b488462a0b4a00700055101c1e42a40743e4060096045a41101d017184100f140500035650031240005104251041000c50941d00d46190348010003503600024003a41043d0f5031080d80480c080505650390302e0302c4080c0d440b0918200d8050355103030580c0301c466802d80310341e8075008d0042d101c64440380c401000411403a10180104070034032881000040c0703c04418001a01140d40c0001c0a01040000b868a1070103800c0907185115a40503d02020109050640560b4800c07a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 355222077 1250 355220827 355220837
    0x5091803041e051e0f03010207050a05060702061e130c03060f05042f10090305070308040303021203010b0a08090705210607050913151205060a0b0f030c040b04060302030f0d0f080601 80
    0x1d4001c2000603224140d1440c0b86c240d5001d01209010840500000c0c09581c020b40252145241110340242000002040702800f100c50030007130071070000000d100542c05403949072084040c444609240a209110740d00c01000e1500300681c080043d403403600218003c91180ea00745400e005805660806101d071500d04000c40c05410125000038585071150300c44002041c180242e1043d10ba44490382000495042590304c0e100c001820420150b0401444480507000b40c002419541001c1d482030315441803e0314402002200c001084c44003000b40020402000010540f480c50703a0f010b6000c5003504030882c486074440c09842c0016030f8882c054402c81e061003070002c10701b80c1001c3c010b0103144010900d904003222107200c010340c08520a0040c00e5240c1405010350010700d82131a00341c26603015111420b5019005601c3c8114001168400103000f00c0c001d44222000b00741815600c01046c0100055840a0340c10301c100c180e4014241c9000c54042c2c4008025035455010f41c60541090f1a082d0044d214180025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 355223327 1250 355222077 355222129
    0xc0118050117060f0901062d08040b04061b0207090e06010e01030807031119061d07090216080f030609070e030307060f090f0c0612140105091803041e05 67
    0x25142d450342c0365000b42c008000b030031400141c401150940109070800e40124102c0c01e030140c1220210004005074040841c3c00310341110fa011b00007040203402500081c103e81801000ca010070800340c106510413400808034104204100380c00035035501e40c601c1000b48007880c1c42d0403400103580215401c2c0c180c0d0030600c81035409034a107a8614440307a01c4400183d0800070712460207060684240300c40d40440c1e150301d4041c00719841030704005003150014001030704560b52511000c666840c001c543c0702d0440d03024110040e141c010500910904001a1000070034108000a0230784044080b00069409a101030352000c3c0e1564904a082d20700f034050b00d491580c50b61060090100003091078204c01d100b500320305000300b0f01180f41e80e40c001e200b0740640000c0340e0310500d0520920403954001e003010310060900b042444402d100d030012154510042c080c1034041e58140001400750030400d00380d1101c0141c8042100c2d541d03a9105a011980c0908282c50000c03a5040306000405141090650b83c481481c07400100c014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 355224577 1250 355223327 355223357
    0xe03040303140418230601021f1410030b070c110609010e1f02120f0304060c050c03030f010509070c0201121a03010f09050d02031e0a0306090501080c01180501 70
    0x6084269542c00354042004041141205015260722044030b082001c00c1090b095000401d400d000050800924280342c403c000480ea0700240d40483c100c40d0007803600700150a070000e500948070148184400d694540140070300209010791060499000c0c0d001c00d01356031200c1400310740b114441c0300054004a58511600c4940c903100000b040b0000b030504080c0100100000451204410748074502d8088014007100d886d01078050000100c180380c0c08a089107004142c0e030f4114644d01002d040a0001b566555868803294000c8040f1400074410302e013140e8591030640d02042680009001da8ad004011040c007145015000b00100010540d058413064140c9025843c440000c04c516009060712203070440405c3d0942c5c8003072150b00d000d01d8400101080b00700b442e0400b01d01e048102c1e084113003150320030000315906406124680041c01d907040318280e0345001c0c0b2442100a4a100e402a8450500c1c1500015030140c000840551a00080e200c80c114242c494161809103452840b0380d0740803802100c1a1600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 355225827 1250 355224577 355224587
    0x7080607110709050a020d050606130b070501020403051f1b0504060e03100c05071b0b0306060f0c011401030201020d0f090b2203030e010801080105131106071b0906090e03040303 78
    0x641c4015011070380c2c0696a0900e60080d07410580301007000d00d900003a4206201014020107034045802d0398142e2030050782000403c40b10b4154031403140000404186081040400c2d01114001c5401004448180034400c00a514000c80311642108092401280f07802d4003c0c40ba0890300d02d00c0154845030f0401e40f808009483c0110621080c95042c000e212a100400419201c2c003102c0311201d9581c107840d8440b44c40d040319081d41700324440780c2e0704400c0b45d020006081c1c1501201d90000e01070743d05684443c650142e1704018015034425007619400c007100007402102030410541268003d0b402c0303480300c0358540c0e029075621070f2601013240015081c400511810500b0303001441030b19048840c81c4003910001590381200c500c1f03508110001940b400245003990787c4840b186014080b8003001700005e00b0308030000c00104110010050022266151940e0700d60382d02d00c00d482160340c0001c10001c0d4544440c088031001e02150051010140c64082c0201c1c00e451988203800d107041c09040110326240c1980c0701964 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 355227077 1250 355225827 355225847
    0x15060f020a0b04140609100b0904020a030609032114010e1003060e0a060f021306020d0834020f0111040f1206022a0714060901120f060e04050c0307080607 68
    0x245101240101201202041017514400c202d60000f405000703280c254000251844080024451581e400901000d0380d04c80c200001125070101000a501040e85002e4170104183c0c5a1419110011120561410790701d4000703010321a00c0e002801031580c0ca50002c10031022059802c0c1c0300401c8804410300001d100e80c0c0c044641d11900c58111200308003d03543d40301c00e032558200035103161364012444211441511003a07002829640c006400b0183d14208000d020600040a2040b170303001c200982514058081d02c0c0304407039082c8840401c980014040e01960702c07200612003144542c0382040c44086581a04140e601f0382d00910f0411644a10b0950440c0302010b4540090300c1c0303e0b034200035103840d010608005e103d0f035188130408480e610401810a40c00c001017030780606040c040f030010406590303032110100c4d0b052200c00d003041e004883c5101030020080a0300c0880c0100c1c1c0b03180c104042480058070b0100d41c0300301d104074100d03030315450906c00b03240d21940d40384140c03640c503480100401e201c0d0b4080e03e9848 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 355228327 1250 355227077 355227083
    0x106120b0a12020d06020d1107020406080624010e0402040602010e15060a09090501020f120f010617011806030204060b090f0411030106050a050c07030b1e0c030a0e1005070315060f020a0b04 83
    0x1740c24544030442040484410100c000690900052270b40c00b18103041c016071004050f4480584020310385003050025010301c99000030845002c40310590041d038016001c440340110301410031500c440c1c07212400f034020112150400d03400d20488881d42c1d00c107060125580d1044201070003200200d0320b041200009000c0c130b07800844040d5024000c1c50750580d2100e000d080c1d50040000401303280d04011007411070128040e0032007030400c001e510910340060707025240d0904403440782c540e01407115181041c0000402440e000207500a051480000b080c100480251407030800859142c00b0851024040000300c4a501480300e407410b805000400c040b50051020707090441607401c00503c1c1c05070300141c860900800b134008072140150b040c00d00800c0c40c03400000d03012944e0100c1008259080c8440407116500008140c18040da031070340881c0c4400f035401d100f01d0007170504001e0b0034441810800130250180450b0040740c0c620b8600c001000615a2080031200700518880d00074000140240d00c8010344240010030503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 355229577 1250 355228327 355228331
    0xc060f050f030f010312030b06180f030d091406130306050705040305030c030a0f0305070903020907110304081b010503010f0b0702040908160203071d0c071403030106120b0a12020d06 80
    0x1100940e40c01c00d009620800b81400b40d0b412541c114500681d10117114100300d01054900030b40180b880d20740c071007181d803458105489034401c071941c2c01c0043c4140b04008143d917058007503880d940d030905411290b000300f030340c5a03821007000300590201800114001c1e5504960f442407980e8082012485951090b50458081d180203444c0c161643c0703c0e5403a55210341c005a40940c400a021040e070340d03112110090f094841d190901403418040c03c0104040e0b06804041d100b501d50300301194446015025000c00e8141d100152178644d81d4401843d916a141d4201e4040100551603207400150b00c144100c9040c1c0703c00d580031000d50f50070241c218490390811038007240c005a990700310030041440c01002d000d450b845501254807480300d5105140c01d103e1680c1c0883e800f0400480c022030030076032800c4000d500c41114000c0070b4032038040c0d09041c0d42d44d9680d1209034140e4040000081400da502900b000b0440c900603006002c07101820f414440448090320aa8081c0d8203070200c20300061800c04800b00b5460700840c80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 355230827 1250 355229577 355229587
    0x90e0a0203030d051308280c05150a0b03161e06080a09080906071506080304060e0607081303030203040306050c1620030115090e030403030e09040c0e161b0c060f05 72
    0x3030f40c4a5030340f1003902c80c5c00000308002c1c0c2c50707c0b02c0c0240c104800400c1d117034940020314118550301c066507580203046540c10504800f001960056081c4d211841d0000000c1c111504020940359602d60f80c0d40c01c0c000c420210b5003c1c182494076a1400721040c0c120f529565840c4040d50303980301700c00010501d004007101c00710000c01400800f80c0d2060054940240141040765208400001a20403504a68080350b140d03001803108202480e0401c92510342c02d94161446039071800d80385040c414602c0380c0089103203a580b0540020052590000180003507030300c1148100b0031500c9030480710754103000d240101142d104040d000040040c82c42c00104005100361010781d00120036140c00a820350360312940c50141e5840f079250400950009014240c19050818080d61603d403c6840090150f080d13010307018065605017011030100003488156900404000824903c41d003040d03070307903600c1c10000507543e0070000781c0312000f441c0d10300482da17400401ea6a0100100c03094610700801511410160f007080c9007404021b00c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 355232077 1250 355230827 355230833
    0x911211204091d060601051b011802150c06070522090203070324030209091e0307030905011d091519030611030f040b0c0c030a0306090e0a0203030d0513 67
    0xa03410305441200c069440e14107014914007182e030f600c0001101a400704008540c0c028002c9001c036080742007071800743d555000290b4850b80d10110050310800c60342c603029180400711211241c0c8920a0302c00c8450a484640901c6c1c140c145005060500c48243c2105002ca400b4a000300000c096141c2d483c0c40c003842c589660701c2c400e0045010340e8020700141c0c0d000020890502da141c414010516041700c030710590110349042c3e00c010f034542800300038010140c000c0820701540341040588400c1a4208400844010303040605840e0b802550044010889120021a00398064070001909030386001c800c20002144404204401d04051b02000c031b003c410340068074440d11a044408180000c030401c00034040d00e90701d80801100c00020502c3c2c1036013002e0040c06a449044c0300e480b500f0541100c86204144c40300d61440d440741c440d80540545920000030a13206064050300003004544400d1000c00c1404201030300b840e01c0b80c0102200940c9074108004441c4501010303030005400072122080c00c41034204c296 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 355233327 1250 355232077 355232083
    0x3010608130204090507180606020c09060402040803030103050c0f090c09090c04090914120a0c060f060509041a010801110f1e04080303100807030206070809010e1306030201030b0301091121 83
    0x440c01d50756034001b004144528810243c0701d102e03000001300108039503031420700003d495100041d807442c41078000070301040e035a80d51501500e028002c5041079940da1b50752403418954032000c2140303a5026207007070340c02c400c0145003ca10345072040d085a0000e614095424040080240f001066803031000f4084c0070100d04000b640c4a0b15120500c0f44071054803403070005007107078603091580c01c0300100140c0400200c604585d11509890b0b48a80c400000305060082d9459400589040c1d00205c0e0400c00c110104814440c00c020254515189a00007084590702c0d43c1d2807a0990b8070501583c007000e002005800ea00000c0800202641c100b1490414414401d5204e4400103078040d0744880d000d6070011040c0040040590803250080c400e000080a8052a5034089882c500480f04050085400480d07011410b9018540c19280c400c00200b000b141d028804002900a081c240010780c00645461420501420140f260300307142a0454910400907e1000800412004040d2806034a00700309801041c010420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 355234577 1250 355233327 355233341
    0x8130b07020706031406030c0d080d020f03070f0906050a050d020c0109030e03060121170c30070c050603100801020c03030a0b061606050603071802031b0f03010608130204 75
    0x395000e00011807900b5001815254482160080c00c51084180002c40d034001031110f4024000360b03a14407130400d007402c00b400c5034018000c10421060002824002c4184128025449642c1c1a242d000c0c2400184800702c8890009025000104404001985586000e0302c05005031066119026182040c40d440990030b43d42d4401e407c402181d010002110b10345828005207001d041c19400540100c14034040940c3c601c0c40340080a000810303604020700780c0b80003a03000c456912820314201d41e0401c1f0f6000c5291200070b21402300050714500d440070051080113182c200d80c0200c1c0c002e100d0044083c181010800c0070743c001390a82c00540c0400381d000405d442c00b07001a092024403034014546a00e04100403c094480d1981054418174040044501140ea028074a5034159042180050282e0784d903000304e45086503580044201c08000300e40018110200c0e0021031180b111043d03005022102d2680300d00950060601d00762049400340018413a07603102d550703285d521078401088680003030b0044d008102100e03d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 355235827 1250 355234577 355234591
    0x11e0515130507230a03050c0408010509301b07030203060a1a0607080304142d010e010203160e010311070b04262a030406050c060601030b0603010608130b 68
    0x56008103c140f0741c02c500241c96164007401c85801c0b000c400c40300000a482183c040d60300b45a500d90215103000c44000540e00a810068000c01460514441250703a50741007010400f84050081c10541042165000241d082c0407440402030405200e08021a040c08258459051a2042d0303200000035070303000c002c3d203070154014034000980f5440b5001c1142c2c80d02480c0240e5400b0318020464a00020381c42e0f4110b91344140c104104100c0d00c802c02441c0c1d810170681103010760200340300000c42103810050052402090200100030003528032440c44003401d07030004690320100000c101103035a0b0450f018080074018540c05160001e60f150b01810511340c41d80050000740d5140803d401008200011030b4004070380080c0c5502c0008003a6a000901e100301d1041c600d01c403010741511601000c2c0c680b500b001620050b103504054903203403070b10b1f400e0040080d00842e178550118400e10000c148294045c1c46151540603014003402e05c1c0d42e0070050180c40043c0040c0c08001413490124050000c03030090011140101c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 355237077 1250 355235827 355235831
    0x1802060714011118040c1b050109171201050307060905061b030d0b1e061e040308160203190f110303190207050a060503090a03081306020406020a03090602011e051513 73
    0xc4c0c1542e8a400041a040c0e4a0186280c03d070700340c3c2c1458001c846605014900482c41140550501d40140904094200101040010351006a0000101014025018100c1e402045681c0d0b51010581d85900c00d00c1030354045641303180103205500b010001040402c03d0070000c1a103c2960407461490b60f80201c0d24008001c5d99198014420f02e00000c5805c0c0030320003080264100a205e00024003c1c1c0316038800111400712901d0b030380400440140a0310021600811000d40318042541c030000300100034501284079005070104c0a902c0d03c2c044640c0700806400001c0c00708046031942c1d032448004942840c5941c184024425888a82113808444840b040e140e406014034620746002c0c4200b2440c1074000d0024040c091040000c1440001410000d072501460070080039110001e1408101000c190042d0030315000050100b142500050b4107210745101c0d1b500d9808890365101d04900325982d83c6213020f4a000c1d024400440c002680e04000e07000340c44245940e030803d042c400003c1141159a0f0080301c526 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 355238327 1250 355237077 355237087
    0x61912030f121b110a0b010905010906170a021c1e060f0612060504030315090c090b03060d03080414010e1e03130605030a06091d0d0318020607140111 66
    0x10780e0200039242000e4610b40c05100140101c8182c504481c07680c03a4070810407951a00503e49400b00300302c92403580307420005050095031141c251602500c0c090141d05981820070704001814176030355210861040d50b600190070201459402c00c20000340145031400e500740520350500c085041e031503c80d1088042111031036502d034401d28010094490383c140070b905161401c01c0401000301c0180500b00510380c04100003403d55220702c2c00303400501078088809401000014007203002c10303440c0c0c4403141582c05611009119607484440103040e1204540c195000843d440b5034100180c06056001e03089407007003000c050f0060548400302e0071142032900050959005c906000030011070803050a40b40c4803050040e51800f150200141c0508035107101d81c1e020007000200284801c4000e6111602512407040c6c00d200141c4e0780c1101c1c080d1175040d003200415900802035060301e140e00a11518800c0342c0501030191000c0310940810207641c0141000307403400a9030844c6665001c80c00e228000c1041c83d102c50f81500c070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 355239577 1250 355238327 355238357
    0x60c0f0b09100f0b0d0615080607111605060f0304111504060908060f07110111070606030219030b01050d03020c0306011d070201062103050c1005060f04050c0306191203 74
    0x50f60140c071548400c1c2d482d141125100d902c2d9a40c40c0284503800440220325130182000c00e580b450442d520080050003402c040c000100d41c00440e40c2140c40241c400c0b29401c4a580789580c00341c1413180708a5074092003c000d00b20481c11210050b5038045e004141104480750b0f1000410310718200d0128502803000d00180511070360b0b13005042c600240c043e00b8010039080c40c0c0f244502440c01d6001d0920818040e04910f0000c081009401c8002c1610703c2408940d1500c1c1245041809014140070407481807003103a064800c40805103945c002165044081c0c00d40c00d07440c000030300c003801601410070340850144105041880e10100070140c024a40b505100b0341a1580090313607643c941002c0c04080841e4100f000800c91903e1721b0004241420a02046070411030051506a8084c0b0a0b40400109400342800302000902c103548441d106076015100c0d044028005000c010460303c0c100c0303202c440200117001007201418828510321142c21183d1090134040e4454400700c42f181c060340000c80000d40c200d00e4981013 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 355240827 1250 355239577 355239581
    0x20301080d020f0a060b190b03011d040c09020306032b1b0c1a280206010503010b030604170c03070c0302040c0305040b1501020322050319030801060c0f0b0910 70
    0x800c2030644050800e103c90521040d03100c00b24018045c01c0c45440300105030a40c1e4400c030b9916580284c54006c1414540d8501031180c1540007449581503107200702e5440385021911000d17007881154011250102d1130704000f542802504041d041d540c1520500ea580411550b81d01d14507000038941d14002483c112f03080c2e00080028148600118141d40022003c42c002a05090303003030306855288590f038884182001080303142d07000f01a12511a1600c07c154140c01044601214000f012140d003a10744607a00c880505003650b00f0603503071940581c8110009000b04000b4031070140c40300345203000039144c0408580041d1445d04004010b40d004d10a40f001042189800e2041d41c00c024554102440f01b464180c803000003182000b01094a4102184040d01047e031080c0100d41da03124140c0d940c05440705001d0740d8050607415a00605010b841038002c84e1040d140081e004083c201d5042c1c0c0ca041c46030b824258102c0c1c0841254004440d404010107180c40012203040c0035a04c41c80e0f149000f4607041c400c881e5a40c00b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 355242077 1250 355240827 355240843
    0xa030e0d020106030c090e010f05180c010207150509060f070b09190b01050603070e040f1509060b04051009080607030b0910061d0d05071d0901061202042a0302030108 73
    0x1041d03a2425008000191036205c40c201250042c400000355a103a070702c1918090b0080291400301545041d0400c40c0307104012031f003441ca41103008200e1f0020481d400c010ba9540386075018a190070280b5070741d403200d0240b01c0e000070402000d01404603070420040036401d0b100c903001020100d03070081c07c1e1030401c40341540130411170b2040c175600c0200c00c076210059121440d0310f00741030041c2801039200100040003d4024500c2058090005d4000c01110000d400481c004051410300c030307500c0381c500307100004101601c3e015a106841d5810001850030381742100b081380d11103981010105114011b2000a4141818001144502c510b500c0100e0300440d00c2041101d81c20000b03200503e105007800040c8003807640480700c1703402d044da580c220450709140e410009180100c01c0340c00408911500c0b10100704454043c580700301031640c1c01441c1407141c6480e1484c074281d0344a0700403402d0038005007034441c0240c0740c6908101ca00a000e156500107416846509148094141c00b091300440e03000001040460820040c40e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 355243327 1250 355242077 355242103
    0x106020d020c0f130b0d05030a030b030102030c04151403010608060a081b040c0516050a1101020a050a02010807030906020d0911030c06070f0602040b040e1509150d0302120a030e 78
    0x4141c2c1d48040000a200310801e4800c0c50140e494006511001c044940c0504030081d0001c042c0b0f6401d00c02c614001d9581d502c00d113400b0002034205110510641014002e030390040841101140c10981031024409001e00b009100b0001c02019102e2000070100460045002e00401c2e0303a80002881d10005108180c502d56200d450a54000c500f0300d402c600700c40c9400ca62045084401054403400c0794000c1b0360500039200d9400c21858541c010900f0840005074592400d8401e841c210f54501ba1b107030040e80c4404540501404682141400800640c803440314240c0c024100d0400091000f500e40f41c42d0201c0c0c12540d07881c150a59030b03000d4213050040c1c8107021018200210700400d40040b664002c1100c6004021000f8940c40b40c40c003070b07041002407940548005e0440c01c0340643c2c495130303110080c1c0701c4d621064a191242050003001a00b07103017050302c1d100c2d104000c0d0800f801316001d104018881e003101040002d030301718010480c250f030100410900800c608043ca41d0f001c01d142c1240d80105041c001c03400c0c191 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 355244577 1250 355243327 355243333
    0xf04030b060a0b12180d030e010f11030a0207051603060b2110050c040302040212040605090a1a0604060915180605010801050d0f050a150f272105030106020d02 70
    0xc00c41e80d1040ca007151005001031011382c00b1030700c13106411150b07114141000080b81c0107034003941806503450313400038075030703071522402445040340d10400d42c000c0300d035190211100000c08100040744161560020880648a407044490704913004141c0000007906030030480d06103455040c284a10714044004004603030401207040c15400d05202025a144041202080902e8981c8005100c0c081c4c03101c16600159000360003559207020480780d040780c40d602110100c40161501000ca031680400141038040143c2c001503c034140380414203110711054001f80f406511948070030003c14040305a0150b42c001c0d00c0203000e807004250410040c8680c0d40003a04243d00c1e4a483c4c110308200b962381c04402141181e80550706441c840c80c09090030080b02c41c4c01d190203029441a00b00c0c1e02c04010f41c03804a40c00622044400304214640007244c2d200355508084034013440850300aa601081026011030600c2c144600c0d520684044070b90f405411109844000101049000c8010064950140b00f201142e0600d0320103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 355245827 1250 355244577 355244579
    0xa0506060313050a020907230c0d03020d15080102041406030f07050a170708160804050c190905130308060108070c120516050f010e2e0209060f04030b060a 68
    0x81005400000d09100148514610a1090120a0080c2c000d00c2d03170042c290940301d2030402d10140c15402c85920303005a640c4001c401c24400e03004802a641c10502c0d03800a450340074004001100a504003a14000845580c0d60b161520303080d4400b040c00081070003100140e1500d10b004000b44c0d42c400d40c42141e5000340020010088087c4e070304c1040c0b0b9400403041c10b05980726482d0540464880c000c3d40c510031000c0409005101115800442551180840070f003440c04045002004840c004c005840003400341e0b02c001c100c13107801d1522030030424941082c04042e9020744d45e90194241524001e03602142000c140303154150a1560018000ea071040080c01c00c40c0190401600080c07048000f440c019010030f403030b901c07130920315481081120305034200e00340c0c8000049410308040340c55091510b029642c070340ca0505000010240401c014015182240701010380c0c1580044a00809800c40701c642d0180303600704404103159a4140147c481d0b01041206a40c865003140b909650240001d0902c510881c0180341c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 355247077 1250 355245827 355245829
    0x606070213050406020910030b0916170403030b06040b070605060901050a030602030408040e0f07020d03060b0904090804150503220809061308121312030e060a0507290a0506 76
    0x1c580741d80801c401d000090180d4690400c4002809a81e03030040e0301c0f11820349000c0015a0641024403036070011151498030740c0f0f0b011580b80c0b80c1d02d00e03000c200c80410300f8008580c410707408080e032143e40140070381404103405049000059079680300781c10800d2000c2021400c07409106192150b250301803402d55501d0034550400001620190852200810340c2d80c0000026080091580030f99004241401c8003c1590403c80103103101044101c40000051080c0b00c5001401e900ca8001e440c2120665601c40b8902240c10b0107002c0641950942541e5192080000040f41c0c602d80002c90114015541d586442e070070429600685201100004090818004c1c2e0140108180c0702c102c820aa100716410360361207040301c40f41e6200b20340590249510b40668017081805c0300d92800240050034021b08100d80641d00d0307000d0047d404058807009400155410042101070518100030101c005507410801d040c056030f0756030012006000180300340c0c507188181e07400c4030304400300c1c01c40340d04039403900000d000078a0610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 355248327 1250 355247077 355247089
    0xa0e07050607171e1801020c0301200a030603080d2414040518010e030a020c0301060b03010512161e060302160b07090812070b1614091f02011406060702 67
    0x4100035480b0340c000a041c40540100008050a040d4080c0d41940c5134103140c8403174540c18000c1c0900d14003502600b4240701f034a14061081c85822030301d070945011600d402042ca0941a004031201c0801d05680d804d0200100d0021805080070902e00a00420b01c88620034143c44826001c40c6510200480050b042c040f48080410004020509407000907280d40c4a0b61141e08000311110700b56515407910341c0032419040040014035001c0c80e00d40841d5207500d522007d15080700c01c1e80c401d40c070348404244010700c90b52808000e02a490030402d4125041c001e07060b180d481030000142e004240c1e410781c091610000d54180700c1c074200240000d040071401e02158540d0000840c0d0501001095402c0c45000144101e028105034800b401001d4101c450790f140b00d821910300f5910011050741c00e846510005410044640c11261031007000e90f88001903c0d400200c80d03a599013290244503800b1a100c044450000e1004031002c2d50b5075490f5001051000518108a40b03414000d0801c600460040001c200961100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 355249577 1250 355248327 355248353
    0x303040c05060d0f0c1215080303040b060d0b0f04062a030c0201060b1305030106050301060501020a11220c030b0108090a030e0d0b1918120804031202030a0e07050607 73
    0x36600582c0d5400f2664442c0300408100c82c015600038035004044440c5035002c4808012604402000c02c04403070505808004000ca500c5a00ca0035401000001c00180603102da568208002a0200303090016642d0740c901c0200c0216400b9580303043d40d0b01040140460390044402101d10003201d11920785c3e10f080c5288003c81b030181d10000b4140c40e00c4884004034400d500040c000c0410703510240c0c032089600088140e86000d48541442513003440302c049040e207010700c503020485605800400c0280c48982d100c1c0c01825003144640d03401003941d000c510384200a8100355404a10b40440020a2003903610081d0444030120203d170b04000440c0100040ba1074006840d0310902c5c1c0605000c0c100e807009000103403000c103001740000d10303043d0b0400034801c035250130300700d4001007020205050060b0000c80b010400c3e6400b002c03001034560344074100101c00c9140140c46007500301340203151580c6056405a038180680e84140c50b00061969920150040304a040c05228045c3c1070072642e0034a0241d040d2038400b0740602d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 355250827 1250 355249577 355249579
    0x90e010611070f060203090a0e0610081b18030f010509031b1c180602060403141c05090303090106050108010f1703040341150901020c010e1c020303040c05 68
    0x5288041070301c1e6401040030400400c520031410320708030748440c0700139120b400100c4840d008075100d11000c20030004041d41780d440744402414442d92100011022105680c010300300002054080421358404083d800c0200fa84a40d603480740824003003004207251a215103200c107440380b0703450941404822003002c0304580442041c0074030f4516a40701818001d0030315803407543c900c420302030500b014240283c12a54220b6034140070200c2400313481c0d4a03242a40c403004211001800600701711184102038001d1809000360000d0481900b0070403420743c188204503441030700c0514282d800072040240200003409001d0142c0001c6c0707030000640d49002c60540300303c0c06902450128440308441a5030032141002034a000710780012001e80004000030114111140202035000b00300001031402c1c0c10401400c4070301034200d401c400201901c1c0450003021114002c0a01314002a540030011040e84090900801c0c6c041d400f01000707403061000b0f0307010f400d44100e008607010382990000c1c0100030214240c1c000c904c04944d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 355252077 1250 355250827 355250837
    0x705090601030f05101a03010e01180902130501090f020a1d0409021005030a0b06070f0b040c09060b09100c030206040b0c0d020301030501020a08011a040521070e04030807090e0106 79
    0x55400c0181c01401c0a020900020351a0108110100719560500011900800c1015122100144401c60760f8407090144440b0749014900400c540010042204800a41500e000501c01d90031b0780090107282c05141c90084d000d4132040140030710360203440f1b42401c1045862003146401801039014011049043e00c0074a00c24000c4d10001880d00c41d50007602205600a00c2803c200310030500c060050780003030b9107a1800074504940192941412411a18265013000400c4054123003940e0700c50103003400500c1141e684115610001c0e88058600030314010b000030303c19668440b43d082d014040710021541d280e2003040000c030080c1000c00d8000c580f2a80203500802c100203155511201d20556104601c86000303442c2c4000000414464198040c280104441d921400141d0f81d07111a040140020700c07d0710403404040004201031b141c41900107015041c0540d01c3c04840c88080101414203410b6884602d84a060074100410991f2002c0304070340c072440900b0000103241c2000c800c0c5202039014001d000900ca = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 355253327 1250 355252077 355252081
    0xf010c0f140d08060108060604181409030a1106060a03021c02190603050906010302101b08070303090201090e0f071103070b01030302010c090b0c032b0507031a0306060102070509 78
    0x1103880c140320306160390007540c810041e00d410595190b4503030900300c82d44002082e503004034a4561044000c1801514001c011034140f905184c04585400280001003c81a030340b01c03403502c258a80d4500302031160041d90043c42e20352422080203400c2c0c0010705141034054002000700500d550f02d0903000e105898041c0c800703451050400704581804610890041e6000030310038a1101400c0c540040c180a40d41c00b680d0501c520b4035400180c07541c44000b800001d41c4031040c9821003140610444403006031040c2c001900d89c1000301038494018940c4100d0003500001d442e040c0000555800002c648000d03c0181d03005406031901100040d8180e10181c089410480e03401c1316020901d000b0000c0e034010070741202214444d540e50f45030103030003030042c09001c2c00801c104034800a0160303405801d0300c0c403114034500a10b00d0200c40d140300c441d01c0c0b101210740101403080028080c02008641c89a540b05800f00e8500054544d8086a18081180c00644007840303640003004001d626607010580c4070484100340d8203000700c0c2e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 355254577 1250 355253327 355253333
    0x20c1606082e06111005151c0b04080a030b0a1d1003050c0603040804031401200702030a110117040317060a0b0d0c1110230108190501020d050916050f0f010c 69
    0x48028209022454103007001d00c503c010803071060f07d01d611011581800c3c600e41d0b5400c01003491400243c081c082c1008031002401080020b402884841440d1400150b030200c507000013070000d0343c6604000e8a400810104052000d071444c00709401242c0000c1f0140d510b4a1541e4150b0740e0034480b84410700039800400400e00b00480382080c1d501869000350342d04c59254040e42c10760700a00034083c00c02000085106003002e0151183d044590464000d009003d04010b2610703100f64010a1505003410403204102000c4440c10500304280158440d81d00c903e014006150500c0555201038489882000c40c208204a00703c2c1c0901110440d214140c0301040a01e007150f0140c4000381e040d46610b90741d000e64000a10809456400601750840203501d10600d116506518803601100340180e0780c0590145007446040b9110381d00d0500341d00d110b107001500d0101d0a182d61002ea85c0240c41c60495941301c0c1c21030342003c00b2071000c01c030003a020a81d01d402900018000149520210f030110301e040c00040b082080034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 355255827 1250 355254577 355254583
    0x91e05030304200904061506030204140915030105040b04050609060106080f07030f1a15031608040f0503042c07020303061005070516030318050306060103020c1606082e0611 76
    0xf4515005040d01c145103132504141700504541446451110801e0901240030382c028403c0d0b0b01540c000111110800e151038081c0007007e40701400c01c1c4043d11001d6981101a9800d020712403050b841414583c28504082c60003500e00342018000325020303001580140308256000041030b0f030005070300102101d1030b2140fa90582c0244010034000c01480d00b007020100304c41d00016540741c0740c010151803110046c0306501c04102a400242c0e40d0755818011341101c040e0140c401c0140d250458010b000c1c0500c82412951514a10362044d4444104042c0d8440070039070300300d10156280da0504c0303411088e40c03c904d04210000d481e03201c0100114030440c440c2d080c04440301c0c45032095405480e440812242034001b224a6503105001501c4102d0010f0042140d500d01040002c60726011140702400802c2c15445140055000e5001354500c2002403088c024000d11603107101c5003010040c0706c2900c5401890500254084076032480701c8003134414810000407140f100f1501d071030071000c075007840c0380005004002d80000e0341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 355257077 1250 355255827 355255883
    0xc02030d230a05030a0203221b06020a02031903050d090c09050109020901020a120c061401080c01050406080a0b0d02040c080103030e0f03070515220f0603180b0606190201091e05030304 81
    0xc0c0402c1c41910542c104175124600741056500250348000d40c84d1307036070ac0407a990451041d00039050307004800307152580d011503c440c820142c441d04095041041440c0010101c0f800c004068603003a500400400c44681a403103290302404503000e007075107440c01040c0040d581d07030001540188001c4c001040c081125200c3d0302e802625550011040c00700ca450540c142601000c00e014011701d5010300076140c0300c41d6014100315400c070f0b01c0c4c0352106a1103651356095440180f604205d45904411464080401a902c0e03106101c0b0041c03413516001c51030350540c10020001000e04014501411240c1c40d42c41da5541d0000c2c107201103820480d09299444072041b0140c803130380100940001400c09a140807000000c0588600c000e03140030301e100791481030391410100c0544060494400e2040c1c00d0848903804103480410b5241e121401501c00d80c42c002e40c0c1c41c0002c0612031510302810043c1d54400280d0704101c00c0d03035404c180c0210300500200c00f82d02d684d250243c9038880a00014000881c80714500e50603030319500c4c545 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 355258327 1250 355257077 355257121
    0x6040b0d0f21030506090601050c07031e080703020609060106230f12040b0906070c110103150506040801020a14040302100f020c1e04200313030c02030d230a05030a0203 74
    0x2e120240c4420081c01a000546489106040c08000640954411020354001e03112200040c96101d155031100070b441c1042554072408401e0755056040071800c10030081070002d00c607078010300040c903154600b5401e000068101208000d10403400b116580488550207480140300540c0580e00c504400700c2d00300c4c61052a0741403900f54000410402840552500c07184918080f406441c07403591210000c0350080908bc50041c400c007988141482c0c59480f940c40695000034005401c2c4480b40c6440004807180c12607400303005580e40003e50040b02c641e02203803110488403088011402c090840d0b00040040b0712500784d030307010070039050100d8001910800251690392005400c0005a8918015112030110605d003000d0181c1c0c101010310801d42441400003400e4150f02440c1815900d502c650800340040400702601007005911601025990a002c1c843c0c0004250310740e4000d10005003501440d01700400342c202e009410a10080c44c4aa40100483c0d0744103825540041e52551a043c1031000086055010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 355259577 1250 355258327 355258373
    0x2121b1e01051008120703031109041103070f0309020d080f040e13060c0c110f060c03030109150519064a0d2315070e0906040b0d0f 58
    0xc4080198080b074090200b1205400c035044d2262070181e5100041c2da545d00c64840d040142c01d01280c400e80c88040b004080d100242d140048079000141074070b110644c545c400351710000c148030585030460b00510014400d410280026201900042c0c00d480003c40050f2280e4800200403805e00560407c8402808140d4a0354015080022841012862081003290310501e0705480c0321200d800b43c8500c7c400c99501c02d086040300195074003801118055000c403075402c000300f80034a006c024002c1c000745011f000301c80e42c0001d014040d00301c8001040280e030700c96401604400c00d00480850507608940a54106040c002201044d00310410201c1c13012042007025170b00344050722420143c80042c1010303251109101c80c1031414051081002449000000074500201e9103500701c10040d0f4448000100030103201a20f159000e04052035410a104803040b01c001960845d20100c2c3c0d1800000c0b00307401c807070b05030f8041003502c20510124031194100e10000c1c1482c5440c1c0d04030803c02606001c03c61103500a8a60 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 355260827 1250 355259577 355259623
    0x3020f04090501140d0b13050c0d0b04121e0503070e06040b0304020111030f0915040509191b080103110406230414060d02120a0503130e060102121b 65
    0x400061000b070051041c113001c0504002d01514100c0800051140c115040000c1602c2e4610076081c41c00c004a01201c8078003450514000c03d55a4542d074041c42030260003001103514140c41d01c1d4421440501d40c420501545040c1c0e0361868204c000080c4400d03030141481039490322281e03419208000c050100c40e900203c005404140402440c5c042d60042e4801c0c8c86201000c0b41110295449000b20b03416141e0448081c454140a40742c004049040c81c83d010055518040c0c465010510794402160140c1e40344503030b13185100c02144144950980480600c45880c1504103a031001451540180320191550305140d501c10359550b00c950041004006880d041080e20064031005040b1424060380720380701e00d140024005d20030200340b0003a4425180101188109040c560821a1142510300090480d1103072060481c0050030070030045c520200e24807070201d0024a844c115992101c0d0041c2041d0454021035000441c0030041e206031045007500c52070042000f5000303450300c1d1802c528003102c21050400004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 355262077 1250 355260827 355260839
    0x1051e0406091a0307060f051e070f021005130b031e100f0806010e01062001020304080306041d07171f06050306010b030103031d04090503030f0603070807030506010b0a03020f04 78
    0x2104510040b032506000303c000502d0001c061311610588a417101140144210711500c505ca880141a104518003d00c07400a900c9100e03244207800c800e5041300c0100d12140a2015031078031506a282d040018031f03140e8513004486c40b00220600c0103200c1e0b07540003940403001c10f80c60345054800d40407240750034000c02c401c2c7c075100840304e000413401e200304012243c22407004203003200e000c03072201c0c1600c0c84d220f410b641c96460000300b180e040680c88100d801c2c8203461903003079654103020300041d4040c1c0e0041c00c3c182d4490418500308821100340c0206460002c1c19240000c510381d9000c502281240d00c56428a0000b610a00101d030400103c881e2141c100001e182c00072600e41d01640c030020658205404491280c1c0c0c980e40c100350781f880280000f8004c614010800c49141c0443d82d4500c2c0c052401404c0030644110716581e071461a0000c1d0785007141c00e64001d0400c0390702e0404220303039001041c0d50401800158610f880b0f0580b90710041c0244c41c0d00d071304001000300440e4003a0b011645500c11030030089a403039a40714 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 355263327 1250 355262077 355262081
    0x5060d11151c140c0a08011202181501090905060d0201080702010e010c0c06050106090602070b1e04030609141f0209030a0203030a050c01050108070b18010309020a0801141e01051e040609 82
    0x100442c50b4031002c080109001c90216010780c0d90301c0031186c80740c002e13590900c15000c10302c003c5143d04030385c0320a00c0740d034406145200358085405038400d207070b01c2c087d2440c6010015291458507082070144030726000800c4280d960300c1c56451242c680a00304148661103441c000c83c0940385000000003650700b0a001041600d500524000885009000420190340c07620f40444d5854000d01c1450010391040c041401031803c20f000800c6403003164021507000b00d42404481e0120741241e44141c07807060ba601010401d20085100c08a201046040540403842d9001f03407010122414404182d047e5601182c60aa991010092001c000b6001021a40c03100c4841c1030045c01fa900802022a0039400c0000005100302c000074410140c0b140322403c0c40c10001d042128001c0d08801c0e22001d0304154881c40c0c118050303110a007910300600301c5030300080340140490815181038a0050034515064001d000e6404503201050f50340340c15200106e4044040e258141007015400014018440d401840d103540010465019 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 355264577 1250 355263327 355263341
    0x608060c0a08090c0102120a090815011805042307051c0201170402092d013803061c050118060b0d0203100e0316060f05060d11151c 58
    0x5a510340c88030780e4483d240c9a484101c040c2102d805a4071000c1000e030f07412503c030054210031019141c08261640c1d075511582c5889200200c080c0900c03510300041c0a02070603064440c0703079094080d000303201d00c2c100340e59058000d00c214009884403c1702c0b4031104541c52010300804000b40f4000300140c150715260000d0071510744c90036600300d0100d081140c02120303010300015010702c40d0740c004041c2061540c44920140c1c400b401c07181030810000021852490050551a07424040c00242807808071103c54050618221403110074070b450070410811a0031a5106003400b12540302d082558210b44071403040c2c41c0c2901d60b44c04080018801c0d400e040034400310409031440c80040a000c0c1c2000c0c48054107010a0065124111a02a406400001c0011101809031b007081d000340d008a03003180d2800d020180624844545040c0442e02c494450301054150b1009020b0311340c001e0dd040720f10070300c150583e80d10017035404015850700740261516004a41e9440d9001c0030303126a5400380b1079580721b104801d0089001003c0d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 355265827 1250 355264577 355264597
    0x114060a1d270a1508100c0c050607020703031103090d17040510083c06031903050301030b0115091818050c0a060305100e090a020402040f0f092007060608060c 70
    0x244c140403143c05402c04003024200c90032a0013a0000c400d0015600c000344c05121405c030700b80450030107030100103001001401d1045010b40e025000b40d07821450002c100b0314103051142000c3e4402d00503012180e855080e5900e00a034403180c40c400c1095a84840d0165000d00c1d40183d6000da0384c0b200d000807103600041000d2107503095010841c0041725600301c410400110034683c3c0049150031101407076403083d0340c080d00e400c12802021122035466401e5400c002000c07004040700002c001200410404c808020f040f800341a40d81c5d030b030a480984400f00200030241ea44901451503000d184070140074040c07940540401d4028042d000e0103042c840c1000c5696924068403a40030b02c04408001800f10700c6440b80a0003038244c00f400004bd6450480603003c6c5900180000301240910520000140d03240e03c004d000070105c414011107038038900903d9407150001603001d41403044c244156503c0c80c101101040e5220202c2d000703800d44070000380c00c10b64002d00042d0003074021445a0130902c890030114101030000d100d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 355267077 1250 355265827 355265831
    0x71505180303030408030a050a090501051603140708070f0509090a0902090601080c0306100905040c0806100206040201021e03130605091512040b07050f0703080114060a1d270a 77
    0x903000185682d0f4401150f000d0b00b104024408102c40c005941c2110f50403151641d00070a20050685035582152001d48015101900d14110703116103c0d018000d92040c109001816003c5103095000a00310000c010502c100708400d00303c00b954200e009400344c1d11401c0e4040c00b071403424a0500400340007000c003114244c1c400c080105c001a031540c07064017020320079010300c45018115220203003442202c2d108243c800c1e050155180c3c021640d900d40e032045894090080e0750318035060500400340161204900c0701c500843d00503504002c0941d0300001c0c003e006205203007002a003c140800030702e00f103024440301903031280c15600c00000c00590006c044c0403060001c4400c1e8803511141080081284929081c602c00c0000c1c120001d404203110003841e907071180b640e0610324902700082c501c02c1100c3c3d000e070030118080740e00d51006000c0c8804003c007401d10000c2c00d4032021b00e000700350080a010443d1b026420f10503104584000765003619010020020503c2c00c4884002004208200c40e0101c50308451903d0194 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 355268327 1250 355267077 355267117
    0xa12060b0409112a0708030d14090a0b06091506130303030c020304051309060603020a0807060801050f090f04020a1208090f0328030c020604230102010b21071505 71
    0x201001d001c4903041810002a0b040c10f06110f11040c82036141881340e4186406040c030001a150000d000501003000c00480c005048800d01502e03428041c1d01601c1c005595000d036280c0700000d032041c8405a0060000c8070501015540e520402c028580340307912058211a011900104c107100742580b44c41035a02ca600e0511064828030000c9903280101e01c60309900c0051039a2100c10100c00e03602a107960342c054000440d03003136140e0b00418051940c03688140c249a000300030800c0030aa2024134a40500000c48042000c40c202900264005501500c6800c0381c5841d0710100d421580c3d4800380200425031002c44214003055402d240d91a43c004400541c042c41030351625079828030340440d1001c1802000c86040c1400b8281075040c00d500011490300700e06000807400340c00c2c0540e94140203800101520201c4600160305120390b8442c03030b914611901d05580c10070303012200d143e5844520000409204c0443c1c600420b28040243c60a90681d0081d0740d12011030342c03000f0f1683d5020000344008100c1d40046070603a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 355269577 1250 355268327 355268351
    0x2030a0e031603020111122d030c04140d0519170307080103080c011116050d03090503040504200a090e01060f120f0915270b01030303020a12060b0409 66
    0x21000c90080c1d0320070b071041e564103000642c0101e2900c4250071100045404091a05109400c1a44400c0a04904090385030341c02d10150480b0b1624954004141040d17402c5003480a0151220300443c0102c010002562118550300c0e280d1015129500341c00c0702c100e4458520700801c4c00000c0d8403860b000e03900402d1304100c01b000da00c2410300b103d016240c1691a0030303550b861922001717510b4009003030351050b035501e81d010072000a8403c0c0107407a4510706136042c44888030f42d901d4141d19040038800c40b8400e147c1420140d0001c10b0020040c0c4040ba0320980b03003c1081071000108030141d040303185218203140c402080302ca103e551310502450594080c000c44c0d441d280d888003420364003020b481c0c8a1400081c00b9207000c08185e00940c020b64507101001c0404150112143e0b0380c9070702107809202c01c0221603515452941800e0000104070800c050010038902154825102d450b00301d001400054140354001a03525030310381c407803006050b8641688004101450300c60001030040d034041c3c03140080603400c0c1140b802034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 355270827 1250 355269577 355269583
    0x14180105090c0d1e0501050106030c0c0c060f09090f060608071b031815020c0406050d080909281406010813020120150402120309010f1202090a0602030a0e03 69
    0x141c64020042c2002d841071410407843c0018502c0c100e4501c0c445521103100e001e50b80c1400d0008903c510000b01d00756060080040440314040003810400007241e50700c6020a40048440c002c0d110189040b10349252031003801e80369001680c1c07183c01100d21380a807030040c2d010284c1c0003005131041030352085034070b0301c036540222400010501a495001007040304c2000003400340e03a0300c17a442d070f4604022070b011541e00d00c14240c154556921110140e00161803018041c40e061181801800301101c12888040c055110408180200202135008010100125a48000642140d80740b03043c1c18600701441c000c3c044007503014001c2c40424002c0000c480c1c0100c0c4c0346600a805aa04c10541e200c04a6000301081d001140d034a4103c400010301c1c03010030301103849455001d0101214a204044510040f0f003410b00c18041710f44804100082590020f0094510507a440605c190501c02145000a100b40d80880c00100920950a8041d440070200d0310000d50b81d0b0f0080054501c80390380780c1307400d00054400814552 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 355272077 1250 355270827 355270831
    0x6050a0801020924030c090117070314090610141c0f061109130903033b010204150804030207050603010f030b090601051012090f0c050a06020c0a090b040f14180105 72
    0xd20340d4010b00c00907604c46d510700c0190041100506d4854180d4410306c04007110381030203a65143c0040e031100c0d5403248419241c8006d6030010a814010161440d0540011f09060118040c01d54114141003040c0e046a030780e1544805002160001c2640c02040e91400c00030701440954115007060401d40106884031054040e143c0250018000512100005903400c009210b002021400d0541d119028622180e51840c03000f145010407801405000110304081c040d4041c602121030b003031f0300401c0b0a02070310751010b2070001441c1e0203080c181c00903120b034035042c5d00b84001ea03002243c000700080000039483c0c0d100325080c800c481c0644951007082d2101c020441e110502401220380100c814084010703881c0c0b085904854560103044000307510041a41c6805200c14440c10683e18800e801409000398a02040150001c1c007482c0020541810100040790034024640b1a80b80c1d10b80e13442544000944654001120210aa400801c01d01c514040a4200d104041e1400c2d0010000d070f203a84550704405206041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 355273327 1250 355272077 355272139
    0x1308070b090d0204051e0f071b021008190911010f0518090c090a170c030a051908040306020a03090606060203090105030a05061203070303020903160e04060e0106050a08010209 77
    0x42d06210303000e2102501029090a5080052200401000e4403013014a0700840005140801e81d04202000400240701040c162000c9220072089400603565a041d5039410844c60400328055901c030f003000c02c0000101c8842e1642c42e42040c04120800035200030a580502c0241c0310800b05c047d6110040b00c980c0620780c680f200096020902d4582498904180c0b94031186540456142c840540c0220305000361507440a06125001c01c407880800344240114060360000f64000c0170b03050155200d0036914080094055101c1100350900e00500035034008590185402c030605540c0c030036070820010010205a80e060703400358a82607010405a10110480d00c20f404160748413400c60712541c000000030b00001c0e0000b82d10240c01650046840d0b01070018110003400703503e005840d001c108041c1820304a1955206a0018140c1010b00c00000000b038419040344d04414005580791458000c140104080c0c0c20456201003205c6000400e030005400400d03d40f80242c52901c0c0720343c000b030070070404082150142 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 355274577 1250 355273327 355273339
    0x41e0b1f0605070f150605030f0f010b01140d0b0312030f0402030708073506010303020307211e0e030f0d170601050a1202090d030314060a0b2d1308070b09 68
    0x8030080f07031585201e105400d045c1c400c00550640c0e80d80001c1e103042c1c0c0210440c84550000201c5c2d180c542c0083c0300d0300000c50000c1c285110f1036100400f20006d184500782c1034140090f81c9000c4280c00751020030403c1043c50101c0b04843c0e81707041071510216031010850f0128070a20840202040141000c25a030080b10045052000a10070441c100044100c1c503032840403140168180da14900002000058000e40c000d4001c1d55441001382040d43c41c5416510440598000504206484a40c81072000400c46950710038484c150711449000c55050080408484c1d00d4412135020f82c036503020114249048108646512607009a000213543c6600b504a40c0c050204406212481220303011b031403c081c80c01c0210b1001031400b01604d000800000d0501d90a80010b550385518440240c40c1c4c5c0c9105401440445000f0f00b01c52800304e00d1901c80c461683c0b01090700c1040040c6845980c0030910711003a8000d580556034603404521028079035a010351042c1c00b2280300d9038a001540080f1801107401c104000b901e1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 355275827 1250 355274577 355274603
    0x6090a09031b05030c120c0706050406050a030c1803050d020f01141513020c060709080a02031002090f0405091c08191d1b15090108041e0b1f060507 65
    0x203034040308a1a49042d00c044c0000c2103000f020240c00e014880c045800f005507a51200104031000d0300d8182c90390010803d000c0c2c10007003482255044025285407000c140b0700412030550085040f141c5043c46501e00d2600884244040b00b00000803411120b90701c0c1350b5085400000440c65600d09907044d04610810050620700800c180c3d01503c03000007182e503030103803000d08100c03510101c035012030740421107001e02504107000344101c081d401504440142540300080c4640070640c0c00098480383c0f034080d02904140e001500c0384c4551514180001c4003900201704100340c1c84c003003480d59250034602407104003601041c61f038091558043c07400140078520403980d0001401c00c86c07140c10000c105041100c29603015910f00c0e490450000c1010307441c54940f941260348002498028402c0c0c0c20585d2042d203407925028032032050240d82c03110030580d0140c3c00854444181442c1c1e07600300264008008050103004035001000b4001c0c201051281d020241024a441060741c0e6003811149401003240051232207500002d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 355277077 1250 355275827 355275857
    0xa05060d0c032604030b010e010518191e14010801050f0a0c0309020a0605090a090203011211060409060329060d1b0f12060b0409050706080a150e06090a0903 69
    0x210303282c02070f50340441c02110400a00c900030302e40c00c16032040700c0004680700144020040c080308507004120568001c850414409121b18800200901c003110031030011a03601080e040c1500541d24013001e060341a03880c006965030801c05801c076040d440b2074051851000017803100051051034424500020743c001e180d107820550f4005000d40000c0e400402d0384400c0e540c0050383c1d40e00041da00825907502c4540d0346143d81d00030b0180c548502d5001d4020103105000400950390340010300c001c4580c0c8001610503c844103000a6054040c0345c00400c920f500c0d2180c003004008000c2d0501960443d58541000c000c0d500c0d0003490864502210f8158100405a542d070000030040b05200d080090342c21803c041d041d48501c3e0040741c15803550700c4041c507100728107031300070511559205454840c08240c405004500c41504c1d078543c0c84c020f500c03074081000300b4980000c0186079a41c3c40005450b14401084202c0c0d5a00c60030720352008401c1c0c0b4054454070114011842e103590911410070b2480d41629032260100c2200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 355278327 1250 355277077 355277093
    0x101a03160605190e0a090504060e0106030b06010c0219260313051314040308070e01090e061002030f0c0d17100306051017010504050d020d02150a061d0a05060d0c03 72
    0x2051010620510079104502c81e6605c401c500d0141900303410001c0e036842d203400e14409030b40c0040d0003403e06926200b018004602c0c0e400030168449070030708085c0d01075102072000c10319130380342d070b0500310311040142001080441d540303150305640480a0f0042d584117a0040c42041d05c034418030246d44005190050200304034101601d041e050907503076040c0015030028404c0c070509400e100311380032000031b5102c808000500e40c0100030302c01c400b08280307000703403006061000341031034603401400c964411500400b441000030b200f082200d24450344c000d562521307540c8000006581d8003030012204080b40c0541900c024500300214101e00c030f41c40041c0311000c1c5c0391840d100c6900030400a841003032181d100e108045082541c03400c05100d010341c004000143d52815041090070312800344020740441d000044100911a400039184940e001510266003040d01c40304000802025a540003000805034007445007111006851118403481c074208c070a0245a41d01410400811000c1c04000e01100c1c00042c1440425604 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 355279577 1250 355278327 355278367
    0x601060f0c0501140f0115050702090c04051c020310020306030d0c02060405060a210902010c0b070c02090703020715050c1c090209040b0106020106060206150909101a03160605 77
    0x6042030300300e07200036485250944840c0050a10301890000511000451401306540100300042c00f0800354410b03984014a40d104070b02c0c0c040e10413410b42c40490054100e40c02244c000700b8004102034011402003205106084070000103912034010b100260036810704a00840f881680c004015004510703107800c06031400c0710074480503030300300c1d00501002c40e05441e46401001c80305200d85802015549034002d4420740e00f000180081d01c00c6c10030340c3e00c40060340c00c20380d916001544034429101701c3c0c1d07622000f1070b50940012006540403481a007440103058065000300076043c00307081340340d40b1031f4483c08021702550030a0701c0040020404228030b002010804500b070751281000b00c03001c03400c203106400044591500740d8041d5142d1981000402103107409110f1640100040d0014008918120b4403c05c2c420141d01d0f405805518208002116680c061007405403001c1300c20001c104a22254850400410880c40001e01030310a041c40c40542c20001d80580c41112156a680c40c500341c12161913540358040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 355280827 1250 355279577 355279607
    0x40b040b04031404180b0f0109050108041109010b03090c01210c0509090106170a050403121d0a080a02070b0c070902160c0303030207030f081501050f0d060e01030c080f060106 77
    0x40301c06003c00b582c0401c001e000a11850009128a020109060044441c42d003c07540c440c200460010301c0c90b9070402e50240460f402401c080c2d5071a0341d28100461003003200c134081940b011407400003044864800020307500608600040b60300c00040500191a00c070040b8400154006200d10300b50280d48081e04a40703e0002e8529086003011108400700c0d0922800ba0030100104003d141000450094055032980c085403c8900b442142001d48000d40403903428148211604e0300c80c41d0703410346501d0040445404031941320442ea602e04035030900c801903170860f802000c01801500e4001821035a04400c0d07843c500c0701c1c1e00c040c05510b85441c422000940c000000c1e100c0030f00045410030046000001c0e2000114042c0c2c82c0540c0c0c3e245203240050004c0e45191807081031244000612a0106005040d03207840e24080c02e100341e403a50ba050398261140991a0501040c504002022641501841c00c660403244100c0c0408a000d84480c102912200b45e40560ba41950004004002c4144030b0b182034070614117 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 355282077 1250 355280827 355280837
    0x90b0f09010924110f070204180503120a0c030207080d0b01020109050f150c0f09010c080d021c0c0201110d0c17090102120610050703030f0e150a0b0306040b040b0403 73
    0x1940e03501e10410b8a000100000302e030412010081c00200d40612000315444c0e2841d1840c052900ea00707104c4500a440000c1c1c013807550307845415140e1600da507141c00000c3d04482100e44031407420380c103001c040c0422038a0a401c141030240707410b10b5038041e00035100c607903078804070742d6040ca142c5c1d0744410001c0c8200301c042e1b0704541d00e81c200ea401003901884154035500a00d030244c4500c80c0c810094145840e400380c55100c03034202c200002030620750240242c61040320f0901e8000342c0d4010504080e4401d0082080a11020780700080c00f001c0b06d903a281e0340d070310090044502031108005010b401d07400c079516510b03401c244040c10010b004014400d544070030081000380c2400075000320181180081050308542000f650381d80090145440c00c80038542a50020701190003901e090401c44004109000f050402420705844200f4091691111f0300030300241c000ca4022109106466041e03076420781825216004124503006003041181404500144120b400401c400410303203c1d0741d500721000710000c02c2038003001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 355283327 1250 355282077 355282091
    0x6060d0504060212070f09050f0105070201030e01060b030106020703030801050d110d030c0b04060f050612030f0d110a09050109060503090a0b15120d020706081b09130f1a0301090b0f0901 82
    0x10b81851845c040c816680c1c0f020307501c40090002400d01d405a8002038400c41400f4400705442e0b80c0602143c202c00d80c280b8011030091034006d13040d409059a60860101d4450210001c40d6982e400030700350701142c0c000d556160b102e03643e070010302480060f03024024080450b400000707039103403c00007410060396100f464042140700060300c07014280801a40c1c212101621080040d15560160003825080034048032810700c1500c00b01c8180303030f5902c99410407440311200851000021400c070351041d100c0000e1216a95500c402c4500014a086914001d1b54046103841c034010441c94407810559204400321802042000d00b10785480f01821401080c907981041c1c6002d03100e44907110703001d0820b00209018010040b0070310701a40a800c110312504080208940c80082040350030388114840740d03d20b004905950307520035481c0070459818615641100ea1400e200c2c182c003012421381e0100150310003a20084640309141001c05d4266054a00c01800f509900408035039003200c84084a0b800540880c0001405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 355284577 1250 355283327 355283347
    0x150c0607030207030c0812100b0a0228050a0602031b0f0a03020906041e03030905010f020a020d02190806010821030402151b0f0124060e030a061b0e03010506060d05040602 75
    0x10f81e00a281f829003521882d03041c0514114442c20010161400100300c41c1003062030b520003580c4800008025030081c881c0489480510518034021080740d4004065484003e21801d140020f54410744040e490300507942c1c40301021a0142050341e4543d0500d0303000b540b400903840001c50282d0002d1079155405642040000303a1365112007040c2c001008041403903802244bd500740540006616032241c0d05010ba100c00540c0295030200c2c15003082a411541030180a0560001c1818040d0050014441c4820440003049140000440c2412543e14904645400ba064081c40c00034582c6100c140b0a20039080c00480c1c01440e28044030640040010485820b060f4505100d0044074415041c803501034004c000011480c01007801507082c01100d0002010389001c01c032134002072580e284c7c800e0070b0802c42c001041050540c2c2c14411350700d000340c00400603c2602d4683c1101c08034070038440420000300700d001c40c0b071541030305041c02050702c1228000c08003030410110320070311009048000d000f00e4040380d08024110130 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 355285827 1250 355284577 355284593
    0x70e0c09120c031002040b04091a0d1a0c09090a021e16020f0405060303090d0f020931031d030703061505010801140a15051e09150c0607030207030c 65
    0x2441408400901c0b14400b1101458148140d2540328100140104021302160b10304c1c00c225070844406020000c1e518410040d409048801c1010403a403100488118106008115203c0c0200c0e41c00c001d801c180c3c540f0352035075440702e82c4164260103070803042a10003d0707644502c66000d42121308800c03c0700f0311810614a44504254014549034801c0c0c081d4682c2c1c102541484282c140c4003550070b0310200300d54100000003969031b0096080043c0703c3e0502c00c0c41d0008010001854503040380d405032240d480f50420750359078500d005540800300c03800c490411080c65000040500c503440c45400d619004806003501c0c00c0c540070603c58000c0146c00d80328200b40040041c499114014080880c4891000f00b581401d000500c1c441040c0d0144540d2418800d401e0640e9031000c004100b1503404149884900161032401e035020301a0401480202102d45c0e5a0544072035003030000c2c0401c0504444040446901c5076040c52140642500782080c4da100b5000102c0391400b9500602031540a4107000c54050072594407205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 355287077 1250 355285827 355285849
    0x3020306033903010e0709090512070803070807050a0e01030c1704080408070503210d0e01140402042702090c070c06090815040f020904210e030c0a0503070e0c09 71
    0x146010700d40416502c803140d100c00c40c440860003240203026000000b5605a680c04290168980303c559801c40b0604000d0104007110002030315450b981d8a130340c200e041c03031500d41e0400c4a0340008264240002410b1034403a004841140c3c856448a00d00103803008011070003030100040060500c00c480810140c1e1198405542c0d01c9140f10303007003040d52281416041420501d031548071074003903030010030800000d40b80200c85d13648074000e0300592a00d41010340890000382c40c0c40e15181d07050354a40340351416900d13803040f50035100707900940d400d00c0002b0110b0810039208214041004a5003d84e40004005207001401550080d001032500b60400103503448541000e44280e00400201f40010300401c1703102c106010b5500c0200c071141000c0351300e02c0c09071581862385204000003071284c8104400601042100c2c040001401d41e25200d00c08421090310000d0540d81900c12040d20900c10044062464035040001b00140d910240c041d000c11740c6010021040103501030720750702c0c606509000c000480c4e20f59a04c540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 355288327 1250 355287077 355287133
    0x408010216060605030c03030415020304120302060f070e06070221010c11060702030301060e0d031809021308031912180f03080f0601140d1107060b120105160302030603 74
    0x4500c400241c584401164825132101e402074000034843d6909542c00310541d4100c8200c15440d50b660f48004a0490451143d500101003082074458000e050550000d038051050010000d215596180c0341010344015208030741d15030340300c0000c2180400505200f00c40444140c58041c0e0b8856400d48080881d0940e454171a40b036001a0944903901400c04041041a8114000d80041d45c955418408001e0002c8900c0b00400d0080d0a00072402c8200340c81010410380405241d06030b505042d45a08d00000031b50301c5000d0b000002c072040b030380c0401e00000100403a20070143c0a4003110304070304040d0301640d03404d00c00e01c035401815540d8500307402110b041ca13070100c00d5a4894100500c2a40b05440d0182070700002411042c0c01821700401c00c4003a9801c070080009070408409400e4441c0d250b007949001901001141c2684000c001c10080c00300440e0b034020030320340384085403c80c810741410041c140c2240c0e8101e805180d50410024004541e43c06a802941c0154000c1e05481071850500f202c1001155101442 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 355289577 1250 355288327 355288357
    0x20031909050d1b060f080112020111070608061203090f09041401020316140c1f06031e03030c050307052b02121503070609030b0702030408060403050418141b04080102 73
    0x907141003005070f0701042c090b102d1400c1400c035080e0142c400820080e414050b4060843c8480d0f000015a800340c0c00c5c504464150300203c034038180e1581e00040810000317444860280165095800c0090808425201c011101414a8464405050822038001e902030803c0c2c0382c001100444688e5030b0f600380010b51051300c0b50100c1000f0550400d0004100300c03c50045400503090a102444503200302007002003100018410402001c4111208407000700b01681c03005142e031a01c000070400b002c409800c0c90030424042d440820034407000310340541c2c251004450040009008100340100700c00444801c50402d41445081c189600980c106107080b43d00c02d01c3e80369028410602040000c08c910480300310704034000e60162000301d14081028012068600004003444e280c000020200d501c03c0050310014a11801250307244e040900300500164804e0052151540c0c90795051944295a40202a0394109400c2d11081a03039446241d0180d00b12490701400101d141003100082c40700090021300550b14a603500d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 355290827 1250 355289577 355289603
    0x70e060403061505010c050c011d03240705120a020c030417010f0e07180b130501030f0b0a050f13030201060905070302040801050f061008070306030503070303060620031909050d 78
    0x543d60003c0e907078440743c100324202120000081020900741300000307082c20410005000702d50405030180c11802c2c4180c146c401c10a29013000c0700844001d05a022090641600036100e45070b080741c040c440d0a40c02801000080041484110980e005040e059002d05c1541d090644031040c00502e100842c40480e80c90b034581510546400f060301c200c0c0c3c0301f454620001c00c004d9281001654242582440c4000199614500a0119211500c0040c1120740ad0741d001c100c65038580ca0000b0740c410001405403442202d2000052000181d449014040d0aa44c5c0f2250310708e80d0f40c810455001c0000d40c0d412411552101c0300092181141e00410f03014005176100580c0b15400d0425860844030b00800f03031803000108405219803a00c031003410920084407480c04001e142c0e02c1d142c00750b0140c0010b9000801c1c502c0700007154418140d06500880c260344440e13031076004e4417101d204e4085042c030082101c10819001000042000c1040b01c43c190103030480b504010320380603500d40025074010807a800c16140480c03107440c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 355292077 1250 355290827 355290851
    0xa030f020606010201091707080705030a0c050610060c080d02070b100503010c05071502030c0403050d0c03120b01090506031009020d06051824130c090e011a030a05070e06040306 78
    0x8001c9500400c284000c2003804110380b90714105900700804290340190000d0548140500301d02150903080d0420100c99a5800c0100c0050140440c480241c07154000d100101d0f40d1100d4103105881101c64954540090401c0da40b100170b840da000c0da282290301c0e0741c204017500008074903181c1c03140b0030742420a004014515080506094400d010201c0041142c101300003000981d40800042946921040040c3c881e40d401880754102d201e1500b01501c50311035403040c0d908403035000f400c08152a110f680e41c2c0c4040502c1c1c4a0b428280c0d815040b455001c6100d001c010b000c14100807005e50b601100c1441c802009a40c0d8200a104036070141d000540ca15071601000c0c481820000780034104200280c921000324503000c001c03030030101c0c1c002002d0300c4c9084a00300b081d0003540c1d504500c19000c0344100303001c002181e4101c0700544070403030500c9840c010076002c1c4000101809401c034121542e0180c07102481c0b440e41c80b120890300505004101400b80006010448101e80b40c0c107018101071803081000040d03034800d9030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 355293327 1250 355292077 355292083
    0x8010501090b041d040203070b070803150406140f0a0f0605040515040b0f0a2c030d03020301150c0c030803190f050115051c0519050f09060103230a030f02 68
    0x180025040110802040161807988600b000071303072081c122900c0c0c1d652203e00c0042c2c10a40c81d40d01c0752070002804030307511090250700401103005510003000e1600300701c003940030b10042c0c45e043e10a9008000a40e4030965407400d0551811030140310052210714916101c9880c0012800250000700001d0700114003444a401d0105003182100f42038580c2c2810140350107102461840703030810b0100e1395440441e080300d81c280182c614000c2a000510004100c84500d842c20692070000303031495110384a45144005014024422a8140d580d19203849043c400710203810b072140c42e6000c0040340c0e4520100400000320b65480041c60241d10307213041444600641140e600191244011a410100d00d020010840040031151440822285080454450340340e410746450307602000540d042d20506140800c04195010a0243d9105084450810698a5036442d814280c07100f21000c80e15a0300181c0140042012002c14440780b604451302964441040141e590506908640c12008906e07581d400142241d014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 355294577 1250 355293327 355293329
    0x1e011205160510050d11160615030b0601030e0313060305160f210b090c040503010c18090e1c0206010608060d020d080c01090c0e010e10080601030303050604020d09030801050109 78
    0x400540300d03407400e110000f660b00310182040f006101d00020b100c0303104d070100e420410340042c1012005440740301454502444013811002118910724202da0082100d02c0305108805694000c0d259031724540e1480015401440d2460700348813984403c3c01003410000c846403450340030741078503500401d06090000d50b1030350102c02101d0b04000d1020810520841e50380c40781e03000303150941041d10b45922400001e603100041c40e940070b546402003880f000b00038003d4030b55801041204c100394020080381c00d062034112010010844450850282c28008010390039007508054003050500342620411680c000703100a0200c211084180541c00450040142076000305020b9408002943e6031a071701b0480d6800a00000030040008100c11000700300841511001d6025084140c2d0100321140078640f03d8032411a076100901c10b010b920307a91080014100743d0311510000455200c0301c010000d6900f1558143c0c05000c0040000b80c1190f424840e00c001c2c2039050240c5094140070341c41da83c3e200d50504c0c000501041031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 355295827 1250 355294577 355294603
    0x60305071d0f04050a02090c0714060108071a161a1911042715121e030207170c0409120305090c0627060415030c020c0a0302091e011205 60
    0x19010400010500114015905c5907040304c24000030b030390b002c0c0d81100a014a1901038044500240707640daa0708400200070b07040c0c407800412900c08558034512106514501c41095900741c0c401e0007070340720300043e440303004034101d01c00c000106615001505007145010103c03449080b4a051415004c19200f4620810700f0100c5102c02803880c0a0030281040001c9111460807285031590b20317640000c51043e6070103101c0018615032b035a202250754840e00b00ea880108182600d8103503808441d2010100418004580154180c024000c03881c43c0050024100c1c14652035008140500510742150360707517501c039200310707d0300c113502c002104000c0344001011540300501118569206528442c015907400b41070fa4052030a10300140c02000b00d0300307580300071040500b4000c4c1d0004004903010440c544040313906050780c0031790754040140305130807502240c0d0303200340d900798903041018104280b01606100c0c04042e4400202d078040d00c81d28600080103820368400b40e110703090fa0003607403441904110041c000c1e1454610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 355297077 1250 355295827 355295851
    0x70203130e0105060702010c1704060509040608060f01030f060e0a120806010309110d0c05030d051b070303140f090d0c2619020111030304051e061603020a03060305071d 74
    0xf0600c0302184141c800d030707040a8107006110b01c000e001c2000000f181100000082d2600e915103075a250f0181858000001f103500c030b5805c0a80116003003400060603881200c1034181c0c0074a5910b19120396406c000d0008007030b01c019449447c0345d000d24074104440c50540e88151801c2c030302c5100e103100061140c980589498105420408501c020480c100c2002051100841e03040c1c01440b4186040c1500c900030b0342c0300d1600f500a1080c1e040282e82c00c003020307000007540c1d8210040e0800c1c1c1020345680700e02c0b2500008022442d41580e00d80c804e130452028141d103440e521441898248451700041c0e001030200390403200107100c0301c070501c1071460050b01541c1164034440c0d122494142551000c3d240d241c000b1009085110f91605c0c40207580c862510301c8015207141c410380341c0d03038205400c0c001d8540075602c9a0003150034340c1e48c40c4540080320002d4003038410299a41500006600b481044019600c08041d5204144d00d9103000f00100d80103001d030b20010801d20b41e500c00c035003103006405d0200980c01409941c03404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 355298327 1250 355297077 355297079
    0x10e07020606040b010201090f06020405040e210304140a0606031401060f09050702030405130c20030904150b0f0c120403150507090b07050f15130206071703070203130e01 75
    0x103400080454001c0d00807103000c500d088410740102e004142c05100908080c0080101c5414060503500900aa4800f5242030104103090003a40d5600c00f880d103001d80344844d44440011a0100312805580c1241c4600d49803c003640b05d0311840d0b45882c103207107010b80c0c80603a149006c20030442403000d50f00312915294003d001031464280244112090391140c080c00c151a0400500018030a00440340a803a0041002c07000f070740380e04004001400d035841c114003c1a903082c84014500d01c2c6407003d4159030780060085140c00c2d01c210a01c40070313001821210f02a2100f490000c1000c2c1007810203404450104003450382c070b0300b000d0b4066629005030000c049501e08010841400419100808900e07000c20028010415844191007200e07280341650100d20000d170081000020480f001ca810825802c6074021603900200c4d104403041c0056050710f148100b01d10700a821b000604215026000a40c0280d04000c090419400780d50b0196000325000401a00001415201a8011452440500701c0c10302e65074015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 355299577 1250 355298327 355298341
    0xa0902150a08072a0501061512050606070c030204150302040c020c0312090a0b16020d0807031701051309080c03120103150c080708090a02030d080105010e030a08070204050910060609030b010e 84
    0x18101c01c3c1955400307210300c80405c1c04004d40000b0010110f0200e02c103061031080358010040180ca0f0f951100c51420000404c03011315060064a05264201580f044050320303541c01c000081007042c0c0c4411003015048000000f40c1c1d52072049401441c00d40d0042c100b086805001c060420030f130b0625200c0c036024140404000d40d124015403c1c1500c0070b025115640d418003e07000c21490030b040d10020350000c000702c065810804040c0c050704c1c2ca1413283d251001c43c40146584082425424001d03d90031a2420140104442c240c0c2c00400b1594040c000c81c0d8a802c102d200c110b07085900c900180c0c06404040d100410821449040c119428003044400304025401c0c680018000000900010108603070480801d070149401e0101d24545a0300034222a002002d48034090009c41091040e1030108200345e240f6000c1c3e09010580b0060b00303034030460013860b100840c0e007004000c06004e171825500744202860f08413021154031480028040303d40300c01074818a5403a04044000050700031801c1100d01c2e900340b01305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 355300827 1250 355299577 355299617
    0xc080105030c121002090d0807051006060c0f0201050d090f060c090b0c062403030c0d020f0d0806060721050408010c3e1b030d0503041203050a0902150a0807 69
    0x300301d60b1202c01596407000d040014031804076040000d004003d00040c1002004000140be00c4800c800e11024040a0340d0350314151040e2805e02409000042400401001988124024140c002c0205000266200e2036100c409103504c40c0304003124801d1340c0d54040003896400c110720200500402d08031030300d84424041e840d52141e1000d0030024020314403d502c00070491405031020100680501120f4941809012007030f40c5042c3d400011025000e49807851000040104030026481c0d0151a5500380ba02c132170013031007101d920807181a6a60701d1b0000d94a08090009010803551072075035951680c442d410b020b0721a013100c54010f038041c01c0c0903180d2900e40800030305200ca02406400501c480c0006018007003100c490070018181c401d868010b5107407803002110044488806140d06804541c0f201d07415080541e6180b2051310041c280e03016100c0f559151034800d400030b0341e008104020114506240d980842c40e8140d000911041d030360400f19108101300e1744184074540c007440700d2810580449640c824001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 355302077 1250 355300827 355300843
    0x9060905010617040620030a0b0102030a0c200402070b04030210060e070e190602070e10030b0c0c03042301030f060b0a180509150306181c020f010c080105030c12 71
    0x304140340703c00084d007804000e80c002d01d0010003080390040220740800704034019a1086230701c0e0210901d040c002c1c030f8442d4400015501c000d0019241c094098030a5150321103071410004000c07001c0018010488034036160307400586040361141901c080c0d1030a15140c0a41041c40b001c080c45203c3d8544001044080039040b56150007076001c1c104112800c502202060321110368006003852816008000514140d0000750300c004c46103400100045900d8445140145e2942803001078070010940010400c0050024020803902d040082220700e81503550703d5240b4582c054049490030451480003118503941c040c00382d140c0d401e0380d52008101050a01491810f94000c80f08164204207100218201c181c004154040150030001c0c4000d81da4681041c4c0740030180040002640039000d0365001c0395103450400800703116074a404028003801403406c60000b036504040cd01c82e0045106400e083c0c0203145080c80b440b030080480d56540c9040790b051509261419a260102c07500810946580704c42100012901c42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 355303327 1250 355302077 355302107
    0x906150d0f0209010e0114010e0a1a040e0a02120c120a0507050903030304082a060105010804030c150608010b0a0e01031b26010605040c020c130f15090609050106 71
    0x252051031810030000c000d40d55203009400c401da034000030446810740e1100c103040740d0443e401c8108607180a001120b4199403d140030b5001811407000380300d40321403008402913041082d42254141a1b03900f46110b4a0304098a1824001d81d001a1030380e0109101030388260f1081902c40e482c0e10340350040c5501c21502d400109906104e59480001c1590b5910a070220303108900014100c17a201d082c00c0c24071644c2c5034041d1021901c4510600da0310f80d0101c3d40030984401d0010b015000d40b6240e0701e003100548507000300900440411a1312901c5200050184440c0c250042c400d20002542c6800c00004500719441c0038582032040304100000c004070903001040d50306507688041e43c00e00c10107824201d1084003407160004024181d6403080138003c1924107030078080d2800346a00a100701a91042132000700c400480d817010050b008136031000400d04001355000c0710390340001c0001501105040b0cd07442101d50200c030650007c4064002006114901c0c01000003500ba980420049075240a20280c104c1c0340880c900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 355304577 1250 355303327 355303339
    0xc011b080403030b03030c01090c05030607030b03030a030e03070c060309020f150d020708090603010602150c03160c0f05070b0a090e0c0316110604080903010e0109030e060c011b080f090615 83
    0x31440c13517217050085c0d0b060882100c0003445418124a40b03990a403182d4050b190180c03240c41d000038011440b0f405150140c10019019520f49510305800302c0140c84929104009d44c801005401c0c0054109404000108080e5600054031120391040104c620318140d90a442071b02114500c0c040240c0d01c0003110b0700a038410f040180d84141c54a820034440c0a40084d40e41c1c014004400020220b80128500c900803030910001200c0750341e0611103003614041556442c60310324100c0c041014250082e800b046509001d040f004201108130380e940c1e86000c0098004008400d40410000011174100d9002c1e0040c014a005054682c80c0c0300da1161128000144107107442042e00c036480e2001402080c903440c40c40150000d440b018541404e042d80b0b160700c00c1503c94040d40c80c004c03209615030010702c10302441560550340d11036040034440400565070404200d0340003d56903641c1e1450000140103240c0982c4145440700e61440c98001500080c0a600030840303100798025030100421880c00304090381e0007020807900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 355305827 1250 355304577 355304591
    0x91a0102062401110a0b01080609031c0c1107030501020d0b0f0306060105030c0f0c010203040311060f07050306030c060c0a050c0a0b040302010f17091b030703080d0b031c050c011b08040303 83
    0x40342d444410f000030034040d001e03a5850001b0703c01c40410281c1601c550b4001c483d40303510390b4003103941d49105040d030703943d502c04401c4040031610f0b0b5903030040c1010020500d050210704d0104c3d001d803410030140f58000c5600e61743c001008251841503005d50000301004807400c031100d40079403010035202d4200911080c10000000002000b0b20504016541d08006c610304040e158009000c5e074078001d50081d24141c02103034803a003802000100024849100d03c070800240c201c10740301e081d01603889030070103040550716004030003200106846010107000c480011100414980180b0f0500704c0c01d0a02110f04940144c181d66001d1103c149001d04a60840b6030a1800c82381c4a0b9001e08105c440141d0200144c0d10f040c0b0540a000c0040000030300100700e84c15501c244402101c5a104142c2e440c0110301c402803032034905201d518031150140d071003100c5148000e0207a03081d29100041404411001141c0301000c9000403405d140440024821350708481030052620071682c402940c0a014941c0c0140010201912055 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 355307077 1250 355305827 355305829
    0xa05040e0a050318010e0406060f0f0302160c090b0609030a290f04030201062102040b0f150304050606091905150604060306140a0b12041704091a01020624 68
    0x3004155070b4004054076125141c01104002c01a0032110039400075405443c0b520b05071038248566411250f250b02c40c5040680c0c01c480945000d5030010010301490b81c02e10186107500c034904072103800385225040303031110b507402c10303000c0c404668403d0200c80c004c000a008c00c9015840019142c0d8085822801c070881c0d03029420f002c00440501c0300d0b0403640036026401444118054012000e00035031094000b405102d803108030a80c522011140442d140070340001440c4003500b81036000c1011140094440100341e070704140420b0381c1300b0806503000c0e40d120000003004103000c020700c2500c0d00703c3d1080750420820f0900d401c0c040703c0c000a1102a0050390303940c0010504062040000c880c4001001d424140c0319075031030101400905c420b01c0340480d034011000d0355074060301e4020036410503900b5202000c1e00340981000d10702c00e03003100108200c0745107034016441e8030741c10120009000100003000d0041040c05100d00005010702c0580010350542d4845001d11030b00c0310050144130305281e41c0c40b96004c41d0340744401c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 355308327 1250 355307077 355307083
    0x2010507081e0711031c020d0e010207090e060103120219080f090907080a1a090117071205010b040608010b0109140307120b060102061b0301090b01030b120f1b0a05040e 74
    0x440312911100b40001c03084100511601100c15800c0c048065408071140442055125140007084400581081e180901d4107801a03e2501240390180304031049241c58080c0703001243c2c00316100c11400d5008200400070841c00c1d0b0424000e0010340c0c409844418504c4101341743c00c0c00701c1d910080c49008041640100e102001c0e0036111321200043c424100c0b4141004050403141003075500350001750070a006e0206041c0d02842c060600301c0c010389440c10a80c0380001e080e00000032803020350312502510b440003888001ca40744158920303005800004110300500704110407150158800c4129904001500d501d0780e800c08400402c441000a640d1040d80040c000241050100e03003050070404c00c490810f0091100e124140d600c54442a001c5416545071031b241d11941940002001e01101c0d004c05c01030202c0300706a0403407080f03030701c0605010542100310800110000c1c210319400407560300008828030b60307980820030000790714024041c103502c0740300d400081182e100750b90056a0145403500381c1107514100030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 355309577 1250 355308327 355308367
    0x30105040609113f0a0f0605010b0f12060316060509101d01030f2d14130618080301291c05100b0c070f06081909030207031b0602060901090201050708 66
    0x10b2002e0314406503d40c80c060700a40b142c06407e032284c42c50140040341501425086500303000e03074400082c0c00e090f88521208600b8030018042901401000110000d0310600382e6031201901c95902d0750340e01d6031100c006202d00d081c501040c2a081003400c0c030076a11140c10a01d101030480000786400302d680078600380c0e903a0152030061120344040d100c4110008110840c4120f21a00b104c8102040c031003408120013454888205a80a4803003c9801c2012000100745500c4084010a4546440240b00e580d03100d0724910b8101742e00052500011101850121081106050710b01075084c0b00541030800340600f051074120080310108007d80d4440100310301c1d80c1c119407018010011750006594810159100da40c0f5004c4901c2070390f000c084d5011001c68094000d070360300c070302c115004400642003450340034106015041008056040d80241074020000c92182c14407401c001400c6000a0003130362410400234a02000140143c160b80d1500e591000141e903c0340440702210b40054009441c0c1c065804545801c91032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 355310827 1250 355309577 355309699
    0x806090a091b0501030b06040602150405120301030f050d0305190905071802071b0b0304060b010509041d070812070b10090e01050a050604050912031503010504060911 73
    0xc441c03410210b004005002800ba214280d800340014601c000c20310605004078020b400141c4c0040d0000c81c207403800b4101c2151310500400c11a02a807040341d04060365944280c1066600070720703800c040c00030700000300861172003002c1030f240400141c60040f5048030094180d041103440c9a03110f0720040203220f0100700840180c2a0101a040c8418040c03210074000d5100843c1101e091990000000f159000c4a410400b102d4122901501d195134581d1060000c0407215403090600c00c0a0005a80c1c51300d891003402001084000410841c040100c9403514018807540303c40303426441060b203048038084c18401c0d034507034aa010003c2c040d141ca940d14101140902a004840c040d03141000060440005422a03401002d032220300700040e0301d440051109843c0210b5010706258402401450207409050003140e0003101280c1e04a4016aa80000b03400d55400341c41c1a1903094480300e610007070140c0342400320f20710700e011140801041e45468002e41c11800380405115110320415002810310b41101c1c0340d40a10341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 355312077 1250 355310827 355310843
    0xc0306090a03020f0316020d0206042601060f06170a0e030c0615100e010c0305040504090b0f01060c0f12140a02030a0f020c0607020f132306100806090a09 68
    0xe0300140c8107644801070031080e00103204480060b46082c201000b29841005450017200781901b981c1c0074030814400c440700032070f044942000700095554002c400c180642ca204401e0092a00c5080a000d00b522995008108080003414040000e160003881c4401550309802e04000c4560321070080c035004001880081d01070b400009000e42400902003500c41c82a00110301040c3d1a1a0f40c0050003100384401030740c00e0204120b24001602c540c011002103880034460310f000b40c0742070344440202d400c1e10741c0b40d001114000d2003401031009100840760039a000d417001d4a802084030607039444d0401c0350450035002030320002100882c047e00911a00c1708500001c68401c8071603443c50b85c840021b580c1d5014215010000b44420114220030f48081002c50a50310010301c1c0c1e9007414160307000c2015503d000c3e803210303a00c6101074840100f20780c010b000700c030700f201408100c0c884807111203200380c810b00714010b14142c40303220032100811905410810380c9420442c140c410305c0441d078806c2c0004d40100042c41d80608203075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 355313327 1250 355312077 355312081
    0x80c120406091211280813260c0607031403091510030302012409020c010b040c0207080d18090e0102120406061d010b030a020f0d1107020406120506180c0306 69
    0x80c0c1c00c00702124007048140e00f12030003100c40c16141000900c40c03006176250541e10300701000c0454001000380003410045000010016552516101c00a0500e01d60101c1104440411440c00c90240118442c0d040b00303840c00c61400d07400c1e9800428940c40f10130704444c5240301101180c2555800c0100c040c0202d22141056a0f600381100390f4180624030b40300460056007408200a02e6061004a0401c00050580c000b8210707820709030303000065040f5009104242d940d0707d100c010183e51b51b01a0032111803e6402070440941000d80c00c07410119080c0c0d1420034050b1030310895030700351060701c882000c54030100740008101740c2071142540640324210075010381200c004144030500003503500140840f150f240c000391000c030450b5000389001c1b1091007255001039007440021a404615001400e90083c1803110a02e0041e070308851408407140c2041031810544081901030450070a4468480074004030021045100c2040d40d0780d41d514000140404280c01c443e86038003030a80420449401c12800c01020343c0e00318 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 355314577 1250 355313327 355313363
    0x40306020909070c02090613090c0f0603060512190305040e1e062d01020703080403060203060418050c1021290d0f3f080c12040609 58
    0xc0d41040000c10710645824000c01c01c068010f10b10068035941c080c046102e1546d55408000101c41c00c0c2c04075021450b181e501c17400c0041c0c1c46c0d00c1210003400000c802d8400c0503080070b100800300c4111b5002140900f51403400010403050004445001415910041800d01c81902d402c95a90241b82d100c00d000d1034400050013040c00e10b1010468061800f5500800305685075420003076080508015a070500c580084040301070303e0844070700c0401d02010700440f04d5603070b42c2c0e03175800415921980c000c0e5455580401403100b03500d4036008500d250025034555680d040c00341e80b101a140c840704150075208a00c07580152424600503a41d9007005502840c01911460000750303044050070040303092200104031410259203800c0f54020651040b100981000d40070503081e5144004894441810340391422700700c4800d0b0b865042d0400280900d900d03085117028042140180050b00140302c100c01c014002490200100c07204a8000d442092031a00c00003125a02c50f03040480040c00b2220025214003551691000b034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 355315827 1250 355314577 355314581
    0xf0f0c010902030d0201020a0c02090411030604050733110a1514060d0c27021801020d08041e0c090612150b060403020d02030c031501061218021c08040306 68
    0x110b40281e05a81c03200c554144c0c101e080f0304c610040d00c404038030506400c00244c207200900076889445047c51714005100100042d2034080c0c202c0d0700301c40070380c4940030510822420705038446150410741034038040d0301000c860360b000c2801c5990009041011001014411400400c003645401c6d8000d80a401c0500d0031907030100142c0702901c402241c181d046070100f091800d0004034085420741011482c070205003000403806030760100c1080582c001d015165401144a8180b009042ca2210041e80b90100b180b00300002e0700385088161b0b007000344a6580b0400000c2800c016003034940106070711403140c441e00c90b0300d000320442074940c02ca00300c030600e03001000c903400000d2904549200c1c01086c1c03807444140500881030565005030200d5410100034401080141010314107180314900c0141642c0c8000501c4000c80d207403803680030111a01d4400080100a141c2d008010005c074003540103010b004400d0841c40401c02d5000c000f10090064121241d0498404c240035400c000540c3c1c001000c03035030741380d80b4103280c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 355317077 1250 355315827 355315841
    0x60906040b1519140403030302070515090d0e01021614031207050c01020106120f0602070204141005100201150e0c1c0203010305070f050d0f11030f0105150301050f04080f0f0c01 78
    0x482144460450706680c080d840c0c2404855113810b0702d0749403d0661ba0220041d400c0b80c10f00300c0d480d100d55811061403000300c003400f038881c4005200402c20001c43e994001c0c4a030180840d00c074150741054100c1c3d0b1441c2018141c0a05a40c030b0f5124180c4442000b1000c64907008000030b50600035140800d50000f0001d001c159400071250990090244c551204010140309183c400300600a00203420f44c80001007654001d003240c24001000003c070000c115110100c8850100d07240c0d41c8064806000303000034903222482d8051000c4601c000c1104800d201c2c0c00c0d00b41c54609006980399841202c0004a0b0b00c1441d82c12a000081400c101580e008040d13111b601c047e40003030000716898050300c000400c124810742029000c541004103031076031020aa44912228014014045e245a42064020701c2207440800080080c5034500000040b9850513100c48120180039014991183e41804284088600d14510f4190084d03006409203980d0303145889a003016210748128412202004030300c80c2014201940201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 355318327 1250 355317077 355317097
    0x9080124140102030703081504060803070b0c040f050603130c080a1a1501030c020f030c0a140304031208100503151e01080607050901020106090203010b0309071706060906040b15 78
    0xa40215190812001c030715088810182c01603005000650200b48120f5085800c80c034100030102d00001b00320041000d40d84d441c1c200b0314442e40002034403002c118002c200154400105403107035080030b040c0000860711104911402d03101d2000807000c50080e0580a05540840f0345c40303900f8030140d550300c0e180030307465020000d803d85075880010003502d110409800c400c0c0c4100003a01d40180700c1224000194001d00420003001c00318800c0700401a56910208001c106413401500100403801c03442c513100e041da1401c004000301136001880200b00240050500d0150030429040040c40ea503600040c0310084c454907404503915101d80c1000c8180500151425170003030b00c449420140700c3e4650340000039080000c0c0b003510416172248000800840c440c1029141c03039201440040340d01c80d40c642d20101640c1080c0c000b440d43c00000018411100002c01402d0000d0107065440072003880040f444c1611035030000e148501841207540040ca01d5a80c50f4003000401100030030017100c00c4101c01d40c10650f900700561507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 355319577 1250 355318327 355318391
    0x31f150806012301050301051005162001020a0b01060c02120601060903140606030604030e06040306060b09010e010c0b220605041a0601030b03031b2e0c050405090a0b01090801 77
    0xc3e103640303041d9082e0809205010784a81c3c1c81c3d0b0f4070b003d043c0404004102500810800f0505c2804298080c1c9003039002c5440c0182800304002c889200c400080c540445001810340d401003274a80d0029131180400c0781150442e051000b2000d5035070000c02e803082011007808440740544030000c511241c00c01c001c0c0c0141c2c0e0188802640301d1940303038401a9544016243c550f0305034090700000f00000e110f8180125581c00c064442824181c0d03d649802c25580d0a40150241e60303404107800300d9a581c0015010202002460304442142075a200c42c0d02251000d0b00c240081e402d00603c285800922041044110358045000c00040c0f40901340b0704103d661140040803d40f0174100415003030740c800d004800031100c1c020007840c03030300110802d240c50544480000000c0d40c0901c0120041a00d18200c50102e07108880c800000d01c0090151003100301c0e00c40301201414464107100600440d00c44403012540044844400121300d100d0000588808240f030b44100c1d180d609040b0100080040c9000300303517104d5855550 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 355320827 1250 355319577 355319609
    0xa0302310b0f0706090312020703030506030c0102030418050a09080a05070b090d020d1d030d02071a0f160507080102031f05030a032c03030d09120e031f15080601 71
    0x1400c40c292040c2e20403281c04480510002010500b142d0107004170310311034240301000c02800b00005003a030300070b05000d4000c01d03903403010420035003400d005414058000344091450241442d24031540c03070b50b00b0f00e11005656601c00004150803001e500541c02603820102550711522000303001400c5030f0180c541100c84805004c00b042c044400001e01e03101c4c04600b074015050b10003080c10210703441005422089103c0c100f4400707080907514144402e0410700c400d50b001d0b002c7c907400c1c40c00c083c8004d2039004034040ba6100420520343c10103444025510410824015000031800600301a803410145e1340028443d54400410b00000c8203200702010003000d0030300c00070700300d540d030782c0741010340b507a00c021400380114514862041d141352081c03541e82ca040c6640141e485010269201191840d0440601c200711a90b40d92801d8091003466030351b03003500e50514641449604601008661500418000742001c807030b0460400000220a41101c04680550000e00308001d50310700c001e540d03e440a106071a43c451031120 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 355322077 1250 355320827 355320839
    0x40b040c0203030114150c0f0d08040309030206030601030f0c080a0f0203150d080f0f0d0b0f1f0509040e030403030f0203040e0c0319020304051614010909020a030231 73
    0x12031204035480d401850541c2e00e007641d020100c10303d05d14565404003620b10324406078101072000c1e0000030780343d40c0200068100248980d203484a04000e201c180b02651040000080d4403180d010103480c4e041d07038415102d833100790068000c0d0024940030036803a130502d000e40d0203055210300700703a114101d0b144003031000d607012449140482c441660036180e0b503520000a0486410b00c80c0e4845070a40c03181161501d0640010f000b4241500b040058010301000001c0300706030018507014501c0340d040100e034101d095540344c1d00050031018056030b040724010590030204e0001030207078088c1c6840c5500a00180320f000c044d0001c1a403243d01a01046010a2070000c0401c0940d1000064a060b00c10203150a40c51b520303840c00c00045500001d0140c2c812600d80786403001844a0707400a140035611a8004108403520b10040c800b0b41c2180d5084018025655210f2110b180e0744030a1090840302c5501005955400540d4203c000e841512000000071808075881c0c0d013007448000801001490709503041240d1900d60b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 355323327 1250 355322077 355322081
    0x3060601210b030f0a0b1b0a1d0609040e070f060f020622060c030b040b12030703110c0a0303080703200910171305060a050405150403021204030c05040b04 68
    0x41a602449401425850030640c40c80d400124030501c010b044804d85a0300c046504d10b410303a0b0b607404440c080e82000c24001c0036090540320700c90407152103007694248210100d000b016100b0316181403129030700204041c03003152104e1048581610000d8024052100c207242081d5a8812920605241c1d801c107407400070340707a403140c014140860041e80c0604010340300c80303c44028400200000e180d50560124103100012a2480303106403118140e100071400580c44c5040008440d803805980c0c1c0540940341710b06810040100855a10035814203000c42e040000d80c8000d403034034000601c0c171900140c030007c021040c580c10401c150303c0391082c1d0b0b8040c00010740c1c035800e080401c0120180d0140501080c440d0395894903291007026010030b81c9140560018110455412070345500740c4400341403050b4150450b080c03100a00c8090750060a0503410f01140c145540c03201d51740c09400700b4540f5180c1c500d0000c14200751091040e2441030910043c40d903121603d905202c5202d0409105461207140340c0300085030f40c0e003041c2c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 355324577 1250 355323327 355323347
    0x91503041112070905010f170105191d010908220e040602070318031113110d0b0105041203020607031802091501020703020d0b1005010903050d0c030e0907020a0203060601 75
    0x403510112001c80e050003440030a12511904160a0069040100780316035036120700c500070403841c1e4105c49100d20b040c5030703c0c0100d0003842c40d84180364101410070400c00c060766511002115002c40004018031002584040701c841400015055420700e4103000c00d101c4440b001d0040540c4110048404458000b030322100180d03103200d08660002641e0020780852401d80c083e02041e402400c200c00301c01e801c014181003001d01c941081f00c071307d005400d015196080050075800106078104e07040114004242e8101054052a10040c0e42c464030740894031a1641b07d0410f4030000d102242c05011020518500a034840d001100c5080c00249421402220301c0214200301e110140c015101d4640c03070700d40c548103040080030b0700303680ba055100e11700b00040140c1359001c1c0c40a1050107802102036608000d070071850a10301c40d0344014100f2103424001e00100d20041524110403089007003040f103542140c034080e160f04002c44907081d4030014507000c0120a503000301d5007000540c0f084059549030f581c1c0c60b00642e110341c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 355325827 1250 355324577 355324583
    0x61e010e01140f0402070203060f0412030b090a0e0c130203090d0e010f20070e04060b04050601170a0b0402030c07060c030509070905040f050618060a020a050d050604090804080309150304 82
    0xb1000d10319142800d252120041101810144c9480e01d43d4001c41d00d4803a0607140d1b80f4800b0120f2040000b1b1160590003c00350302c90515040c490110450002021500702412408002da9204102c10040341c0030042c00003060b101902c82c0708174207850301445d4020341044038150400e02590180911003071048154504004058403840204096418110b95101003a0f5030003000c08d4152014011682c0100400700080044c0000704106107454504442a210070b801094000c604000900c040f9a8003d054000f0302483c500502020341c0d15102800c01a220314407205030401d10000030700c45001d60307400c01001c0b001d0181109208401c1510821421204102ca000c00d05400081051010002580289801c5801058100b41e00801c9450381c904051081c1c03445203809148400070456a034003400036a5000020607805c6091440007800507195204018072403480a0f503810000380c030750f40c0e2988480c4409400841081d02c0f0780c0c442d01007607502d500407806188030b001030400380c2c0800034200003105e104980c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 355327077 1250 355325827 355325849
    0x3080a0e2e0204050a1232010e150402010804081201030c060314040213020c01020c12040f0b030108100c110f01051e0118050402280e01050d05060601050f0c061e010e01 74
    0xb1402c0251806903086031802c031407000a44440b00401f80914514100011401140042c5961151041800c40b90a004440010340181822040c5070040d803078072590203602800c080c806542c441c64102c0c0c070391150a019507c465501c07000881032003501145131058414549040140c1c0c508202d0442001c001100c00962041d0600c070b1203030800c00650040c0008880201c00035080030750100d042424882c400c0004400c181020404010b6041d408021000420544c11660314550400b100151100c008201c2c025005446040b08008148144150740c1031a000e401a12501e10030541c084c0d01801040d104590304c186020716400c50039002039641412030320100e540c11006185d001d100700c0941001001030343c1c80030b9a000e412010400010141030710007034030400801910300b0100000341084042c0c0015020781407415404000900c00206560804402d0070200d8950400c941903240c43d10400406400798040d4806100b0820501d072122801015101c0031100c107030f0389441c08036004a2092103007485402d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 355328327 1250 355327077 355327079
    0x1306091d06100f12050c1e0c03192001091101053f04060615050f070308090c060c030405330706090c15110303060d03080a0e2e0204050a 60
    0x940120030b459008403c0c3d00703051101542d5445803c04517034040742c019222140006900720307140f04e68461803100a01c2d0945031800c100d00b41700c46a66a020f449500b005901800242c1c103206805290102c4074040c00b0040008070420072981140681003051007251008005501c07007102e0f40c054010b42e542205440c0740e4200043e001c0c0d2201740c1040308070403040c800000e00b030f070204052104003803104d01c03070390241801040382440c1460b0f802c0c0700502d402c40c080400c81c007813107101c1c00458803c3c211a200e81e09450034406940b18403800a0030310722503807500b9511090005100301c002c134020020f00122042143c0480d20800400c00c094080d0050441404407007480c041d54500100d509005815410300900c0300185541255540420a5a00d40c002032014404240300104044d81300d14159421b5403010050b60550500d0b00200702442800c602c0101071115481c0000e40094090384640440f0400c4012250708044003c184c0054192806c86c4688014104030100401c944a008070740c21540003030040b0f103000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 355329577 1250 355328327 355328359
    0x2a0c040f0b030c04050a2a08010f0b090f030c0301050702070323120a020a060c0509100c0215074106070e09130210050406090f03050c040207081306091d06 68
    0x28072001b05881c69003950703140b0307022450b034140100c400d0310800901305604480d071646002d0410309050f4002010520300c90000e01410351404266207014030141c405015020328840001e0410141d040074941542c40d10003000440e03940004c6200440340035040102030135200d078031560650007043c1e00040040d80001c04940035404003c0090100120910645441640c1583c8510942d003d082c4140000b80c000b050102d20b510b050301c0d800c030300c203845418292141c010940c04034024101c64085541034280118040e024132104444042c407005003e440d58600a280e02405903418000725a041d0701c101c41c0320280400c1c0000003605601600d62900c803199204010400c004a0500040c1a080d9003402c042c07080005884090703207250101c5480d04c5841c1c4035410001c008003c00c00d0b0f54046220070b1406039040010410108105911780004c0d140941e4940f02404c101c5181d00c16401e0051800f0016000051540d50003401c40d020b031059000d2984c00e00b90a00d094000d084019107485e50311000003c111981 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 355330827 1250 355329577 355329581
    0x2132f091c08030a092d030f030605090c0304112704030c06020c0705091003020607020409020d0c030503030619030b0708040203071e090f0203070f052a0c040f0b030c04 74
    0x141e0948000300d150008402d94807400c4070b410513120b8840c016210200641000b0090311070086030065040410000c3c160b4803507054a180d00508040c2c04d0080c0e0f6588104801d04c01e030001d601509028103112501d041c00840000789500032103080d50301c4407462002c001d55241884100042c07040012002d02003888040c041c0c6010000070380203c0a00c60040c01040000780240081c3c40008100ba01504101d031a081c02d004807204020004240042c20101c18801640c030705003501d8040b601643c0000700c900d914800701e4000468101d01a10004481c4000000c00100200452080b182030740d02400c560b014030b0f01e0410011180c0070050048481c2c4cc001500c0c14400d852559000703000904039411240e0380c072400032281a05850980014840c03c0c010300c8580d680b4050010045e007801011891444c110000500010706071a448041201c0001e454408501c0f0640f030300311484151540c00740a080600f002076035000c02440c00e6005d103080182041402d801c41c4504030b00c401c00a809170800174000820000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 355332077 1250 355330827 355330849
    0x2a0711031501090c171509060f01021b0433090203010e0a0e100203090a140d021e0a0215030618010e071404080105010308040e0a0209151602132f09 65
    0x820017980080c1e090114251640c1d041c026182e51000c0d401413480f42040c03000d4103c00410030342c01601d0413010494603990001c2d4943c601d42c240560312244020040001d0042c01d900c0e40340d205041020200382d9180c0d04800074440030780c003d01040d892800c0e915041041640001d01c903c00c1c9590418000a609090582150b410700c00100240c41d800c460f0103082d01708903001074030444500e900c0158007104210641002c9100a46043c004002480404400075500c0c014500030078400601141064825441000810b00d25503008040340324801e030303803080020550802c6510900c10240004c1603054041803002c164181c4220b0b82c3d04088654654000b6030b0a60840840d50308009d40070440010184c07801e104140c040c5220380c005d00d55070740ca001d501e011102005462107440920400c52150700e0742d04c00b80740461104490800b96100e580c0c1c420b032115510108500603400445403601103481081550190350240340b00c3c1980d2026109000700c03903082c91464114210091402c106d888841d2400020b040707 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 355333327 1250 355332077 355332101
    0xc0316061b0203030418090f11010224161211090906040b09040b100e040c030501111303151b030b040e0312010506090d15050603010c030905152a071103150109 70
    0xc0b1f09a20713a50348411040f0176120b001d85032101c01c2d5642003110b40c0c0c141b040312542c18400789090b241601102c0c1d4004d01c001d01505c1d5220403c41c0c000c03842c01590240401888601601c50200440c86214000d0300e115071201928038800c10700c1c403000030740c0740c981440748a028040161000395241d44650310174000100242c03141031500324030a0005607a0700d28181141c41580b03d1026202c581c0d24515000303080d0742d9003820505c601c00d030510100d8a84443e00b0b40300003c403500001e5440949070400d40c010018441040c0050448200c0b002190300160150005006114140c401b00700003140c40042a88a005210500c0c0c800108a0010841840c02c5406000d21a00050860032644811f5507144004404501c005c00303240c0d00d6004211681c50700303100ea000c64692508003407020a18560780c031740c0c481c4004032020480e18000c9020541e2405d410100c8440c800545603030101e5000704c0d05000e4040e800a22088440e0b02040214a0150401107015406149000326079507443c4d00b043d003c80040d002c142144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 355334577 1250 355333327 355333331
    0x14030412030e030c0705030c06030613050a0902040f05090601150527040c0207030611130506030a0e0d211104031707060207031e020703050c060c0c0316061b0203030418 74
    0x44506000c140020113a44003d60018044180f420303050600b4511030000e503034443c41c0140100900c0391100c404414041d45001c0d80054550740301852400100756200010b9005131602c510b494400d2201d5000501030006a422030702e50380c0e0b0760550840401005002c0d440050018400c801501080f001c800882c0551804108420303034544c030100e4120f4244120101c0142d04c10f002c10410710109101d00301d841d104407400d05107031800251280051414034410240201d20010000d100c0c11000d030710426150507080255841c00301c3e1020001d08100040d402c0d810038035000b101000c0c0f244030b01c1c400c0c14034900301340070100d0131301e4a503480d000c0b031800212000226001b4100109400107202c0c1c0300915949200340c4980d441d002607041945201c40c074003d101429580711f0342040c00403800004c3e110ac0721820441e001aa1004002a0581414a002042501841413000d038114041040030300c0801c4e502d04c0d60b161840c00007185101c8214804003030020b034054108003c1484001c02c220040041c640e5100c0c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 355335827 1250 355334577 355334591
    0x50712020f0d06051b04050105042105010908031803070b06010e030a0507180b06031003140106030c12030e0a06080103030c140303071205090111090d03030b190302101403041203 78
    0x40381c0d08489402c030031200c041c2d81d54100800300e04000720507040050100380e224286410040042c1c4144207a0140c58404030010785403612021244d0400602e5950020090201d0340c45403924840d160015a00d00c8000b00c5c05090070194010000150b5001c0350700159000c0a60302d82d030005607208010004a2605030040d29400d4001c00c604004a038000c00e421003e14800d51820308001e400c403a1098165481a10100140b2421120402c850002e8030b4000007103803805001d1040c590300400d5540d00050100301d000d4400036030030600c41c0800450343d0282e260308200c0790340b01d01000b51411b40c9020702d60100f80501e00500110348038071111b054040c41204c11612404280c0c03035041c9076800440e0901d000800304000c07001295514014143c0019010000340002c406c510620300310340c01100b0905000b040c8004008051502c02d2300039117410b12004c0c1c0910607039001c01a500080000c203000680c011034000d18668100352190800f400203a251016a604503101c40c1d03070782d01c3c580600c10341c04820035495007a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 355337077 1250 355335827 355335829
    0x61106040204052d161403061306120c03020a08031611040f09050d02100501081f0b0a0e09070609051011070302120f06010902040501050403020d0501150909050c0d050712020f 77
    0x41140e0b2074440e400c00044e00380c40c10102c1100c0340000d864142d0200514040b2034000748000c00700b03494101808840a000d80e03e40d408601c001400203a100400a5080324600302c144103640340e4290036a0b009880060410340c03902c40362a0b60303109111a403450280f4010186000c80d0206180402500d8010402700700da40529510b00c0c260351041e5030a1f5166004120710740500d80d01040030310300304401148180207a6240440458031003080300e00345500c020368840071190b54000303548203040e880e000034188038102d62264403868a00d88100c82d03910161042c1d07400812000c1c05010780404581e0002d200304a00605010200e40624600c3c81c50320f0284100d000105c0180d43e00301002c5200604540241030002500b02502c0ca448010780c4051a550b1040009000360390703000c0c088a040e2a01034070030740380141c160b01c0c049004152450743c00c071003501145800320350400300da000358102c1401001190035540c0349004110551203554002001035000c01c50401c1040c1000340640d00d581d00007801042840d040700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 355338327 1250 355337077 355337131
    0xc120a0b04061b05040509060405011a0903030403081602120318010507021201050c0c01060509010b12180706020c0405091f0e19050303040c120f0303111603120606110604020405 78
    0x19800d40c080340c8082411b01040c24403004156001e10102d40c144003035454555001c2001130104003d000104000484003010f4808200b11002164804001540e45601b0244503054400e013410072807088490b22845604464004256550307280c0806042c50040c40d40001920264800300080340c001070308010525034075200b0b00c1014465283e58000c15074a0031550324542c02c46000d03030803043c401c1a403c00180728040b101000d50310101403e000002c1d05d61a0411040c16200d9140d14424032841684e00218900d0f602081444280006036820f110b030341c5404041c00d1719080c10340302c800c40c0c8405690400e841c012998000d600d84a24000c141c41c102c90101181400701c444464094078960300c00000c3c00704211000c004403004010f40c000e400d402614541d00c141d0710b03d190180243c1010f0301c50010344e20410151045a10180c40c1c803162074980300d81d610b0007500b22840b281801d2403242ca004800139003240a011000c0c14125000702402c11607481c0e500b0000145009826481c20000b04003201201030b01c0d203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 355339577 1250 355338327 355338371
    0x5060909060f0601050a03180b071b05060112020619020a2f0112020f070b15010e010c06021e0712030b0a1404091b080304090e01020909040303050421050a020c120a0b0406 75
    0x21405d03064a881c0080012f402460b0b00d440d0022060803100122011680202c4e4003815100c4c942c00c0140e80800f94000243c0d036004248000c100d640030340400c0c8140580014880000e9031191026050b940409900b540e01020341c1d181039500e03400992641d060b15845240c00b0502402c0038103005050000f4106242d0301600051b404036804240402400b003060701c1c20b462692040c3d401d20307100103410300550000f0101102400d00415254020900c440c02640e0b580c01840703410082c2c00010303124450b904090070440e429403c2400070a29101c84030000782400040642981e1039007058818050404051200424495000780e072201842848901c8202006078205c000b412100c00441d1200d050812402c103e90611700400910380c4100409000c40d22507106880d0b01a4140c1000149903480d03041c074041d0545040c040c2c5083c0d000500c0d0198182d0b800901600c4220b00035030885500e1039000c1c090150b00c2410844000b1940e024045103400550b80002c00c0e0781c07140c8280c401050117221554002003201c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 355340827 1250 355339577 355339583
    0x12060b0408101a060313050111120a0e060c0715020304110901081f0209030f010507031505090906010312050c0d03090605150a0312200105060909060f0601050a0318 72
    0x10000d420005010200403400407040380b11403c0099500002011088003200782280b40035840c0031001510b04d030600d034412011660480000e20880c40801003107403d99025500e192210400c1070081070740d100581c424401501e803450002d0405449400c40800e09401040c0304641c502c0d904861101440c01500144d80140c2c0b0444c802c003d002085001c0190301d05050700001c4041e849144c2041054441c50040c1d42c41c811710420041c2d46000700030110342032038640c9071104810340c28103040c001500d6066001103e6080300034071140030240c40b00e0810040075400c0c0d0f1038418907403001c001403000c1100d0340b070084445007090420602d8500d481d1180780c10403100071420001700e6501d030100005e00506004481d4841c43d01408802034042080c0020b150100b1030001414203480d000d000c2d4000350168111503d403c000510414110200d540802d0103801c0c112252409002407030042041c4150018009002d482819600705103562032000450b0642c01c10506003040588800006a8060002062113241341c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 355342077 1250 355340827 355340849
    0x806061e0d0c020609030a05130302040213051509010c0b131208090c010f051801020316061d0f0d030902210d0908030c07050f1203130e0c030105010e101206 69
    0xc041c0c264001120b4228811000b550000300c1000540d11000c021034522840f81c3c10481d403180541e191080080019804c0250414400109a2009000c05c1041c80480d402100e540200640b003104284442c090802818003184007201c08030000f800c2419000c1c1c1c00f200d40940340011030721503160b900e240290718031580f010070082000c0c000d113000c00307200074400502d00b805d2058601c01c9801005010384195800e0074032201c11801d0420940e0300c20b00032074003481445000c3d40b069080c035040200003004000480000150f01d42d2008030316030300c0420725050641494025003424442200e050f0044e00404904076070201682c003864102d60400a50701790b10512080041038082c0c4006006400703503030720f504104a154418020109450740c00504441a11010748010449810309000b00301100c802c000020040d00001c07614044001c101c00110049a070800550409626048441d11640c070003805042e000800a40c2401e445080404107004912111318201290b4110881c1913012200300e60040da07001c103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 355343327 1250 355342077 355342087
    0x10e01120216170d060f03030f0c0302070b0423040603030504030b0a0e010515011b0b071b050d020c1003020301030b0a050c0913060f050a0b0a0c260d06120201020c010806061e 77
    0x10541744201c00140c0713800061401c1460554401611030081d5500003010444150f101204140c03003842075a00074070032044c450fa2103031346403040b0309402d41142c81d2000e8071210141c0b0640d400e28041c00340c602129099100d40c0e19003410b40d03e544030030940050400303010f19201c10004609c4103091040711300c2428004d5024a034040c01100040140c65040d5641e00710000041c000f03000b09030f021050a810a0036030803d23a152103400040c0406c4041e500d00003170300c540640c41c2c1c3c52110030303000302e0307070b601100012108800c60a04098080c0c08034002030001034400d41030800028440d080c0b561000d5041a4440215820588464005143d0f480c070401e2045d85507232100030411070f01c950401d50f58090002190f5107400d03541020b140c084c2602920b440341040128070fa0a9209000047d24040c8001c502000c050307180c06001d501407101c90380000e01a1103418504500001d08808090901010590590190144005800c01112030500c0504030591180c0e041040d000003070300c000a4a80300060745505c0603190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 355344577 1250 355343327 355343347
    0x20607050a1112030a210b1f020106060207080a031b0f05010606230304110a050d1b140f0108060112060303410a030204090e0f0705010e0112021617 65
    0x20071110040c0303100f0350700900c40f40b0416034002c058034504030980421b84596020001c0d112015080440805e50044c7c01403800031140d05c08000d11144003c1c180e0000c0c04095a5120b040ba65128140b20b80c400a421000030f060000b80714000d01100f40d020300e0203402082180c0d4680403680f4130b49540c1100c4680d5039007420444250080a109403030409100a0010300981f40d03600d20302d40c44010402444003218601d105c0c56640e902c01c494003e00f0340605401d01a038580e16007510000740540320100f6608800f4400030b180c100071460404204070240c2496070542800d0015a5200d901800f40e5051209030341d5000c0c0c084c0350500c104802140203507600c694500a038180c0d0399801304542224600d08122a024020f00c2c035095040d01100081e41d01ca155603100407000441c001c1c000c94100400b05810803031a603204590008000c04d80c047c1c00010344030300c2c40d5103030010344a001c40c8074100d501040250003000e5038032495038058602400e806007540031100071a03407004140d015896204810340c90119060303480d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 355345827 1250 355344577 355344589
    0x92104050a06180f1805090102070506070903061512110103270b1806180102090603040f030e09100b070212010f022208030d0e01150b041e05090c07020607050a11 71
    0x61000c994045113090030584480007410004000007080f5840d5004180c803d0825070403a03c1c00e40d008003e807580340c14130002c01416018107120a6540c2070822000c0035107e0341101040b4103c5125000c0d40c1c3d1040c40d42d9a0305010703081c003400d6140c14180d07030341031102c0016104d003500c0110001e98102648484070505c0d0182043c5009008411180c66001142c03211940c0050302d0b075006211048031002e040103c0a1311806481b8100380da58200e600401444100030141c40d00c007031091301c6603e82608212180040c410540011980000e202d420b03000200940b2a420000b81450350002e04810260a201d8144500b55100b10318050302c82540003130500c1000c4000100c519103000350070402d944851400b8911952409204080c01c15540e0310314401c2d508070804d50028202d8801d4688003d030b06543c0e14080504c54000d442550700e00e01c000f56051340c400201300c840e50280c6500a01c3c98903540ca0345000450982c005041c01c9800001c100104004203d04002150810b4840d070703032210b0310f1817951050203c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 355347077 1250 355345827 355345829
    0x201140c130f0308161e05070e0109050402030a02091f030b07031805060c0d090f060b01030b0f0321040b0f1305010905010c060e0c04060306050a14092104050a0618 72
    0x1000b042400024000544984121140e206600d032884140e07004a040c6070040150346200702e181c4a900780300d80030030000c02251707010807240210280c40040c3e0369190148141c0b0b504841c002e52540003c0c0000b40186400340d1075640181d080b02c01c40b801c5000d9201f80c0b609140e0150820b86034903e143c800c102c0e56541c5801500c03000d45070750054000c40109035803011307a1628050420b000a0a000c90015081c9140c0d522844445810002403094140395040c914010103074030f891140020300788030142c1c3e135905204200400d1000d004d4000c1c0042c5040540b506c03c0c13604541185680307100c0820000860500620241c92495003034030701a9a1403010404020359240315501c4641803041103e801c12540c7c2e0044050040142c10130b8000c03900e10380080b80d490904000c12441e42d40645405004014454568000e520984405004000200c440721420329580422034141010794040300080412542c02c40c0a405052141c034070b0907061945803c0001e085604a8000a0008081450000140d001e00410342c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 355348327 1250 355347077 355347089
    0x305151009331106040803150402210105040612060b030102220f080105071e0e031f0e06090705010c050304330306060e0f120607080f011508160201140c13 68
    0xb0f003c00111a010503120440144080c04200c4040000340e8900c05d00134001404101c002c104650384c01301000b04003180d840d1038a20300500e201e2880081420f0900c0d200b55030540e01c6002c0d42010543c082c0c0e468101401d01d10b10500d800d95000d00c505203000201510901c040781091003c0b01c0103d0a241c072550000c1030341d50000302d041e070620040c800001d410120308620102c0b804c0566140140065080d178540d100c00d11301c140c052007110a02c0103540f001d40106401c00c1403c0009000000b81c13800581e0b44c480040c0e60441d002e0b004000304206643c002e045d800c1e800380c0301d5010f80e400c00b81e8961b80441c1100701a02038044a400383d40c0a000c015081a8907100c03652140d040400030a411302070028120381d4504616405880c5d80004070240b0707500c0313215001e1a50078200c122200740c5490000102007103030039a420b02c1c1108601002040384a46503400c000081001d60b95a41a0b43e07440703020040e0700c58072801c01000d65503100c502601c0182640d014611810085252a0351000e04241f603001c4540300394044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 355349577 1250 355348327 355348337
    0x302090f0402010f271509060e091302011e03021903050f1501020106171b0108010617060a080312061011070515040803071101080106030515100933 65
    0x80140c0e007103001c035001007803a4a005070050070005400c50325520880e05003803a4400200c2c5c0040d02e007030f04c002024402d0758150342d03125050755141c1090391055500300c541c540c0b0101030000500319240000503071024a00501d0a09032880c1200c80320802e02c804150f9440000341c001132180c624100149021200900360302c0e01b0807a600e00540d0000880030013400f100c080304480400c0e185581e100b5040100a040c90304400300084800e42d03482c9a1b5020003103c034651592503004003c5003903000e03101c954120f030782688071080e45201441e46007140340d00c01007980d41d00c541d00e61800300c0d056000300040c1542106110200c0b08034100f040400c5280203104003140100604d00c28042d4101c80c010529508440f015907042d0400d130078850394504c030b500a0350400401c512001c2480014864051250703541c44e0802e80700d001591b6210101101500e5048a01c0d022510112561118604011865040c0c007880b0745440403009444905105010755a2502c040400f404004418000d00f03010340a551000014105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 355350827 1250 355349577 355349581
    0xd020a0f08061c110303040f032109060810030b0901020a11011b12061d1807050603150a15090302030106050402041d09150f01080f010b030c100203040509100302090f 73
    0xb01684980c0901e10003d840d8042510100070751003c200025440081c1030b070784c44645034103107185040080e20040e40e85101d050204414090241c030b0100010707400d0364900f82400d06000b410344401030064282504940c0585001000ca51083c8140e40134040d00c1c0c00169a90001c018000e001e8078401401d41020703450015000801e40b541459240c0e0242c4506141c08a400030082c69002004154440b85001003140714a44400c0902c15086204030441c181e0002a44030280300c060340c5480d20b002c0c43d50400c8040000c070702d074001c91002c88120f5160040c042c0003103607116a960000d80e0f02588040b001b040030404140b00b145428020074010700303400d46086080c180707030080105c070f01880540d0500d000391000b804500110014004822503142d0308030f5100e0b10341800e0103003080300c1c0000d01c1180228000c0f1264060301c800107014070b00403003000400030041c0136000b0040103031030b801e048a08401d5200402000030140c40781090503100d44162110204040e2a40c01840407600300103240070250805103003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 355352077 1250 355350827 355350829
    0x4030b0106030e0f07051005090904050606010f0c0507060c080c120a020106090203060f010e060d02120a05071e050c0c1c020103150e0f0c0f1b0c030a020307290d020a0f0806 76
    0x103017001110001c82d4001a10000711505807280e00c41d5035002a041000e9004000501c240020300c0c500134082030fa14840001244181100e01d94694000100180c1064208000452041000d054a1406022000d1515140c000a60700d440c5000443d40700c04030011414030203003902031143d00024840d194040d45985488400240d061020300901c50600c4061b001680e2140c40b84010348481c2d5000356000c6588a844205210082d4030403035212142d00e040c98001101d592281303a60410740c00380990200c0c451041c0c2101a20340d6080741c04940824840c4103c90f49103661901c820340c0502720240018a044181c0340001029a000000000c0e00c00500708804c102f014224001e140e4099020218030140b900c0b03501000b000c3c0e00c00c0720409e00507408003280040482d10905660750854800104984407400414289501c4d14550803010307500d60003072481040032003205039044499a02c4111000419500c0000035021504100a45140c19a011406400240e0880749a031556143c2d0b0801c0c810b1460100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 355353327 1250 355352077 355352083
    0x1112151003030e04090809030f010b0a050a1203030b01020139140d0b010306030b1513110d0213120804060f180308161e02041b020601150e030304030b0106030e0f 71
    0x3d910038082c941d503042c0f01081c030100c41c3c155405084010290741201e012090282d02900000d40183d2040403954000a01403501c0e281140031209080c02200f10491107440540060004558143c1036540314039105008032094004d00040b404140741d407540c0741ea07800d10700304c1c0101c0301e150f44041801401c400044804803d02c007980c0130301c01c07040c0001c2000a80040100e000d04030b9540000c2c610800142480409075002c00c0c55038005005a45109410300750303000c2c2c0c800740c0c0c900383c443c4000c00d03808101694003c08660010550051500690082c40d13a65020103000c000c034601c41a60060004502400103981c040f4499412407045d00d0111603650002c3d20254880103035100c010890394002400c040511114410414642c3d0400490f03207441d84025161601c042d4112800c80c8114942810203103200460050320391510181d90080c00949c3c20300b07240740703180380450103940b080c043c01d104800c5541d64100010000f5520a1a100025500d003220160036520501070006c9240c00a22245804038000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 355354577 1250 355353327 355353347
    0xa0204050a21051002030129030112060b060c0c10030c080f041104090c061b08120910020d09060b060a1706040605040212011d010305030d09111215100303 68
    0x150032442e1000b02002c2d600c0c1c11289410b100601501a1880307483e02c0c110b003503000d50b0488558070900d40c0c3e054180445000190360b200380d10400d41c0001d00041c401c00341401c0300e040300c4610840001410184d00000614242c00c0799110010690041c42d41ca0b40b1401c0c00a107800c0145030505092010035044034001e000084000d000c19690001a40000c1c00d101ca0203146080c0e4a0026004100039401810800759601c1d41c1d0151a0118011054000c40d014203100d1105105402a550a040202c510008c3c100f20350054007180d0a88503c007841c44450718644001c00c01d581065070001401c0e001b62910105540581c40a80c0c031919051000441198100d00c003c41c60100c03907000d0014035511040058001e20554200541042c8045242404000d0040f04d00e0b0580b081c8407000f10303910410610f0000f810f2001d020007441c54009100002000b003d5401201c101882541c0310f000d04140240400c4441c010614220086d1b0302211080114070b10144241d600840c0c6044e0b00040fa83c15a10b001c0c29550034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 355355827 1250 355354577 355354589
    0x1090623010e131406102c1512010801050105061c0902031603150f090804060e0d02060d0903120e0a030c02030304031b09050606090a3503070b0a0204050a 68
    0x40407041c0b070307195030b0007102d4120b0a008003010000c3c09410499404031007800c039240e5004400c4103086840c0103014030f000300501c1c980300c0000d03041d003654000ca50601180c2402c1440c1c000e0400f844607004101030f10060081c3c5103a41c0c4944103a0340c50010420309455044c0d02142c0110340c200080309400266603101140d500f803c0102240e91a038a10109103801c6003018010041001341c0c07408000c1100d440302c046c1201060315000d00a085104034510b0071030b1072040c001045030404000c2040306174040d60f00b81862050041030800c1800700c64010035065032049214002d017940e03030640f040030150807042111078288180d104105000c1c3c00700703203159556198407004e014002480421000c541d170400884d4051544800200f044010240c0000c050503d14091084002e0070000012040d04260381542c0704030900410b184142454600901132401e06a8840c004414106204a0244040300d0381c601e0503c410314011a5034100380d040005a030300000e00100741440c0100000c01142c3da070005484150b0340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 355357077 1250 355355827 355355837
    0x70f39050a050d0c0203060105120a0b0702031315031401180b030709020f03011d0601090e0a021912060e060a141801030303150b1309020915070b0109062301 69
    0x11490521518107a1900360040c56441040103004203680d1061503e5983c0e44241c045507041d0740c82d40c0401c01d90380c0341081540044d40c07003024100041a22a035000303400040c00d005032403038049100389030030b180481608200c40507016030980c00141c90f40351040b0382d0144006000054554141841e48103485952034404c003000e503d5030b071400000d42c0c040c809003000f8003d41c0d104564420b03000c4a82a6560000d1140c5010700100030f40704491241d008c00c80394401d0f03105035a210442801c1c900481c2c000c0c0303c05000c92308800d03400d20040340c02d0940300c0740584643c2a45d450b9000089903040c280800e40303640c0d4020500040102081c8080c5498134840c42c000e580c01171003041041001c140c041040c0f40c044000d41d0000003118000042810340550107a0b444c045a0240d00c115103448080c02d4601d48100c0c9408a480900200200080d111a03400b5140303402c0d0081c216007800d81204003d408503000b101080c0d8164602100404c03061896204000091204140c0d01548101d0b00388441c00104084032102e0500c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 355358327 1250 355357077 355357187
    0x3050a260c0f040f09052d0426030f0f0105121207052104030c05010c020f010f0e03010c0e090702071a0702010909060b120601020f0712080f03070f 65
    0x200302c02c030640c0e0107402005804900c50350303600015405400b0941d070740711001070260139481c11a01104520482021102c07100c1215458030b030b07150321034081445420340d06480344003d40c0b18106450360045018040c1400364030680e0500201c80d0040e1f0a060380301501c40c0d0741a000c000510040452044c0e00684114100e9444401d075003040380c00d00360b2100f0320415500e111500405500c0d602e802030300541b40260415056941c40d5001501c0803a0304000207540007a10200414207984602d40c00c504c0b031040b0b8075020069444000c0442e0a440150035180701083c10400124600d04248007035645c85100d6200400000d441c051100024115515440703031030400c00201e600569004214541c0200506a800c1160b2941c410080a254010300e410f9000000c0c2c50003c035503d90710028035010145082c0d4041c041c07580c07a0101d80c8070b2929441c034040711405000e10805000e002c400700030750721858850310340e20805071144030014101d22081c8040b82161041340909014a28521580e4070403a1410300501012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 355359577 1250 355358327 355358347
    0x803090f070f06080604020f09131b03020a030e0a03200102090a03060e0606090f2d04050d11010603030909050903070c0b0d151404020307051603050a260c 68
    0x100d081019030300e4030032401d0000701d400c0c4900d08101215569030350910300da00c5103010001684604490b24000030401d04c801e04241c41d15030600036046448580c00034a00c0140c0501d10f40b43d01200c0580c20100e90b0120700c040c00f280d00f45c00b40c0d040d00a141c2000d070104003800c0da005080c11500d800348040407004100c250a030508254120380c50108010700300802960b591600c40040d2801c0000c00b030b080c3c06240c01140882c00d22050060140c80c100c19103448683c3c0d028403400052004001c000da001301c0b85050f107040003841c550343e00c0c0194050800b4101c20010000007030110f1140e00e00c1c01c02e030343c0e142c0007040020030360043c43d21060710000310020070580c48010b403091039401030060281c854a5a41c1001444014142c001c25004503906c80501007507001c507100464641c00c038890f1201180c5202141c411500d4103a0095921524a0400d1404d046d5850720000b0701e041a9101140490000259182c0180d00109950307040c2c1c041100c404440403041c00b041c00103030742c041d199901603230011a400d901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 355360827 1250 355359577 355359583
    0x70f030903170a0f030506130c030612050705040c0206040f12050c030d0b01030b010203120a0b01050403120206090105132102070801020d0209040b0904080f091903061506030513080309 81
    0x65400100300b0140b030300c82402010341580a0b9182e000803d40c6540d21a132604e000c6c0c082c242c841e0200514480201d030101c1c8600303024100014a2030100740e84c507a0046840500c1c0c089510181d4040c40c024020513040000b800101ea940080030340c1598000c00c10080080c2c41c0c0d89038400150b40c4408122454090424152003038094407011030214040480c1d0100010810f52103800a4202680c09005c400624001a81c81c0d100c0d100100b179503a045000054a040541d8100021168044c0340c0365142c190703a41c884155201041c9480d40068004809001010400340251074008219003a0001c07460b15580e14024011000721503551031a924401d1540d0990091181c4802000704000030341d40ca580303a05443e402035202c440c40500c16440c0c403442c0d40f11401e01000ca03a205a5022220920f0020140749036245504800a00380d808502e10012610a2202d0206e0b40300440c440d160208121840ba0840c0c003203034815400180403d4909010070068450224840c203642d50051007440d600d17120001003500f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 355362077 1250 355360827 355360829
    0x20010207090905150606270312040303020715090f060f02010f1a13050c040506070f060f0911090426070209340c03050c2a03010b15070f0309 62
    0x2501902d44516002070160105188207650480e13050300030759940d6901005080d00a0450310544c0c401c1c081c0200810f000c4001034040c41c3c4600a00311451201c00d010000c00c150320641044005800070b03142040301130801040004030119600b031110360b140c1000b5610142e0003181c07213503400f0041801080054036000f94401d4406a0b5151414070511040c8206200329003190892207009085620109000440f54407800b4094626201b113280b0b41480c14040102c90303000402e00b52511494a1040c1c00042c82a100c1e400b600400b459011407e082c1a0424641d1524101101801034225104101c0060780484140060241c0501d04415800880186813454000c400c3c0003034009485400b4402400000b449600b07a00e44d07032060391441d00c0348101d4040e240c40e401211041c0030039030070040c010019014201404031030b0b00c2d01003100d02c03103035940482480003050303c04144c1c40c0c0003c05102d101ca9060a0241c440032039402e88030141c1140e90009520018810240c1c0a448201064001c800305449501940c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 355363327 1250 355362077 355362089
    0x91b03020a17010b130b0306090a1d0607090f080c0108070513050a0f03111c02090a1b08010302100e0312160c0e0a0605180604110405150403021c20010207 68
    0x40566854804413150344d4821418204011501c2500103184450041100c3c882d02002d80f8400407911200c004001400ca0721000d6035181000766010000c04004101c02071140226580d01a006850700c1c0201b10284050b0b0441c404641285003042c2903030340c002d266070780c000c1514a0415070780c071007504001c0c4104842c2d8010302c0e40801003100008021100151100940340500060203241006c4001c01581780380c040c000c843c0e1001c0c9071022201510b000b5110542c0401c825a001c104c1440104d84045003009044261010601000c0103000b035003020509108000061300740515003451400010b0381e500c0003a00e0404070080c0024102503030040c111a03561045034420354090540380c0301c040c40c00013103900b12500c0381850700d4443c0000e40f07460240315200582d58036400920940c2c503400d090101500c41e000021403151420000010562107c4024201c406503061004d504c540c1144104001c9004108240c2ca20300444118440821956074040d070517180302c0008101201392980c0184d081003410b40c405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 355364577 1250 355363327 355363367
    0x81902070b070b1b04050d0b130b0412110d0215040f080a261501203a02030a050a0c081605160605031302030a05160807091b03020a 58
    0x760800811815040c0603100c0e03510000707144501301d103001001d40180d1150540c000b50206e192404980759110142e0440d5805030030b1010b4019a8031071140b500c4068030704440c01103203e078554003070307a62018480c0100030051014080d40b040700c1c60025614168541a200740d030035458042000c00026101c41d40c04035500c410619115502000050b000003071205d540101445010304003003250010100306031140701c5102217000414141d80c01160501d0743c68064103905009280d60f0721b81144100b02e5a0440c003050171191600814003960003d62011b901e4001d2841100b1183e000c840c15004801c0e10401c2420b450201d498101da003404440f19650781c1c1000c2c05030240002e54850a0392190504803000740202c0c100c8203508540001314503550303050700c525000a0020b00118030700401a055420a0341e0005040b43d0840890740c0b0b80b1400c000c010a441c0c030100100f960100807288042c401100201120b040030041c0b00000d801e0420980402c40c6034030105a40024043c140718000c1d06e004a81d030b1890901 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 355365827 1250 355364577 355364587
    0x6090f042f03070b030f07020106030804030314070c0f090c03020301050a03030503041a10030309150c021314011212180504021b0307030903020f0f061e0708070312050c030103081902070b 82
    0x241c1c04445c1e20a840b000060060380380003031340090050050f2002c8960000d0041d25051544c5c0b421070390442e1140888180c08010004d4402040e840d031181d40c0900441d980d0030320340d217241c0613004081320707041050841418018001048107076580b0090750212505424500e0f92541c2c0e900c0d00c0d4041e08040c1c480c04503046250024418640c590310415010341380f0a80b61081025296000040c03182c20910007040090030304040000181007800c1030302850048070f0f8004c680c0001d140481002240260005403c2500c044000c0d81403207501e001d20002e1180a0070b00004c1180303212040200d03c4c85d2409100e0082d034002944d94040304080c3c041c50074400c2050b003643e0b00c440507403800a0440180d40700030b070b00ca802c0e0020022814a8018603005d40c0c1e000081426140580941c903800003c1e402d00340304002c100c0e00340f102101040021001f815054400d5071048036101c0b1948100c0b048035000340c00080144401d00040c8000b40b600c80481c2e0140f41442d90036217010b91010030480c5405140d401503201510081a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 355367077 1250 355365827 355365839
    0x3050702030d030504020102070e0c18060910051804050c07031409090103120f08220501020f16060c03110a120b03030a0c030306151b030309021806090f042f0307 71
    0x130050380a94400d03400e030f40d0f41c03680c0c0d202c845500080c140e9540103622802c2140c19108900600000c0c1b91400c05424141005d040000080d030407260280f10a021640c0002d83c4281d404040750003812050044a0800c51818010b107411154090804020b080c000403c1c00012000e09180c240c60b0401401400f203c095078403481c0c110401a134104c2d985004c105040c040c4440c0d01c0c0100f40043c03041d1040c081100ca5842d540d60001042d2517441000d41e40c0d9503080000c00d0fa00c0d10f03007800030821024141000302d00d82e0030318a0300000302c0f18642010402c140c503000e11100d0013841a0100d401124281c60501e800307c0340c540c05440101581c200b0769506101c00a03410b0a65a00014000c1d20140a81c03070802081c0c0d070b50155007201ca6041ea030580009009220309007151040c041e4403d007410f000740750000d4502c2c80c1d9408240c1c0f0051440011003107040c03280c200034091a082c801207134001720000b0000b605003800d640350403010440c2520311202c040c650354412603403948402d4114140034001d08446035507a5540e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 355368327 1250 355367077 355367081
    0x81303080405090a090302060c131508061201050c090f0f09090c01030609140708041401110d06140f091b070602220602060a1805010c020d08010f0b120403050702030d03 74
    0xb100d203d0041d8281400214503640c180b1400710000e4060b0040c0c031036903582c0d8058000310b42c01062400c4510038564000704d03a4240920604011140d60f03141c04446041c01e008001d40840d1500502c85940e0506080140315900d00e03090300d80315071043e2041143d400ca51000100000c8104000c240c021594000700801c0c5e102c005000e004400d420b8074204140e81d03c0d8403000b000d603040d02c43c005180e180b4410224040c2442020381552203030040c0000320001c03050300602401e451000c059105206000300382c5807050404c51080c00c0082c0401c55401c042c00c800403000c525495625031405100301c0c0400c0008800c40710711154609002e0b03c0d4002580d0340c20503490840c000750002248140054032851549050106d0030b0350b40015039582d500108416502c0141020103080c6415089402e030f15119885c0c40000d0090050036107034401500a00400040100010850341c81644204983e0381c010000300007080307045040b100d81c8815030114010607500c42c107003966207108103003000350184501031000340240d0385031f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 355369577 1250 355368327 355368329
    0x1030b100c140304140d0503041a0307080c04060804110112090c1701050c1b01090b1303030b01050a0f0509030325110103050709231009050a051002060f040813030804 73
    0xc0700c07080354020700301222903524001c60017610f602c005904201d000e14a804041e200401d485035007224a02074554040340d483c000c0010400302a85d90120a1110345030300503000642c0001c01c16010350402d4030b40480103103820005230000e0001c07000e2907614803640e4402c450900c4070070344c06c0d0706c107000d180341c60b01d000b150074803c40c85983c220544030800500451010700035607000da400700c50310034240119034400d91410880f000704411035641e14659140040d100e601640c1c413440e10740086c4140384085003030103429030700c1c2c1c51050350402c2410410b01074001d070851311400011900740303031083d212250729011924510501442002c0c07165444c0a03001700d110025105502107120745211a9a410150010350a07a01d090b25204c0210711100424410768558025100007006481c48640b000780c0008041224a0840c050200004411420612050900d4901d1800410f01a20300e4460b80580c080c00070344695015051342801c1c1c52507404035041c01450310a4444ea28895580114803560301c0c40d100415500c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 355370827 1250 355369577 355369583
    0x8030d0609020f0750012a200106081513110303091224040b160c060c08010f0e090d05030712050a051803040305100b01030b100c 57
    0x205031000c1000041c81c02611440c21408580c141090364669400d081c002c14440041000307022a5031441100500c0440c1000140c05224428000f40781c8424a06030050740c4280c0c0255a07040c00a40440101703041d2400b619100f94200019401c05e04c024100d40814008207a43c58540045c4111200c11308190700c0312048072a4601154803a84803515100140042281c01d0114103074410a00d0011441d841c100d446800401419649040c4001d0001500c00004580603c140c3d40416480300c140b2120029003a203200e09849500114505a5a45220940000c1c00103d4160000b06010702c014002c55551400301c1e8000b000b0f1144504074003004103101424490202260701c0103400003248a5182c400c280588500b80c003801d0110100d1806035420751018103800108060281c21030300d47e45580c40b0305402400d0b503003004580e60030180140c544503008418208c1715504100010400500e0002e1a80003580c003003040440c84040300340040c0c00404c44000f245400154401d2510701d515801201e007000948 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 355372077 1250 355370827 355370831
    0x151f18061d0604020a05090d060b09010902160f0201030b060a050705070b04030201050d09150608030903010b0f091807030b041a0c04120f0f0f0b0f160f11010e0708030d 74
    0x307034a5141403421001603078019001414180401c0607424290024164141c0e5030520782d140c903034201c001ca040921a000182c556640d80c2240c20130528216203200e0042c4071104096041000b4074050040894503440000c00e510000c0701c12100f1a40242c214045100d1f0090080342c07a914034001c040c0540d07001c20012601400364403004500b0401400030349094070b406943d114103203010b0318809001040d040509607a03100c000114500d6a010398010000503000030009540c03140021700916095a20303000c103c03440b94031040c00c00032554403080c001c9540300c00020100c00e51241110051424201c141d017000c0d151030038410420003071100c014402d52a400c8208444c4109607284501c00d80a030040d03000f440c0030944049541c03000b08250192405a40e801741c1d202d0303410ba11a030303036071990100c80444080ba00050440e0400243c40c3c00d4104496011603142c0b5451107807491640c00070902102c100c0c003941400b45040c0c000e42c0104003580260800c09043c402c031b944094440740e00341d960f6001800c070408814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 355373327 1250 355372077 355372079
    0xf06010e01030f02100e0301061403150717040c0902070c030b07180902090a081b090708090a0602071506032103060315020f0c01020403030827151f1806 67
    0x440c0049950403242c2151190801203015030030050410b090000f600c007041101815190280c0d000c0c80782500a00000d038400040e014040d00f850f061a0155804404480304caa040100113030304170341064810840a84050425611450a130581c003006070088192903101041501c101304c1d0a280140c00e5a0150900482c1036540c07800403a00050400400010380e10f510742d04200d41d212a030040d09d201360009040034141521081c00b546407640c01d580b40c40e0903c107521103003115800c20000f070303a401810500d8610124034000a01540c0c43c0013284005060941c0040d00c0000d001d81c40000941a4000a1060020b00c1da28204500c50743e00000c9008082c031142e922012b1694020312805080340c0e48084502059840905440d001390008884011040010482041440c2080c40140060751107611800c00f2410b20105000007039203220300c6103891b500029025407801000060124200c641d16500082c0707039807185010711901005440200c0ca800030481c002c10207a08142c1641403145601c0010844a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 355374577 1250 355373327 355373339
    0xa05060304030c060e0708030c100e16180b31090f2901031505060604080a0b1005030f0a0b070806010f0f020312071e0f0504180e030406020f0601 64
    0x40d00c41550010301183c1e585560300d0000303100da000401d00c900401c0c2641c1c651030746d884001341141c6c80404241036541100030350310105c540f6072045200c03010b0550020b1007a2441c80003602421b240900400324480c0c50b00c1200d000e90b21071034100b03080b607080182003654002480c815107810040380f607101e0b22003003419100d40210b1035110300c10304212135082010840008810748490b18010400c125004440203042d268070052501c2118290082d07100c0c0394840c10801c4070442690484401800310307442500108010017964900040014450b0b422955031000e9443e8200340c3c142c4110a40d02480d014020750550741d244050101c2ca6100e104d000c1ca4007000b42e070f5160708003100c030002c0448640d0301003000403203490381d4180710305504443c420550049030714100342c1004d4450400011580c00f800038009050003160340038142c0c00d0b41000d0040d810b00c4035141800e40b002a00501550151400518611800700f06600103608212a03012181081c1c0b0350f00c80e150f110080d168550722a0b401c100d0301c2520000690 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 355375827 1250 355374577 355374589
    0x705011505040c050d02030c0d020f04030b010605072003070305100209040612020603180a0b040b07020f0615040b0f0d030503011a0a0e09090a050601082514010f0c051207020a05 78
    0x40c0d4400350313407110314101410019030000d420103445810090801e1051240460f003510040086401c1002c2c1e09407a00d00c0d5140002800750141c00810070000240158400a40d13840c0384410209a101ca8007112000c0b00300219140040c5644040c1051003048400030300003c06600508091006072810f011007529a02e101950322a1214004d401420401c00100070301d03038001d05241620803040c01d89034140d0582e12807201003041940d050741c01226003001c0c00b0405804000014000b00e024024064519024280010b00841101c1c00b0707008a4498145410a59070403e036018070900007010140d1041c00d5050081064200340280440c00c1c0d11902441c40d2030004030309948002d500c41d07580200b101d054005004c1d140d40301a005a41900c04d4403200d40000b00c0034003246c0e000c0d181c03c50061060300101100c448008186000d58599400004400e000c0d0405200d920328441c0c0081c02e1101605082e000205c4a071495950050700e03500400ba924011007004000404a143c0201c5035600d20580362002c00c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 355377077 1250 355375827 355375841
    0x170403081e060a1202010207091a1810030605060d0b160908150c070206070f050f061f12031701180b01030b090a1a0618130b060715020d02070501150504 67
    0x251010000204100308002e94802c1c800045c81031055038511030303071100d00070700742c0303081d01c0e442c203880f03903d031114100d050804d5407031040d809200c1c480540883c10490042c0325500306900000e002541c441000641e603031506504401d150b584140310721194523041c08590144072246405000003150003100207076241c000036000040d01c0c07850703072a01200c1c0c0720040d048c29035a200c1601260049030138481c090101c0c02e0520071440030f1b0f01403030141c00140b40e131501c2181001c800400f802c0d9003042e90007040c84200d400c180504195800082121000012810107480072440f101d445410004460000700e12030032071620440b030308840c6440074820355108800643c00c3d00c604100064121410301e0020300003040c0c40d00038521010624400c03171081011007000c92240d9001d8a005285e030503088524443ca0300345681444100c0b51030300000c20030004c5a4000032f80a224a80300075000746201030303079112000840d504988412030f0300e07a000c6564241d18a03000780a04a05580f074064118403590002d42c6040031301442c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 355378327 1250 355377077 355377079
    0x203010b1f08072a0c051f0507020409020909071406030c0913060b0c070e090102040807050126040c0602010c0908030409020c0c030d0305090d0e0306040f03170403081e06 75
    0x2007980711180100b29541d04006255004108a0a989628502d008002101d600740e40f08072004521610741030513510000140d01c01401841100d40c400707030301b80b4170314401c0019180d64601203a480c12030740006409065013250180d4864212000c1c4103c1010000d484412500c01d8511507161901c0d003000c01403680411603006074044800c200859441c030300f01495403510070f04044000b41150b2200152441500f014480c80b459520034a414041c154050300b402d1b61181484001390319107410102010740b204414442c0a06101e01c84031500f0f0502c00c20703401c08401d03544031581000b144c42c0074100703d11554414407400000d035203807100e4403041030703c80d41541064842c603100035860189010007400c000d60100721520f046000d035140004890390309120029002e0015a40401ca9007407812181d42001454074288042c0603080b01c294242c0c0d140407807900d43c0705c2c0d00b190b2505038802040c1803e40720510502c0d01d03a424a56044200320416402a1095014500c89107128010003d0040340c02828034081c0d03109 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 355379577 1250 355378327 355378369
    0x60c0203031b030d0f0507181d0402010c05010504050c150a09031e060e061e040b150d0b04230c01020c100e03030c1b0d080d09140a0f0203010b 63
    0x201e030401007544440e00d142d44100c0b044030701e400200340d620b80441c0d0303410101d401c5898440c0b0620040c1030b4800e5910704400c01d42e030740d0020403030b00d8882001490107a00c0c0070130715803c001c42e00050540e03000740891101c56802200a100c0345c6043d01d0030035124075260b0100d601c01c4011580c100348000c601c20a541d082c025585a450503541582c03146e2109480f004c0c54902d04a41d000c0d45c0c40f000402c540a0710380300626940080000d42003040c0709a01100002c280c0f41001c3c7d001d1410480420450341030345d40c000141c4840a0b40c0080c810003c610b17400c20700c103405403240c0f042d88148020442d9200d400103400c40394001020308000001ca94585a03100d81d51120300590000c1010080c030b01d4054840d820031415410041d84070300a00011a0840e00f0800944000d030700b0600035403403202d200310a2072450307403011603000745040d646685215003070107052410701b041542c0c1c00100040001d9004102559468102101c4100c03c1c2464200222590740788224040d50801191900c1810450001c80340c0c100714040b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 355380827 1250 355379577 355379587
    0x3240f0f040f0204020f13030b01050d080d02030c04090204030317010e1501030b120a08040905090c0604150903060f06170604031b030215160305150109060e0a0308160c060c020303 79
    0x14000e0b151000c803005a0b403080e401c01450300c0981c0030724010100d0518030345240c03a002d07255080081003c039050340198001c20002c030f1444000b442890480305441000800140c480c4c450450030141e600498000c42d0080740b00042c04814180c1119127500307640062040030a00c1da880c0c0300c039000c008100f920720814001035a014014958040d4001c071507444806000145d81a04447d081850845000405c1c1c510700d400180600488820307010b42640f0060a0b00241000181100070a10030310a51040c01100000407454640741c134840e004000085130445801d0040038a004500d0000b05098850107540321190640740320b003040c000c15898401c0744c06860f01e643c68041e5100c1e0007458207080ca011011406010360030038680740701203e00390040c094403890722902403010710040c040b9003000d0301084c1c4c0b6000d03590a40005a9011841d41e041d41c02c1e81c03800d00d82040004021400c0180f007500028000100440d100011002d0707400e034150a07601402c0a410b8850350782e003066404c508a484040e400d0340003002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 355382077 1250 355380827 355380833
    0x6070b0714030f01080d0306061b110a06080601080a18080705010905010e0601050f0a0305070b1e0d140906040b0a110c01020c0307060507140304080304031704151116060c03090203240f0f04 83
    0x1134045c0d0702d01d0003043cbc0d400d29084541d00140210340310303411000201c0c610703205218030303560300000c0103901c02d48655080000e8508488400e40040003860f005105840000751001080f00c2034111308950366005009000388030500716080c0e110f04003402014028411254404c4842c50400c60a1003229084400b03025485c0c20150400e0469101c030300301c02e22031040b2442c00c42c400d4559200812808015000c0000e0035000e4224007203941202618040050340120140310225507000c5031644c0000d000c060001d817181400d1400445800380f02c00070349880d4800300700c000c0e802d503021000389170301da00c188401c0100b507580c030740151900c3c864049541c1200700144000b0f400a59980020764006010f400e02c0c03061000404441007503a0320442d03003120000315240c1c201d034a940141c0162070a004008600c90708004420400440701304031424040c080c42e803108015910b46000368000c184e002c0d005016100c1d01075031501007694125030602c9480b11702d48420000f42c2072107040c58030203024108a0b150a036558841e80c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 355383327 1250 355382077 355382117
    0x2040f120f0b0702010507120b06030a2a02061006020105010b0406030b240903070603290d080408060711011a062b090303140606070b0714030f01080d030606 69
    0x100302141d40418000440c404504900380300b922a004035400810245003c207802000c2e1600c1b40114070445081640c2454140e40e0f10084c0c80d400030101c83d00080704880043d0484c4120f0b802042c3c144004100ca00c030344226980450001d00c24050030021a0050759560030880c203c52003481090030745030b0b0030700050042600c65089520090002400c48494403160404944105d45090346040c49580000d50b09801e0305090081500802c914202004214503104004000000384408480b10702c0c0341c89910140b070742c0c400c4441290b442d00000f40e180c5136a160b00394203541d040305844c06c0c0041105002d211011000501820868504129205040f009a00148842d98000060f82c56080e880d000c00c0c0a890000c952400303510950184003c02c03519054180681211101003006107138411030801c2040d16264401100d100552100041c41240e0312031104803019610301540c0541080000242b20602c00404e40f840d0680f035020301501d21000c139414080e0100e03011403185d07501040c4000c40b959a11845c1c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 355384577 1250 355383327 355383359
    0x160503150405030c1b10020607090603090219151119080c1504060b0a080601260f060a020406030b03030901120b15040306020a140301030c030602070f0524070302040f 73
    0x20710031a4100002c1044c118101002c00d1100f81e007441404091050b03c0ca4032a2410152020500141055013014200203003041e05500440e0141038840e8102000c54807140c11501c1c480c1c5800680ba5415526081071030410301c1c1801091001849501030380e1208000441c4020040c980c02ea0384030849180b6a4400d1b4245c4c0044902e80c0c42801140c41210850141030342c0345120b1817280d88002540400101008200d004503086540154400d000600014001103045904583c614410f590074034607000d041403030804929400300d885e01032002030001c100010b80240c41a0307001618140a0f04501c14249541e034003a081d00f480c0015481c0080e9110004580e200c0c501800c0c0107007105070700300300380d500e402016071240c0d00445000f5400100c09541c035902a000c0003c0321860307241c2c1c40c03455155444040b514002c9000140216500251400c01c100700e01c0a92008540d000701643c030800c12110510200400900c0c007103d030709a2910025a905100e4400c85040c0c42020341048405800d100d8880d05400300703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 355385827 1250 355384577 355384583
    0x40b060309060103240e0717030408030d0e120a0e03010b040e030a03050619030b0f0903040b0d2d021c0b130b0f06070c0915030209040210030f150501021605031504 72
    0x1118031031780c5445060003100ea80310a004001c140d0985003260400840c010320489103019041404144100007012044511000d078251010403202880c805007400c00c040e45e00c961180440000783d2544041e00415460018007049000304414211241070205a0b49041031791142500100a00c00119000741e001d5608150007800041200720000c203403044809041d0416940c17620410100104003110811265000b03003980b01441c1030924003a8299141d001c0c1c0000c4050742e546400d00001d030402d40070101900c1d650340801001d00c2c007440e488030034020352006004181a000307410070f000c80215140502d00d848000a4a0306a09590150841d0018580103980940c003e50810401205075904c901501c1e006024520901c402c070710340080c000840e00c0c41c00503e0410600c106040001da80d5541840e50701c590181c851034050048990200d0040040044a14045e032030b02e5085d035101081802103800762002a000c46829491140308007180d20f0383d40c4240d07035059000b40814404106822103007500244 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 355387077 1250 355385827 355385873
    0x60304050a06110909150d031409060f0405010e03070b0417120f0a17070909020a02031603050903010c030e060402010f0c0803010602060f01120b0c0c070905040b06040b060309060103 80
    0x318582d21101500c000210740a030090004c01c0d041131514001d46015000396140901c04001c11640002c41c5100030f240201030148010280c20780307103148144045a07054840141220358440d03514034000c900390001e010340d0740004d4903290f8000c01410700103100c500303540d07075110441c1c02d0034505004110004d10320103c840d400c0c011600400125140d410140000160364070150307480d07540d006d5000b0030a08201e444011440410010700a40d103800000d00019600002c00c05641c0d00c0c40210203030300d944541d001c00103000711120030540505a01c200038154609045000340a071100b0150100e05440f140d10030304c03509801c80d501007001580505a41d1314044c4443c10410080038080d11041c1c82d6820907070205000d41c024008012034180307282c01c4180900f14140b0030440b80705031920340c1d060708803004060009844e00050504070380e1404002d0320703005140340c4000344164500340c50806007807641640d40601807403d2801714040d600e005000d07240700340c65420090950f0f03841c2d0380355201c411038181101c01201d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 355388327 1250 355387077 355387093
    0x914101509080303130203010b030d0f0e150c0a050f21070c0b0f0301090f0903050a0e0a05060a030b1011150c0721110c0a0b030c040f0806090d03020301060c0206030405 74
    0x1101070000d507204e00702100d17907148912000d00605003036542c0c40d860139100f500b00c20010f03003800b604407009168407811807034002403945011001c101480040301c240317a140103000c1003000c020034000400c00c8102d07200d50151244450707440b00081c0c1e02da42070748000206000010700064a42840c01c05011094014180c0440fa290f90701d403602c8190340400400b4101480000c010301c074180550107400c01c6c8801c0c0e80020000c008075500c00800500a20030400d040145150402c0800d81e203c3c4100310103800020200c1c1c1e55006116409002015194a058080e0710310000016a10f0b0003041619541260359010b009184800341e040c06c50364100030041a40c6072020721600d40480c085c407402c00c061082c104000450500510720150080300c00d4003c0c0b00c1942d104809101590b141d14081008a6841c0a070244e182e451b000910700c80c41c01150050402d40716040e800282c038070350015400b80180302c07000c107982c0100000c4000301d00783c3c802401032902107540d4460300c800604000006540c03207401942070b07030060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 355389577 1250 355388327 355388339
    0xd0c0b09150108101b0c0602070204090b070c061b141303170c011514040f110705010b150705030306011103070b0702070f140904121b0b010914101509 66
    0x7000a0b0020704003a4465050000140f505100741c0c41d070003189000000ba400b0010700000c0002e407411000902068002c1a12070440d292a04400100f135441a0780f007540d403801c3c08008020030a02042036451031300386030294a8050342c80f0030a88414205584804000e16502140d00c02070781312020a050200d440d240001c04142d02d00e03030140c0841103403e01d403661034508403051406d580c04809840700307042848608211a0f000750414110801c0162404158140d808604100405100f0301c4104800c02c0068440e0801806511504204000316445c42038481c403c441c1d103e030340c0907841c0001c000d540200040740300d03980a885000c00340c41c041001c4910b0b0010300d9503100c1a42e042546c121001d40e100010a1100c0424030800d032000e40118000400b10100f01d100141da4207602900c040c121084889070040924070440d52203c03c0043c0840c0110000958a03015407100400d11035841c40c1071808078100c002c0d05840c0101402241d22281480310182003003031030b8100740001e4441300c0500c0f00411000542c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 355390827 1250 355389577 355389613
    0xb0601051b0f0d0305060102012901020a32060403050a03180f060e010605030c0a051003060e090c0f0a1d0705040f0b03010503010609060b03011701020706020d020c0f0d0c0b09 77
    0x1044080014001643c2920b60140076a6800b50800d419641041b1031200040d0303450810407440c144200e1000038400c0d0401c010303410a1410003001c0c7c050030050341000d40d054080214010050510a0641c49504080c0c42d03090700c4180130ba400400007802040b6140015109030048030702040b0064a1038007d1080d583c0c0d134003d420710980100c07041e60301c0744114400e00d8028070880008040c164007821041482a002505914050140500c00c10170074940320500c61090344140040c048c0007195010f1030078840a01607441c0100c075100c511032050b00c0304415150906a14050840f0701e400c00040131140d14046030f40031808000c2c51002001002c0c0400a044480310009070024442c01c84041d5a0354100820b00d0309580c0d860f084200303c03a041500400140c04041c0880781183c00280800c21030300036080e0098064803400f02c003c2e081500200d0380d0540301e20305500818160424600303c40700c1d90b80c5003500540b84e0058440c001c002c10420381400d0080b402000f00b0710342c070160803010340c1c101e003d90000d4128 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 355392077 1250 355390827 355390843
    0x17041110020c030c0906031e070504091a010b0f03071b0c27020723030705030f090103150303021f020c01050c030610170402130e010f05061305040b0601051b 69
    0x50307219002d01c001e0b40c1804d0065019400c1c2c240c2c1e049078a860700c000429920a4802d54405018403600d44c951110700d4144078079006001c0040c014086441c3d20b05100c0c0c1d0b21100d10b6190003246900c7c0000041c020f90803003c031044080111001c500310b44d100c607010ba484100b050640005500781c042000001200342c02c81d4000303800942c0500000c41d81079111001c0e0816000f06002401c2e104200340b00c0894020030521314100d070036008000d410400e1703011490039409001c0b0010028070020400c801c22004141c00380002150030f076810000718481c01c14540c80d004041c4405400368200c05502d070304c4110104e04286c02030121a034051320748000030301240d0031200100c486007003941002c8140040351900303000c800d2800b411890f24101200801d001128142400b420003803240c4001b1410501002d15074100280c0528048000c110034403603803405501410f021100d09108907000c1d85013003581441c0d0704c1050b0003139421542c100001d0350b42000544550b03100d100d0030100e2103d182c5403182e5071401000070f85 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 355393327 1250 355392077 355392109
    0x706060305060912030411191206050601030b03010b0a05240d020a0e0a0806010b130b0c0604031101060b0313050f070801020a12050f06040c090801021605120703170411 74
    0x103414540300c20f855040810361401d1a019000030801d100104007480c2200c0071500003219070503200784da01e540b4040e4032002c40c2d011501038550310f0855414040c0070343c405403050101307803020f106e2481d20300708050880da0304480003075000000c80828005da04090902040c1204d15a90240008200d40307200d01003501b00750f036001a8a0b030001340b1510368a81c014800951480c094039400d450504224810342c442e4814001d16840c0c1c000494580c0d4410043e000080080031000c0175182d5400c03031440c1480c2c80d03140489050b00410406400940d6803001407145804850703801d89084d0031030302c1e10b0900c41515490031506641a01c1403690108208005001d00e07001421680d00044e6206010b0310003401c1c40709400388041d030151414040000680ba01120558030000071203000540c000290801c1d20000010f400038034240d0301c08500c03100c407032803915004000140100100c0d0742490050340ea218151007549001000034400700c540c1a12a5064a22240c00074414807071001840b03088808201030000b009145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 355394577 1250 355393327 355393333
    0xd020c0a1104140403050724051005012307020f0a1818080306040509010626070b0a020717030f03040c03150b0303180301060e090703050d210c03020706060305 70
    0x80200032195503207498200301600d00340046004001c0c10b00803c400200050140600041c0c0f01040010403001182844030000c0f18020a02c500c0d005400146421100c1000582d0030300301c007003509c0d03008000c82040038271101000d001e030180c540c10b06046900b248404030303000540101c0c2c84800d540d0341c00e900006026807401c1103442c0102040c2250550f6840e05004914051801d0380360081403c08003141e82c00700040d40c0100352900e94000301401003c25030700443c110035542d2a860420400c1d600c00603c091030100441d10403544641c0c0100c1984915401c0c407000da448007404128801514a2403209150040c065a00340401c61081584940c0708950032109102c110394207204205680100c1e400c00b2400b107404128040010300425501d10440e44481c02d828040c42190f511070b0340035044000030303010207100c1c018181484480c0b25a220701a02045a8034020701d1101402248642401260300481f10843c0c5100300e074504040c401011008065420140c00b0440140071808a01882006520407001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 355395683 1106 355394577 355394593
    0x30f0408090d05030c0d081e0601090e090a03030608030a121a12010c0905030a0309030206250f02030709090804030204020f0c0615040b06040620030d020c 68
    0x440c075030102e990300b18841003060200207888281040c000303c496051003403400343c404020494156441c429841d980d05085000c0c0011580c2015041c10710181c2240c03200c900c46a4404c08403603032181c4d42c1c4176404010401d075062040c44020b003c4400514202440324034010b0400511840d451403054070346a0f102e403400801c00400c800c40700c00411003003414508481c244c0c040c050204080c2d0110b42040b80020382d604000c58910400c2d54903645284080b81107508000c000d070040e10b01603089240c05c90a40e1440c640001140d4102c074001c03030300da1182081e1481014640b90494000310610380c01c0040040003d0781c11001d54003a00e5044030003607203584044c0c3c0034115030701510075100007a00c1247c0620550b05414801094128003c2c0c1d01409401007120a000707851050303100f080c0c0090400200303041c41038004812540408200c4c400c1d61300c1c2c03040c0c1010000607a00809a510f80b07503000218 = true := by decide +kernel

theorem cover : BRFrame.Cov 355215827 355395683 := by
  have h0 := BRFrame.cov_init 355215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 355215827 ≤ n) (h2 : n < 355395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
