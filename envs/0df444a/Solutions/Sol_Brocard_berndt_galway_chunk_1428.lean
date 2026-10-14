-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1428
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:56:16.240043+00:00
-- url     : https://prove2.me/submissions/677b4c73-5f72-4170-918c-bbdafbccc02c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 256654676 ≤ n < 256834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 256655926 1250 256654676 256654687
    0x9090c0e030705010306120b0702011b030b0907093f030203120108061504020703032721090501050a0908070e010905070809060c1818091c020c040203070320 69
    0x40400c8402c0c040c0100742030510595091800700c0980b80c48000c0c024160300044408103180a00030340c00340c1d8480b000c4000307501c03000c01098400f40192001c0107990b8003031628400000c0c40e031849051401301383c808680c1038522855a0500c90201020901903165042c410b200c090554060000c00d008201e0748242c001c0d42e02c900005010325042c290503800704186400070810080746542070000c400103940301315001625a9130b1401c00724000e040d2842101c0c1425206814011041400300420782118070404529800c0015201c1c0105100070390301c001c03004501e0206082c005503014074054910844985840c1c00415138a55050349046103c0d400b6110350742c2540c00500650643d405016806525420502c1090424981a55a40c00300400400a0b25808039650824000700100890162341c000d02400806801880441018509881c0c440e002e00c01c605001444005071540c000c9484c14035005015074895040c00c1c80061740c80101140308041d6a02641c1c01e2299000244100d0030366103c0c0c48030307140c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 256657176 1250 256655926 256655929
    0x203040b101505070201050d0b04060801050a0c0504080c0d1a070306030309060e1305090a0206030c031501110a06150801180c0603022d0c06041101170603030d050709090c0e 76
    0x1540a50018510400d608812100c0c0e83e80003400c8a60702942860200d83d155000102070740288620088070b075000d8106040020004015084140030f52600803082003050b105001c284c5003441207100310010b0380c00c0308100c88624601400e0081440d0f0007840f0ac0340e030401420058071441070301181c2c038401003039030352805009155201d8000000341015007448800ca40341180003074a40f60140c041b100c5c209403260002500204140824000e241d0b014092076140e040405d0401d0b0345070000c0b2030b00380040300042220400c9612840100c1c2091060502422040403603480d580302a003400303610024100a102c1c400035a80b6800d2180e00306050014888006416891406040340341c060b61201c02003500501400303451100762100c4052560300c034030030030014144120298071540a1049200c0c11802104100400d03c841c55000c0e407844002640d81c081c0c60803890450140c0c0203000c0c0c800540582c414030012140168a900c200e4100d0050b0400300400d658400c010401d40f91090120800120344185180c0309 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 256658426 1250 256657176 256657201
    0x2100305040c0b0f180a0b040308041d070c0605130b070203090a060504060504090905070302220c0c1e02030703150e0601080c01051c110d0e0d080c03011211040203040b 74
    0x70b040d00240c010720f003040b40303d130600080c007840b080da50004800070010300c1d0702d40c0c819014000801628501540740d580e00e040c002c6013500180f064012513618004582080d01c00308008500c07420b000d40340d1001c0c1c841242c5840f002028000c014922040346014028049241551203510403602a80250b030740b101608240882d5510701d501c00e070207014050005018080d0004c0030b44051310760300b84000a0440d07140c1086480c0040c81d600c040c1d084100301410b41c0307200f0010103444030075415aa01c14031481000340030448200c40340420103050415402e2088070b1034030000701000940d80c00201102c0700300380c5a890b0140720411103000e850301543c0d1880d0201c0512000e002050050000238040c00c04c256503d070000c0c1603840340720b10b80150000c8298401c10050201d80c0000030003203c180c08151980b003c1c52114006240864011240b40708203c80340c0341c2c2d10f10171440c140c840d901030040d10303042d6441c160010b10001d415100458855a071000795444548852000d14481ea001e00c00303c0e130480c101040c0d030040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 256659676 1250 256658426 256658429
    0x703061a030105091209010c0602040b130807120f110405070e010e01110a0b041b03080418020711190302131d070b0f0306010c02040920010302090d060e030702100305040c 75
    0x82e410f1904004444501180c030807400e0b11100252541da100c0c45d00105c5162010313075070040c244c44c03001c640840e108401001400426201a405400c030316203c1100558a44507031045008424030074104c10f00003070204164400d514403d44944134041c0c44800014144c40c407c481d180d0000d201111111107940e84400c1c0000846030a081c510b80b5180740c2c0558644511601c00041c1032a0b010101280420001c0c40c00c291080444891400c0d501d03407246480d0079940d0181c860941d084548000b075000c1d038019403085441099001d030b51441c02d00088024407040c1c0d0390000b04180001034059002025880d0308002c0425100f00b200c0014021515581030028041c540300c3c0303000703250701141c41803100c000b01104031a071030f02c0030701c140580302c0da104c0004848100341d03098000e41203800d00c2c415804100340c540f0100f1350502d100d80e0107071114880d000110100d000362803400c0d601840314106070300494034907840080708441400c241ea24107482600410250660300600d40300082c2c3c0d50b020041402059802d060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 256660926 1250 256659676 256659679
    0x63405091c022809020f0405030708070305060c0405031b0102120f09040e0106060203160203070b0c010903020d050c03041424031b071505070c150e01060f0608010e10080703061a 78
    0x3080c01d82c0b82440c8500c2c00c101402070500c00d0380c0c0064240001c01c00203051f01d0051400404684000d503e80021985800040c4421944d9209800200d110011414141c9094542c054028a1001d651845207014000026819410f602654608000c007074050001081d5910f41c00240c150b031031026505003c11a10b03941902011039160240a019680d400710407a03021142c01005000a440e4034000070b404c008641c0e003c110010400124035000c1c81040d008060b03158065000e41c0c00021644200b41d80c1303407046d0402d11645030010081440708405071402c11a2000e4040c20a00902c1e81e0f0890200c41441c1d017060301c40300c0620200c1080561700d4650103010181c3c0708072500e50704001490751440d201c00e011144003c0465202d50005d04082d1103140e903c006542c00440003080004001070110050072001c00d200c0d86542401000314051440780d00ba40304940860f0b40d404056840c18800c1211254050711040700924103202c00200042c081100802440c004c41c00082c0c845050001c140c000416040c089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 256662176 1250 256660926 256660969
    0x20c150106050901080a0f02160303050a0b01140a02011107030203042108030c1803100501090606090312050f130801052706010303050c120706050603063405091c02 72
    0x41c04165488015102042000e00748109540c07120704a91024000d200c0b54244000e101150020640402003d51000a802500c0801240d1202d481013801e0322029000d0b5804030700381c5409124070140d41e80061180300300300d01c00000c51046401040c40b19a00040381980181c0c0045014040310b800c071000c5044075007450403040e400407410b946409490100031300ca12802100842c40020a103c1001c4110790600c005055800d2030140d20440401884203004110b8668582100070420a01400040382520703080520007050000c8040c6c2214650b106404050005005101c805a01e40e001d00c070541c080c10f040c0e000414207140a95096a94086842c0429692805000307010191000401d0b403d0540307800d450401c0d55580c40c00345181c034100c0c5101841000803400200c00d0103105203588154001c0b84120240d88c80d03038a0380d00c1c0303078442042c03072500700046064500c0c6c05041040c0312030050f40706080340c0d082c0f060516078020002500505159084542c018900d80c1900c210300d00305100d030b1510401d04024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 256663426 1250 256662176 256662179
    0x509030a0b09210c0712141006090e010b0f06070c0e04030305190c0c030e010219060605090106021c0807120501060e010e060f1204020a0306060b070b0c160f0f0b0a020c1501 76
    0x459680d05c2042c4641c5000e806600f1514041c441480700c1036400c1d07041c8408880c0302038420141180203099a1056a0080e807801e49041d40c040418040c040246c50010400724450100350108400e036801240300301e4444980600025181c3e900c6200107208900075240080c02d0700e021840300501b140c1541d4003200082c5052480129180c0041601c1751041e014607000c458000760000603454450700d058102d2403001202007460030040d40c1c0d049681a55001da54003100381e41d0b60354041c1c0e510b000d070207000c415a044110500c0200d9211b00038103070f4401401e01e0400079241300a0400000c0300c9013030b08450000345540300b80c121b003960400300482101c070f400e941403840c25030040382c11103442c000c050800c80085034003000b14003950f8803856514055034202c1130800c202544c1d2080419641c0c4030309811035403203000100084148801030252504414100c22080c5c510015a82d00b606107040c0f464120750010401c460301c0c0c081114100001d20481c02100010b0b03940c0500e02c3e1003441c0c25804006200e010080400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 256664676 1250 256663426 256663447
    0x30b1009030b0a0f050901091a0601140a03062402060f0103030f0e01050705010219091205030d0f0e010c0206010807080106032a08060406050a05060d0f030509030a0b0921 75
    0x3a1001c40c0c1e0004509015a11600c03006070182c0107241008003207906040a0000c0c803041907000c62016403080300c10760a0900d850b10308181e090011100140031038041c80808a400c6517440051a41c2c1d0098a0002440f944410042600481c031080d80c550b0801c0c03000312800c0c1daa40401203260003514080e8082c00d15071555400400341e01c02c0f85244410045207505400c6c283c1d014100340c0302d6241c0d1000c0250340350b110321000c8000120081c207403000003445901c0002030180c0d154120f018041e4001d00030b503203028601182d481c040d0041000601000e9903996401d00340310428460058244400d074058042540341043c03261030070140343c20010199252000c20400510300121050440a041d01c1c0741c50b500b8070000680040380c086504c0340c83c080c0100010042041002d900030391040e01070401c02c010a4840606002007813585c410f006105411007a1f00d04082801340d805091100e00080c01c0341c69139109607890741800076043d5001000c9912004840070020f07030003041c0000b040c00129006040140120 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 256665926 1250 256664676 256664687
    0x4091e1407050a09050918011401030503070b040c0302130e070801180b06011407030908160602151503030706020304060c0503070f050a120606020c01181a09031603080a030b10 77
    0xc14000500c03100140e40c0303d0030b500480a0f01d005080c000d00380d0326145015a01503441c0e1450302031032841c65191007041e010744000c45264505a1785c00000031401d002055942074040d84002d017007510f41105400d0000010395810040c104801e00103000800e481b40b051080034a803840340d402040e440d90405070241042500080800100c8d50003040340c900d070b603c076000181c80310301426050013507060000609106140c0c105c10003030202d50111044408030140e0000c02000d8165900900d001a00800c11200440380c40d8000e4039040794115020b4100360b0350002c0000e10b182c0c0030b110202c030010b401104200501032a441035201010b19800c081e491454150002000b0b205140755078410b0120100c0c000249910030024075900c0809400104509525a00c0181d1b803004a0b20015000460121400c0040310100041314122041c054034041c50360300008184406400c407003209500f521442841101d8802051045001117009849140d41d0b000e40601c018107070390030405654011021302021905040c0e000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 256667176 1250 256665926 256665931
    0x16050c0f06090f0f13020307090305061012120905031905070504020906120c071e141b0607061e0c090b030603100b0303070c030305043011031204091e14 67
    0xb1518030080b001c0d800000b45445d0324202c4800c10f802d10100401400641190401c0152400340701110801d41d902004003550541501659031402204c0b9030f4040068404440e8000d5081d403428500403064540c00401d107040c0f01c0490540c00c5581e00700154050110a00050300540000e81d0700394a0811480c002c40ea41d07204c3c500c642c0d4a240b4103413000464020811040e030304595803285155200c4103a0044c600116500c42c1e44c195100398031503607858140d201c00070f074040200c200d0045442d0b035080c0c42c50800007203400900099a009480394011417003551446594044690300150002e0090313031202000701203010030f4000703105000d420402d20040d80c2e400242a081c05103100c2d070200388030003242c000c83d00714042c0300030040101c034401d4008010503070044040e106468200358101c981c2681405c0d5894408280301c202c0c8640c99000d0b6150000c00c41c808411072644801500311f807064005040b0a841c035621a511800c2404d9a030083e044c0c1000c00420407111241400c6000d000c02c02e60940b4281494401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 256668426 1250 256667176 256667179
    0xf030e0f1203040c03081c0f0b0f19030819180b0306060d090203031804050705160f0501020708040e1b0403080d1a13020315090705030115030216050c0f06090f 70
    0x302c005030800a002200101641e03105055948030303129000303442200196140c54030301c61400c1c881c900381c01800074800e081c0400d400514010b4041984000c2c000c0800f441c2d40c080c0c06040e82e041022004c0354080300200707003800a44d10000007801d602540184400340d03004096000e1848088108015074102c810f998005104843d495601d40d00f0203500c00c020300c40c00d10003e4041c000820750003101110740801c0d4031204410381d000c1c030041d07413640c1c800ca9030791080b51107541c0403034121380071500400c582c2d20141c118907204100040c82d11003a6103481a281e001079202d003022010303140400031403070000001c2403614400283c4d814145801c5036100301d078600440ca00030660540d600c000b640800c0d81e140700107030719030009404048a100594489030103540111401d1030001800345d0061224100914600d10890840d0303078040c1542d003000400c00d55060030017484810140c007400300c45002c481c000c11001d1003a1281000b0042d0030700e4281444205a8102c04251141205200750302464690728100d5030007450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 256669676 1250 256668426 256668463
    0xe010b0607050a02120a2d170a02010b041814030d151d0f070503130204020a17060a0807050118030c0e040308090115050609010203130303030203010e010b03040f230a030f030e0f 78
    0x21f022030340051040d803024000300301c03501c051040e050841e0010310010a40ba8002d01030304180c00144000d4a0304c0d0107500c52070700c1c072000c003450100c1c0588103401c240f50750b0481030ba4540010026103000b5120001c03c40018400c1000c000c002110180c0000418090b410016110502d09141a401204c0b03000745560207108000000440842c08442c825401681c018011901e9a08510005003505031008080c8661241a804070340c0301d24001c00703440100c0e801d0000409101d810f00b001143ca0390000318190700c0c0040d900002200150607049100007401da040e1402c0c40914150400800d40e040281140c00e643e45852081180f00d40c5040e56032042c0d0300165255a80d60a4040040f440e5124070101c9001020701ca00c0c0100c100b5a140d0003c40c101c030030100b0070080d243d80350142c0c07806074442550010301c1c0d07004060041d0006404650001014184445d0380041b103100c0501c1d0608000341114128000303054161303030001854052240c0500f09440c40c008022400924005503071380e13210319a08514860 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 256670926 1250 256669676 256669733
    0x3020904020f12010b03010609111e0409090302030a0e01050307080f280b0f030d020706210518100e0a1401020f0a090f0b090d02040e010b0607050a02120a 68
    0x4442e0140041c2640c80a00142200408000d002c1d000307080000129100394201038000412031002c1c081c7d0021750600c600210b14004509040090000060134000c00451003404005078420340c80c82081e00c824003036006541d845060340402004408510303030742c1c0e0510800348240060681d000040584c4114000a00f070519218480c3c2d000300307418050082281d199160071558a0040d681d0003100e0350f1101500c01d040039841001c00c00d6241c03000c00313200c0001a4025041001003501c01c48442aa40381201d070001d40b0350400c1c5500c1e00035914211303072000f01d14a074030051140e0b45200700f06072400c000c0004c0040110440c4900761644440861001130b0404e5a42100d5100c018820340c1143d0010a803109269030707900d42030001402205051084d514400c14444000a4412908040710004500200909007200c0c881d800c0000a001014034907010790340c1e80302200400d448040042034283c0c042c0006044e5401d2034410030451104c007041d11801504880e4407240080d15809000a0781d1548500302034149 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 256672176 1250 256670926 256670929
    0x30c0d090611042709031e120e0102120907120602030604060801060e070908010204150c0c03020901170609030a080705072901031109040c06051c0e0303010806090105060303040302090402 82
    0xd0002186000c600000060002904c080000809401900c00c03401d02001844607600c40d012a0140c040141c081030143c40296a10442c8206810014003c0c2c1085500041c054070b001c0101c07244250342d03014580d8005911045071022130411503020040c000244652800c003480d0803082185214000c01d07142e0040082502d0703556640007038004d812680020801d2640d1f482ca81403901400351001004192410404251090180216800c0d01c5640203440800c0b00320550403900c0e41031081060302c601603d441c0220050383c45075030050081c101c015070580c0f5a14034017456800d0640242c0b05000e07aa10403c90b1108940e080311081f07910080f28100076807a05420304002550071400d06481c200c103444c0b40401c1c401400710760242c506882c007074a040c84802e80c0721002e10200c500300781c4000c0c18130142c642c001c21146201e5001403074180b900301c080c00290105c4081da03000b9a8961074659145030000301c0144400c03a405c00500703600c03a078540024000d07820301601090f2a40704901010b230040a8040008095 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 256673426 1250 256672176 256672181
    0x181c020c0d060f0504030503041712150103021308030c0c04060312030b1207030f12020a0b010e1e040f0302010b010c0305070602160f05010c020c10120e011b05040503060606030c0d0906 81
    0x3c558105112514091034018040c3d0b0080324112001500c10032151039000b0b8550940d0404054a408a040c648900240710300d00900018510304260b02081314810704d802060281c002040101c000355211a2121141070078059542c0e1158001d61800c03e0420126445c00482aa1043c050600041000118002c281105901c6441e0484c0c4d10075034000008000d001ca8241407178038007031482e4518010407030070100d0311581c06c600042d08900c03101d0018400e42030819070964100b14401284c03040c3c1080324030200602042164240d41e01c442812410060540a02546c402841c003442c04402e80d43d01c581d80640306014030480941595804a810301c066410031005034020307134000e10850403a80d641d1070140d019210021240c4014000c1502c00011814421007040000b4641d4491001402c14100c80304002d244000042c1c1c103640d03e880428402544034094071f01c4494499032402d580d41d007050281450400060b00c054000e1740c00708100440b14841e00c099031032902c860742012844c807140b070415001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 256674676 1250 256673426 256673441
    0x72006070b01140d1e0c090b0105070209060f030111070210020106080d0c0c0b030421090501020a030305040f021906080105010e100302030405070302061602040605030109111017181c020c0d06 84
    0x285c07000090180070340d0f0030301c85158044a44103000c41180140c40f4403000d8240d81400451a0100f20705200391300040c1741040011354410380c003074034020f00703c0c130b0701d41c002401e45604000003c51058001001d10035070600c0c84043c40c2d4003800d40000d11030780c0c0c40d00344c61b01d50300c100c061450401c0084410075041000041c00c07005000300501c0040641701d091604011a41c0c030086a60180d0b000440d00c8000409405400443c2c200c3c2c80507009085001c01c251400d40c09031034018003c0710b042940380880c0d00141d482c14400f14440a025141139026403c0c5400a0300880301a0080c40c107110021030154090f0352081c4007041c002c03e0380c1c0380240c1c9039115450b0903854100c2a41009500050215018000c00684154010164022141400310a907074405140c201c40c0e5210300a0b007160580ea80c0100903081c0030241a5641c00e907443c0070300070003601078954404220240c0d0301e1608044883e0080c03264180400206512101075411520104003806c00603603219050503070385010307007503048400c014420503a1140c0d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 256675926 1250 256674676 256674683
    0x70e01050907031112190e0706050d020f041403070602070506040303110f0709020d1107020a05061b060702060601030b120d181706011d0405030904050c0906072006070b01140d 77
    0x2174035048042c0d03120740c1340300f82201e042007540d10310b00042e01a2003042c00707101030410300c40d8042c060306070400c3c00031981c07940030301c2010852a808028605940d4501c00040c0000d00080002200800090741003500b0a02d60b0307440f40045500c0340314280b1460743d0303200445007181c1c0d0500f000c404881c0071007101401d101503800d00c80740074001d0b403a001850090b0f5400500341101d240400f000810789070400001c07540101100607411015001e002c0c0000e04190009185c5900f181201d051149009003c0a10301042200d403c40141c01910070700035a175825000d844550b04084418000c00090b010002d41c1e141602282230082004081d0004d02c009440e01c4854051304180c00b100518400c901085a0380700b00c00e00c10303031b00d80c111f03c03503120071f081c02520103064062503016015501c0c0824080410000c0c040180c60420903240800c0405019a13496005148051144800d00d4425001c004001e1081581801d0701d4000c1d80700300b1101c00000d034011900360542c0c0c11150400020a0b0703090104440620010005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 256677176 1250 256675926 256675961
    0x50d060e070905040c1107051005090603070908060c07110415081203040b01151704020120100e0f0a060e1002070516050607020108011401031b090314070e0105090703 73
    0x4003076658012951410780e0000e880510800c04100b0b0304a5010003030031741ca40c5203904282030038403480c540072408080e0040c0300c0c5002c50030654440c0c002100c0707500542ea2070010615514007040792140c2400131580c01482e80b60742504290b50b9032941d00740445403410b4184100e544080f0680b041d40480710901c0540000c108440c0c105481c1c4141c000340e6402a84c00351000840c070301c0000791130300607400c0c08050f401050391002c20001a5034620050700e00050301c203c2c14496030182d200c00c3c1030030407a0300b03c0c1204060310042072000240440c0d0f004896007400300c4030980d0450280340168150010b950407105a1101c000624020900d00503401e0500b103152141803a4000120724061042c001414030010520f54100403441c0d581d0020003000d4828558005e002c10b418500400c80f00030708241c2108509018100401c154060304190754502c14410304404c046407403004140103004030032000c016803403104802001d0241c1070964955241c00c05204080c0300341034460004045504c01d812640c10400c0c0b0410f46c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 256678426 1250 256677176 256677181
    0x1b020f0d090302060904201917010303090303051305062a0105041e02040e0609070f06020303010e01090e0309031606030b04061d040201020a153e090102010902090f060909031306050d060e 82
    0x32208c1030450746810b001500786929801004a0721025604a84d415110103402c28a9641e0989081e08140b00360701c11092054000503e680311800100060103c0c010652009410365000c1e0268200c50080380c0030380d80c581810400020203400141038007403182c1e07200301c580400602c001006045c2000440406000c1e910621010040000e280000d481c035291481c0a03907520f402d8200da880c04248613000d02250001c1c01002003210582c40b44c00481c610000340c0307181030100d0011900d00b1401704c00000114980c5102002034640c14801d540340301c00c040310300344203251070b0000710200f43c22002780801000340c1c603034049800c583c000c000002d81103500c62280c0810840703a070781480c0180034014502c4058210100e11900c40c60140e81058070100d0324410130412480d000911814503000720100d541559600e81c05200980c1d1002a441c0c0304d41483c1c0c501e11754900e8503105014003100c018000c4405070340184900081c0e0f2142c0300d040340580d07240345011911480c013001528003408030741d030122040f000450b09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 256679676 1250 256678426 256678447
    0x11b050114010e0601020a080d090314031806150f060a0905150901080a090f1b050d061e09050601090b01140c030703020f2d011b020f0d09030206090420 67
    0x140c05048500d400840481903a42e1300040e0303120103140d030004003554801c02c00011038000552000314110f00074680782c0c41000280c10a12800d80c4240c2e41030a015451034030121108004000403503020344500344a05210b4880d0002c288599420040e03607106031000f007a2a0383c0240306144210040170700418107203400c250003001c0140d9502c800e406500203078044c1d00141074800613001d807030455640502000800c0d0581d03155160074048401103000348411900000400e655909149910075024404c005070b01608020208642d90340004211901410906050301145012500d82d0440d2800c6c080801c0c0c01d81210f004031182128000b1000c41000003207030b10520210000040c20b202d034031a4007140e80e81c0c0006904036a0316981010030ba0b41110645024280100102d00d03c0a80c098959001044092001c91030007110900000d0800c01038ac0098482e1724000002c000c1c8104485103410030896650454000c01d080340303e4010b02901850b15400090248909651442d41c01140c40300e01a0302e8002104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 256680926 1250 256679676 256679711
    0x50402131820031c230d050603010e060901020406030b03070623070503070b060f040b0604050f1f0201140a15050105071a07050d23040b13060e100509150105011b0501 73
    0x214404c000412110340754030b803d04030000c0801407a203003528541c02d000000c081c25002d88401420b660f01075403034101c900440401004001e00440000e4005a111800e107030005003184c60003c9018030a6000801c1000000d401104446820411001d80c900702424222501d2040c420311400401c5032200051039410f03c4003845501d40600b0341203c6408144488504000c1914001c52660343e002c0401c01040200c1d20701041c1d0030252400c060310181f0703010401545141e90f80001d1203d43d0240c6d440724100c1e1200d42d0700000481e800b5800c0c3c2e408118016030b448001131031b40203600685051000018440e0280a00384003003016002124107884c0307180c1f809601c01440b82c3c1219011411090030020568030401c070007509000c08d0310460148078040d954a07110012424005004407a09100e2140fa12021504900403441c890b86100001c07d1032403440414601203c0e001420b00c050b5400020342c005a00040c009918115113091800382d40600304017441c2003004070ba29900410a41c80d050000c01d6640d02fa8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 256682176 1250 256680926 256680973
    0x1504180f08250312050703090b011e05030f07060f050f0a031508010b090610030b03100501051314040b09070f290a0219110a0905040213182003 63
    0x1142c40641082c06601c0c0e141d00010b14080180030514800f0440350700e1805a0009600c400c60f0f00d4041855001c81e02c1d000c0d500c2c40c00703130403603a0a151562510180c1d400c01e4241d20004180507001032201c0a0740c0301000f62283e11a0051004002c4141c0f6001d0000f0302c22030660b030981c0305200401c0d580d4560b5120140c01098400c28980e0a0105100001000e00041c402c1d1401000c0180800000d961020104200b145100c04a107041c16665484a201c684080203611000744500300c00003015418082004a45440c2420100030542094241400200d001c00b405070070561000d0f42e00590344807694114103241e070642005107442c0d490f810010f01c03a1001003200c81c40402c9900190350f14040305a040c1910310525405501583c4200501200942041e10f110203050003001410b480303800f44800206000155885000d4260f160000e110651404c3d10440d50b10f018152010000b12045440c102e00200382c504002d480c0802c1c02c0003000346030039070385c030007080d5040018203440c0c2d00c040c140b0b04e000760354030b80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 256683426 1250 256682176 256682197
    0x2090405061203070312060803160519020a0302010c140d091d010b03131a0a0209011b0209060616020a0e0f1e04060b040e070e0114091504180f08 64
    0x14000400d0403030030804250329000c162540514a413007415107007170302c4d4040c4024407241c0583d500c01e000034000d5004d1018100300f406180000013a42101e00b40f2a2401c480b9000c14506d580c81800c001c401a41c1d0302e4504c0c01180d5082c20440c002c41d01d6410001810326014029443c6170144140c110011580001500309680400070841950b90311144071817a4100240100c80a086041000c1010030f0319001c0c1a010640c858074000c08511904507040755110380039920218151303000724800c6619038111040950302e8805010702c090110107138002502d003190181080b40070740d10005000103076401401d0402c2c0620b80181501010300d540d03110500015008646681ca802c01010224071989010380420324020207500c00c010243d203594856000405c06084807a03889030f5660ba000c0f089403010302c185401410401481400c6601d0032a01e801a154030a40303c43c402e050742c0041225000b00c004170900e10840644000600011020750440b29080c520009848600080c14107010040f031040182415002c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 256684676 1250 256683426 256683431
    0x90b1602011a060304020d02130606050a0f18090519050c0309161427070804020307080307030507060504052b030605010906020c101b030519020303010501091a0d0e01020904 76
    0x5042c01c1200740140e42210031584160108049005407401140020585000500b520000c0c500350404104a40450340700e040442c2010903c908029040142c20306a00054203000c00d10b002c141102c0c1e0300810290054290495884000ca08007080740b948004054000b2442086142090444003180d6001160b12511600c21010449046200c0c0c3c5440301c01c442d00300c80520050080f0f0420000d505d2490300d14003100d903801c80e601d002080181c00d00e10f070041166448806081c00e2078010300d4100100703178000890a605c1004603d000035440411030f200c442d00200c00080c142c540d0328200d41070810807000500440030040c1c100035443c080341c0301040b0002440d24100701d035568404c0159400c01d403c0c490135002d6005024055090b06000c1820303910301501c1d140601007e001c90144d4a12282207420503000600c0200321020814030000101c9c1c03070741c0d026000460840d854a4002400003e05000b9000360390450114200b4148854007a260455081001400b00c1c00c10050218002e4000d403065038403550 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 256685926 1250 256684676 256684691
    0xa1d100203011a0c030307050c03161209052409030a080c030d0e010c1d01030603020a0b070b010e0c160302030c010c1214060f1002070f030c03050607030501080a0308040303090b160201 81
    0x10f501d10100d99462a045015508541d6241c0b03068030f0a0700040e0081600307000400040492800c225002030444d441030121462002c070740341005181088a4008038000c007a842403516407414894960134004a900c54400e556041c00b1011a0800e500749400820000c808140b180720480003101808280228110070000d01948210450903150342c100d81c01e010510f01190440d100c011100750100c0c4034018100032580c03594990200e02e40740070590096a456030041620750420000403440c0c0e004246450084540b41171a0111220510451020032105260384003c0804c042c001e0003502c145100890080001e00011000078000f001301d0312030100014170f04000356040c02e14000106008190140c01030984800300e50602280c6616500314409600c140c00b800242d000c142d05011001d10f100300d1080180b6840c500d8018582600601004145800c000052004010015113000f910fa0145016141c030740340da050680003401840c1010341b4203508582002500c0c1c418940c03200c00602240d00070080c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 256687176 1250 256685926 256685969
    0x605090306070315050d2402091207030221070807120210110c060d02040305010e010b09060a03080708030c1c140a150e041a130b0105090408030a1d10020301 69
    0x1138a1030640900c014108a6040c4124200f1090b26501e43c0c2c130030001c0d40c69102d02d070080342442074940f400d546025a0000b42889040c01c00d50043c88401c100b0340300400a42e030441d40060400380080a000305218002c203450002c11000b040402e0081c09810103940c60f594403603034502651421031809a02400f00d5480251101c2d100324403034040e900b2528064040c590000040041603480003c4400c4265001d22010000c20020320500c000b4500d11800000c4c25604441130041c00c8800624035807203499880d10420214200100f10780c00e06030700ca160103980f595601903040141c0240c80d15140c42e40070000d910221141f45611075403070105221181d00803a030720040480d05542c1c60000240416510113400c01c400b6403003420442e0030074812138a08400198111182800794812501c14424480f90440001448946202540903241c2901c04c51128503240e181c0d10340e0b0344405800410300a5071440782d10b00c0c0300040080c052425211a013a140c80300041c41200d030183d0400c1c0500f80f0752202800d03403020030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 256688426 1250 256687176 256687181
    0x7031b020d0215010b19021c020a1e150b06070b070f020708030307021f0b04090b010e0c03040215180604060c1a06012703081b061602100b0a0f06050903060703 70
    0x40311115018645403420a110000c12141b0304c030303085030952041081c40307a20001900560002a0000d40c0100f10044c075904040703007591240d0148401441c0e2810f01980822901c40c2a0800c841c040500071401316041c60201d2a503209212015044024500c140003505501c80b003150f05410b42642118103050311525a180c40b0711058414a002da03201e040040380c0b2103003a105c20510f00d800102c0009104032202c010806995410504803107845031074006200002c4d07109081038000e40300850b42c9045140a0780400c0808070703030801c0800d14400210301403800041d544199410810050f100c1038aa6558039006000d883c6001401c488d06c85000c0c882c0c2001c600016140c80c402e134016910300c480c0098004100f003200880c2d16440d0700e0038141d0000400882c0311007004003088000071041d616400c070303020f152a041420190070210a480d144440389080ea0340003800c5488280328810000d2100c07100e8000034290416540104e18265444800007200350704030018265114003034090f00c5256482c508200c0c00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 256689676 1250 256688426 256688429
    0x6140105030c0d0c0b0c06010807090905030d1806060612061205120a120603050a0c05040c090302040b04060305061008010e030a0804031b05030c06041b080601030b07031b020d021501 80
    0x10141d204002da4100c910304036400129030fa00035400301c960070b5210207401889501c0030383d000c5016882500108a00c1b80100300369070040801c1c4d4001c0140f040281d44a0340c40b4803402061090315525019103041171450005904c4440d03038401020401180d5440010b000345804108040882c0d103425000101a002ba0b20100507842d4003201400300310250501c0d481d85a000240c2d0074003042142d0030100c460204030310420026501420090203281007510300032124515903000f05000d141032803400f80003190410780c6070055a50490300401d1003481000410001c00265101504903c80c450500c020059088030840c1921000d0000f03104038014010a00d40d644103030000c6400140d82d100004000c2481200181c04641d4241c0d4a1082c440c29521a036107103407c1806007058913082007061200708500d41201d0490085c01d980c100c1182441d1131102500d8550511003c0c084001c2e01c8000b40140380709a002d054880302c150000032544100000003551040d01ea401c25025124009909200c5841243c5190 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 256690926 1250 256689676 256689679
    0x904090501140a020a081f1d0109050a0204080309040902040b1c170418051b0c010e06070e030a0609050705310902060301060c1506060e010909021303021c050607080406140105 77
    0x300d40da15945040030104194650070a10104e4444008c03131308034180c000c640d24103800140c54910550404054800711040134010140301d504c1008200043c0d00040140c0e04403200803500010209030600104024060050695a101d0055400c4800083c3d5140e0700c208075170b0080700c0661491a66180220b51440b0300d0103800580310f0104000c5440c9504c0340c0145902200180c0c00b41011100d15404400b00e1300001710100e10ba94507030009810001c1c0c10050f07a80c0c400c0351450900094400407001c292910041c600c0a403d003a1240402c41c01e01404000f00d40080c01d0281104a103040c3c1a0042480d0850f010b50740941061701010000e0008007a010714600141c000b4422451a480d1880903528084150000c44800c0f80030b08030120000424400ca60050240341c40b1001030540c1d08000400300459500007016147c41800b06c6c0040500403021403042d20350517544c0021086680894000c243d885620040c250b2103858100f1125031383c848902401144140d10600405440d6403c4440988090090300d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 256692176 1250 256690926 256690937
    0x5040804030b0a02070606060e040531060b030d030e191e060b0907030b1002031612110a050307230a0201030c030f05010e100503032b020904090501140a020a 69
    0x744040766070324124035040507284074010301c1d0038220303a81c1030709070340c00d03681711a011039141404199a82081d003d101d0740104a07011781043c414005040e869016130400c031604984202d080003130200549035204003c850b000031708a80742c182c0d610300e004000d061901010080b03405902c2255a01c00041500f00da405d40e40302d0b1800240c0100b46140044228215900384c45007078482c0148545616140c01c01d0380905006d54012170019005024402c1d4861089006002c43d4400c1150304003600302d6415244c460b030f9212408002c1e20003040c41c12281d060703120340720b00d085000d040d14100812030000000d00103948a01034000380c80105000b04420001c814401c54090340008642100640c86075200d00382e05685030900049206152080b00c048610907002442c00d00780f40ca0034840c00b0110642040c0c02070804800035032030540c00c01702245807200c90100110005d4801000c4c52204000c0d03405817500c0b05805001088840014202140648000c05000c0c100517445400b00c0c020040c03038000c03100130040c1911036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 256693426 1250 256692176 256692179
    0x306170607121803110c010504030f0807140d030204030501060b070302100c02011d15181b01020c0d0501050f0615040303050f0708030f0a0b030d081f0e0c0a0e0405040804 75
    0x2da07450324182d01070892441d9150140e12500204910980c0c0e014080d981e01902e00380f500342030034a00400311080c02e041c00800e00042000070085d4100c1000300e64042203041d00c03044180b074003d281103c0407400780e07658010000000c01450340b40d80a03004483c0039000901245545512401c40d80c8036180003d40181c00282d002c042c0d4030004d07005070320000705e1440001403a035140e0001d0340545d861800d00d5a010340207058140e001401041485400c650340000f0440b15a2022801d01c1e510b4554040812100c1ca0903c1201801da0081c0b201504011024060740318540c0396107000b03402860308603500094086c001c0d000c19003509105401c000288102c4240501d03003421620300b50b902d6040304402c60b82500042041d8400100688041d50240180741119000e82c100402050140c403201c0303501502942c8100e1704007000c950310403a0b440d003040680c2460441c00d1580944090340360703016000405612003040612245124400051200c82c00c03d030340d1030800403299010041030322415140074080300d009000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 256694676 1250 256693426 256693441
    0xc071410080702160801021b060f040b071209030e210d03020c100e0114150d0b1906150e0904050601090e0f06040305030a0b040b10030c111c03061706 66
    0x1c5241c0040e401c1c01201c071a00e01e000003042c2c81075071381c0c0c211905030f03500032803250b12552104080b07041030f1400c500500f29501d003659140c90342d090000c0c07000e00785200d80302c0850380746805031102080c1300421201c203100035540d86c00e024003400c18000105003e13074400d55002c50380584480e8502c00c0e0003c5c68006c1e00c510103081c1021400b035001282c0c0d1003098001c0300c0c07100140d12020f1181c5140c1b00080130003c5286d202d00000d230189118000e0010908040700b10111031180d440ca4840049550b001200645e1030700e4141c10350300e6010703c42c41c151010f680781503400b190a4508403c084968607199035504004110340092010b031309410b07500140607500c440c2c014040b81e000c68208107142e0180c1004c456010a0a03549a4a006005c1e03800390b011400020a100314803150f0700885040c81d80c2a14280406001440403c100462070381c00d00041540d159492a00144954a2030440f14071650071192000d0700e00540c031008400070f440000100b850f0280000302900c0789080b8000800404000d49880c0c2d50780c0c030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 256695926 1250 256694676 256694687
    0xe0a0c0c020f0114070c09060608040c06080403091211040e150114120303010617010b0901020a0f020613060909050603013c0614031209101409150c071410 68
    0x70b100c20305200181240e04142c440c01d1001c1d00d407032400340c82071080d4035141c5100d031400c80b129500300004110643e404c120214420300c501804580646c03402c00c03056596800c08946080003034010b4012194000d0300071052002c52002e0f00300400040342d0030848082d5001039182e9a80781100b08507030f000203507001003103401c0202007070748148500940803810540302840b9082c20741e4000d070801000b040403026150901c01c4840d000c4c1d405401480c0361185844c008600203955128000c00045c860441d4400d10011501c40c0826249060501420720103159101c130300c094880c4c0c12600504602d14a0302000420524050040b18601030504800c082c40440031500c171041008070900e10702c0c040d4924242401038403824829000144054a1107100308000f582c10142041c464a9611180031400c0c0305a16072561007010450044009062044007000d1140c003000032405281c1c200d640c0301d142c1348404950005600000c1450300300c1c005c00d0392403050b192841c450481805808040e003014034400f203024010b0151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 256697176 1250 256695926 256695949
    0x40f0501110a0c0510060609050603250206100f050d08090406090c0c0302212706030a0516180b0a1205010b031807180b0f03011a10110a170409020f040e0a0c0c02 71
    0x81c803340201e460600c0c5140d00d031400c0d500020700180e005000300100c00301e003080c02d507014003410844203a8151420000941c140c4010501420803076002400c1c40440d0f4455110b1401420400c205010200ca005405000165807090a40c094040c40e2200440508510007442808105122003400c010765000180e540c035007101c108030283c45c001196506180d071041c02851080700c1d10140400d8515107041911504102c0700311400c10f00c03546030000c401d5068604c8414090311040d60b41c1c60b40b0340800d840c089a112201135031540740c40d49440b00116400403040021442014145105140c00a00350b8030942e940c121031003400c0003503008005c0a8104030641d009018544801044801c41c10310340c2d0000b0742101e00c0003240401d4201449200c80c041e04145540e40740202c4507003440e003a103105492289841d0841c0c43e20081520300312440c03620079602c0802c2910041d0071708a804540354000b501c0300319960f6120380907da14040b42c65000451444850203203041e485901e07510300c04003000a42c244000807050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 256698426 1250 256697176 256697191
    0x801032114030c070c0b0a170603031605100507020a03080106080415140612010b01140c03040b0f071502070f060f0608010212060a050103050c03040f0501110a0c0510060609050603 79
    0xc1041e04039011041e40910b01a80c0407101d80c0b80c0d00d0000c2e00e4010b0818100ba4002d800c1518144103403806142c009005c00880c940c4100804c00700e40d16807001034294401d4100303000d03815880041580900000250102850080d10020040c40c2c4a110381a0f0fa64056a038000300010307452001803118a10600c000e64000f4480d04014282ca0000d50a01d002d499140720f02c4c1c0e9818580908104441c6803150703051103018010310081000b251001c0008008140f03015480c2d1140780006180c140d112030030011500200011120360381c8902c021462810039601c074020944d200400300a030000040b004c0d108540c400e5505c80e00800c41440e81c5c2c0c0d11180030340010402024110b40d1000c0020361540c003070008001c442e00e1054402d9151400d00100030440c4242d4000c40d0400d49010108555040c401e811a074200303802052030940800c1601e0203d001d45464143c1400000e4049040c0c007807190412004265142318406642c0f00640c41e00900c0202c2d5014450a070000707600850030000c5040c20b03402950030000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 256699676 1250 256698426 256698437
    0x1401030b060f0c070f050d030e0f0907020d14040b03071107080d12060e09030418151401080f0f06100c0b0408030103120c050c01080601022e0c08010321 67
    0x504000403030701d80020716210480900059103a4100304180210006486840151070017142441c0c0881e603140c038103090080034803000e80c102d084a5903c1030054008100014050003240c82c011000a440e1805000c146022400032140b48081006490076a81503a04858045046580703a80c42140e004000201010881c014000c010075409030601600c1d0404000d91918201c0c40c44442000080307030a15880004609004000e102c8441004801c54084412503000c00c403001c1010042c1c1402418150f200c2500c10703401c6d07200042c0364815041c5200368030070240c90f001e84583d2950800309520008403120040444030350005082d914002d0700c1103448030300c1c0c1c2c60141004000d030743e181d15840340300707a806850340840800104208000c46200d0030802c50240b501d07903400b484950703a4640d928440f40d02c01d414001e9400001e040e591007001090844c04070841c0e05c40c2c10010749000300159076440046081e12908080210304402e0140100d0342c1200d074008481c80301951401003d011191006804c0b400300175 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 256700926 1250 256699676 256699691
    0x6040819050d05040b011418010b0a052118061501050c0f010f0e160f03150f0c08070201060f0b0306060c030f07050d0207060306240203091302090906090907140103 72
    0x81c0b14400c161169106502c0c4c0c102d0b0f941448143c1e20300046150780e041c801c0401402c200746c00d0168415250444550701c854548544000c0c43c01e540e0390041950040001c503130088804200c420144d121030050f50b003c80406401c107400c00f0003549600c002c584640b040b0b0304803000c038070055110780c0040c404000d11006483e0514203a2410394250340010360317443c103110b81ba0b00866101c4071051003880b90403009031800030001c6140c84000643c0001c1448054040d20700150006007490054110004100d403c070010048200852005001a40e0550b00ca400543c40e01002140007070880301710b50305545141031a03909681c0d80703c0030000c480c0d004000001c1140010b0014a281103080c4002c1c0012030311650107840845480340c2d00031700d40841d55214008141c2080c1042101007003480c2c0480d41ca4030071040040011080d00c505a00e54400c8030609504103108246a00030000c0f0760703010301020740c4101d40558950f1194010800c00c00c0d001d0301c40043d2a0040c000811000d5410302043c44440e00604004c0ba840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 256702176 1250 256700926 256700947
    0x50c0904080c010603050f0f030316080601120c26011208030a0e192609010c050c09100305010e010b030c0d05010b090106030e0f0109080405100c06060b04080601080604081905 77
    0x441c1e0313560003100e60303a101040c50b414000c01804018140380c0003a0040d0308610f0074010540e415290a2122801e002000000c2007440c0d00c00d1081c1034544016600c14040c02c005410300601c00c0c40c9003507801440c100b080c401d41140f40c089020443c1240d42c64518041b1000b01501e507104035501c0a0241060640d650a600c103103102d00380009006511200c2100212003a03034241100d03845144903043c1080f8681500902d51800018251030740d400081ca0140b0942500f45042480c14158030710040e44240748000708414200410f01002c00d4074402c030002d22060441412141c20380e52000c141e203605400c80000c40405050090480b41564000e00000c0391501c0c9910114010f00801e801c400b001944543c4543d004030800c0041900502156008110040240c1c60b022107a00540c09814030400c0c41d01c00e107042961148c40d41a020b01e4200c0f6003004034568980074894a54040d200f507440e24000c5200005102c80081000e52040d03410074000e0b031030301400380710b2a10400d2050001405100085c080440d10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 256703426 1250 256702176 256702181
    0x42d09171309060b03010608090a020d0314360405060904060b0a09111306021b042c0304050916140f0c0a05010902030f0c011706010201060510030209130504050c0904080c01 76
    0x108440034013555254142031008003a00700c0240845000c0e4444016a001038441141c02c21000303405141c402034048001c3c00ca00c442c0c0c8120100041d50840b0303014502c0c28000340329800081a0110706080101d00900380c04d000654108541c19607104034100700003408900203070885e00b03240c0c20082844540c29241e418400449103100000342d0400c40104070360b00300c0d01c075020544024001d41e0004122040c4404003801100c104035046034062500d400302411703510000090303030707113409841b4207900c3c1307201840144955030340c010b482100d04c901d00c510041161290040701940c0004242d0782d540301c5032014078501d0380043d0b000c0305100544007010070040c5020074042c040600300307a206000103e01071940780101441e09100501c82c044640018102c0e031026a0445800c2d9658600c240c5c040050381c1d0b400700113038014071555000c40c4c1c20003c00300d03640e1000c9030301d9030082c44d80250403900c1a601d0b000280c240350444800b1540100302d54070441d0301514038944000309030b40c070600c030310642841c1119842600e4203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 256704676 1250 256703426 256703429
    0xf0f07050a0503131d0402100207150806130c090909020d080a030e070f060e01200a1202010c0305100b070c030204111c0218010c03020a02042d0917130906 68
    0x48640010032144c118082c000c03074184c0241040711115041c151895115600c844010b00000d104030003944225004c81d00a1024000410034000b03c14010201c50602400d2401c040b10396a03c2400c0c51000742541c0e0005100780b080e0a0803d58640c03140c41d051400c1000107003000c6200345c2c0d0040178030101400181c8000020b101c0311405603001f0414031000c00c01140fa280d0b083d00039800308a5404400d00c1303420707401a11094608000d19200c00c0a03c0c65000907200920b426140c07180c00e0040429000074880b030f07624040e00705104ea600070044140c1e10320044007107480a480c0000d482400301d4003080b1480c4050003a0560501928800d0035a5a0320750010302150390340b41c1c0c4001c0e0300001064507455015020747d038607404000c80c8010b40c9003503050311120384d0701e6004000fa0b0741402000448001414420083c4040d4154050300420103003009058000701c0c42520041201d80015100c10b175040c40002e8000c041d03040d0ba10888a800382c40350300e054401550482907e24401000d1810000b4020105029980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 256705926 1250 256704676 256704683
    0x705010c21090302190302030c1905030d0203031816030b07050c07060f110a260d230c16241a03120c03040b030c0d020a090e07020a05030f0f07050a 65
    0x44a5443c520600c42140c65181c0380314000141828208090b8602140705001c0360b0085400c0021581c0d622602140508030360403050b05841451340c0e0740c00058001000b14028002c00351403400c40003100f100d007550356056110303901400e54281810400110104030380358010310355041003410034480403505490004550300c00800a80c0c0b106a50300130300d4010b51010301115450020303000718a499201c100481c80d440c41311009a400e404070916034804410256030341c2111081d0709001320070040d81032240d440a17022503c11240d08003408140ca45d181340d400ca410b950501080d601c4a50341c00e0729044c014801000c20312210040728841d4511300d500070303c24030781e2650800340c002c88440114010b00d0700c5c040b9507842e90014204104001d2000b00e0001041e2011141110640742e503a030b03651805001280203c85e0481c84250020842e0480184c1202c0444161001d11012014503910300000700ea5030b950491024115070800c108060b40c5030340c020000c1181ca090050014070300005640c1d818908122040300f80e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 256707176 1250 256705926 256705937
    0xf18050a03030507020d14090103060302030a0609060516020a030c0203012004080105090d09300602030405010b040b0a091a0d1a01050102030a0f0e150c0127050705010c21 75
    0x2200709034062140c2900710311244001c211044091502808181800070f11000c0d400300424212400da12a0700a200956805421307a4200301c1b4901c2e005000c0c041e222811039402c2c2c10103001540c442c842c850b20924001080d4000c061f0110151820307038015610910036030f0155202e8200a00803000c1908482c074490351820b0302580e80f490011034608503900070f00f1618003a0030a074100b1840310381c003142c44000e0300e248408070440c61184540900e00321285075039080381428040143c0043c0107a5034080c40c03003075018400900c081040b200c104411101100c480b42e0b4032501e866418000d420403036116140d90040e44170309980c1030314010002070107024560000c4400c108852040c01c00c04a0005000f8010403080c0001d50610554000281c4807401200081042004a018101071552030261000044454140c110b98035503c61b490107000e08610184241d076030009003842d81380000f100c03900c01585038024024002490410004480080722908207880300300c4080c014904190b641403021081410f1038454 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 256708426 1250 256707176 256707193
    0x306090915091b0a08030a0525140d0903030516020406081204050a0b04120803090c0409060605031e0705010e010c0b0a090c0e09060a020f0c06190605030609030d0f1805 74
    0x80820f00c0c48040d080c0c07401010313a03007410000380c00300000fa140b403024641801c0351034121000300302d110a65040b6040100090303c030740c902c0501c00c40803140c281101d000d1050320b81c40a4107240589011906110003000603104020751000c140218400906a034401040461100d5403521410b1a00107413014130640c0c0d0300000741c2000180b0304406144018140c81c5151824240350541d841c0c4658103916000d09400c0b000030002d8600d101c1841012020400100200908019818410000e10480c00b6580c068881c8002030020501c48840040034008088014401d01b810031004503011852845040d0600c151900340b003001071036046003640b0030504a44005014040390801c2410360b415940039500c0800540d0034090100404201d00e03500008800340540c2c0ca500d00301d102100340c4071f06007100b160380c060b07c014000e482c034035003c0000080341017030070a02c040d98a6104264440070203455031500341c2d004204a07480c241c01600314030180154804005a480d03241d00390100032105000d000c44254112071078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 256709676 1250 256708426 256708453
    0x20071d061011060705130e0703050103140a081b070506030112030305010e0f060915030d03061403120406080703110d0912030c090501050c03070519170906030609091509 74
    0x589000c07540703441ca0044021810070310590386a44020300a40204040004c1040301b190400105000410044100354268546500c1c001c0051900b80411141d071440e4080c211000c40000680720516a000742c0a40d10300b00314028115800d03000c10f246901c03075003c1c07068001115500d41000c0c50013010307200340034840c1c4005032400401b145ca058002010a00c5504140101c0e074600c42180e0f68800800d4402040d035454500a250000b00c0701c190441d0f1511400c2c044200c1142e2680005c1c0481d00c581b00c1c8004c108048500305500c9120850103045442000c1c4010070031180300d10140b58200b0b019043c0080c0d1421032015101c01c50340000340101002d504e5101036010400f030312075260601e000314502001442502800181450003e2103240e04004000c20a828009070900c01c80c3d42881e0700004503005580b00144421106030b0b1100c00340c40383c41a501040c210011840f04403986000000d20031441c59841100f048200c000140940215100304401850010807060300107001d100400c004106188200f803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 256710926 1250 256709676 256709689
    0x51611220e010504032109080310050307050a03080307120225020f010315090b040209130c1103040b0d0906020706111b011109010c021f050d0e010203060120071d06 72
    0x420708079680e0301d03010400011a40c80b0f5050040e0306200380d4110082c0141d9100400607040b080320107071041100100b0f0085d1032140310084411684140c0c04d40300d009a48000300802c048642c84058240341040002404007440b92810044c6900221401410941e0084000034034883c0c100b1500e120082220050080d46000c1c43c15414103002441c050100c640d4070b034200305101d1624418141d6040e113450042c44d0756955901a10380c0c1c8400681140d4103d070020600e10003800d4902c2495001c90309000d007044200c0004001c0f5000e564020340e0980c03411404510b0900140505c0c00c0c10786e11640d0a002e001c00140c4207002e0f01032640302d0300d85c44a80f100303014a00048210032201500303203660b2410028400d6040d4030400d80b4080c00d82400d0540c0c841d44c0300d0020441220420341181082d081c0308101102d0280c110000c4d040c6560301140400404c03580701c1146080740700c16141280400c4044203005420030b0260245640c80c0401001c0d41c191a03524041154058041e400c100b4040340c1c0703032041082070700700705 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 256712176 1250 256710926 256710941
    0xb07050301090f0e070e0901060317190c031d0a091b0908010e0a0204020901090324050601030903081305121201090f020a140c0712030c060f050705161122 68
    0x140f004000c0803e400f0b00c1e080e0b444c000381c81100c914032014400229500c0080d071046000796000101e420340c81040206000c5540d01000300d0020510707200510420300c91058960303903d80e580c0341e102d8003c51076022030015500709554040d5a44030080c00300214080c0031501580e02100c0850841001040404902624180180e0030a1005138985041602002d100046241110b43c06650059558400d0401220031480c00e0300040c100c60030150640040244410980b1503008d8090003c1240e80c5070000114255981c01c48054005003904000c2440100c5130b01c1500c1640d031292088940303030302440d0201000380e040444400c40f00910b44c4010040042280aa1031481240700c01c01c5180855950028108090103002d44103102d10219500c19070741700030044600501840b02c01d0030b0101602d0b150041a950300a40300301e520905082c444101021a03002c2d56000380e59944540381080e0048610b4420000c40c00015501c0f0a6420110b248a80300c040b00e2104200920840041d00c1c8402c451a200740c0700b80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 256713426 1250 256712176 256712201
    0x903030e0c030d03020c070f0e0f060103021306052101172b050c0c0d060b01110c100516060903020706230306151c0506040606090b19020a0b0705030109 67
    0x400120340365a03030b000c200c84070b151945003030041c0c43e520280701c2c107032500c042d03a00003a00384440105d012402d081520882c40c8900c051854030b1740d466480100450a90252220f043c039100f007400414040e9038025000b8110341c01700321240c810100056070044078505c20030ba2040e1641402c0081071003119405000c4603030042c0300841c03000c80c5020090107800303e050740c0c00c641600f00b1502189500c6510320601c0000703890500100451204001d906001009090b0102601d0120f0001e1040c000f0f80d14000c60b49010104004085240c40b520b2010152016480b502c4038501280c0440b4a0400040141c03040d155810b000f030307004100c034504121025042105c45035030b0403c11415114000a26071421084030340c00348060301d01108040840b516000980241903012138000030f141020360b001401035101c14403400c012a01804180c0d07940b0425a440490360140d98a4485e081100d003a10b00d41000902c2006821441140d9640c2c0780c0d0f4650211000042d1420710000e0000001013181d05402d019806007400c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 256714676 1250 256713426 256713433
    0xf06200316170109090201090e150a0801091505070302070501020408030702030d091202011b05011a0103112505031e12010e010e060d0302012c0f0303010b03010e040f150903030e 78
    0x81ea2041d40000003014441c8041280e21780c081e00c000c59108607802d1006100c10000e203225420131002a044103020300ca0414007402c011040064422014014002043d0304864483c141144061022000d07080040c8440c05042e001c000400029030244000c1c0028091380c0091502c445a91041500f04441920b00108001c101b080c01c0c4880000380c00c00080669090030440401014503c1643c50945800c1005d041075180401c40c0c4d08110015444203940303d4266010007944501c84c582032114001c00d440b0151005c10b03404079588001c46000b180c02c0181c01182100d00342412482c2c16a88582801181c611901e808180d11002c00840e580c440d01408070222980d84940c14a181d00200e0300c0d008010521808007404442c051600070342c001c8a4907203c1070280080282c40c00031184000700c9000f000c0e10303580324011100c11080000300650b4140c400040d5001e00d1a4070b003012212540e00003400644240c40b0340c0b04800d00140720071990102c070051000d000309440c1c085040c09000c5905204c00c00500c0d41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 256715926 1250 256714676 256714697
    0x105040305070b090d020409110f060a0e0d1106070c180908030c1620030609060601021e0c090a090501050610021f06150201021207020d0c0f06200316 66
    0x807404181d5078140d81a041e45951103000c80c4001401c0c0d00030096010307400525207189942807102000d00c51040d02816901414003407114000d0000500c1461440d01c00100c00010a1815250042c40318610034001e4005008100340b02c00058415880140704545140d010b183c20004581a9400b5510342c442986081003044d0403070b00d0786050784c4402420040445000134400c07401501d2034065030340064002c2c0a00e44408859540101202128403000340300f4031400c1c0009000780b03800101c1e940304070010780c050720488040a1401c400c42c000800a00018007400b0120728254a0f08840e40c1c1c810441d5180104003551541003035801c4441c05404203001c0c502d42481c2c841007503000902101040e05840c00044480380080c50b0400410071504011401505642e020a559605401802c104150700b00c0441803500c8040069a44560800005020070458000035010410030b014001d51140902004140458a4072400c0b6003900902c050050508002c0700344001c00004190790041c00d800c60420781c81c00c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 256717176 1250 256715926 256715933
    0xa0905152e080d051b060126060603120a020a05191a06030705060306180c03040b0609090d0302071e031805061206040b03120a0c030219031e0320070204060501050403 73
    0x1e14480c0d03800b900780a800035117114114030107485403000701c1854098416a5851300081450907019051034030048035120041214820003207161409014001c004000794141036050207442d400005d518800e50040d80d01d40c03800b0807402e1207030001d0403410f0903000c0801550703450081750302621909c40848540c020401c000683c0c400040d002c06643c1c0460b08a500d81d501c071000186900c0c0c40c2e0717045d40310882c45402840303101851075000e98044d52146043c50619901c0070300340300009800f140e074413003950701c8518081d1040703003c5d07801040c0240c01010301d5841c8501c0c000c8000791304001460200c000512081900c0313103141c0e40111800252004881e41481c2c54441c00a807010800301801c2544241c0d030b6000e00d0b204654081049030b00e41200c5a68140e120214040c001c0c006090440c000d80143c00780c0e07100b04884048060540c90455030603120310640940070352a940c1e0f40050a85803200703055a50b00150082d11442881d810f075054020401640d5840d18414442070310302c40d40c007960500c1400c0c442031000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 256718426 1250 256717176 256717183
    0x70608090616050307081923010e04020a1809020406080a05010609020f0a110319080a0f020918040c030b1f050303090607020d030509040f05090c01080403080a0905152e08 75
    0x1452841c00e1011a11980301225002c1c2400d004650b1fa40d103050b0110203898684000303600c801310b4000f8950020fa07a10038580060b040102ca00a500400c4100e040c0b1003401ca036403626042402c010400948072003240e01140c02c40f085904211416445101601c003001024001d0071b018200c1d03003a0660509100c112070007907074082c83d050b00044c80382294500c0040351b01003065920507104954501c9040c000d030000506a50000d441e006c90f23750601d42804110851802205d9034401c010b03011000000d940c1d000700452400c0034008841441180303000002280040c0300042c0540800c0c4800e000c0303540101001c00800d4095840706010350028000310100d65110810f81c1d480680540d480c110710242d500e4100d40da4402e401c881c55009240c408601c9080083d580010700c1a000d80085038945080d41c40150742503042200c0081c00101c0c61000a1080045a0080c5603040d1042013201c121640503010000651800c80b18040000b074041302c40309000e017100211440d0340d0303240d41215414034109a0035545 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 256719676 1250 256718426 256718431
    0x90f040605100f0302071707030207061707030e0a050f0c040e06063105010f06090506090a090209120114060910030302030a0302130302061605070605090f0405040201020f0706080906160503 83
    0x240a100e1103c0c28a144c083d4045034007003944181c4052101606804006c7d02e500445030541c010312403140702180c4a03000e03485048500d9054010b202082e503030088118003030102e89545500501600c40e01d03c00240c4108030500c05003d080026005002010040c0030854098120109840e0f010030148142902e803d42080210a00c00c160f041840c045284003083c0061803021010b01c19280000002da10300000752414103495407070751400d44559440c02005501d005810030b90303600c02442c1c2c0d0104445a49a402000c3c0403201500c195050312401c0c1c0c003182181c0380c03590100000d0200404000ca14030301100000d0780b11341c0c8410b5216819003141c80095880c091000d078542491390000c3c450310b86424522503038000395070081540c4c1d625221f002d40784120f043d80d0081111a0300c02c030740c1c020401600800554032a0b1401070007078014a01c01008010290202078010380c194014a10148490481807105401401c2c0743d8980000d40c0c280324a4961410000401d540e05036920b04c42002025548035080300d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 256720926 1250 256719676 256719709
    0x18090f060f1d0c030105070905030c120c04060f03051608060a0504020406050d03021606030b030a0b04020406030f0b01030507050f1e150a0909150609051c0c0b090f040605 75
    0x41c4120154280c400030124039110410b0751018800c0014404000640c0041e002810b0740284100d031600341e030984505490f8025650f15802c0054130564504103040000302d140281c100b216000f80181c0085821603460b0b03003244198641e004001e105002040182c0c82c1ea030b0402c95812605c05181ca5480c3d915040d019000880b04d41d04d0360080340a540c1c9581002029160040c540c0c14116024070300a1341d500c12542d1070a040341c04a40001030298002d00c02c0d002030810190281101d14110355803502400d0b8010412640030b565080c0100100d0300c030748068031450380b241c0c20004155040d82441403507d4060303407046108000e03480b4142407a03200d0706204100b81260030006c4001c0c205110015800c100030914440d0100004161030450542c400c070000f0480e0200b5904000109005840702e5090f20540603407004240c4c0b07204104600c4c20800290011070034020310003001c2e0710300c556500a000b01c5507481700c840c000340480c41d607801c0e1a18216003024034601301ca040198500d084046050324000a4014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 256722176 1250 256720926 256720931
    0x907050f0705070e070509010215010e181606050a140304020a150c05060403020102031609032d121e0309020306060405070302090d0c03031b030519030609140118090f06 74
    0x12001c100c0b003000b91601a08000408006629103030000504981003050790900601c5040c000f00402180c544406069440202081c4031390b503501c1010b07035158103c04d000c5882c1d91240321004580410640302c090064520395079140c3d5035188180b00100442180784504a0101081081c0001030340d41c410f5010440307aa07103070344007e42620000c041e0f8906442c6030000d010b40c044c4400300000c05038198001d501c98a018030381720480400100301140c4040e01400000c0c4800c10380070240740090410103183c0004d0004000d5104103034055034039102c1f1480c2c1d821001d00030801403c0b04004a43ca10105040350184914081040c10901d40000741e840c6c4c00580103d00556807100491400e500c2038048030110311001d0803007140d51001349003041c8a002544002e800081840c4000202c1031010501481c00c030344c041c1c3e16181800c003641010300c0c0c0001c0c152014020b0503500c4000103110400d81c021042103002c00200281d42d58900310503980040d4612841e84106450b007401e08000640d0300c03013420030041c0c114600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 256723426 1250 256722176 256722187
    0x6080103111807080406050a110d15150305090d030218010305101d010302100e060403030e0d1401020a03050a023a1107030e040501140d0515010902070c050907050f 72
    0x4200b00340c00c000c40d66a0320401d000704100082e0b8101300782c5401180705410410035a40c4001d0b43c602107030800480e014900c04204036450650580350825044444505c61072403c250313a401c01000c0c0c000c0000d25040129403514108107a121040c030a00b5104215424154904003da201c019581d6800030301c21418940d48030003050b06040d403440c1103c0035025121040c1240340800e5444000d060092204078811124812600035a910604000c2a40003003e0301c10350519003155000e1700d00d00181210b24dc2c1101041c240a408a0300390898400d0040880c400142e40d000500c8000342075410050000070407070700400c521407180c80315018219132208005692801d1000c680d07544009503d0b140060745041d401c040b00d00d0070001f01a0001d00e0054401e8603022540d04043e4188000e0318824400e010a880e4804a0365001e03090032100c403040e181c400d805484001d071204d004610012800c2e00010000c4da80403800700c04110781e121404016001c1102c4021240c603121a0051483c030800984030b0059002141 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 256724676 1250 256723426 256723429
    0x30c07060b04020c1e0a21020109170c1501081c0210020708090a09110a0302030c1620030f0c060a020708100510150e06090109091a01020708070608010311 68
    0x782021100030000e544d41c000013101c0b10b5a56600000d03480f4030035a0115400d454080002d100c030100b50344000600d2202040c803801445500e4aa041348096540320b4840d03a0008c0d8000304602c0140903140c018a4452014801a600d404040c02e035507041080043d00522503148002000c5580943c1010302020084464100b02d0030721003c0382c814409a0300119034101084624805001148401c0d105032000aa030340c8403400c03d4032840c01a40d5502c404c208030710f4041901c41d40055a11043c00402d0038680444004140600094110240d46010200241d107a101100e4824810404803c40040c2907502c0383c211100d84500901020300d115180000700920b45078000d010036402400b90409440c1c030003051aa02001500b402c441940c1d1301291030b1070120b0f108218001c0303da960910740d41c500314100608010b04c595580f01d050700310705000301c00000180f248001e005801050005080310314081001000181c0342c41c000c1d400a000c070780c0103030700c2c240304642d4050314250440350011112400c4044078030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 256725926 1250 256724676 256724681
    0x409110712020a0b0f0618011217070c0504020d1805010b03101103150d050706020309030c0d03050910120c11010f051e0406140708060a08030f0909060a05031c110d05030c0706 77
    0x107c1c02d161100c11100006040c4088501e2110114014031302c15200e0300d409100310a5612810400900740d0720059003e12103070905502402c007240b20a50002010b0492005038128403042c00c0381116640e445508280c0d4900301407140c0d100154103518140300f0301c05c102800ca480c03400020401c0382d900301480500401036560040070180540c00009032842c0503100c0344000d45a50180c8110741c02841150005a45070030021021540c03250550f0712141042c49003010000c406400b00204801c2104256020440300240c0c8140c00c0d142c192912002c01310043c01022900b91603104298000c0d480c902403c00800b001444040d100301c41001401d054541e45030300d06840100050305020321485002d00c100505170350051100d03800307500c084030145076240d940d1200340e0740e911862050000c0d01c002444050800d00381201d0454000c0c6000f801d08448a0301c400201c0e00c1c0900048056541c0071040d00217020083e003003071040840158520143c00b96140364000a88103100141810b00b08070000582002403241d6039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 256727176 1250 256725926 256725949
    0xf05240d18140312040618050304090f060e0c040b0307020340150f051e0703080903090108040b040f0b0108160f0503060711030409110712020a0b0f06 66
    0x3954100510004034045a91400994400b21280070700b5001c0c480044100109030b03042240140310300a80ea9507035a0b2264041c0c4244548a8040300021983c0c0001a9052024002900e240e18000850b800308001c40010354250307a100b0104c1501c03403000d1017000038100f000c403401d481c40f164884d9a2034031128822484d502c01d2a41642e4401444049103c2030404000700d6500c10303443e40601d0a1542c21980c01d82d030017080740d00c2032240a5114881d5440054001c107040d094a15850070010300703203a41840412603119048440c0703d55507c001810400300b43d00804240c0e0054544e50080d4101091000080c00201000c0e00c007a0038020b8ad100090204100c084420741659403000d034403150365039032b048555654502818100d5140c9150880850040d00b422601c0080f10002070040c09641c5500c0d100344c4401082441501c4c0d980010031021445a400d40035031104062007204980e950f108508003818444290611601107420098200300402d07100302019400c1400700900e14004d4948500085060701d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 256728426 1250 256727176 256727197
    0xc1d150d060b13050603070801061115100e2d0604020c01090b160e0f090c0f0406050a030621060e03090d11030d0c050a060507170a150f0524 62
    0x280503010400300382c80070240010800040e03403054250740320800c10400303000407681c42000070044401004624800c0f52500f401c0b0300700c0000d4404600c81d62140b43c0131074404884c50394440e401d60030204030180700707840141d60010341e014254000a42d1030500e21405814501c00c414070004407c0810031507501c1d541150f12211090b0001c000f64003040c074000c50710780c01c1141c400c010000c05140214010b401220820580c2100400150030f60504101700040907401400c080035102040c800d071003d0000000062015025549a6649541c50100004d0507920107811401c400e0302c0100c0180d4003000c020b0350b460b00640d808035001c502600840d440601c1d5000701038206900504190303098051011660828030fa9402c140d0580d01030350b040c200150350300c1840d100000d01c81da106090b520086441580240c3d08402c03540b4005012401802556175404019249114016036410b030b45860320524441c41002030102003401c624480c50a03000581c9a9241507100441038910341c0402070344080c1c0001c45646144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 256729676 1250 256728426 256728431
    0x20301051c0206073f0f0e1813050105010806010f090c08070c02040b040f1409030c0312070207090c0e1f1d151204200603060105070f0c03050d02010c1d150d 69
    0x128811460343c45e240c04159400450002c102c844405d0f0700c111000649400054425a6990502d00010300555401001560000280860300001036070a015330350080c0303900ca0041466505204040e01ca86030182c2c0030502c11407821603401c0d105078210f41c1240d44903400342040c040341051070000c070300500004d140c29076010717251100c0395804d8845588402120002c8980c510459a50381c214540e40c0e200e0203032960f040f50700a01009414010481c1c056902c102d003031055410040e9109100303403c1c1c0d41402c4100d00410403140520b002c501300442c803107004031440707100c41c009141500c60151014180d000c00010280f03900b08038038984c2d01c2d46a000700d5411194804159100d0702c000c0d003045608016141140c24041c0c0108030302c4500d540c3ea28030441144011300b8940b858858000644180d80100c40403207500d00035810000218182c804d51000a41c040e00191841c040b10031402803c4504004401c424000030b10b138070845802c12004140303c0010306540d0629405580b190006840c010804d42403031090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256730926 1250 256729676 256729763
    0x10c120504060306080304050a0b0a09080102030108010c03050c121815090a0302071d0601030207140109060c122f1605031210050d0609060f020a03020301051c020607 73
    0xc0c0e12000510440e800c07a5002c004094660031020b840384220b104003a0321402e07105052010746103141c010607000c2d2103030810660b115502e040b5107003a60000d03404440941d5440194801d07681e014043c4a6005e154010043e00c2c002c4409440d01e0304e610302a04952140350702c452007a058160030050001c100b01401e00080340c41c6040001c89130ba4403d00902180180a80540003c090700c1882c3d08050482c54144d810060f50340d02001140290020b41058800d04c0c3d59803c0104091420305c80c0440a5000f090045518019250090510103801c0c2803012510300c1c260900b28075840c0038003203400d45000c0340944030f41c40c01c0d40003042e40503000d02c00400000b51044003051003046000030050421860085085450740e4a0180d02c941c21b4506101d4590440105140c880002c1c5680c0c0c85100ca00784941000200c190340c42038042c080785c024000c1c0d940480e0780000180954038020845000740310f00d10003400343c0b8030340036804034a850040800040c09122011209900912031444001324954040c84a08219 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 256732176 1250 256730926 256730963
    0xb03010e0f041103030c0609070b0c1002090307030b0c0315090c0409020d1d1c0504050a03030c0303141f050607021503070c020d060c1d060406120b060408010e100c090e06010c 77
    0x425007501d42c00690b2049c0000040d00048001c10f490074101c40c000075020340c0440b2002440a0741c8078443c4540e0602880a0100c0015003244000340902d00c030091035500d070b02d04007040505101c0080d500746d01c10741c8840d041010701c2c0102c00c2213400f641d408a00158440410713105000240c0381200c0d440b2580c030508965140c20781c200162012403001e4110b0428900481c18031305171003511560054580052100e0000c0c00400d000341850300c00a4441c0c6000501901110a250000702040ea544466183d065685682004450300c80c100035140440300d1624055141d030000c0c0e51801c880030803900c45100400099503490181c404121501d8028040320a0b0403030500d0054024040182c104001c1061550b006900019802c860410141301501c40c515190500201303650100b10305d41c000800036112200005161180380c0644001c21280002240022228000c5405c0500e22828a4030346480c090500f44070a9004c840c41d000c0302c00d0221031400380d171134100041710131440800340900130000e5880f448410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 256733426 1250 256732176 256732183
    0x6070b0108010207021f080402010f0c120e0f3a240c08090c12030c070807060305070c0305250819022103041209051c03090b03010e0f041103030c 64
    0x340e82c070865150a4400861211b108582c00b50407014000403401000140154000d1b0b074843d04400c0d072801c01522076081c0d540c0b40d912041000c1c5109002504c5042444001e0410102c10940100c0883d025401c20403c1c4003603a441d080d11407046941501032481c0d11030181441031280409071f402c4581c031a080c4803000644118542c021151a203164a800c84003c940382c0700710140e038080c03e00000a401c45201d03032002c02c030f503500105072000004c0c0410441300c5082d140811004000300728030344c00780c15110b140c240c0103022110010038140511008031180000241c0c42012616245003c0d2170442001d084080f44d0003491150110090042e40000b500390303010395203d9900030720791095900b106c214000100200c0b48088941e0405c0307440d0082800842c1c0065240d11a21050440368505943c405544070700050a0f00c6000003248041301503c54150305042c0c1c04561b42c1c0241c18801901d07840d65140a030400e060305d4005003110068052100803e003000110b110b51010120014112a05d030301007070b42d100f80c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 256734676 1250 256733426 256733437
    0x6060302150903100c260603060901110406031104050d03080402030c0105092b02030303070908060604020f091e0619030509060727120b0603010507090305060a020906070b01080102 79
    0x42420301c41205034600007120100c5507011000760140c500802c05220354000307040100c004100b0300c4083c0800707030000c10214a6542c020320350700c02c000c03804e130a000080c0750030140d0150814900d641002544d442800020703007110700b00c408600e40040e00d281600d94034170a50080f1b810050340030910b0798842c0241139005004030b00840c002c4041c1c3d004141454019126071080191040c2c0100c4d08520b2000d048201a40311034000c0340280c842c00c80840c1c4c0750f002a0541e402202c000b00422028002404180f0303040141c254844001c0d581149009068071840341c65000d008007170751290b01004100001101082035442c1d603520080d0445445031001d040704000854103c1409000030310304400900010300001e1814015000e5884450014040c08410003860481d940601e00300428550000b034000405200c401c441409011a50740da400e0400c1014292a0702400303000400c0398029090000c00c40204035642c2254440c2c1006030b484882c440030480c0303030003442c2c0003070801000c200002441d400c06400428 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 256735926 1250 256734676 256734679
    0xc09010e030109031b0c081e07090b0904080a050d05010f1d011809081b010507031b1e030609020d02040801061a07120507080a0c0b0a0c12090204150306060302 70
    0x4503940c0540300345422100142d00140004050311401c8951103400b090224a032400360703466121190b05c54011502c2d040004104240b0b00c030700c0c00d161119240b02071140c51b0192050b998240300b0210034030005003090308090701c040d144c0e032000076200c0c0071a8007880440e0440b0174220340034002d40d07030f4855942e450400184a9160015003200c04882520445908681130300c641d404404180080301500200a24558500312000713141002900030888030040da0a5002c0d0344c02001240d2481c0007003008058940050a245800740c001d400c1019071500145401003140308801007150030002200c00310040e1007194403c1032511710002d00903e12400c1c0350010320640380c0843c002d010f056510510006090f610052208481d4001e2142200066801300035141c01c2400d45080742c01c01040d51101c044980c040741c001c6000c1841d082044080001d00c85041b5802500302d070b410042489885000f900c1b40b1007050300c143c450380d0780c0d6041e601150350750790024441124801100c2c0324941c90b85040c0000380018042607 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 256737176 1250 256735926 256735937
    0x601020f0102040609030f111509130603080a081f09230610110109060f020d2406030905030c03070c0602010e2a0f04050a0c080c0c30030c0901 63
    0x4000d00380d014021101183e04039964105a103195443d00014010954421103080203140c1c003e1050380d40e605802c2c00400130314400c00e542c440740da204201541a001e640c103004c2c1401c040c0c0c200007080d02d800c141d6a044580341447c1a090b5544000d000c900c0700c100000e400440c1025102066810051b4010300700055a0b880e26140100c14071900300250b074080701c0a9910608041080c00098860594980008140e10011034011108d50301d44040d0740000070f2010031181d0208050f4003c4c005402040584054078036a040e280542d400c441c01010001e0140384289910341000e08100b110030000ca0f0004070901081d6500c9005914041030750199911a11005600300003190041c0100482d01ca81c000907401c903190341c4e00b103900c05540760011000d6002da80c40810042c2c569080e40361402280e114000700000064052410300c0007410003840a4101d510058041c80303480310489001840c140c002c138000c40300051104110f0035400200d0090b400e0030324441d40120600450900304009800c0c403400980b2403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 256738426 1250 256737176 256737193
    0x90203010b1906050c01021c0e0d0c0804090914010c17090c22241508130320070621021801031d01020f090117070804110a09050906060102 61
    0x10007482d140c600a404101e000210010000140543c0017032010b194400009800c10100c46244001058144180b0980580b1200510030007a01406600c507541e80d50b04180203400101d4485c94042e02982c0a002402944c0340e13009010b00102c010074035002c0308114020301402d598140000c002c0c104040c121403440d81c5050200d851300c080070400d000900390150400b035801580c50080045216000c50000c0d210355500004c150070030025441c50454814441c007003c10320302d04001e01e008840c25007021002c2204c80ba051065800e41403010f031983ca07405142009440c0c0fa4500320b0030034001c2004074441a03204005000a400e50808c290601441000f0b100041d610061410031040e4415006e9032455100300702111042503009901c0b00240d4148084051f684002003541c40d03089900c8065004440c6501003840011580c1c4900d5100e421100340d8841c03c07007400c0807400a48480b501800040000cbd080c5050840281c55810103540100466003003404503040420a041d1600001c2d940b003801030144c4c8c2d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 256739676 1250 256738426 256738429
    0x307060f06080f0606130b03030706091509030504170c0603010e06091b0307030e0f07350d12150e071715010c050a05030c030d0b030c1806120f01090203010b 69
    0x514103066001d000c090320842d0b40340c0c01040825140c0e1410328410787e9540040e01c100b40c8081001d82603035032103480000b64000c4a81805004408038005070314140341000340100010b0790100c1550111045840c02009000c999048075013003810b400180c54020401000008041c00c5642e2031a0107180c3c1500c0d00b2442d900c551545800255000700308245a080400c082403403940b295001007054500d1105407100300340010003c50030f050b019401303a8800c403d000300c1c602e00409201d41040501060000380440304420100c820b0b1140c00350100f44060060310300314510314890540280b001c403c42c440358442c0c03207501c0d00504075000d81f017a41c400000601c0040d200000340e05000360640200320300c000b0300301c1c2e0454000c011240070000000c1142c5a00914868400041003003010302001500300000d5520740d80030147d02411a07a60b802c03c0c03803280e80180458000d540300c46600001d0300601c545204101e03520b41011450622144003501c40034030603070f585140801010340c4102c0030b40780700310001d1042d40400e20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 256740926 1250 256739676 256739683
    0x703050706050702072d03061505010e060406270b07140606010c02031c0c05030a0c02180708010501050d0902030d2105040206030a0504050f0115090e06090a02100c050307060f0608 79
    0x11a00558120040030706d131420001d4890394402c800c00c4841d06581d450f40c0d60001920200d508071020680b002c4000e0205680180c9680b140000c00ea51240c102454014014082a07840e00380ba03141c900003100d50b0b1104a40c3e0f801c0b000140010000c1cac203a66032060700d818000d18100d45000e4660780900000720301e1541c851023041c0d114640090007418698200c0c02d0b0703280a000300c509900b06101703010030840c00180c805c0c00501900e00d00c5840301c40104020f8010311040200c0c100c501210b1a04500400c5551038102c2c00345030640c0e80038030f0300d540c4030f40400c00804002d005003c1c020754036104400e140050701e070b84511002c3c4204900150120502d004c1d41c601e0096503c2a00c00940c400c03424000549000c00d2a80714640c0f0034041c100300d07800d0b40c1d1382e0301d0018215600c2c80c0e2038035554002d4503000d11240030180941c041d0700c00c051009101c2407500c80c299949800e40107070028890a000c040044076544034961441d5401e8008007980da90311501d00d07080e002011220301481542d400d26400086045010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 256742176 1250 256740926 256740929
    0x3010e1002030604150902071101020d050a140c03180a090b0307030b040c030b01030b0405010b01051603140f04080a02100e13020d1b0507060b15040506030a0e03070305070605070207 80
    0x54014024165001031080181d04000c0c6915089035a410342c2c2401c106109425900618400e90016505e02542c10090b103034045898129040d580051100c2135519888000c07900c03a1821494540543c250303030348034102c1502c078940e6803040b184008190981218014ac0c101c0200303001c05c49500b80d40e580d031003081c071003500c51940f21a41d0603001018200046240504501d500500c0b8481d07003282030343c40e0380c2c841c541000c6c2a00180ca105080d1410403040043c248610066900c00342061410030040000d18031021044210003010420b08190000407220383c481581c944910318989240c603548c40700c114594801e500a8144d20034a5007055000109018a060441410024110580341004000c04402a50007010864903e0745e484101500e401603519170500951019074501e03545440c0ca04009042d14542c1c0c003d6403154420005502c0d10704003540442d0100c800503504951030ba5071721640c2c8001810300080c032030481c1c0030001e03904041680c00300c01840500c1c03040c681001143c541183c220390328201e9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 256743426 1250 256742176 256742201
    0x6060303221a0c070b27120f16051203190504050303070b0106110f06070e0a050a030506061504050a05010309060902130e070b0304020d030e0a0e0403020604030e0301 73
    0x108050110398501041454010300d0300501003103035681e965000c000c00c4202a0b403039941c0c2200440d2500c010b1105003c030000a00b0014034845c10004010818070002d04401c0b40998050b00c2c0220100c0740e40c8601c840c1510040107041a0303101e414030203112917201c040400c038185041d8000040410316180c00042071003081700c0304001f1130801d1540390780090702c2d046003582c1c1c00c01e0001c00e100000d410b40d810001020883c2c8601151030880d454841c1c040c200c0e60042c1024646078000c80c00c20305102000240e02c40e8450150b141100a51300803402103911b11031913402c00340c1c01142c0004007100703010b030001d0107030f010f440140c1c1c20b0401d203044500c0710b174a1406603000d40340d44000b00c0d01d4100304d158441d40010036168047e500c00104424554002806441c2c90000b81c0440c549500201c90030150138000d00000700801c00e01e0614510386036000500c41c11060030300505100055002441540300c000104000c0d00c0300d00c0b0249217500b40341c10041e65030030048908400048c0c480c0c96071a654201030150341c120101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 256744676 1250 256743426 256743433
    0x3070e060f362202030a060f0218060c0604030302160f0b061f0206070503060a0b0309010902030d05040503030403081b0304120506010512151909030302090f010e0d0f020109050603040b0a0608060603 87
    0x340d180454260f007030400802e036490b100702d01890001c19414480c0d02c20794034400341c0060f55180805044c0e101e0140801696101d0310007031003034103520784002c01c80e244c1c45a40b515005980c2c2c0c600034081c0700019080b81000d450740380039814810130452492003142c020701c811103841034220015601840c10b201e010b03841c0f1005030807040200302018014000346400120007010078254540310b4603100c02c150011140c0c244103030744504102095050074880b0880041403440c2c0207103001e0621000c640d403440f507884001c0240342c0001d102e14031031030300e2154800c260410405407561140c2ea061444c0d03400d4904942518a8011400005014500101c0d402d00b002290b20142005034400c07041c900689070010410000b0610502c402d405003961f0344180c0240c103200340c50068a904400080c00082e413680b181450500409000c1c07440c0300d5540b20260740049510680c2c46543c001c903440102e035080c034a68003ea4025002100348001c0140c0041041d00c5038000c0350042164130754540c500c60741c030441547c20542640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 256745926 1250 256744676 256744711
    0xa08030d091506120b190903080f0109050114010c0804051203070c0b130603050a15080a05070801051b0a0c0606030c051309080a050d061511061503070e060f36 70
    0x6017004812a0320805488410701340f488680400000d881105d03e0807070007d100c4008000040d04040d00c010f025001c111410070140d81080c0308030b101c1501004490341407040d0400300c3c400700440c0c84212000b503e800341c20340070000c082d014055980e80040700110b603211003000b008280c036009042504d2462001c01c0207005aa0b14280066000f04405494691603a4850139280c01c440141a030740001004407900500400e4080d0500909150580d040507810741d0404003031060344e500d55203c1840070b071000c000059a880316180d081d5140c4180c0c0200800c118104000041805880140c04044410a54000358840031251403403048442d40c40000340055801d100c0306070790503ca040501444449858001240d503103510804981c5581366034051f000940c04881c240f00d80409020b880d801488149100484101c81000a5200c5a4500030480060003420020318030380d5510320424040700c0c000d49a0b44128484680c1900d4042101792207e1003000702914410350001e0405c0710743c1c0309a084846626141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 256747176 1250 256745926 256745933
    0x1e10090309051e030d02030d0c0503371b270b09060906030103060c030c0f0e060703050d051f060509150901090e0f100501050304030f0e0a08030d09150612 68
    0x20002c035503c008200078160102d5203602c013004110142d100c3c90b0029501d90034011310060598030502092420440180f00b44680219a124006201c0202d1220b602d103181420740100d07042004485082026804c2c225200248010900c4540100391640d4070f42182e00300108180d101095041c0f6600203803400038008000c848816000351a107100b00500040c54519000d0000d20190401c2e0010b652591b50b42122003449605807060601c15261400c0c007011400e100b44001c1c2c031403441c0405807400fa840008880b000c052048048400514034001d0821440c18a1808000341d00504e88015840748104c40020170521b0149040d03d84640000300500c1c0d5501100f6890031081c0c002e00e520606005071141c010079012096001c003445031506030048032003442c000c8440d040700e0940f40d0140b41484010070600000c2035004101c2112004203040c050400a6081d01080c04130710642d018541350700000c6100c480c001c030660480c9010a0042d0000395171004444500000c5038054403400511054080d10301001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 256748426 1250 256747176 256747189
    0x606040506041e02340f0c1a0904060b160204020708040e01060c050c01030b060d200c01020c0601090e07030b070309060504080306031005071b11031e1009030905 71
    0x40d0150011820b00010020f2034580d01c88900400015500451032403100a5662400c0c01c85031030540b2240c064000c62510102507841400b0040c00d180c8038000104180315045074a0750040000329034151040c0700e002144240d0313400405130940b00c2d5042100004179009080c054074102d40e1400f25050400d00680e003000000c1d0f12007101207601d610144800036401e8050840940205100c1d104d480305601140741a41c00c0680030300a2605040c40d10300c0c1841152185001d540d010802101c001400d0100510300700000107056600c89815000092074042c02c14040d0081c080018120044401300d9880e4500c04054401b2800d01400590200c0400c00c04105075042e1960004100d08000804c651287c8411054031402c0f2000d8520341000001c3c004141800c00502040c20070341e8804100b1410303c2d15008150b005a40006420002684008814082e5a040d10f00e84408010200e408032400a50000758078040d0110000701409034050400c0030b0030f858040d98089075450b070345100c8898101800c0206 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 256749676 1250 256748426 256748431
    0x9030206060d0c0f06030c090902040e0a1d0d0e0a050a0305250b0c010c110607081501030b060d0509010c110a1209150e0405060a050a03081813050f0601080906060405 73
    0x54140c0d003c100056a5880300402030701508070340d81d000c40c007058028000f4224042507405201203a00c10042005050741450001e84c0041c070035400403c417010401810204c02a44040e54032a5014115442c2c540741e03003101c40121030610694500803c0c550b14410000d0f00c2001e8840030348030742c100916a0715026050f218038200400ca01c510802095110481d46407503402c942c400c104141c5d507808030054040e8000b81317064011400c1074001d085514040c031009000c0c01014200802c8284810764951003030f80030384c00041d0000e0b07010309100c0e00d4026500014014050656440106501c0c10400420980c4506002d47c41300d1092801040030000a031b864409954800d0030700400c1000002d0007048064041310700304540c410968404415a40717000811045410107020944201e03010001000161500b61541c3c0460f03800c0307112992126090b4201041000341410f140d07500c0762560900350341d00841680440e00a01400c040f04e51107680341c0c001035400311b000352a030700807544c030500000e0318502c0d041c0c00c1690b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 256750926 1250 256749676 256749683
    0x1202010c080702010c0c030302030408010f1107060b241207050705030f0304111c1106040f03150b1c1101020307030516110301110c010e0c060a08041b14040f09030206060d 75
    0x5105c440980c40d00811140c0e290002c80042c0c00c00501000014402d005003114625440403c00510124010042c1c0b144111080140015290b02c50301245507102c0441c40c40308070491010652402d51401c9244841d07105c40d07018180d20301c1d5600071074002840f580954000a501800540c130b451440d165402d000c0e040104121812410440d0002d09503c0c0c000e10340c4904000c0e8402000408000e14001e507040d0300d45165640a104140301c1004507000d14901c9200301e94010311040c0020342403802e080080e01072000701540205a81c064130301d245a00340c91152445004590000c500780d150001207031203104207074011340000c5c0103100001e28060048042c891356840f40c0b4103003a41c0600f0b0341c0030a0079110f811407104c1200d0004036a01440d0003003130080406128242c000791800d013040600007003c50040b81e2410b0f0801103007000042c01c0202c58810156203600b454014045281c2c0d5400650b42c007104104640e000b1810a0b09401c0011001d0140e038071401e5068000c0c00050340d501040c40448030078850240d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 256752176 1250 256750926 256750937
    0x103111918080312091504020108010611030f0c0a02011205010e040204050703021c0c0908070e01031e050a0c14011707030506060f04090606110a080904110c03130608011202010c08070201 82
    0x20002c0040005002001242c015021145009a002d904120b40034062034000b020200070400143c1c4c0c0029035605603486814101e10040c4c103401502e02d54000c480702018002c00001d400c2515510000d048814203200f6030314052000310300701030101520000e10454000e501c0301000b04006180c81d0300b1940d03001103149001820800040c00c03940382d9245100705510380350350300e40c014105076031f102410340040d01c0d0000042014914150590810490520016007498000b404290300b8000c1c54180344084c43d00042160a800c4080c201045948039902c142c1301403040d40c07212100070794001c2d605480100001c1c641800c8aa82d0380c0c42c15005003000926084d1b0205d4204414109480450080c001501d1006400900b19080c010090329a05111002204079803014000340b000a119a08a032942c0e003090b900030400100e80345a03001280541d81e50b460150101258184504101d81c0032402114515a0f031910580d03a105400582403195801c083d000a03007194071034ac0231540d0b24005060a52062400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 256753426 1250 256752176 256752179
    0x702010e030313050a080d08040821070302040e070c2307120602040e010605191407020a0305010e0c011110090f020a030302060114010503060f0108130804060504050103111918 77
    0x2900310340c8001440b8083c034114100600c502d040480c0500040c05c0d404008113030740d042030400038000c41c800400003403c0300ca0000740d52802c0c0156a900c8039003109004001030f014200540042c2c0030350064015000070701880000108118494654181c0d0f441c0c100020000c2c040c105826001090401403610709075200300305001980c000710a54005207580500c10060301d8504002c4200078811041e884081000018010350710941d400399540e640801d024142240302000c1c16040561030700881030701039404407140c0b2000060041c190402214918080d00756a1340c0c030742400040d14043c088411601c44e90b8480485901c4040e1f07180d00c00380000740204d00e4503072450115400030b504100301da002200180c00940040100c8405d0348008283e41c0d4090030014210b150150109107014010090181009014400b140400c20302440c20038409800555290340e035600c0e13210161069100f4481c0f540000d140c03040006003a00751009450014610303a46e2040321185458089070000403c010880510324100e00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 256754676 1250 256753426 256753429
    0x206071b08190b0610090b0706090609141912030e010f021b060a0603020306040f1e1103120f04090507050f07050c0a05030d120c0309051203090d020712080702010e 72
    0x1629031902d48503104001c000c1d46001159a02d000d80480e00070300362003c40c40c0075503400034034010503140c01c040c2107a1110005d04095000c2d00304003102600c02031400c5545800d220803844800142001003048889034403210080662041c0305040c080d24006a2008480c0d1042c0300350818141c00042400101c1d85140079203202c4100c0e407140f00506003a5034164111895200c0601a250f80200081c0c0d0070840e0328078580100b61540310050004040d010340300521010044040440400c00d124030303514500604662500401004c3d0b400e902c6446071044c0c0c0c44950615128100715410a100a411941485d02e061400405010041c0c0b200003401300a100d10702c4a60808005015083d01580c020082c000c1401e00780002004103402083c043d421001388610146d0b0020703256242c01070100d50014038803840e140110003c00d070b0b100300107100340500243c030820b1020300c00c013440c0030305400c1c800d8560004923100b059035034400502c208c2c0104100d03813107100c0200310f04001405105006052900c61025000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 256755926 1250 256754676 256754683
    0xc05120d0806190b0a0801171015091a09091f0e0c0306071d18070c151802030c03070e160512090d140a090302060315090103030f0f0306030206071b08 66
    0x41000020003408541d01d4805c0350300070b10b0307030340144241083c50760104070520010381c03120225541c80b86000d441d14640002080c8101c941402411324080c10003000d00c40f01c8908020200031001248100b80d180045004c9900c0868001c80d10001e00f200e81082c0e61030f103041030029012855800c0705a000b140c50407030701510107024035449074099654002b0a03442d82d09243e100e6950021015000c2d2004c005030a2401c0300c2d4201389034000010703061202c004821490009000c1c0202e410407030646041000b00f284074030080c0d844800c010b00c02c5040c0e41a014088090640d5030707165110380405644c611000c510b00040d81010701c5a403029500c5d145103400d0091401d945000b9083c0c8028002e17074403002040c82d00700e910400c4d00c25026882c4c46040c0c50700c004032400500303642c10340c00060310409000010444007560403004d90071214000c0d00c00d844c6503a580c14058405071115407200c000c40c410302c4400810030f10030300c0b0b03200a07264000e21103424030245441c1c00899881d0715646100342c0e19070013004190140d040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 256757176 1250 256755926 256755929
    0x501060b03040807053912071d010b03100b0c0a0501022107080c09040c020703060e010203040b010e0118021606061701060602010b1333030c05120d080619 68
    0x148035060b40c0380102c0c0b030118508100f41b00c1c101d9404120f00014681c450031200e21071529540380c2072a0f90300c1c82140c03000500e580440e100a50451158100002e108a00c65142a9541e480305021180e541e03030b110302400c1c10348800c5820305902d80004009010103003894000e0682451014102d40075000156202070881c0e11000f5201c071640002c0c6081d40b210028021010f0340120b051901030b10605052110007214040c980126224580302e05030860311a100f0001d00000319044103082c40b1899140940b60300031745c4190b5041d50320011180002c648000c0500809040319001003c0641c03149120100400039040040084200c0c4010444140825241d00406014000c01c0810b0a041c1040080c1c1c5400c4802e1070780010306690400402d02060355454803036060000540001044089400b10b0340914a54035918000098000e0107110394000c00640110056a1183c20800900d83d03e50301017014104c1011000040c0d42d208081c8041085c3c414203c1540100000e00428000c0e0f8445c0c590507001c841c01d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 256758426 1250 256757176 256757183
    0x7030f0812060402070f1e060204031202060709030b0a020d0e030c07091a03191b0602010615030e03032a040e090706090b04091a04050108030702030d08061c0501060b0304 75
    0x40381c2840188102a203240c2c2201c1c00f15800c601e01034403030341c86444101c0072030310150240403082d01003150b00e0002d036403506c1041d42c0044210340e01d030307180c0c500b11b0190807215104038018440c0c0760015070410302076003004080d6074229a408815a4812940c02c01a601401040358140e481340180c100c8480c003000904800c12081c000342c403504c1d00b40146541119503101c012881c8481c440c1e00a81c407901c02103003840c1904038401d5002140340450602d0542d64a641d41198404e0f2118078002408950640c40a410b96942180e0101c0b16400542c0032002e440e0980344a8038284c10401c0410a5160500c0a0034040c0c45d0ba02081e4281c1a0300c0303a40c0307d049401035802a8050351040d4100598200d0a11481000e0011802c0044810382807200c40b001e01c2c080c6024150106035a0190769250f181c1c148034688600c0c200030001d01956071034041c110f0b160340154204900902c202401c80038038030b020302919440791102424031b22051200544001c58102c0c0f403074091352555078481c0007065014500b0000c600c603501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 256759676 1250 256758426 256758443
    0x1c060b01080c2113020307060c03080f010303090902130b18040b0d0b24031204051311250203010603030503010806010e07020a06020c150f090c01020109120302030907030f 75
    0x122100251900344000c2040010080400c0300500721043c00781100006805040c80e50b01594540b86244a0465030074006035062259050019000d6881400244c070310f8484d42d290102034a400a41070000d110070b01000b40400e41102d000d120804043c3d000e40274686030300613211480d40e61020906080c0d4002203144600d01003100c01e41160342030601401c0404d00c025100c24817481d80701d40b5252842e00000d041c44110502c14441709003d48009a48401d090400130150341183c0b4074000400307030310741c014882c0300d001d40701c0388845009180d9203204d101c42d03114491120600e0f00d040380c03e10881d0030703019003440341526101e85514405070b00c00b4411580950b1007038840359030302d505080e01c8500d000c1050703002030810340014040000340d66010070940c1c005c40d4840c4015803a90242031000c4d0178008030501a40f0080d000400f048680204080910f0140b810784094503074082080c40124240c41d02100c0240002d50001030403e00c0c40d1207a802558060118025525201c0d180d580343c0e2002500d101d81902c0440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 256760926 1250 256759676 256759691
    0x504031e0b011e05030f0c0108100902030115030b010f020a1203060b0c03130b0a020705041505120615030d020a2607030306030b0c160605040204180c140f01020604111c06 75
    0x11210303544031004d40b50841c01000404202848255649455045141004003100119201c0901d00c403020b4042d000c408820743d12580c44200c1104208815000800002c2c109416100c0c594041c6c640300101c1441580a040b14881039211522580c00d501420010180c2c0c0d40700c0010203024160180410340240300c0915038840c84e416606c80552007540010104650400490f0581a0001140003c0341d0050714045080d03400e1005107214502d42e0307030141d90030046000303000300e95000101e12a8400c3d020b0511507034022000b08245a5202c00c03101034100581c2c0041108401f0074001c0b00c0b086951408100a405482948180c11680d6081104120040781e00d80c8400c3c020008090035042e440400121480d0030869998848042e1240c401d0016142c99519004507055403178a41003c664038081c2141501d803045240f500e50714038205841703401d244440200741181c01c2c3c40c241c1040221148140d005001c1c60f00e50341ca503140307007181044070f981c0c0c07107982c0415010b00010420912600b040c00b0f40000503103403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 256762176 1250 256760926 256760969
    0xe032802030f0102040e01090b0d0606030f02040609020901021b060c0114010612110301060c0c0e0c0c01060e13141518010c0804031e021212071e0504031e0b01 70
    0xc0e01c4184800403d0f40140000d0207001e1000707808034112070710b40b000402c030300d1b201070007041c0d441402d58000361030a4144900801800303403131706000a01074400c0da4200a2540e4542c5080308900481480c180140c00c8140c00d443c481c84000e8030030046480c01020307a490040340200312404c40d0031044514029110391340041085a8008161181e0949103038000e0000710007403042e41c0210710050007188284280f283c00c54007480f40c840a5403014061a066410107410603016500e039a4000b00a030703150541c00c00d04081001c8651209003401207800680c655940c0840d03695030005480c5240c86001a882410152160340c5500502d080c001c2e207403804d82810514910f004642502d044400008c01d2002c1d42e8140030000c1e0380082c0c000c0545480211260005a075090124104a4a400140d404070804139045103a009015407281c01000c0c01d854442983e01c00e02c0340c56818020801070903012403c10301c02040802e0f503d16070100440b225124140900103a950b0310011460280c200d00000034407008e0091030b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 256763426 1250 256762176 256762183
    0x71d0702070503070e0c120906010906090b0a030609050f010204030809010806030f0706120e06010b0c011404030e0603070309050a0f0204050615030c16150c091d070e03280203 77
    0x5140c40034160706810400880c4d910135440c441c00071a44483e50000700f403d600682581e1580440c0d8503070240b00d0600c038004079541c41c8203004840e4403514000c00065014500e11900c640c041340504090091440c6858072401400100c505031001e02032040170644000b403c0c07005001070340c414a00d2940f1007031104001081058000d102502070303441109550719241000424208a0f007052800c1210420010070040240006014552081c4186000810906440c0c0040c0405940d500001c0110341e50004840708100303800d481c00b9002c90396503080c40e0000d041283c011580b0404074103022600f518a1750301d440c0303400070304481078030200210b490000c1180341500803150085070031111107001c04040058200c0b02c1c40060010a040c40300000d20841c42c40c1c40c50640007442c1c0e04070b41240b508103510041d400183c000056210000f0b40c80c3c481c081983e1101d00620544090408414a6190340748042590502600d100943c1d041c418060036107000990116440b00b031203089a514a242c0701144141843d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 256764676 1250 256763426 256763431
    0x7060305070e060c0a30050304051501060f18031205130602010501260c0d200604030f03030905071a0d0506060304020108221718181302060408071d 65
    0x803d0508100c400385061000031650b0f1100c0d000040300801001c00d0000403600e00244c18000c2e101d541c03081c040e010490700b2202442c071440c0500241d45140e0711024400038480400d0080402240c00c106a8046451180040020b80380e4070043d2840081e44940b5a01100391900e200040020f05c0003a03d0f5220341116030000004040781d000034011941032202e814259500800c1c00704c0d40d00c2039401c0b20081484200030420aa900c054011280540d007070030205400703942c00940b21403403648030910301e01b40d042c804100e404580d0001003280c001916503800f00c000c4c3c5420306041d41e8502ca104c1c000304401001c0c0b0082e403030389248009007594138101ea0119030305a4074010040d510451080c000c100140c0d8116074206e50102e500b4041085c64038585026030b00081d032090000c0d15441e00d09060180d114807031801001290b142200281c00c1c5c036500010023400181001201c02a00214004152458180101c599211780300920540c1000e45804c58589021442da0200b201d410040250b050039100d80040244c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 256765926 1250 256764676 256764679
    0x90907050d08030c2b2a03090f020a060c030f02060103080a080a021c1a011809050903071401060e1503100e0705130626071401140307021f020703092607060305070e 72
    0x1845480b0000a046c00110311a055005060701ca041e10360401800029130600103500900070f07403809442e03040040010b106020100c0c041074640d22030100d01400020240e040b40da100c540640341c04084d207011241503a0140002c94500c2e02405001e45914a071140341000200d00301000880560141041c0682206c16a9041c181301d401d80c011905040107441e00c3c030a44004150100d0320340c03200b03680c2c030740355200345c68004e0320b0781d811000c14400044040d0050400c8032101020404592280308a006156180e0161a903142c3c0c40741154091591860f0040c0c0a4403001c1ca05030b440069664002c2206414030f160783c0c0c07040c59520402840040c6504140d070302600050b091325504521200789096071a020380c0500000c1d03583c1b006450340381c0e030310440b000070340040e4041c1615242d0401f03080107940ea0b50104000c0141c0d58000c050b122300914079100392139103240c0642d2050306041c50000c0d40c1c8001d441c10a07103d0342e5005002003051031140100111002003034036540000b914600403100826003010508181e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 256767176 1250 256765926 256765961
    0x306090610290c030f040b0702040b010e031005071b030c06060b07031704020625030f030209060d09050c0306010305100c0903020a210c060509090907050d08030c2b 72
    0x20300555007401800c2c110b0058294416542d4084032215600e113001d00b0b280c982c9031100009021440c9001c850203029610710139601403220900400040d40c0d2021850b10840e016402180c81215855080e00319980214032420306580d118130403040b204558001e0b04042d00030883e05000b140422415202e5400104810a40c983c180b00d140d43c1d00030300c00740b81051011884481d100200301035544480444003494400c80b070405082c1c0e1102e413a10000b4003d10401e8012903003403550100454040d000301d442c1d4440007000c01d85056401642c0c5401054040c40c151110b2150690f20703000c03a10b0420000d8040c1d80204010024290000c4110b010341d4117420401c801c011140c01c04200507122500c9000560b0810307481e00c2240650584080703207800f07244e580075000442c4420000782842d044001040d03202e2040d591003030542c2e10500c40607601c035218850150049003401c801d40216147c03c2c06140c2007081030066030301e4402200b1202d030b5050750320499030041a1303401001d80b00340e1003c0e10540404c40344d03a1441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 256768426 1250 256767176 256767209
    0xc02070e0106022a030a230d080a0f0f050f010503160317031906150e490c050a08060f010501030b030f06100303030b09160f05090306090610 62
    0x2900e42c0a4a01c4820341049501a43c0300c0ea00c107001214000e02c04c010b400c032a01200c081c18401001d01040b0000340007511040d240010b80c107030102c0c01c060344200e2500c4005590301c580e4001c070000c0c440b5070304040d002e0b40d452140020010f11805003d01030001d035103d000350743d41030030109810004411020148030009640400010390a4120000181c4c09050003a8590340c40c7c6d254481da1580c0d0314022400140b0303100c03011071040030f0515050a51107851307850700c108010400502210300b4a03440d60480184010046070002c8072040c40c1c0a0078071202d200303500e0030009080c00c0000401d00f030703520454032017a400d107052215040c04407441d80180a02070013000e075400c16034006541c070301041c01820704040d1100b8035056140c07030400c80070101e100300c0005c0310490b1410554000f160091808118006410b064144a0318508114601d002e148160401c640840c070554043d610352064406003030610070140058402c6640c240300c220300c22444000504054980600703d10065501038020b41d1003140c58944 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 256769676 1250 256768426 256768439
    0x20f1204020910060e010c171306020105090f0304030b040201050913050103021e0616050c1002010f0e15073234030503091237050d090213020c010c02070e01 69
    0x82284020342c5c00e00304021004581e043c8072101c111300c5029900034000009109a060440a285008881c0c155000b04121303291800c840f41c4815015041403415032080c8000d20101d40403008064001e8414100b01e490818203d0109445196090f0384d40c0b907060750740f00100158282030071180d02d1038505d151040b6020720710b00700250540c0105030b041036246520b050003078200030701040b0b9078200d0900101268500401010001c1c041c0c64481030121599060100001040a0003d502c280e443d0001610f04102d5a803c3d50848141100c1c080850481034107150b07042044510814200311118404c1c2040c1e41d9003004d810032850007481500c03036070000c101c0a1490340024070030300d80c0c00c14440c2c1c14034290b0b07600d032500d840c00c600e402c0d20760320307801458000007030040c8e00c0040d001d02840501404130217a01d03100c40c1d08078075500040f244c80843c2000c9a0100112114030301c4a074841e0700414402052501d544200c1d09100080760448079560805030740da541ca9643d050303010008a001885110500001c41d0305140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 256770926 1250 256769676 256769687
    0xd0203040f1202130b121c0311030f0c251a060109080d050703020c030f0a050d140d0e0313090b0a050f150903030d150608010b0a0c1203020f120402091006 68
    0x3081013505554031050300c56036031916140550741d902c4008440c584044120321108800c0801351001c046484d0205080d0101c000c00d054a101e041e1401d5070410703d0b591890140003503480010344500c004650288035200c0310f002854a1102c42c040d20f4040710300241002030740d485c0500a40580d05004026070100279a8030002500c0200c860300d850015140d40141c50309070b10384031181942d9a032500800e12101e014480009415104a024104450f84620700782003c1da0f112001c0798141d0b4006000300030602c081062034001d4421841c01c101164a0301c04010346407800b0310360a400c035840090302c070405d8110524114481001504003111070080754860000003d800c1036003588546659480405c20407025907007030059074241820b07501c0900115181c8800c80801250900400c004510403800114000c0c103c0c0058425048250307c0b01d48840c2031545608000c101410900310801d0780801c010040240301c0409000c05c1302c407440300b85056003031a104024403844010030203281c9c00c03004001044150f5014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 256772176 1250 256770926 256770949
    0x80c0603060a321e12100905032a060619080609060f0601030e0c0418020d05010203010602160302010f0804060e030406092412020304080909011202040515031213080d0203040f1202 79
    0x205d50f1000126034990311141080c2c4070040d08061a49814400300a2182c08402001404002584400c04540020300110700c0051440c0c040b1203548a0b02c002200780c10800300890350062445003c0060b580c0d109071480c41c0890446285140c2d0704407100340442d590a0b0420280c10000909007070003005000500d9503905c441c40740c1402c0c403940d181d243c00b542e0000050000108941c000c0d2294440d0003c0e4102903000c3c2d0310a1040200500c00c0340010308680070400190402e80354169210264000c0ba0b0340c040f2107100303010b88182c90440e9258818001110100000c1006102c0d68440301b0303025140414003840411740000c084041189100c01d007000e558002d2a61011409400300141c50741c80718180809917001c0d0210301c64010610f0710000c00c1e14a181c9050081c500e20071141448030b41d88001d4426140b41d001d00c007158059004241e41d40d105200f0130040d182810692003040845039880c9005807400314004590005a00000750512547c40200a2031000e000340d0110440300003c0b90707004c1445d05000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 256773426 1250 256772176 256772179
    0x17072f10030b040207020a0e010303080a06030803040b07030b04020d0b030609030711100215010617150307050103110706180203060c0c030d020d02120c03100501020601080c0603060a321e 82
    0x603002c000140780e403940d064510007034010b080c0d002c0207511084040c00410307003030100ba4080740300403000929104150140e0030039240e00420150654aa0355581c0e2409503000c0c2158041c9910740c5050010350310b5502c00b80c0501c0682400c00308190b05100b0130300d0308001010b000c02c0416042041007402141201050800020064561800109503d04228207055101c6514940c1c04224400018100da1040c480c120b00081e54a0b40304550f03d54002c901e103c030342d260b2001794150700302031810805980070b179010150f0300c60704803506443c0019540d03560341113401c0400d19545d01c40138194010150304003005001e03404101d8030b02551505c168181080c2e0349000750028a2078085c2c00054078404243c10341c041e1100310844401c0003d032402c0090303c1075801e800c110346040007209001d10000e4190701c0010914100c0d031820000c0c01c0301c1c0c44001c0602440b0307480180800c0d00032502e0780c0c00050a407000b880311410382c1c1070201c0601d10284c2c5800317100745080609848038404d80300603041e922500030a01041018010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 256774676 1250 256773426 256773431
    0x4060b070803071103040801020c0d140a090905060d0212031e031e060607060c0f11070b070b130203030703110c090405030313050c03010c090906051005070f17072f1003 74
    0x215141064603511803600703c1c0c201f950000c141c401415034006034086030f182c1692949000310802c948901d5950052030b50440c0042c0110408011010096202c503811034006405181d403501301703801107009040940c05401d010b038000a0b40385181104000c0c0c0500800d4444042c070329605240402ca00c2e0305442d144190910100c94000c102d00b991a1002c460b103141d0302403c103000c000140342014000c181240d540300040303000c01101a10160021030014241e48600e031074641010540c1d281e95901142c020000e1500114041e4600c0260381d00700050030300e4074440e541c1c4148a210100102d81040d66a130300c03c0d40103c0e1030606000000e90040b0580303901a03081d548060b07040c5501e0500764904002d035801d41e500355207801e114010840d4095403100968030301305418001340b03030384a0074041d050b014106854001101404280001610210602c100300c2c00754003440c55000c13a2003420741550740400c07000c440409002c247c614051003c6c2400c0c0f0050200400b5041c2c8600c03000010800000a42c03542c0400c040d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 256775926 1250 256774676 256774697
    0x301060f03020706050106021b04020a050f0903070f080d0306080c0a03080a03140115031d1903180e04050f0c0319061d03070302060f04030203271e04060b07080307 72
    0x14400d41c1500c1c2c07102c4d000203040c00f55580d202c00c06074070b920540300c0c0420000d1003d12001010305041c02240c80d92002ca98900345070031201500c41420303801c02420aa458000e41d03a002590011800020002e8040c2c84040d100401c000d02028003100c2460b48011020303000010010117564071009a01c0842e03800680240d600d03034828004400421080c0080070f820500f103000401d0441102007541c00a50160314200014900074000d10500e1885200040305070780822000e5032003030301d200c0e0100382551080c140703e8000c402042d000014002c6030742100030740387c0c000ba041105005040120103071680400d40603110503186c0e035000c42e0f264050140403540c400d0007d502c0384200101d66201c41804000c1c89a02a9010700480140b5201d03803003c4000d80040c8030720703004641d401ca060710302640660381c0360b00210f02e04103001d07a90b44d00e01d1806e000c610402c003444002c0b07180641c89003090078005a403100e411a0903041d004040204942e0f00390008510184244192800103c0c0c000480e03803c80d51a0412007510b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 256777176 1250 256775926 256775957
    0x603080d02180d150c050c06130311010509030306041404020d110f030a0b3102012010060e0903040501081f030f0302013603080702210403020a0905010b030106 70
    0xb10a00c241c5039820903c81080401444010039a070799442500c45424400d1701c0c1d100104071118001c0800700f00c0c442d0443c40c0821a00c00e541d03800b4100e818401e0422154206503503805500b11602100c01c003050303800000c100102441c2a00c6040c0800314030003d509650304294010840d44420710500501054060186082903521703120702c442920300043c100c4114440d03524102c807036142c2c10b90700e6500380511003650902d10303251492814030b08190292407507003950541d0011a20705000b251180303c3c514561004c001800418004511007408015000c2070407480c111141001c4500100070014a1308188802c1c005a07901032011500240650801460480b00e246070b01c0700c03081180c0c0b00404288030b040e040e02c1055019000703d00c135401c9808a030a1001c2066000c9112207141940d8848031b14038000702c02c0700082c060f407640e03500003010f441222100355004007400100304241001b0305034228003080c1041140f5021440e05c0180000000c240819403404010620a000600a801c180100a02031090f0f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 256778426 1250 256777176 256777207
    0x70308070f09050a030809040605040203130f060213080a050607032f09030a0f05060601020714040518030307021f0c050f030405010b090f070806040e0601140f0402030a020316030603080d02 83
    0x3c0c2c00000d0440911a0342c07440e041c159540b05400c034600490418200182e980307018800d980c8150a8280411801d804c2543e034010000325640c800c440d041d6080c0000e00b00100b4640d0281e0140c043c180040ca4a10100e0801ca03281000062402c0c2c201410921200c00e8565000003250072544a1016842c02010b041c1c812480c0340945c0510035010302c036100c540d0703083c020068044811640030310b054074603a403680c000490f100c1c1d00c10301a822415110401010850410384d101790350103215807040c040c40c00d143c40d5000b41154015030f448001a8401103072106640b296400c5601404101c0c2003c00c4040000e281c00341040c014001056540080800040c091010a41181640480080200ca001d00c0e22291100b0f485000343d64020001d0441c80000e40b00c0d0904d8402c141802c1089001409030380c0ca04080c160411040801c0550004a0403840e0710050b01e45001441c02094844400f40c0c8900e02210b080d864207110641000400d03003400010004202c40004442074003078801c1c40583d6500c00c0c1e0384e51500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 256779676 1250 256778426 256778429
    0x3021e0a170304051305010501020c1203070203100b03070e04171c02030c04061101180210030e060c091507080d0507030209030d020a0c060504083c070501080606070308070f09 77
    0x402031007401d1030809903038000c0002d00590f60100c035500d0640d0b50f101c0c03411044a0090007214096849000305001e40e20744500c405514541e0407080305d141128581c0400e080c81c0c0442c000001e02501d07000c000c480c038941401048041c1a80308040212480c0c5a00c900e61400d0a034a00d60450bc80c00080704681c0e1046004c4041c01c4410403034055640e400c21912180d003d42c094424040082d01d000d05d10b200d400c83c18000c2140d0007020100081341c940054003041001c2c46407611407001d066440d4000c0c2e0301c207601842018441d5400c08002a03c808a007000c2c4040c40e8417001450120301000c100082c005480802622964201d0300c50001d155911b8120540c000c1c460351500304d030301d8810f04102103030700741c1e00007100d00306648a60007038003005a0350041540c0a001d54021a0b9040d0071045072003483c0f070a45103000d02140406006000b140114400046174440c2d00d0510002d0b40e00102c100b0711465800400035038000406032120b92030134007240c400400700c640140102c820410842c102a11030341c0304840c40340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 256780926 1250 256779676 256779689
    0x1030b060406080a080d0f0507051e040503010c08041a0105030d0e030c091303020c031f050c090406081c050a0c020418140c090a1503031404030602030f090f0703021e0a 74
    0x2c011418a083c01700203500004481003d10b0704200d16111600101d00a042c0034280300d861b543e04040d000c0d009100d5560040444605502050000150b90750342401020750384100b5032038a002a00300b40c140072812010341030754071600020b0007004005948000640f58040c813070a03c2c0a8183c0e540000c0042d04107451001e980740d00041020038000d604c240d5483c0e840c1d0041c8250216022a5203080515480f0780d2006107103d101341120050200081407608440c1c0c1c4102102c09081c80c040c030140c0094200c1e001600300e94070b01e40c0005055000c00015004079010714406042c01e904080e404480149440c248560080c0640c0e182d141a00031f45440782d54a0740f10550100d420f1802c1d48a01c480c8540e01c4030070700e8600c2d01c50408080441c042015174803c003c084110a0b086480050441d14180c65050301c1b01040302541c0020800040410311500c042c40c001d199400246400d41041040d0602d021100c0c44520f029400180b020001643c85101001c01198940307a030302001001140041e880b03200903031181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 256782176 1250 256780926 256780933
    0x4050a0209010b030702061014040f180f020901140d11030307060e16060c02090a0c1e02030d0b040203190e0c060c010b0a0602072d0b0706060302040506030d0801030b06040608 77
    0x3c10f026040001562017a00706508843c1956958884211a84003a11a60b900354a9407105101103040c40c0c1c0054071000c03071520700445c80c2c01c400224180ea054509074152800201840b442046142040c4e00900501201004040092b40500060400c041841004050f91150102d2403810b8805106880820350858401c2100c40c2e900c90300c058641c684190040110b2030000404120640151511100386401030044403ca40d11811401c00070f000c9006d001d000e214a1441d80b007080e025065900510001780e0303000e182c03038642403101401a01e090a03403151165005004004050032004610170100c1000c00c40416801c10703c0c40000d0410903401516038101400042283c0b2208054000015204e000d0f02c840203001c2d42d40f5030890301c600041c090452054040c0680c0c0b44214950801c1c6c2207180c0114011041441c2c0d15103103a402c9621840c0c0454040e5151513003001540b0b8544140369201c002a8080c3c1031150404200901c1e06d4414040101200102e501081c682d07107070350b440301d0080c2024034101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 256783426 1250 256782176 256782179
    0x7090506090423010f090c05032205030a0201020705060a05191509020c010603051e1005040201050f070b060a230d110303040305101a011403060409150902040b030604080f0304050a020901 82
    0xc1010fa20000d02910400b000008130020f804119841742c0300c0c500060384d964a0442d00ca84d045400b0402d00c01c022041031079501080a004140c0c00d1000702440c3c81c1ca5000140c7c0c42400e49000b9044c90401400c6601c29440c00c000c2203101c01980b0b4501c0c1207081071450000381d07440320030900340c010403880c4c00c14003180344082002140090150320032025a8069002c40308103034000b003100b130f4490220b003150440c0e9401c45d80c41c0841c4800160021504144141440c03800d04907100007200c01c54109120036038407000c107041400307078030b042c01c85140014003180401860090450b4a40e01c0704008403403a003e0013108143c2010084c8007003d1a100c1c810f20780101a02d6413503649042c81a55281100b081100452600700c3c000051010b070721603c1d15514042e10707049400d1001d0407003480c0b150401440c040c0c00544642c290030000b1140d4400001d26501504002800405401030000721011600348602a81c020700c00c9c00085104602991038034101c250403955a03507100e140c45401e206c0381d100700a4004412000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 256784676 1250 256783426 256783481
    0x3060e0114090d110102070807080a020a050a060212090c0102250b070f0302071d01060806030109050604060e12031504051b0a170f040b0a020906041a040e0c03070905060904 76
    0x403880743c0c211490382d9810030b0300002080c2600301c2c40350420042c840c1404215200000e0103180144c203003000d09005541d0383da405503e403d42030215450046840503030000380142403115680718160003a8a400040c0007100d0650300203036640c03001668810204035155007650b510036400442001810b2180300440e240d080c580f03081001c18035015000c9000d4001e0460100d0441441780360108807018210409101d40d281100135120a00301a03e00340e05035488000407000b08404001c8140120311510300000ca007192003030a03a0030300604c10722109242c4010000e100001000c00c02035081c4030402c84002405d80c40e6002c181050710b0f4014120000200c02041d03c0003444e4200c0740402060841054410341541c401c00d203481120411180241925130420200d010204030340e010340030174038000d00450f01e42605d9645900900c1d0b12240302c1c038010f840028050110509da021565001451600c55a086090503c0003401165480c05564019003001c038841e1a41d50f41c03078100c0308040f4012450380c1c5018a2040c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 256785926 1250 256784676 256784683
    0x13090f20030f07062007061b0f0c0501030f020c060a050c0c151005010903051c050405181801060503060f0702030d0c0507050c0303041a03040501060b210108010b0a03060e011409 78
    0x440d800200717100a50460009210984911030840b0380c2018005e807601f0b00100342e600c403000707a4404543d0b41d1502d00034400240c0c584006542c1c0390040041080322854800014141c075006060302a800340107010240f5031500c0002c403a40c02c555103440101c0d8641d203040700c1850071302406554000c20320880c0007035000303000300e099400d008412400c035407035015494200546100e10380e0711000b0066444803288010202d4001810000800c00c0c0c40c060b4902a0b485000903208450345ca020148a600c03102881001c00008280004034034240009100c982d241c840003e4a810004000c1005882c1400001d600b4510034400c8961079079541004111012047e500144a604a844112060b1180c410355080d2803400100b03950803074408112004144c42c0c0010400c0d0241c20203007084450f99256600410525007075000781c10040034030500d090b00c1aa07140400d496042040e40034156591408030150758940314030b44510b05803900000c020a225080018460043c03420130403407211005a8018008105d41c0070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 256787176 1250 256785926 256785929
    0x1c1e0b0403050d0b1c081804020f250b010b03070507081603080702060c250b0109090c0f03030f0509060904060e100b191b0503070f0213090f20030f07 66
    0x4180800c0f40301144c80074070958104074200840900241101c44001404090081010940c80c1c003200320008030440209083e40c0140501c03460840000c6420040101c03000902c7c00d0011803401e07100c207003903c0398852040503603040c01002c502000020020740c44174003441c06c075144203a0204520f6600d990103001c1ca080d00440240480c00030303c41c40d02044c0440d10021b0200d000740344a44580c2d1034010300f002040d40300824111980c4810708500380700c00c04500c0c0310300c1c0c040c001c01030150082055602454820210605034000c12201003030a072081c8007003540244000c407075146508109690340c0c3c420000500a000708901c26034858245040402d018240c00e1150780951403441c0c400c54080d881c0e600e180403500070500443d1a40c1010480707040401d104800d000c0c081c401409aa0b441d4a0658603500d00b50790040400303495840c41141e5600460030f2051a401021030b194408021030803607985c5002c0c02815105003e0324209581d102c0f0005404814007114044400804460350345000c201084c1d140c80f41d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 256788426 1250 256787176 256787197
    0x10b0406031a0907030e070b04080d14130330030e1c0e10110f030403051203060d020f040f0608060a1b08010b1305100507060b1c1e0b040305 62
    0x1010001c1c50036072800b007041691154010048000c83d61007800c128018108100074406520504c44001104a0507000900c080e1140b50040c00b03030300d020b00fa0050f00110003030440140342d0008001618542c0c2c108103c50f0f09030303035200d1030340380034141902d00c20402a52041850004120031110a00101d90164060040c0d00640030507103081c00c104e020500c400560400d12800416403040c10030f0703410f242240c44d170020049181080c00c3d5801c01d4045403440c00c1c00281c0c550902e0b6000040920901a0402c030012003040c1c50fa10321803540ca03206000c28150591548000c0c01807050444101c402d540d150041024509001405c121003503840451a945040554207001c3c06803801c80e120f000450500020206001c1540750007a06919244a003042503002c40400b107400e201d003100104c0d8650312050f20790350b5100d4a03a1542d484441e00e0910a0440c1d860064151044016440b1505071240700d4645030030068201d606800d960000d0080c2205514005200820302c0501c04104030400da00400944044540c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 256789676 1250 256788426 256788431
    0xa020f010305060d0b0c070b0906090c04060f0905040c08030a0f030608060601080c0f09041505040e0d1b020307030210050c1002030c0d181202061506040b070b07050f03010b040603 79
    0x1585001901150301c2a64036a030002400309641011485001103079412120410500346400b0080c0c07a0840004819a83c42010703400c40010f000308807204006026400c03004941c1009100e140415210180d4151f01c1080801919070000800380304c08074006400821402c0192a0b0b42c00c0c40c041e004100b442c040000c0f002282c07400d070020803a904c000982c035110315410f842c2c043c8140c48200d440344c01c54000c86817401d01c48204120a4107941c131507001d1062115091400044074034240000c01094441c425403984003940701c201603007891036000004652046414400700898401800480d00740919508081d4000c1c03000302d0460ba007a50b000d001030402c03001120a40b4064034809071000103070b20068801030101d600a0040b400d1075a035980c0208503464400f40304401801b400e0341c0380365150041014800c09038100008003c55401030b255004031a00003250158a400c1c02c052288803503000d4100e0103003c141d8440c00190200740100308856080b14044a40794880d030399034503502266032207401841c001a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 256790926 1250 256789676 256789699
    0x105090f03070f020105030c0403050708010525020705092a04090b01050c030d151d0403091d1f050901140f0a0605070f050304090e0705030d0207030218070c0c06020a02 74
    0x5030003005940000380e0054901008800c43d4004441540014110440c8100300300300c00030002e00c0c100310090040030040300104451a0100312400703a180421071440c0a51074018088003180e50108002e03090720348c101e85030b142ca44c4500410401000340380c640b4068600740d0750100a001c2c501e4001600880c0c0b40380c2c0341800544524401100c0500440781c01099540c402c0c070a46c54408042d4200150901414543c03040d415650701c0142400c11340d6046010407084241c3c1884245648250040043c00001e4801e0003404904404405544001060600b4030380c01091010380207000c010041000384002041d44285507100c1e1550000d01d0003107000c0c41c3c49003104a890346054100107110350200c0301d00f51546410a01c940d290b401400c13039000c0b0201c03030900080001044124140c40f4407820070300000001c100b41030804090510340110745844505541c0640e004000580e40d460110704442c01200759030311651503060f001d59801480810003488490421004582e41d0303400504008110300866100c142030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 256792176 1250 256790926 256790953
    0x6010f0b040e011701290a0e070906030b1f021e1203010306020a020c030d0918060302100c060624030b0a050a0902070f0f050604020a0905060a14120f010509 69
    0x5210310b00c40d0340031141c000e40c010440040d0841c0c29405648a04002040035000054507581301c1c905440c060580040010421116042451034603016010511484c0300d541804100a07200c441d9900c920020141c80c0c5100d441152581c039904141c0c000c40d080103d20740b504040020b521101424039003100d0010b400080510752790b000131407680039002421100e24603400c607103e840203540420110010b502c01d140100c43c0c161400c2000910240060f912411b207541000100d03100340d0030320349070f20340d17124140001440580e45241200068140d141805805091030703141c01130140183c0e03030001c0581c0118080342100c0400800742030f00001400d507400c000824140301003085034107160042e40c0d0400c02e0345100384140c20980d8010903000e03000d4034529a01d003c255580031a42545540221842c0e0042d02c144411410080410740140040e501e0901203172800340003203803400140703105001102c0410045010300c1e0b200d8266038541d03610078405171003000262031240c9011300403c2c2c410070078601c204448903204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 256793426 1250 256792176 256792199
    0x309120a0b0103020d02030a05070b03061002070e06091b0a020105040606080d020d140d05091e060c070b1308070f110a03031d031c02010606090e0609040204110c03070506010f 77
    0x440364030540700e005076400c40e020303c00625480b00c41241c1500ca0205160007042e0100007002c0142480b02e500c070f83c2d83c94190b050085440c007400d022015075010007014450701c2140c19405501c0741c01556000702654a408400224142040804180e6003002401050301c5078107400c40382c401d9000d00d02c18420541d4074035143369078051141141006070070190464928510420310102c2c40303811140154200030038482e0b640101d41c0165103040f5a64081916120320301c00040000d00c0700305441c000303015245082075228005108000c07004040440790b00002e490f00c0500c8120801e5643c101442c5502c030b40403031915200d41030460302c040e200401041c607288071500e40b02d001101078903856510703248801d1860750480403488081c0306043e498001c00010341d4450381e00c1d10380805060016400801e00300d180881c041c0054215422135501c003080780042150b15150300320055006070781a580003840d000758a070300c6500c07402810110305060200003184c0052082c001200340c140c4030600c0c10005080d80d10380c6d02160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 256794676 1250 256793426 256793443
    0x819080f0f06040506040b031e0f072402070e0415050f061309170c06040b07301508010b010801090903080105120c0402030705182e03021308030912 65
    0x341c1041c0002507402d0800d60400d42d0040f2014202087c803404810003c0e0400080c0f014402e00d82c0800800c9405013001044201d10100024014200950900c0140383ea8448020049242c0700008450302d42914806c010030002044404007014290070a80f41518142c06d00c9440c01c0380c0385007003c0100301e030240c1e240078081c007400e0018607000140241c4043c82018184408042c0c034504010308130f140041c0212802803c003500108060b21803450146821403c40c03501910030020084907a1a4405501c00680101031103070910f05108082d004441240300074104e850310907030300714440d114000388180c41500b0211481c2c0c001d0326100f040e0303a00d5100c01c0045840c140009800240580010009030600c0e00484841d801048256400c0c041894042001c2ea40300780c6814001880020703aa2000303202d008048039500c08111a00488049040607246500802034504d040100d1500c000e584d885000c2d0b170441d56444268060041003550710000c2c1916500540100360081803004850810690701052015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 256795926 1250 256794676 256794691
    0x2011e0e01111c12152d171c0e0604030602030423011505220c020307082805070201080a0b060904090f020301050c1903020904021210140d05060a09020105070819080f 73
    0x4000000001c21301000d040c8202601c0840300c0c141c0021903507c640d0189003003a4103210005100f4070a61241c281845600c84c4104010440195071400b0030755581c104075422290007810143c3c89440e2030500101c01e80d0030208410f640061544180b410030b4042d04207a54a154500c030f8900420703075507010b00040c100d1488103a540303903100940b50031490b0b0080d4440c0d1120190303403044a06020f00c07990f405070750741e0042a180c0c00c581c81c0341d0940c003101c44a040900c3e0160f80b9900d1b04a05200c4180d0002c0c00d4000c0183c10041c4003912199424801c1d201c00041d904041002802803000303001c1809c00f0151100302c4442a4003030350074036001460000e03440c01220140c004105d460384031540f2001c03046009420030f04070729900c03e03000c02007082c80c0241440006c0c02210411002640305d45040321102100705421441c0e80030381c42d20000c1602080f00825480e501c55180100801e4408642c40101c0e218802d060004050398404200c0d455240f0001c40030320a10103060726001c550f91140103030b141c0b034590101d403800d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 256797176 1250 256795926 256795949
    0x50f0609162a0210080a1b0509010e031c050c010c051303060209010c08042303060736060801090608070b090409060e1902011e0e01111c1215 62
    0x19100e8180c0741002d0b0740e0000c0705000c0700310704204650019121910f001c0710900040c0e008000d0000e40c8185204890500100d01d2502002500c4110050098021307608468184007a0000d50b640d140c8003407150204035a80c1011101480420741c0d400f40a9420448203585c0035884e00c030340c3c0909075000b8811200000c0d10868590310861a5644810295001e11541d6042140c02d20381e500000b0303956005080604200e002009030540300080c0c036402e5811241340365101e07a114a0502800320340140c54400310701140041110358020566070654020070010080040f003e421100056841d80038510768160f4030038403000d106450399194107030b55030012809036004da441d08200507400d500d09980207000103486004d0125102d40c192000d20b04104120403900f000e40b0403000d80c401113682c86200e1800c46d20008603c400100c400703c10041a4101140c00541404007180420415403800c01c50502c050b403101d0740300d9040c0841c01000500644c600901d8028050400a560350600b102c8103004084d00c03580d1080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 256798426 1250 256797176 256797197
    0xe0f15070e030a11011b030503010b091216060f090312110f010f020d1d0304031e06020706060e07031a01080c1204060b01080906100306110d050f060916 67
    0x224401400003a0001052001d070120061003901c052040009080c000d0001c03400030304d5410005040f403110502003a80d46800280b5010000e40c00030146e070f05541c4403a0030245c940b00f0440100d0040c20303403c09a51810303c00c405084101c0103500c0350301c2c0252445030303076456001051110265401c42c40ca020003804c074032401040300d01d45131150000c1c42c00b11030040c2c1100d800b403a048507100d003142c003c00d0002e654542c0019909000070114052600c402018a101101c0707001700d030001544a0040e80030041c03a00c8030591115100032101c1d00d4035100603410010440d55090645011801040c0d10300c1000b00b0120454002801c0a001e8407440e840e00f00d40c0c00d4601001c0010000444801343e00809240400c42c0a00c98000f44042c11100184610f124200c00503642000308000b410100008004400359030010701085510794020740d0004c02c8961021010511501c505440c00590081e070219402079843e00c400c0040c80103a1440160159205940b02c42840e103c0d25021100b01c02c200b1000d80c0440d60781103e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 256799676 1250 256798426 256798453
    0xc08070503150a03080d060e0105010504060e04090c0e0f010806010b0903030304140304090603030201140a020408030403060924090b090303101a0d1e11040f03060213050a080a060e0f 80
    0x2400b03040c0c400100700005054607139031031038100d41248004c03003442a038038003061061000300c0c19080c1c0904002d0818a043c50325052001384881c0508100341d00841d00c3d289007000708400030013204090081a0004103c501c1e00d00540c0021010900c03407820039100c3d88000003421842c00d01220580c0d00d01402561441d03175152180d20740f00400d40309038140351108210000e13a0440d07520811018500c01e07800030031810718041d4412000d10b4003420440007148100300422511000204076030441e90302500110750000079007014500c03401e001c110740750035203c40282c40e0301040750b03540010070785441108440320586444102d55171f81e0108684041c400c0304182011b004103e40003c48607400000b5403101481e0103444404170007901c040240b1440005207441441410342480e019604070a00780c500018102881d0040003011180e052101130400e6500240e42620f11600c0e507030400140c00301624100725a550b0f91000350340c90403000c40c00d03141986818000c4003440004607501c224842d000d40100224501084d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 256800926 1250 256799676 256799701
    0x1090b091c06020a030f050f0601020d08090c030703030f1704051207051906050709060503040b061e030a0309050f0301060506030105040c09090e0a03030c030b010f030e0f0105010e0103060c08070503 87
    0x708010050401c122140c00000c45a00052600700c1c0c2d42ea5012031141c41e030060300003e42d20040e10051740c580b0010304002060340d001030403005800040c5089100f0362143c203011418407000c100010780601a004001c801d154102d400707240111041d584031000c0d46403040050501d0300044d107005150343c101540c1202c400c14040060081071b40110152451120010184e01d0076110000044412584980400c01d6081c1c02c100494000e01460400700d1440c0380075030b05c4034200007005200520511100c1402c1c1d003103100746900700d0301000740501116550001410094112100b9201da103200b01e102600e414110f04043c0103000c1120307400390540d801c45e400c0c00204009010f50480c2c0804103d00f20100003078640b018010921400c4414020b010b07a09100e04000b01030324406d203040e0381890300b0180d00d50f809036030001003640c0140c4545400200140c1ca1904030742041c0d0b1400150506600f071200215080007905a864105d0344620030800102c9102030082e00d000004444030000b103881400018030329071100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 256802176 1250 256800926 256800949
    0x30b0d0204050601020709180b0105030607020a02010c0807020d1b050a18051f030b0403030c050406081825051c0803010605070501060302040203090f06010f1a1315020a03080601090b09 81
    0x5006989816487d008040219a0680f030a01c41c0d4a451074883e5061100c060780341400b601080d4080c040e180760030540a03544250402c1d0090400001d084100203004c510010365043c039900038540c545c51121414580c010321007070244181c240c0540640000c0380d01c0d1004a14044990742d002048801203502401c5000f050018610354008000d001c50624041c03511480720701540c420500c4a4090400c0c2c14000d00302d0f848115842c0600604000512006030020310b0190f0200c003124005210905001c051414882c000240520901d82c0380301c00600702c1c451034690401d031072050301c081c1442c04070040d09107030b1114510b4000c2c01406c2c080006201080c45a001007149034051400070400c1a92640801d003240c0c4102c50050042d00b201480140044082c007425004101402041400904055441c2407401c5044c030590b0544e100016107401d06003040c050200200488e40300f8a10240d580340000e9254591400b0403000103414400151040d030250300c21106440581203003900b0041d880c0309020304001d11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 256803426 1250 256802176 256802179
    0x10e180c09040204230d21120221060607080301170c10050a030b04090c0506071103011a030d0203031b09010c0b0a1a0102010b090f070903050d0519030b0d02040506 72
    0x100300140441c2c0762030000b040109400f1642c0c92411452407504800f038018143c010b4407505101c0402d10125400403c1c0f2908031070b41407021404680c0142040d26001e601c512090000c50000c160304001e05440d000c052000c040b02d80d04114150382c0c0b201040031900c1800d00080c02d002c018001448007150240c001c140d09130320a01203424a44510700016202c42d1416440c01c00541e000590469180d458041e141943c0340a13902885a0301207641d030075100c0c4c0024015035003d100c0203e211028072000400802200e8005402080030124201d1503144416042d5504d502034450300e000040138900c00001c480c03040d48142d1944010408059085503ea4007812072603040207001c007550310100c0d01490205029060103031000503500c1c0b5134640d810a80b400809944c0c150392400904d15070030781320320545561250180c1c440000558428105032041c4090390800b034420711840e0103601c03000b034019006141d182c2c01c100a410683c010480d04030191049a0348103131300500220300d40d00050800b50841500b00b20b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 256804676 1250 256803426 256803451
    0xc0f040b100e1908010b100e03070b0d02160b09010b0604060212070c0b1210090b090f0604140702010c02010f0c170a02190221070c23060c0c03010b010e18 68
    0x8402c0740b60a0f4804954001d2003480e551048202d5062500500560000006043c00046420600002a1540750a12500407800d80004805c1380c81141c0d07a048940a94100e980d8021115040c00d00802240080361800302c15807038802e8240c070920745175090303c0407100140d00400714541d0110a292042c0c114080458404006680c0031569003c410040d12040740d000d5030b0001a442c01442801c01c2004a0780304d113a0030303480c1c010180c1d201e0321003400700c0343c2c40443c0038803c1059450311070120b80204101c541004010740040140800150f06420078550012158000d100020b038000c071360300455003444149004100d000d0303c0c0c000e8078841c034503034150f100741c2c1c0c007100500704011448035654821004842d80700580011008030b1849500000002149074600c54440c10807070296142c40c124002d6000f125400805085200c5401c8140d004005000d04003411058031101005a540e0351441c941c443c0034425400c0c454420b819511404131403461240c02801901014013805003507a1200024026000c0e200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 256805926 1250 256804676 256804699
    0x10b030405031819030f1104111b100c0c0c08060106090e0406140106050703080108060630070f090c0807081501020a0c0b190306060512060f0406080c0f040b100e 71
    0xb1071004c02c0a0085000d84c03550950103103030745020703131001c410102030610030b615051448407210401d0054820118000720b4900781c100c040143c0a1404c08100401d118090400d0360100381150310880c00c41d40e06125404c060380310f1781c680507000d172125000d014030780004045000410020380c031600515000b81c02001c00103041c0619040c213200891003608180040703880010a03030300300350348107039070f14010010341c030280401b0f00301000020004501c0350041c00c03014100044038200716501c010200d580c8003c2c00c2c102c6143c80d98030b851015400c50240700b16003600d4034205001c98810b018904840c80742110760b40360404c0340c2e03403d01c54003102803504201c9411031185100c184005a50f8400e502c01078085040f1458480400d008201d100300901428041014100482001095004816901c4040d8200e40c200c8087d0f0b2000b002c1070700002500609640300d0b0400c4400114044046441c0462174400e0b03135588d917080c0110b028003050303480018501d42c00180313401c412034003984914036401c81d02200600851914 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 256807176 1250 256805926 256805959
    0x6060f051809040b19061a0903031213120503040506010b1c0e030304140a03120c030b04021c0e010b0604181404030f0206010530010608030705010b09010b0304050318 73
    0x8050450303003101da02c00404103105d800b9541c00150007051010301030511082d0b080400703110280c1049600d03045151400300b11040c050741c0600aa40e0000f02101502d11140303890841c6041d010030030001034a1440b2040c103070419861041c0100ca10490308070004203c244d19203054040d01c0e42c000045c0705413018240d00340d14481201ca004e404601411100210b0300c0c0d007098100301c2802d51450f81441110703802a1010400680c0100103494000320800c4002064060544150050580925059406072000410300102c505042c50f200681c81c80b910104040100040c1a07800c90392034004440c0d010800b03020030403628035000c80da041030681d10940400d0511008000306d1010100361011400300c0e07000d118801540d64104040c600510301201c811080441445070b01403e69108410a813580305210314a06850030250000c030018820b42045903510071b66070520900070001ca078890751050201500010f08110040c0c1543d0107250480e01461034440f202e00c582070702c0c01120000c941c0200d0001d04480c1103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 256808426 1250 256807176 256807189
    0x230106200304150801031110020a080904090c03050a030f0206130f05070503031606110405090601030b04060b0309030c060a050702070b0c0a150c0e0409031d12010c09061206060f0518 80
    0x1e0060356104d52425504501d850044001103000083c0148000130740f01d0060395001034180e0b03140d40c0110410b03981e14810b0340440c2c06800e111101600070208807600000b0000002402d0304418001d0f0303580080410151000c0762980300544419100510025071b5002240c62a5400895580b01d18202c4042594a0002c0ba0841d0040003c2902040c0b00c01945400d000c1c040c02101c4500791802c1900d440c5c5414400042d48940c00a090141010f41d12076030600c403600c4603440000602000210f060301d82ca04484030715034941c000b0700000c1c0380380140c02c0071454120042c052640124619000b41c90120300344043c4119517000f406100170244904900310020a440046070100c080702c2440100d17802c0e48900780a80f07014220003c06001e10718208460307011a51050300140c098011081050301c0300b42d40d00001d900c1a01d00900c880700c81d440c2034511044030f6000300e001c508644a076150034841080b0340003404101da00070310881c804100c0880c24049003034030450050041e80070500b42c62000244c030b04007180c2d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 256809676 1250 256808426 256808459
    0x61d0102060108063d0303090608090d120b0307030615060206130f030203040b0a0e0108150d080f0912030306040605060a090608130615030b1f0e0c0705060a230106200304 75
    0x11702e00200c1c0005d2040c0740d480b089207000740100381030a900c00d003010b110180c0d40e00e15031034038203080107604881d02003080019003045203260402400c485c0910740340c0c200680104501841c61184070b00421002036075900101d0402d10812107450381d0803107207407261904240401c2d003403c02c07030171030004100110341c0101c188082c040000040c7c0d2018a81901140050619440580107552500803a403201f8403d40c0c03822611603480e50f004111946622100420714941c1c09101c088540c4903280095401030300e840000954800c40b000c6400b130001c96600e409000c15031183c4030880c4000f52001000340f100900621441e601f1a848904003044030410b6100c490860b02c4d007203141000205118010418444a1030020340c0005c4580d41c29071001c009418107400c1421a48101e0200c5c4407003100042d05400403500303941d2000c0d00441500c1d0680b600300e00710b00090140010b00780c1908a074030b0300c0b40042214007040d9410394014ce15070590741c403030b980640c0c1c41d50480b10a645205100400c03003c511035220707a06401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 256810926 1250 256809676 256809781
    0x60e270103080a02070603141623070b070309050d0302130b04030b0a0501050307180f020702150c06070c0206160f06020d020c100209060a0c0c080601061d010206010806 74
    0x180ca44003d08802400d040041c1e010404160500c903406803450009040301d6049aa00c910030400d16401e00030070388055540d0000038641110b640460104004024010940760340700700d907441100d9644030401e4088802954024101d0350050641180143c003c0d401014111190010f010020f947c4980d64200c545c002d800807a03404a0481c10700100030000d00520707016000440240c00840e051252241c0c04070828141c40c1070194490f040e90603030840030341c100da0001c1d40262982641d50103212140705070340c3c81002d1340d49040c410140000c0c40d05105104400c02c1c2e5034020442c41c9040d041094107100b000c4030160907242101c0c3d210014002405030302c000c11094040400c05603d0358021100305007002c01c0903100c1c0413500e004001c030b694695981c0c411255010b25a04110b140d190341800c1c03440d02042150084000c51140a0012803055003205507900780c2d00b001c880c1c1d15001c2c0c01d24401280c070380703400b1300c01c5200301d9005c4030104041405940c4180001d8400280050804042000281104400d10b0000c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 256812176 1250 256810926 256810943
    0x30912082812050c0a0518130b090a020406080f06061b070807060c08191806020709060b1201090b0d08180306070207030308070f0c1202010f050a06060e270103 70
    0x7807040d80028403070500b5450034000708100d01d03201101c895203110718521740342007040014030035200c40c3c040d240041d030764000680700c1c01c640403446c0024802483d07140740b40d03031180d004400060000c2d8001d00880f030690740990b8800440d62079241607503e00480180949610003c1440b5001042400c60004800780403000f00801d0090311308070302e482c01c4c174440d038119804000c400d2885001150038001156502550006100030040c066982102c0101c10324001442000400e9400a0803035800034010041d40c0801d001000307540e5903000c0c1040303648189504802c05543c2d800c0104a904180c2d07000c00030f40d2501070401001e64203030356290710b4507511031040c051454810401100b0f0301e0800b000712580c841701c24001041e016055032030103000e0080041c0108104003c0b161140721043c454000c500c021540852512450409002c000c0d010709010451400000e1502e030004207801c50380d00a40741140d08a4840301c0010b00820107005101c1c002d90210301c5041603a00307584444000300c850710390081d80201d061 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 256813426 1250 256812176 256812247
    0xa02040f021210140a0503061501020f060106090e01060e030c010c061503080d0506090c041a040b0c06150303160b0c12010e0f0c040f0509040615230a0303091208 71
    0x8003002504d030301d2120781c0112805501400366840011310039401ca41d16107c03968526501c140101c1c50081d0f40c030b040301c070213019407000001c010350401840002e5034140e1103518240d07a203c1c2c40495841302030f500b82660603400380318a000c0950051542d03d91403401542e011840800012150414607c25401100d02410000b40d000101200784990707a08004200c0c5d003170109052100c00b01c819030007680150040380140b500c24401d001060002c88004000201040d82c69038403000c13401d0340b6494112524403123a2403854202e803491401100b00d43c3c02c0b0820344044c40600301da40e00ca4100002000b450507c0601c0200600c0984124071014940248112000d28400d440e04110a0b1a01500a040e00c0d0303200006010a2180c40003070361181083c1c84c3d00340d50f0303038603a5940c506041020b00000054038001030100000490b606003400340c1c0c03108201c5010f0304182080702860510400300c400d44000b5001501c005401d1120703107008940012024040c03036040d400e01c00c0e601c0b84146029001325000e0b2010a50605 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 256814676 1250 256813426 256813439
    0x18060512090c0619090909060b030c0a0f09020d020706090807020a1d070c2f10080906070507050f0105070903030e0306040308070809030d050c03010303140c0a02040f021210 76
    0x40d240d44030416901030704040030340d003011400e28016030281c444010700fa40c1007800004d10400c1440c00030050024140580800344c148040240a29910075019010310b686810403802c01c40403200c221a0802404042c41d4900180f141c0250880390700407821380e400300300240126a00d40183c00c2e4503801510b80707641e1010288100300000000340c1c404a498520302211151034908031340f040e58082c0c084d050203104820b00e4500206900c0c40c0c003486624a07200c61031111500480401d00c00d038000720607600000c1c026410138055410400407900d07080d00303500080004207414412005451081d05c168100c40d03030721207200b201e40e081d2241242c9034800651f800900f0001d265201503601030321a8294050f207d40d0a060328000c1c960b41c401030004060002c5200400c101107070400031211040002c000800c1181080710280980351300a100a50000703034110883c1c003a591039102107842800102c0002c01c51140150300340000380500d120104403140d07080c0028101d41e02140c001034030911201052145003400c150f03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 256815926 1250 256814676 256814707
    0x80f0601060305060904030207060c030c1a180a0c290408100506060a0c0b070504080d0507140115030f150c02030306040609050903090409020f30060c1603180605 71
    0x4c0c0003e100c1c0c5500b00620021a03008900007040c0d806c036107080c0e0403651940c00d0a80da0704032441c0d4007d10740400c281d240210502e048481e0703801011917032442d544884500214581c0c40707503114406049180c0448c001c0140310111010107264050401c01101c0c0510260b14000454010342d100d04802d8005140089203481103100d045d51011044860500346030566000405070070040704000d01021280740482c444074082c0003a68014141e031012940b108c515182c008000c0d81006008503190440c28400100d8003006001b40c505026a080d08036030018030315113404100802c180300c01c0e112040ca4807c000e5003142caa0003075200080b10303500150343d2420040c0501041315a103500c1141200d03e490203200340c0301c0003c01140c0b940d00046601081040c118000580000c0c4454040303640803000ea8030404102801c24140b07241c4028075010108820554146907840341d40403108402013a00c108050b596000d030720306441d00a28040e203007060101c2080c9050f9026922190081d401080001c940f00c2d09020045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 256817176 1250 256815926 256815931
    0x506010801150e010201240303030501090e060c0d140a0e0d1e0509060f03010326070314030403021c050301150e030709020a021f0504061b0c0206030a06080f0601060305 74
    0xe00e006102580342c400b0007000074503460001c0742003000c183d1540c10160b10035004601030030301d48482004901e40100d02d0040c08082440103c000c01c0c00c1000008006c1035a22034021341000c40c4019200300e540d12107040c0c0b01607001a00c00307400b05a4a040312902016104440341c4514860040003912880e0311004501e80982145580c08200c43d22170907030044a100c0c1d01a100188039410f203181c40d5910342c000180103000700302c1c8007c020310010000000f481884010612503203600031020040b01a0705900c004148140c1d0009008519101c0e1034074a400f50100041d6485800b92044d0f5500340702650b6a42ca070710784940d201100040c804401030194501044003150032030b0701070901c840020440300c0440d45610030752141011841d800b19a07550700a0090003925940e107181e000b400780c116a40b0308014014002920240d031000e290480354002c60300f0030044848003003001c1e2618800304200307130b081080c1540010203903c011500c521000920000030084503c01050ba4000342c161503051140003400c48100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 256818426 1250 256817176 256817179
    0x906021b03070c050f01260a110a05040b07021201020a2003070321061e08070e01050306040b061512180d1209080906041d0c0f0d0e070b1201090506 65
    0x1008260b0008800341118030840d002035884007801c411060042e9000250b1202e14185201044034403c400c42d00c94110900c90ba80d0100c0c1080880900300c00d05d80350b0300800103400c1c003040041209001190290b0064508188001c18002e4103a10400201e401c0e0382141007204041005400403a00200c054007514044601040085050903802c0d10010035100307c40a042c200c45031041190303400301800b0f4101c20050208080c0180d24000480c59008a0101600c01d801c100d000c1c041000c16000c0c0800d12880c101e580c000c00400041c1c45030303201c60300a01e60207407020390710499440d4440610142c95014141d0f07801c801c402d0740d0b03440c5042d030704040500011000d80c034802c0c0c011612500306541c000c104280745031168480000c82041d039103043d5000307128000c091796001201280006203410031814100c444042141c10038030544500780c4141e003e000348040148100e00a2090000c015115840402c2c84240c1e101250203899079800044000c1d8480e41c48040380302c1c810001403000c0002c500806800580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 256819676 1250 256818426 256818433
    0x30307120515040e0a0c0620061006051c05070c020411030402030703030c0f1e1b08030306040f060902070b01080715020303040f020d0506070207090c0809030d0e100906021b 76
    0x104103440482104142002e0751040d6a1842c20030b1030160300b00441551107900803134042045448100240210780c585811555102241c04001c401e41c1011689038000d407180c014000c5603030b0801609441d9038002c240e820b21000080000501009401d0040d81d0280c001603d5000501c0c180e80184000c1d00d814150031501181c08000b84001602c000402804503505490184c1c130701c0c81079240007408580324400180222203401a90310320581320a454644240c41540b40391408042000d907100d840100e441610200d410600018455040c203402101d0240381c80301000034016151039a840480c1c00c0340e6801e0750b40c58030020060000103800c000758800741c9a501d0b0030b0001031455003002560707888028070040c90502610202011911404000d456030f941c0607050710f01320315007404029581c1030b035840b0783c110180c02c01e0349404c00380e8025800070340903043e00e03400385140c81c50411f411005000000c100110f00d1249142e030b4900d9282c64400d2900ba280300d0000903039504000120911003902c0d02a449000e0740 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 256820926 1250 256819676 256819681
    0x6031d120403020f0612041112061014130204080a030f0206090703230312040b01060e0105030109050405030c0307080415030203010b120a1b1101060b07030f11031b0303071205 77
    0x4008001c0d1811658110703141d00030390049101203502409000d0003e50794180e034405000c200450503080c601e0103c401e80b500b0250039000840c0c0d0b0f03500c50f001e42d01c48134150100d1909000c458200a1001c030703c01c101521010784081c00800c1d4074200d0380542e110000b6508209d00710003c040d8010740010409045200600381c900f40401c8854030340086200c020000c0004007000390701c0c44115908459500001d1054030740340c0e141c03c00c2200340d800c401c0f103080310b131550700d80000b0070603a00403c8590051348041e950f003070450303007071604a1f8003e120251066506100c148003455074040200003c00c032a6100d43e0005031280d140070038001e000c9240c0c140b00400d040c01800103021000c0c0b132100356620800480300c440650f444032441d6100501c2c41100350300c2e41e9180304016800203a0028100701c5080d258038002c000072503481801d15094042c0c2e800080c00034400c07290a025061041d000f401d00b0501a1098a14280394100c1d0058075086129400800ba0408420003915a07080303000d0500032203207400c1c103002a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 256822176 1250 256820926 256820953
    0x9010b1027031a06180f1902041a07020409020406080f0d020105060d02041805030d02090a050a0b0a110f0706080a0c0c020310020a02070512070312030b030c1507020a06031d 76
    0x100300c03c0110094054000603260b0341d581c50741403190718010010141d00b4101080f03148154041140d20740440710b1501c80c9640440703800e10840d0201ea26544070010000da104141240d59440100300b07a81c03080c0c4610310740d030150381c1d1482150001c1652000600f114021000e59901b441c0c4088901d0080d645060100f00031a1601503000c0c074103590403500090082c0c2c1c0c40c0d00002c070546034020702400a1001041096140c4456401810491000c581c0810340316550b1041003c0e551081c080d40b41c686c3c0c42407240000d484d0054a202402200c407100f0b030780c2ca480d442c082c0b2502d46615940305400041d0f91a052081c0380d0b4040c4281d40c9914507a01d4000856035064002c255078105002d2806002640040c0282c4498402e0005402030400209070745042120601c0c2140e0391a144c0c00240da200d2484030407000c10500902c0342e00c101d0340e00500a850300054080800c0b03c0d00b250080c40784250181000454016a070b81011380c009842151030010f400c030344501e41010003040c4a4059882903000303003903e1206 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 256823426 1250 256822176 256822193
    0xc190303020c0f030f07090209040e0a080a0804050a060f0b0916020715120504050d0e010206040b0a020d020706020a0c050712020105040e09191a070c080d0509010b102703 75
    0xc680c0152550f003440f101d0000800d140945003004074401d80101000882c4190482c1c0080418840c215400e01c803d0080510090300c2e801030800042546000300001016039014079940c991040c0a00e081d9010618943c5454058035044480603003d940c2c4c0301104c00581c500840041c1e0040704000d4a02400c03250108041e6849031a80250300303003203281401804003148a038104401c0403159040030301c0b8606080c90565914180300701024082030b0500442515940300040d07291145800582850303250708e8115144000394400411542c1c0b207602080200007140d118001890b1007100c0e075403101d0000301582082424000340c3e8100c02e03160141d0001040160707900c5400d41301941c444445540e10f0703882e100c608a01d003046102d07118500c50803c0c8221001c5c0481400c4054000c5140d000303c1c026603031a200c0440f0700d80780310040100703190f100b07110015040314543c0c001755214a01000002e04e07404000b000400d41e071200c0c407420001481d10304a948038440031006481d0012070402c80c4607010340c116aa901d19 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 256824676 1250 256823426 256823443
    0x90c03040b45011401170c0d0f0503120f090106060908030702012f030703030c0306060c080c2a030106090506011b03180b03070f020d1215170c19030302 67
    0x4070b505902e981e41d0b0002d054a4181209800c00020801048040036011343c1e80c074248140ca514240405c400d1b6540c100205a091501800501500a0101f19030301d55105034820501511288414000e8040d5161074100e52405480720540d40c100070315008110509460150b003102c000c11807842001c014185000007075800456090800d008011524071507100410b050400b21202c0750100900894030740d101000034001140241c0d0b0a00ca00050f00e50180d056414a104500014030303440410004036907000040c000a00c40b400c217651258618080100c035040c480501c400e40210000b190fa202482d00b4400c07040101000390381400380f854824000f03030003403254080980381c94049e01d43e42c0c010035204120030581c02c01c40016800c045501c6043d0300f00d942d04201c44a44c0424501554815000c0c00015080b02001d0b05603200c504003441d9200c41400350040ca100b045074200b03810404100500d20400145450100900602404d04a85c040164050070100c0d1141d031403007000800c0c40400d501003414103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 256825926 1250 256824676 256824751
    0xc030a030219050109050105010b070b1e0403030c050d063c0509070c080c03030703050705090a090b011101060b03090c0a0b0d0203130206030709050108070504060e090c09090c03040b 80
    0x640c082507083c658007400260b80010300b02c0d480e010001c54944001c0c40a0300a1034080c0d001101749545010700b00d184031442e15809070a034110380f0000b40c0086e00c20b03009a25002c0d000e00d45181840f00d210020783c04d0b10410703000461003da914010003170041c04401c400c0d011403c608007000ca1014280c3c0032582c810400d002d0140a00315081c00200f80e13038013410150a5207940007481aa840c1600000c0540365041600d00f440024108004162282d203c1c4040d13400b21000200000f50061030120b02c000200b440c1a0300c2418040c44054180c1018020300c2490010b00030070407090354a00d4140c2e0040e052181d00c1c1c121a21404000c3c9060000201401c00e9a4a1410701a00143d9030b0311a035038200f8088140d014000c0d88010004104845203074801940003c0320380030b8803030b210a92100002600d007401240100741c00280b03c008074980a2030a00c0300b0b81e410141c40c0300303000c0c80c1843d40750120301488000c885002800c68004140402c02030600c1180344d0000829400c59440d038090b54078080300ca0f41c01120403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 256827176 1250 256825926 256825963
    0x1020a0912031e0e09060904031b0201210e0105010503160b0306040605060723010c020d0c08040f08030408100b0a060e0a05090108010902150a08010b0c031c020405030c030a0302 78
    0xc108040c041c6028005600ca0f040ca84075140b01d000c2001016503003071050b424010268400403405500380408410b003d40e50603220301d181c0030140510042102030420003a0304214141000c11a550b010260000c0c480c02600c0000c1004d0b4107010000b829544103070310030307402940301c804070038003480148141100f41d400c1104005d0350b9803290000500901042c1c3c21443d8400300006100007045003203190b0300030b1015090301221189051041c40d50895120000b48809a000802024911031143c9410f4034414801d41c88079007010f850b50f200c2a880c44254000040135800005c1c103003d610b2041044420401000c0801c0c45450481800309002020701c2c850f91081c811201455030035071b5034032600c6502800300942260183d6a44d58240c3c2e02a00400301e0aa014014043e0f0701c20034854404111400d026070740d00c078a04541d2801040740b541b5030003904a81c0c2c280c0018481c00c0d0b45200001141d01041446220143e107490034030040508046070000305a109a002e0b4820000190300401ca03071404000303242c0070307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 256828426 1250 256827176 256827209
    0x1205150d0b09070503011826030105061b010f06030c08071d1909060b0f011d01110f0a20180a050901180b070306050d0b060f06091905010206070201020a09 68
    0xe0b00d142c95940d400996255080c1030b800c0d1505900031001014060151b1915451008110b0590024496941010b07030121400c00c01409075081540c001c0c0480d4068103c010300c50b860fa01e08080c04c686400c004080d8480d142c44080061001050740c402c0a0309600c00507000d0380d480c0004c0d02510482004c80b0000000b00a0001114400d50380015005079000010500090305c1e507140580060001004c60b62041d04c40c201c562500794821541d44000380b84541d5100d407401d41000042d250f00c1e011101e02c18080c401c110020194600a100343c00c5402d03c94240c8481c11880d440d01424510140301400b40106159040703018103600c0c0f000d105400203000c860028442c1c40380c01405000d07007400c8801050320701070140203000300443e10154500c42c460701da0301040034035103500400038065118400544524000c0002c1146480d00b00b01c3c007141d54800501151601c020748002c581d030000c041c0340030116018050010051941c05010b4690320249500c000c510b400700d010009030880c1c0180c010707075000000e640c02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 256829676 1250 256828426 256828441
    0x4060c02091b03090610080f030d200408061006030b0904030e03161e060c020102060c0a030b0904050309012a0b0408072a0906050a0612090606061205150d0b 69
    0xa0b0103501030b590300c6485a80745010048607580c1c05059544034940081408002401c0c140420311583c4500c40c14091031400425000000140003c1301440c4001140034500c1802e00208400400c010708034032019000919012510b0a00c00c0090f40c40001030600748903040760a5075414416540c00355050514407041801540403034034205040b003101c0c1c11501641c00200c2d1070840c1201485c4000040c2c0400005c0d0b0340c44e02c1080f00c004120460017805603003c5004969011030b07072005020020f0b40da203000030b580126040080c1c1696000d41702911503400000e8520300c02e5038801a0540c40d2100e11041190124240706400d22565000d400500404e031641d001c2001c110b041d0381181d080300d807c4004004000c540c01000c4006480c030046003020340d00407503000120f410182c000c80f030846000070600039a240c501102030711a03a0300c214182c070350715a85c0e45254000450500c640c60103440e41d80d44048050b0170000000003214406002c18040020200c0718081c80d6450b05c024040c1958402c1624015864810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 256830926 1250 256829676 256829701
    0x3210f25020f01020a030f052527090209010f0e13110702120f0f0a030e0618220e03030c0403020d080403050d050a1215050402090d1e05070b04060c0209 67
    0x8072804a2075000280e4a05c2d440e5041e0461010f000407134500708020740b20100e202001680090180340302d0ba1a81900a0a0030b0165504544500c10303c00442c00b400c6040f100c8803034140054100140c2a50b0104089245503440001c1068000c40c45c200300c288000d02000007030142c104003c1800103140c031188000456010082a100404c0c2c1c082c005a160300800780c034041d02c440709d4020a030000e00c506940c2c079604040024048a4140d010345900848001311028070007681e101c0d18008000c0e03400302d0028407942d240c01061040d840310540c0e20010310061011540c0603160303808015011540103005002003807120307001f101c0c11aa8101d070882d04081441c070708801280a5030388050664001c6405025182c0c0d00580202840d5655982e005034a00040181c94205d440c41526984c1917220401c003402241480d5004080060b8024604481c03a0500e540c0c0000d56251841e042214034010380120003000010040c01e000317440e100548909280c10400c004091044585029103d071044801141d0380d400d010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 256832176 1250 256830926 256830943
    0xb0a170907030611030411091618230405010501111015080607050a08060901140d05030f0f0405100806030a0602090a09180b0a05012d0803210f2502 65
    0x290301340040d240e03000241c50319420031181541c203012000d0403040549403040001d80714403030240c007840c03813261151011119140626080c03c0d64900c0c1603000310f1f80d80b40520206203211811407241c091900001d09000a0724010b0344404e041c40b802d0200300021140101e20b259030441c1c1300200082484ca5404a2044801030b603000c4a65409107000f8400390a40c4040142403402c0c1c42d407100d0a0a032035039010700c0011182485680c3e03003a030b240c0051004628181c0708100050380100c0459085c05400750504d6080d074810390342c000e03c05400003010401401e20304241d201500f51404c0444040c508035000c40c0c0c80d0b140c880d01c01807001764005a016840d0f914400520301030081c1240c2001107030342c1c070745003e2612031000400f99515000140061452103080c01058141c9117900007080160310301c8140c500407824611210710075900c0c20040400e1001d802c102402035030310041070a5132104c28814a05030b070701602a0460a6055030f203010000d4034030504070390500760130000f036a000007200e010508900f4903000303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 256833426 1250 256832176 256832183
    0x105090a181d031210030b010620010507030e07050301050c0913110a120b040e070b0705030904111e0f04050112090f060f0f050402130902120d08010603060b0a17090703 74
    0xb1050307030302c401c020000240a00c0c141000e40c0540c0c540740c40c2c800682e440f26070b00c8001e14000c50400180103003449002071080103a241c00f908074840180c04511030035144c04945900010355130300741840b8816401c006010040206030002c208908040c40c84848a11440014601900320b100d80c82001110583c81500c1a0003480c21484e181c01140748010b01c8100e0300d0944541070b90901500084919241c812541040c07000401031030382601d892205001c82d00800b5064402e8002805101c0d056241c901580c0b0840301c0c4448803658a4680e050305001c201d140c100051400c40b41841003c1c2ca00d010030080720207030307142402c08a040c680d10018850140640c2d03080104480100b440c00b5080103556041303108904101a070900c0303901d14000040080b62000c6034040c4d0300007000c44141594000c0790380508905400034020140301c2c40380414031803404030b82024090002d403210004020301541407151070090101240050300c0d21150203c001d0a041301c401e01a08070040340408251000c03020030159004552 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 256834532 1106 256833426 256833461
    0x702010b010c020f0a05041515050c12030c0415030f0b030d0e0609030109020d08090315040b040318051003020c060105150d050601020a02130f0b0105090a18 69
    0xb070156000b517804203011650707441e50701480c10313138166994861030b0380c43c43d065241d88010622000070701044030a03c2503201281d40460310888102c404d01c40d5544a8566484061a5125a50001c5481031420a000d2507050700740e0003084000550060401c80c0c200c00da028180c4500001c080c81c0c000564882c00101c5602e0105c025162590016000141c1c0c544c031703540070442142e20000c0540303003403a011030290a6071030104170b1106040556038052195003000c1d60b9000c0d190070007600060500920b03114620500d014101c42c00010940101851240b146a1402800950000105c0456402428004651420f00182c48540811074942261030080a000ca03400100002340881d41140503107229000941d0742c00a07a0048550a92000a85181410108400c42d030001417014144101070024240a684003842c10048549016075040e40c08104d00d0360320300808402059070450744 = true := by decide +kernel

theorem cover : BRFrame.Cov 256654676 256834532 := by
  have h0 := BRFrame.cov_init 256654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 256654676 ≤ n) (h2 : n < 256834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
