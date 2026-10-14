-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:10.722326+00:00
-- url     : https://prove2.me/submissions/834a7b7e-0d77-4311-b1f8-7b534c7ccc7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 373021582 ≤ n < 373201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 373022832 1250 373021582 373021589
    0x50103022d1801091a0708040b1305130b01090e0a09120215060904050d230408010b0307050a080d21050a140106030606021b0d0c150801080601060503060f01090906 72
    0x140020b1840002c07900b40c209a010350024640181c800313180592840790303118002c2c0b4918002400040f01070030070179503008032001056100744280e210b013900080c040000c00d4a10906006031004005e07102e0183c0300d8410391100b05816190601d406050440c071540301ea80003406580340580da840c440c030202e5220000e040e01c2c3d400d203034005c12078140824148070700e100c170103802980140e4060051000040307002c5048801400c6130b10b02602e40700308001d0415002d40406030220f0401000081c0458400f0064004805c0e142d026812511040d980d8014049104c8a5106070165034204243c0384078060b2241035401101d050f820301d410709041c40c120211089510a07902d203000d017a5528a00fa0303003008028602401480c06060807c82c0e1303850140044d4a800340c0c885c0307220081c0d032800c0e664803941e074070000d8410f41150807050104000703881c1c00141e4807000b81c1c0110b100c0401e02d03810000500c42000a41c06040c1d03001c44c0e0702c09046440c0d1100384120216182880790500c80c10b03032004205000c2d01c0c49550f00070b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 373024082 1250 373022832 373022917
    0xb160b2517070f0c140106061b0203071205012406020c040c0210111207090f12020a0303052a0102040515210606070519110102031305010302 62
    0xc0140320585081002100c0225050001d0030103003000120740401103560114190034802c80c240c14045048580010488000b400e0f41c1c0c90510011500c90154030000c107440345500c541e541054403000f481000c0c000d050000358190b0007100c1c05c0c00034140000400800911a01c0041500e10314004640300729040700305440190b0200340010441140d0401040707001355025901080550010076009403501022080e04003c180ca444c80407100030025002c40304002c078001b800342c145060580c030051440078684103c9901c0040d4500116041c40071041180c01964001c1070705120b503180d0790b002d40701d581040f820454007400001d010b0203070b45240e1144441d80310000d000181e03540d040c002003104001c9050400d0041c24003d0240c0121401c200411512030f04048680d264903950707000004400c1d00c00c5400041090003045100141e181ea00c3d110466418426001e2000071045103004a950b03000744ca108904c40014910204000d500950041c4080000c440c1100313103446030700350741d03810150200350303036158 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 373025332 1250 373024082 373024111
    0x3010303030b01030c0302091509060904050c0307030605150a03360c0b0408031602370504020a0f11120a020303010905010b040513050705162306100b160b 68
    0xb07590390510805c0100764060904504203540103000c80c0e540aa030040021001000190365412a0f90b40810361300c200d54010014085450304504403209600166041d40100303040200210306450081007541c0c1ea05181c8403103900300502c5680482c017521500c150084c1004c2e100314038a05016080407a0602c14844010f550011081441d114074512099071181848031014003040c405e4039400b01c02c0b1100d2019100a03507100c505a0300000b0100101d1110410000d0603480944040072000040da0311130b4800f004170255281e0392501444141d21811000350700259603200440384481c09803040c43c111440f203404032480640300c15100ca6003903002821140143c0d1011004122400c458040e0901404041000d18102850400413a040404035203002100340c0e11540014880c6200c0e03c1928071840124482010040490030601c0c00900c038084502410f08124011804281000030440e0041980746800080146454250803854000c46405982c06940300c00d1100441c0920313942d1801b401c4203108030103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 373026582 1250 373025332 373025351
    0xc0f060912030e0d080106020c0411122a190809070f06051e090d08032e180509120705030706050f090d0305070207050904080d111908060a0b1b030301030303 69
    0x41c5130244a0030f440b010004500c005210340342d03010502a1001c0c000380d40224000c01c403d20712000c580034500310800c1100c5010200a90b03050042c0450000404144030101d1400e11790744400740f01c0c4600d43d0744040001c45c400081140724400c840c1641c1c0542d03101c2c10350700d459445100d005002c0039981c0c00407001520200719080725102c011003c40303074901c000d501585040145030200d061010590f07005084852701000045101038005e0000f000c141500c003800a150007414454a80e600c0140200c0481c201c200b0360a4a400c0c80070f116180c02034074803000030025500044000c125950001c4411070741030005001040000d166402a20b02640512044029504e441403101d864841c0740c0d014141003500340b00500c041a600400d80c00150f031000e945d00046591503042c42c004074454504808034462810303511900020341000900b101d007100c0d80240f6040844c00d1011151240140c80700381e8002151241004280d0304000144141e0401000b58603d50b201d46010f00d0558100b60310a8000c2521840e088 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 373027832 1250 373026582 373026611
    0xf071116080c0913060e1204180c051c0c0513030c0602210a030216050a120801050409030e040e07050d050c03010c09060c060b010324030506060409030c0f06091203 72
    0x90342c0440140ea034001a07140c140e0b01c800320001c40d0302c0b024214039642c01904201c41e106111035013000000e407402c90380d12a61100c00300403080001c40680010751500c7c004010070380c0305900302c501c01980da103568030b501101240c0304002040030488100a00c00204550020842c0009150006500501c08100c8071440d04401900300100007a800c40c0c40201382d848240407504000c25101015100d10340140c9540c0d004001c41c443c16640304000c1c0a0b40304680c01074081207881c1070381e14035150300c40d5a0240d160342d8840c144401c2d50b079412001008102120200070050409a001400849551040f198202e555a0101e04e101095107426036198000303440900c014102400b904c8150b0147d49444011a882c2100c01400d88860600c003c00858840c000e80c0801c0c0e1090f00304041410b20035802c1c2007020507403041c4072904025803000f00d50700e02441001944610f8035116440700c250300354540c03480b4820569221203c58160038021101c55580b11a44004a50b010100b9210000c090704c0005414080c00c191 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 373029082 1250 373027832 373027843
    0x105311208040f06141917010b0a031a0109140418120e0603040c0b0307020a061d0c090423121818010303020c04020d020c120a09080703020105030f07111608 69
    0x141400003a0b0b511031004002c0d401200c0036203148003c1000c03900d090020403907e040000d401840301c020b00d5400480e12040e42401803118200586040050410b0300040c1d4090710b03000e4001d00c0c04a07070941801c01c5005a05c9107044590040200006202384a03c440c141038810b16410545000a0812581c01c40035080100031703a001b0800c543d420705600c1c155450b881d0003c20380c096078400d004080046150140200f10402c034041d803020f400c5c007007880d03104d046285040303032125407805070310880c0490581400e0011b84140540d4000c13aa81040601c02020b091005000044482c812302c506d40050000c196280080c101014034400c60142802d400760800112011000c074285000e0502c4004000298000079003130103026040c2c0c0c0258075011740032410300c028003036850b0204060041e035000d1042404004024402e40c02c80ba104c001449807140e0203160344009030b02000f0301044007040828410401c084156600501c0f81ca811050710f001c0b00d03240c2d414420140034064012207407400038440200c09200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 373030332 1250 373029082 373029089
    0x20c040c180f05152503020d09050405011a0309030c0714130c17060604051206040506100803030c090d050d032c1005060f030316050c0105311208040f 66
    0x39414141d81c2040700254211130202c0d072448519a0002c0c91825040e06044d4151181d6001090628220a1428081e44500c641548880000c1c20900040b48500d041d10410b03040c0d0b5407034150040c2494824100b5a1144d001a000070790300d2001f84440c3c00074903400c120a8019020607030a0201c18100603091116510014031002d407014100151552040c3e40314075945044d6444a010400e551901408503c0324465600103075080026040308030048600010b801d400760b48950103c4216503912100c0f0b2100202a00904000390010400304007400e00c814003030007000400400152401001d5664030f85806100d1005e100071a4452005401c51000010740110034011040c410f41c0c00c22a0b009020f0700d0300d5000d10000c40c0d41c7c2d07490008c11307072503124400380056024024085070b9803460340d684000080784000804850714814032000401c154032035010703280f007455050854190729041c00c4d00f9041c2c3e1304280c84050340c0d0911044001808503080c4d503490551b41c6c000c40780c170f69495040041c86502141c01f0b80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 373031582 1250 373030332 373030349
    0x30a0c020c0f010503070f0e03010f1d030304170c1002041502010e01110a05030a0b0d0b09011b050412110a060509090c163e0306060d0506011401020c040c18 69
    0x3000602507980144c104c0b503100325030380b4242d1140740c134181c019a200038600c51520f40562800906200c00c90300b642c403101400ca440012000f00c5003080050a550b84411070f4010840101507249084500c1e0700e0001d40191100d28003034441c0038102028075012a0030a5000124810130144141100c580a1044101001070503000f4010403101040801e4248905c00100040110000000e90788400a030300002d4a070344002c0c80d40020444900303101d00030580507150051254031b04000030000003401c000d0746030b0841c1540c913540e080070307d0001044070300f4014181c1501c4812000040b1400ea6499a045901811040d01c81a80320591241801a0142c00501002000804101c0c85060b903c8030f070603998030a139111039a4030340c50341c240d2502c1e08072035241c40450301500c402d9140c09852100f05000360102a100390219105a528502000305a69040c80003820b913811031001441681c1d0a404420807860060044174607151402001c01c0480c0c400e2002e000018280d141c40c030b40c12031031403071480000300b0a14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 373032832 1250 373031582 373031599
    0x50411010809030a0c05011112060901120b04080304020d0609081b01050925091e0b0303091008150a12030305010803030103152c060609130818010203040b030a0c020c 73
    0x2e2400e558901c240d1a0718070900210018060800c40e00350041c0d00c014142200050b03c0c0c240210040c00c43c0a03003505ca03184951080c20020459559000c0010111904843c144006455a4845d10956072001c0c0c000d98000c405091014041007190154042061051003010341c1c4900304c02101c60484040c8403038a0380c0ba41410144409004000743c4980f040d0070000140504021f0800100c081d108580d2000788400e00302408054001c00e803045011030038510820910a2480c010101a141c1c070810810552040082d2140c0b0340040c031500045920608000c01150000701d400f0010f54040301d140d000201c000718081c0c0d280201541030284c1c900410f1034000841c25941559250000a441c03015070010031990fa1011013220010107101c81c0314108040552440503011074502c03502e0340011548d0500035034200300441c80c0a00d28a129200c22500b180605051605010304001b0402107605020704500c400d010214541031010300944c0205410302c0009803452844001034104a0700c26012071148906 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 373034082 1250 373032832 373032841
    0x4060209061b010c09081e03070c0e0915130b19020708070c060201110f070302031218010b06181302040b120106030b010203040303080f06220621020f090a090501050a0504110108 78
    0x701d080030740d4a048901f00301445140382192460081060180480241c00d80c00150b07034072403090643c02004e4002c2501d1002c0003050845901003400c0d54420491100e05c51f00c0c401084c07154420b50782004e681c1981d038034404190014602660091041540c8422002600c02e04100d0440480740040517030780000d00504103000e201c0c040c14054203403400e503c00400980c50003058800d204a494002120f500c40300d0906110302010042c0e02d07030810840480d0b290800d1141680313000f2055400c214401c0030450706044000d0b051002c1121880640818a43c00b804003041164000d40a01622010390100880c290f1618030000d051b580c44001e02c81c1550420403045c0040b0703a000f5401c60344000380401b8403800d616600041901501c040001107a098841022107001558a0304030204555851100c0010061158002c01261384e00c00c50081d80990022941c40603400c2121480b68882017003000010316240c1c50b01c0d440d003540c9089940641055036274003000104a6020b001d4010a0000c5c60800100e180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373035332 1250 373034082 373034099
    0x40e0a050f070c0c330311040501030b040e0d030b0a21030e030f06090708070902090a12020d0b010801090605090a02010804020405190f050a05060102031e0304060209061b010c09 78
    0x60240241042007281516103050054940030b00c001040b02c0004116a1a155a0642c207198250030903400e440400040344c40b00c00d8800c1c01025221f076110102140340919002c010740c01040500c50f503036042529130701d0304400040240310307480c5590003644002c21104001d60400a07c1e0226800800c1a6048401200c845e491059a401780349589420007000f070b590700e6030010345000c0051030452600d05c29030b002c0240024002c110402180e488008481405440c1c0c21140140d0041c00a580d030080200f4100b0090f0b80c5040124000c0b107800a0240e005070b01340d80e110359429040980207003426a448000080400146101d03544c0d100032404058089400c640e80000c05029020308042c0c40345d6201c801107012072100c0142c9400c5100c80c0d401c20440a401034060b100074100484441140c640b6140c00078105500210884913515000c2d00101c1800111300070004091700003410039950726500348140c4e5070315143e0740018030340e401020003000b2141e06201003071070a45880340c0a280c20400c180100300181e42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 373036582 1250 373035332 373035361
    0x31b0b0406031e0c0e1c020102030f13080307050c010206100e0f0a0e0102070f05011b09090510030602070b1005120d140c0312190218010e0d1403040e0a05 68
    0x4074030b072602107540e400c4488100c80f441405201c6402d0700b80340240a42c801d0750000041c400052064440c071401c1031803040074240f000030441001e40903030010001000c4a00d954402070a0750480e0b680d001c001d082d185c13101d03603185800158045466600800c002a210360b010002158070109844408400300d080014654807040007404841d002c80070000409c0300c4820300e402c416480541d8800031911542581403200b400003000b0001c2c0e0300b9528142d000001d8040c0802019403100507500c07485841460034000703400804e401001d410f040c103002c00001c0000740701c50008205190003280c550440d810300c4030801c902022503a109510030190f095039242841c02c00b1569008030140c0b400c1807800884015001d4080f442400854082c500000455140100e0071980560141545c00179024488940b000c042040707110700038241d10120603502108405600c203420041d03e5160140000d4203681084e52021000340c008150b0b264203070030116007805500c100c41c1856074000c81c56a0213005900f80702c032800758401d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 373037832 1250 373036582 373036589
    0x1111c06060f18050910050a050306010e06100c020a1d0f240301021b01140f040506060409110a030507140612010b3004150e060115020f01050f01031b0b04 68
    0x3107400f00100c0050710300640440c0040c030b409000f40c41c29203004920428201040d000d031521030750403d480820181000580715050310341800d003454594075481c04011070184d4100d04001081000300913400141c4072072620400500100c4083e030b1108221008000040030000d004a005100850070004612544030051030715101d548040241d81900b0000700f4060310401200c882ea1001e00041d82d400d24105500c110550305140c8a030000a40b610414003814010030b030782c045d000b035011030041006480d140d031142040314420a07008850016520208902c0d00c555030081d11181c00441d010014602105d5030074910040440c1d82c0c070b1a180288030210031040040c0211420311102250045002510624040c81c070100240050108829402540400d201c101e80c129944c00071544440d41600c02401205410f10240e800f0700220782c03c01c8106038460f003410604504501c2404040e44601c0c0d02071241c0c0340284c1c400c10320b1f00c41d20f41c150f007090100724401c0050920030410a90003000585c2d044410765068 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 373039082 1250 373037832 373037837
    0x6060510080a1a0406180612030507061a03010f0c020705060a08040b060f120714041b030515040f0911010503010b0f070305040312080402091b18040e01111c06060f 72
    0x103041d0803da803000d01d10600a00c00c0d41040c501032000c204840b202144d0041510b09990911100343c403220180e0510130f401ca00200410001d01ca90030015541750800e40442c08042e104820120b124070010f0700751803442601311b5545a4480075170001d250f043c0448006000d05130f80c0c962505c840b1880c001c0042e00d004101070501c11240001c56200c0c0d46101d00381d454020300905088081d082046170a0312540f0030321400341d90003604d001c00c0711142018020340150800c944034100700e1f01c40c1d060b0240e005d04401004050b404441100301c48031691070307204c1c5400340d120354000021203440500d040b45a8421032140141845010710040212407610000c48800d0110014007546503415480c080c0c07450300880d00004c01400480000001e5280d00ca100750317100318000c6604600c6078a92260008030030b40c0c041202814840304222004c4804c2c000c0c61204907091000d800040d400350704000880c00c40b00d180c0d04c18003070604002003034849940720b9130000c5c81041c4488402c209a81c40c02c200a803000407541201c0c0c09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 373040332 1250 373039082 373039091
    0x3170a02041a250c06090806010f05040b0f0a0b040e0a1404030f05040902030a020c0618070506091c03051209010209030606131b03050901110c0d030207050f030f0706060510080a 78
    0x4411402c1ca4203940010356602141c0d000c41c3d4602090982c00a0042c00c0008000c3c400001e201d62000030382c18101c0e071440c4484a992814034090001074a545900300b42c00540e60313950030240d0703281c007098a4001c1c41d00c0712401d41c07540d003894003183c41028003400c1c00e160747d414440240c4103560400c4807184c1080e89401c003000c603182960000c0c1d6146c007803a0301c0309203c14404802c200cbd0644854004011220720310003a2001c0b44d07544441e002003030040502d10410380d48142000d0242c1d003403850003403241000c0200b20102094100610040c55864103004400042020907004c030b440e80304c080820b421484203c000d41c249020b10011940d5510020036091044a6100d4280386400303650b40003182c02401031b4800903c0c01110b00004c0c003d80307810b03a44022035601c1d2065400c0c0c2c2c0f020b80c2c41074030307855000d003400380c5070300041000120040c3d003280209480a01076403600c00580001003000340545103981e840203850f003809052440441c4c5c840c0e0701290080030381b000000f160700c0c5d000044543c805202940000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 373041582 1250 373040332 373040347
    0x4030f0909091e14060c070209070816080709050301021902060708130f080c0307030201050f06100e0d0305040f0326030c0a0c03090801090b01090f020a02030a1101090f03170a02041a 80
    0x71301140b40f40241c001c00b80584418080d20803561402001014000d60748032200c1e4580403001c50706040115280100241c02c1291400f000f88030742c01240c2c0140251410204040e201d1001908980c8030441140145540c040c1d0101d0720758050200c00e61112036402e00c0b00541c1b8040000481c800103502004002c22202d2070404100f10119080d9000041150100c0f900e0382d03a1442c000e8024501951142e100c2d01c040c0000542a1520344409107514035160788180c20076048a041c0f003413100c1c40074400ca0a0000c144004100301041816800086006641da078010291101582d0004030854034021346000e030400070400d1060704001141c100319003030316044008038010700b42110000c02c01d420116081d42418a950148104c3c40c0c0914181ea130850004c020021051034500c00320b1140d1150540035820521810203038038018941403621444c00c8c00042000780c26903032031440141c0d460b0b00440100e08101200340c0403080700f001e40d80c0d20114146085180508180f0103003010200c1d400c03e200b041000003200d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 373042832 1250 373041582 373041593
    0x105041203091a0310090e032d1c0507051303240606121109030d1803051608010b0405191505040204140118050108040b0702011404030f0909091e 64
    0x820003803503c03040050b054495424010025401600d500041028911000c1820b80b2079104895205462030010340c60030b80301d9201900d045c140a49518800380b06c1044031400d0f0010b081c010000400b4401c081d60500c00c610010780d04460000c2c19000402c4000c0c05085028500140c0c48029039070032001e41000420180004440440710782c4001c20094101340c000160545c1110800046007007900d001e004000703841024200500502e500380c2d5040e400b04040902c06070052154429082d10000c410661131b86a44813907103003461200e85515241c043c1034003040070b00c40a1082030740780c02040700e0500c060b06040d150315103c1c401c0c050340e0502c1940d50b120203800c3e00f80400307aa10018207001d0810354565542d600c8403000c5244840c0795601148142c06000c034040c3e0848243c0007901d205849448141d01e880c5c490075034509000344401d06543d40c88e40c1600b03210040c82140d40c42144240d440a14452084500a24201050f07002c045000e04010040340000c00f1403800940090149401880b403c41d01e0420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 373044082 1250 373042832 373042847
    0x20d05091309030302032d0106030b0102030f1602010e030f100c02070f0905040c1a0f0a201606050f03061207050901090b0312070503030a0504020f0a080a050c010e0105041203 77
    0x1c404000e240c00c405000b01a05600610b03c80d8099403101130003062284002c004900d480e000c0d45510050180051090a006c0e501c01080c134441841101e0500b1840c05074031a0f40d5000700380350548a40c3c00c080b2641150380c407080c1841c5440c0140c0c0542004820790314826600e12181c00100c041d16200d00c4e00d0440c051003000940c0041c40380150841c0000d03030300c0341642c00401042d9001c0e201041913410224001615143c020207003050350b080d40d0301d46100f502d028003040c3c000c1280c490410131002c0d03654101d0508100c0f120711440d2088003071b0100307071001d8142c1d401171070541d400003040c001c007803021416491101041e6903000c1d0060382d24041c1024011100c9040821980184d507014103004001308003102c05a10107180a2029800c64055011003c4041842c0c042c1540c0182144c0c0100002580c42c171050300255041407025203000c2001c1440800514000d05540248a541c2d11288800080c402c0c20008a0a8200282812031589400d007000811900c514015607001c01c0450b1207020405201d01c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 373045332 1250 373044082 373044109
    0x1091b030e242e0306200a12050601081605070204061505040801060b09150c0a0213020705070e060d0f050f120409140f22050d0201060503060c0307020d0509 69
    0x600380c001d1480c107580c0000b4442a21400d80d211980340703030015245200c0e01c0640f6181c2c0803207080c260700361550750303040b001c2c0080c0400d031002802841e0803c060000124080d00904000b500d0380c0c22140c0d1502900300c12100700800340b40c10041134001344a6115200c94410801c05828070b0101c0c1c2c0c4059034004a40a00816405029034240b00d034a94010658043c02a1041d159120001d01c14160340f442010714600030024004d07400407030703100102c010841e00c600906c08030305608151554500907400250075002170707400d03000170180c001410b081045800d01c40d0303001911046031071303460034100040410b40d860086a001000b40d102c0d00302560a00c2010030052001d01c9902d41250382100d0b8030340703031131440340c00c00d210300301100d814407416890707041c0c0e4503d0081c4101203400a841035599018451800e001d0f00781c1c1044d030128100d00841020070030900c0850964101078001013004da151009061902c00c0c003d01c01c0160740c0d4148244004160f000c6a441100d80107442c141d601d405d0030308001000250350b400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 373046582 1250 373045332 373045363
    0xc0a0f09270c0f08011e050703150602030301050a051c060c0512040c05100503060906041a3006090d120b100807020c01090f1802070c1d01091b030e 65
    0xc84402009640e010742000e880c22282e010000c0703139980c0f44281c281c1c1c000034082542d9426100c0c0140c41110035903c1503502c10180d2401040f1590050740d0510b100b5840c0d00028016040000140100c0c00c2081e03080c001001c05842d29a422a580e9000c1d04007075440b0000148060f03103840030880294403c00590354038a990924086d0942010303c0c0c00d60101c400c0f4481c06000e0941941c61400c03075402042928414031000d84070703400303596802c1c04010080c1f401920b0070709041c2035007d007205652620588503000100d010760a4202c1e0b03011890814070824100011403c1d944054104140d8020200700726841d030040e410850400ea58a814245c080d102d0258015005410021303215549940304a800f0f002c3c0c2040e409445000c40c8000044a40140a00030503040315000c40040040c0c401021642e22440d008450042c2421540c1da2001201c00c165481580450f42d40d0b10317030a038003244102201d4010040140d040048070000c4411003050380f9144040700234140d4407842c0b80300d100c6051108150501080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 373047832 1250 373046582 373046651
    0x30203100204030303050f010311150f0408010213090b0307140402040e071e0201051614360604060e0609041409030a181a0d060302030a080c0c0a0f09 66
    0x1012044002d401c280b20030740c00641400c0c0401c44034240c0c2111141a43d4010031002c403603488190502c10206174010300215030340703000c02a00342000406800740c0f018262900001d07036072348030b03c140225001c080c640003801210310381011010329580020b0b45e58101d03010f003e184d820010410000030028022603010b2042c80010310200079005500c080c0381c000c01c1e400b0035101a44030035107040482c00c0b90300446000d03582181c0d416403441c19a00810901041604000007589003040c41039102604221f0005e6034034204588092810013148115441080010266405030a003850700c48028840c1c00c0c4d0710002d80c0114000140b9280c0e0b525141c01c0b01800f140175200d185020f081411025589900904c1d03d8000170b00388180d420041814072140c002101e07a4003168414440040745040b165a01c0780000c0d18003d80e98440000040c0c5092005011a50146040541700d004028103117040c0406d0072016072041c1518030080c05084404103d060a031405210f0001d00310560008441c100601c6040d80c104d00b4228 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 373049082 1250 373047832 373047853
    0x10501080901062403051602030421021008010f0905060105030115123303080f03061f090f170a0b09030f070507080f0a0c03030309080708070c05010801051206160504030203 76
    0x180005002c0b408081d503130030800340d91484070005907c0d500a0203100180c00c20841080300c1d07005a21401404c400c2a00d01605000742e45c0d000450b855907400800c004a14010010030082a4207041e0364010075102a06100614188000070010f12050166101c40c618018200032124031904400c2c040c1d400303840c0c0c00c100401d108075002082a40005021510000d5040105010340302d014607141166070000c022030900c106542c070148141c00003449a50071664a20a640c03543ca0012000d4940007450f031a4000000c0c103000301d907c0b4078036060300400031803055480c0240904000040d008202600700300036641030b8031140d6200e4250b1040803400c08060030f000c034035030003840b0300890441d0882e00000100c588011080180540b1000e02802c040c0400110701d00401c08240039400c210305030343c41816010700c2c2082c41d6451851507041018280c50925005002788503a5800c14480c5001d050112180c43c0550920b8846942e2850000d107080500741c3c51820310b408240c0524166005186d000b01a108803980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 373050332 1250 373049082 373049129
    0x1b0605090a1104020408070b160503030a0506040606080103020906041533090b0f0309120309010b090c190e040b04113f090a02060d0c081b0301050108090106 69
    0x10080d02036644040d11142d100091900b8400c490888040070098014240ba003c080002e503000500c0c08003030104200d02e280d0000303006000541c41020710310f5000540d070a1400038842183c101d500035005000c0801e0060001d41d44a4054681c8008211004070300c882811251410300d407003a90045281c24081004520741c80b01003080da1424254080703c0320005556002d08642d521841d22401d190420b0030001c3c0b0f1846c08040c402160300076458011944032600c0500c0c014450f40c011a00c0c503130380d80d40d10240d1901c2032030000c10041d00641c1c050701e4541004591a680b2110702813408208050120407045c50b034003602d481c0c06c10124410010305c108040402c402d503a41740340d0f1088018039200751030030988140b02d52400c04042e413070340e010115a040020300e03c0f504c0d00000c14081c000040c1c0d4403c46501c3c00069450000402001002c2c00c00414800d601d817a0181140b00040c01241c0b2050101c188510100030f0081a2411102c003460b03c143c071a15040c010364014440c68200a50350b44180c00e01c00c00c10103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 373051582 1250 373050332 373050343
    0x20f1005042d030318050310020918010e1f030804081507021f0e030d0509010209010e031f091406070e211506060c100b0102010513121b060509 63
    0x5603050b4810409a40c0c0e41c08980845450001a038000748045500780042441802098141c0c480e11364615089615000002c0c9059211502402048d400060b10b00d2141020182441c0010078002501c841d5410690310060300a07000b014550f110340d4151400d4081140140d20030015038000144643d603503100c20700542c881c091034034010354101a550200e02682d1001800645290f020344800d01da451000741c5c81400f42520800111581c030050003050008902480381c180501d0140e400140d4920035a00003628200e40b09040c544a90071013104210b4030400392490680c00c615007100024045020303e85540282c49111140340f03607100e030b1310070400c180741c01480f503100003c02101d080c1a14807a04000d1200742d41d10403a210a80e8205c1d20305102e4090380d4140050304078400519003818008410069071a00c20140d426411081d1181700d800d02c0d03540c080c0b081a4122081c208008840704558580d0b1400051010540d0b00b00601e8182181a40d5800ba1113a01c0542d030080c028400d50500e05001341d13441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 373052832 1250 373051582 373051589
    0x6020a180b0a050d0b040510050102010b0a1d0405031207090303080c0304080d0f060504240618060e19120b0c03070207141207060c0b0907050913020f100504 69
    0x1015640300000d2031081035200c804480121800516001c0c2810040310543c108201c5400c80540b01d4420703214039a118090300c0d1091540c0d640c20190903203000c000a0a440e0f0015880307008900c4160b044c0201204044c840040805040c400c595a4640d0f107412446d5119642c6c0714500050208103102c4165417180030107044900969a5881039124086207000d40c0c842542c0042c07494104018500c0c95501c241c10109081080b903400103590b03580c88000c2805d640d081005c00c00070710300a49100c000380c018080a000501000e24000d103021484011070601c1421a000707640c2401a00070194059565050006084509601b441c600e500c0d035680804100ca60040000c46003500e08a0000301000d10501c01d803071242ca901d50003448071900d0310880c03d103503100003400680c001d0741140c0300200c2d81c80200910301c024041561107407800c00042c01c000c419080c01416881b4540c120000400a03a9292202e1641050070b4161010040446100140100d202c400d5050380003400e200340324288540010280049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 373054082 1250 373052832 373052837
    0xd090c0b0f1207091202011101060b0301120318062102040902040e0103060b0306040c33050405030706030902010519110a060605010f05040e0c160b0903040906050f030a150207080706020a 82
    0x216121a40e05071054099809517018198070420760b440035600c10504110103090103400081c061341c0b00c00d0403a0655200f40c00c07032600341c0f0360448801c08059120300011714140c5111510362040e4140320380200007400c4510800f0124002c151203884912041c1c1c1160001c0043c51021550349503a0021003c0061091000b621018500f0916420310705000c2401c600c1203034030005015500d0b00f8130001421000c42c11441b2088512200490008401002d030341003080340c03240c0c5409803241e20745010149001e08580050082508144114005036044410ba07401c0004043d035143e500f044042048070340c0d0764501d44c02200e80c4180d07e01700e42440040c3e4001c80c00d0b203600385e846151540c404c041c1920390340310320b11801c0f00d070b07600120001d010403c41c840900704885855008aa000700242c0b5140c240c44400e80e545d055580000031700b00f01c0c0200038031442004140548160007070000000000e5214080e005028003c0010020310000303c01507a8100c85800b035101c1000341d00c43da07075824644025017000c1d10007000f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 373055332 1250 373054082 373054117
    0x703050c1929040b070201111c0c05070506150609030d0e09060114070f0206210118090302031e1303200301140412021908030f07030209060d090c0b0f 66
    0x1040840601c400a0002c0e80c0703900040291142d83e11100503500042c002011950b84125480f0100250001000003201242451002c801e0f038914020407100c000c10709400313009040003240006040424502d40c4483e1240d552900450080701194191142c00550355041c000c0b1a0f00d00d00d0180c100c1032030381c916071040e02d0008480d5904001920007840d0b88a080e69444c5082c8650304c0080c1c3c07180714060940b8409440356040044c442486200c6000b1246100b85581701840140071210101c0304030005095031031400d005124941d18081d45a203c0c205001403490540030f00e017000b0b20f05a0048809070110610510087e5682c1e00382060105080c01b072900d2081d0741c810102005250500074805120028086d814042d101c40e55140c203102c800230000029070180340610350b20501000440b01b00f01d402100e200340d032464012a003c1600da00100404180b40c4140081b00e41d90f02c441d021b507040d91500400001d0030a001341000b034038074038140e44508010500012070188040710100a0031280c0300c003008819 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 373056582 1250 373055332 373055363
    0x20120060a1b02030409090804091112060301020909130201020c06040f0806010f06020d12110a090303020c04150b0c07080712031205040314070812090309030c01020c03070504020703050c19 83
    0xc2ca00800c00e0319880141c0c800e00c0305115a0f00b20f6400034203070520038061613192664a0922105550301c9000c9402411401319201c032190020404031079120130124001c606c0c0441c5003002540685002e0510300350410340480c3c4100b103900811130742c0091700b001840300b600c5036540c2c1c00b40337034418600e0b014040090091000014064a075800c0c0b6a058030a0358010b00f101110321401281e01c0c81c210403004120307a84481e01c0d5819040050b00901c0240c18a031340d0502d115055040291500c44944441070055103446109400003250a0003801510302a0388180d40d40d6888a5055103000302135000010240244800000c2d5645900c045500152003a02d41c2203107214460250401c81d0002c990113404500109481c40c03141101600400209108249560811503c0c00001e28503c0046a020815510001c1c604070359180400c6030403d0000244001c00349000041c01003500d4225074841c003406690045008020540a00207842d50444c007501180c0304062101041c040403100f003030050303406411815050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 373057832 1250 373056582 373056611
    0x1401051b0303370b010c06060905010914100302010e030a0206040909120203030702030f1b060f06120115050d050a050607050403030306170d0f02010b13060f05010206070219020120060a 81
    0x103d1120b1109981c062003d00301c0c002c1c0300040e1401c0703143d480c10044031100510026006114200c00343c081003000080541c140302540c0c00706c07800170004080c585404010001c241103124203e10547e40e0a20b08409000564030200b440c211410500a5112a0108000c00c0500c50395019540b120300507041172070305440403d41039132607200503100170005800800c4100e2402e0007501c01821208209900000e1344c0c0b25820a26080c0303007064801e01c120010381801d00610b1300d0b00450344c003001800600201306481405610101880d15481220f010b184102070071030074440e091182429580e00041924220310340a400100a9030150000303e011034544200414950842c2c64001c5181210708000e050300143c1d0a0700f5104050884040f508640d00c80410ba8030b951960914103500d03400581000c610142440c900c4044500031f0b8118074115400641045411540080d60340d9080c1c5c14443d00a403180c000d400103e850700030b800380120314030301c80681107000c442c00041c0c42403013405517000c200007035010803c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 373059082 1250 373057832 373057891
    0x20906010e1c08090a0914010f0513200426060f070503252001090201020303060d1a070f08071d060a051209030702120601050a1401051b0303 62
    0x1031600035403010201c442c4045200e12400700107002d00320035401c3c910084006082a84182c00522100e42c4810b0407500c070041e0310200c0390160a00c482010049400c20002c80c0b101d050111298032495114490706050a000e503581c0c03c0c1094203106000d94507131701c9900d10000c603030041045034024404201d921460000101c2c0d481d00030074100c040004581c46005003181d01c2e4002411241079440c13400103110300c1c5501001c456101c80040e03100c1840c004410440f948910070342440c00101a4101015080140c0e404412a075020504840235500078003a070420102072490300342a2104010840d080c0600d0b260840154070a90310641c1d9500055a5072110494028429110b032440310700062880e00b00e5441e1003800740020020904d40141000da00411440c55000241d0b6001b000da08005891401d60a04021110207003003000001d00c01540340c48040b42e85c4020b94820350b1424550740c003581455038410300c01c5801d0094440c160009000c5480320003900c0743e00640b80340c0c1d0154400801505071740784000c1e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 373060332 1250 373059082 373059107
    0x804030506061e0307031202030912010c120e060112030c050a0809040b0f090c030c09091608010806010f09020906040506070605012102010c060b01140d1b0903110d0203010f090f02090601 82
    0x190400707500d50366442c0a4540901c1a0391f0942c0000c1c844602140c071400c04017004001c9600010410310807540c1c015200010704072105800380d062010b0b80e03103484030000309541140c0b01d03402c0d005131200071403c04485110749074000914a0082110803801c0c085040301074100b0450840d001c0001094034820049c40800d2405901d40002c68400090580020080a140e00014400c400c0b40f5201120001a80060703040b030f00342c000c03619400100da4456601012460140c10000000c00c40795040010081020b007803803040c0714a40c3e400040a4506858040c00e031001400041d21841d1152028507040c80a00424002c40ca24100144d803900d159944e407100c444c102c40d4068550600b402c9660325244c01810100001c1030601290840582c4a00303171810007806000d980d59800030f1a040ca1322200e002d98190709646038200030000406002040d0a5905002c0d030f400d00310703103451000c0f42c2ca04c0424007410200700c12502d020b2420001c3d1051001e5028004034070762080741d8000301030352400015204003107400e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 373061582 1250 373060332 373060339
    0x30314061c151104030c0810050709030b1e250219020f0d020a06080a0b09010e0f0727083304031205100306050601140f0f04030804030506061e 63
    0x465010200700c0100102d8565400700b4008143c103000e81c20303445510383c4941c4c022110035031440390400610f141440050700c441c4210005203d14201384400400c3c4d401c10b404090092011000400d0301102c0300c80c01006a0040c1d1b4034103900d40e10740703048510300300b801c01c85041742e400b17003110100b021003032000c5803003102072040381c15400d803407074480e001e00c8940082048500d40003680c00c0d41800169a92200742d01c010f08e00e0395910b04161820000c03076002d0303500c5280524040c0003080c00520000356200300d059403000b4040902e070b03617a50b0384840445d001d0301d0005914011403103160050b1a042c0c150b0b10f0003002d0f9503001c011100d0b0120b907110054004092501079207a20b100c0c046005050880202c040c9800c140039142c51484410040302260840d8400c3e1a44682400255010000c00940303001d45a03114900342429601043c044002c000c040c880c6003a8030500306400600c2040046100302510043c5030040141a00d4640f80e14020340d0b90724040d0782d0326108602e24241d880804010b80b501510600c4080e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 373062832 1250 373061582 373061629
    0xc0901030305180a090504052104030f0201030906020d0905102003070f1110140c070b07030c021e0732150403140d111203150303130303031406 63
    0xc440e08042003c0c4448210342c004820203002501215500880e4080c0d80108042c052900b101c150307041c1c807a07041c6414000c5111b8140410000704601c6070340f0180c2e2907020308001c0740800840c13408900a10070602c04c05070f40c624295840050080010b02002d29440c446000c110b81c82e010095082c030f1900034081d61068510800020385001d204040ca40402e482c1340c141802089802200d80f42804000660380c1c91055640c111141d4052070300081c560400307240e03040c007840c10009880380544410010a5402407548500c40c18003964403c00800880d01c00090117444420408892a900c0d4550341c80784004241a0340c0b25140c1c1a0001d40101c40a0300409a00500140445061044440c0c41e0000d0f0800070100780b000201003070394a0400304111080310003904000c0300c5800081c180d1240038210442c143d10070002e8203400404541180d40040401083c02054240000001d00c0c62040d0100002000f0103150000101074040c2c10001c003501c070b0880e0200b407994412040c0a0700200402c040080a00301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 373064082 1250 373062832 373062847
    0x70309050c0d05070b12070909020304020d110f03030a030207050c0a121b0506070305070501060e0c07060504020a0911041a130e1005030313060306090e07170f0604030f020c0901030305 81
    0x503042e214620300c501c0c103465a0642c0c5080a081c44c1e0400700c11441603a4251040054483d4405141030103807509407070843c11410240c01048421b182000c008040040070341d80e0f6481585d58090030214144010b04a9a403548282c1c0300030082c0d00400411907562240680c1074440307103003c505d801c058800340840f04048011503112110010082d043c0c81c2000f9890242c04215501c5000091000c28041c0e00c80d199502c045250071803c640c0b840e8007a03260201a00d050015500030101200d181c41c0d00007101103029240c03400000c00f092001e0340509003841c9040d50480080e40740801520031101c1e2410000c260030402c003a886144d10800003128013030200300509108400e83c6d0803401c1d400141c003810140c0c07540d884901003480c0d584903040c02c46a1400b0144100112589405508041c01241806200b014a00c2407101d07a9188540248000302c00c440718901d20081d070800c08119080c000004a03800c42c189424098514042e0016100050080031140783c1a030a00d40303403a60484c2c4e07141ea20305190885 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 373065332 1250 373064082 373064089
    0x6150302100f090807030308040201020d080f0a0c02070e040c1a03090d050c16031506140609010503090a081c0b0105091e011101020408160602070609050616050a1505070309050c 78
    0x104034a0700c010f20102e0080860440d00c10020440034511a0720742030100e052a0001a00c0c180501100c0010040b50034100a055803081d03414642001c04d040380840e210b07404190aa01700041504903c9049040310304010038844600c06403001c540410501b9101340042c5602074801e4801101c066696511203000308815074450740080192442000a42e6150f40740020782d5910692642d00c20f940303804507501d0281c515813040c45043e0040c0448044d0701158000080400d5140c010b940045050240100004508000c05e110895403a80d10082e0a9500c00c0c50123401c0c1c101d042c8000da44000c45141ca0b0040a955000b00c00f01c507001c0c10003c01c0544e400c603113400007140703101407a80503034104250210303101c850107401d001620203000810094003500d01c428030a0b044401c601ea20100455008940810402d1742049081c0150f40040d100c85a8800c0720080307004c11501146001001d600c2190080ca06109903e0071181c02040414001d0216881c0c0c0c8104400f5604100e0018103d03810000d201c071281e24 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 373066582 1250 373065332 373065347
    0x840030b061302030a0e06090106050f040e12031905100e04122a1b18020906090a0902030a05061e12101d120a05090f031c0c0615030210 60
    0x60051200614507008014030b401e0f6003055032010401500da900c240fa42d54418455130340d0043c039140013040700f1440d0000003110501080102c60207942c3d90703180ea0242c600b082c0008081c540420352025500d0070000150821a80011115200310345460007180d068800302d5144011690307615407040082c1c451b40c544102e0300400003000c60034014250303104814404602c082e030f400c2d407851202c051201c07081410443c1d0808507004003038190381380c10038090101058080a00c89040c000f14030043e1140001000302e6200c1c86041002c60780484222000200b140c0190021403044880b110284140e840c1c000074054018100050100800e000401d02051070415070f10302411980c07050111001d9104003d0000121075040d400402d61006007915080144010440c031984071801c3c2c5171445c81c0c8194024000d00358003856401600c204146111a10540d80c20482082c108201601e08549181d0503000030300550030004045495504010090030b40e0380810f1203c4080781d030040c02c400d1401c2c040c20b07812242c80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 373067832 1250 373066582 373066591
    0x1141608010f17101a030601090912120b03030310090f0510060e010c1509030813030504050d0206090910060906020106030804060302090a08010507032003061513030840030b 76
    0x82c45203104c61150803100c1d0065500204c004503000182c0420704040c117041441c142c0200c0c0403d0704006005000499040d14954407001c2454520100c2c1002915003025081d05c516040c0d146c0300100600101903c2030080c0e0048458580c410080070106103200c1c030a45508a80b6803400f02c003e85001c009481c024622802c3c0400141f61210502145503070700c452004450343c0742000c0c0303aa24082003040540019009030000001040c01c00c002600b5903004100d072145000b20786c02407600d00812004c640b10b200c255000d00300018a14489840e080380e03150407000d642d200b1b0a0000c1c5007418001080350061103188240ca41041141d4540f90508005502070340c040a12250428084400002c0c0b0180a11841d0300602d202e607004152000d840104980d040c0000b200758500305800c1041c4103280d61800c00b40d003610300942da001c1c0d40f250f1701c1c6004000145456030024020031000103450310303440010702c415001c1007500440501007044401ea08403085c2000449400219600c2000388003050744903503030b541e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 373069082 1250 373067832 373067879
    0xa06050912040f06030506060708071b08060a05101d1501140c030403020306010911031b19080609010f0317130902070302010510170c04091401141608010f 68
    0x140900780385031030a5403080e0701c40b01c64882c4003542448280d5250061941040c03089420600301380072030b25079030094407443e8401050510740d43d8800c030040403500f0f4800002d10307882c8140c81152901c1507521010700740844207482a003003003980101e410100440789800781400903a111072603030790380380c480703809607044980140c1802165480c4801e101072200013881c0140c0c0e80d0001d1503c442c03071403040c10b19149040c1c01c90090581001c05a2503101c60001c16a50722400340400d200e0101c840b02406107561080c211440215068030b0880e8002c0303500551502c0c081c070b00946045a0076a83d4040840d20198a4040140faa41c200f848034030a2081700c4c8040c06030a0a00d0f01082da07215542d6140d84101d0344090300460140c7d440d502080481d000e5102030340001c240d00d0a1503c007489040b8070341d507194030644203080c0c030460791502c402c014825038041070b0620000c0780000300000c8034089514102c210048a01ca0802c0482c002040313013aa00c503949090403503000c2181c1e658410305185d0740d40e100903ea41c650303510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 373070332 1250 373069082 373069093
    0x30d03020f0a1d121501060503070507060218130c080f10050108040c0506040f06020c0a0e07050a0e15040314070f03030e03100f0608010f05010b070206092d120f0a060509 75
    0x2441c0d94060104078400300b038100a00001c0e00c45d01d550104200160b100e0414800148200080b4a400c20f040b03411103a48440016603810903285558015228468280e4001d0842d0102d0000b81c251903008454080050311858203030307566448001c0c0c202000311034400003001003090421142d4041d4040d02d4106101d9403c010810341c445021411710b40140c0d000d03000b1f0400540082000c1901031000310b00d0140141e990054050403d11449440701000d04900b08020780080c032100018890203102c0c40444008181e6694124102e01082854119020035a080c901e09500c080c820107000030800b0444401d9131040c01c1152550b101a1200c0428113251071309070140311040380c2192980c0c070544068404580c40003401c0b0b402e084105007140c400180030308130640340c0401070200d8003a01007501c1c004c40e811034030251380304c8505d0003060003e008052540d42c1054401c0740b01d141ca8011000844804406030b40d81c0482c1100c05842e1580c880c1202c810140c0c58000013024000310750b041c3c000580c40481e039401c440c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 373071582 1250 373070332 373070387
    0x9040b060f040302190801090b04060c0c05060705130b1809101208030403030e010213060807170a0c030b0a0806220b0f0405071e05032103070e0a090c0c02030d03020f0a 74
    0x13425190490340032100c0627501c4081104108007071042c00821041c4e45040d003420001d80d030720b1382e95840d000307040001801008a007090702408848050405040c240c6c81a03902c3e000441690b60b28082481c40c0144540f0110340014140040500550b00b16400a06038800e001415122a079080d84007500680c00c041d2680c12400001c41d00740010413805202c03800c501d604a1600300f00403c404d02c040c00100c20070100010414924405008168000502000008413a900c0c488183d004000c10030f041500f0200d00c480002d1982004500c807440388050085070080c450059600d6140c80302501e6005201c0d44c0c824000c55400d6001411440e44203110300201c07241561503280031a802c014030a2150f0381d5541803d000c1c080c60509216039210014071034001c0c03040d0747c00c440d03880030035000090850302000540c07010180c207a90380407008401020903d00030003110f410315500070462500300c4802d9001e4032038001401101c0c1d00c28400c40b000c1400004506c4c1c2803500060040398035401200181801086003044103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 373072832 1250 373071582 373071599
    0x10f200a06060b18060c1b0a031b18150b16050f1b0414010e0a02070c09020405040b0a0e130501063311070b21010303030209040b060f04030219 63
    0x1000900b00c8502010b8a900e00304c02200760062103001c0c03140c010803042c061140d681760700188205c01c040e0101c0b4054403004101010135011050341d030005e03100340b1002d2810081c500041202d0426030312049001411140100d00183c156a203c1d04800c2016042c010104400c54110740074088002855200300f500404689500f031400d40414001e285540080c4903952041078a01c01c4401540829a800d00c54a54002c450744010343c014401e0078002c051000c001040e90003194100d43c1e143c0e0340b222001034400d0716018000b000f500107020f258012843d00c0c071794040601d0005240c40071101060348400260782c5000c03c00c1e001e00a00f0504491035901c130140400c4052840300c040920000c82c118200e501180c055142503081c499035000f90521403007078103ea01141004c60014240d41140c0350250360b03110720203400000c8000c620301c42040301d20a6130012080583c0b6800902c80b80d503040350700340b0500d0001804c01000384a000c02d030740300139003080200304018108048400402d010301080303040c0c1c566641c803c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 373074082 1250 373072832 373072841
    0xa080a090f0302070807060e0a060503130803070e09070c26072a170c0603070915020c100219110d020a0905061507030c0204150f0306020c0c010f200a06 67
    0x71000768000704c42c00d00800c0f00801c08000240302924106101036001c40206851252a00400d02009000000101680c200e105045006a40041c3c555503a1810303210060062909180141c4a4161080401e4030680f181a410105030b411104646143c030103020440580300100285090700703402030000902058100e80c00c1c20303c0c0020700e0782c42c0801c1c0e142d5550b510f418800030703000200c400c0c0c04540c1e8002001d01c005070040b00d130082030720b9140d6a0380310860255885006a4080700b071500c5034500b040003059000c200d0000417102500c1542050981d080c041e0b8440078000f00b4403100c050300c00801400301e4489030416071040b101910304c0403981e01503000700f9200c1c8100e81003c01000d440758240013240c00c0c0803440c41501140d10441ca418070095640003000d0442168000e80710f1381d214010701c42c1c14030010003804001d1070055148450300b40c0d40d01d400401394021110300c076054040c0310741030340241d40121070382c102d0b08105989004009034200a000080003160b00303d002280b098540100009440317105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 373075332 1250 373074082 373074113
    0x12071d0f01141c0f060810110706020301030f150b150d0f0e030a0905040b150714061509010e06030303010315110307120507020a150c050c060f180705060a080a09 71
    0x1015680040c00948400554082560180d9603d150842c00c100251b00401d81c43d151540c0b00c3c102042c3c1c0c0b101c8282040a034000c00d280a40064400800042000b05e846020f8280a104031000d100019100e204103007201d00110140e9081402c15521511702100c85c40205059401c0c605c0010300c40940b04100000c41340d500300040c2c119440041d020440b140c20209400052004075000d1111348101c0020035a01c641c1d6085042e1003000104924041200e00060801000015400c0301c0d09454100340c40c032103058250004038020000704001181d140c4d6004800c0d8820f08000d002503146900c0d40e6100e03104425a11034024040d65078100c00751031020503000540c041c01981e511180e500705260420001c4030f10140142d82594001d0b4040e10005014960f00480303040c040800080c08000c200064070a842070107000e480d41d0085508118202076031604450040b4007101c80c0c01054200500e07425968541405016407103a0144840400180302d00d0342151300850000010981800b01ea0310210b845551030f4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 373076582 1250 373075332 373075357
    0x1e0c03061210140403080f10050603070c0b0c1b03040f030b0603100e0c0112021c0b010c050a0f0c0f061b0c0b0c010501092007151107050312071d0f0114 67
    0x10900040c140d000c101c1c540c110214804034011f17814554a1080888014441ca0323009207004800140307000d01441d5580b10550300069032910526005800d5542588070b07180c42e00c000300c1145240781000200000b90b4080d03841200722880130604585803c040c14030300400855041c802c003a8804201061f40c02100c0754046148002c01001c0011000542054040204210300910601c40041d403030321440c44034050403101800c00540c0a04a41c01290f0700102291701806510508412400300b1261581c004e0590380070342541074042e52140c2810b000c02000e0305c600c0e4005174003d41c4401e40703500e0141d00b0310b034010300c910340d402d2595944800300606034000c0f0b6084465650340301c0040001c60001d008404401c00c1c481204244401e41c50b08070f503443d002d5144060016010200d0319598000f9030b9204030400d5000040c41ca454003c01d1600390b92360b40c001405c0404d6580c0c4840896203540c05045c4d5a408240044450b00354190400107009144e02d0207183c5904100c2a58003c014108502000b0513a405a18 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 373077832 1250 373076582 373076621
    0xa0209031f0c030504051e070902040b0d06080706020d1416031d040c050f0309030909040f030e0d150b0f130f1404050d0813050709051e0c03061210 65
    0x1100c690742103403035403800c500c2490b04203c00c12000841c040386501044103a12100c0381017503000c814003480c0c040f698201c4800c0520000300070032805501c4001d41115914514240204c903110850242c46500758401d11016078000740141d060240500112850341400d60031260a01c0b01c5440403130318402e00d1640a0b4041840181c802d10764a0443c4c07400e84004074107513000d04c031045038048000c010f803107000c1c005400401c01002090003400203200300c034005440108440a1414541490a0f000e10108000c5000c162200701c4900380c0e04041d0350f5441c45507002004050302d5038031a1010800750095450ba60703480030300301040e200300da80c03503c0381d40035080c0000100180d0801c900004004541190681c440c00c0d1003050104800143c000804e052035448524080056071941c0d0401c0c00c001615174802882c41c0241c42c0040394500f03072584194800d081050030300c16040700020210a11050946604d86000010130000d5280d040c40146c00400720152003c40c0c1c2040d440b0205e550845038408007141018644 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 373079082 1250 373077832 373077883
    0x2f091905010816023a0503070207091512060e0607051e0c0d0c0f0507030302100f05160f2601050906010f080103031d03061006020607050c070e0a020903 67
    0x2001140c0e002e000c20f00e8020410345a490080d607a100a441c01e00308035094003003114480801420f8518100103000c0407411528820342000d400ea4104031011340051044640c006001e41c490301540764920642000c81e05c0c42c0d410102d55041708411760405660080d150101003003103c030100101c9101e02d0b0113039101d9403548110591207400d81c42c0194812031101040c8104104620045002501c02007903050005090040c1d1514024070000b60038081c0c102d000d00c0c01c3c00418550080350340000c0c01010781003040418540d51844044503003e0300d80e04141d230b2050041401540c0030301e0180188110506050380f800c01102803130719040030340b00003102074a003000c8010071441c141040c0d403030b400c10007d0900d686840314007440101010014031015040241480c0b44484c81d000d648045c403a48440642543c0903440c0000c100c459904192141100510412000030711140c4601c050710700c0d281c0c490700a000d20350b181004165000b90040d004000c00e61703007040310407040d0b60700b0010440f03044080c0c3d00d0380707030f05551 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 373080332 1250 373079082 373079087
    0x50313231009020f060304050f071503050117061303020c0d11030f03070b0a0504080f0f0318030a05041a0c0f060f0a1a06030403171302132f09190501 66
    0x19a14480c0042d081050b80070051303031030b00621003a4035003d840040d2282c1d62410010700d0550415400006405032440c0032420f0007103907602a50800302920207000c2641d841040c1d059910b111071501c4015002240425140c02c460030780340080d54060f10444001c4038418002810000042400700e500182c43d030303611500c600f000d0100f03000940c0400c2c0a141002902e48a110038000010441e000e202e40c3c030800202000307c00410f561486055024031a06c0d01d40486071700c034282e4420b0300d1503a2215034214010b01c01e510000121400d00e250741ea0307254141842c0800341035816184500a0740300c1c5d442800358215884082001082610540307004014a0401d00403606070500042c03c9544130034208170003980950f203080804200700100765070f05e540e82e95850500311500d002840580f503060004409000c826416400c43c80c2a4a000719140c003413445218070404210b403407006070f41d15600d20402a562062a2064240304c503c80508003e034038090924000805005e040c0c1076000d83c2200f501400e010781c1d43d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 373081582 1250 373080332 373080343
    0xc050a0b0d0e15070f020102070611030a05060f030c040e0f0d0c141207030e040b0a150f0513050904080d05071206080d021002090418080901020c09040c0605031323 72
    0x802d110040c2a14030316552010740c0b0558024560740c24003c60b406418072040c404d504544103070b50004420022610389200d4112140d0090b58009005400c0101064551401040104c040030000700240507042c415024840602590f041214032800382c0c50746021408014890103102000541d107044d800c42c21b41c41c0070600c04013001c905c080180c2c05800961490280c03041180c100076050b003018003005041500080240100c01300482d00600814000150b05503e503450340400c0c0120b071526071b81e03800d400300300311003030700800c2c0000b00041086c18040080c0d080100c5041c0d0454090f0f000b0a103030455015075102920303419186100010941c03082c02d468440507100d10000362503500d014000c1100441d000035510302240d03800340340c81540054400180d035619032100694605003881c448a0319010308000d10150041004240503000b2a040c40f03031180b4010704214420750344400b0480000c2e0070080103c60542006214080c41451820103501180c850364540c0c488500155038038401d12990b01205040c030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 373082832 1250 373081582 373081601
    0x30c0e060a060c350a0306080d020d1d0a120f0302060709050d230706091d010b160609080c0a030906050c1207020411031e1b09010c0c050a0b0d 63
    0x441e0311441002500421100741c0c0051034000107014604000b11048120713920503041d0a80040014801040700c1d0960030070350460321400c00381c55540e1000034090341c8550328410f40c0c10020301141403e0440c180e4404000c0c08802010f4000500651201081d00800c40010000e5404042e0045108101503040051984c041c41d203103041c036521460000429481074400100038000a0041c030310744007503444c04441d01c14a000c04012605401d55030314000c3c2108415015a58840440803201d0405030410304c0401d04a030380300c14001386032407a95814080305207000c000407119070340c50b0040100030885030006080e960000300003501d50f01003d0716015042c5030007507010b041030260600031400c15620100b07803c00035400144140c0d41e2042c051000a00400709541c282820f200c002c8180003020440c20404205000f1400754841580c030349a00c4141c25144400320058494002c0001d42c1e900d510070b00b00c90265503ca41401c600c025202c800054100c24146c00140c030070440406c000c8100710160003101c044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 373084082 1250 373082832 373082837
    0x1502041d0105011e0807111218030c010c1205040b040e0106030b09190903090801090809010f170c07020f0405010b0d0f060f06050306030307080408010207210f08060a030c0e060a06 79
    0x41c01c2c550703803440c4c80d882140d000c103040c800c0d9400040c1c5c0b000c0c01100725840e54000d0100341c03111074600d842500000e41158107070005240030210204501d090014001808040503113036400e041c0d40703130340c0e60b8103800f55200d03981c02c1040b0f828040080c4034440d40000c1d1026012855018a42e9814070030b00400321520000101d200300011001e00030158002052001503801c10f84020400006a080684081080d1342c001b48882d0320b0442424103001e80174024003104802641c0b00c0181c6d5203082e00031180c03181310f1004011010402d202080c3e1898142004020140c0302402c4640350f888070384005411100b017648080b108100015140300691041c3c45010200e0705950001c000c00360070400c0504019111740581d10504ca4000b02060046d0380c1001580c11580e4412961541d0705c1e22095414040c0d009500119403000e441080504800e180a8070085402150750341c00c060003045004c1100d9010b0082c1c90103421a031001008004540a10040800751180207980d002c141072000a1006011465000780304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 373085332 1250 373084082 373084097
    0x18010203190524041112100602060c03101401030914010e0c120303061302160609050c0a0b0a0305061f0306050f0907170901060e1e18030904091502041d010501 70
    0x207000304000d6181040383c400d80d00017940c006100c1001c04203118030f407014603000201d10b0130803d030074000c03401c81c0302960765907400d9800a443e404c0134049540002da400c104902030300c20040c032141c20351600708070419105140c00701d104019500e4200400a08003151106079464a81401c0c03c10030400c1400d04043c001d5032240c0c004600c8060f81916400090a1188200110110106595603a405583e40c81801104a01d040006440c00c1c1008000ba41340482c1c00340142d03c842016450f14030b40800c201c0e003000e8261131a141c0110300c01c40c010440144065440b203543e08000c210343c40c074100d0800c4010066203000503128140002c1045050301d50011501c02c030176290420401c0c82d8403282d20f5000e25110402e02249490f01c1181ba4054481070b0000b00411080700304001c40c0640c0032181c06601070020109451903100c0c215507900015000e80c0154555004100911107418158400c07424980a40d80360498400c0c0e40701c007601640c1c4150301200010300c10b600701803900c042c5d440d25180180f009007081003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 373086582 1250 373085332 373085371
    0x902130e091b0406050418120c230a120201240506070803070918050a0c031505150d020d020702010210051e04051501030b180f06040b180102031905 65
    0x2641c44811050030940241d481c2c4540030300d0f45550700088041c0000500a100d80403001000c43d50760002d0000c240c820702805507488424a000e20340300b17448590008100e004110b0382c540003241d13250042a400c609445004d4401300403134228030380c4410010459001007403803074418540000036507140c0c02d185080c0300e55490030812591350204403010300354000881c035244e41d1170000a850520b0950301001113090001c2c6021101c4407581e024030710485464a04003d0702e034004500310304441f692032070900600c0270f45805010500c0c0404142d82941c0796411501d1a00065045003003d1340c2040f41100702c50b81d00400c00c0d000310b603010b00c5401c500341a184002c2040d80713031500d401d2220b01130000d00c500a808100c0f0100d024031030203001c1d149144022202000c01965640341495a0b224100c0d00041804000f481d011034401d00460b083d12121003040082916072615215034107141c101034142a0b201c02003500c0302c032021500307001452288900740e500d00105501c00000c1000d843c0010448100f204841e038480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 373087832 1250 373086582 373086601
    0x10c05030c0a030e030d11070b010b0c07090f020c0f0609070812030105010e0d050a050a0b100b0928030c030512040522270224070b07020a0803010902130e 68
    0x44804071454900420b04d000c42c3c3c910241540b1440e1245459142810b80b1080c0403200d100041c01141d1046c1c101d15050ba0f6558200c600070701032a800d02416800c5101d0400804d50b00c1c3d0080901904406401840c0c4020308544510381082c90340c0b91141504418104a00302e90140f04c49030013817040f00c0107861001c1162a03400411311050050354103010811030750000c2ca0303c03090710400180380c0c40000c0f15120445030402943c0d0b0761900c10211800e011501c0000d0301200d4501d6000c2c11220350752242800c01620404000c003100c0d020040310445480c10400c02004022410700728020f41c0a6040c42c00d115041d4201981480e05401d111004200c0810081107035407124813051010006180b06207181129101301c0c1070180455007030000c04500c030452800441010402040d1a140c400c69554030703a00c0f0002150442c160050302000241f0005016101c0800d4201c82d11039841180d510641d10190040d9442a01580081c1c01c40d00c94141e0100d1311140c5580d201124001070b0440c2118032070603203440b00c00b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 373089082 1250 373087832 373087837
    0x3020307020a1e080c031815070f06140c07031116031b09021306230708030405070b04061706040b060301090e070f140a060e0a03110d0501090311010c05030c 69
    0x241010b403c0354105680c0207881e8452640a50f108100550302c803d4054010f0f504c1d00a088151814212100d80f103d46152030080d4080020f07401c10113a0034481c1130b4607a8503405020400c02e0700c0f0307a911490709102290b07020214070302c40c2e520300c41c20740d80301c00c00740c01c0090402144081c0c0c1c0442d071780409252401040b04022120841c0c3e80540b0500d0301c1c402c0401c100300c2400c9203a009403003160001c50b0f03c0c100060014101d9043d5a42c036038030390500c00c540442c0005921070042003180f0301a000c00a800108032400c00840c1d000d805401102c0400b5520810a0100d51003030740540d00203200c0001519512132826051504042c1c101c50034440c0c43c0c04500000c07a01e21062243c2034055596440d41000000184401401094035019464401e0f55a0400c003121501840c1030610401c0800008100c060094280c85c0e8050380140096803014119940c4400d41070029002c0c0764808a10401d00703000400034015504810311aa070340e860990404081e09081d264210385000500c2014000c00142111075020b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 373090332 1250 373089082 373089103
    0x22b11190609120e0d0209180105012403060b03070302030c070804120204110c0d030e10051005010810150c02010c020d030e1c0f0807030309021507120305010b0a2106080a0209070302030702 83
    0x502180907108d0210400188648540c070060035400c03c000090300081507038100c1c0310840b42c58019002e2004003802101140c01c24050018440d0007400400c900d5072080d03010f1a440802400071905e00f4605490350900b03900705500a10800c50144036031421800c00c0d0152031a41101d03080b0701402d1001e005205501d819902c6010009c041e951908946000c00400c05280b414a441c2403c0040d0f04055440d2811011980114ad000c218600c02160302e006103040c95904490b00311454840f900f8041004440c3e001d900b80040e0304018018071f0641c0503aa40c1881c079243d5610039110500d52b180d199003480540e1508031864110b106081d903030000800c0c0814010a111648800f215940366110b28065009221107100a90000000d034602000410b1450003810201c7c0900310000140c13604440480039030303000340106600700701c0601034541802d001d15442409443d01440d111040c1c45400d000301c08035440c0d0380c001d40307031039002910050960400e15100d50300b25041d46000c3d459464040d43c0030395940c2005c2c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 373091582 1250 373090332 373090339
    0x1b12030904090303060f0603020c0d180e0402010909020d15060504060e040902120a121d01050409020c0c100f080a0c0512040809180403022b11190609120e0d02 70
    0x50300c0307000f0540f282d401803014180c80111010141c0d1030710030003030081d00444010303841441500e110080160040000c101a0b043d1014154845424051000700745000580202d043c0040c4c4200071404080c91b0014080402055070005081e210000b2280c6050400341d02500920004002c1030103d95401042c242d0003000039540800c000f140783c80400e0072000c5200603060300c0d000c2c075500c0404000078214149542d03070740740d540d0500f100501100800c0c030400d54003800780480d10400003000741c0000380e005070246816803020f96900c0300c1d04101094070302d0f4500c2210400106541c3c1561145a0070041d05070300018411401c0120b00409a0060300c103110303101d044084c0b45420800501000480e40407034a031801d02902421441511710142010440123490490142c054040217160a02c45900c6144d590200780500d1880c0003410a029603a03a500424150b040340900440e10702c600c1070070012030b040c1034400c400000c0c10282d02c0c140244452190b20300e003402c010100400c88202d948581e003c209054044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 373092832 1250 373091582 373091591
    0x60d09110901030c27060b03180105010503030a030b030a06111e030105090103080f040803040e01140f01020a121b0b010f051f030f0b09100602010c020c181302121b12030904 76
    0x70003500c4105d48038400068190781041c00c003083c0c550b0404007860040c1c1c45c60300c0049807210040c0101e820303540e007402036a0305580113002c040c05103442900101030000001d0103498078440c55440790410340e01000c41c3d0b80d03282000024641d002d84003040d502101200202c850fa130455051800041400d4030600c030180800c000407544519240c2d42100b20340040c0301c0c0d80c0c1100d683c2ca0f80d0b07650100301d11800740f007070b980300505525450203642020007590000c18070590142001c03944a5840e0f0030919105030011007040035064070700002d215030040104641e80505100605580361602c440740807a026040035005040c0780000d00c2000305040e0846210300c850742404180b100d011282d52000744504244030f6804208142400048800f6098010959683c0d500030300040c0f0703076110148c2ea19101c000603907400c64044d1300028210780040d46141d8228466040c4001ca4426a40009900400902e4504000d03003001135050460102d84100200148050340e003e50580c0c1445041d40e182c0c020000d03001c0c051600c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 373094082 1250 373092832 373092869
    0xf070e0121060e011202040b15030604110409021206030606030a150c02030f0301170d030c0e060d0906020a11060f070512060102070801062c06030613060b060d09110901030c 76
    0x15006400600240e0842603c01d40e0745103500040012a904164003c502e0032103484207030b041c02c9107000389e00022100f90600d152a9042400010040e03d4bca06903120024800482c0985850000f4003041618001c10002400c12000f00b50408078060300c9144680d0200101c8400515101d00381e03c0800032a540000388003715901c1130707040d4403d070a400c0000c0c17000000040345c81d0b45607150720601c40c1c0038a81180d0b100080400305030111103c1480b00804147c10183c400d42c46d190001c002c04034031081c0708003c108010b03607554407400d0b86c00030310711540801c406000d030b05414502042883d40c440c400c0c8400981314104100040c01512074108920605d003103410000d040780e4003c11480c802000107000130812a5510360004541c022a00000100740d400ca507914010701840e174150b87e0080b03000a001c1e158544400140c1c55101254080c106c0c0c02e6510fc803000312499441001421440808060100e54400d15151205459484a001f14800c0303542c2c034010b2000c03484102d0351030140e0b4540503003103180c0c590 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 373095332 1250 373094082 373094147
    0x2615070e0a03030903050d021b243103031709010e060c03070f020a0c0e040515040804170102070320120c01020a09050d0f12120c0201050f070e01 64
    0x44510303060304018000301c00010154405503141c01c89018909032a54100003030b10480e01c0794a44041c0c2c00b0280502c2001d001e061621186000c0c0003190403440091169000d07000005c0b680241600b42410b01d07074a040c601c001c81a0800d15082e00c02d80483c142d48080c11a81e01900105112054009010301034000842e8000c095014400420821040341d0711890300036400082e40d07000b02d071544006200400c5500310580001040b9400d02e502c030340030307400c800d082c140301910215000388103503054402d0700070b444148002000f94a020324010302e103040d640e50800500074411000c0710203500f40b9a2041010030080381c0e1026681c0718140115007801e07901541e0102c40303841d0401800c8501120f20002600f9007502d1015802801c81c5006526000b00079a940c000b007100c0c540b0418001b03003002c420020301d9070000300c0031076959840035914140000504080507555003240c03400d20385100940e54840600203644000f0a9503070340292075140c42c004240300500001d049a84818860f4055140300a60540031030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 373096582 1250 373095332 373095347
    0x15030a1a030604060903030b0109050108060405040501060f150305010509011d09030409021c140403020a080901050418090302061f0303030b280e10030b06060d0605040203070207261507 81
    0xc0e0003021100e0904040c00c085001301100c40044000c2032621284010550040c1000c004488050712080301c203942e41814040034080c0200125980d55961001240d03080d034000700100036105004109403030503a80500a001c80b281070b000301e44150491001080500040320202244480060000d030383ca8580b0000240b841c082ca030044080d450021802e809650321049000c2504c092201050110495103824120128026200170740180c210f001c0e04008503030000c0090490200c10b00d04207141699441e0310140751000d01003c0a03d05881d248020140b550410040e60003000714810a031308500c0c8041d281c844a032040c40004e040c1503e03407905508541c1c80891200011503035500c607107103528240e4007860005040b40a40c003580345007103001c41d07501000d103800030041d80d0b0b114445446645804003040000e4006560f00707190b054a9003c04a05500c0790700243d409580c00c0d8005000341c6041503564020142c120308050b113203011140380b4241e444000245451098030034903000f0201d4803401e00484214 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 373097832 1250 373096582 373096631
    0x10c060606110105060a030206251203020a0f0f020309011b0f0f0213090f11060c07060e041113121b0602071703090a0501050912060c0c070515030a 65
    0x1545010000110240c0100d00c0240610490008104554405c420400021460301000e5040700e0213000c0541030201c0b03980e03510071100300e26030702c06100701c40350b40c807500342200f40703440003000940106e50810150b407c144e84c1a201026400c0c054280c1c810307160020750702d0041c1c0070340904000d45405407400a034035800c46e101041c0d4000c1c8030806400018100700244000e0701030101e00541c01040da610309101070b8890f00c0c1d0180c0d449120504807100e551a54406182917804090b40301500f005400342c0c010080014000610064850302d5102d400c0008110840710740c0d160798011500108441e00c0c1e400d40d5000d00c1c030f040c1ea42892310981e04103101d08000c1d00c007042400f42a00e1100c000b800120720f0507000502a411111400926003481c1e000c1d90146413a8090ae40c0601d4100700910402e03c80d940c000c01c040c020700701001c0c00345807500d00c0010804e032400301e06845480307240d8000075000380c1c01e03070741481404050030065451030f00d028113800703013120148001044a60031a9640c030020145900c00d42140170034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 373099082 1250 373097832 373097843
    0xc04080709141b0d090c0503060f10080a08071403040305031303110d02130504050c030304090605090c070b01060c03120c02010515030105010b0a08040c03050a0308100b0324010c 78
    0x190340c0381c5040e140204410428107018050103070000b640080140301182180644421041c1407040000059018004882e02210300440452010945840400003944690400741110101e070400c110702e0341000c0d8086e04411b40c29045141c42401088000c0d04849020790321007114131000c400c04960070300350300450304010300900000500d0880040011001c8040d640150b82e11104043c1c15800c0109103059075100a4004400204a1020010903032100740d0083c0680d081d60782815881c070009007540d01542001c1ca201e80e54840c107101d54103040011991024514030407d18080181d1125171202205208560400c0140b01030001010700c00c42c040d0100b0110054184084241c40201278040c10003240c0d02c0d00c40c518a100b4442046c5414081d080c100c1360710401c9145007c012607804ca881d00001041034030700d500c0d00180000024030410001d40341c54060f0361880000d0910b141512000d2429501c6400525800e006000704e5500c00c400c42040c4103030350b612840c0d0024260005889020300c03071802404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 373100332 1250 373099082 373099093
    0x809010e030a0c030806030309010c0204020307140d0c030b0d020f100203091905030d03140a0914190b09030301050f060715060609090b0607050c010c0f150207030f030b0f090c0408 79
    0x2042c0c2c0000300c64144512039105c010040d034030441455503a0054004a42c00038503201c400f03a016090642c0115042022494034903e04031004c402d5180c55400050564601ca13070300c01d00c251095174148036500c2406406c0710b6105103420250005203100840c140124460280d03101d44020b000e000b0030440303d100c84c000c0c0030400c01440407070380011405014403503180640542042c05403803a119101e90340280d141012071000c192103200c0f00d54001c04c10000700f22082c140b161181d0520307410400000c90200030590401c032400c40f0390310305a44e00380f0025007000c171168030610040c001644e5549400300d64500c1500c8058a615142c2800c010491500030201c2007240ba04801040c0c4a1b40b1907801415107022031418402c13400510107210007440b0b810310140058002003103903c2ca03503200300d0310001403501030100124154010b131106240b40c660402c0c6a011a81c0c0010304504060b04216409264031160504001c080030300303400f04100c0341da240401c1c1d00c0b8407000d00c00250152044003d0b0f078090300d9000f08456 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 373101582 1250 373100332 373100347
    0xe07120309030c050117041416090e01140c090402030a0209060705070302010e06120a0e010e100204230906041d010608071802030601120c121e05160e010809010e03 72
    0x410001060000ba511000302d0000400c0a500406c40c90f900c06500ca0340340c4d00156165210707058809442c0f01000e40303c0c040c00341a801c243c42c03e220a0f40c042c004219000030040b00700c074080d40c01c542864091240d140030000810107650151402e84a00000682d00503a90742d135120000c400a00c100c003580365112401144040601c800000e00c034050724801e8944416100710722040041c640034503c15402004425070000c0c9016409401c0440400e01410000c0744190090103014207281c00794080b80c8005502140400c1145054003004800c40380809986059603981c02c0814a041401405140a19200e1440d00240341c480c0f4020b0092070854402000002d4841c0d03e6651210f40a01c5142502e002021403e0601d1000c1d00c00c036402b814050b180c0d51921002a22580d01800611105509100000c260001941814003030b0610700070300200c0050301c8403031a03a8614100c50000d4015812150b44043e540c0788190440c04500d840842400e15880544d00d00c3c01d0140940000c003001d911500010503a40c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 373102832 1250 373101582 373101587
    0xb220504090f0201020124031e1205130504020a0f0315050901170f010e0d0f11030d0605011b020312070c1d0403110a050a0308040516080313050405040b0a0e071203 72
    0x29240c0b640b00764024014104800365081e0706100004d07140201c40b040e0f00c13040002a107504000c8d59848401507042c400100c540d2245920340141347c030480c01292001a000ba0100c10290100b0094223040b9011410b00c1d044120040468142026140501d42d9801000450561407040100140401030402e50190b84801eaa104102004007401c08544103006d0b40c105042d138180207034080015102c2c010714800c980c0483c00c40b04241c2c46001e00c0184540410059001079050000b060b0f21f04943c000403c0281c98600018980c0740c0c1c1002c0c0c1503641102d6144840160345c04950115120408000310351603290300d0130100c0b0500078a6120158141c40030711038083c038207101003940d0b108500035154070304501c000115885d2034030490880140650012051040040c0c0151001600240580110b40075100301700400301003003941d5040220b140c1e101141d40c450900014891101405041e2804e11030744c100f80d0340b601e80b4640080e1032100000d0300ca60300c4000d40e400070441d060040044160700c20b8803c0090801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 373104082 1250 373102832 373102853
    0x5010f0209041116020d0215120402011202130b03071101050108011a0a0308030c0a05190801080105011d0406110c0a0807060c11030904090203120409020d0f060b22050409 75
    0x380d50140342400e002d62004500c401c140d030000b407195500d84e4607515256080103200e0409040407684005e400d21400300fa41c1c551000380480d903401c903006d07440d2814503000240450510035048909540100035828403018200361100032651803003a820b40700d4541d42d40035240c600840d404090507620342000050084415000516111114400c0c298589001d0092141200b80b43c000601203460420204090740300d408001d000340400b9160803810542e40010355404079000c03001c02400941468018400d5410a1040c2c40c010716070103040d03007850100d0f401548165840104050000ea64841c03907007280ca2015800c40d5860140e050030f5519202c403d01d0802c41c03540121100b6036100e80f031314542101080c01000e044255540580046040c150410100009000d0201c001ca825001c3c0c1c43d2060700302c000c0803002c5d00c040c180c4c0103805612411600b0610049407042562171503d00d050400800c90841c0c030a0407110b03118074010300152550080b122000b0601c2065101a03002031034140c4503018403012400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 373105332 1250 373104082 373104097
    0x10f0209040e01090c1509120f11030706091e03050708060a0b0d030c02060306031c020307140c01080105090727060f2f0106030f0b01211703070c05010f02 68
    0x2001c01000c000401454200c81480a0040075250b00410500c5500355106c00703005803100901e03050380201c0c1c88080003540080985012034400926000c22000c02c40e03101080441c3c49400c1c2c004020191908030014440c3c1c0f130502c1107a1a80174602502c110544810301c58801460300300003180c003031070355880c0d0f2181d5850040f10700c2043d143ca80040c0e00c2181c0303049440c04e143c8a82566a10450700c0894082121960002c1c3c0a81c0d8107100d040b201007801c00101c50340511083c00ca40256480314900c2c10040e282003003100c24101c16410280e001c50740c0383c0c0c1014815054803410384040e100c030740d00c1c4c1e03100741c032403e104030301102d40018082c7d0108401c00c0d80f00d80040940d03500d03584840907010552410340f008001e00345c1c9110024a80c069020111003035101c4800b1030214400040707401544ca0319581e0004c07600c42e03401d6440081c14001400003074109141c000060200203c100400201c0b0b4544d983c0110912018204940000010500162045400080983c0c0120080002131450071695000354015072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 373106582 1250 373105332 373105339
    0x1d06010303080f040506180a020312250f060b0111070305072301080103170f04091508031801050d090218010305062a0708120901021e0a0e090c0c010f0209 68
    0xc001074200b0083c03200301030040c2e51110080a45403110b2200313248200c04541500400c0c81507406590240c0c0d401c100201100d488e42030565910710000d40030041284034041c000c11904c82d040744880005240752203104049411500000c1d1140344000101d0307106513000d2122600d0700c100d49000c4207001c6e001c600d0f0400c4a00038581440a03940360340c0e1811022044080140c0410300c280010030110761203d00301040480c001c903038113280050320701084845400c15045495450343c0c40103070708a038542410602000d8200c12000b14141401081007036940c040d141d80356810010041000e08000b11680c0061110581c0200f110305103d00e1881710000c441e80034030096804d441498040b41c0c9000c11400303030711200000c20300511748280518401c5003c642c01802c04568050040240c43c0500d90200580c80c006d0140400258ad01c018101d00003014181c2d0500000703080e0b000300140c44400340c00800c1003804003019102824140e4440e10088983d00070119080700650030000d946c4542d20140c2c4c000e082481c4c049 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 373107832 1250 373106582 373106597
    0x705090f010801031a0601020708100f06090506060301060509040b060a05032403030f07150204030521090105030a090303110c030a090f0506031f030f0f1a060a09020d1d06010303 78
    0x100c0111075400003803102178000e8105050103d0803c800030b0786141d021406004944902d0340d80c82005140090305958070740d04544d01c6007001d500e81e503203010b100001e000d0b04000b441075050080014103a0311043c4105024080c0c009407246043d03d0350b4014540c0309200074029030726161070003405403045e0b00855070945039a50510036610198520400e00700400000350003182000c40300490400b0a80c8441020b40d1101c210340410b41d201c034098002400a14410130150110b54900020106040030300900001006410b201e4000c0d5a64024240d039880300b40720001054081d00d905055000b884401c0b070394a98541d000940340006c01000004003c0e2130b043c1c0c1d6079010140d07038502d260980302640d406415480301e820004a418000780c0c00801541080b41c4500411082d84c0e591003440100070480201c4260b80006980c1090010304800d03002104504105402149810800200da4228a01903211490f0307012510480081e503640c0b02a01410b8004150000000551105c9541f00c1d024031040300021141c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 373109082 1250 373107832 373107859
    0x2030418141017070303020712050109020a1d090c0d02041d0d0e0f0427021825030b0a05130212010b0405030f0a030e1c05030d050108060a06030203070e0c070803070509 74
    0x5000c0d04486d0154041c218039130030524401d04081c0c2c008000d660541d00d64400c0805070ba1020310301d1000b01718000f60240714207040860702d002407d00030481c1800d50000000040242c6600d1f098180c1c050741264001541152a0301a0048080c851507444091080000800c40c0c0ca400c0410311405400132154a007030b4464400c1041b06a414913041916002e00d08059007103110490002048410310041c40000c01c4155292003108045003101d0044258181000c01c01040c01d00480c03003212000c80340390070302c805c480020200b4900003052003554014000b00c1d601481582d081c0d030650b1540c64001880340740c19651102c0105041c0c20034001c0314171a000d8229488540b0710001803044100e941510341d4441c413004d0b03c040050b000140d08554280100000c404070008100b40000c18041d4150300002a455061080241c82c140e0000c042d03100251600e079050001d071350006400f400701d80848c625541036907607040c40f04445014407400108003410100c24486400d4100e006002c0700c40d801e171000c054590301c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 373110332 1250 373109082 373109129
    0x210203130615052101020903030a031b0c03020604030c1e1103100204030c090507051e0d060f081b0307030c121104050c0f0306010309051b0a050907020304181410 71
    0x41500c070f4180d209a0b5a196004801c2030580509140c1656400050900e290540070a0031544030102d0034001039070701c0c4103915652100c0c02007a113142c10300d840c160003912441c0c3d801039600d41c0d02404c090240801c58401c1c00408c44a008a06400b0b0708000e00c80ba41c001e00c41c034103207005502c260701151007030080c4501091042c25900c01d44003202c0d0050207885480c3d1a1581c3c80e00201009442402000400c0162410940300b080c003900d40c01001c034031800e5540d0a0b0548000440301250002d051551004004104840c0e00195194462090381200b840d03c555220029241c02c1e031a43c40108a03854803080081e02a9658039198a442c0c09400201c80d802c030a40f0401c800c492003102c001461150502043c0c20180851001c0e561010040c1000501c1010685840d443d201c07084c0d04984500d01042220200707420026500e000410090f510b6100506000e4006910390040d80161031300c80038407101340300e080e1002d174002c40b60041d012600c0030954242001e1301c101c00701d411b00808200403480f0044910b0b40a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 373111582 1250 373110332 373110371
    0x90b03060d17090102100c0804140309040519050601210b010c0507030602030f09070305030a0e040906110310080f0c04051e0403030209150a080f130204062d03050c012102031306 78
    0x707c0e9565624499482c3c0e559890b050b0f0f0200010040344c4000c1c403102c005a1524410f6502911509003060314960110325404107980c4028822410050054035003000503a5451701c41c02014143c00300880d4020711000101e801c1044841c003d41780c0d114081001060000745d900450041103103501c84078482c2d590800c0b2070703070300da2040c80700410952080100c2d5442130311817541850202001800803490004a403207000c156030b030740c01c042c49560a0000902c040c50301203100300c6004040190241c8003088100d9260782c1c42d03800c00c200c481c0c0107a44420000703003403642410759824026164008801036042504004000303401041c0690302400070481040466410981602d00c0116190b9440c2066900c040700d00c650300f0805081044001c02454505005035160b00407400517016524441c9040c032015603495900d0841c01c00703021901070036440180040703100401d20f401c82c42400c2c00c103080034501008110342460300e1a074061002a102000f80450701400003115102c890159105000281540c1d071041d04c4103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 373112832 1250 373111582 373111601
    0x7020106060c1104020d021b010b2b15091202010b040b220b040e0703140105071701030f0318030506061003020c21041a04060305090706090b03060d1709010210 70
    0x140310740d8048040d9413800317800a15803503108000c00f40c104820a0380c0c105200441d0803a101081c1d45980e0600150306000300f107a4030854129040c0c0469940810054100d0941f91300003030040c400315003c880b1031050302c0d08071003038450344020a8425900c0040c0300900170160b2003621880799042040704450fa09d0240c4802c3c2102c51503c0c05402107400d4182458011700d6489161070300f01e034842c1030a2a045205000c00802107024000c00070303244001c12207082c03c4443c000d050301c0c00d12000000501825222050890550fa488404801c04507902e04090754103412865035580e0030400300c4404800c1180104405010300700070f03500c0d80c80c1d42d245c990058040e4091085443d105600007003280081820100c45c941c0100d600007907213071400c0d481d21648500c200390340000f1540070600003403c10005905100d1241d100c20100060300001e800c0c100010a850400d1040303000c0000040042200c55442e114481e050780e034025056041c2c1d614800314042d0b140c201c0e038a100d01500a903c0d03074044031083c85c014401c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 373114082 1250 373112832 373112843
    0x18030507060506010c0b16021203011824150210051312020c030d0311041527030f031d1e130e0703331b2c0301180b07020106060c 57
    0x26075607d280300c940c005010b0030050b08500c03400070301d07101c000740d268001c40c0030380700e100c682007044108000104d0944040c011031204502294001d800c10750b48100380b90f0290341c004040004684402102286440b00403150031800a10700018002000c40035035054418910a43d00030101c1400c050060b601c50041004080d0540c102c5034140500501c00c1c0c1c004964001c00c0300031907051a49070f0400303d00e4001c00341d201a0215070050401809a103144842546225030405200340b010700310358030421003520800004060200344c27580350740584d0040300300e8502c00c1c01c040d00c0b110b800c1c415506258992450213100702c0c05801d14024151121605015440041c040103000380020780c03860740c4000000711144605c80381344507101c0c03642c402d40d0080e140500d100300c2d45000100d65007005d1138100d2803600341c03003a4980500010000d030160084180ca17588001400c1201100c018007400008a03000d00004130041c0620035400d1502e03420420501100750041c0c82c6507000700100740e2109030980d0f85210700c42c4060b14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 373115332 1250 373114082 373114103
    0x901090308090409050a0804240c080a0302040306090609061d03190e030601061e0302071e02030f03040801090b0c07032705090103122c01030f18030507060506010c 72
    0x1c91420802041000c5000d00000340c41085a00c0396030902d40d05d00001c03a01040c001400300b0012a081d1721000c1c0c655602d5a80d40c0084600700e0001d41500103459000701442e0001c100c0352986c1e40a68103032002140c0200062050244510300301d0018850008202c44a1345000d1798004003105403030b1911528a001d000841c5400441084200f011200186880420107800032880d10394800348001c600819a94a0303401189005030481c035500c3c039917280c4440401d0b10512a01c8041220140d00c80120201a0700c028030031640f90010a007050088200034401d4440054001001c05056211115550040d45041c42c02c3c2c0741e155081605214040303014000504114071304510062070214186c0c0b03644460b01d80d0340110b640f280030841e0003000340e1007920154810304019200e190003100a02c001003808106d0306d0611821554800031035102c20b101410143d07103445110800d03232141d0020071400ca140388d21481d42c4040e8540200709900184080341c090b81000f000c2080c0c3e5014201d0303182c2c1d50354028070100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 373116582 1250 373115332 373115339
    0x70806060607030c11040213140114040e0414010c0f02161a0307120f05061903021c051002040905100806010e0705070f02090a0e1b060417030d0e01090215090109 71
    0x1c83d48120304ca0241c42c41e5440d000040b04039a506c0c0f000780301424000004039501840d02000b0901c060680d0f60003810b01641036011540500a1001c96050b5030b01840d000590362180c0c10030390941e1810100e140029842c0c003600c443c032a6004a038072000c0714240e60031039565031401e65a0700785038074003440b90b1140b138103d42d91207038484c0f40000f000d141d0052984c900014030411103e25401520740940702d98070082d6035441402081e0070617011602d031942c40c0016411714949150301096807244081001d8440c0840c60518001f0800c09000154200d4800041503448035140d2100000801c025102c601c8022030b191f00c001642d0501281c918101c60311400d0311142955005026146540326100072510300545404500040e80c0301d040c4640601c110030000035a40100c0b214440c0b070034540d0000c000c200108021500240d56825003110107541182e030840348240801d500592460103101c00e0140341c2c03170a140c7d0481500300154440e44006008880005003003e0035134501503a8072504001c0c0380020000b05040c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 373117832 1250 373116582 373116587
    0x60f03010621020a05040302181509061314100e010b0306011d03060709030b15030a140c030d110610050d0318091107060b030d0203160f0b090d0207080606060703 71
    0x30745800c0b220007030844224640380c086200b02c2e4070402420000c80d0b40410305106506021000360008424191001031074240301641954207085240c48a00c2449620700281c801e480e100c150b18480740c0c2004043c4944108420114100c1c10f080703d00840c680003020001400e0391400f4903a0b4102c0700100c804c0d500d1a158000111022104800c04c8880d1000c581110039094804125240c030882c00765466031a0b041c00c0d864010003135032000d0440400603d2240484016a5000c03c2c0f9190f071a6000e15082502d40404e0941e505005100c6c00c40341d41401008804040d9640029445d600000a0400c0d64150780d1501480c80941d409400741680000b114200304002038083d0602001c0b1a01d41403d0200b20380c1d5030141c00c130035103140304c2c624240358101082d00d6041000741d00505406000c02c4029000035170003610029540e0240d6403030041028420480c0743d050246200c590400350b0b070401c140007440e1400030585980c0c1d0020384000c81c010304c40d5090000c0c0c2d50030701082041c025400203144515068003510304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 373119082 1250 373117832 373117847
    0x10203040218040804030c08100501060f09420f0201050f06060a120608030c0c04050408070b1305010501142701230901060c020a0807030b0a0207081207120b060f030106 74
    0x440d0700c44c2c42040040007103600080f41d0401404654002c14001c0e0710a0600415214182d101030140500079100c011195082150704068601e0034202406074605642c450103100241408441c40c0c10500500814454070441079080c400da03542c59000389104820000c03800c0b554103e0300e0030388040c4510046207842c03400d400100740320300d250718011050342034440c940340498255620140040d4000a440c00c100c40007030182c0c0712201c0d02168104424502621011001d10646c40e0082820000b18002107400d20900c081c1204130703030004000c1107030750386411250071030000c8101404d10841400860035940c2500c01d00140074008500c0c2807a4281e443d01c2c0512005607400c10640703000906224400c0d9041c0c45041641c0e008110641c0c82c00c05403030841c0144140d014540c0c000b00e03c02e4000304400e2001c9100c00c040c10f038020a00c0300c00140c1c7d503034039400d00328264061042c4c020030b42c0c0b440c003003441106544980d446100118108007086508500810400c585c0b003548296a100b010920041061900a480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 373120332 1250 373119082 373119091
    0x609070c03050c070611100e150417040e07090e0402031e0705031c08100614180402030708040512070f0818030d0807030c080405031206011b05011d010203040218 71
    0x4116003800c1e243c007003c0d0b04003041034024900041c4080200415107508104104040f48076120410100c0a0200e03d2515420032080c1c1d444007450318070100e002c0148580b18040d00c80303805e44615495030303200e04021240d01e80590700c10340003c034041c0002c24008000b0001d01d010ba81c0c01001014940c040e03644c15402c85005a04040f901c2c080c240c40050b00307840a10101814440a04040d601d524901c3d0700580f46101c0036006030b0b00b4050360b010601010383c0103040710f45541801c4022a0701c490609582c2006084068191a080b900200901c104150001e85043c0200d1140c015100307070141c00c00c0449014021500050408554801c005000c80d1141d0010304852104006d010004031550010030320304000c09c0018000606540100046190305200d244103030200c6140c20f00c49800c0c592643e42e82c4c0e0040300c8519082d40c02820203d0450380c040c002c0000055206080000c1145090506500a090001e036070301843e1141c160b0400d217001c061080303e202e03550080002c60506070784625503640c5c250080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 373121582 1250 373120332 373120337
    0x1030606031a0f041d01020306041b09060507080d020406120e0d0507031209020904200a0e06011101061715010b03010608010e0a020c03030c04051e03030a0318020607060c170609070c03 81
    0x1081190011281c00c1614405c003541030016aa0f0300300203041c40211090b014608071690341011041c1500d0b81e0004880742119583d140054403060281070100307684c4502c8011316051031000400140098000071f02c0034802054900400000c3c082208040d00c400d198814400020800c20203040043e00a24400711030340820880020701210550200d030001000741c6d41a14559000085014107800c4101e120a0400c01030305d07050100380c5461613a41d020030029040d1030501a2010350107510b44007d41c800b40042410140c5061240c1150a03a9a00c0e040703a141c24003089a007070030001c54a0403010f4100d0307040b64020358511500da0301c4c0899460051000ac1c00080585400300106018030381c0800103103000d0100c0c80d044664030343c608404c12891640082180030508155041038040e035601105071084030f5180c2c100812450418103078010304101c010402940300d100441c06009102c2c255110540c2d8004a440d210100115900710541100d421074070990b0140241c4000b51595125140c5015903e02c80d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 373122832 1250 373121582 373121591
    0x1050a0207080f010506090a0605060711030c04090c050307080102090d0221060109150e093f120117120d0b130e120702030303040b1003021e01030606031a0f04 70
    0xc01e40b07982080c0e00c610368031400c1c0e134458083c040c0b54501a804e450300404800820895980f5142c0480c88502840601400d01c60001d03e0480e01c64805001c0152a088000d0017002a11020321f49100f480016000741c84c064410310783d011813210030510840714168801088040785040e02d03800c2160720610b80410303000021a1a2010030004d1341000010f011f08074610011596a04030060110411a01d600c51515540c0d41d80500030060b102088251105d4003501e11850f4200301c911101b0794801c010556440540341101240c0d00c80490329014103c03050560049400d0303a44e8507041c40d0301d546c600d02e00900881e00040843c00d14100e0440052458034185000444c00280304000100084008070111580607120b96000c1d5540000784080000c2c000c3da0702c103190030301946402080e9280401032004004201802c040307140c820340e0003413500c000c1d5401040384945584210340c403442142c1007002d0342d0201c3d0800c013000c204140a806401e40d01c0110b041086644c002040030800309091030104150000e540d0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 373124082 1250 373122832 373122839
    0xf0c090e070203210421031e050105130b0f0a14091810090309120f021201060b07111507080705060906070c06051308191202030c0301030803040809210d0f05040501050a0207 76
    0x140d00c0c2411ba001a151400074910152585920030504006102505146000014001030351480407400044844a0001480d902800c0104581600000300158807042860300042c052040c05042d4202940a54006405456480c10100c3c540e04440001e60b00f500714408018044840368090801e0380e029161000c000c2e640e54804c2c0d40303940300d1081e0540d540d00540c031180003541022007280000031107a0000700442440c04030079586078090307101c0060a1107620754030131000d50f55909002e9143c00c103071031401e6942c40c0e4518110010740d02c0300c03c2c00c48903401540005a0300366008101c05126440c0f1b40c8414030403140725900c80c402010f00500020400b0032891000020894030780240c0764081441600401140340da29002e420b0852114200c4004e50040082141030b00b10755003034038110ba5100030807a489071124601300344907014451105400c5070300c5032941d031302d942158520801d9402d140070030b4804540306104201d40310a07405c412000030810800c02001a03510810041c08003000f070744165440540c1703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 373125332 1250 373124082 373124123
    0x31211070f06170f0105060f46030c020607030c1b05071403070b0702040c051b06160e09220b0c030f01060c0c050906040f0c090e0702032104 62
    0x1c9401c450b0000e000844103d802c0c0c655819001e0f00704282c4241040298905000240c503441942c26a102c8103c001c41c400c100e810303800c4000c4040803d0209100d4500300202001c034440c4c541040e06000609846d00f13207106880c020310a103400780f4202c1e4003900544c1e49029003600131b807041c08208820072030401c4103500022180341007a10b000384203001406142e4a0603d040c202d880740d11003800d1180c0c1040c141009920403840c2242e04441e81501e001c074002940d00c0b401e50b96801401c0108420f001c0b240410140d00c0700100b2460b11071940c09a00e0100d004004a0840d460310540c0c1d003041c1c11407c010085074851808815102485502a42405800304e4036600c44201d003e09850142c4404004000c0c80058121400c1c1c03036015158600d801c0c00300c41210f44914004144520415001b000e41901140c1c00c0e44458008840b074810781003062004010301c1c00c00030081c104512410b10400e00707890100c0c3c0d0f20f80c07010088860005140341d02c03055442c203418084200500243c0b080710040c4030712121403100708 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 373126582 1250 373125332 373125359
    0x1a031008010c0e010807140d1505100c2f0d110d08090a060f211d030a091a04051309060c090312170f1512010606110703121107 56
    0x4a09983d40700c070f10b500c48000075201440c00343c8644280510018540c031481203100c2600c54610170544045a002c80b151040d1000d150a9040541c012085116107401d180d00515107100d910f20410112510319080b2425206da45401e5404910101501c56020001e250406a00701c00c1400703010640000c6014000103a041c20712400112451b080c0480c1c054003526280e04982c0003041030707007400c024642d00313081c0051121140e16564400c9950312201101c0d0721015600c0b6005018840b41c6c207900c1c60000d0717001070359640c000188401c002185980c0104014014100d0b14480345078243c0303041e06140c1040d0401c1502000a81d2070507500d0740c0e902c04080412250f0003510a007820761345403035000e5810b505106940750740072100c1c01d085c08405213442c200300c20041c242c60340c004c42440800e0f9040d200d0f8511140400c10954010754480980c0600b064541011340c0503c1c04c440c0a0707115510714000e48040152035450321304c009014040000065440c032402101ea29980a030b041c01902c0360340b40c850641030f5100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 373127832 1250 373126582 373126601
    0xe090619230f0301060e180a0c0906030b0a06050a12060b061206120d0203070f110d06020a02010c1409062a0705041107051b0d0b0903031f1a03100801 66
    0x194281114040a07041032202d03900002c0c0190300920845051001c100d454180140c408859210030740c200138100c140078015200c40940c0020001f66580e61801d540d03000d055680000d482d0103881c80d0118048a00e40e00c51003084480c082c10710b481d1030f85010009140341c16140c0042c1c403140d03190800d0388500c0d0742c1c500041ca665489039100c2511b80c10007109215030005241500c0040f5440003001c4180f01303400106540c05a0703845503034100d160034180f80c00399203815580251600005902441420018250040d0141d915030b5402042001102141100c003203003510810700b00030300300b0001c46545003000710061100722038011000428001032810300314250401a4610699082004280100c0c81c0c0750140300329660805040508081184e10317813a0300da1244e0481103601c0070451003c140c1c2a207030040518a6290021400429450402413481d183da0044071035030a0300140c0d4030400b070000812400541500d0580155003501480c041d02600300341d0000d0078603a08003001180019001c2c4003405400540c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 373129082 1250 373127832 373127879
    0x10050a0617060403050f03061c0605040506070e0d0b1b0d0507031a030c010807020c18040b01090212151305040f020103060b0915070f02030f06010e01060e090619 71
    0x1040c81c02011011501002886000942085040c080440e0348003040da6042c00200c640c1941d2903c4030300004188101201503600713a5901604940140243c40d0301c614815030085d07080c0c481d295036418046800c0c07002107480b41d5100d00350052110104a80d101740c1940300110180c850030b1f480d024806246550042484950035a888108101842e13903d40100544200703604410303c00d40451200007900c5419401440d03040100c02c00000300729510801070400e104802411003a5104000804840347c0b00040b1403c0d81c42c11511800080d250445208542007030f12882035014981d10b0f0b802615041e0400404016840240041003a0343c40800c3e03c11103014510a81103088581d14900c005000d03a10709038420502d0070001d1150310116262001c500800e850040050340c2d4844103890520784c99201110040d403d0b10442c4540c0021200000d001416982c005100001c0f0b40c3c1c0e0350404580e505402d83c9100e0308404500c0214255090000d189041c166442d1031048110ba11103031852910205130607140c48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 373130332 1250 373129082 373129091
    0xc170301030c1d01031e03031d030405042003070c05030702090a1410030209011a19020106030302062d06130507020c0a050306010b0315060705070602010506130b01021002030910050a 80
    0x421000c0c00300320050f40d0b6890942e40710355851926804481c20180071002840c41c3c0a00700041014071a5216010b101c0e0841c140300c102c00b02d400175080d580d4000f0700987e401a403400440311800c00c140e009000c07800407214403d0b4034603a140101101e078510004000c84542c80306000c0f07240142d50fa440c0452044480c0c40380014201c484010010481d0000380c44a81a110659014400358403070704a41419a1502c0041c405d00400411039000c1314811050030b921044420ba1140101590640102044030701941c01c503101c030b443e03800100400036040090a03091041140c032250b41c03880b12030000359021030014031104c81106c03150990750582e80304890640042e0015410041c49141c800240d0006e840c082c1d0042c440f640c1002611002484058103042080e008244010456a541401c982801c2d0b4000150b44280343c1c5c3c1c170710181c060102a14914401c00020001d003c201d2a284508070511605130b0050001ea400200303854000d40c0b02404d1170500b800b0318030b0491140581030042a0103624501c00028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 373131582 1250 373130332 373130339
    0x50d0507081b0304150c020f03131d1e040201050c030d1b02151305070506040f090f0c02030a08040501060906030b18012c01231806160c170301030c 65
    0x1010704590820603618081841440042415a10703071711030200b029000080c820004400070307440c00340103040c1840e80e48000500c244a199520310b2034003c03a11396121002e03201e2161380c6840b074124012281e00c540c0c2804007440d402007817030070100d0751381050040c1062490041883c58950442d4017210b0245602911903140118240c0204960014190948040c050341c03d810304401410074405042101d000c00351052410a100d01480620003e003002065203540703a0340d503001107040d1140d922030726010341e203011900c2d541c00e1194000c00085035a154051883c1420b02c0703105a03100c0c5000340082d20599601e030f402280362642ca1090710081c601034a0700403198940218508002654003d07a4001c503418400b51480545922002120512440031083e40c2000d05512550042010384c6e0b101040828101d00d400150b42d441440768002c65520500f00542e034039038090745075524400d80d44404e65401101c924040d0b01c0c86a00544035480c814100454201d4081c0c145402e9900280c005a030241032a01080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 373132832 1250 373131582 373131601
    0x20f0c01020c060601210b031905100c050f0708160b0a0b03011a010822061407031401050109170a020604060f0206090c0d03080a0b0a1401121e020a050d050708 70
    0x1e0f03910080c01d02e0003100000203a1241111a240341c4804c51203140ca80e00105039548e4140052100f02e89000d00840a50b1210b007003141d91803484450903828185001d1034421914441c0341180c0100708047c95061030183c195680c24410392102c49038001c1803085516000c001003151643d240030700c1010102040311145841058215003070f03841100810444480034000c1c1d0f0360003010103540143c0800b040d8400c1d1050741c0d9003080c40d42032214000c140b580303002800c00007030303903141c140c580946015902045084542c0d449001c00d540c5c28050304c1c0c00324840003010002c2c4100300f1014007107410100240e54003901c0300c1d8046091034116400140214400c1104440c8403503042100507441603030352000305580c1c1140c0011448c0135004500103000c10607182c00090040740c1d1074100d07004500004e05944222960b446001c603959100c1807401d030000d40d00344140e00b806685809085005000e0340300350740444404c054a44000c3d4407994165003070080601100c0070001c80340c86041d00c42c82d02600c48061034035050040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 373134082 1250 373132832 373132843
    0xb030106090501050405090105010c1403030708010311090f060907020a15360303230414060702072304060f0905161b0201200304031a07020c01120f020f0c01020c 71
    0x24104001417101b00300b00d0b82c8442c0705504584080c20a6880d9030698100a03401483c111701c94801484000103110585078880903030b604890141591200040d280e0041000c41c0009a694044c1004800e0204800345026001c1a400081ea0300440c1c0c40789809540f4070f02e81e50301c21005404140c0e036445102c0c1c030a80450062400f4940f004a401503400c00180100c0d804000d040000780400d03a950804840090105941c0b01200e01c500d000045d19150a03d052702608541031540381d030303070300401c008114120b000289a5003614465140306031416880f200c10400c0611700786249038017580305c140c0081c54841082c03611019007904031001c00c140c90110000c288800441005004114200319072080007442500c010280c10360900c0d14900d4100c40d504221800126440d80020340d0100140000400c85200200c6441184512503078020740e840b4a42a45c640804003001404030300304400d06ca10440d440d6100d401e60b0181210010304100e5616160305007a003001142d1441c3d43e50002e03440c44600410000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 373135332 1250 373134082 373134089
    0x3050114011a0a050f12090105071e02070303080c121f0518010e090c1f0e09061c060e0d09080f011509090515070509121c080903090301060b03010609 66
    0x81d410b8070940802041007503c11a0f204a0030440040303611224540900304440030500600000c02003030421481c5a070090006950200114140a6803100c11800002e0102030488194002d0540b0380d2554409031041d40c1c0c0203106402c07642c0d0070800c40700d40c0404001414041c0c811021040c240603c0b4070f241e800105601d80090703106a00d00010100b5005803400c5030b45c19605040031202c100e89600b102c030380c034220300c9000307895210b41541e84550030004100303070b0154004280ea580c200a16004001e20450a00035240f10703800c10041c6888800e048da58829440321103202d50000200c41c159a40303228180a140001c4e0000110749800410100000f00f00740c20004040b80006c120222440c000000000768900c509075586403602000d0050020501c0f050f81d1490002003120301614151341c0013011a4404c0848a00c903100c0c6602104506400148151403c0600d10908bc004000c0e403030141c3d8207203402803030018240300402880645071401e00a00000306902105203440354100f40000c0c10001d002d42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 373136582 1250 373135332 373135349
    0x2d090608070e0903042c0703020d1d060c0c0a0c0803090a0b1201031e05011a09010608040b041b270b0f01050409020f040f0f08010609020304030807030c02030d060305011401 76
    0x300f448064280403088404031401542d41b1169542440300015198107020400a1100850000c02150315019001030012410824040092500e00c0d011103d442801c07000503189640244009400e91203581c3c01010480c941d6800c84e041d44131990b03501e201c00f1301260000040e03a00301150001050030701d0200240507050304918182400002d44171501e007a00144800307421103c1c00d500f00e00a01c58182803060049400500a00144ad00b0810390149a00c0d50101c3c4d03800f40f054400002138451060b21400d0055a101030450010b48846d01c9880d284040c0c03107622000a00c081c0c80000300c40c018031400380c0011800300c00b0001490000074403001118480000140100c1e03071404c03038944c607030307800000c54040d01c103140300044c0c4641e2030b03a901c4541402981c011408514103c000803031076185048002040703800300002405510348503020001a40402d48008004c00d00e103e020804150080d00580130040d05481240d0602d00209105402d90b040b9501c05d03117069540e40c2040c6052905042c010303000d006401e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 373137832 1250 373136582 373136609
    0xf07120e030d080601140a0504170f0a2a091a04060f06110f010e100501080106060e120f1c020c0603010503120d061a0a0216050a2d09060807 62
    0x140030039120301c0b1a1480a08201c1e251000501c280c2c005c40401d03607400c4024000a49a210b54080030b460382d03200c0c0c003856030000d40640c02c0d03c042c2c080020b041510f5840e030002500d040b03c0d9681e11801d219600401587d035240350300159094480c07440f5202c0d0003c1c502600040b07007040215090a9442951400150041c0d00388482032001c0f04000b16200308507002c6240001c83c03030303526000c19400e280d10b09509542c194280072128000b9080094090510300d044c52040000d643d032410454200c50302031082c0c4000c162090300386290b43c0b4000d0f080c1100c034041441a40c0d40c3c0c080010607182448085648803402c4100303a0034050926504200b0703040c2014058032600c1c03035035052800213075031400001c00d4600800400108045d0005054220000400d400203480c0d1201e09006840d19954120300400c9005104080c0021168002d001e8020700702c44028210900e02420301d05a074000003202e0908014030200c071146107001045403041140201807105c0e0001c0c405007032802990800d6410f501403505c508a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 373139082 1250 373137832 373137857
    0x8030402090f010b1e160503070215040e06040921120e010b090a0c260106111f0e03071e060c05030c030f040311102f03010302040c03110f0712 63
    0x24048176850000c1c01d600041180706080f101216103c3d910040907003484203603680d020844008054150726100b1a4000031702407092007d11118000c038400c900c0c50b0010600490190304187c0c0c0311100351409520350b6050007070201102d1042e405c1c1010058000703601040300741107040c0c05114050030380160500a01c01003c0110008694090203070000143c1a0f07941000314003e4000e64040c11400008413400840c031601340b1384244290402d2054002007041c2c104407812801000c0340440711400d9050b0181001030040003558010091403401d058140300800040c0046072030360b00849036985c44024a64414050351404c03c05559401c1100001d03c0b20030f00501548100040c1a2648105031800804044d039480c203003240c2d40c0526400f030b0340c0d0358085c1c01c007880095030140e001110406460242050001d0781c0c50a002007546c08403507240780e580010310040c0014509a01300c28182500c9150224050408030742000e0f0b13a80c000002c0ba81110400601501000840c41b1030b02c0300000c07282030003044402d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 373140332 1250 373139082 373139099
    0x201061401080c2a0c0f011403040b070e0402071b05100813210509040e0d020a0308130c0602030a0e0d081c0f06080106170111250203030708030402090f01 68
    0x90181180fa07145001007500010340056110030202101d409160b002e80e035000e00c04403903c1c0d14800f580a40102a0182c180c1e10650141d64403920050034070181c1c6156903142d0b00e8101c40140082d101d1000c02c04600c56800440e078990000d0302d0128000c940c1e0400103010b103010034080c4030081e8003140c0285007944455607041d8000d00300a078020b003042c1c5031240102040c0340400c20560025500d40000c0100c2d03642c2d20020703030b200c0b002c0c041030501070343c08105d04412171125030f41d2800f0300d8100c0e0006034000301402c00001d103d08942c98005241005903c03108446a403000480082178000707070016800420100c41c136a900c003012060650090b0740c919604046a124802a4413034660542d48400c820103040d031000d140d650142c2d0980803246001c0011a854800490203012240f06242c40000790584100b000041131241c0c08500d6880c906451600c0808815070403141c01507081e54880a070508101d81c00740e00d080c00105040361141c605550340740340c1881000100e00c0081c0044608404a40040c0300c00c0e603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 373141582 1250 373140332 373140347
    0xf0f090c050a1404050405040809090709031e05120a02010525020c1c060509101a090402010c021f080703060605130501270305010207020f011803022707020d0201061401 74
    0x50340f89418645003100d6001071541e8440c035405241c0152424007040140094079020309828401150003217440d4941201c00c44802c4010301002d40910090300300001700038039815407060780501c160281c40b600755106200110541081a0840141c1d44600400044503c0c08102042100c03031801100301200c0700010003540e8244081d402800740103002c007c5200200101e5981030f52940c0a04203101c43d02c1c003494403070b4a540c00020780300d50306800c2899203e81d24452001003400070b13501070940c1a065039190011148841c404100340d81200f6020800d4440340130104070032605482c82d8482c0003d50410840050443e981640240100541808001c10741580101d00000f159424600040200814202020321000d500f03100302c1600b0203620004200001900a000b103513000700c0d11000110000c1d801514101106115610380840d40c8000f40014908001804038014500070003144041d10240c070b46070b02c1282500d07402c02591004901d5460107909001d404046e00c2d4429496905003403980020f000740 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 373142832 1250 373141582 373141597
    0x60608070f051e0405130309050f0105031303030b0312091801030b0a0b061c230408070b0901020706050406150801020415080c16122703080a0309020306010f0f090c05 73
    0x600c0e862003e06800d200ba41c840c01681c001c010400c00150901d407011a02c0000300c104200c01040f040b0500244a2070009109114040c043e11007a11b160344480d12110340409a6801b20149130b940d4242810740d403030400c82d03079501d0b240c010f4030f1030341d240401b40810808100001909510000100041c0b0004603415081500031203400f0340811300643e46000aa01da02030403400c590a444401c440d056145495003210301e0300d020424a0305040b1440c19480c0e50402c2084038060840704007080250000303401054840d82c045100000107003440e080382e03240b074180d43c001e070340039201207854103034200303024600028400040c0481402145024501000700704401c002915000070310210500090680c00c0b810300700c0724035500d10b5454805240c000e14005080390690046180001d500d0a07001c801119503050440c41681820121211310340b56548042c0103900c1030010b5010540c54048580068408010340d901a0114046140d94a41802c0100c0500c200e15480034100c03606141100301400e42040484000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 373144082 1250 373142832 373142839
    0x110105280203060d02100f0905030703020114130308030a1a0103051015090b0d051b04030807060b0103020c060a0230060609210a060c02010207050c040203190e0a060608070f05 77
    0x10303a5100f10000d484c40b10810b00194004065080c0389201c1c0741c0c49144103520455a4584000e0103441d0b0040c1551044d541c04002d012034400d85c1c4100700414044081e012100814400c084c01d1626540c0d0750059400c156880400c3c19103444800d07908034880740744035020300d400780790802c00d9241c041100045605584520001c1010307800c0e01ea280c2500c601c541c08054400001e8103070742c4004590020004000c111035030110002206000b0191034010b80495040340e8008061508217006e940310312008150b00510641815420000c03205c1d18035051021610906c5001801a11403e446a19001c044202c244a0054560000c001540c0c0403500c4c0c4200e41052081d20110b841d03d05090108a030505091070502042005844610300a2000100c0c611800d11402040c49611f00600342a4280d004014000f03007140c01070080c080c218142540030f198007064118644c44004170f188409411980d559a101213107130899403a04080c088a801004010003a800080005503d04050742c2e0180940b809114803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 373145332 1250 373144082 373144087
    0x9050f0411060403081201030b01051504030305030c091309020f011809050901020c0723060304050d030b1f0521010f03030f02010b041d0d110703030c140601061101052802 75
    0x28692510000c1c3c034061035118a104d81e0768510349815000260382403000302e585a16450000c2540d0600110100340340c0b0310040103604082c11075600391182d0704010100e4851040600a01c0b5095481c0d1003040340d4400c540303100003100c00050051000c00e0700140c0d5a94184000440380400400f0804402000c56002c100c0006494446034429806481503205403402c2e032150300004500f00185503034180c403c1c1c100074801c0074205603541c14402d440c04116000351013900245003048806000b6001250a800001c0001e01038440c2204600745942a44141c000026000f056030300c90380c5004000490a0b207003141c0c00741c4440d890400c1c0c0c01c0c8100b03424000282000030041d20031044070300075040203007400c1d00244144140342410318503444004106130b00510b641303c0c4102c140c035014000c590303810740c450008010b0314005040d81c9040c2c1750603607503100845a61070b17094000c000c02d0b14244002c90203001c4564a250840142420203802d5842c05000c8078520210004280039004020150b9045123005010240c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 373146582 1250 373145332 373145363
    0x100306051b0301031209081203060405100f06051206030304080a0f03170c030403030507030e211201080f0d0e03070302130b10080610110a14160306020403020a09050f04 74
    0xd9103501c0c2000250180d0348084000320420005411035000001e2998a14604682c1c5078030f92030b66141022081610f4160802c0458520b04090704415809048002c41101a6640d44101010303013000d130744a900008c0c40031814900307103a410555690000c0b0124010f60805080107061038482c8281c04e4010700b10350510314a5010540145082c00ca07440150600c0a0b5600e040c12500249500868046001034036000c00900d44500a00c0740d09001560070000b0102038502000d003515031426120800c120355028004440300d00c10703207201c9034042d100850107804084c0402201a1905503609006000e2081615041e00da545000410304100c83d01103030001c800b40307254007983c0c00402020541c80e0b080008ad0392540f00c10b41c2c0040c8160300a11007540d000700031240728007040f01c4901d40c00e0885105600560000008142020440400d5104050a441c80440341e5130071080e28400700d50048072495000306080056103002d46060004000c541011300ca20f107000900084468801000140800031002c00c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 373147832 1250 373146582 373146601
    0x901090b121f09060306060e06040e0604060e12031008240a0c051606062414091801080705150f031b160b0109050a020903060705070501090c1511030310030605 70
    0x110700510304040100071340c0f600c1e4105003002d0451030044885810814010138002e051611401914420980140810381c072282d4401d400340461885008003881211050f00043d109040194012004200d0302d030606454951042d04010100c9041508510256091401c0041800702b03260f00c49603560000540c102c00c0d034029215402076500c04605424446107100c1003154039809407090b0303415030251002c084d0b0204100d20b50a5682c0111000240d4540e082441c1000410090449070302c00914010b05001500243c0009420903844980550b21003c000c212600301000005a01c07404c0d0401c3c0c0d4904941041d40410384d10015180c081c6090800c03580720381d040d012000391106040c580d41103c415400130304100c58550800e01403502d48915200110340c04403510300c201c0305140c902501500c0386a48901c004c0e203480d080154203903002c0d5203800c107110024800071414000340203014801004034010100c0140065980b07041c8412a40c410010f0002000c02c5401d034800301c0e039100001103659942d60380103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 373149082 1250 373147832 373147891
    0x9030d030b03120403030e03010b060f0a03090f0b0f1e040f0b04020a1a0c07050306070c0308090705061b0c1917100504030e01080f0c0f0a02210901090b12 68
    0x922840004c40c01101309580f110303001d5182c600880090200241c2c0d40304022943c821462491201042000101800c0c1d0203508011640d07809000e00740b881140c0d40d1113110340102e048a481c0154443d88017004101e480800c0c6003403a0264000e5441e515181039a40c0c50340300c40c0041c4010300140007003030029046540d8280220042c0040c681032140c203035030500301001503420211004445004050000c2a94100011841d00c900001d0b664030b02003800c1603c0a80303074014003400c00161402102d5000c1020740b51000101162180003e0703510806820310300060500120003a00c40c49801d5240c0c0411030181ba2030b80c09019103190440340f400c8905514192480c15054800b10002241444104403e0542005500b5410a02030703c0e203a18907035428081a00f048422030f1a484403140500c402d0120040d42c1000d4490024280100da40c03035904000b0903001c0d24080d4140c80300c141d800156241c100e5138000c0b101c0740240914681076082c003c0042d0080c035500c0300140b00303402841d8406a00c1103a859826070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 373150332 1250 373149082 373149103
    0x60705010b030109121101090b06090c0c070305060103030905061c2301120210080c0d0c0302042312010c0c02280b03070f110a1b2606060609030d030b03 67
    0x20003800c1341c20b03d000101501c844404c05c0104059100f403050100042c00382200255200007290303050764890080121079100a0007506110310709102c0551001010400c85000e50f00a80007842658914074000701802480c0c3c001c40e000f403005100c8034035105000e48524210900000c03001c0345003540301020741910a0120100c0c0744240c94000001885048403407031880c40c0307009451202ea41c2c100c0d540184c1c1c07500c0c802d803244440e2500c10044441d581510fa03010204503a040c1c0340261409a60325482e081c2c034014501c04215154203200784044901e08451200c070044041c1000340300344c489128002d07000c81750b04d010190046032761140c031206508203400480c04091403628104042c0d038450800070300d660411540000071482d11000150414060400c072009401c224000b0250040c031035485a2407102101c10b17002402c0c0d4a0f803000f09510460041104543c0b001c6210301c920980074541e030900e046406002680228804c004411b0342d0746003c100c6c468820041c4c00c010030315140550201e4070340f551204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 373151582 1250 373150332 373150339
    0x10e10151d0d1103160806070c1b0b19080603070501140f0403080c0d0311030703020a021e010b0a09090b0c0c03071505060315070801140102070f0b091c02030606060705010b 76
    0x200c0420426900c400100c3e00d03c00360119444c829002001610114007070250308a150310507400141074601c100e92892045110b84120041440303c0180f401e69071400303410030101e1a00103d06d010030985031681000d49852203180140440c10007401094440c8201d015140c10822030130b00d808074005d0120100c554251091000d140c2d1640d03241030500c52038000750079143d95806800d00309848581309014039440c10002981c842c0c5540c540d21000c0d40207600907260380e01135004200e100c3c2e0551951000910070480e44900203e000c041e00003c000d00f440303d80c0c000405c92840d15200c1404034510072405607102d40250319955036150042111861801000401845410650207003080c0034101e07049240110000e4046031200301344295500d002d08800c98180c0c0004902c3d1004101e1807441902030013190106006030350080307444d0101c00c111002c403038010700501c507400100b0540c81c1c10300c88044664000e0034550552070f1000e941c00aa00ea00000e00464881c180c0800c2c40c02c01d2100030340c001c062101004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 373152832 1250 373151582 373151599
    0x4080d090f05030c070f0e04020a05010c0218070234031101140d1e02160b061c0b01080706050a0504030204050703111207030608030a080105150918010e10151d 70
    0xd420301d681d80700305019a26a80051400010b003884404080074000c52740104070422850610f0011141030089602c01e80e840440500e1010341e000320300c80918000c000e9070b0301800d0300c14920700041f82c0c0448044910412400403c00c0660540714520000b42039990206241c402c40c814030004803100b418001e402c2440a000007034170f56009031590720100b408520400903403854020b00b455402240605840f00700c6105031440c082c0f0000f1070b94821b65030b00400c024517003130240c1c191801c1b50580392083c0500700c401d511850b005000b4000d04000840080c019481c01500d05003c1004c000d000b030041d480001d01841d101c102080c8450700075001a201800b076060b01546943c00a1000c3d0941103043d928a40840c0c5041c001142501d8081304513040303001107403104a072136441c10080c440c0710000180c030221485030502c500351f15990b854800110000000c0c031507501650604100781003906010300601900225804204848400404403149501140c2080d00c4001c04481000c006a03402d00f00b06075120090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 373154082 1250 373152832 373152847
    0x1302010c12030c090e0402030606130e07030302060f0a050405120310150f0e0103200d111c0e0303071713051f050f06060714100212090c040504080d090f0503 69
    0x35501540c52800d140c0da811149540c0e410303171543c0c0c00c0ba0a0342c0103501500400f00040c65410128003244442c1140ca4000503902c0700074a581341400344c0c50f001100103030046030a01000b1030205135100d8014101207401c0001d4200b640c0c0340750361004292607248050f034010002981018511803e00020301c072200c400403200354403000c01480d440c0c50a00410204503c41d2030007625520038030a01e1284507901c0224840042c45242011654111480306001c0c80c0d1120300c44100c10001801501c22001e81544a071440f10b07103140d0210a460100c2c0070442c8a03030062042210140d4040b4035241000344182844005484803411403549a90207034002e42544107107544c460702c90800c40004086c80001c10070800107922001c0320300101990a4070020303440002444404041564611114481400042220404080300c1e400070280d8000b55030b840b282e04070b54010041069020710280080c0842141d08104500c3c1036611200907009901150402c955501203003402c0011410710940e00603049011292216403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 373155332 1250 373154082 373154087
    0xf020c040614130b0f040b040204050a0f03020319030503060d1b0e090d050c0c0108060303070c03080d050622050601020703151506090e0105060915031e07050a081302010c12 76
    0x58030314041d001d00e4080c0da022407009841e00c02c2c064480720041c405005d02a01a08200107003080c0451203510507030030000000d0a598803842880185000480d6580851450042500b010b0409000e08000d182c40c0301c00f1000651b110040780c1d4030100840302680c8103c4541068100f070b150481c00382426400d81c000c003142d911101c144003803041d9040011164450600e8204640f94040e128004035541d21980c07201843d580100c0c41c59501c05005002c49007095840c1c0c861000400aa91060b140820002240038a40c0140c2c0150385c2d211030245c4250030007a50701030000c07250407a42c1d0381c40c62541e80c0c0ca2022078007aa200307010850055030441a00c050510114401c10002c0848042003103004004010014000d0302502016084440440c2403240580c40e00041c045650301510301ea580c0412103050b558100c009010245000b400355a1081c040c80d501074030240d840c41400f42450040c01010300001400d15881201154400c43c0420301c40202c0030244010b031a01201c2c9000100f4298290944080d05030303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 373156582 1250 373155332 373155359
    0x601120b0301240504180b1810020409060b03010518060604081609060e0c0304080315060a080f0a0513172505060c070804151106010803070209150a05010f020c0406 72
    0x3901040c00c0c3d00040d030b114200021107034541355960421340c080304640042107416042540c0810200910200c012020401d2410032080d41c889444180c0d011600b40101c07035541c400d00000d0305c3c0708241c0d40d00c1e550501000600c04e11941500706288042c880000e0341544490f415140109404000c0303900003001100003041d0264180195100640f03030900010b0081e44491803980140306106203a480d50300c0b02d403519002c41c1d0004012034503802e40103020060301c0e25075000230580004140e46050f100d080011020720510b0015003054091402d01080c409040004840500d420307030300600007070b80d10160f0758100c1050b024200281c004040111300d111030f0481600d446a0304184180c6c1550069a80c1c0c50f480c204502680401900c010401c0c00180050703052070b410380d40140f1346410320410550f50050184c3c9021826003007280c140d000400c00c0e8046040c40040303550059600120b041000340c00c03101062582041c0c2c41420304000c01d510760010702a00078401c8091100003c1c1c000d02c985074071000107075081ca = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 373157832 1250 373156582 373156631
    0x4020a031506032711060a03060f0905072c1e1f09090207030504030f11031002091003020910050f1b06010303081302010206150406090f060312050406080601120b0301 73
    0x1a0840c5403241c50803080822030b0b8660710003110b181e0304014501b400303010380010500c1001c0c166076401c0401c03441900d841d4103004040b00a070100d823a140c0308500500095103d154041c07001520300328000c0c0f21415098400d0401400c2c0c1d0103406d82c2c42080c102e0546003905084050f00a5507105482014109560380c020740b0401b181c03140c4409640c0d408404c03040344510f03034028001450501042c00051034441c1e250030110b01480e0a080000c52aa00103401e207070700ca400c0180c12560028100c0300604100101c05125103260408600b03110b04a00420085140d2501c540204080000c41440005255003078071200c107a010003003480400340780401552034000307000c180d001c20840b80002d05207680b44c0e1079191605506902908041c0c40b815502e80d40f000210540646c481c5e22600d012805060724441d83c090000c1c00c002c0070030401d103103003044200040416040c0c010440304100c181f1000b600443c040d40c0085c0c080c6407440040c280080040000c1640c0b1510690550803c031041404c1d00c071090680510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 373159082 1250 373157832 373157861
    0x3080703020405120a1208042112021c0e0a081902030c0d0203090310180605060609030a030206010e090f12090a0b04090b09060f010c060b1c0f0b0108010b090604020a03150603 77
    0x40360030000047e43c100c50121030060480c20459a80c0c3d29010707940500b01c0c41c0f000306080c86004148000c40310002c0c1e0b085040340c0802804080c0040c3c0d0601c41034000c1411600d03035107018203405041c03a180c03100c641c45000518240c0c0d84244030700c00d544510030003c0311442e050000940701d1003038400300029200e5012880d1b003031082c41404100141020705100d04941148600c21103051040c841da40c04002d410020aaa940040d09009006d05600d041c0042450a44a40c1c046c1c00035605160b00b806918101601075026540900250304000e08005481407110703003882000340d2a059408000b81c0725070321903002511020b00216000420354920303008560005d004459500c400d60751041840901d000312030301140007440042150000c1030440e0701c5000c10a201401482003200740a20000d0100307280c02c8210744c91b070b98414540086c00290f007201c5000d840e03540000c1c803008070f081000803201daa0203005144103603800204c1061182c0642e000c0e9286117003a21748121603660341ea10240080a081400002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 373160332 1250 373159082 373159103
    0x5060d0605060f12212a101e180201050301120f050102070b0601021b0907031e060605090102060a020a080708090a1b090b0909030708091c150c0c0f03080703020405120a 74
    0x400303c500030143c451514416006ca1498900f000200c40300307001d5943c1e10500c0780608041000ca01d1500d005150f07801c940c1244001c183e401c10000300c0f044078541d51a50a00c00104800000142e0340701c012281190111070407500100001d06040d42020716801d002480b641c030000760001000b804851703051041409809030790b44035440f5200c120104856200081c1e0100c1d641e4001030140e4020761106801004140020721264010f58080003100e600c0d400003004201c011419030815a0304009407030340226001c2080d81488d108010142c044880a403016090205c2840023803215541002501c40035608100581d480c0303510551449480b128601070584c0c0e480c01c0103044046030a2035010607001d4020000118503080c070b20b80b290300700742c1c1007848619440a14100034410180c22110480103143c081c3c66608403101e981c0c40001c0444207409035003801e0042e00300401c1d011601c404039121100d0740508010006039104c1c18210000e10458100780c0d0f00c510a014050012000090006092446001c00e9007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 373161582 1250 373160332 373160383
    0xa05070915020d050315060f0702030c1503010e150d11031c02120306030a0c08060f062707090906030804030507350c06031503010b0405060d0605060f12 67
    0x603005070005400d8016900c1981c42e000010310810045a111035242d040c00c15000420707000801990107540706035203a54000c9040410752030103101341c01c01d03004112008111013800c0c494071110b6001c14401c80800c40ca42c2c1000400011905c1036100441100401210b4017003e9490302e04850071064a0090191140c1500b40f400340300c10314140b884468103a0000c2c10000d06140010b1a00e038401000700340c00d03010b407192850001c0d213078500700b0f00646600740141419240c00341c0c90b01002c0030024a043d20542c000c0d80401c1b59400005200801a01c1407018170015036034206052303075040000d03409240e0041c80d160300027040c44440c3c0058426244240c00380e45003965604d00b50096a4010036007107103aa4580b4035203800000d8403446403500500403c00b528507030b054010018001c1d400403503515488226608075104940341c00c0c4500c078100f2608507010052400d0000100341c0001a1143c002c1607a41e558012421765595a41c4400d0456402890542140c040007152078440c0c010b003604e0545140780c111042c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 373162832 1250 373161582 373161599
    0x708070506010b090a0515190f020606060403021005030a0902151206060a1709010e100e160803160206070b041217010b1e160809030c04090f02040c020f01050a050709 73
    0x581c00313544c0c001d004401ca1070411081010f5881c3d110355020f400c40041000c1742100c0007444a0440b20701c0c003611490034542e1803460103420700100609103071107a1000c1106000590b219284512020051b01d819a12541c8010043e8011700b003420307010b58009200b4903e820701525010041044000182c0440c009850b0141800424003038401800c0c0420fa0020751203045d10001e407001a8445100c2e0008074281800017a11402c0428001203044081e4640e500385050020030010004442c00401c101c00700c141c85c090026490f4043c0c0c0401c9040d500b0340d540140c1c25940c07100306503a40c0c29040050031200741070600d00f244002d41c80c0b06c15207012801900702c6403800c07000c4411040c125001c000807980b0782020700003000e41411080c0c0f02c4d02010a8203002e1401003020914070740041030300c0780b088140da500e031017410107291488020317040d8070541c20201c50000007250308148402880c2c0c140c9020856407004e40c0d090341060360400720b095566180c1810003489070083e401042c02000755880b40b4032611703154880b6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 373164082 1250 373162832 373162837
    0xc070b0306030c040e1204090605010f020604051f20131710090c080a0506010906080102040807030f110d0305040302090114061206120a031101060e061c03020703080708070506010b 79
    0x58a90642082500d0800b5080980100c03892400c60750030788a1541d240900b545264107d80c101101459072840c09020550300002c0d01c4444401c6c43c0020701603131910b42d1380c2c55514055003c040c1c2c0700011140d40c91004180c0e5400000440040c2203c00c07806079000102e54980703400409040b03080d01903a0300c0000d1821038003044049903000c0c0c44042c045102400302c0000280c003200c88102c81450b0581c034002058042032090100c40751007140035042035490005d215013030311001e070488130560b40304101c03c01010790700044450489a000b0b186214105160400c00c540c1814001c0c03182c0c100c45100260340800d0350004c0100240c0784201d5580b000350343c807030500d00200445403509a4100384100b01310307840c800d285032005600c40801807006d10303a04410449039080524444e4124089400d41800600b808002c0c041e0700081c0c44104585c101514158000444034a000740c8001026031754408810141442448001c1c040c5400808265a803141860301c2c01c9035510422082e10580185400480d090704d14408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 373165332 1250 373164082 373164091
    0x3020c070b031306020a020a150b22020403060501170114060904060504020a030203030409020a1b12050c100903120c0201060614160618120c0b0f0901200c070b03 71
    0x186081070804a410903030b540040c1400c0c184015080c0600300289040c0020100110a0b0f40600001d40091900d0ba600d24500c02c0307000b42150504221140c0c0d030303c409640131220448003402055002002040100034490f6070400303440303c0d0601001150382e200d9015000c1070710f08004001c201800702c2c4900043d1080007074412590180030300c8041001b04540ea00601d8100d40001c2c04104070703035906d9002914503809584603407035664001c5080c40140d40c0042c7c0007900d00680d100d9040041d0525510304000d2000d5103c40741c2840750105e15003542642c00c10185103d044445401c0010700a1170074040c000345440300031661a5400c151000c00414418011041143d4450325020030003a0420308524658000c0004c0901c0010000c1068011030b096025807252121444064581c156080c1889925482703030810748428084001d160400141c0600a142ea200d0950000d00d02a606c41c0000c850141080b65004628103442e4464204082006001003203400c12110884000310381d1140c54007201d010494 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 373166582 1250 373165332 373165357
    0x607080708010e0c0d0f0b0109050409020f0409141b0909030c070303030c0c080403080405040509031e0714101a010c0f080906120c07110f060304060b0a05060418050105010302 77
    0x2401000f901d1030210455030000600310320a8104020000d090089900c100c50340e04645458102d0402196000240707040038020581d02406209240e40204070201c6124141c0f600441c0d075030040c0414043c0001d100030701c2c4800201501e00c10b0040e0381c003451101c030010790780714402c400c0f00b808120260300c00004c070740e030080c0001c001d02100c03481c54070140c00502a02842d01d00b40180b00b6094000204e61500920107503203d40713100b07230303e650400081c0411268000c0200510794401c01c03c0c0c101441001500741c000c611020007450b070343e9145281c8203403d004d40306c21b4030410348501c0c100091422415000a0341c019100704031a14240e40000c0115840540e402c400f8001e18510311103000803402c0c2500400204801512852038010f11071084c40c800402103503043d0000801061103000c11102d0040402000401ca60071511421880d00040d154840a00000e00c0c1541e40c0f803802410b500d07800c403014000c2c20010622a21903580f4041c40104110a1103c038030303103074a46000410198002e2003a84c001c11000c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 373167832 1250 373166582 373166597
    0x8150106170a020c03040b0d0f02070203101a06180f041b05070c1a0c0c0409031b0f050d0e1810150905130603020f04060b03070e04021b0d0206070807 66
    0x3a07140c140031000150200000c50340030012218009010002070000300400c5002c17071f80d6000c0c05c0c600340044442000c1c0304034506004200e0800942d400080007149035a00003000184104580c0d81e26440b01c40c030068154100401007130b016031001c40000c05032a50749040d21828694010181008101c034800d0442001d54503c1c00400e20380b1500c150083d05a55215034010306d44a51a6851203000c2203140d50195103030741c03001600b0341e03401109110010252006840500001c83c241d50041c1008050188070354418011020740c0c814800010104501030b508201075510400703510000401d803004100c2d0f014080c0b003880c04035031080e200c0700140d1841075060107004406030b428408160031281d480321580e003c2000450f00411140e6585640c03264404d40c5150004d2207902c0e610500c410390070003507100c510a6181c03003070400c500000034040326408016403400c13280d1003003054001802800f56011000b911400088c410410020002d04007c41c030010b17800f01c80b1683d403401c00c1101c3c003840c00c40340d4800140c0c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 373169082 1250 373167832 373167857
    0x20109140a1d041202010c0e040b130507110705010801030203120a0207031401020301091413020105031e09010204050123070b06010c060e060a0b0a060e1302070c0303020708150106 79
    0x200ca0100048840080581e1000c598501d14140c890110b904141102100c200a10040000010201c3d00c00c01241c0000d00c580041400090000e07002640d00b0790144d9100e22104041c2c1d504d01601c4840301200314030410050401c2d2000030941099084007176503d22660002007071542c01072500f0f40c1220382c01402030005280300e081032056a0800b00c0c61405510840c00c1c041700190b0000d000b640c032036a49400040c3c40e98540310850080d40c1e11078401d420151007a505200d0b104d45400d0580404940a080c0550303a900c40200b0441c020481c1480489014040703002d1000c000f0064004004445090361040c0203180f50406501100990040c80c0d1a0807104003c42790004014510050313110380d050410840c0040285c17188407d03103004004c49402508002c0030045035103490b120301780216600f969842c0c0032a09010001d44400c030b010308602e00c03401d200e81010300b46001c550100c40c0d83c3d5502c5040244425134900e0040d6513000980103041d001e01802414091703139414161602c1c102c44207a40d44ca0307440d100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 373170332 1250 373169082 373169099
    0x510120213180618020903070305030703030b01200a0609140d0c020411090d0f06020918060307062105180f0303070320120402030a200a0b07050622051006090b0409020109 75
    0x1b24a88868260040703010010124009001616040c2d0081c4c50101d03031002d940e000100703002414908489400d501c506843c4003030400141e140446035114000142001030b45c186102120302415001c1414481e0200720103600303a000c120800c610707100340c4092021200c40305601241d4040c2007645500608000010004100d0158404a038980207034070051528120704049518000d090b644400900b064005004581c14100f000c0401088030389080404c0380c401c0121a464040b4110700e100e01c11780c440010500702c3d9201d03410200fa20101c2421140c0e45c3c144000c441e43c40350003c031542008607180c00528500194184802c05124101615280c9440040b8444c034125500280c402e03600b5201d00c04e107100001e03030a000c0209041500c1c10b0410410005141085810051a0049030100c40309000d0800003400004020f508050070402c900344e00c0d0620745100090401415000d0720b940b05500d0403014205503540000250341c40380405106600114003407000b903981302d81001303000800b82d1070304100110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 373171582 1250 373170332 373170337
    0x5030604080a090902070309180c05031305121201061205060d031202070204050f01050406090b09150310110a030b040c020601090f090209040503180d0c051012021318061802 76
    0x80302e410706000260b142e070880302c00c0340c02c0b0440440c0401d10b050b100b800348446500d124210103540c0003092103018003420005019000107894a10700b100c21000c0c040800c4010700030f601c3d104980001068a94259002100e0700c180c0a100350008240000d842d0f0381040c2c0140038151152034090304110355210750359800c07034122034043c0060b001154203110036001a5590300a0300d00501c2c5185025895504101c100300c1220a20f41c44011614641010002aa1075820704c1561009442028502034040500428240f030710312100301c3c10740303440d010204260440c844094640c0c1140b517a03007000b08015000910080700c01d41380505015900c21801000903070055001406070032401000400e00900c580c3c00318203010800d03501150503400120b0059075241d51111004030548040742c0592250446455490440500c3d01400b400381c1407002403018054003a0b0300c7d140510f0f0001400b1545d4a0110240603583c1c07400340104108078200d0700d07410341210350038050034060343c0b000c0c0305050340079462640030b0f002507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 373172832 1250 373171582 373171597
    0x20108040309090e010c02011b2309150415050405061b010e010f020306030d080c030a0b180403021f0509072304060303090f0b040311012d180f0503060408 68
    0x2c0004200001c140c0205404135000100200c0c4880803e8800f03070175140c04404520354403184d201c03164186039105e01180d0481d0519203142c2610402d03a581d016262081d00b038416080358400d2000c0198140500051080b074001c012842601208542c049a242c880c61043c075500c413200b405000311006100b9913103120307050041d00018003c05c0080c8613030300f550340c905051080241d0103c00c002d01c42c20240500b540060311460081c03403600d4104141c42c101d0002034a260502503503001151100d44610282c4900c44401034030401880c0b8240c54000c1d900d0700d4111406281a1640c148540b0201a0303018980c06481c4403005410303400c1c144107010100440110381d03030b040f0500180f94261551154814000910300940d50152014180114900f1184c2280c5c071054900740100000c00220700c01841843c8130a5007481c042414245400c03500044e84100c40359034a0030582c1c0c907d154030b083e40103542414061105401c03045010340c0c51032105100700081c456180c051300101e0019000491040080900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 373174082 1250 373172832 373172837
    0xb0f030601080a091407030b010806071e09180507030e0a05060604090c05040f0209010807020a080d0902190806072607081b03090102280e090903040810050a140c070201080403 77
    0x101e0036505e0390100c02024a600d8003258001102c14402e100750030207070501411848004020904042e24001d0108007509280d110826180616428079886124400c0060180684a00903008241c82003c010030054809201280c640b8800c0440f0810128504600d550030002034009960b448080c800a005900d0044a1140d270030030300407465070744a1241490314030003c500180c58102900004d03081d50000780203002550304c81c03140301000500160480305044c441c0c4802107140131040c804281100d0200300d00c5042c443c459200401e18a20002d170103841800107981c1c05100e180582c82c85400341082c090200403072400c2708006030b211070140444a4000c105d000c80d0500c09203d0355811540f5420607039240743c0d240d40004800d01d6031190184041445500d48203000da1105d09550080c004450441149028450170400203560120070700070342d001800d29101399100301c600030300c44400400045400b144914602100ea002e0a1003d200c6203100e46401100c5528044c0b003074005664120000380708608 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 373175332 1250 373174082 373174091
    0xb01031a0f10170c0a0921080a0302040918031202090f0d0809030a050d0206060a0b0a030506060d06180f0603030804030e21060708010e0603030a030f020403120c0506010b0f030601080a 81
    0x10743c10b03014002e2050713091003005900c68103540c6000702146000c0e0b114a880c9410308400c1040b4009036444620041e620540499541103d81800c3d070181c061035108900d803d182004038804442d0140c0e01305580c1d40301b03a540d0200300c1c01000e50320781280542c0008c1600035803501d802d1903607820010100d0503100e000320351550030549000000b0345130400100e000c036910342100311002900e90b0100316003a0400d00c1181c2c001c2c00c55040c4080c860417401030410f05000c060321400851040d446510845181d0280c0b82403c1c0003190300c41c002100c0c0c044a00119000742c40c0307030000390805903c00e4414030050b00c6c5d0540e600082d680322a203080303070180300a081c1140d0000018011800b905c00030f41103450a00e2412000c3d00d41c0b8503243c0c04c040c16910341680032802840d00038003000119079001c011212440a1030600081040118401600034003030b580004154005604103602555042400c4014440c4078104503882683c8900b2842d106001d008142e1a80850500108109601030000c0940c018600400001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 373176582 1250 373175332 373175357
    0x306050615130611011107020f01090e07030209130b180c0d051e151f020f0115080d0e0109170109020312030a0f180b1b0301090b01031a0f10 62
    0x190310382c0c4200700c0c42c00c2d2144050010460f0581013031000642002240c000c020305162440a80c10502c56114000d102e60101d0341407100d940e0090300f210000e07160b0010340701d00c68900700300044c1c000e5208090140c40f822042280f243d1050b03a9001e50f58155401400000040000c80174643d4590f1000e08a440016014000d441c104880c5114191042c404a1046404003041480703002c442c43e00a80300700440091513500305440d4451410f50003240800d036210b0010481880c81c101d04102450082030055401d0040e0940e02144080e07000301554814010fa40300455201c00a8170942034100c1c1190200383d0000702042900ca0319041040e00100e182c0001c20400130603400203080c0340c1a408081e004005c04020b100e011070203441641b01c100904541080b12140b44d00d01d006070304100840042000034100f00003242c8021101d0b45002135280b442c220340c1c6958586800d00c0242c02c500d207841e070001c2d1400c1040300c18000c2d1280381406640c0003801461080d55160148451511180d0305541170000010445 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 373177832 1250 373176582 373176619
    0x1b0405030a260c16060c0c0e0910020d090302070602070e070507030903020d03080a0b06120609090307020910090510050d060c020f0a0609061a2101110a1710060903060506 75
    0xf05500162a000750440e80b201c010b09200d0124150810804c100c100c0c403080000a04d91196034080d20004044ca46080d95020b0b12a4039040350030b081c07415410300101c0c800b41440a1504402c0c80a8030030b2302074400850b103621080780e5030a06442203c008841002c04200b00f20b008400900c0d04c58000d02c1e00364402501e030740200301070029621040780003814004c10010056014458080c1c0004c041300c0891400070a4100d12400f4080a00305520803200e800200e585031100700120307590180d002d0a1440c4e40e03d0076550074010440c172485081e0640d0308181c0099500f240b60724a5000361031000b0040c07605041542c94100050042e00351040c20f600c03606056600840081010b050000c1c41800007141a10b564a00703001038403039001e089402c4d4001501c1c0409941d40b403003000c1c2c000110480712103c198000a480b14003600d40038180c02c501540000742c2d449c0c032651103c0d00d002072154030071074141d41c1c4d2600d2004004401d001e218010005040c580203000049407a0001604000020075110389625004c0d40c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 373179082 1250 373177832 373177837
    0x80903190903080c060a0c1b1506031a16230702042c0f030304020109180f050403110c0f150d020f03010b0703081302010815010203211b0405030a26 65
    0x4a0f00300341e010a04000310103045000340006400140340001c0d070823184c1c154040c403118604800420050400c041c842d070072400c590041c00150b4000354204c1405003000601d1406034025038501020304c041d0030140c40168000e40c0c980c4c0e2101c40e40c8100c00612825041c281d141a0004902240d106444003d4244490000c1d282c0301c40b4086541c40340e64011030781d034031030b1b900c1d00c005030704e4001c0d441d0070601c20030015030f822007000d40c00c40d60100344040d0344d40c002000c602c00914924140c0341500e8581005c0c0024076602c1a2000c0c4d01207510000c0758441c240e10360400030b1514409a01c1c9134010041040b0303c0008110001030081030340041c0015051840380112030f969900244c0150b00b00413070104a100c24150301030002070f04565000c0d0300d0003940c0c095800080c81c8000007850328808100001910f400c0b41d10070400c80f00801c4804600018003410804840c0103840c05680e2034140b012001c075441c44100021080302d08980000f0700a08848100d40da440c2848024a68003074042000c2000b1103251030ba19000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 373180332 1250 373179082 373179097
    0x4090b0708060a1d0a410105040911040c020705150904050c031006030207021c0303061a27030703050a060905061005010c031101060504090c090b0108090319090308 72
    0x8030004189408014040f60007110341c01606082888210b410b02c2c018000c04141d00700f080c0d4003010550380b9126007244600c010b40c883c4070240d4550090940c03502d511891980454003214414180303940d90380c03801c01c0f055807a020406080e88513a0444101c00d4a030950103950010b01500680745810380e03503000141d0403006407003070b40101c0800003464103051500d03120f000da000c0c0540703004030304500741209000b6242040d4028801810b5002901e4802c0d9030b034100c0d4a11107001c07054540540c07850503140c000d019190b1441021030741007460810303100b500380e9030041d1008131400203504180f0301e00c91041c01500602c03e0752159050300840a0210200320248100b980c0e460041101203036101039490030600e440c7d0010301c005180e0004031001e0009a0380301960460494051905030401621140702c60b006100a0748104e503c82e107000c00c08070810084500340c40403500e1a01c020811820766800540e03640200f200c81003800e0308100030340b15080305500ca03000c500351050702c1c000c44000d44aa6608415900100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 373181582 1250 373180332 373180337
    0x705040513200a0915081e0903040e27061620010c050c0d0306260106051009030303050a1109060a021221090c150a02030d02040906030c1d0604050604090b07 69
    0x3101404070070f5101700b540290401c41d28000f04039181c00550340600070b84200240040003003880c041040020108151409040151328000540c01c0604200d80189c0e110101c00c1c0704896824001010003a01180f060f128490701307541a55003c40035842198242d404054441c00c201142801e200c40d21000d100b101c45060f010f840b40c036966510303020344902d00236003240104105030a10300e041c050518600c11022640034400500c0c240e0522100c406400740000f41c211640021941498040290744031100c94202c9009450400280e122400d201c030035950600d030070240560041101000d14104640140218a028030646803000a01301c2a01d03a99401841c9a0480a00d2a242c103640301040104c034540000c0c09400400c445201e81d4049120710006441001c00c040780464a600344174002d004036121440d84000440d522034680391140c0061090380415152503102c281c012600c40711040d50440f0300c0101c43c034028031641d607030001c11000c5d0000500311508180c40301d0a520024a081c10031a010f0403458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 373182832 1250 373181582 373181597
    0xe0604080a0b0415020c072c0408130602011401050d020a03050a060203060a050321090d050604060207210203040e0a0b0d12110c0f0d05072403050705040513200a 71
    0x90803d68140d060713010a8020740c6104110b10740d41494002504812100340445480303100b5100c00c90fa4050003a1400904010304604c401c100400082100030300d4080d126070344140320152203841c00c908841a51032a4042100302c01d00500c50340c54601d08984100348010448103101d5160380e2002d0405010f40700481d009900031080c0040391030718100f0701014200079401002d10496846c9007100711f44000c14440200040021708602c1c0d9116840701024040e08181240c40d941400d1400d00c0003940019802d4603460142c8403440d144c501004020700080b1410313030088d42000d0901e200c00d030540c6070180552594540d175509541e00c513114003580c4044031b4002c08012084440ca10000340005100121000d03941c1c22499000910759551120380060640a85403810700c40c40910b4540c0c80e052507500003105080319040c03144400f51101e200d411201960350b41c18031050b11110415125030041c1c0c0111a4021040f450501d6145c03134903031155446000c03521004046021401c00302c0029840107000320300042c042c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 373184082 1250 373182832 373182841
    0x30f0b03070e0606040b0a08100e060f0d050c030d080a0f0606080a0c120f0b042f03190905030309011404020a0b1e0f070b131115070c060e011b030509010e0604080a0b 73
    0x400c0d009c07000a24282c840c518079450144005001204040c0b141031145003c540c002c000c1c42070030000038170144005012504469051034015000103811581d42c58941c1c02e0014200c903c000c54011310040f9070940c0c598201c5a20342010075405000e02543c4401001500184140410343d14007800480100301a03001035506e4226090005664590320b401c0d0f032100200801103c102800340d1403018480887e13890503201c0d03c803005030360715039051101d0102a0307a040144207000d10030040000d43c02400480001c00220212030030034184000f08481c06580b0003910807040104a000301e005040000d00c0c2d40103507240c6e0300d00d80da9041d41074024800141d41100007150400c10400c3d09540742e504464100040c1014820690360320710b6030f041140c40035002d0354995131410f560401c81001d8806c2281d00010040341300351030b942d00401004000f240b403400540070f0074501105006a0322540c055541542d5214607002860300103540f816880681640c1203202008005812403003802030542082c032615160805041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 373185332 1250 373184082 373184101
    0xb070305030a241e1a0d0b0414190905031b011e1e020301050607080c03160807061103130b06030f07140a06050c03070615080a0b010501030f0b03070e0606040b0a08 72
    0x903004d07000c4150540c81c07081440300441209000146100c0000f2542e642d400c1c0c02c0090014140007450306402504140c8049494902000e0061246c0f9000100d0303080d05411481075000d9400b01c180142854200300003d00c00e280c3c0050200c01481500400851440c1c001e14242000807034030b101a6000319500c1004405001d107101d820f94407521030540960940d41810001119842000b200070b059210000d07004925070305c14010b071101700c0350260065100103503078206034000f030f8040ba404440303907403500c2001040e00b400282039034040c0c1e8020556195456565890002054010b404164944100b0021980810003040000054040c01303507446804040c010511070b848000342c00c04c5007480f0060146010b607420000c01d940105800c1840400d08400e803844000110030342e81c200d80494041c2e0742e074502c20b02004107855030484001f0b030780401010700611240000c82e051a810301d0361580004000b00100715400c002c3d240c000303070300505281c5010394a90b000321283d4850401c010100d28207904101d251038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 373186582 1250 373185332 373185359
    0x324092a060903170a0e030a0302010209030d17060906150d0608190b04030e01030b06070b0f07030b0609040218120f070e10060f02070305250801060b070305030a24 72
    0x1080c1050500c05007903940c1c50090007103141484d034046002003840e510700b600c1034400314000390018090311161000307401e00034040c0d030100003014001e2240b401c100413614824415813801a00e01c8681612a4079a5000c1207aa59009040d40394031403a480c1003020144c400c1c00041404040e80d10300090824580348540c3e007448001c100580c0c0340801d001c007040c080b0702d0080d946584070394149007840c00d00300050016001046c52016142d00321a02241e010200100e4200c030307074050949201d2031245640d50300c904609031012040c5d056000b40d01880548024103068002d80000500003414003020545640410030000840d9041e1119a10500c82e1220070002480100c014000c0300190301741520f0801180303080440580f00e50000c20045007034010501d8424003641c1e0155a10405032281411803540030b404034501e041402c090080402000194100144603142c110780040b10914208503454400744c0d0341b50401052540100d443e40b1007440d0b0302160507410344400701030705207851403a81401e00130761880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 373187832 1250 373186582 373186589
    0x90c0f0902120a051302060310080307030c05010e070602120c032229041403030c07080105090705041a04020a090e161d0102060c0c01140907090c090324092a 69
    0x10f030f140c01c0501a0f000075141601000b130740c056810568a40710300c03110318075106656200c00301c14040450300d541016482521b0441040c0580d0003400203180384a43c66844d40030f103114050240c1d00c04000c103116103001d00041c0079207014076030550f1700b401c1024904203580386244d4483c900300c00002c170051046076181d40912459014081c6160b055240c85a1580400e01c61401038801203e201c1031503440e5030f60100121003081d0080d40540e000780e65a0030015001c0d00c029145c00001d40a07820b004512400d141c03203016003d040710580460072208460a000083d404403107900c0c1040200d10002ca0b0070310116061a008401594450154241c0c0201c0200808035040b8520f0481c1c4100c0b070394084503a4001069a08900072041c6140d440b00e511000741d00420241d40b50804000c2d8038410071076034000202d42d6204035444681c007400010a590011078108115010082410030204448c140da60340b0012050302c0c80c00307245800281c1c46a243c40d400c62441500000b001e1128030007041c1c465250034251080000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 373189082 1250 373187832 373187851
    0x100c050414040203060621070806010c210e0a0f0608061e13020c0f0c0f0301020c030a0c0201020114090102093f070e010608010e01150c0204090c0f090212 68
    0x101824081c0d0780c030801180a0146110799008000b007900b503501d84040310003c0c80b104500c4080d49041c450441c2042e0811115000072582600c002003031035015081c0840481d610450540c0500b803018500c80351100855215410030070b4840b2004440c5d250752051102038000c815880703079068a000c20081882000074000307805001c540c2c00345c00c80001034810b02e255900045900d015659010b070b0042c0028090700c9031401040c071429038042c030221030104802c05500e400f6181c031001c00801c681898240d104955140c8401d9000300b100b4841103104000d44a00c0e58414130020520480d910301d05100008241c4624420f07035030000349a2118507203c0840705107059640b901c500100c40d03410071721080c0208450303611144070199802110701481032040c5000350600d14610a21075071070345401428120240642007000181000120307500c8a442d02c0c031200c40009030340d155030382550f0b5424000540b0b0b40c02821a49611000ea0104806c80201d848001405113403400588408142c04002030810018060160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 373190332 1250 373189082 373189087
    0x219050a0303170907121115040b181002030a11121305040b01030e0309010c03110a0b0702060f0105030604020f0d12110d09050d0204050415020307180501031a130209090108100c05 79
    0x40b445c0442c06c5902e981c101e1250b92043c035004010135100150f203401d049100e90b00050200ea0104910041c10059014102140500b0341030018031995000c1d00c5a0040503a20038002c101c035080c415413810303105c0b24405c4140c801110302200c3c40349598014200301248002c80382c0052205050600c1010707135000302403809114030301030104007075102d2040c481e50034100000301c6d03004401d06002d0324000c40d50001043c12510401c045013821072245c0c0059900c800107014860100e035000d80400046410380d0070050182203a600e80c0e500b00020110200015901b004038406200003154010407241d92040b0642c0307400c120010655207403410050f84940c4081440b84003041449039860340c400384983c1c1c55068800140d69141d9040000040184003e80d0103051300000400500551010b0303801e4034420104032100e070107604d840054023a0ba00013500c8070481810281c5140c02c0780383c1804030360b00b6242205401868440003102103149401c00340c104400c29404150452240e001c94480c0c0070348041180f400e10f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 373191582 1250 373190332 373190339
    0xf030e01170708041e0503040e060301182001141201081207032a120203040501170106120b191202090907060f0e030319120507020105060d0219050a0303170907 70
    0x5010f0303540500080c02c910701d403461000c0d85095258000d40110b070401c4c201ca4542c0d9450b0f44640c40c1c032204032003541c000c1d400d204014002100329280c04090310f0784810510a440b0314620040c0424030402806410803811034507603500402c2c0b2400602c210254080d41f1030701d56040c030184915001621400707004000b0104441400300e980240d20340017034401c8030050400407880310343c01d00000d030741c28002a10f142d0308071004400d199000002001111000e0b02d5561460344d0b800503205202400340714620102d504240d00402102d0a540202c644c1d00d4020116201340d660240c001c42d0303400b856088002800e0099a0350800d524010082d541c3c010407010003009000d04241c401080c0c00004d42d40c0c0740a1001d4070215046ca581c2c11f0007941c0002c14020f5201d4605a1008001440301c40d83c0d0340b00c907204a103003001080341d003803060040300d1040e40003808400d20b403000c80d0b00744440440080100300038048d030300d00d01203055038880d101070004600075550b00c1c8101c001c0201001c030030345001d410007000d50321a81041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 373192832 1250 373191582 373191587
    0x17060405150c090405190608070603050106090506090108060d06050901060302011805280e0a0606120504030801050d0204140c0a110105060a051513030819021f180f030e011707 77
    0x43e001c034101034801041c40c1d121518004a03410010224111060902d800410303c0000041c8502c00c8800581e02480143d031398107001c0d0381c41c0340c0b98080ca40c0c001104016040c025401005d2031f07904000050200034030030303480e91618021a0b0040e0350308501a5161141003007950b0740a440c080e190302c0440b107c030448601d00000503100d120451031130b41c115820001031240308002c1d245018003d0404845820140c42c119a00200a0582d406103802050811614441190640c440c05203c4d40d4161151003599092a0401141102c200c80c1268000d4440040c04240101e07940402c0c0540c40c80322203117440303118900029015810b1000411303003580c540020495a40e459a6131141141e6068500b40d4a0702c413003001b080e03d9481a43d80c854641d100392440003042020741002407000149151064807540c960600407610b0303140d071064071414041d11460240c181c0c0c8130f6070302000540407005960400d0804540c1c031440b880d5841d000c140c0203c2d003140701107480e42d600040f1210006446035a1000c03545401da802 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 373194082 1250 373192832 373192837
    0xa06020d1d03030a080c070b0406050712020a0e24040806060111060405060a050a0b100c020a090c0c06230408040e0f0906070c0c050607051b120a06020d0617060405150c 74
    0x16502000361500101b040d07100e0f46c8085507007854102018a845103841d06014010b00300a598000015002402c0b0085c0041e4610a0302ca40d548560b58072248890390750108680f000c041008214010240720010342c00c068814028030081c402100a021a458020700150000300100035020a17900321404002c00204041500c40e0300c90f00c88440001c1c50f07110340f08190000c0100031150b640240c900003585401e29004002c4c1c80703000e803080b55113158154540c807848040d00d0310450020f000c14400c0c444400000c01d250003d0166401e00c0c3c0d900005841d4004c0902508002a02d086d60180000101403005410781510b4643c045859a5080468104020391547c0c0d040018088010811407a034182c080013440001440104001040f042d203079076440c100380d501e40407180c0244010303003a440f0b240e000c3c50074032950521090003d403020380354030301040c1c1f140f1000c2d511124078a02e426540e50804240c8400c1500725280464080c1c0050245140910b0451700c0c19004200c4a003104924000308083c0320090003c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 373195332 1250 373194082 373194097
    0xa03061e06020604031202130e0a05060118121403040e09160302060a0305150603150a08070f1a120109021803120409020f04080307030206040210080106020706050313020a06020d1d0303 81
    0x2882006d15803101c2800c402402604019070b001d403107000001a2002218181d030307000d080c11602c200056101c800054030300c64400300c0c8000c001c0c440c0b8041085003540c1d003008890720901603e0341510721a0102d4070725082d540b141e04400140c1e0344c00c5c018055020410888cc40e010128001d94a545904540015045004505440701010b885100182180100b501c030b54440c0c0030064000c1e52130707084c50138041c0b1066044405240c000d8000c0ca5002a040100040d0101240d040c03a26106105041c0040d284000c000112003088010007000f010724210a1401c1c1e840c000d086c24180181c884a107084104028081c010145101c0d610900503040c125802c2c100712000c5400001c0010380d80c0fa01100348072954083d5034455010750201050841c24180c010915910561003120303c0001080720120565001e003081c015540140c7c40f030b0301c050140e20f00032401103420400e290181c80360000194006015400a604881e0068201300e80b0708070101d03082a1003d040502c0101c610802c0301c03c0c0404a42c1c2d81c055a0f4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 373196582 1250 373195332 373195337
    0x3070203190c051c030e060f0708041a07020627120d060308030c09040b06040315090606031b0e0a0902010e090c0702190305070501051603080702030f0a03061e0602060403 75
    0x3040c1e10a06000c1c1d00c102081c0d5600c1070949040c1c08141c0d1150124640c18041c08001c40e041403903c0f50103050200303c3e0752046101024030b0104d43c494100454441c10000c00c11100501c031110980000e180e950000c03442294554000c140e01d00e4440c4400301c10303213420001048180003c4c44250160800412024112000c00d00034035200e00d661501580500f0081c0e1000d020690000140414018a40d00800240f001514244400072245085c80001e2299200181c9024400500e00f600120306400044500d0300545000c68540e4036070712801c1410b40f480b6030100311650f14800802c00c2e8907500046070341c4000140d0042205503c140c00203054107040c6c0103091721485407040019114600c08055440d0183c000d00240b8860098880891416900e8082030b1101d20030b00400080f00d40c4194100c2e20b0312003e03ea0a48040d2111ba0b43c20303035400c84060301d80e0040d4002400401b2807101024040c2ca92051503a40115001d80f401e103941e5040518482621910040718400b40102c603000215260001d6052 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 373197832 1250 373196582 373196617
    0x40e062206031109133207030512040305061503010b0a080a050607020f0c13021e180306010f0312020109050105070e04060b0f04060f0311180102010c09030b01060c03020a020904210503070203 84
    0x3424410000006d10a80f180c1030b1040c0644141d0425000030103c081e42d100c0c00c02c45005104401c0102620b0040d444028041d6010a000a10342060102c0003490500058000b140143c00302000520120842d0042c4485510502d0010240901080039075001000c0e8005016804501140b840e2183c0380d005066000744004c500349203040000c1c1e030481346211200c0c0f6540c0300345030710300c4130070111544400c949402d0724107134440d0704125190115205040320b41208415000d689165105c4094040411045081d0755803600c0d0a00458000c2c051180318801aa07246c00c2e00d0b803044820001260309940104540c100140302c1d1414402030340c012101500c40e00e003407041520302d0080089019080300086036005010104050001c0c440c05c0030001c1250b03909800074407010009800c111041c00c1c46100c060400c40e85400100141030150080d0441c0600070304c19500d03002c0554000c42e45009081d1001c03110550038001c00902a541c18880181c0c90311203251071072540c100940c00075030368062a11a00b9102c8001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 373199082 1250 373197832 373197863
    0x50309010c030c0606060504080709050c03010923100819112809091205031614040902040f140108240f030105041203050901060506040e06220603110913 67
    0x80d181d41d80b5a540c8804c0510a0580715100100150414400c1c10900e104011022910385102e025a43c480c240041480c1e0440c5c1c41c040c90003003d0000701c5111803450305400940d1008080c51914288148800c601c1550110f240400311031400c40800c80104c400708821500000203042c044c40200351038821220f5a05650300303c203080e440c05074002221001c285c2100030010b0900c15076006008041e025411401c02d842d24403005480750300c011944e60382c54100740d4092014080c01041c040000c04101d1507500e0070b203030300c3c0d2000300101d03809030304108070311400c00b0403c2100394000c00d42c01410360428031b00012581440d104409144401c070700c580505074900302d800202c075150f890054031800d5009000b80b01a04060a145615000003a04500001d041400103060071505000e600104c0300b0244c5640d01e4a80380c60310250901401403c4954040c150b100d015950340a10029030300740c0030504600082103442c525000300006074400055005500031000c100e04040c84403070310500c50f900140412001c404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 373200332 1250 373199082 373199087
    0x1003020c0a1b050319020a090b010e10090b2b0213120501110f0d0605010e01021f020c0102070b0709060c0209010909051e01060608061e010c1a040b1909050309010c03 73
    0x60f500144d42501c602c1403030501a94000500100071030003610405010740d111a02d220507190940d00890120780840c41d11045800c0c40810f00880c45594608580c0c0d454440366680e6035039110103440c0c078940710800160b405403659206400c9607114500c008529004100c81a05c00880d040e100707010307907010801382c06003e0110070340100030382ca84800800e540d0f401684510207003640000009030291442c042c00490254041d1548800b0584140c004012924086828120409a170541170707840310340920a0b03401081c000d0015060382c82c400c2804d41e41c0c03843c00304e0b4024614525030b4000c1c010080340740100d1026844503000355054902c48040841c648219003003a61804c00e608170000c0540d440c07141c034942c0c0210190700c0070342034580690b1101038546844d01000101101221446007000d0701075100c0401c0d43c001d1912802561154030420803000030b054208880ca1022141a2281000300b001c00802c65950007a210036504809400c000248664548a50381c0c000c84004905015949001005160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 373201438 1106 373200332 373200383
    0x7060c1103031f050a0b030415020f070f0503090d05010e010b0d081206120d0e100314060f040603050604080c2802010c03030f0203090c1003020c0a 65
    0x440d110b008141c0003c41c0d000456041030998800504da4607a2103d940041a0b0300e000c3daa140c2c80c080c00c05146110717407010300107007143c030400c010002c003c1ca00080da4940c0d0b82280350125014810728009186101d0944c2e05940b00f0101c500a0040204c1508440701c004140300090020135a844180580380c41c140000a189041c1817081140140c1000806544604010107105104201280445c20016402d602c1d1000a0602e003031124a0700b00020b003075010000b189010441c8051000c07422032140c40180c4800d21031254030711515200d5946400c13040103150001c0580d641420145042c4120360720045600d600f03070041e41401103c0c80000d4641906034100c100c40b04062890b139038011990540081c00031400d041e03407404400306450b403034800781d407041003100c0c01408001c185a0410811201075064a005c2600402050620180202c0c10f82e9103a6809548940c0c00c44907031603603030a180e = true := by decide +kernel

theorem cover : BRFrame.Cov 373021582 373201438 := by
  have h0 := BRFrame.cov_init 373021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 373021582 ≤ n) (h2 : n < 373201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
