-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3834
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:04.130172+00:00
-- url     : https://prove2.me/submissions/68cd2934-5b3e-4dce-ac67-f3700e4bdbeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 689388489 ≤ n < 689568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 689389739 1250 689388489 689388559
    0x91504020d0c0f02060412030b0f0d08090a0b180603071806020d02010b09040c06080618010b041502011a090c0906030f090c01110d080712021b0606010c030509 70
    0x9003940c00c030200d03040042c200e4020384503442040e022400c1aa1a400f0490300200f035443e01c038052960341c0d8003d074007442800001421043d0b60750313420408600c092900800c1503400650110f943c0b905032030043c114070301404148481c1c50601d00d404003d05041d030301c20078405100d894003000040c0614420980c40c8025000640740b4146140c0e5004065211039001c00654015400c01d010010b0710300f04410440c0c042e0340c1c020b404d03041306864080102c0f01c034140580b51950001411100f42825128109681d001e1b25189202550301d5282111954540c0800c0e500031342035906000001d18900840351815510721416a80711046959007060b144887c0b10740c600f41c41e44404048140442030011001d52842041c010007119211110800192031004041290100707551000c11491415803158039003d810110a050102a1894105552099800c0301500c1d405480038110a100181400c000c1da0350012400c0c02e103401100845d49008200e80704121202d4040e0284960703412080101000003040a11201c0f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 689390989 1250 689389739 689389747
    0x70305070e04150e3103021c020616110d0f110a0302011d0304030206040b07060b0d11030616021b030304120b0411060a0e0f0d05120705100b06040509150402 69
    0xc58240a1021301034041c00109a0001030508051401d1154280405404a964440c01d20050502001c42141c044007180030780c400000030b0400b6500c00481d01b042680282200d8078050040d92031506505000800304400e0b4030303084030031a5003c6009480040140b0700700c16075a06030182618034800038030a140b254414540d0060502d5419409810200c11f00c0005089807003031001c0540e0360340590300005e58030000410080101e101c103400100300740303885a4008500d92000301c000601d0009840c40c103494254403820714644910f400c2c4170360380d070111406950700401c8600030350081d941e050080c140c040601c0400c0c09149141e4042090790010240741611701803844084c0f034440040c040589007180d0b10b5000381c18a4141d880e0190550351014016500c00851361010010010112100c1020036005000303149201c0200c0c000744445406a10107000d8030780d42d0b400a180140c5803030018051500881d2814280340016030311030041b902103500c00c0703030684219141c1d4030810444004150300d0980c054400a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 689392239 1250 689390989 689391011
    0xc021606020f2a1c0203060c04090c0305010f1203020a05100c1814064e01050d020405040320010c030b09190519140906060a0608070305070e04 63
    0xa02c4030610841d40c080e00c050605211503c282c1c0310121400c180102250030344054542800da103003ca204454a0a008941000e600413a0401c0b005580510101c0d20010701440304d28884c5c01410401e600a1804000c0c80d0f1402e03503000d0007509680107100c0040c4216a4110501d0710070012003c041345c2103c00d4500900301c10054000500001c190f0700082403010848004903910f0701c403a001207802d20020040d03411001010046c00c0e50102ca500d034014020380c1401004803440302490101c14240c001ca01218840d84891045141c0301c014900205594000050110351a4003d1080105505560106440d20f030340c58142c03042000d050a8400c044d107900304440b460141504500c0c41170400b078500700301000003a002e10540310401ca912030504018003d03102c10030360f9589ccc0305551005a1160780b1f403848000d640218144c0d8518403007000e4841d41001484542030061000070340240e001c40e8015a100c0c03900c0b50107082014001c2c406400d040ea10000680046d020303441c2e994034500014400c000d454011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 689393489 1250 689392239 689392243
    0x11103041203090e01211e0303141005031207050129180106050a0c050304120b010e0c21250309050f060601091406040e090d02060a0207020f040c02160602 68
    0x400140d0025462000005510f11284d005034160b4204021040c0c1000c06032903000e840f1707082c4400844407040c20b0007940c0b8030403c000c0030b0032400a100799000b00f200080502d030244240806840f0807a0717103142c40e1042006550015110740401400080f2a803a2180ca04001d401000707200c0f00001d13000fa01c20309820407040640120b40c4030250444d40b10004c007210f01101803041201740110401301c0c4040208004e400d028140103c900f91083e01103d14250b01c40c103a01c4080480e440f003c0f2540f948100c01804401c501e070400a920400d40c1c01c009080101c3d003071140d20140d814041911052040c000402c40006410180c1e45010301010300c40c02846881000040041c455544143c5031401001d802c88001000801d20074081d000503541c01070b40500304000305496030a903005840d44442d0801c00024042a541c44280c817442d8000040c4c141540508800380c20f0003001081e8103403e034810000180141d60f51081f0000e944001e441c00204000311480c00d80c503080d481146007146040310352002400030340c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 689394739 1250 689393489 689393519
    0x30d030f060e13031101091a10180b1509031e0106240305071815020102160f1203060b04140d021201020a110f0a03050c19060606090e0603060109050601110304 70
    0x802c2d80c4071007009417480109400c80d40444c1c801030002d00da0b8000040040e2088002540200700d0444000740a69910a0b0f10200341440e00201c4525441d020078400c189011040c0f80000c107588160342d46800940070003c0e480d950b41544000a46001201d95100d09000750300c0f41000e880490300d5040c805031072425460502e0340300b0660a000030705001c0010b440c94400c500c2d01200c01c440c646610440ea0900503d00340c0c07007915a0400d02190b41c02c5c481d10041c140110f402c05d405a002e000c10648804080c107081d511509041560300915080030010071000f140724048030100c6441e14980b40d08180b0340d42c009540c003082da45c000fa50040c4481d0110406032019070080440419075100e80d03280f43c1100781030076182d5a85548000007500500100404030380030340d0080543ea203800301914550070099801c480217807440318058444c6940d9002c1800f2090b0090026405402c0c1e40c6901c006500d000c0000a0f07030b0741c0c814002e07000b66940701d8002c180d06901418000209a03003900c240ca0321907031113201c44220340310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 689395989 1250 689394739 689394743
    0xa06050108010605040f1b031d01150305070e090307030e0112091407060e010c02060d0608030f0408070f150c020103200d0c0311070f031412090f0705030d030f060e13 73
    0x8544046c95041038000d1060b2061200004803103841442041300c10360091121350602c00b402003c140602c2884802813160713441d03101c94240200b007980e08508103645054025008004610003160620685400002c00d0750445a41860002c803488034500c012122800c40f40b19503044603007800070b0b04081005407504800c01c0106003089400161703031850100c2d122502c0788080d42c00b01d1803250503c0701608148004140c420081c080c04a80c00e3796500c4203e11b07550103c0344c003c510310700100b800d10080005003d103400078084001c24000e801d01700043c11001449041140042c42546c1c119035045901907002801d205040e405140c140c6103540044030300715070011840007400e515000d45403079054003d205a040859039106568103014032a503c150b4406401c0c10250b06011a8107505003c52803440300401c1303180c40030250b205007820041c4140e0714020541416003000e401400090186850014558101e211a03240100d6030b8034800b00c0d47c40040404c2d801100c07c0007a0141040380c21500e040221070254 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 689397239 1250 689395989 689395991
    0x414160e1614040501120b0603011e06031a060705070e0901060e0c04030308040b07050f0703123c0b030109050c031509120c031207091d09070608090a0605010801060504 74
    0x101044004440a0300ba4400c1e200c0d0542e4180824010b551107a40c41141c0c00180701000141c101c04140080c4198000360701000040e0b40110300581150651004c04005004a09007485501c0200580a11180d034002003d030280300d0202d45401400402c104480090040310003c89260070143e04107800717804103025031244501c06101107545000000d085600b1250144e50b14515501d50b6620820a81d0014080344c04000d000d00441820f07041c020020440700740b1946070840310110081030304041d600320210551023000c20f41440d500540c01701c20720315408a080144541e002d0700c5050b0311401000140005501980782a20144c1040000549da0004120407003ca415100800c2d800714400101103440d00d02981001c038440200802001c054a030880c0c88000307990401b0301107a203080f0000c2c0704903070150000310300301c2e07040080c1480a050070844d60081e10384240c841c40c044004999030b030390602c03c181c10801144001240103100344501c2e6840c41e440b080a200d0345d40c0d100101030103001a40102481a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 689398489 1250 689397239 689397271
    0x501030c020c03031e040e0c0310240f090807120b1f1208070b091e01020906030f06120f01020c0d050c0604170c0304030309090b06090102060414160e 66
    0x1d00000d8281e05031003005005520b01200301400400c411045c0c145128041014800840d003100769140c514411b003850146280c8078540100042c41d42c0d80d240e030041181c540c0c950700d14402c0e41316013894030005103024100190381141c0444203c44407021a40720407484c2c090107101160340da14a0000b105101d002d503103a51003503203598100203038513100d201e81d8031100103200004200d001600e010025955001d546400c0c1007101d10f440d1f078951074504a82140107a0040342e0290046102130000c9011400048021070a001e1418082205880701a011450601001000500c03036582c0c0c80d415640e182e01041500c800103407040602c1d010b5084011102c58602951010f2804c0714890b00075100120700480c010000742e100c5844684100e250940c1400c0841c008002c07041c040001080200000c4d84260380d81c54220346003c28100444580e5201a4800d04080000c10900c0c1c0e400240580c021790040744c456110740c00309000710318188a0015800318a503804800040c195201803603030740300d0320b4550400c00e05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 689399739 1250 689398489 689398511
    0x31d0a150b0a0f1a0d1107021e0f0f040e0f0f06090604150213080102161b030c030b1509041a09010c0f11010b030102030a050601201b060904050709050103 68
    0x2081c60244001c0d40d03e603000c04005000400d4264080c4c2c010500c483d42c60000b081c5000006d454100500141c0d046001503d03404505004070148242041d4141c030014046203d400a540c44840350070b104d118110140e2040b1455840c0d074002c02070390b41e915003210742900303c42c90400d0316401c03103a036882d14034022140010103c90010445d01d20440c2d0000c1700121000300114180300a400c058038501805d92024001f00e00d5080034070040a4030301190b081f12201a1061038044401d5800144414284103c2042080020341201148040e01e074030a400207110fa071103030307828400018448242070340310030f460080c84240030540300300300050380c1214821440c50b03581207002d600361070fa240c414500050540d0a0b910006208407a51042200000008078a5211680000382a60000c0e100074500c0c031b5464050105544e04000c201e0140150a210800660b12086c0c00c0c0c0d0302c51111803c00109814042d410b141556517200449800240086c0100298105148000e10207005070003518046843e11b440244 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 689400989 1250 689399739 689399749
    0x30a06150206060d030c030e0901180e01020c03040314030f0f040e0a18021504090603060614010c031205180a1a090c0a050f0105190302030a06050109060807031d0a150b 74
    0x1c800c84004d0030f1070004500940c0c04540301102d03c00242c04111005207902650395510944500801d45120044541c0000707460303105c2240d0020081410f0382c0e1040040526116012042d2030071a034202010389910142d00c10400e04500c20380305030b0303035400d10001004408801d41c60040d1041e221401215080d56803078500c018100d1b42c1c081a00800d41c8481c3e12801c005280c40840503400c0e1031000420703403d0956030103c003420358495410440b05d650329070109028002030540c84980b522824a00003034481d460f920090201c1540d03002c1c5480591301c890014007070691180c0034084040a0104403081040f007801c0811031a96480007946151440d070010908220000408580c43c1a004051a02d0a4074050800c00f030070004030300079030500006101420041703242030642e070240d10300b43c0c07805688d03403074a00c0d00c07101103e00703681046041c069041400d000a81d800100680c0c082a64180041d21400e40781804403200e10910410209218043c112410069121040190411092018840743c1c16800801c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 689402239 1250 689400989 689400991
    0x30602120c0a050d05061f020c1e0901060f05090a0b09010207050406050f09130605011d090303160c060b030f070e0108060f160c0f030f021b090c0d0f02030a06150206 73
    0x3000640b0038440001d90b14140c1e4417254203e94000e01c90030380b10214620403c070760003000039141d000d80c00c011070030041c906000110006031901c802400c800305140400041c40910103000d41810007000c40c4003407545d0760160781214080d1100030488003080d41e4812030940c056104031017890044c000d003a400501800e20340951800e641009011030740010301407041c09161100102040103d0a41010040c0401c000740f2950340685114106400d11584a080c0192003d1024086c8040e962042080040220800030042c001c401d482c40c0020060b8a20309019001e00700b0111016410f00400034210200380d03000515208451440c004102c1e140c0c1c1e16000c1c1510342208071080c0244045000014030706044d9125540350020144c05c4c03d000f240a191520504207411500440105100d461081c6001e03404011012401000e00c0305001c08950030004200d1108014044030050000810141c00300070854000103039030941391400310f4a901d00f408000d8082c04140c0314241040a030b51140d42d00203880802e0b02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 689403489 1250 689402239 689402257
    0x10b04050705090f0105041a030f0c0304020109060305090c09010b04050a061403040b06060c030c01020304020f09060f12010e01021606060b0a050412020a082b0e01020a0b090f07030602120c 83
    0x41c20701500301c044c0010050110321590412408100115164903110084c8501d51100c0032030a40760f01e8401c080c14402039003e0b00c0700f20f01031024010070005030307448540b86c003d070350147c0743c081150744450510a00e081094403140d40d124100ca00040340070050440944201d0b481260503500d401d640f08020f4503c2069601c580440100810000d4003199208072955009003025190500e8803041c40c40c640c0c03d41c0c10180c1110000d94000091005601d00f44e803500f403500350110b44a9806080400010700b201c0b59170038200340585802e6180e04e02c103802c2940400c080600d020000e5503200300e1b802c0b8003072100e45202e4040b12050b01c2e0003004108641080c05031018844561a128034050400043c074141241c21501242c0c081140403010403503202c1030002083c5030f00c00b00a1007a4241c5141c0c0085001c0054142080401804595000f0280c1c0c0c005105103810f0381040440c000c0c1d841c5c081220342801412403481140d4440c0703410010800c07480303a000341094084081c141a568884203121881c9215100075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 689404739 1250 689403489 689403497
    0x60225020406120804170c030d020106031104050c07110609030a06060314031e03060a031e0b06060f040b03060a050301050405070602070e0f0117150a02090307050a030f031206030807080c010b040507 87
    0x1041c014140c20341b04000803501c81c1c0c0b04a030490a07400300043d103007802190400d17006035143c0f60708204000341c000e00600806401c50f01408186808406079042d07006100c0c0140c002400610041d0443d150607040355000d540241c207403680a040c500301075002d407042d40b0081b03948610b071501c0100c0400011060710390103403110020701080501c01b4a02d010380d41020304a250722001112001000030008040c2007004280e4400041c80c520312410050b1840740024295405540b0401400030302c0d482110464040c1c03980318052548070384845000c1a1404070a03008140c05601c0d040c02c1c0818048005050022510cc41c2e003156041d948030301090302c6540003910804000300407040180001da9010b0042510401000212206000c3c4681c88840765001030f1460011107500085103445803d0901807140500015a101926030b440d680d60346c880c885e1030400c0a0104003802d120701b185e882c104c3e00242c1c01150004007443c0c4034402c505114042d07a00c001c000c1c0007103601c0d001b2903440c036080501402d0300c25021521 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 689405989 1250 689404739 689404747
    0x20c0f0a0804050d1103010c031406030106080c060706090b13050f0c03070512150709090b01050403080702090c130b09010314103c09050912030a090602250204061208 73
    0x1042c424444113011049030441080c0710400e040b40c40034412448000110741c0d002c152141c01100d034280622003c0c21143c06641005018000b0301d9001498031082c80341139a0103a5600901e08115005042c0007070014012071804060040c1026020010f05156001d001500c4a901c22003548541d03032070200414035095040190100100e1820580c4050070920100c15a14110038003494040d50010440310f48010600c408001e220300704040c46490443c0b03400703080c0305160a040d40c640c0017440c00b07000b500a104802070b2001458140b102c1c3c0940e500303040c000300d0440301c807510b400702445c1cac039008108845e0003e0300c0d00400d0003904040104050142e10380a072150241810513190f0a03440b005d141c0f070804e03402d0300d00006481c8001021030041012550304910304040382040103040a507075024011040340d43c401d80141e00b00d28000e104403508a841128005060041490407401038000d0140075040710300c00d290203456170700d070342030345410101e00c200c0d002c014040d101d18091061080f05030000c1c5c0312a170248 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 689407239 1250 689405989 689405999
    0x5061306030b010507020d0b0702160807120c17070e060607080714012c1b1323010b07050d111e0a0c0b0c01050a06180b01120609020c0f0a0804 63
    0x1030b02c80d03008181c0c1031501c0c1e0b20b0005e0b10f4020411020050804690707070210001004070032541071040e85510400380f8100a26076181030381150342e55610703000d0700c140740c00080440401c020024000c05c3c010721040b642d5981c6003000d0624151102c6c0940b207074540300d8201400150070f6291010840e00c4841d0b014080a0030301a036503e401ea10002e80d103010740d8543d9a1140000d0300b030350003e5400c44144510700b84110b460394070701d070b145401e1240707254900c0001910607a404c45596290920381902a006410000350034581841c03030100d080e5117000b070101582045002103040f128000003400c1103030180c411580c4500c0d03103440c02c0750041d002c104011096005099066084403408480211000c10942101c820900720703140c0c04080d0300154003144510300c0009104002480a0282d940d00140d101c60420141d840c0180c11002c032502c8000c00c00c80030b41d0361429072086038000e0806040b1392035510800c1220b1915000e520000f50b011130840126403045c3c41c08480d41240018401040b15031110615040a10300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 689408489 1250 689407239 689407241
    0x3040e130f12090302220e01020313020909010225030f0e13090203010b03030a030c0f02010e070302040c030e061503070f2301140304030206010306060e07140f1b010b04060506130603 80
    0x2da000d804000d0b03d14000409680e401031082031180000d584a080c90f41103c1c0307510121000c0059868050740140201300d0b00c21400704081c40200c1c2c05031034071002591142041d074020310851454604c102207e0f8a10444410b00f22200c0d01206c1c070036110b021007000c030f03a441654410041541e141e4042c8443d0402d4180688a400204001c0e10180c00821480390b030b48006410741c2c20850014002a075503101c01191907500218200b074075402c6000030410f05000500c01c981b10580d5020190003943c40303440c0ca050305c43c0f0952141c0d07003240001c000c2d01e0082c14465101511510b40360382c0c60b4420700c41c0407800f14a00c009101c0301c0b01181d05200c541e11101d00c41d120641c048070407268100d81484031450b4030b16420a501c0d030040d4071441c0320b6805002c86605500d0800111021a0040c102c024800810896460f40210041803410b0300052115154411164081e4081c4550601742040400a400e101107a12054022500b0708204a60a0248a072290180300490040320002c507810040705200f005180c0c02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 689409739 1250 689408489 689408513
    0x2105032b0911060c101a1c0c03030c15051312090f050d0f050a0813090506090a0509070f0618080a05030703050307140415030524280803040e130f 64
    0x4003006640e0b005e044044240211002c0b081c40311030100c880b8080040381d18040400403007076418500d41c45c1e50303c046a00e81004141e25804000d0500240d120654140401c2c071001041c04820304105100520f00880080c00c510302d580c07021200303d20b4040900c01518000d5001c0b40c05c0c1c900000d07102820301e1510f402c0100790380202c04161030521100d1684004100c2c18800a150745000d6021141d0360034a01d260250795951a610450b0354034984400c3c00020366074008641c1e00207203030900c0070501ea1141e06006080420075842489104011000003500c40c0d0031060913140511461168040c450380c61700f50945806941c800106550000c03c80e20700040d000e0405103400071070901d0581416800b8559200d00c65000303400c074034001e0502ea10f204508603810f00410354420603010803203108000559190240241101c1460302c0780c550304540c03543c0d41035074004017600102004089194103076102c1186469502500540000c20038000000d4a080241201030525a50050301c0288801060701e4031480800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 689410989 1250 689409739 689409757
    0x7060b090618190c020601140609010f0c020a08190c08014b06090f1401050607060917040501090605070c15020a120819060b042105032b091106 63
    0x68481d00308103c0e103a0b640304401d1500e03529001807289505000c07944030140740c0d550304107104810801601501da648215040c81c07002c25400c2903c600c44541c070000d40c00c80b00a030020310319803150004080311604110384920b066802408200d000030b407200c0c21282a240b0340000a4900c2081d4481007580101d0581002d00703140b03a82140601d0080603408401385008007140100d40d088e01c0d0142030043d82c560740f0840c03100c040c42840400018a200c0c54030800c40c10b051150910403000441c3d05410300c11703140c12045806a0003111481308409080c003103580b41d0800d0140341d0004005401c00716056000384100d0381c2ca80d400c9008041c01074940034800300c2118041c0c2c2c0850031170140480a200040f00442c12146c1c0204645401d10b0601c0d01c0d00d0448000750444c900c074094207043c45000c01000d5007107002c80d020790350000c08014207000c2c8448400050341890728010628440000d04082000700c0c100d0800c4a5007410406445489110a44106403041418040d000e0b03502c8082c030301c1d5a45828402401898 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 689412239 1250 689410989 689411011
    0xa0f020708160312050705130b0a021c02030706090b090115081f1b1101050c0412110301090b0f060906040b012f01150e0105030106030f0b1005100507060b090618 71
    0x40404d0403040c064440503100d8601140000c18942c240c0c480164140b0080d200c00300342c140c14400120402544d440c00b403081100307520b402581c01c0806a10078411214000d401c04400e102c481d0381ca1411718600502100c55a0007546400f0a40301400d108502440444810740010151541d180c2c80c80c0c1000500c0c910501031441ea40c12410400c221443c3e440d00b1060956100c40c41020301d5240081d003076500080c0400049202000b0074440100c480c0c42c0005210780145d9082c550000c00c6020030300400850802504401094041058488421030074901c103040a440007032554490000340000e8800c004880344c04107908544007095186070a82c4104c004030b60800484040c0c80403a989802c40386240d1407080c204440410030700c2207204c0b0b000031500401c400d50080108501d5611030700074503503c1440050035003004138003003501208840c05200151400810300c0401010b0f81c000030b0103035404104116105401c103c1e0f403080a1500c0007200d88100c401a00c0841e0b03010b184a28404651402000000c03d6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 689413489 1250 689412239 689412257
    0x30307030f091a1e0108030f030c090306100821030103080304021818070509012d0f0f0501200606010f0c0506010305070e010b07080f03131a0a0f0207081603 69
    0x4100b540d83c4604403100861010000d41c200003611036401002800c45a440c50800c400412601000004075050220302200880d20f80d04c8036484005d051007270401c0954513129100500c0307504444881000e04498103036044402041d0f020340000480c48900d401165511400c0c00100042880d84c0011a48140b000304103441c24416401d0064043c0c1d016107200e0115001980c54500e0003100b008010064542120080c120f5850300e640314000b182041803107025400401d1a6404041512402c00d010b00b01c1c1e284d084c9800c2d5180c9458042e0702c0c2251107214001010221070a80110450300241e0070006410080c00c204d581d643c005444d80408041802d041181154aa4000c01d00a0145501862140014007811440c10020441002040e0000c0c01d141e0010803100c00007510860485d85100813074a10036032079550702d401c40fa5074881c1002020740030052000c500c030310380c20f20300070181e11174020071004111601c103100c8110100d00401070002c09105c4100a869188003510100400283c401e10381802a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 689414739 1250 689413489 689413493
    0x821070e010e03010b0904081b0f1b010c0803091501090513030e0d060f0203010302010f171b120702100507180b030a1d010506030d05070201020d140c010e03091c05030307030f09 78
    0xc04408a50582d0300c801e01054031041e01464003009d001c0410701c50003c10110000c60350706c0f601d40811a506101904880c1441001c40e402034800c0001984c002c4402a02ca00c0d2460045864848100202110551800020905090700e104841c0280c00350318400c408051a03070b40c140e4005005240c0b8a80c012048070032000000c1090259407001004a600075803694990720024114255178071f516014414104a014100c05d0081082c603486a918a8115407141c0f20480306203440c403441e586681002088000c10100c00d030005690300c0440c281403030400a603901c16008480b45100c000c2441301c5d80150b49020440c0b5500c95010790303040400ea9400041c0c17a90394002c45880b000b6403014690360b99449000b002094902400300c054502d0705410705a240001550000b91905c000c80102014803400d0b1014403e484001020b07142407490074002009060403001880e41c1d00d40001c2031040c401d441100442d10f22100c2e8001e0724100d00c2c0e00c00000c1d411500d580fa019030180c4600c26030f0840071507880880f100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 689415989 1250 689414739 689414749
    0x6020d120209190504060608071b020d06180c1505071425080d030b1f1413050909070812030403050f0307030b090a0506010504260a0821070e010e03010b 67
    0xf1810300c2d000b881c003900901d044288001e40d4026840603043c0103507001000203a0780c200c5c2141e00248900001041c0185852001580e2940c0c0c041d009840c1c585080d0907458002d028521984855000b0f0304401c151990300c0b189502d00301c11039114000014010310980f070014442011050000c2c2403901540c6000c0340e0101341c105496171b2046460011011010100040340040c4102c90110700c0710310782440360110a801146980141160030083e039031701440c502c084a0703c55124501038400300c0d48456503a44001d103507210160194000c0c18402c51800d0301040b005003000410341d013141c07900c1011388040344984400c21001c0c1c10050058090010400101c0c1080404a000390303c548010344000800c000d0000074030030640f20061843c524071b0715110a101c8681e03000015a0f00326203802500e000301c003060002d20000158a0030a264140c03107003a0703070442007002c0c103800f91401c182050b0000b1035006903017002c00c240341c60079241080400c9645500c000d0b9544102c8424101940c0900041044011035000c05c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 689417239 1250 689415989 689416009
    0x180e120309060115110d08040629040f0b0f010c030512041b060302131806030804031a09070f0312110610050102010c0c020a05060304050f0304060f090501080106020d120209 76
    0x22402e4000800510040c0c085030626018a005442c0143d14451400c1000f40d455200c0180d071820302501c20001010090550405c00a40040440d100003082d540780d4031305001c0007084000c6218500b4030080b0708120443d44500d282150000384400c1d044d1442100566035000d81c490b0076010443c041104025441e0030718010f9007e24441c500190b4084c00f0608800c01d101580e07003189040500407c0485c40c1d8105403d20241030301e40d095020340d010b42c0c29600f0315004004960000348900d501050020500081e41e51900c000001000749000e956500e030000d9450360024000d600d400c00c07200c58280040349001c05071948078081c50604820780c034050303040a803a05504681003144080005014442da5a0a0041c448035001c0c9040690318400d283c0c3c0003458642070703405094020140440000c05022041025403000c3c061384054a42c0e80d5141c0c400200710070b101004450100d906107000003141c1d4810240c0f00e04030350450340907151101c0020801c40b0b00030307280910305e005c1d143c0920211034980d0341c000e00a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 689418489 1250 689417239 689417251
    0x70c0f1d040f0606123c03030b01110f03030f060f0a060309022205101e09020d15060c170a090e060307050301230a0e073b150a180e1203 60
    0x8540c0c086852a0806d07602000c14103004800d415a181d02102c0404c80410f154050703850b05012030768071100c0e00101c40044903460900f1a62003119005025502e001c401940034404801e0306d08507507030303445040c0115062140c500a0300030030315101c00c102441c42617105845061000700307041c40861041c0c0c0c90481c201403105645409599940502400f485100b810a00600084224034401c803410418207415601300e10030300f4050f5400040c800c400f14440c6c0d01c44544d10240b650020300381c90312400010700724081c4840c12509801941c401c809002c6c1c02c20b01f134810001003543d441008600b0807400e94140e580260956816200f401004911a6428080c00149940c2d290780705a4190103140c5414070300c603024000316041032521610300400071010030380000340c641d2441030003c200d103065001280f00084424045800240a100c20502641c50009034001d8081c4152104400942402c0014080440c440c400b01e0500c109005070422a0030b82161282d403216500f41c0300760040643c81500307954011155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 689419739 1250 689418489 689418503
    0x22030204021206030606040504021c0201020304030b0f22170d2003150402040806010509090f0d090303110303270c0402030405030c0115080a06110f070c0f1d040f060612 74
    0x4101c041c4c2820040c40b40c3c00881101d0500440c240350700482d41c1594110039064100042114840035a4000c0007241c00441e0f00c10116082440c00e07052002d000a400c0c0d82100e000852034150003090701507882843e54080c0c1002001c550941a4580700690b50300941d5059609a11544941d6642042d00c1c0150740300500c0f036904a90303d1400405000440201e160030f02e10407803041c01309110001c0b00003820390640343c00303482e0114540c0302c520895151085010307111045201d1102d80241c0d2952040c14042203d01c01d40310180e400d4001030003a622170008440a0032a0150f0114202100581030140741c20015440156503200c881000414241c3c1c0c0201c5069665520018420014150900c1958100d071191b2070302400d0581803a11080d180c1400c050701500458a401b9030042c0f6908900450b01003050000c00541c1d1403089150841c1072500314490101e00e86d10940001541c1001400c901c40c0840f24100c20340d6555aa4ae551780302049501007003910a160b55140c003207003650b0341c511000380040c06403103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 689420989 1250 689419739 689419741
    0xa02010206010f0b03040204020901031e0e060f010605160c091109090609040305040306050702100c170a05010b042304020403080d0e031204022106100602010b0411220302040212 78
    0x1919041e0181d001003200c0300390040400c4001c4003201070300c2d00320354129000342e603941c900030048020349041a4000306500403c03050100c0040f0a0b03119188030020760742610401e03900c048400315104001d101c0c8001048041003c07501030040006080b0710329200d0f00d94261029140c000740c0003143d1990001c0054a00c000500307852618051200c640e00501c100c2e00035803585442e50340140107014500c8000c1940d80c039040841c504c18024401009200b1150b14100700b20150317200000c004170510300782c0103524a510004510f0140303072405904d040e114400e081a292515000c8500313948a24184400500342131800e48080c035590390300080000310b001c1d41c0d400d42ca542842e0001000c581d076521006030b03103510400c6409000407500b150b456009404907405c1402050301410062002048112803c0c05c1c02064104030b0303500080103110040c0c401d2075000f00607003001002848101d94540c090440b42c690240a100c1a545000361186012501b1180d14500c140c1d0b40e50125082c1c0e001040005c0705400d00d04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 689422239 1250 689420989 689420993
    0x4030212191e09180f0513060b01021c0507030504080303010e090706050c0601030204091e0501150509010506030f0403050c010e070e0c1206101b0605070e0307230f040e0a 75
    0x1052886003100e402c0d41082500000007030003d0751507210310045080d0b110b468031440200d9503c450216204c1c00c5092007945010f118910601004000480300c03180340940c41c000c2035100241204801501c40c2c000034820840c3c1e2815600d603003014004a0402c1020040400d001c80c017807001d035009140312115003c49003810324a06003030200c00d0304080200300041c410400e4021000880604494066400040d010090706140216055803200c807011010800d003032008211055020241584c5070302e4005944944400c1004100402071007000d50241c400e10106d2181c9404105058009100e428040d280c55991501c05007510004050321140360000c010400ad40840307a280c050340602e40d810620310300040d1540c000404400981101e0040e8206046061030a00440d04994425500d241c80781000640749004400b501040b41c0d5100003585078a140308650400181c001d0642e401e42421410768403203008003008041041c001c5903800340320a441d101e80c2e51114410b4024a01c2030b60302411410b4118 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 689423489 1250 689422239 689422247
    0x20a08061828020705160f17060c0a03020919060e0a05090609090a0c030f03030609020910030b0604081006090f1b0c020301110c010912021c0819061814130b0403021219 74
    0x5132310540c0c594040c084009500c007001316007203600c2212540b007680c5510500008800901a03511910341150408000c00303980c140000c100000c0381c81554440e55039503480c0341405a044050301c18070303420004c82c0c0e0114016140207214a40d102e4884422104a5000ba850303841550746e40394001c3c0c410700c5003607400f002070543c940220400f4154001c02946088100c1000c00c2c001419003812170708060b80d4420700300040c2e540104590040c8210005c035001a613040e401e00004000512490380c02c41d180110001c405030180c01200b8414100702141000d140032080283e604448103030f012645075580d80012140050900b0251004001020002410107070714541199050000721092003558400c4001c1c40c0d10301460140c00201c00580e10b06500b40b41ca4102e40056090701e1000301c0b440c144d00700303800801c1084241e42c1160601000080c00c0c041c49142d4890580a4a4152a24942004400d000340e0100c1c01040300700c0c5d00a40b00c1d2044440340030f20380e4200e4903d41c02c60b000c11441c102518040c030303003000c0d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 689424739 1250 689423489 689423519
    0x30c0b06030102070b0c0304150c031e0c140d020c0d1707140d09050f1e0d0804021f110609070603110c15060102070306020a0806182802070516 63
    0x305900843c40c044072600c500450f04002015070042c100000300280070452412402402c0418880060005502c5508098090303c000d0800c0010084801c0c081410f11401d800b50110040f00783d124418810b800c0300e91240d8035400012200c0e44285c007000f40c01c0c8070036010405800052040e640e05003100c1e402c1d0285008003000036100e034040201000811001100c0752007190a84880c0c400d0010b0600c90b18a02142400c1e112072450006000d039184250100c00800c00d00080c90103400203650103006860030944a400d4240ca0103034018000c000c1c1030002c000001c1d4140c0da800c4c0c02d42130003140683c0603208141381c058200c078410415004440f04000541e014010500820001c01140782004803010042d5074820b000858102d0914800c004958940d000344031405c042d41d0415815551825200c0b8040d01003801078032428003928030b2a040c0c290700078681504500484015a500000303a600d0444a81d07060040b5100003002c542c00c01107480041c0080000b014220780300f40e1402021454020164034a40d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 689425989 1250 689424739 689424751
    0xc180c1103130b0a031401120203071508070c210e030f0a031d0f0603070815010518040903030b0a0e0907050d08070b101d151203070b22030c0b 63
    0x401030000038400b03200e400c15007050b40c8409080b1901d8002c000011009060840c410603412000800007040704070f03282c00ba041005000b903089070702c00c42d660007a8400e0040781b010344200049100000c290054032400210201070300030f05200044c41414020365000305c2d0180e990102152041d05c0e8041141400c4c00142c0203000301101410700c41585440191442c00c43c0c1800c0004d4031a60b0203075a040d6136911041d5401258007074000c07610788c9011400980606810340d84106400aa45040d2080758402c10481da0b05a1500c82888084a407450034000034103074000c001c03000e150311480304c0d01035511204200c03402010760054892860500c05120760a2010a4102a0142440b042c405011806850850f000e440d4012921680c40da64021040e400040c20740000c8003220f5841500c00310b42940d4800306000d0f40c4204c280045070142c0d481044440184085161442c2e0014842a400702d00d07a00f1107103602140c4984103803000200c400007030001d20f0381c0b103200714003190907172035010140b003440b220b0507602c85 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 689427239 1250 689425989 689425993
    0x509011406030a0209040819080411030706090618080607020a030e030a111002031c0506040506180106050a0e040c03050f01090605030312070201020c0a0c060f03060b04050d0c180c11 80
    0x41005804a61500c0c035044001e0b02401000300446c0800401c03204507840481081e00060303106980c5100180042429102038444981424990009240118010080b12121707110041c0c1c1900c0e015080d102d00303054161044042444010004005034180315180c415220395001d0300200380685009844104200700c094003d51001c0000f0000408000241c006c00380201e941c85440069508201d1030343c0702d400e1400300c01d55020314002050412540010780074910449041c81706503698418080d030f5a80641c90046078420003001040b1480c000d00c01007184220350703c0d00c0051164204c0204003a103203004051740000c1d54401c100001c281d0140460b901419000310f00344001850701c0c000036070324080c10500d0a09102e000380440c4281d8000d50407250500710005c00d0f03542d5030312a4101140d03058510f105113030205162b1002e8000c40d40c07081c4202010f4944500d145428603041c00b00303001c02d61400d01021600e0f003c0c1c190010030245c04502030040003200b04140410481e8584000030402c1200c0b40e0010003907 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 689428489 1250 689427239 689427241
    0x1d030109060e1617100b032514010201020a022808040f0e0106110a080d0f090c0f080c03070e150d08031b0901120b1504030803010806070813110a0f0905090114 70
    0x10200101d010f2403805e6682d01d0124411104070000303410701b0750b03c2d85044c54181002c007168042125000e074400840d030068140c503000c54100401a0300707078422554030000503000360107107119400b00c01701e8064802c40d00d1004900c1c8145d1503541c05896600c103400a1500e14840b1404000207181d518110340500024a001c141e6107940305071071030782c6581440c801000e0780000304414841e103040d540081010f480c0550107000a0310142440441e03054a0300607c407132000441c101140440740004d0042c11048054000c114444c03400e035105203540303c0602010000c08142d0b0103d501607403841341c1c402000780118400b83d502d050010907402c610100c030b0015980001c044c44200d82170707a003007017180c4140100000041100800f16001507000752660340014844000403c010080c016400080d5050701c802004580c419100d070320b03003134800c01d000301c90800340300d607201440c40c0c00a0341040d9000440722010307044a0106403104081c0c1400c600d1604011704042e618400c101841c4024000c810910750104404006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 689429739 1250 689428489 689428529
    0xd050f09010b100309060f0504110108090106050a031104020f2101050906010503190b19031e080901050c0f01020a0c050d0c0308071412090304030c0f061d030109060e16 74
    0x1d1600419402e10030f050740c6003000300034081e441d00450301f4440700c14800c105034503040ca86034096800085410b40040c86440001d00f00400510070001550703030044c00301c000c1c540340d5980d40807640c14081c60305800c50b800f0f2110050785241c0e24003500c0c40440710513514000350382c888200c081011050340700e0b51003800d20780207102e0140d07004400c6a4015000959550064640d020760300054031041004503003003100c900d50b684100d0003c64204054901c181d454031040ca020340062940c40b1010480503005032030030040078503598002d0005041d25140310b4141d1300441d8051451030b0898010171072003008110a100ca20b0200803083c040c40e515149141428510b0203043d440003026001c00418200503c0b2051942010795140708013510b2118004803600826480c001e569151250400e120442d80100355000c0402c41c03a00b103c003400c042d1a82544c0780c800941c0f03101c1d0b618100906260030365805550311800d540c003041043c0103a040c144242c000402d1885882d407890810515590322000405e40c1450708801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 689430989 1250 689429739 689429749
    0xf150b1801030f030f0e0a0602030a1d0a120c0f0306021c0903090e070c0204020c0d11121911030d0501050f031501140a0e090a170f1b01110d050f09010b 67
    0x380f650b00362500130740c001013805050360040100746540c0c1e485040314900181079613000005184181c0c480c2e442600b1003409030f0004503d07115aa20b4140d11099420090110300c0c0c40c07a2006080500800010b01079982d0740c07007110310700b400351781003503416940003c0d4440740c000f5005810315644140e003c0420403122a0b4800501485550241d0811a260032001c80c2d503691250702c80d0301e0074a8000700219640e00b403129008d03640b08040d10500c4041411102141000c0e080403d00310b0318914440c05092030805140c0721200030010070b00140d8180900380035181083e00042018000c5403c0c84600013815505060800510000c80b20b40c080c17095020000050170041c1d0310721140d0445510442180c181303800140080c06120464010500740e0440c5410403143e0440000e98401c0240504007544003990000f00302036641c81103107001e000944042002c42e1500300000d07800000440b011000245590840c0c080241c203600c0b4030803980860b5102e005004000d1012103100d030300800c4010003009144140b1001c50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 689432239 1250 689430989 689431013
    0xc09060d0809040c110d09030b09060106080c0306011e03020304060b120a0f170a0815150306010810030506160e03010902090408070501020405102d080c070f150b180103 74
    0x40c00340e81c42c0d15144d92140e02406030704045420030019500001c603400170041010710644001c0c0d034550301000100d00c80e004081489816640c2d190360729401992410211400e642c4042c104d18100300b2040b003856002c900c3c40030407042a003490341d000359581c1010305094007500c425441d0f00e1f10420300482064112000012016000750b030058105060311070310b00301a825071070281464803440c140090b025142e154001c21300ca20807001c0740b01c0e2899858094082c0030301100c586040000c003080230000718001d5800381d800e055210000f21801e9000503100c1d614182405001d480c52240d00c1c1b002000402203c1d0400c3c41250f401c0401c1c3c000700140c2d00e013038000038040304000d40007420720f40c0002007030b006010007901128040d0070041c01c601c0300c0550780d0f6002811503601004c248203102d00c0e08950202c020ba0406088204c6640b5035814101c0d440790007032015242c0c000201216040b100040c04400101501902c001003007140c40300050001540c1c05001c21a00000c0107000e103003414030014000942e89010f15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 689433489 1250 689432239 689432257
    0x19030c0807020309131d01230408161b08010626060720030a080f0601020a02010f050a0c0c090506040b0306010b040b0f040503030d050402210c040c020c0603090c09060d08 75
    0x40c013174029064001a008095642a041085581c096500042441500160000003030195030044108800190b049010400e890041650000704240042c1401c41108010001e000d10102055200300c3c0d40c42c040b84502c1070b4441306459440c5e481c10802500710003188050455108451360104003160045500d4000041c42441404030804c006d07a00d0354400705a800c060401c1c80222565400300400140000e04101c3d07090035420380b070380005540e952000c6a0070900f50350684450100a121000640720b94000c03180e02001c00001020800c0410302110342c0c00014507441f00001814201142440192100415114000c0d40044010484004082c00329411100351300c80d10340d00d0701c003882c40f00519882154040c80e4184000f15100d01943c140e5408540030b144219903483c4860340003251190400646090001c3c0d641007410001c1c4141880d4020107212291132040d40c041001000001b699038105981560640e0310820036010035007040429aa0405c20072160b0342400d100b2581e441c0030910a00c284 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 689434739 1250 689433489 689433499
    0xe06060c0a17040f060504080d110c131104030f050d0801060914010527011e0f0324030f05070b04140f040b06220b090913050a020619030c0807020309 66
    0xb90400404a0080d603019020304124034040a90f103590040c82a0824081c0c44454040c50715409a284c2c01803201080921441e00903007116407140007040604050140d20941d000e85403401d45500200490040c000340d4800d801c4c160002226003003051916840304010402c0c82040401408100e4100c001d90341107904d2008501d0554041000407200342c01925171180010003042411a1440d60409003841c070704ca400e81e01e5501054003a0b061442c40d03804605c1d8040030511600360030a046210341c200003070109070400c0c0801000064080380d0400c844d151310581c4d100d08003150800800805200b080d0081a100c0c50450034142424504000030500d0000c040c810385912002d400aa00c40360015801402c0041000d174560109840500318410001010030400505007008500400c0ca0010707a81014400b03001c150103030b511900881e100143c1400180e400d44240c1d50300100607a6030200601000050362110b402c2d0b81d88108001e42914900600b500c144050142086070311a400416500c0b802801c0320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 689435989 1250 689434739 689434763
    0x50a0204030c0b0325231c1e0902010306050310020a020d030917090d0506010e0a11041409190204141e100503330916050301090902150c06010e06060c0a 67
    0x1d02a94034548040d00c60407811940c1d402d1420080001d00035040d1f00b0701c40300d807101e9000c0e019083c4400700c1d54001c641280005d50701c040c040e00f13441642d20000e01c403481030400050031902c44001924004403c814600580e4000410100c00c50b4148600700380f007030b024142032043c9045550b0310b01e4810210131285501c040c0c00710340c000f0660b640c3c006084034144c208040d80c06658407140d8102c0c2078101201c000b065182088115410704140d10116811280c03025611208200010700700591011701400c159a0b401c4410b035644044040ca20003031008150308180003040045000c24800f9294184811810301c605d040e481410740d86170079518410022491070229642d42d43d90a112002c080b8202680c4c00412030001d145e058144620701c003600065084402001d55540d91030f0310368407a1100c0c0307008800160140010088a51107803c0100e54503c01840308202042d006902110340e00020ba000d032540d0300c600010821200080d02d401c0d0080b00a551051a014140c407029541d4458040e000300844a041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 689437239 1250 689435989 689436061
    0x4021f030e0a1b050108220f14061005010216090e03120a0f290f01181206060b0a2a021e090a0203090c011b021c0308060319150f050a0204030c0b03 65
    0xb0303004040740e500461740350001274458602c03940c44070121a1541418880c10000c80c80307600008a0000003002d0010a6800c50b080c001520040c110864000c00710b44002d00c0060070800d100544584a560fa600e070016082d10b078005440181d500d00081c1e80e0b4400e40e401d41088200c042c03502100380344030042d541c07203501e0095400100c0360036040280642c008185510040780502000c03040741196070288405004140c1c4400880d0064850001b001022508107140d10303007082034a080c80b030300d0508203100c0244040f126070007054496952006020010b18a07001d00c1005180195840e9042103502c03204500b181750100a080c3e46d04504a400d41c140000188038105d01c005046941ca10182c0c09405141c40380f681d01055100ea01c00d141d400c4011640340e200042003802c0014201140c000070f0225101d41442a4480848516a540144105076142d048000026000d4080d641c05018006801a515440d40c14505000038058100c1da0000c90200188030010060714041001c8002c0d51415101c0040d8070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 689438489 1250 689437239 689437253
    0x20606100926030f0c0615090f1306050c190e0102030901120f06030305090a090c14220b0a18030218090a21090501020604021f030e0a1b05010822 64
    0x1202d2800c905101c0001d41c1041458400701410000c500c0d641120342d01c3d11085d070070400700401007000701d41011220001500d1300040c2d2038500c0d0032441d0f1042c1c080443c403294540d031090310002c5910a60042002440740000b401442004a40d500c0350300d015451303200c5810000351644140d8156904001250084001071700302580044e20038101c000040000c0b9a0300d28002e01240c11129100f44281340d46440007030750300c00500410308991b03010350303030707503030141d03019a440c140c69003005004001d540104d0300c011020032110310540c0050a00100e045440e0440c684000340014801c404900400380c05150030070050f110043c3c20511000da00a01c000716503110200585000b8511a0140048984503403201d07210081d52a04000740110ba03031031090041c0c0365001139958401c103035002074009100a040c0551034251603d42c2c08552007914002c98050701801045181c40c0c90110180d90103034031409019203607a400342901000b4502030038110021301d41000c080004151445019008030800d0304840300300f12403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 689439739 1250 689438489 689438549
    0x1b060a030e0307050706031103090d050f0c0f0c2431141306060c020d030207051009091b09030609021305090609011d100b2e0206061009 60
    0x10410841c1e440310f4860a001d035071403c440c0b003424003091070010310b00982149130040b40d202d80411001030460202c242011101c0d5400b40355020f004000502070700426030014031004501e030701004001c0c0340b444101c03c108030307103100202800328051403000d9100e22400118000c0d192400d0f0710415462442007880d007040140003034042d44844111058801142d13401d8000306060701210251200c150311003c15808000301d500e40d01800000c00d0180c1901d04c01803501e803580b00b4041d031092056408044d642d10124054185001c541d0001c5503001e042400100c1c2e140c49014580455417a480e0113517110f0306400340c222100390002520311925640400c2c19500c5081e00784505c1000100100032501d07041107007035150b02d001d5405181a50030b100c003038004558440300c0c51546d010300c1005171002003440c108201c000c02032000c005410490400c0020340458bc51042da2a1140c0418460711581b0800035000f800c100004000c144507a844d920305426840d032181900c420b603540402e44d0900c09000460700302030900c0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 689440989 1250 689439739 689439761
    0x807060e030f04140f0108040609021305010602030c100513020d0816150510030c090b0301110c0f0f0601240507050d020706030b010528050c0a03030501050f031b060a03 74
    0x70002841c215403030b580b0b50051003201e4480d1240401035464204111130040d401180c0c50000b80340c500460081f036469805035a180d44000d05000d502851100c9040907036500360701481c050380010527501c2600d4001d02070315a40a01c0c80310f0401c034516000b1903241007188100c2020740225040c401c000100300c0340004071911101d180e031010303444090914203480f40141b800511708080e070804001c0303010803140c9102181900c0c1d0003039200048030308040707160b4014464000415819901c2c0c045002da00a0204010400c6250030000b070512a14100426450072940220b9002290302080040103200005950740206443c100c110903528091040d0455041c0540c1030050207074024414140380c900c0d00040c0010827143e0503241400512010801501c840c05085501c862000710900d08011113024415030426484450416a0078203c072043c03950700c0c090980ba0100c021070341d40c4006221514124001d000d50b40001c5004081c21304054140591141c200113034240682d6001c225811524040d410040040e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 689442239 1250 689440989 689440993
    0x30507031209170715031a06220b0903160b09091314060711070f030b04060603080c0307060605040c05390102090f0a03020a06050a050f0c0a05010f05090a0807060e 72
    0x18003428078441c0c84002d203101700004984141100b10304c06002e0f008000350010340e9420a840311001c4018010300da8040c212210f03c0108010130960307100700c0c41059034040c102407602d06031101000d400307041c40c16410111044084c0900d400c10049103260004450000d074082e00e1000c060344403003607903000090b000403000380502d00b00c200c121115000000e4007441458941d440084407014000c5094440d5a6802031000403900181c042c40440c1c84144201e4020f0300c60f0800250725662600c0d44495500f02a21000c019007000420100740502030181300040c02044030104030200c0c0d461009000c1d80300c0c0f9914800e120081d6030800740d82070381202c0d41d6001c440c0044141580158032000303260013580440d035098810280c203030820955080114104040e681c1c007414403034006091900079201034100341014010824100701c224a1640f80901030140c0f0b568403001460300740f40350f1402c03900f500c0c0c01c43c034040c05c00ca192000300070707100c000000c200310742d26000300e00307541e4400349810900d01038211009000310038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 689443489 1250 689442239 689442269
    0x90303151f0807090501110a02090408040b070c0e01082b030e03030c12010b030609280c050a020c04150b070318060f12092d0f0c17010204030507031209 67
    0x4107400800803445801d09130390f90502c05445400640301644134284100199000011260050901d1460307070f0340050043c00503504280e40d85c00c8000c45035010880844400903800820048500c10401c10382c0940b0804c4064044000d00031500c402e00031404010b407100500b0749107a0164103002e640886c4950281d001038030b54038a07291445802e2580016041003c0e041500c1c000220705000a0035070b4001c0344004c100780140e86440c0c00310848000c2d00c01c0410318505044411a1550041c0d11034000403032a5a142e080c0c4030b00319011b0190818007070008070745c0030700d00b045502c001c0000c00800d50000c0c2d50003c2c0303049455030380131b00701103641516400c0e00300d25004d00c40d01d010030a03035086000102e00c240300d55510003035101c0500545054800c4100021712803c005180034485038002c1d0348000078000024031440e10703003c40c0d4580031a42c4074604030a844170300788110188144410281c9410440c00c0e000000e5250600d0340d43c64a41e540280d200240c08004a441d2404000744680640002060407507800600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 689444739 1250 689443489 689443549
    0xf020702150c0c011b02100219061407021902040f020d050f0a290103090218100e34090806010311031b0913022206150809030315 57
    0x1242d111081070078440c8220601c40b030466200d141c2203240c069241d030b1840340510329a420f00c805404e01950720340641c020940046042c00310340d04d06c49072141c01103401050f05040d4074010b120148015120700c0440d00503052081d2441d003d084814003680d0305607400030300c804190581400900a59016406850904062004101c15003180078000d01d02441308010441004800c1840b061004084225041451356040d100c0d6010b0760040d103480b400501070040906400138240d400d038500b11003071013010f1405c8105000c07034070f68607000e40c0e402041058030b01c80340702000c102050700c01e0800742d020501c4559090f0307c0c1030706441004804002c21781d02c2c048541a586034030705502c0c8500d48000c41c9000303200b02c0007a000234400c0202c078000c05150151072800c0c1034941c02203220006490407010780c2c000241046203410b141c100e2a610034401d4800c0000203065040480380c3d00700003164076904040100c980203110320303c034002c02103d1300090745100350a582d40308080820341c0e2682c43d140035070f0107865a0024a00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 689445989 1250 689444739 689444779
    0xf09070825021e0307020a0e1b0c06090601060f05040902221701140f01030303091b08010b150c030412060e060705092404050f0604050301060602160602060114040f020702 75
    0x851500d00d014600034400c00e54101d0f540d00d004001c2c0c00780d403104c0c2c02101040112010500720b80c0084000640144034148100890042d600840070800c07658000c0701000180321060058902500c017034504410304041c180001007480c01140100b03170829a001480088982602c0d080c101d111010110400d0f1007942d400f124400401c21940c0e4000e15405c2c43e000020701c2031050040d500c14000b42c03910640590942e10f04600900c0500011100e40c0c0408040000c2c1b40c1d2604c01d600000c0040c00d0010030300503103080034080308410455155003859414404088a0013010003a03c0685001042005051506080240c007604c0390414a80850103604107004006078001c0041c00609415504280004418400095800e841c00d500fa01d0072801440203020515103801e0360902908018070f02410251070f000041d08540d8658440405030703010300c0001c006180541c1c2107100410060000e00742c613614140b4500d010942d40c130080c6d8480c2399210f41c601101c100507416903d4003070b00030380101c110305050401d00d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 689447239 1250 689445989 689446003
    0x10203180120070612020c0a0f020616110307050603041a1b070c2103020604020609010e060f0a0806030a0f02010f0903051501030c08010e03090906030a022d0f0907082502 75
    0x5400150580c1d0242d415685e10b000b10356105400c00010b15506002d44c841201020a10004a81c40b14080000c041c1d104680703e2280300c440c1c0038a81c1113494141c180704041c0b9081044c0d000f28021700e01402004007003501441c4c0100101310810b55620550b5845400301c15689010b44d2944e428a0085000700600c48010700c95030540e4101920314101d44903415170b907010402140002001a40060005001801c04d1005458543e1040c1017903032541481c0310006000740c01a1078070400160000c5081403d02d640604404d4004009078007a04000c500303a15800d15003641c020004c0d0501940c4101c418403207101e56407082c000e42c2c014066940c901c000d26100d4440540078403040d111000228000300b80340d03406116058500201c2c000640c58a400c220900503110340051119500d8000c2e41d10141c0540c030b843e6408800c0000880c0700c464480090000400c3ca1031044154602516100c03041088580f0340501c141e420050604041072185e030f40d0b002542004088564982e81c00e48100c441e00c2007160005981 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 689448489 1250 689447239 689447249
    0x30606160803162d0207090207050a0210080f1303021f09140d2001090204050108060403031a090105090406291e030a02061309020f070203010e0c01020318012007 71
    0x2001c000d12500303504072103e5141c1c0c0084102e24034280000100e000001c100c0c413007072a059006580c801ca5407040540c0898001010907200d58010440c0c0404502c0c0c0221060105045800c3c048100c0c1006004500084001001b480924086110500900d4020400382940c021180300c04461107540590900142001e01c104440311070303481081408200300410a42c280c807800d960360718408036180f48034410421524021108a56881f40c0642c0580c4403800f40c54040c05958005010900f024900201101c0e1101494844a008000c0b030400c039a03510810241110b800322401c1074140c0320750405d60010104104c02022a500251803000742104054504064100494041801d81c68060745000703d8050503180a506da00072a60880052400102a11403004d204403040344a41d1100764810484c0d0102c0880b0311003440c08240348007180350901629080b142c000380a41001400100047c1d0b40f030003505210300944004200e00485644603a02a60050f08048441d895006201c00c8294940c03000b4016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 689449739 1250 689448489 689448511
    0xb1e04060902011706090a0b0a050a03060b1e060922050708060112051303110f03030c03150d0b060418080d0506010f0c051228020c13060b0708030606160803 69
    0x113460404c0c00101514440c21001c1c2c5118002d0b960070018030004e10120345142d500c03103046980460742e07484440100c40603502c2a080091405060b41c01c0010503a0070340c0e00b021601003c1803528103580c98500a4038078103c8141d403040c80c01800a1000d030000c803403910181461030b25102c00c100c0503d03800009540500c1080e00c4e6001612440343c100700546000b100c4903201072407071107581d80010b44520002408a10708809440c12183c00225035425a44155075580856501001780900d0340d4070b83e010001d15402c1251209401d91540e80d07000d1781090002e05203489240d4841c6602e1300c545900381178100c0f865001c100a5980c0d4070003800b000081c4829035201d4000349000540c026130758007030f04448070201e400c01c0040200c2c07540355139580c490390320480d0303043e01004141a03540c0c020046d209101d03087c08200d401500c0080b80d4081804107402d03520090010850802c1400c11980325424111541d45401c0524140e50b6610b0b0300102d05688120101c01070005071340c0e840340c1c00380300c0704002541c000e201401c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 689450989 1250 689449739 689449757
    0x518190905012903040302031c0507120921030e030d092105070b060105090d03050d05070207050a06260c2515020a020106170f10020301030f0b1e0406090201 69
    0x200c0c00d0010120302429111100d203018007811100400004c1c5501904c00e1045038a0810394117103c0d040090780300d41e44040c59440310140301141c1c1d0082c888540454415004100e10742c4240c03501c0280310400002d04000d521400da4602c1468481d130000c2c1110383c0d50408580d52101d03100c540c0001855a02c0055510300c144404200892202046041c401c00d026a59982030000607141d00c41d1610f006051a810b1200400c00d00c80765483c1c0b000e082da0442d020303481c0c442e103440c00b44c403003202035440061040c0c046401c100c0e0306000c0307503031200080c0041d550706240c8403001d1001800b4924100605403015681010035604000490300da05004040325050b8841c1070390484c0070800e00074800300c00c004004042c6a0740c171300cbc071400700151940682078400c0c5034800401c0040e99035407141d40e000c0645400040580244451000c0380d0320420039941c2c0741034000404c515541c5103490340030340340c0e20761100180314820704008034160f001c07594005101d45580340c580300202d0800317180c585c009041544049021440f0a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 689452239 1250 689450989 689450999
    0x318030807201515030c130e16081605011e090b03100f060203090102060402010c0519060507091a0307050f04090c051201120c0e09070b1b06010e040f03051819090501 73
    0x20a44480c4440140040c40d030710801d01b0030001c004510344820039680355145503003100c1c060204081000c080000c929080601d0800f2101420700c1d040c1512400c1e40c0c0c1d1001d10411940c0d900c903d0f0000c40500d4548211200341030140c08403000752030b1fa0f1007e03120000100c2030006015000d0b1142048944010004010303550780d02c03003a6280d004501c601400358201400040c00f40d40220710030419248600309036005880c1c4104166151010403000791440740c0d07550100008180c20501d201e000e400725034030340351400c50744810708115480010b1401c8100030002c03400840c540c5016080c0c44c00743c03102ca00140425002c05000600c1500080d42107100c4050384000000c240035540b540080e01504a4510304c08039062034081d101c115406000c0c240a4400d208000901949400141070004109502c2207820003c4484046c035101c0306800107110b09118502f480000b03000784800144065140c1816a210005034030706143c680f50040c0e0150700181074190705440950800e5a18090340d960a0003000540d0301c030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 689453489 1250 689452239 689452261
    0xe0f120f0c090106020d1409120109031d06070f060204170309040f020426071e03201c020118090905120c0c092a04080d03180308072015 60
    0x81c032481d00545c00040c045191244207915803004034000e081d0f014230704820000418255442c095888072103942d036140c00e0041643c00301130f05856131615a01104c4150001d00002c042d80b040150040c0724802116892080001540503640108031111002001d1000c4e010480c4d1a80d11a2011070312992400401700c080d0880c41c0300340c5090340c1d902080400e0042144190345141040c5040404051044540001e131014002e1040900200d000400100701480c51071305281c2141d1460018206c50011100300007151102802c18030b442082d40c11144c100c903c2800161143c000d001c1d041e0201100810f4085480d003d2504142c0c201c40c4a2002c554010010709a03e05c86401500800200c0e0742115101c90a14584400004d401c03548011101d410301400c006a04070041104108020034240441d04200e825400c1c0b11070b0b01da000b1541005d1040e0450100303890040e81c0c00c046c0081c01c2c8003040700480c040da0722a5030000442140c8540d801034072030b40074a03000d60710400c0c20002080300b66003400040f01401e003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 689454739 1250 689453489 689453491
    0x9030d0f0603110d05150a0603030908010506090f04060204150c02011101050903040501050a050d05040f02090c0403020a15120507081816060807020a050709020403021e100e0f120f0c09 81
    0x101040c0241c00021030f0400c40001294241a10b2610480080e0144182001c0f025401189038460018086195150191408105600414869142400b00807090b00c5207003055a002821110f2100e035995240342c060024004c540040d40c0d004014a41c0d090810f8110010405260007602c0b001c43c6501880c0c002c0d801e90300200d440b02e04580043c80100800e50040c0003400811805040640c1000b135180d0042003220b10844003958142c028030b1030305055041c19000c0319006181030344614901425a0003003130407007035203200d95014203c10408840c079141c0b1501d40345110b041d202030144147d00f42000020b280765825904645802c11003031150099030400201c3c00e64911401d03184030b0006140100a5841c400d00809500c2503015400c03024002030030904c807943c0585000000107031280d0940c014018542c5101460310414910424041c0b20340da1101100841c040480c60003c10300085a401304044480056086d5009030400c0203201324818046421030303180c80450200d8030170016120800041c200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 689455989 1250 689454739 689454743
    0x20d14040c03080904060306110306120d02030304020f120102030711120a140c120c07080c01051c0c030f0f06180203160e030a0b0106050a12060617060a080609030d0f0603 75
    0x1d4001c0420014000d10064000540003d200003100d1f40c2d05d455000580701000881c1f8603c200010800c403070380c50800d11860303a080415000f05200788100d08085c1d9207100181001e845020500e14004c3c41d66100740040304290442c0009549a04111102a040a05546140ca024000d002400052030030300000d8940c228106e80d207001281081c030b00d0307030000c550150413050b8090280c5100d088403400400300801d11244008004d2281c645029200c07030820b030814800030b0411030204100c030404400310584400071050300c0c80000e100c0380c03c280260b008015000030300c441941415501c048020f100d51061080b910580350101e04d04c840400d01a080744000c5885000111007240c0540d0940c1c0b00b1008005900c5015080b21413400e6542c60780f500203402603001e50001400046c085048613440884006048142001032007030030704000024002d0710000d41e00c84400c11240340050483c4d075a00116400410300b041c25103205041c2070041603200d520400c1d54200c101d080c03042e040405501481844200c035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 689457239 1250 689455989 689456003
    0x11130302040504050a02060a02030c070515030403211505030609071214030f130501020c0a080d1101060f0608160903050a080a0c141b19060c0510050406020d1404 71
    0x160555003004000c020160050b1810f11480c40740f00c0041e01d50000405030101103070003c54681440d419190314180450708000e00900c181904500d825104030262078110741e00d4202501c02d08400b8501820300e22081161039602414407205928503807510340d100c815220300f45c09641a0b43d4960b1a042d503a000c1902c100000c83c45442808408503201c00304910382d4120003c140e0340b4194046e010320003190014201c1c0c851082401c0400c1000c0d6804002c0c0c021540010741d014152149440001610b841d40c1001410034401300c0786801c80310b08000e42c01000030b400800032100c50b55460341c60061440104503130030f07415082e804025810390b9004200d01d00440340d00000604001b4002c0d903c00034241c000421034814030401800c108000b4846a041031180300108004011440d212145d40315400f460590301401244084000311840300d04042e1403013691894181382e02020101d180c01481c008410702038003141c07443c100c280400c005464000308201903400d40140002c1d0012450340d111100240d400500513 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 689458489 1250 689457239 689457277
    0xa030b01021c110d050903250e0f0a2a080a09050a050a030906021f021312060509012306101b03090509070e0f0904140f0307061d0601121b0e070311 65
    0x3100c505c1c0c8c10f840c031f6260385000503029075581d09140c00c491420381e401c840c0500c04508110a00c0c94034443d462030b1b008410100c4618248145600041d240200079140030041d40100091715196a0f40120503030590010868980b0315844c10202e07150054000128005481880001506031000480001c0e603008070030000c6041c05170518400c0203500c0740d000341c0003508850000280e018510b0032440080390007004041010701d00594100d003110303000382c00d0394541c00031110b00805004039818015407000e41030f91b0f404401d0b80c450200791a00360466070390482d010b1300700d100307a001c05500c0a0084226a0180c0d601d009030b44a00000740c4082c0e68520203560801100c1000402515010013810380181c002c91242c001d25031000d00d110304084201d40105125840001e014042240e240300e1041d2810158a51105082510b04802d817600c50600c201400c021412607035100344000c3c008081030a284000e1605102c954031440c0c180d0520040740c002011074034100701d01100b2042402142d041c0b0742d00451290f16 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 689459739 1250 689458489 689458513
    0x1c030207021f02100905070b0d141b090d1505070f0e0312030c090f04021818092e052503050712020c0f01090b100f0501050a030b01021c110d050903 65
    0x100030b001d805071594410500005151480c00300107000909610101107000d90714102b44100c0c846015101000c40642c0300b0540c0d000b2000701c0251a048181104d400c4241d1216060500c0b001d8241c0f851281386501d090140b2a107140c01c100460040c0d00e4946400c074600d2090410182c980048029090306600100700160b02509000c1c02024046402820600701d04034060100d8126000318450b510350b101c0303000c15082030703140100003003d6003010454548881d180100d00103441e004030f01144540640d43c028100201c0200e84440d800b035a0480c0c2080100d40340100354002c51104124580340f00042188846c0c8150744a8080e0702d00c10740c0c00ba11000e2901c10004c2c2510020742c0010741c48419409003070300036280c0721800c2c0102500301d8024021001c1038245001c0800d280303c0035601203040c0095000341003000da40c1150907125104260708000a981200781c00603414210460f01180e0340640c580415000d0720741000140000c0c00084088514100c02c0c032034103582d2481200061581540306103e000a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 689460989 1250 689459739 689459741
    0x51602010f0c050601060908010605040506060d0c0207031b03060b0603070c11061209030c0c060406090e0a1103190b010c110f0d0c060201240e060f031c030207021f0210 74
    0x2010394880d203000c4030342d8055074684030305010080e0406000038103544800c0240b07540902503040034080440d02084a401c0200024400e0300c50080750f6a502501c94212029013402400004019500134000950f46d687e80c3c0c0f140d00280d001800200c500c0d03403601002c140306007400c00c142c0e0b10640c1e07a46c4860003600c0040e1207400c07280c0c02d090612a44801d04120111b00e00e811041c01c28040d032040d00065071241c0280704e21038103018203440301c180240028001040b02a9115982c1c00440e4160400e41c1e2150f00c4403010400034214407090652014000401e00c04405004c41c20307680c000d20701d000c0400000b00c0344001111000304040001c2c003444c81c11a9808032070300d0039080c2c035a00348a00034030051b0940c4e882d5642c00031070740095002c80c01507503403074058079800f881d850403019007042003029003a020350502201145801c0007a02c814014010150740100e039032002c02a0614082208001c0c010311141103000402961102004034000c4480354940d8201007113442000c02180503a4004c0c2c00b2000d04508084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 689462239 1250 689460989 689461007
    0x1e061305240d09020f04020d05090c0f090a1e1d010b1c02150c0616020d050307050a050c1608010614040b1f0201021315030518030409090602040b03011403060705160201 74
    0x40d92117100441e07818419603a03440102240341d09040c4c0460f2910b00805694204280c03d00498050000c5000c65180c41d910a035200b94080d411000001f800f10320039040390000e54040030080d001a00c4c21010900d9140040117010034030182000900c00c0c10b1031803091006404008403848949460110340c4401031500e000340360115008800702e2806d00080c140c4640c42c00301c3c00e48505c500c8082011030907400030750503c00b1001c03809840c1002499800c0501e0020203a00c2000040c00c02c00c0004294544603a005114480003420030380884003038240c4940c00c0c180208003a21a0600c050100481c2107420309140c01038140d00f100c010712001d8007070540a513840c2d8540304d8020700d401315542040703098a04440b170310225009d8800791452070505000400e0140441d00c0c09810143d03078070116203005000038000001c031001c3e540007402c0407400034003a01c2d00c80003a0043e508400d62448001c80042065100c04c2c41012240b0011421104642c4460308c0603105031003084401003c214450b4800b40265000d200c40b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 689463489 1250 689462239 689462243
    0x40e18120a0c0803040807120807050d0b010c050a05010e1e06010303050304140d0807030c03021e0f0f030901381908010c0f09051005091e061305240d09 67
    0x80b5004025650f6282c01580c012582100d00580c085600c074180001c611040708101c01506055105084c0741102501a00411582c0c9605649900d824940c5034461207030070107056405402c6810b0040c052410a01800300310a0380883c610804228ac0b0b10300711000100d200e59000b07480900b14507401d603181101d0310b90005200743c8001d0810710000f1010201000340710360214890361104901e0511080040c1074171203100b034582c101801488402040c084906031143c2c0c5c002c0213403405603548181c04001080340124602100c103041c0100411605000641010314030314600c40c0c0d030f04401c00300c61400604090310102000390200d03000c03600b254142040040b503030584104006404000f42c0d544000380c2911015201c050004070040181100e058112580c500541411a030180e143c0030300400080c8140101014036100340102c0f103101c40031a00f07000d0150f103003045c050485551902881c07401c10a404039441154014200c40c40c1d01000040304880759880443d081c82418030741045250640d02030110900d003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 689464739 1250 689463489 689463497
    0xc020a031d06160b04020301110711130b03011404111f031503020406032009130f0c0f170d050f04030602130906090b0f0406060e1002071a040e18120a 66
    0x8550041d81c03442825a26511544030013400e898944141801c3d2056811004900c0c81e003441b41000117000318000480d1040d00350346034004c040d1107403100f4001c1c01e01c0498158042d480c0501ca8030400900c081080d200e2401401c040c0d420400410500000011801c2204d000100b150704002c40c0d90b210350402c021030307024881c20b50030f019100d40004040b2401548201e0f00c40764403402c44000d2003482c81100e80c149408851001741c038a490240d40c00e04003100c5000400d00000e4003024010085070421300320240042c000b03040510398540c0e0b42e098410088a02c00c8134648921101e1070341c1e803403064084405000e180c0e1402400c2a1551391200040e4010105402191490720400710b064040c0c0e01c034410060201c0b00012802c0038003107060042d075640461056018504040e420310000f078010398452031150081e15003140c941e9104401b07e01700071031a0030a0708882c200c0944072011403c50800703442940c403e06040041c0b519044100032003200b14044c07082c2250402d90303484880106000c0030b0607127004603080c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 689465989 1250 689464739 689464747
    0x130203030a0807210b0906041103060103090807051518030301030c050906061207030c030c1803140f0105010305010903030506030105070c0602030a150f091113090f020906120702010c020a031d06 85
    0x1140c50840d11681311054038544d0380070008818a0514401500000180d8042004441480c107490080c03100415003030605480d14845c0041065110445510b550010182d4089043c070741d460b80c0f00e10302c00b6030760441000e80130a8101000c3d400401224101d0354480f0410748110700d09000d00030701080003030806030300480c1030240d2003500c0c4e0500c8000d4410f220350ba90000b86c001c62014060116450f07907000f9820403420070038402005547d1f008101c1a25000500a1207005121119600d8461560484a050b5080100000c200030054100e0b4041510a032010b02041d0780d0388042c03500300d8008031000d00014884500f82c0010902943c02142c002c02c0d43c02d0041080f000340030700f40c03219440c1075110111070040a03074100680a9144580f080b00c0110031802490103d43c031101d0b91082c4002d000d0660200c1c0c0d074078600c00c4088510350448002d00d4001c0c0085466400074242c4038101d1004a0715800954200a860301d9111305c04150303854442e6154440c1c0b0340491000d01b200703020300c030503034240350700403100308 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 689467239 1250 689465989 689466017
    0x1c0b07120207110a081f02030a090503130f09110a0c0305041a03011e0f03080a1b08030412020105190506040e0a0f1241180405130203030a0807 63
    0x100041010a010350100c1103c07045a006009100c44190301007003841d00400d65480d044002601034420303501400501503140d0300d40c410b8040041003080700003080d80c440000c2d10542035020000c450119480310a0b02174043d9030781d8030a80240d8402130f4110403006000c00045003428090414a40c105020303240250034242c542201074040e0a205400100e80e2002000402c5a520034043c0b11a401918005013910b292030072241c59801d17080c901008282c608085400000c90703104059170a072400c9080080850061141424800d0343e00c107076001d450400c041802495000d005008940c0110400c02500001030f43c5004514004c1c9006820780d0b44c01f548421000025400030001e203140d0501038000b0b0109080c042c540032400100c245602000c0c80403900031034420003d01e982c2a1104c200304960759014441c141e2400f070304070112040c501d40108000c20494141c0c810710486103002042a541007105440d6000d403054801c110402c000d42c07651007009450603440c41210b250341c2203480c0341030441c0088807407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 689468489 1250 689467239 689467241
    0x20f0613030824271501020a081e030a0c0201150e15030307060518190f0b09030c0715110312040f03020a0b040f0308180d050c0703140304050405061c0b0712 69
    0x2a4000c004060308a40300b49011903418048245c001070501840c284800c80400040d4803810456409000302c8800300b0a4580101e42c5403024008214042c01c4583d20700d0103500b1071004181c00f40440380158030304002c100c0c255101695207002d8950703510300244c4540d80c034040c0c101003a030440c00151b0180401d0000d44000b42c8c1381d008250054030248601c071110101c03504d62614185d08038030b140403000c0707940c405040890490180c4000da10b03003116444001e40d817091102c600e1882408045c3e0650300c500c50f000242507004900e11000014166500c1200041c051002c036564001c040c4aa400007000d440450000b8031218001c1241c18401d00689603295020b80b170704c1c4c00100c02110281c4105030b855425108165004150355807100d24101d000c100800711030b0703403140daa9000798040303001d1210028442c905c40c0410003824004540c010ba9841041c3d2082d01c9a5850b42c12502ca541d0056090001043c120320342801c685800001c07000d01c0e0008829103841d40c1c040001c01401407010301c41101429500c00703800d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 689469739 1250 689468489 689468509
    0xe070306021204030e03060112020d020d0506090d0f0f0e040f0b06120406060510020a02010315180204030c080a120c030c083013031d0907020f0613030824 68
    0x550942c00c0501d411304000d01110111010144241c000384014094040010402d4080070340583e20980d10b140a4030105020310780c95040540244105010880d1192000503002440c21081c1d503000c400382d4910340b081d10240070094030007000c0f4211444521841c00e10b80c0c40b50045203002c0d0b1021941d19040340229030720b135000030044180180c440003000140800c5014446c01408107482402512040820094440c41c103444024105504c5003040003c140181e40d4050141940ba17501a03042201000e5010081d0700c01d1104848460b040600018040c9010515001c2c582d004618403400b02e00305070b41120700410f0f0b00400c600b40801801880d004c2024100a49403c2c4d00d416007a040742c000204c078841740c3d941c880d920403658072180403c010008508180d03208030181d00d400c0c144003a05683c07580d181e41f00040a0059008803004040060480d0f0008002c1d500c088403406441f03064590911200007140d2034040a40400c00e000041003c00881000303049003108030205204244540b000028800e20b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 689470989 1250 689469739 689469757
    0x11206030c1502070b090603070509030a050d0c0201080f07051b10090309031a0408160c0e1f08070f0b0d0b1201020c01181709060d181509150e07030602 67
    0x1841e415011040343d0100719904c042e1009001e05802c0c0390811300002c21620000740017404108000c1a612195101000605800b40e0b0040c150b9040d4014428010b05604650307900360300040555010900c2d00008140260156010303940391880c00448681980800034801403000c4a44558800300420140e03922400601a1081d1f83e0108511300e503040c68144c01c100b0445c0042e190030f81105000014003000211001541c0c8085869046a10741c102100008001d9004142c040c41c4001000040441c0000d4070101204041c2c0440b400340e02d8000349917440055014440c2c0f60038190906101003c1244060725580400c3c00f03001c124800715502090030200515501d07070190b174021908803101c21003030088510000c2c0c0e1914003030318120585c0b200006030003140c208d01003103500000c246409032130f03040880d83c034504249014090303101ca035045036420066001094400c001114025601c585550050006141d0406403c14030405505407080c02001411050310051045401c0000000c0181c0060080030b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 689472239 1250 689470989 689471009
    0x3020c03040f080c090f060f01030c090305030409060e0c04031220031914090f06030601030b1507060b040c0806191d0108010501050301140a0c050409110306040f0e0c011206030c 78
    0x8600602444030801d000b810305006c46030303030707900300079841c0c6805801c1d1420000910f00032551034020003054503020260342020705503001c00030b0302207000f40b4203411a07000c1b540c00c0c3c802c55420380c0d1145600017070350007580802080a0f0305001014091031043d009031924444c00c03d4010221120850030b00d10315030040d0a00c003105242602c0864245030441d0400d1050800c003123415250542450016580101d100540c9120b8080400460b0640e40300e6030050520f0724000d0403141c81000b00c500054405d820199046072228117200d40241281807d00405140200303588a407102c2d0744409042060012071081d050007200030300500000d055100ca01010070f001c2d100702d5451042c0d410640c0640c00d440050f00080e0190703040050580c01e01c120090385a9210a14100016655481030b800321003e00c1150f000480460401e600e54100f400450001d40c0240c404540400100280d0700c608401d0b02c100c4014000c45030090710041c955540194403444140c03c0c250750001d01103480e0f9840d005100d503940c00c242120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 689473489 1250 689472239 689472253
    0xf150406080c0f0907050a0c08090303040602100605041a040c030b06220f030228031203060612050c1602041e06050a08031213020103090c03150f050c0a03020c03040f08 74
    0x5003400f03c0b0004510f00140c1d441c030380d1032800ca180548036100708800e81081120f0100e504090008000a9a80c4030303000406483da03480c0e603070800070340e10b6107010700346020a845c003100020b1b00d19080c801c1c219200f8040b50040d800750020030800c0000d20003550b8003000e160312911008619550440102040078201c1c81407130b01200d0091341c42d03038082e00340d8101c0f2102e181d0030345060000d43d42c0d006100002641c010030140c141c0002150408904600d42d0005214a030b240940c412940c0e0583c208500741d8110b503842c44009241c035498003040d1038003a54140c0c00002c00b00a6003010390014018980c5c0140007410100e416010680016103c07118000d00c03010295039041b0921076854002c00140041c040b1030010341c2403002d144069080c04401525070307105072030185641000c6900a41001c0082c0d50046e01ca6611641d40c1e00b03140b40342002913440007441501e02585042c5849841c8519070040800d005e41d0b0741032283e140400d030000d42c8801001c0d80307140b109000c001581d0440ca07003c04041c146083c060402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 689474739 1250 689473489 689473513
    0x609080f01050114040b210703150b0d030e01180b1b0a05060609041104020c0106050f0d05070b0f09090108150a050105010f0f0311160516030203060f15040608 70
    0x102440e12034840c800d0390515004000400111401009820040303030009401c0410000281c4156a400c48058a840c030035681c000c210030000c0342c6001220300590035000240329010004045907089800d10360300500380700d0004040707845440801d80383c203410305203d034107425007007060101042154404a08141c00003a100c460403805201c01e00521031050003020581c8166881d551215001415907018019401c00034051040d000a041c42012018204540d2018800d82e264041c000d140036050041e801000d5925a034184a40742411083d0400003808900e4140b04200a080d0320251050f0a041c6e0107101c2c0030f00558034507522500a1507074000902059002554001c51014020b00300d541c0c0601d003000400c6540d80000d100036034900320b854928803100c814103056000700340d100d0907076100c2400800c0800044003803580300318185005034200c50f20740e5044d0041009408040c0030094054018001248540f02680c510070707005a41103041c0080545a880803600321a41c0d03511040141e40003011045d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 689475989 1250 689474739 689474743
    0xa060b0f19020c13020309010231170d050306031c1d06031003111f170c040815180d090504150f0b0903010b1009080d02010c0906110c0406060908 64
    0x3000280da400600b69100c0210b00041d44c0d90320103079114a55a80000004901e035100398101c44e15024024003007400c13040e0001002d408116030003521036500110700303804900c10140a070440c600c04203100040150b200101d4041b9410741002c0d00743c2d50948522001940740700201000303c54156595901c048080c079038030208040e407113101c00003940031300740c00c00600081c080c00402c150181c0c0e400649080705003c2c0c0501081e0220048008400055060081d504032140e0040d1281120f0300d640c0210911034560b0000c1d560300340f29900c200d100701d0344102e1390b0144504070608800d5118103080c1c04075207900c80b0364034454100402d09060900150b801082401249424455100d00c140a210030040c81420100741c0701c180f101ea80901e240c1034401240e01c988681e425004032964800c090504440f022000c0c50140c40a64240102103c40c013880c106030304403500c14410103038100c99070b07950342503218a80482502d00c00001d54884419003e80100e200c89030f100d50050310001c003401da4402404602d81074010b8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 689477239 1250 689475989 689476027
    0x62103030f041707170a21060906050402130510121b0801061b0308060a03061b0e01170106140c032b0204050a1e03050a0b041505010503060403080a060b0f 68
    0x204554900780100750205001100c001d044880321005c5580e5140d40c40400e03504442820340b00032103d615400580a0310708a6002070044a0070001c00348040d03a100e4080000b03901528650320a0050303040c4d000c20162600c54100c0d2a490050f0805254003e031409680041c2c134111141003c04070850011865803540c041f4070503004000c24039201319054036102c2245541c2c860000701030208600000800c0b0a542c429298000440e8414001c110b104201d84d0b060390141401065a00443d03940d011135506540500303117080c140344c0c03001d1a03190141c3c01c1050a5400e0300c04d44071301e92004281402001c00460341040148603001071120003898171300300e8908180d44040005000380106005010402003a00e80c01068020340d0841e00740c040041c00f940315030180c00210b03644060b210f03210306802c1405103c40842d4046c055400703901e1140b0135600100400054540a10555800d80d0001c000180441e100b50107076a045201c524000c6400c6603914030700d070001d801602811902e500300190840c0d514070002182 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 689478489 1250 689477239 689477273
    0x405101706091e07091e0302040c030501050603040314090901090516050c0c04050c12011508010f06090605070f050111120a05062101020c0a0311010c03090209062103030f04 76
    0x9000103107001144040700c5a100040c900c480d003040e00100c1d4049000d00140f00c040e041407281c401d1b0341856494507031111a0f0500c01a4090b5181002090030113100c0e00801b4142c03500a8100c1d840c58840e40d4040360701a405840d90a88400d00b4080c502190b5034648010740240140c0c44e0101c0c00381884480540038601c100c40751424000f04004c11134014401140d4581882e41c01c0b600000c8a40e11511075410303a10070300b4411002c0c03103020070001c40c031540f940c91130400d10b42da0f41c0c1e01d111071681c030740c10203042c03203a0300707014642c0811b961400c20066144510000e2800502c0303500002d0f00e0b240c290b03a409003507039101c00b041c801242000c80c0740045402d8106034250702c803602c810144094244000841c040c003208540c240810301251200d241509800d4048403a120240b50407240100001d0800070700c07001d080703400686154249010080301910038003401c400990000c0c40303545603894000030491005c1c19000c401c4000e481d40b0b4120a2003007014409907116901041e040d05203803078245809042c2882c11224 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 689479739 1250 689478489 689478499
    0x80405150a02040510020c3f010c020607032a05074b1b03050304180605030f1005150901090e06070c030909091403070f02130204210303020405101706 66
    0x742d010aa4845d00041c0c02342075520f0300100c05e110020354620480008100d02da514850b51a40c01800c411b056005d0380030001c3da50b080d609551a820b002300d00f80d031500541801c501c3d07008070100b628150085074801d281095428800e10380039840d40c031140e83c40f01401641030b252001d41c00c0f001c0004840c009495081601c803a000140341c181c030040e142c10b01c2400c00080c01507001c10b0074001c054044651498055a004012291210358582c076002c012116103884050aa05020300000c07503080000751a900f01c01e488000d0440b41040f00d1800009180081184115940d0015245030307075219020b4040c041c00040c1d0000c100c0030071183c4594a03100000c0c1c1800c0401075404444c1e00865030020400701a07802201000c90407000a00349a009000e6501100405000010342c1208102c405803012000c18030986500c0003142510100c20120700691041d220700340c01101c0d05881c030782c461205407004079100b8240142801d8841c008544a003603600c2c0f811003c10860410f400094402003600750f80070904a0f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 689480989 1250 689479739 689479753
    0x1119090906060302210406150806090d03060e1b0906161103060405190c17100c090602031b10181e030509060d0605031f05010506040302030706080405150a0204051002 73
    0x250505c071608800e0b400b000d4604207401040800c6456041000b2281424000c80480c40c0c680d14165110f041c2907038940502d12400441304109802070140204842110702d4910581d40d07800c9a004140c01015403841c40c0200400840400e603a4000c080d0001004000c01c0030030020b083d2a025505e0100044e0592296008104000028800240b00c0d1141800d03240c080100138030314074041c07580c6101e6030458500c40d004044c0f000542040000c0c3c50880c040204024030003800441000d9a900016005501c0103800030010640e800310780e041c9448620055200f00d84030080e98112007002c694225091011034030f0310400358000e0105c0c8026641c441c50b2a003260b40c0350a0402d5901a205105064196014075800f2881444030080e50344420020300014050311460f0700b090340203082e0800e000c8001d554492074140041030b58200501940c06607603025000345041c6091480c296940c040c024030480c2c09101e500c42c1303a0151040d204110b400313015443e10242e1114101001c1010760b00c5c03180032200c01c43d4040d80c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 689482239 1250 689480989 689481007
    0x708030f0306190b191206060e0f0102030d1a011214071d041113061103070825061b03140a110904180b1f0303031119090906060302 58
    0x2000300ca410440c101c03400010600d040348607a90f03049996019a40740f502c0420b074840650703d101a413000c040910f5840015a01607a0203180848640b402018005041d81c000340c6d107a802e001d1510440343c03805004484c14000d10201650507500c903000c6403148145400f02c0050a56044140104d104980c0b45061001c04403080d20261351040052203901040004031105008080905c141c0d103404201510500ca0103111a8490310760f41e0115500d00e02204450b4030010b03c5500c6040d0305950b00980390050b500d041d803180c0341e248154001e040354458807058200414440182d5450700c180051140b0404110000c100700681a50552080400149810700a544008166410499a11200318000040c003800b880380b942c0c0b10ba001c0c1a03400c58016150225952401c60a0164080d109100b030010110360307038400340d580b06803c5440d40f10012205e20000c0c107000080c005c1e000a41c408010403119810306940c55868a11000c01580c40d1012501e0a41c0030b000807000c03030280394041d100d0384c10198900300b001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 689483489 1250 689482239 689482267
    0xd151b050711090403030216051b120303040209060f1009060f0f0f2007060309060c050a0c03030902030c180708010509132004090c080c0108040b06040b0d02040203090f070803 77
    0x42150b8600c1951448002010107010b681070351201c0e00502c005e90760f081c0d410728141e50341e58190100200601000b58468401e407400c4064030300c601c0380d100003850440e21503600380080b00d40c010340b0007684040350780391083d00340d100c9151040022081d80d070b81c07948a41c5070501c0600280f9407803d11208000740853303044110b9400000d42000b81c404d61174411074000c6014070119034440302042d038030715900a420300055076a030315402100350a400303540108840304a55034203940c148240c1e0010808520380105036408680641d0180a80740d0000c1d042d03840001a840000300034000034107510450301c1341202445112640400d8081c0075280a4814002605007801c403024070314081031008041281a02d012440c3e43d0112210590f20140600306000c20207851420500d00742d000c0c010491107100f0100760040c03640c8103410302800350f0341203685090707143c44580600024042c0c5012007078006481c21010401a152407004510403080c0001600c0c08480c06e1030510308000b01d82c3e008040e150701c103200240d840c10300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 689484739 1250 689483489 689483513
    0xf03150f1903170d110d151a0a020a08191209050d050d0b040203010b220501121a03030a02071d010605040b03250207080f0a02060a082211150c06060402090d151b0507 73
    0x6042d4480341c4404521802b246480c040f840000c1914070085100d00d200e0302d103030900b009840260f850f040480090301380d0650441e000600d010b44698003007000081e266011701d0040104441a48010a40201e484041402d0780c0c000e900c00d2043c0440058000401542a054030b14102c03803580074800024500800241200125002c0c007000a80d40e1501c08040007058030703224100c440141c182d944410102401075103d420601c01c28082c107004000c5000414103640e01e0a068038402d4031482c0c10b01d41005070034119604002d02c01300078590034141d00044003406001c821802c403441d030b0040510900b42204d503810080c5455161405520214079800141c2e0f900e002c0c4c9100d0405480d04070b00c80d58482c410382051510f00e03c90a039078400704208031010720015246500c600e01098800340d1103c0790b00f04188445104003541e403102c80e04114003040640c506034008141d040700040ca04144401075884070400c86a051120841c01070382d03568040c241e1407400d12003034626110b60070b1403400c1c0021a21410358001d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 689485989 1250 689484739 689484779
    0x1120203061909020d0f050f190f060906090b18190602070c03020d060903030b1e0f060906040e0105040c0314040311030f03150f1903170d110d15 64
    0x1000401d414820201c5612143c10903030020710018007a8490b080139402030a00f010252294029800d6400e106d200001c0c850503508007180075030031818019128003000840e5014101c940d691907003859804a82d160003000c1c1000e0281d400f508403405d0990003040c00700449030009200d600280c001c3c00c2e120700c0018000c2c81054020101503658100c5e03140c1740c4a1138206400081d0310055040d040030601402d54094a2518884d45003000110201e03000c2221a001040000090900411a001181c1008054049001c0303020703700b142440c0000700092a650413540001985503600001000540340602405080700028102040011226800301d04040d400810250031b0100d451203850104a00300200e64441d006150000e841c0e0a04403030540141000300540b41c412a1000c0d41c1421902c0d109602d4541c1c039050746103146003145595241409500764050451498400384486040010707180101018032207403010403a0744040d5001c0e91002c54000100070101d041c80390005000d40300c0b158901c003803528 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 689487239 1250 689485989 689486011
    0x909020c010b101e020c09130c090f0903090e0105061905071e051b03100f111206031e0606010813050a0308011712040b0306210c01080112020306 64
    0x41248580d5502602c140da10b025044002112441c034600c2d03001001880805070141514440307215403504076525801041000d9201e1416004a4264030a040c0318800306840344465200f003075990400b00048480c4800300c442c2e038945a0008204243d0b01015013409000303807002015255042401048090103200c1d00807180d00c01000a2110141c0144192210b241e44540c00001c2e4840f009100e400400d0b8040c8101c41c64404d010007280d8402203003004600c4074401500602c3d00b010030244190180001c85440102d8554a114100404030000d00034414800300010807022810144140b6251401c800e081c0c0c210754488500200041030701082154000d4000d18024006884144124042125420008115200e03030b030300150415410010080c100c0c0c694075500714442400c4c0e90010303118244215040c0f2501b4040200303019541f081005142c001d10701074a08625201e60701201114000e0100311340007140c0c0722001c005040c1d0b03800717644d46015112480c1f285d41804580c0c1c2c080381c0e803148003030942a241 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 689488489 1250 689487239 689487247
    0x30c0503071509021003051506031005092a0703050901050a12020705011406010f052205090903030108330a1b0e04180302150720030a1806090902 64
    0x10050030000d03a00c903150042200c01d81001000c0180c0003c04030441c080340207481c1811140c40290180c4039041c403800c10200d900440124001c1004a00d07413000b850540842c02c60034000c01c40d51586001e107407081201034291540580c5481080100d041da440f00c20380e1b130038010081c800000e540076054170070351039081c240b007500c80540c03500a45100c9454410500c19610105800d0240101500301400c5030803001a001025240c40c0011a01d15150030742d40408980100f00039a40352a07101c0100a280358a05900e1034044d45940001e5155001a210901030382c3c004401442402d00500141c000003a41d18070b2005d504164401140e0184040f03040c07010000c407814009216008560483ca0718080300750890344104c5000c44014081d5160110314034007039891309000792444503126242460340c0341c140e00240003805070034500f03402101000b090302003040a25018541c4c5100402c3c2121408440c40b4013031034568001183c020b2141c626242046803010300400100702240c1c2112b40002a42c021600240ea6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 689489739 1250 689488489 689488493
    0x60a050a090e07021506060331050616080f1003060b12010c03020406030b1504051c0b01030b04140109080904090203070b192d08061c0b0928030c 64
    0x2610419600903010032200e081005802d990108070003890030041406141280c1ba02014040c207400115180b4100518110030310b0020304017500d40700300f440600c0460648081065480234100042551901d00100b00c84d246000c10302c0e08541d403507911175640b8882d0486443d01201c80506c0c05c060703200c0901901c0e0f0b5040c070314104c0d8880940b5a201428090b0003404209140d420050003507200c2e2191000007403801002903030a24212004900e4025030600c0c05051904080403c0003c2030040030300b140443c0010b032414001510040b040c1d0085000c2c410104403450030b410b04840d82c0220035040c14407039150181c141c00103102001501c600420030384002500302c82c00d101003441c210043e086501d0b4424086a218400ca0700e58a101d9521083e656a00001c107070f400c4840488104c0c41c040e0509003602c09003014102c0f51003690b01d42e510910040007030340d46195400c4d00c0242152070540a440c2a10144100141781c4070800540f60401c0302a502e604510b260300360300c400451a140e2008081051400c51581 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 689490989 1250 689489739 689489747
    0x706050703140a022e0b0102011506050c070e0a0c0806090402100e0102030408010f0515011404031509210f020c0d0b0402040212010906140d02030303070c0602042304051302060a050a 80
    0x103d00a08030351902c03c076a460507107510101420301c54001707174641440c2d083e21302948103000300711303055943c071191000440c20124195865000090465031130b200e41c0340002040c9030324581041c0140c80722031000850981c41340d0b0052a8010043c80b042c014200d01c1d040c0b10060325960710403d400e5065151411407549403200413030652142c0d620540d80c030340c2003c4031001e1151007a80450b00909101c0403605044102000543e40740014050400210300180410004603806a600a28440e09450002200c4845a40b81c010304200c0e070340880450680106880c2400e42c000d40854860700307043c0018201d407480440000e02040400700028a049400070218045444640640704081e0342820f0a041641c1c4440c1c20b040181860301c580e0b5010f00c0e0800c1015400c1c1400c4020701782e82c9801902a510f03603658250151800e0010000480710300307a00b04400640041c1c150604c0d521104a100203140311030101080105489006d860503d40018a010b4000107030340319000c4600c40200f50400030b4070b564001b40151 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 689492239 1250 689490989 689491003
    0x20c0139020f160e061801060e03010209180f0711101107050f06070f1d060313080a2304051f03020705070f08160f0b0c0703051209030706050703140a02 67
    0x1428031075401040741c490443d0503440181e5000304d449440d075035501002c01540c01e55185d000d640d01c1c00010010f000075440380c80000039040300a0300241c0740c24030700c0d00401c000c42805841c00c160021088103024042181c0640903801c0310322071030005400301600f540b90385c64003150910084800d54880e01c44090024041c25521002c1e00304060399440f0318203010301511540111440f8000500d603a00c41c0c6025800b07030346040079158120002034580c5000d401840641c0c3e101070000790304100030f00000d100241c2c1c00001481458025511002000e81d04c41000b40d15150407891042c42c0e2000703020030700490700c030b141d0485501000007108510565541d00194001d110300000a0018095030b40081080c0c1e04031103040040364860b074211074100071158600b4414401d42d0007400d17a6010450400c009140e21000504000d00004064415007581ca1741c0300c84c6000c01d0290742c002c0d001408161000e0614042c451741e0003c2443c1d041240c81c003201e9540c000c1030f40035140600211910085a05041c40b07100f00442 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 689493489 1250 689492239 689492263
    0xe07030602030a020a08010e091b010203160302030405120a12031d121e033601060807060306211e2f0a030809121f020c013902 56
    0x210340d20f09045041e80042d5000001c400046000c0400010300ca04400c0c03200e074802c03d020005458038420400207544060198440b490441c4010b2194905912411402ca51914400d800440e039461425040c4504451030010780a515005100300601098400c0011032030303a85146400920103001c03901c501030354001d10041008511450307a0001d09002c400b00202600c12040303100d00500902e00b80002031302c1c030044401810598070105a149107805101d503104202404032000364211000e00510307400c44034154460801c03540b013258204640398151246501a003400c041d91002c651180c2a021910b0700480402000c1400380b80c82c0104a0000004c0100003c5c0d00a070020b4048107408042150800c0c031007019031004400221030b80c034500d0001d1041045aa0100302c080c10800b103c000c01041c0100841150854003030310f00002458a50440d00407403558007008010707160070140d00182c0c2110821700c09028011035207007048100d082d5888013208080e011803240d02100983c200c04a040070910014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 689494739 1250 689493489 689493491
    0x603070f02190c172b1b11010c03030b0607060b100201020a091503020f0a0c0c08070f03110409051204090c1701121b1d0f0105100c05120a0309050f010c120e070306 72
    0x66010010319454030b0740f07070440c9994411449032071b4180500c440403401507008181c0440f50a40118550103040205101030203401c0004001d1030792000705010742d0166400310345003540c2d0000da0045103062944040c0e4080c03035100850a000b401c05020b40444842e0180706c4400301900c400b003010600c00c1e011900c240e02c464a440c0d44880305d8980240502407000300803a44c5841e5000041250440094070390204c800031001580074074a1030b200e03804d084e181c800381d10781c001d81c80317200201c0426800c008244903e865442002e0b80c991400c64500c088a0070020b030707039041200c107034824a046600c0c1500f03241994052100e440b54201360b858920144203400144000b990b451060016100a02c0fa17144511142e60080c0543c00d90754000102540c801c1c240106075009400b26000c0346203a109030880c0c40711911640866100d000c88206a040300e404c242d48090010307450303402c03020810405006045001a50800038044415603c002030281da14840c000400035544054410100b001000148021038000034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 689495989 1250 689494739 689494783
    0x70b071404090c050c0f0c0109061803050a050618010513021210050c09030706140d02160f0803070f11060f0702010f060b090108010503030421030903020603070f02190c17 75
    0x28000e0000e8200f1784403500d041c01840610100c1c00340204560b80070786016514011a182030410a0340d4951802c00243d145420a60340840001c0e000c0010181c240d004034000c2c5418500307900301c40c07814501c1000040050341468148951f034200ca001001a0a5044484400348150001060301c1d1170848504002ca0f5420701003440f02c40a0070900804c190300c815401d40c0c0340d02c0d442f0030060b591480c8500907038080c1d903000c11200480544660140558040503103078004c1da810140c4540c2420022100180c0340a8800005d100000742c211203407000030211810a0403550000c4805107071603039801010021140082000038216901c01c1d03010145610b176080d000c229480c0c580c00714070000e0300900340150104001b035001007003620b000403c0c3d80c100c3d0b40b160820040039104900c01140807104c000100c080c014000d034040700507134807c8051842449282e07108240074114130340c000d1900b43d106000c5a43e806088082c0408600040040e0059030511101031000ca0300d841041e07031414591b44009038541ca0020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 689497239 1250 689495989 689496011
    0x703050103020a0504020a09260607030c030f0b0f010c110a0b0c0d1e0e010201022b0501210305091507051c0311091c0b09071802070b07140409 63
    0x250085060303074000c1e90344002c01516901400201c0c1320b014080004501c0c1541c1c10010b0100941f10705c2c02e80502982040481c142d039042d864609030b01550354102290700c2d030800205071a45485207003103501c0d20800074402c1c01c0b2240b004c10604800c4a01860402411207402024000e00b0601d0141d942c60240840c1c1e46555a003d00744e505802010080d00280a00c214503038515208843d55651b602c4148491070028a00020984001d84258001030540d502442803941e6481c41c2c3c90340301c00c001f100620303c0801480e00b4603264200d030016041078110f1b4a0f85103040045401241c8418900382d89420080d5031380600c0030028050742452041e81440c960006028010004041901281c0b10422650224076a4400e9810750540c0c1001c0e01e480040340c002e1100b0301d0540752240c1e04070041d102540c1c40c7da000b4001c0c1d8582e82500d00040b62031002c503901c00c0d1750810840500307001d40560003991020450030440c00b40ea829113101409061102005a01140c01ca004034149040740e004180c101f030208404580a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 689498489 1250 689497239 689497241
    0x90705040b030c090f040606090213091b080601050708070212010b0a080109170d0b0306090f1204050a031101140c0604022e110709020720011103040e06010c0b0703 72
    0x15008140c0030360709025840e5102c0c00c0c0003a580c1c0400000800008803a40c5540e02d502c6026001082510600d07160200091001518030042010b440e6000e400c540b2241400b0809068031407401c101e1035448a00a80b411109500150054100c80c091030810743d41e0405080c90000c60042003000395110700d0986640040c0d032415070144c0d071605802d0795086400d5580c0c540c051300b25030080401400380c40e2012070881c5460500790040c486e01681c3c4c0d00025640c111640420302d4886c00311081d1441d0b0b802000d80103201c0600b0014601007132403650000b85040d0801e000b088040b1500c0c4401450803810180309000c1c0c0c3e0240740307450040e101050b4601d803103001a0240a07507503002070301c05a0041802500307002d170110070403520915018007a86600e08111000d03800721f500181e800810b02e603030b00800130b0204200d60240000c2c04039a00420000343d201202d241411101001c000c200c905000c02107003804121600841614112090410726403c0c036941c0400686511401e82c000600210364101006056901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 689499739 1250 689498489 689498503
    0x50d060f050f060307050301050f040603060c020a0501050c0906040306110c06070e0a050a03051b120a050102031e1b1309140a0608030c0307140f1c080c090604180e030309 75
    0x885071115890b8410040c400284402e407040c40014404000501c01030800807858070700381401420004070300f580c075102d0500300d035500000003006820680c2103d041c003100340039054000c0000c6072890328020300d24002030b400b0300c00d520006108644507261048180040030544865002103800c1c2c945030310b400c41000b008a80c514031514071480302c00320041194185108107a05603580527000386000b203817000d621f118607409510796aa0001c0c1500605015410602c48500d040d440b0354005616410648828140104078a403049808180b01d0104203a800411070f0384810100d03041c059030381d40c02201c00c5402502c1d229030010704589040a00515100035610b118920603400c8103010080c143d218000c01d1348901c6940b0011001c6c0c1c1c0180b1400000c6001c170310003080182c074481d00311007005204a20003400c2c00b45c44440d2006883c1d00210150300181c01600ca668440904c0b0245450169100300180f0180114081d010190388a5040400300d892268080c0688040e40c1040700d0301d80c0307800d000d030b250340b4a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 689500989 1250 689499739 689499749
    0x21030f0d060609180f0e190308090a080a05031905010f03030f0c03140903030c0609010e0f0d090905060607050a06061a0f0d05070c080408060f250f050d060f 69
    0x46404400244544105100030580e4201404048040c413918450006040820540e0000c645d880544070b82c2c3c03403030030044000c505c25a44500803410100c0d0030f014002110041590800f50084107802c0d001407801411500044d1107400c0240c0c80b0344a031140409040850309041d0b09052400b4000326041000f1603025007100d12a90312a83c4004204408031500d0000920060102e5400c1c520500390804801c054180400050107c2e400d1010486c54185406810b541c0c8800136551842d0808110b101403200020700e049000040c10340190110b80200f100c800c0d40315020310b0750758810202e41d695a070001251b0240d41c00c101102e2811902d424442c006010380c0c40307004c201321801140c0c0e0104080071001e07669150765242c00242080588920a005424018401020801300c3c0d00034000080e450800340010b0040403000301014070340150740d00000e08003d01240d8462901331058401d84a050010042180311490001046035030301005035802d01854005d4007a0500700030000c0f4880c4101e07031206048034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 689502239 1250 689500989 689500991
    0x4020a2d12120216140d020402070c090b03030a1b140604031e260603010603080f030609061203071119080f0c043602060f070201030f1a21030f0d 64
    0x41e4081d103043c4c2e074480001a50741d0342000007450400002c81c1030710710180c101502500900b440c80c060741c0050100e03840b41e41c0880d0f800550080c10b003c07404151266400011042d0000d40ca03044800401131b040380e41d0602094409000d000301041041130710f03800010307a031000c08110740352030605160160100b10703e14010500e007040c107011001c2c061700c162104030f91b0080f52000440007041040d034014900c40001c20041d05592200e50000014100c3c40c010403510410540d043e440e13040c910308221030102c018209074814200c0d04021340001d6000b00465120a9100c050310014404910100b6400c281e401541c0c1c004180307869002489580c0424001880d851540640e1450007047c002c10080714501005100301680d158115240201e02c001d4422240800342082c0c00001415030000e0101d5008071243c007001d0b42c000c203105013196050b0240039019010080c007031144903000c1107000d00c1c0d44450200c140c0b16031000030401d80d84000503070000d2065480344054135510b035011503030082c107030303004444158040b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 689503489 1250 689502239 689502263
    0x336060c010203070f1803030503101e060206070504030201090905090a1205090a0f06080c030907080304151808031914040611060a09080307050c0c03071404060e04020a2d12 76
    0x143d10886070003401300304c458054001c0e1807c0d46c6044805400040c00081b48140450002c101e148040141101010700d441c00190286c2c1041c030003d0401c100a0f00803014000188410300060780c104140c01c054808881c800140c5d50b4612045a20b010150403014242101c0f60704058001b40d40840240390f844000d4400c3c3c6816075480c5e0740c80c441d10340903100e070f080028042400305880c140d446000b1754005c6c0300c0c40119813041d40c4071401d050079903015500407030b4212011005011a43e821502d4820b10400425450311101e290888040c0c80e445210032241000307007562001550540603200e0f580e40000252881900c89848040c045d1030710a000c80509014401c2400007045404c03140112400980d10504a9045494400741a5042d800c0b07802540d410340602080c00c041a101040090014810481200380d1080c5410511003203a107650000162220308104000150716039a00715000c40d19820140f544048205e4040180d110600321401c41420f40316100117042c030424140c1d04006406107d4034094 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 689504739 1250 689503489 689503517
    0x1f080a060e21030105041d060a020310030b0703020406031439040305010509060c0325090b0a03050a05090115030221060703051b0405180403120f0e010e0336060c01020307 75
    0x804000c0e1f000c04441d80c0108001090611550051038000c80003000e100140c0341ca942e41d55400070812147c90b4000795000c0790802680d43e00d4040e2800b013805d07440300890a410300d0404584202c1d03601c41c0703032800200c100703001d0118030748000070700b02d40c21a00307601107511651a883e095010340400e0704e0500e44c0b481504041000d101d60700044070700a160a075031604003d1143c884406001078600400130a100b4044130000d41c24243d503000304400340203070780c0004080c50a0703040e40d01161400703890815140e2402d0b40d1081c441c03459200071000e6030b804807409072940701500410400b00307429050800481c020007050040e0142c06801c42405900101d004100c05003628170700c101c06014074132609901821075809003078441742c1c00101540090003480d080d0442140410321105580e0410b6224440303541d10007000d913a0030000c1c4036010700080700030042c6162203c528407130108810500c001504109000c4000e0b40005050852102101005010580c40320b1458035018000d400444964011802c2c0d05980c0702 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 689505989 1250 689504739 689504771
    0x610180308090a1d2404050403030207020414130b06040f021b2a01080a1401060e0102160605250c0f03110a050127031a1f080a060e2103010504 63
    0x54528642c80c0058a1540c0d100d184405c008141003d10850410340c0d9102c030b03401e807114000c1c503200d90b000c0c1c0c8016039207800c144113020844182400d824465240b550070b000391045c0d2152100c81701900319602e00e10684442d0f0005004080c5010480c00091000a8090034000d82c2c0704a00680c05101302952000d01181d8101c000200760000d05481c141040280391071a580204c000f42d03040b9400c4540000c0440c40c20102e40c10300d88080e0000d2011444c50800c07030046683c10041c035034013402026010110f580c5040c0c0e01400500400c0380200311581c48140e0040d03e00d00c0144100c402d1034109541d03607003980c0c0c4d41c40000250011400706a4050307580d48041e400c00d0425036150400c81d80d060359100c0c000001c0e240034a400c200a410315043c0400c440c40000042050003407030340460350314801108001d040040300740c0e0f031003500220050b0b1900d080d14800c200300380e0081034103a0aa900104041401e0101d601d4190528610032041c80007101c10704000e60b02c030318000c405181070303074000d582c100710041030860f44075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 689507239 1250 689505989 689506019
    0xe030f16081c1205040f02040906050603010b1e0120070311120d080c13170309120a0f080a030e010c020705010207090b1e060f04060314100503060610180308090a 71
    0xc404207511071590f0541d1034895100ea0703449030040c1d25903039600c42158000380c26640710f000300781c481503203e03000d110040c502845440c0c1c07502000c944d818070802485514071181d640080341d460502080308000031200510300030362050356801200340c0d42950b440c3e18103158504c04141e03200340200342441c5444540b030360000b904c0c032140f07400f520341031115a070300302c0003080c075500c1249038042c1c043d1002000507004089112400041c00c07140c02558860200c00140311103e0010491a0700c0c50f070114003410003240a00c0754000c44190081c001a42d981150b80083e4080d08900782e403261039600c1c1691030b020655020407154141c0b04241d0039130383c865664583c0340c0c05a40035020000d90000100801800030007031506200c848402c064a614101541a43c00080300d800c554010000b02c1e4440c4104800800c0009605510142810405110604017000310b50345800040800c0e020360340c21308000da40741e0b0207040710768074240c501c0699013400b88e00cbe4507080c0842e4000044d840c4c0502240e440206449802c00850 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 689508489 1250 689507239 689507293
    0x120216050a0602150c0d0e010204030203010c0e060f0306010e120a0312110d02160804151e0c14010f05011712032203090812030f10050306070e030f1608 67
    0x101000c0c50041d140b601a1540036291005c084400c00440d841e10000b03014405400c9a414001070300e075403941c0141400d58614a0080080012022505080d9918a015a60780d003000e40da85a0700da991b2880140c0e00907028412080e4440303001800d08000c0107002071001c1d5414400e668800010703036042e1300c001c1034502e41e0740e00000020b008d110303040801550380c0c090b10b03401402c040c2d841d80140d0f0640754051250320a03040724401504140101e00465040104211311034880c0c1428907143d01c04000003000941e21200040c141d83d80c1c0414901d0280f0b00350044400f008001c1e50400043d40e407103494065400c04183c5c15a0a4015581c9010045002809480c42070218034070100c1003049204140b0040700781020304070184513441d00e020410140c01c00c01002405e80d00e00000d503072800e00716000300d00340300c005010054030714102030140402d4402140342d039040700d021b0405032091140c14002234102485060b0081d00c900c01c0c08031141801c0c1d01c9850031000c440380e11068804518541110348210b00400d847c0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 689509739 1250 689508489 689508493
    0x60521191b120b220507020708030a080c1b011109100509240f0a0e040b04051017030408030c0303070807020a080f0703090506030a091101030c080a0209030a120216050a0602 76
    0x2c400a807182c1d0404850f40c0c00c01001da4081c0103119401400c0740070074000c01c4081d5981c800410a00d180c0412222015161010040d4201100800000c282c460010061500200c0c0803c02130031914082d01c03140991003995009210340d000b15980d018240c1c0141c0c02182c800e0500344244004d13503015204171011250007400c00120000070150700141c10340382d03802c00d0203005020806c0004111a210140c002c41040307030f99040c0c005500d407042101b40c5203000a01407042d85044103200301914030403c0c1c00119140c554118840c0c80624441308c0c118019a400510707a80000507654800480100c0203603c207040c0d5480b28660354440003400c90b907491104034010241581040348240001100c030140003024824a0403420940c0c4403004510310f600159055900241c403540d4140401c0310350b001c84000560203180c10090103010205c000c011020180130700c0c80701580041d007684241c8051200c80b00ca20b4200c40c0030181c1840c3c40d14001c2da54a18005011016111044081420324128029600702c0e100b07580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 689510989 1250 689509739 689509757
    0x10050a1128020a02030a1a010506042607080a050a02180702060106030207052803080702010c0c02190902120f2503020c010905060916091104060521191b 67
    0xd600219001541d940000b0740c4034200381000180d400700f04040c0110702c05c02c182c529400f4003240c542c00d0b454040c2c1040d4401e44040c003041c00380c900c200701c0f2139841403d00d5030004002c10017070100908145160708601c2660050483d107109200c030014030030b0a681d109890300400c66080d4880200300f140c096440c640142c01070350040024074426000740c01087c0c015001e80d07440c08426034580100c04403114600c03020b10000320040d414540c02c0f150107540a9000d000a000b0305520000040070500e900300028810f907600306403120904500c04012001d00080c400441d60b400e130500640441d0319048403a00038040360072001588003014588440f600740c4d206980043d8540313440c00d066019400c852a41c05544d943da003c10307404602c0c03c2003564050254003000d40300c010382c2501c045176000b0303098011030f40c1d081c02e02c078120300782d0150101102d0894200c0c2c902151141c023648180e0090005900441c01300c0283e0105000a0794004c59060305183e040da08100680c20a0201414048201c40c65101c04200001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 689512239 1250 689510989 689511037
    0x1207030c03200603070309110f09011e0b0c0601080d180b07020619260907260d021b180114040609140702010b030307050304031502090310050a11 64
    0x80c002070305140d05488a4a1042c410000c00d030710380c20440303041e40000d0312011180103000354900807040da0386096500c82820000d800100e0074a410601c1486080d258028101c28001c0c0500310f09009400f0000c04286e85500641c0f107181da0300028002c601c40ca00032800381a07140e501807440d24981902c0d8101100d04107141002c0c1c1c10a039080000240c0c1c200004004902030301d0070141c03018858801da42c0721244841c50048030340b044a50300d0001807034011040b4040c41401b10000038080c007115101003204041e5000c41040380c0c4001a40e118031744180c85401000007a65401068489803098032154580000c11100c081000070f00400b070900f000c801c0b000c4014800007580c022407100ba140c0c09800800c995541e03207250340c07c4a44200c0c1c0500c1c041c1e01c600074031409903820700816650800480003982040c2c01e0303403910341d16403081784001000c4030003070510300403c51a10f8042d9400503030020b0903a480f80786403032000350240c5070860b0a0b0398004e02d0000910000780e42d00068507021800c246901c4611400d232 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 689513489 1250 689512239 689512253
    0x105010503060a0b0307020a06150503061b09030609030913022503090b0412021201020301030206120a140109020d06470403080a030b0117280f06051207030c03 70
    0x78020a403c5500000040b4200e1046002540504c0083d170092203400803d080001c110744000d040c41c02c1401d10303e02e003000b265800240050304a4010100400344500055800556104147c403407a018040c00b0108003090030301101a100b0b401c0700360b411350310600721140c88900300c3c840c00091500c0c0d0852154220620307640c0e0680c0c403c20030b00c24200720701c0c0286c82d50004030058100740d1204100d800040d00080440c200200005016003c42c4025800d65045030700080e054024003a0090080c15000005513180700c003034012459612000701e8009140d611200010007940c08042d0f41109103003003040005608100700c1c20b1140c811940d03690201002c5880c0305112908285069601d19503c0044101680c0300c1418003c100961194801d2a50b469290b6406415541d22030a00c3e814080d00d4a50120b1000c6102c40b2580e20542500300030342d24809100245288120306000d60414601e0300018807100380066100000f960821114000180b4915007420360f41d00e82400003e005038a602d908100003000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 689514739 1250 689513489 689513491
    0x12140607022d070e010803070c0e01030b01032a09020a020f0c0109050409110406060509030708060709090903021e0102031807051305101508040b01061d0121090c03030917060105010503 81
    0x2d6441952481903940d0031014801d2001c0c0c02c0042c1e1a0000100708080103143c44060000384020102241998910340320350824003c144806001d040400b441d0100c445400030b111000380f0408080c61035600c0d1070340d400600079040049888054403031222400051500002e40000c048816910328417668100170500015281295023122213201030701820300107507154000c80001d0091030380c60540f5180302c0c4040600c1e0114942c000301203074100c0c1040c0018a640104a501a0303448440f0104911009240c01c03454203811040c6800f81600085003501c2c00901900210702440850b03d108100018065445840340890720a040c1e004002c0440800a210f4507080740790720207021034001c1c0520369035640c611511905410f0640005100300c0400080100c640c1c4083e01400d5a4900700c0c0b04d040d0380c92228408c0c10034030341216046c48070405821002c20015030415088050b501001d0040c07050382e00d41440c0415250204502007040c100c800704903140070085c16403981e07402000615141e441c0600641e01070380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 689515989 1250 689514739 689514823
    0x504230307050f0a210207031b030605070c12034506050108070609030206090d0206041a040e070f050d05060a03080715111602010302030c041214060702 67
    0x1480688041041030121402c0e4020383d60180142d0b64191515600b01d152400c8071450480e559003030b40001e9580028884d082d40d90084221200c51a402c041c00315007032090340300916040c00c1c04100131030160300040e100d40c281d06c034110b00e4080b00d4054800341c003a0781240072100246118500c401d184581100140082c0300e9000340100042403d00141404d0702035296800c1c2c42d03458443d80100f00030b0704100081e4004202c0362408070302460842e40050014420154000d104034041101001959036500440c0e00030900380e0800f480d1b88844a1411076503070014410589051281400545c45030300500302d040562020381e03a00c0b4681911030440000908014064640018003078502000054070301001b000b40c42e00880130b0b501941c8840c0852400e440390390032500070024007031040d01c0000001d24038103071701194242000b60b02c030395640071100c209020b1340d8800c46400c00c04007510300a005202030165081031000741611110b83d034102c4260b9681024503550901c0895681d1000000301c680d05440e11100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 689517239 1250 689515989 689515993
    0xc0f0809010212240609220e030a05030420090a0f060b0d0618150302090910141f05030325020612090601090e030f0306181005030f0f0319020f0604050c010305060301050423 76
    0x108c0014460352464010030701c490701250001090006214100100800140f600103041c03850321000f01c0410624403020f00724a180945815042d1000c1d8101d80210740a8060401201d859004190031140a840e06102d907060010712008101081c0e0f48500032034245840002956030070500e1340d030900c4034213800140070f081140114000c0021560391801840d80541444442d82e4090504070384110340041c21030007440419280d040e04001549002c000c1c0d82c0303d140e00301d0710904100f114100400081d03527002d000942c8000c00190b18152110441021402380301c51400f119810380c0c035010410112a02c612a0304031650080c4a03035508164441c1c005c1d80e02400c013030a031903031516552031110b0540000343e0301000d4400c0c4507481404641410000a46a001740c03100412a64007021502903c6c0e00c241c04454400c0600034240354940740c000c120700f003a411090401c40300685002e04000707032100d40d01c40e0f0160000741003101040651605005141c000c039003140e400d041c95449000c0602124202c0510a07210b4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 689518489 1250 689517239 689517251
    0x1a1612110901230a05041d07020a0204020a03060f0803030103030f0507030e0f01050f0d050103050f16140f12060a0f091a07120f1d010c0f080901021224060922 70
    0x3d00382d03a601a04600e0a140c4030261554204040b541284440403a00841180480f04228109900003044400290107550040c2d544081c00700460190003e40c000c1c00f2051401000026407010000085040781d0007581c464a04403070b548800c9889202d907070b00160000e5000320304014a071030b000c031040315241014140303d8600a19402050b00035005100b1200703c07143c1e520010421310005004802462802d40050f00749103800700000d41002000e4021203e805061028160f85c0b519925400b00d15010001c0070182405040b010b80c550b5224222011000d0030b06294560745901074900031202c80e2907103d01c0484040b5814142c4e0190303208001c0c268000c00c440740025080e441d646110740c401420385044041200521b5508100c2c0c45038904040e000c040c4e141c20300040500303a1000b40900f035814070b0f141c100000d48036002c51a02a004059800400380c58150034170107084800c000c006440813011010404442c4031204000050081040745034015650440410021207601e48050011201850008513 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 689519739 1250 689518489 689518547
    0x2070e01120507050f060f03180303040f03030c08040807121e020313230d060f14010e0f040b06040c05070b040c0e0114010f0305041a1612110901 64
    0x14165080e480382585502030850141844000d1007400c0107404140d030100c040340302c0381d4003041e918031034004060301c80c810120208071082d01041464021010042c103c2e5124142804d100043c5504044218042440c0c641ca10b401315019090051040e904079035942d0414130151511030280303c02e025903d080000700c024500b880300740d00360b100ea00e62040c0e41c01140c94485c80103031100701043d142c105695030020102e60b041c40d0040b840529143d940262801c852504403860400060b180c460302c07840520b42400c1d0303080060703a2003007206030403580c640c807c0c1c03003040c0c842c0481e281c1010000c0c0c5000e483d00480c1800200da034185608050440441d030715200d031a0205036214603154642c1501e0403900f580056200300034408000f01c240d4090041084403480a0640030006010301a200c0054018151148005030501603245140181c00c0e214501c901003518250189245801c2a500700201180c010320110310300c9001441905c0c40710b40814a40ca2511000c4001528850545225241d11054108803190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 689520989 1250 689519739 689519759
    0x20d15090b04080301080706021605010e0307030c080105240306041415040b060a0b04060806190b07140d020f070b09041d0c18040f110a050301020f030405010b0109240207 75
    0x7102d6809440c4090b16541003982d01401d1034141c0e48600d0443d403080550060007480c1b10200030895030242004003144a0540210341040810741c0042c4c40c9540d00040005c1c0070406401c0300e44039140e68180c04000c1032814001c0b04003942126580c0f074255000740001000102031004400511030844111244486442d0108101240c100c40413101c0c00c5030a424070206061100d0881c0c003405c41c540c4c98600342824404001c1c040000213006c14803505c0c0541ca422808040d41820b100070303010390626140c0e22085801c00c4850300c00b02c01c0c440701700ca1040b81c2c56040d16034404038000c0072841c415030241c05400c0c540105482e90380c11903110958060790b0740c50341c0210402080301e403800303840440010748003071302014042107a01d0300d4504000390075014040411000590810f00c40c1c2d052707a840f1708020602118003000c41c1c5400340d29008280c0540c40002c482814030b14400c0a90f00c6284140003d1015801d601300454448a852003000232810300c0240f2040c540080d0420400c1c01030703440c811201c2080d6550310001e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 689522239 1250 689520989 689520991
    0x3110706170f2e0f0b0304030507030509010302090a120203060a060b0f0903100903080f010e010e0112050c03060a0938130c0b0403050f01141b090a030803011d0103020d15090b 77
    0x15032003080084040011000d800d130918001c02810f0509425450180c0b000b904600c01e00301c00400300722000884152a038025030544d0b500c10000360116201c0d944640803c4108484041e05034400d01c00c15000454001460162200361408003540c03909007000c0d9244146145c109a01030f0745d05000e04082039404006e58813410410304c0c00b941d200980341c00c00304445c900b0b012060300f1400c2e0a9074a040140020324405150030304440e4034042e201040c20b2142001401c003021869015494020716003401100d10858004180c054050380c42003c0f4141110a01e9640000c0020702440410300b10034182c070b851070040d1819602c0403001c46030300800c45a55485800c5901c494008500802001c2420300034080208401520224100b008025400e580aa0303241011001484540d486030702580c0c15105c2080c1c24290342d00108054810140c02d40c40e4036110704e0b113400034050704d04400440ca00c41c000c07100b0300124950480b600940582da03030314811b80760f9a00740c040d000010540151100d03030010000f10440d8070341d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 689523489 1250 689522239 689522311
    0x207021c08040f090c05041a0d0903020607031d1513060e0d1103090f120304270c0206070503040b060a0503060405010c0305010909020f121903110706170f 68
    0x100d03610b41c24604440c00c0d0720604d80080100c1c0e4500a81c040d40c05403c0b9003120180c0d040016a4680c0d851b00702d586429030320501d030510144505105412003059000a480b074060720241d1000e00c1061420300ea030501c6010035224603c0d0f01e41c00b0400c034441c03100c01b03111a0b6810800201d400c4a0b1b04445888110076200d04003180d000b26407140700f0303054125900c0350030070060003254401b40d80f0706100e0174001400150314401e880e10946003205401c03084034080003164001c0102c541a01480d00d11841201414a07c001045003254240ba110000300c1d440812114440d4000f80c445904640350780c0c442d4251014002c140a40045801d040800e003640c00301f042c140324034850000842c0004036008014140d8038180e00070031055052580d070000590312280d4005070448140d03000c800c0c01d81903000292a05c401c1c2c00c502c1e608440c603035200c0b20605502c03501d10321038260940c00301e5049036540e0304103c1d411010780303a01c0d0504102d1100481d80002c070860f00c5c1600200958900d003000c105101c20200000d26003042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 689524739 1250 689523489 689523503
    0x70503070818150a12180b060415030317010603020a0503070e0a120f020f09010b0a0318021908150c0703050a0c020415091a09040803130803011203120501180207021c 73
    0xb10840c1075020040d400d8175429400d0501490150181020b0b101300349002c01814040c400c0d0016903292616480140342104a0f000218000e9503030074050a880c15608041740360b02905400842c03000c0c028021503800d020941c0d00c0a1840e540d041c4111035182c0100d004c030f030348044054400507008c50301c0840790340c55030300550300c10034088400c0c4100302004030722801030b0740101c910000410541000f541520b0b0014a40e040c0031404212210003011840001c03d4000d5005203800074140020301c0b0540c0303800946841030100c840360408484440c0308600c0c111913400d0601010860700c00021300c00d002822680d5051f00f0b2100c01c00860364001801c0e507002c9103400100b81040b440420441c0da99000e08006069a100030030403200103080031803c007070b1006001903c40040040450310200d04680c4400510707820024640e100c1d6100d0700c510344448803103c410390004400040c181d2101040c0e118a604a0304100043e04443c4c01d0480300702e001c0d401400060f80d12090513414074500c41042000003500c5481280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 689525989 1250 689524739 689524747
    0x12010f0e07030b0306010909030504172a0906100c06111c06121b090e010b121b01030f0f1b0908030403030903020618030f0d110307050307081815 64
    0x96403552150040c00403040508200444020341c80124085045d20034010010039280300078182522076200703c2d40302060417880c4001c20001c0c10404905c1c1c516041400b148101c0b40c20800e001c081c664140301860355402900d040204005192000c2600303043c110504214004c040c15807170300c000701c6107446110f40000000180030703840e00e213a0803041114841808010000b250510070440c1c240b001d0301500078980c9440704100c45003810b2400800000b05482c200a218500c1940e9111f40600b40040d00d40b802082502040c3c806201c1c0841c16558200d100c4015110f1a101e142c011801b83c10001018034040c0c0c0e55103030001d50600c0c18000c005254032290081c10b502c070301c02e002c0202810390507404500150014481800003e0740840345204480d0100c450503140d044045003800e8843c104d4004561503c42c1c84410803a1010104000aa90890fa255045017004400d1090388134070a0140c0146260420002c81001458000140805c4600038152604610500e400304000d80c040000c65000008041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 689527239 1250 689525989 689525999
    0x70627021201060305070b09010e030f010c090509041212021608040e0106080c1611060412060f021e18030f0303090c01020a0804090b01030906020f0c0601091a011412010f 75
    0x4600070740d14540c40081210514544038951200b6a50055070803020000a0849251380310320f850000030200242941c88910f000d062080c004e0040c00605404a10414000902071510720a1039100c0c540100e081e910f1154000001c83d00c080050f440a03074840d601740f02482c009241c081504000c28492890141d1b25410500400300802d8140d0110381002014030800c407501c001c58058030301e00e4881d803003c005102218541040c80d50040b00d220350b0000c40c0840c0000d00354400307400a0300c215024004c20003522900c20b400c2001c2c1c1c490b00348640c4040c0c04000100142100300c2000700b094510b2082e00100b001032800c0000d080046c00c3c1c03148c1307841c2d90000c028009641001d102c0c048604000b4001841e8045aa40d20207145000e01d129049000750342d0400c20000c1e03402504204141540039038110340d0354452810740700080e04002c01c54101c80c07040000201d800314103485084522416407a20307036554039000d8011a4080e0b0003d0a504080c102400036814070104c200702180a000b00c45807084260b4101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 689528489 1250 689527239 689527249
    0xe0306090303010f06080702150a06140118050f0a0f27140604050919050313050114040e07090803030703020403020f09130605070219050f12040b090607062702 70
    0x40c0c400c09158004100410041035400074400444455040900d0166625003007642040d030f03540012242c5d80c903800e01300b1180400e1a4004070a03210070f8140c880c01c500d0304000448405603500340c1ca40b8000c00310700c824042450003203c28800354900410201d40551540940f2941501c030b98014800c0c8a10300341900042c1111009118213696004400c001c10121448400c07004807003d01120f020b10f58400c042100c000003408200181449a041600115418640556030341d100c1078050420148010340807840750b2003840c1e9092004c040b200c200b17050a0601d07921211640d8050030ba2414403200d04030004e11040148040d40c4100201d840068513689103005011a450b00f003603480d4403d210100c2048201410506044625900300100066030ba40c0ca400503464030300811074203900d161031629175400708540061088000643c0c40c00b0381d10500042d056074000c40c0514001d80c1054041070016401e01d0074600050011140207000102d01b180d200b207002e04001400302c80001000803141120b00c254101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 689529739 1250 689528489 689528491
    0x1030506180a0902010c020301090c06301107051006080c0f101d03070306060906050108091504030e090f07020c01110a02010c05120307020708191e0318060e0306 71
    0x5452200c5034004107a114240101c004040e2401540c0d42c2c02c0b4901035902c210041c0748803683c06402000244800d0518003003030000c40c4140800240c100718003054114160368401122500d40038040000c40745030450304080c062640b10003144210034072003c0f010034000c00010101907806440069840c1c1080281418400c00c00b24241c00340301c0003401d40c50a5125076076a00c042034050310701011036100d420314002c001d502009032540e0512484602000f44801603100c4412079011110400105079200d006407200003044030301c625280c200314049a58076a000c40003035401482482c200035143c4035000043c44580060f04c00425080309801080940c0d40c04100c800d84142c000d081c070100b1003a002481a640e0302000c07400a04101c03a07200780c1d004111042044003c0061002e00c000e499141000c8003d54451943c03043c1d2120303110b801d4054030303440c08460043ca4281d41108000314501c18000c0020303007c1c02c41250407410401d40da8001d60a000c03c081c5110042c0190b0303070303410080a200b10b04043c138001c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 689530989 1250 689529739 689529751
    0x2010f0501060801030b1008010c110606040608070e1b13061b0804091a091509070509150313170405101704020d030215090718020a0206060f0f040905010b010305 71
    0xc6498010700c5056040a81d0300e0440390703c114044401e070b884d4100b01c01050307034983c014aa41e60038007a00c91212904808000c24001c041021030f48279507689801c0006581c80c070f11600c20346800041c1c0038010405064a01903000c3c5110a605e081440c51070001c1540b940030000204203078140034020303c9203540c4094040f6030a40c01c01040c0e600b134a03031074460140612840c85920450303590341c40100c0041c800d1039984c00420000810710380e9540340040c0040c1d401c20014564a2081c003443c0c00045486006d00c00340c4040007030150100e5509100d400d1a0065544050300da0601e5050610880b00004c0090798200c60f025075021106d43c0300d03454403051100400191580000b406031804403129608240c60340e05a109404580302c1e403040b0007a0500380d00f42003024000c00b000030084400c00130203400003e010421508068080468403400d03804407400c074020440c4020050b0882d0022800515029480c014034040060441c01c06002d94800102110010003040303a407a51102c41d480352640e0188211a4803103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 689532239 1250 689530989 689530991
    0x1206070210060e10050616020604030f0501050f010806270d17070c11060f0f03011203022b030506030f03070c08280615090204060225061b02060f120702010f 69
    0x81054080c815042d00c0750f004031400b8040204440800b440103410507e01181c0182003180c1d16074032414100d404401d0f18509035915828000030503141401050100d040b5440380000e800107440c1d003002d01c1e03e03c8440b140d4410b003041d008004038607600c100b400748603101043e07a11124283c4241400c58120312500900c05030074040b031007041c00b000c20034808506840b0700c0300300d44180d40c40d042c80c0c0c1ca0003074a000e011006102d11001000100b00030b80000180c0c0b17071182c026000c4900464800c403080c00703000c44201c4080920118415501b101c24003980105400c00390040640c1c0d07040c1c2e41187d2291642d0400402618660040b180800c582141072000403c5020112401510085e01040000f1080c142c4240101442c2d41d0700b010900f080203d250000c00341c00386080c00d5680b5555000001d548600300c0340f20746118110a01d040d6084440803003604111009511000c0e06000d008254101040701002e041e60411000c0180586003403007c0700a0250410030211106541000341009084410356055071000c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 689533489 1250 689532239 689532241
    0x301050108030a120e1e0c0603010311040b0424050a15050406050c030f0a0f0e0f090105011d10030606091203050f09180403200312010506091206070210060e 69
    0x420700842107614008142c1000141c2034040343c01c11004000e00008104217000d08030031305054607404400703045503209080c00c07a4030303400c826030800040b40300078070000340804140485660b00d8242070f00700070080c40e0000d100140c129003440c202400d207000562009221382100d00d051000380b03409500da4010389030722003401c030040b100d0701c001400f64881da00446051200100340303208041c0c0e0400c1160307005204101c505440701a0491301525010100341c180001c10080514540c903810008550b060049000382070040702d03440e1070010b540103c02c0e580502408100015880c144e5202c1c4030030b015101d0625036000034260b1502c5001860b0320701ea5003000910503410030144020a9000e801e81c0c1002480e000000ea81d4100d80340001c121200509190220402000030170040c1500104c10041c1c10600314640e12a05148299503601da05c00d1400540140c50355100501590504501500d85024040d00342e000041c03060b035071240b0b0709200722660401030b44408482c40088109000d554014400d10300382e20b600d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 689534739 1250 689533489 689533499
    0x105031006050d0f0c0315060f0b07050a03050a0e060f0304030206180304090c0c050a0303050709080c03070b031e0c190f27090f0506040c0203030103021309060615110c03010501 78
    0xf00511030000740c103810104c180304c001d0040140791040251b900c1040d11201201080072900500b42c07505c01c11141030041080025550001402c40d00400c0d03020340541000d004d60f0398295407640001507840100040700441610903190070700141600e90100320580d8a034038242c130300240380c41030061011405682c500350320840d00d40d0000644042d50740b01000443c2050340d5900465104002240c0900702d8403440c4041c1c07080c5034043e03200a001305807030341d6090340031612003c400d0381e1280180c07403054040d44240410802222050081c5801c4032807415500c60709486550304c40d407240010395004c4060f0100164280d0810040c0184c40800c2c5101d00780668044010040502080c403a00d034013503252000e55400f03a04640d400342c45040a00b10099080003c0901e041c030060050104442060207149130804c600d0f8160b0002003540c1c102c0ea4000e101c120841064440140601003405085130120346074000459514000042a6400091a916000c4010203008141e1a00c8942490175009234501001448 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 689535989 1250 689534739 689534749
    0x70306080f0742021011121501141810020d0f260402011716020c060c191533050a0902090d0f08090307062109050a0515010503100605 59
    0x544030115041ca0340c0100640009030b08203009038404e03102c5249010300303810b46110550043e106060405001035115668142020000d0713030905540c1d400b01e1158407000704940d2b01100108100b41d054000126901c1c6040081031101503e8000716000d0303000461400d03d05903000349050352504040c9822a00394001c40d003c411101d20740c0328504016054600004c0070b690182a00410219910700454120300d01003041c20100c00a10a0160042c0034601a004142c80d07c8d5003030f5501aa03294000e407414100741c040e541d001080f40e8500b1600034041c1c04411413018001c0c4a200004040c00b52401d020032a5413200e6906c000000c06204105032101c4c0040c000c0742c8410b03c0c44019a41e441c100182c1d200c81010015504020fa8240107040da08008000c0301001403100c003a2601800590440e805180c03120307000e81da07407481036070b031a04242c0381105e499076409010382000c4075650181050703c2e00c240b481c2d203a06080180723070000c54401e0421403004100e14203040104003c0301e40e0070742e4100718a0742042c0c0014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 689537239 1250 689535989 689536079
    0x2c010b0a0c050307170301151701060c0c0e1f0b070506010b031503030c0a1b061b020d080d06031101021b1e130b03072408070306080f07 60
    0x30070410110340807810840d040040303c040725009400040c2c8181000314018641c0d00c24050720000440343c542c03810b0924010241c40c0503101c00140001c03841d03800d0140c00c0b61040d80501e020341d48880c00090000e8005407404046002c1c0b2455011180d0040c042c042400404080f0341c000608000204010341c0420004a4602d05461000c01d25580c0e9450b4400007506196140c500182d1501002541c594000c60016200c003050340706c0c4d4401c0c0603115000c06412180900380c42140301184903440c4200c64a000841c0079a0070034802040042001490788954203541c01c040714401003169145c80078018400143c061108581e0b0910040200409416a0005041a600400d070040308220201581141ea030389a820410030060010080f040c030138040480601603200c6098000d0090540200b100c40b154503190003101c00200c3d04079404111500101c5200200401740700406903114408103441e6410b100d07040c0440545802442401e00746030001d505150f01c2581c10030f0390800701c030b01c481d2459031001c405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 689538489 1250 689537239 689537257
    0x31a131a06240304140f0717060606030615090d0f0b1b040b04051210050c030a05090106030b0c16060e0a021f0e1201020403060c110c01080f1f0308042c010b 69
    0xc1740707003001c00d00c024901900d00d00b40e098079006840c800705080440b600c0b44018200f040040710000d49521040c81404d2009480b4141c002105171a0016861407030001094002070242680781c1d60520ba0f11001040720f00b0100440e140740a50b403c1c02030f00c092100740c1005401000b4403292a25140c550b000c0d0080c41503105207070180308004039140520505100c0440700044000041c031007403911000003642da80c400c480320040d0750301d84404105115014450072042e80d500c00e070001c690b85c4418480c43c0580e002100010260030200c0c2005001030f1040c012200c1e407030391450040402e40d07058410010f43d00341c4100c02954000103440510692544000d0600642070241c03940200d0103803d103507040c0684110303080905041e0400d451520a5a80302c281d51800c002040140c0e40940b1810f4011202d010003620001c40d442220400f00e204100e0031100070303080402078203240c15200e50300c1d55000302681081c0d00150495207030754201c907400443c0590907615502100305210790303903041042d9640f16014071011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 689539739 1250 689538489 689538503
    0x6041d061e1210020d05010807170613021c050601061202070f02060a05070c14010f1d040203130212010f0509060f0c0706110d0b19031a131a06240304 66
    0x701202d84142840b000204074401c1d6025941c400354001380344081d11080c414100240b14006002a003010403560030444a4080e40c0640007549440500200901c0c94910507030744850480c000300340b800c000d6041c00d003c0500c80c00151656614040b07000c0c1c441c402e071401011010780108402c85c00514414400c5213413560440f0711507100c40000908584d03d01a180e00200308000485000c580c4010b800d0f40e8040d05003003640c40003a4442903003c00c460b00001906038803181da094030000d01040c50942c0241d544101c0e1013501d9851507007940c000032400a031501e40300402d42d5444400303e41b404940c1c061564045440f1000f03144504120048002e800001064423004848c00301c2c444040288a8212005a034865010075844100c800028401850440c000301c0c4181000961a0244d00b12134000200712900544000d000b460301038103142400c00010800e190700142070282c1c8000440c00800107548004500d01c070310b241c2c5018024031076440d51445003a410440b010f9105032101c41c2c02e608807031744154002c1c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 689540989 1250 689539739 689539759
    0x60405181e040501060311060f0313030e04020f030a1a0d0308070e0907020606012a030c02030a021c0c060e0607080a0e06030702103902070506041d061e 67
    0x40600140361800c8141041c0118003002c0c00180076054000c1c206a0703028000a40380700d250142005014421856480c00074031040c000100d25104010607621010b01a00300b201c0415290300000d0200d034040030380b41040b07410101c2880107400862003001c0601c00ca90150890720300c0c50100140d8200b100150040030030a1444c00904654416614a40100d5014002003070a01380510040d46680003119100e00007150713801408290344c5110b440340500540300c00041b00307003182a00d0813140d8207480041231341c1511030a8003010041e00c81c203040c0d00c1050489000c000800280b45801ca00c4500203030312003010008010b2042c082d40d81d500b802c03910403541c85082907590f04590403050340c9084603149549d030f00c20300110401095540126600301c0380d140041c810403255500c000e018a501030520085200440107000c1171203100704041c202300030b0101600494000641c0c540c002400ca03402a0407a50f414044440301c240304000521021360011030032100016a2002c4003480d4842c0300e005c0c030109104900c040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 689542239 1250 689540989 689541001
    0x303070308040b0a0e070603090302101a010c0201170901021e040b0301060c14060106030c090806040b010608040c09020a03091403121f030807082107120c1b12030b06040518 76
    0xd44072003441c0c00c2c54004c0c0c03041d00791f0301c040103402009144030960240c001e0000c10040d2012912911410701c2c250000055401d030814011500c28402d00812810302114200f50762031443e0b03240700341d0320820306403001503035400c00855001242c070705d903410032079080b41c0600c42400108103440030b0303d0540d40079180a070060169802e010403203001d844020742a50141034004541c082c1d0540119071011100d40711804400e0b618404203907143d0040750701030018050a0012702c01171340315412464002d40134540600c85151034021402c2260304c12500f100c0440c2e40d840c02041000700f0000042c5003006481c000d1400c01400a0302d40c030304007000a0000040d0501d103403100317010030740840810000d035400002558442816103802c804179403207540705110918074290072034a400c152001aa11a0590b640c4035041b18001d01d070070301c024241c04465038090100b00241e98150304c4a0701003030545540115203100c051003030420050100c40d0307490760302c0f40144002c002c00c0c0600d8460b00740c04921000004400c0001d50347e40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 689543489 1250 689542239 689542241
    0x12030b06030114032e360b060604060512091612060524040c030e01060902030a050c04030210082802190201020301080304171005090a060b031506040b0a090203100e060303070308040b0a 81
    0x25258031092031000c407840b100490041014543d0041c8107c00c00d00c8252518010071025001c1c40c4605400600c0420102c0c1d0300c0d082c4501c4058100e50b02c0011140c0e015088440d404c031b04402900070070452038001003008280041d0740a23503500711040c0b4845103000c030110410b200d840594003e107103004540701c28040360a03906c6030380000001900c47e0020000241c59202603406035006480f525400d5051901103581ca04640c0115070460368010b107440307440a0740109c1920a4140100310f10714010404251201d0b11400c0c0211340030021243c1d20050b601c110b06564900744a104501c100b04580c410320050110140000480303080d01c5001c00a82090742e0203032407540c83c1c200e00c0300116110740d04103010700510400c0001c7d540c000511544040c040c10108209050307840c0c003910541036803207020360040380c10f030704180c2d10042c00d01001900c03851006407150138a4040c2d0f030007a1901c8100320340744182084034007424255076400003c100c010314078000b01c0f03450042103503002038030241c890b00c1d459010030b0b508002e07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 689544739 1250 689543489 689543531
    0x62a0f030c0c0c062105070e0f09060d032709050703050f1b180a06020a1214041a070b070f031104080d05090102030c100218090f0412030b06030114032e 67
    0x198424011803404810003090b00d501c1000083c0030354440340b1027402c14502010701c18440c060181c0010100d900c00e0f2012109009902e5a400300c803140303500e0301040300c001e07140624084d200000c008030745030602103c001c003180c0004203074640c2280c0c1c80741032104000b0680c42c0ca40c0c042c8040310308141c0700d8a2544410f84900b001c4c0306502d502814551002805503000300342003d45e68020303100043c940c80e502d1010346031503000700c42e10100807004000034450500301b8013400f00d81d121a84000b5040211a80c3c80d06c0000341e00f03071140004948148100d03000242c0c9401149110081c4c4002c02d82040e15003581d8658556402c1080c80a011001c1641101640b00304145e90320121441c0c01c4510317059122038260b0007588504c00c05114182c00e6801700f0401d0030b00007803a501a90201c49607100351b40d616201e41c00104144801d1108040d1245540e4038070f42d0b6188065070181804140d614075042211080502d811400407000c0101e084a5080c4110b420200206d6481d00c003c5200205492420b21030360064416 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 689545989 1250 689544739 689544797
    0x1c03140f120f0402030708070803030604021c0f1a010e09040b04240509100501080a0201180906080313080a050304060c030c0b040302031206011803062a0f030c0c0c06 73
    0x1c00008100c5903042c201c0c0e54038041d60080d420396000a84440006e0b03258489405040c045d94010000300c2d480d03007415401044917002c1c828100c0450800c80e40700400342c41201e0a03029420703449058940841c500091100442d4409003400b8039642ca495010882d043c00c020300c0034003507070240000941404854804500051715206410741401c2207504010000c29041d070703080f11b00384034800050305045103a22619058400400040032440c1140d80119580d1104d40d440e4031013071082c0031b40000e00c001e0602542d005800060055070701d0b90007074102401d0740801c0c0e070b202c001154001c490b08004214040201e4054440520b066002c4100e1420f017034404100340c1d4002080c06000008000030305501002810410b06464910250740c0c69a40c01102c030310704003a00460a14500c1c8a0820020300303103074401041681d980a20301c0611085c600e045032201061041103021074030340b81848071525803510491042089908001060301000e40f0b0b0554078824034021603060040c0342c01c5042d81c0900001116844507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 689547239 1250 689545989 689546017
    0x80a060e0f1507110d08040210030f02040f1d04020a050d061b08010503060f040b01151209050307260405010311131509120b06010e0a0e04030507021c03140f 69
    0x3104907070b52002c800500f1554100054484102c40764540e00c003107100d2034904466074501c1456220368003040034400440c240c02081c036a1301e041040c10b020460025000505070120a0045a450b141801118181144011a003642440c003004016a41c1412107000da41080d1500c0d103400308645000c10080c481c1040300c1c180041620f034170101041d448640745045e1f543c10b9041e640707540c60f80031203500200c0d01510020b06948200740144014a1000d44000c5008240d2910707100c42e5000240d0001220b520110a4485c1d13000040c800302845403c0702501c0c5d80280f009000b5180200e4040025850f00490144504060700d5a0400400703201c4841650600c140610b1181281ca40d00c0940703402ca45a41103c64010440884d00011b080340105011f25482c0d40002c104007403590740c40011111500001c590550103c0c603050301013010702d40e01a6161041e4441d07221306699a00c1801001603c411001a02503031050a0400d080081d601141e005a140110360141d501c50201c0a62950f51703019801c201200c03a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 689548489 1250 689547239 689547253
    0x10170a02130e130606080a05060606031b04081c051908151e130b0906040b0d051006060216060e13110f03150414040803060102010f1a03010c030501080a060e0f 70
    0x1400030b19103540144c0c800d480030444150389a040d151102c044007006400740e08480c0002d911420030030300465000450f8047c0e00300c003074500c82d0400c06039040b5411207029588140f2480b1300e04944088a114041d030070741406400c2c08042042c0700541b90b01c40311003504002200c00421385161010410341c5280c0c00041414441d50490406090011800b1038098861515824140e095100520444201701400341c1130107419620fa000b400098030880300c0050f04504140703940c0000c00d100344042e07500e0200001000c1261880c1080007132404039019500c0c022010464420800a03400200c0d114500d80c0a03520030260120122200b00180054070b039102101c940060349001124025009500c00e04949101e240c03000c0c0f0306401e0104540d180d20f503c110800c500c0010801280c0c1d0780700515800700c014030012035a466900400415600780d040e904282c2203d40c040d020061a003030180d25030200d8075260400c907540c50f04460300c1d51070103884400f8007250344d00d08542041e48000c1c000c04d51082100011aa1300c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 689549739 1250 689548489 689548501
    0xc070516060f020d090f0e0613090507060e1503070806040f02041401081305060112060b100c0b1b03180111040b090126060609040f0e060610170a02130e 67
    0xc086501101c0d0014000d8114100b13016001d542e981c0c1c140c41080e07161894a50905041e81d2403200003601e815401000110b00d03030125070300c0d4040d12000034403e2000d400001e00c2d180000e00f90705115100548601e4808514900c1d02202c5015a40d001001d0b2901500703645801c0c0c0454010a0280280600c55000090108044404030701204e600c903000e0ba2581100e5a800040c00007000e08860010400c0d0004001041054103241c50003190070700070b20000601003038080010b10528100080c1c4408508011012030602260b07a0f861940509440001000122540b42051301840300174003100002801503803211050200b54040210390002c0002c03240d98940360018121290441c0c00c0281c0010070441c030b4104024490341c005500c10092550103582912034404000268010320002e40d00150b0350001d060025001e8004d58019160a801501e420308209040c001e00b00e00c00c2d840c0ca01400100b5200a0b9181450b1084e40e500c01d244020050300e401c42c400401c0c003c10142c1d40206200c282520034014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 689550989 1250 689549739 689549747
    0xa080d1a0a06030606110601291c06050a0602030c1c14030f060f0d110409021302070c05030c06070b0c07020402071407180506010c06110903030c150a060e0c07051606 73
    0xd451740c80e00c41d0480d00300000211a6035090034082d01607024502c65008100450b0301d06401c4500300d40301d104074100705001c48141e1081010904400100d40c89190030011421711650b150050300300761001d5031030320181d8030200c0e540c2c000840681d41c42c0c2200c00240819540320b18410414039415420580d5a0306013140d8051100c2c0c2c09980e503920034902004046980d1a1500820311381c01c0c0c2c1b00c50f129011500380400c0100401c00580181d03040020180000c140320640d00c0100780c1035108000301d155580c2880c0505251641d80182c02c2c0c05070100300300d4100440d515190f4035900c406003d2000d551400240f000c100680210f19000b406003480d49400844044d01203068420307501c40d03400402c0c078502143d5550054490544085009c14007403d813040100306250490104112100e00c5030f8a041080c0300030034516400780140810030b801c0003000b0021100e802c4405074000c5070030319040c480d150510481c40e1030305502803c1c9000070400000c5520821400f401100c203c000080c0344030300380c1340d80c2e040050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 689552239 1250 689550989 689551001
    0x190f0b071e0e04150b03061e040c12112d0d060e0405010c0908070902030a02070602030103030804050c0a1a0901141903151413061e15110d0e0312070f0b07020a080d1a0a0603 76
    0xc4c5c405040c00d0f215a62801d0709002e445c102503080740928030141a20300741237075036181c58a00440c000310400170008481d00c2c07801110010031404c11416082d16050800900310388502c0103801c1002700c200020060030f08001600340035078400c21401603594a41444a000034851404024801800400000309250b0000c43d0144140d000d541130750700350700e4100100011003101e0f00803030342003030380d48800c5682c0004007030050f161b03e85060408203689005420f41ca141508400c080b51510402d0174840503055a05018482d20750380450f1507001d6441c104110300c540c405d58810845c3c0180840e8400c00382981483e0804d130000c00d101c204042c0b2002542c950029800c64501500c03005403030f6207100180d02031248400d40c02030200e140180034402c490020031121000140c88160f410300c1241405415103040790300030003a541c45020f81455800391480e00e8504000014210000c4d5084050400040b4446008a8000c2c0c881d06d40000713504c842d19800711180031240f00e12190040024140404c40c150154424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 689553489 1250 689552239 689552267
    0x5030405030d02060709030b040f050f01020c010b01030209031b1c05061519290c06010510090b040b1b031803190f0b071e0e04150b03061e040c 63
    0x7940c42d01e141e00308207070395409068642c400040d0103010700f00041120000303c41d400511942005c00400300d161516850840d02d40c41103012039600003407011092000344111201c0d080c00382410740c100030368900025154043e4201d008050705445180940300d640381d220080c15150810746089424015040c0317299114002c071000c1e001031488800d142c0c40b0745400c0320041c501d11103080419000340e00301038406002c072101404011070503d21040349407402160902030480702d00342c1c10080a00d507241104000c481a05070300c0103010f1020415050041c107441c04200e0341920b0341c8861066881040c8820b0240c030b03000707510491303e040c040800c410500d00444c000317503d1281022811a50326429960741454031500d046401492981c0c11212031001442511403168050701604203100018440f06ca001c18101110f030080c030000f1099141a100c07450135108404880003201a0320948600300002000a40710182001d44500302c641c107000d41c07030134003440a000b003440c0182060081e480380340c8010313122020540350 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 689554739 1250 689553489 689553493
    0x120d09050606060405030a0609050c101809020f03070e0f0a060e3a0204021909060f03020301050d082d0403021e0f0603040f0203060c030403030b040504120e0406050d0503040503 78
    0x820031900c0c10300f0584085e254000c001c0e0000e6026641d0341802403002180440751400784002481482d6640080345070a01003946603804090003290748001150442d41041d591b041c414800340c800300000b0401c5d2503004a86050015602102500007207102036807020490340031f266500041002503201c3c100490000003540c0d0b01d540c050f8920300b54000c100b1081d0066038040d820500003030601c09011101f501040c00500700501d0042000c0908500c6843c2d040030300b0104507160b03420000c4035805000924019642d00e800c41c150750402000410981e01180040c261030350101c2d00d04c8408002d0407014008808202e03100f400310400c000f95402c917401c10f1000342d100c0c0810034504181024840082544054010050110314045004000180e04068025034480c00494150401602c0130004103010300a61400c07261070b40740c20300e4020191204200c0b0240124103003024080018284040920085070038103000c4c0560003280080f40050103d0b501c00369110400480e50401e1200210007002520000d0702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 689555989 1250 689554739 689554741
    0x31e090705010219140a0803090d08060102190602190915020102040e1f030b131e170f120c0a030501080d08150109090e15071b060e120d090506 63
    0x10609444a8803807180c1805038005164041100042030b204045640c803500003140603800c405810340c5800c1e40d01c0400c0fa441307000082845005c000400140e6080d41c81882c1c403040d60310348000000d4483d46802c02145450f191444900708000464055507181800130b0850b0301490b03100d44008121005130700c00d02c000b031380d400086414010f2041c0200c5041c1d0b2074000d45000304c0d0310350f010a0102e400358144540c5a00401c00408000610f5042d1200d01407034100000403400403043c100f11030180c04540d025881c02041c072071000c00060b44503440505010310010107648495680310721075054801d0304c10381c580d0381003044104a1015074400c06805c4c0c00034581d40400013a80c0700c455007590f0301541c2040401041c80b013000100c0340040b2050312035120780c0601d41445c4055954441c802a01c1107003a10308202e8000043d02c41907440e002115540c07151043c80c107101001000d400640e43e46a9920003d4550341d11080380c8881d8000c10401c01c2d0880428020140e581c0e038087c0d501d00c00400c800c0b82d08403140d0282038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 689557239 1250 689555989 689556001
    0x204181a0a090b24060d0515060a0e04090503090d030c0614190b03070302041a0906040b0114160c0e070206010906060e0d050c1201090b060904030f0813020303031e 72
    0x72003a82c0000c0c0c0d128050220300e840700c040003102c5120010810508400d00d004d000480d40312500500b030090280440840d060400c4900f580342e50303140303040d01ca0160a080c001111265400300d062481d1003000e490005003c0c1450419900314456052915040400d1002042c20140e029a400001500403902004003091019985007100400d40303000c2004142d03911036843c1c0c40302581c042c001d262402030031611115503d03400b040039240c200950049980300c200103004235091031041c0b25400b04013240c082003904100000609081885022040d4030304010406040004004503002130341a000b9207191a4030380d8407038040d00c512808582c076000501882c8000034110b0300c14003e02c403e44045454036012144030400703100f440e4483e190251081d129800407040a45c903420450040e9000b01f400206440140c2d00308000c10300006032001340034982107001c00022940c0803203050088201840c00b06100d07240e18411000c010324603180a54140000402d10524154120f002c0400000510707656146960784 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 689558489 1250 689557239 689557241
    0xf070b09030a0c12051c0209041a03030a0302130e040f0c0e010b070f0303021612030b1512040521030601080708100611010e0f0123011404090204181a0a 67
    0x80c02e0610046007292070a40c3c0003c10f5010682003915040c40c005082140d010302031040d201042c041b04000a500240550f81d90802e40581e0031200c141d142d41c043c8001031000880c0c0d4034428070040324105a80851230341c070203600352280e000041c0340e02050100a0304160404901d03c0c0c2c0701ca001162404146100040c01c0c5413a100e005040751900c0d1001403d0107004d403181080409080001c50400d0b82c02c01104c00d502d8014881c0c6202c060280b03100a0700315080808c0a000c0b940c004d20038a10604580800340090805d4804895a0b0044c07508141040e40720740c038040d0302e08044104180006190aa4072162121181e00518803e48090b620591075807a1403c041d1044c000654001f0070070440200c080c846a030060844035501c0e45800700000e6091a4180b00900b0000404850040c0340d440303c03000c0303c0078980300c040c40c002803400d800b060707145500d09050034440c06407020a15000d070751142c0100c0c0c1590344a512281c541d07035a061206034102180d2811100308611f06110f02d04c004c1104c0049181000b607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 689559739 1250 689558489 689558497
    0x10f0b090106090b0d060503011d07060e0a1e05100e0a09020301060804060504020a0f2702040f210606030803060a08190b0405101112090115030602070201140f070b0903 74
    0x6407200082a03080c6402c0004c03a0f40504079000c051526448006070648007441201480720180c4807000c0d03072800340c40f000c0d070820034682d000004001c60307109001515554904030b44200c40343c620703c0c0c007080783c984802c2c10b20044240c2d001c01c0d40040d4501c4500710f015040410101d5a28046410391403071500c070364180080b0f010a001c1c20000407403503400100001c5d804d621032030b0464001891002426541d0300703140300005158006090014003002c45c20801210200e0344550440080301c254207041c104844000c017480316206007004504d21420b0a0340d904c00920b5459079003074002c0018806103490382055481a071007910a180a000c15030000503c002c0086155074581000380050200c0400a403035001c035040300903001b80e0711801380c0300c9a06d12401c100d201d410540c506280100381c035050420500440000010080001c990400c041407590452951a0343c0a81c0d501480058548049000484071240f04004071071000800091440300c400b81c60020f0040148640440411980c03101042d1352280a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 689560989 1250 689559739 689559749
    0x1b0a051312110603090c030d0c0203010b1e0105030a06150507020f01020d0806040908040915080f03210c07060606030b0420040501031119030c0e012d0905060309010f0b0901 76
    0x1168146860301450100000c6800410b170108030740400900b100080e0030103001900301d0740810400000c8030110308082c041c44000d90000c4074500101100d100309000054882c44c4001d041110000028031055025800400500400000006400700343c013405030095000340c07802c0c0e201c1c580071284504e4540c8005140c0c003040005a4540400d61501d078144009003000c540201e890820501c000f003140d421520480103080b000c000300300340003440c000f91141003402484006100b60010072000310b45612844c000311040b40a881e541c0180c1e0340300c00c52195103001d14600140034038184a80010420f0b41900304070201c1c1c1045400700b0070714440c0390f02075441b0320049400c00710910b000d00c01080990300036880b080192100105007860b000124901003050744c0044840d9020a540d5020388403942e03441501c50500380c60a003000d550a03d42c0a120b14803004440303a03200705006200c4d8001c1d11140c80340c03e1000003000040e00040d164184083c940340600722484914030b041d464107001740701600d841c46d03000d41250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 689562239 1250 689560989 689561003
    0x7030503040914191508030d240803070b0601030e03030a380405070201020702090903070c15050d09020a1715070c020a18271406060a06081b0a051312 66
    0x904d0111649001e0048100100d25000c10203800044400b018401080034401d20100012072040c2c94403186c901c4402c82180345c41c0c2000d861000e100c2a21300100300c484541c5c00c00c03094407066a400004078050041c40600450394040030003800060480e0f90000752425804040360078000881c142004040d6054031100003030040449011007090401d0350219822410503c0003514100c00fa07004120340010694044005038070014a003001d2104106c604070251014a80201c80c0c000a958003c2c680d01408071042d010607642e046a4085556510885008041c04882508002544106284c480345611036400102180500041c54940700e505a0003080354010a81d80c3c80398100780342c042702d16445034007480c1c0701941c86030880f542a9500700039840c00c211b00c09103001c24000c00c1c03410441243c0003901c0300c80075074404000c0c42100d07660142034405441385840d180e40c156480540029481180c40d6181e1403180d070002d40482c044d60b004000f03081081d0000c492900e1160b13900c04000c026424082c001e0944 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 689563489 1250 689562239 689562271
    0x13050a0227102a05070b0c03072108060f03070305011a0405090606010801170f12030a0b010c020a05100e0604030303050405070602071d040311010e0303060a140609040905070807030503040914 84
    0x550680f00781000f2083c0034034102c036032550311120f450364075920090311171350242e101113220401c1002c2d080304074565040280140b540c8654480c4094407010020b450b152042c81c80400403115078074104400802103070440c0082c441844128003034030100c00a10501c42c0124103060004410080000350680584811796642070207a00c0c002044c44c0c01003851b0f40e458518011004201e071010400c00a20341c0301c01ca0035090654030306104c0b080c80204c0385020901c60510466a000001580e68a6500000c9500a0380c842280b00b15004080303911480c103650545d88800041004401e25034542d201d188120b1048088804440e19100103031396648072403080000c00c0400c0d1a078151184080300d0708503005440b86c100039070f9070020700c030b1100c3c03c0d22010f035290304580c3c0c4007008104072407500300405001806c1d46500d80b05c2807088040442e00512803080c03a40d01030340e112070140041107000c200c180b00034543c0784141c40045840e860425144d85c043e00c142411241841c1440103040c04c40040d1a0003401e07102c056080b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 689564739 1250 689563489 689563547
    0xb01020c18040201140a050a030513050d0e040b06030103060903090e101a07050a03030e0c01050406050403060c20010906140123130f2913050a022710 66
    0x107034100074022810003a03600c845c0030032055401c02034403a1002d592110b907283d83c00100c00030210741c001801034020340b1810b24003401081c0042512405080b140c84c1502c40d01016101040260034106c3ca00d5800a100000004c144a020b0b030041140d5440f0f652040920ba13034414000d150700703405a4184004101544081040e45c18041689031071a01360000182864501e803909030411000d4001a404652114400e038000310061244199140017405c20500b864248130b8018454092804000d290f940e94807441c102503400360100390600070f80180800b84980084811501174091810f080310350314240041c4103050500e614125040c1c03048500801071030585008802c124100001398180c100c240e141c10000c03998400d02410400f00c25002001c00c0d001d803140029940b05c90302c0048408181846034000380701c0c0c1e0711a80501c5003401d45403c0420340d9150754070032200070b100b0701c0016521901503050b103411070500c000f4264070215086130800d5044040d00010740d0901e960442510300c0f415040c400c259 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 689565989 1250 689564739 689564779
    0x3020306060f0a030b040f1409032704200d0501140f0907031b030e070503030c0d0507050c0901090605010e1203190c1e1202010b0904080d0213030c0503010b01020c 72
    0x1401010a00c1e0200c0c0702c504041c003007000c950200203a440400c1c0c481d0360078201d11048e2001d10b60003090340c7c7c000390314005003442e03040c40b4200b000d1815281050310192446060b0f90b69040034280e454101056074181d003803e544203d1582c8119544001340c0d041000006a05450b0f0b962400b02d5100030b448800a0b28170710301000000040103000c41c05240e95546885400f08100c3c956035800041504d0002d000440c88414901d406001c0c0d202600c00d900c100140c0b110180f01041006041c01103007002c40c1c44020515049090900c0214455080b142401c0000366040b03803070b003050f0100c51080c1ca40c40030301405c0c0014803070200c0281301c40012070781c020000300c6440d01026040031818011031503c00300407011035540d1071005102c0b0800c2c8480351080c856000c18401480401c810f4040326000811600e80e214022884caa100108083d002500c003080b80d11752401c094040307c0404004c01202d0000c15101d1401300404011402018080d45ca455207020030b0354000102124410710041c103044e0201e03620308c0504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 689567239 1250 689565989 689565997
    0x80708090415030c0612090213150909030305010e060f0a05090604062715060801151709060405070504020a0804060f1506020a020418032304050d08040e0703020306060f 74
    0x1c1d007069a468164500c40c441c106044040c5104d03914000394075107442030040080f01c030f90790034800c5645030208100040e030b18903042240c5450304000c081034002881c54240260112940484425418800031030201941a03100906984d1000d20b84000c030345411042c00400415404c00c1c941000d03030000c050140340380002e5881d5200c0030017000030071031640750b059031600d202e02103420314103440a40b044ca040360303490b500840d1001110807000346c032a10b00c0c085c0010b22142061044055400d80c0201c28103055121b52584414003049101401050800205550b500c10703048509903180d00030800b000c6007519180c0222441c0802a41d00c074105030b240c5803510801820501d90340c4241c655134102100c251030400501900a00c0e094020708640040d600500c0266110036111041510b035148070840020b800418141ca01d140d080350f40203409030f40c08043d1180e4452500070304d50010200320300904000c0c0305001030090742c183c50940344040e02c5040023581640800e45445900480c280280b40c0e001ca4001d000d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 689568345 1106 689567239 689567257
    0x17030408040b03060102012c0601080303091203060315010303021f0207080307030c030902040e0f150f0412020c040612140715180512030a02070f03080708 68
    0x81544902d00401c8040301c800700202c4d0140e40300750321010040d103141d82000600d0401508111500b160500c1c070559501c50140042040400441524012202440241103110300240504d5442e00004d00c01500f61064040701180b1981102d00213009501940162403202c400395912151480d2181c4400c589500401481001985010449912a100349000110080f014004030094400140060360203802c207804031621000c00b062088e9401c024408950751043e441c0b000b820300500c00c550704020490700700c0020b40461625502d00e1b5003d070091040e14040c155800024040f0780c8a0740000010b48501030f03441c010808900c0208003600c500030010885240ba101c13140030790015413640c035400c000162410220b1174034041006005800d008003841543d40125000b540da81d0000422800184554100001d2141c19410108103a91b008001c0624201ba1a1120100780e4048521 = true := by decide +kernel

theorem cover : BRFrame.Cov 689388489 689568345 := by
  have h0 := BRFrame.cov_init 689388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 689388489 ≤ n) (h2 : n < 689568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
