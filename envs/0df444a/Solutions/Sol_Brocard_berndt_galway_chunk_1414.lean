-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1414
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:52:06.961834+00:00
-- url     : https://prove2.me/submissions/42b92fbf-c314-4456-96e0-93c66ae60f4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 254136690 ≤ n < 254316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 254137940 1250 254136690 254136703
    0x50106090f02070209060d23070e07020625021209060d0212101203050a0e180a020405011b0515041518050606181302190803030912030118091407150e03060108 70
    0x8002d000b00230144600010030310b030001951020741c84201071400d205200d03a000c6000340c02a540c2c42c0115101e1280d034201c01e207018903801c0000016902080f048007022070541e0240500702401060581402010b0300240d09070f92011101502800c40a4108030001d401c101d0460043c0902a54001140b0707000e0b0790140c201d01c41e00c100b1a05001d03c04c3c984a10320359408219041e41001c0203460a12400e1034048003003c0c1d0418020356012845004450702c500e0060901c0721042500003004001c0085501c0c204104a200a0000c0d180c5c804101d100c4c1001c00e04600600c00d00000140d80d14501364841c1c1031081c01d000e0050801d92151860280d041c0c00c000c1c0d4028029001f41004400c1c0d607030b248440c070028240d021401c03100c44004c48000c2c000544d9003808000396201d407202100382d81c6403455001d07851550784424080c0c1000c01114410054442d800c0b5400510a03611503c20301c0c0c4250f02d104061840e1403401d41c440b6400d072480074440c40183d07910000e8003081b138406800509031941480e50359a20b40c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 254139190 1250 254137940 254137973
    0x20d120b0307080717370203010f05070f080907090b0102031306020a0c1d0a0203091e070305070e0103120e120a0f1103010c1b031e0207050405070801081009050106090f02070209060d 80
    0x2990b086c0c0c205074000e0060324002150340d00600030008507400c24204406458100d4902c000304128544440c5c80c00e020b0b45101e8440d0501401400c50340d4105808800180403500e0020304511051101e24040d28002041401502c00381e0001c1680b00d103a8544004404c0040e04000b403c0c800c0300d40603605001519181c690000840350700540c4a60342d44070600d1070400303840e1010480005680c841604802c0101e180401d5038001c1c41a940e040d9120404154091330a201c02031040c0020742d421103401703202c0c80b2100710a4900801c80c07411480c1e203030040e61404035001000da800c3c0c22011880c00400c2807a80d030010107071000354000d220388458008040c0841802e205040c007401810b0100c2c01c2007500c61503540f880380101d41c1c6910001c4040c0c1100035030b100000c0c01114011860070022400d22802039903114100c84e41d460007000100004006140a0f000784a4102c0390b40d900d80d0750203c1c1c0c110280c0180703013241c4c003644001601c4405c10300410101c485d02505d40d5008911010f5040c0101c3c020311160410071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 254140440 1250 254139190 254139253
    0x91401090602032b0603080409051b16110607080909090f03090f040209060301150f0309021c0c030803070210140c0301061407050102030123030706020d120b0307080717 74
    0xb1240441981554021861300c18413034580480401007007520f0001d40f0580c2c880070410045591181a01451070b400142c0101c450f040620180003c070b0b800941c10262030384500c4210502043d0031001c00d181e50041d00d400c40341803070045000d10316810b0103014540d00104030402080012800b180d0765440e4814400050b000e54140c0c0403156484e180c58040314507141010386202d43e69a915031380740300501c1111b80780d0300c0010102d48001c0d240510030300a00e000c2c00d400815004072044c0c2d001406016142010f0101da40c2410140c00101160048000e944141c00d1078000d041d201e0b046c2c0e07c18004441805101b048284151424010f4480454056070b056909506014a1046040c071980c261030280200c001c01c0b540c000000070441c0001d11201d1000c17001142c14811154002004040d1159441d000341c40059101100300b02400344118103024044140d803400140b82c1c1400c60101313082488a4121078403079801240c040103c102e00b261020080701006028004a0b1901000f04c400690242842900d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 254141690 1250 254140440 254140477
    0x10e0c1005130b04090203010501080a0e060609130506010e0106020d09031112030c010501081006090e0c0603060a0e09030307230a18090c031d010e030306040f090503070309140109060203 82
    0xe11181d009a002d03001400c402504e45a80d6400d4402035442400b6107030020f80c041000c02c10801e01c0b8042d0408007070102e030140c242ca070b65060501c9105030004150302c80302000140c80d100418001d10800c0d0107000c5041440c15558100940030f8641a8401d15590420500030400c0001c99074004d0352030351540c000c5807640000522120504e1840c081c00c9224445946403400000e2510800925a400c0406040043c024039546036084c3c0220740c082680040700c0c0d0070100711283c2c10b262802c000c60b40001c004003660381864a030450407012940490780c10710141e0000085c04207040d0403c07a00116940c0302c030240520f40360242c80c101414014404000c09010050041d00150200e01082074040c2840c40c9040103500d8031500010083c0883e00e0511032001004821101c1802c4180a0030801c454288015451a2a48801d010041c10601d0a00c00c001d60349183c0715001840a000410880c0d02a030303a280b084600702035107419a402c48601380da0500507144000c22040d60048140c414090000c0d808480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 254142940 1250 254141690 254141707
    0x1150b0f120c0912100b01050a0e010f090b070b011805071e030f02030702060414070807051c080a11010608060f070f110106090617030f0f0f041a0a02010e0c1005 71
    0xc050148098450f4845180d8890321503aa2000403410160741ca50030702801b110100f640103503a00d110312250302000031054105140359500030151505040101e261250303c1c2941c0d441000c295070022103044070729664002c010000504004d001125007c10000108600e061000300a003008030900241107000300400c40018145000e60700080c000c200c144425590391170300b90f500a445140445040740c00e02c0d0000d168030064140000c018054802040040c4440f074101001c21808000740513080600f00941c1c03c1a40002d80300720045d00021400303486840f41e00201d41045402c0d079840c0d41041195521810801410044d004c0c9459040040c1c0d04003101c0303000d8882d20449441000c1038800d030517982404000140c0024943c02442211003690308040f894030601645620780c42400c0386c1c2d1007007940601490311680840c80060031224040e4010503d02a0b540c0910714031381e51100c501e1546071401084c4030800680a0040032000e40020010b800015030381c4000550901c100003042c420040040398044c13 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 254144190 1250 254142940 254142961
    0xf080601180e030d050405160b09280b091c0b0601080a09140c0406090608030405010e28030c0909050a030315120507060e01110c010807170901150b0f12 67
    0x40316210303500070f4036a40c140041307111002d01000da804940d20300c0707070394801105004603010442c02c3c0e8900d0030701c8500e40b02880080040044507411000880c4c001c54850481c00070748a850000141644140d443e107400754141000b01d0000b040d9850705100480b05118070000f224000c1050340600d0908001419817075810081e0002c0c166080001c103e820310004c060003c1c10700003142e040d000740c2258284841340d03c503062282560740520039000664800c1c802440b071907004461300c13000e440f00a0901810408081100c0205844454501c100d081c4c0d201000d00501051a0300c040251200c0c0c10213010203d0b440e5581c1d43d90740c01d41e80000d0304050b07407174610046121501000b42d0081c8500541044001120708060ba222011882120041507611542030340315401111300e85440308104000e45103501d81c030703801918240030040c01e4904000d60300d00b8416901c00416034540c0240d0100340005079034000100382c07401c80c142a400030a0f60384002e0214a000c9200300048a9500100b10a051941d0321040e1106 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 254145440 1250 254144190 254144201
    0xc0801082b11161707030201020a020d0204020f040e100b0c030a03271b06170a020a020304050d1b062a080d1b090605040e01171f0212010f08060118 65
    0x600c81d400382401d04041d03544940e00f5281901d0101c02122405206098081d580d0b908034130000340581c00c002d12a0000d450224011207404c1c2c00a071025141c0003a042081006a229070030041c0c1e2003291105001c00c1d09800c0311610017800340000c0c4c1d00d140084500100f60b0324004d080e00f1204054548048402503600158980808030b000d200030f203503810042c41c04404004a40980541c9903103800fa00090741d40c800d0b80054010350104408000c1900c40382c540d00301a5000440a1042d071000700000691511103002d0079001c2070040322000901c05110601203940005548540308005807a40480070700b5880b040e0b00d41ba90035440c0c40d20080102d0360301c1c01c4101d6004001d84042e0b560320384600d00c555141030402d403513000030240d0b0b100c0c4400b50b00e0310070030b681e540654003d00214450707040040c042005191002494490311104941c00e0441a0030a05031010001c40041d030440c2d0081545482e0700c4105038103c0c05400000c2d00310100030300f130040f0746583c1c15051044210801400c0002c61a4580c2c55005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 254146690 1250 254145440 254145467
    0x5040b030c060a020a0312183008040201030f0b01050f0d0b0301060605030603061315020c0f06010603020d060e2a12040c05010e04140610090f03060c0801082b 70
    0x1400c3c0c48411000c8003946072a0400c5042c0c000c40e8200c03a492200742c0e031038401c1d581c40c0c600c0c10b030390480240c85c0364417240560392100b8561100c001806061451007181c0c00440f010042159542d8512850a44001800d46100b18100c2c000c407403d00712010307460f03038008054842c40c14100c011035482e0ba8000070381c14058103103003d94540551800c0408120309a009004500c6410158100da4258441e551100040c5070101400b41c807560b140410b01c10f6500142c3c00811561404204841c0380300803410506007082c8080c0c0c1f180c00440c0e800500d5a81c065900e00401c0000c00b09000c4101750380c0b600c01c250000e00241c07081c44680c1d4000300281005525007000035640000d5400d552030b0403603d031030320b4a020071a860340941030100b0302e0010324030198a8180070704d14079058801c11400c22500c0c0c010070310984409180c0307a002404401407002c1007401700d04038614021801602c0109071845699000341415a060300034904a411699000c0304802c2039100710110101d90031024050b82c10280c01c100c9501422200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 254147940 1250 254146690 254146699
    0x10050c07050603271018112715041d0304120302160308070512040605090405070201110c10050c0301081f0b1c050d08100e0a0b0306091c1805040b030c 66
    0x8200521140064121920000340904201005241b000c0181d500f4120800a0101020f040c4500041c181402d036003e42c004c1c1018503000c0443c0d40088404400750840d40c0e007142e1503983c028521186018021607406d08140c4c003c0310642030704a850b0988030301c910702518021516007480101018420099000c0700f00d510b000340f10780d0340d40b285410b1115510070f50f01500d261140108900380300e03003018100c5041b2009519070500d44900e400612001e40340040c010025550303036400840310400001c0003030951103071400c0900a0b40c4000300503181117900c054000c07014140f05100500c244000003a1a11a101104591801103540c020880000d802180f40054002d11603c0c0c00042a04203c4200c040b000c2c42141074444d00b1036460011207031312804854417400510840700820001d20610501d540002c84110040303080802400884c2c83d00c102603490745420340c400b2569071100411080c0f40e284441035441d00048940c0d000031501c4d407100741e0780942d910a55079502400030540e410000b003c0c11100180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 254149190 1250 254147940 254148001
    0x302090f0301060e010e0108010c12090f0b2d1e090109020d060603050d020c010905120307061a010f0309020105070311030904060605191b0f0c030b010902040510050c07050603 77
    0x1141102c4104080c421946845101d03000423850b64010b003d800056692680c0d401e14480201d610000030f005110820f651025003e80a14041101c4511007889420340300130f1940707480c80240718543c4240780113040216241201d024044041e010a8100880b03000c0007903840210388810350018014018210025405403403611031600f0088030f60455005c0b64020303c01d442e0030086148041e0707110100001c00c1130001c2c070903500611040c41d01d0240d00780b45400e2542264100001075603401d0840c0c9586402508070b403048440c9016541e844030008060800c00d01d4140050316417a80040c042e4001d10000500b80000c03003034440303224001001035603503050008006000c81695044047c4c0301c0c0c0d0001c0912890515101c2408105a01484100b4000d504441c2d0032082d8a1090301c40117500c9100c991700319200800924000081955201d016002c4c0c071101c0c3d0016036035454101001400a045052141441000d10031001404000300b041001c881050740e0f01e5503207940e19094000c0707800c1054100b1403d44402e4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 254150440 1250 254149190 254149199
    0xf090b030708010e0c01030506040e060f190603060204140a0609030f38010b070b0115050403020315060906120a0201030905010225020f0105190c0f060c08040312020414010302090f030106 82
    0x9071191401d0002c7c2c03010021500c40500b4042130360039600403c42194004008a540800d00c1c45031240c0c00261302a0640003503204001c00b8060b600641e0003a9039603500070a00307001d5414035603114140404100ca42e42c12561030001c0141050b10f02c2d22015000074100c510a13418040006c407a01c2501011000700e908624420101d256151640712080709904500400030415007030b110100c6d1000d58026811040c1c581c6048030402c88030311b000d4105010041c041c040040140c50801a0400030784414050001c80e18140d4240544501c006013418401d00151547c02c3c1a8840800c0b0313885420340a11b00400e03900f0460524901910482902505082c00107ca200c0790011035503041e0300b1170f0720890b45080c081e0056401120310340200d0101c802945a40c0b554084e140d0b0140e44c0207000a84244d2070100d02c4085501c41c403080703a101421003000700da0f54604100c105940001801100010f05200f1400d06d803c041c9036100c8203030402c414a0506d6030000b2a04101e039030b2005602d01c1d00303074000d001380082c0d61603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 254151690 1250 254150440 254150443
    0x20711040504140d05160b1308040305030c010b03030a0e100905060c010605130c1b05070506040303080f060109060e0402071a09030415030507020d0f031b02010c021005010f090b030708010e 83
    0x20614004814040d81c94031041c00d5104508460851822124403130602c2d006407165219021f015284000b00c080b1980741000140205000e000298003d502a544510301c92041500703507018081c00c0c80c443c2e00208410850160070000845004905890840101a52400a1f150b2403001e400030380e4041404a040085010150000710a584090720201e403030880022110068940407164600070a410207900d40d441c2080c521040c8101d0701410888900941c0c401c0482e14950041d0010b50000d10a44104200d00000c0c0c2d0440307802c50310030700e840414203103082c0005007145044c224072403040c0d0300000e030f840a00c000750007110380041500310107000754202001c4152b81d0303900034490856103905000c640018076010341b003441e202e1039040c1c014002000c26039104599281c140221401810758034180004000b0344c3c0c04901c5e411060a400001c0e10f034040b81070103890001d036090111000e50a21006109036a02840d0744001c940390f5010124110700e80100103814050076030805c1080d58a460f9011105040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 254152940 1250 254151690 254151713
    0x1112b0e150a1b02060f03060a15020a0c080303130602090f04151e0308031b160b070e060a0509040f09080d05040b011706160504050301060806010f0e0106080703020711040504 77
    0x1070640f11004402c840c05440c000c8550010340195002070184403107a40548800d0003950320080090040f50b681d42ca41110150f00410440c602c070050340480c1845040040c070300c010001402540d0f008505600e031040605410030170102c8000c110540101d000c00603502d5102050381e00e550014001d0056002c00c490341400c03a2903030b2040f001e146a0aa0186150100454411090b281c01c030755500c0c615942d0000c41c0c0308044c880c50746070be4042e00030080c511100303000040c05d0307a04600c120519042402c01a0f00213040615010749a48690010440d4209043d000703001c8440282040c0c0d03000c2544407860b240000282459400508026400609295501c00030351105124901c500c00034101640c803100342c42800c00030300c82c8110312544134138080740c4034404812081103d407040d45040c6152030f8450000c80c2c2503a9083e0b00143c410b502400c0103000717800304040d5034000751903144031640d842c2d031602100408110b800340c240d20505d40d000500c0c4060020303100f0012500030000c1c00074802820f0a1800141d402c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 254154190 1250 254152940 254152957
    0x3110c100501090204030c061409040513030801170316020d050106170105010902040b031f0b040603090302012405060d020c0118020112060b0409021812010203040201112b0e15 77
    0x146007100120300803005100340d4041d29044882c80f40c0d00c0e81000025948040298070181c52007038140014403190307903240103440c0f0400c0c0c121a0110302c5603032840c0140403468180c112840d400324012116a102070000143e030a681c4520500070041032403070000c80d1901c00c0140e00a0030650820801041c03584900b0314024152500d00002c10003682e0b9000c2480c00c03030140c0c1c012815110010800b04515801e50601d01500a105da480302c050303541d45a40502240d40268000c002080e260300022081c141c081c8510010b01e00070b15440d584081400054042070403d5001e100e104120209a0710250400b9a050369100b111600c001c111820011401121003420f0200490000300c542601103030403843c034040c81d811103841409040c242411308000c45c0107034000f00b0300d1a41c075501c0c10f04115000d42d0b403014135442c000c0081000594a04041c0001059440e104a00c6840c55011409600028200726207120300464080b82c3d4000c03064110400b1180700103a8080a42d001c0d00d000d9524400c100020010025403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 254155440 1250 254154190 254154223
    0x20408060a200a02030d0b1309030306050102280305030414010e150601051323060310060e0307080304060503070e03010e0c1311190228110f13090303110c 68
    0x801080d500100a115a01010f80140c00622640201c0300036a000604101030040219030207055800340c2d28100c4d9084c003000c0d00000d8985104008a507018044002d15000d05003456111400c01e680c40d2130703114200c2030300a042100c0003002030180512011342000c240c40b200001c0c808454841d0405079202961042c0d52440740b02100844c03665802081110000c080c0503c0a0301a2454540403221301814443d000404107180c01129032641d441c00000c40c403440804060480090404000800a1060903841030007948500402d10801c030002082d10226580ca160982d681c1e694113074102c81106018102941560034404451300b14003001c984000b100805907810011101c001d1080b1040d00c044608100c00d201041101c95413a907074131040345400100d0760048543d011354900315800340c01600c1000e102000a0001d0943c10171440c00354188031a802180c201694418240024041c041c600801c440f0242d030740c0b0162020103029810200107610346481240d22080c054440648500c074918100d0202d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 254156690 1250 254155440 254155481
    0x40305070807060806010f0806032d0c0406050a14011404060f030b012a0521071103070b1213080a05120a0e0a08030a020d0f0b01021504110f04020408060a 68
    0xc0703218000d458840e0030305035a100c2d075847c0c80c05019100020042c000701d416000c0c440600f0070417004c1ea81e20a1860968403080803a4035403a6000508161044c18880c1c0301f5030810704100990382c2c0e419004426103403422201c1c0800050040140d51040d1110380c0307042542c80c0400d000a4a54012260f00c007003c0c46520705004054020004490007020f03040d640350103801000d401820605007400580b4140c0c807540c22034404208141440804a0500c1200c504094001842c0c1c41001a007503264403481506900800811341045440340050085e440002008400500018020419480b417203004940005c2540d68072000c03c9002070296000c803091340c003428050400700b24915490f22880b00c0321904c0d0400f8264444069031080d00c103a00140280c43c46a4007844607240300c91407480744030202c0f400d821001030074609450000e410120030480c1e00a40600c404200320105420b40c030100d543d40f8088400c0c0d8450745042d8001402402180c01402d414410117040041c102007c0d400b80c40010743c0469658030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 254157940 1250 254156690 254156699
    0x813031a01090f060e07030c020a051c0212040b04090e030d050405010605240304061812020d0f08060901031104020c0318090105030a150203040317040609120509010e0d0501020f040305070807 84
    0x141c4040780705048a44140900240c0018803235449000c4004803441078a00d0000c00b901e5080ca00340d0141c0e10070740c20801040301900c9603501003112040d0202203104040c00c01d0b01c2c0104001003401f5520609451a840319610282c041c014400c0301e0441c6c5445104200605050038031a0091286004d440d006441c4040403c1915000007803107004c54281e41c66407071551740c9681d01c0c8030140541000860410000c2c07020f0000003a056644005401b0745070b80240544000608020903044400c4211004d1023106020302c6115200d9445060540e5001a410010b040c061008180248208010720900e4000416450700c40b00e841c1401900e9a10120342c2c81200da41c0714001c00d61114584071000b0085100c58960060b0000c2e41d4020f076134428000d00702509110110b10440c000e410086500700d48065440c07003e8010001400344148503a442450b02a003811078083c0003a2440310303440001842400f07203403090810041c00350112000803000c0811580c9669403072074030700c0c6d58090502482002d030041110200c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 254159190 1250 254157940 254157971
    0x50a211b0210060b0403020f0109050303030c0c0105060d030c03201506040c0905060307080411100c020a0e0106090e0406020c03070c06020708011109040905010b1207050315070206040813031a0109 86
    0x801e031080318800c45e1a0915660820044103588480d8506001c4034000000d51684d05002861040740401c18140e43c80040798502c600f1200020000c2e480340b200b001c000d01c00b0a030b000d0203920b031083c0d0606048401e00c80180800c10f0200020805040c40c0c480c28035a05200b1541d01c20240c0220340c10394051002030201403059034207442d10300600380c0040c02440007071040341c41818582e0b002800342140c08241070715040481c0c1e0b0f141249402c00d012481c022048021801d110240c00000c02050500c01c05079418400000c1c00300495108078622102d420b0003060a00c4010b50480f0076011041084070341c0c070712051070801041e080b14400d42d0094018500001805030040c041c04003041c02c3d0601da246070445202c2013100030120400c059541d0341d40e50003501c0302c82c0c580361415603500c15044018882035280c6400c251070714140c1c40304140030341e00070800d00a0680d00002c10302e8105038008682c035100d00301d083c0c400c0003041c02948090582c8104007072440f5150f10f00707101075040c0d0700c0d00f90051280000480e048d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 254160440 1250 254159190 254159201
    0xa021c0212030c191704060c1e0b0105010c03020f0601030f331d100e0706091203081e0109020d050c070c031e0b0f01090b10050a211b0210 61
    0x100b03160880803248195200020440da860f170722030791500d00d100c40c40201940068100da00b2400200700d00e200c40742c0038402d600c8810700d80c48000300440c2842d06841d607504e0129442c18451103040c0541181c40700201802070103045000d80007a81114065a52400c010080d12608030301a5180e0040c2160858103180c1d100c00d011981c10082e41a203180b841c9a45002c0040182c0189118141041000c2070f40969091052180321a043c000c0400c040d80480301d901e0130000707603a002500717104048800300310707043c600d00c0807150550b05030910f00d10503540d03015a404941c4030a00c00310018a00500003088165042d400340100f00760382c1100304069075415160800c540f256440291001180420810005041010509019480a9504030f0740d21842d510140071400c03e031a038146d26201c00c8010b010000091007400c6403042c0403034403d84600d0301048060914490085800104a001381c4010b0031085503d001411000203500c0800070481100701c00500f000f481c072144001401000c51182c1400c204d070140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 254161690 1250 254160440 254160457
    0x13060510030f0f140f060a0f090b060f0d0c06020f01141909080c101a15030a0207060207021003020702040605031609020c120a0801030c050103091a06030a021c021203 73
    0x150b5421aa0703103c051030325400300300444a0300300000a40c4580e190501481c0808554903009100c1030400140480517a00010382000440746480600310100700b520002c01c1c1c00507001e5407012001c01e50350004c90100e88a84001800b24801c640c0c1c0028842d03030005800d00d01145010003001000c240c882c0c4650b01042c2511980150115046c03540080d0b455640981c001520407021107103009981c243d403a0500b54220b0030b5800da175544030420100c903060104080300148044030a40b810090310b0600c3d01075400054105945294003192400402c01258100c80710560028400c00e040c207600c1d28020042d602501d4204e0165040540c0000c035070400241c2d81c400310300005a03255070241002801c5000b50484c024a0fa114400e03801c8040103008102c008240b10000d560f140100b56040d030a204d102038050340e000340c4c101440c0400508c00304255030031001c03009410f9100d15185440b5400003a19004010070081d5110000d01d903045158501401c1940086100342d8518103954400c50b42d1036143d0040210 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 254162940 1250 254161690 254161703
    0x241503030c0303020307110111130f270b130203060f0d080f071b080d1404050a15120f0f0609020c06010302040908070b0106050a03110c070e130204051306051003 71
    0x1101e2000a00907009181e006601c0c0c03074200340ca0405440c2481c2540c0c070804000000800c00210601c02c0d5130301500d4100a06101c107000e42c1d0203403801760701000244801d004680302200d000d0010240e081190050194150b008110040b4800341800ca1070003988107607003261090700b0084005004c3c0c10070400380b021913600500d0890030445031702208038899010540480b001e440c92a00c9135159005007545502602d400c0c801080031180c8140701401003540c0710f0503c44d5005040c08104419610140d00030292044a10700d8100300c51900c000b07680001005503801105810200880d0f84805280d04c291300c1c11000b0b5030107210055584400400300d201d102c0c880c00310b540241c030041c030243c01e240d000170000318440c9080038944101912203190707192080c1c00107400543c0000e20800655072500401400303818000e9518a040540e90b0710321703500e8085200e0480c0c5010b0340e000007855040c0200c60b007800d013900580f0a2026182c40e04000b40c0c0d07544810f1003142d82c3e6288c007011494070364a5155180a5130303880307070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 254164190 1250 254162940 254162957
    0xf04050403080118141f0501080c07060f020909070f0e0a1409150907050918070512070203090d031101060608190509160e0402121b090c0724150303 65
    0x800f00014000c8480808611503252005079450084400d4a06d1244030303505055a111102ca0443e8108644e5035401a030400201d50b0074409540c040c04221002c0d00d41c00440055a003043c0d244510180c05009801980114220104012990401d52001c2c04d80c4190b50340444000307004080080382a40da000c0c0c806000c15400c2003c0c094180304082a41041c444418015101442c0f0300007440c2c0c0c1021070b66900003420104210000d030a10502020f00d0b440c003001c5080c1c20b8a40590700030011f0040c00f01480b4a020340d000030030f101e54000c2c42141c09240001d0f140840c18041c9050103840381011455002856281074400103049100317241b060700501c1684400c1c1c8045d07406654000c050500541f0f0f001c0d15018800300750441306024211072009021545040245c0c1c50b245c010030509000b04000d40c480d54010a00080801c481080c90040564048502807003603154183c2c00c0405004407600204150780043c850720100b1050441e00101c481420018800301122411181e1284e099110041c04104180d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 254165440 1250 254164190 254164199
    0x20d091a0c011d1506061c060b3114060d23040b0604110405010c0c0306020c01020c06010f03050c0d1a04060c0f0806030a0f14030c0c0f040504030801 66
    0x4003603a008a0314410001400c041d4001c507003600711042c0c19205484007150410b400d000c148248040c0300744101303a203a0840d440c500000400c40b10300c140d02c05002d0802e1507907628451566141d0020300070700301c540b03101d54941d0f0400d1103503c02c003082501d80c56542903680f05142005d1003010030310710664083c0b540500b00d04407034a040c844e540e00308540301e1148c261210003142042082140601c0494003000d000640d43c24030b03040c0307401d11810142040707014609101000c03214100e184100e500720303002032a1900c030080c0389003049170143c136441d00001d101e00e0000641c4650680150040c203c00880c400076103070142d17a2450581c0100105100003423080e000005220040c1c902258000040c03400f51200404190150042e01c91001d000c035012501d15944400c85111b403a480f43c0441b11000150a006036541407042c00265500800c20005182c0d84500500030200441d404148101d801e0035400c40e5115005c0d080403644810500541c0d6020782d5440010030407900c1c0c80c4c080c5c203018680640781c603d8145d0a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 254166690 1250 254165440 254165459
    0xf0c0d020904170f0a080606090f1302041a030402090601020d021b04061701050a0f060503070b160206040f0e0703020301150c1707030806090603121909170d0f020d09 73
    0x2c006030754000751a80380000d00401c1030003c116520303541d212a40c0d0748041090280c4404030150950703004281c00d00114441e0385901041380310400e41251502203980154225401034400c0e81c01c1840700b68001a403070214103540f50090b42c0114800c0b9103070062076594000482c3d596801e84d0321600181e01c0103001201e2200b0f40d4030035580070440903001144140e00d40210030f024183c60a40c1484581d5030700204072503008188240c8154910484082c00b600e0f10b00f40009588041d035008040181c0000104502040750aa4809175055070150960742c0380c969a0389041c80c141807510a20412140020003d0f013264402c0c82288d0580e000300b002043d4031400c0e450304131040341e40c3c405c08a54084004040200b042440d4000d050014840e2380d500d000b40c82c05500780092804050302090180d4005641c8014100c0f0301c1c0f041e600640c0d10549801c0740c00422030b80440c0c1c0304106912880e040c910141408586070030110f4044440c01c050340ba00c40e1000d000030b2049998138803010141000401c41501070210290 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 254167940 1250 254166690 254166709
    0x1f020702030c0a0810140c12091006032409080a0c0212061008011107050706050a0311030f070206100f060e150f03010f060203071205030606120f090f0c0d02 69
    0x2070100d4480b0035a40d00815181d04058004c0300b559441007001440c80d01c100c0c051007107801d892601c0c4140c0d0741011031040c1c0d1180150b03036800f0301c3d100c4c0c4c2070005400001c041200e55102c0d0541013041c007105a580c105500a00329443c80750078000c1e162110030405212071302800c211598450b100c140750242c9000c080b00d007555640c0701240d0141d84a540707449501d80401055000fa422144654401882d10b200700c0d003100c4c09124504000c50b81445843c0c00b164001c5161000c07988036041040e540c0c000c84000710001c001d5500124007407400442840403044880c032011340304121030f8085840302e40710716900c01e113450300c0b0b0300c00c420703000e5800304083c484c0750b00c6146503403030540025014000400c00d88031100d11a03045003240040d040d101000411180c59039010980060160303001441c83c00c1e4468452848040c5000d170500c0a2140000124000340c5901c81101d60307080c21192116030a0400700400040c9807000e4236440c18500c01c410040f002c503140440d0b40a41200001d180529040ca113a091191001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 254169190 1250 254167940 254167943
    0x6010e0c031b2101090e0a0203070b0c160602030306010e0405040b040303020903030d0204150915020705042a030c09170a1403090d0302151015140c030d1d1f0207 71
    0x600c00e010607624242906103030040b83c50104144074071981400710010482d50300320b180700c449600080c3e1441c00368601084c09400d0b0352011842d540c1d6061131000030341c903000740340c0c108248458540d4000034a060f07000c005140500404d0341ca056004000314200000c0d14000c1ea40584007210f01c3e000f040009010703070b00800d028580501601e04046c1e02c2c0c800320040b80c000d5482540741e003036014441c0c02e0260b1702c4060b040152840b481c010940140c0317101c001b5940c0141e402014003403039884000c3c0c910115095250102c041011011484070120454000c0107064441c0c200404504a65804240391003249121010f4216800007401151499100c801c03400820181c83d507814001000010a50385403d80010303001402600144600c0c2c41c0d0b5900b03c6288500140181c840e201d00390400d0160302c3c1000f00500c810043ca1a0400c580b001c80c3d40340701c17064480c4034204c4210b03200000c0c48036000807032038002c2e001d03070150022000010312aa03541c031a04c83d075185810b4244480d909114400407012980a0305030035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 254170440 1250 254169190 254169241
    0x2031501030b03100905030403050c0603091905070f080d030b040209031b0a09021303050f0a0b040b060307151101060509090a080f0c030a050d180803131b061106010e0c03 75
    0xf0701405581304554189400f51500d400004051040c40400c001c824004201502c1c070500e5454241c100c513842d1200520741d540d040c2c0101607c0000e10004111220141440c4411003807040c4da180380c2c459841c0d402d9003181000c2420411441b40c2480c01e0b10030760384445005000380c50818200a021401154080317100d5501c8980d250020035000510710251180120048115503190304500705189415101040310340a54820241c003000190000001c5810603405501c0c02002d0b26020300113424028070740c107c0744031a13a80121030051580e1010204024094030030007040056100d01c20f200884604444000040d4030210044000505901c0100044903c042e902800c001c1039810b540d046a11401804c0001000821070f182c00098512400e500d089190411850411065585c142140001000609400946149a001d008405080310b0907070141091420216031100340242a4903440d01034450356218501c00414182c120301d00c0d56000e40e00082e0703103905550320364844001070582c140019150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 254171690 1250 254170440 254170453
    0x4032022060909030f120e070e0601020a0209040309051507170307050d0f0902092a030601020c03060405060a05180c060f070b040c03060b03030a120e0c0316030507060302031501030b03 81
    0x1d02c4051190001a500c6591500d114140440c00104056045c01c0d001141d64600f900c0c0d900490700010360700c000c07139490801c400150303074403540141d04240d5a9000a500700941c80d040104155100e5524400d466044907040482c19110b010b10445002c0c400c2c00070704810510340d0400e41161800040d41d032105840ca0314502c4e000d040d000300310540d0b5541c84582c080c60703168580d9a0440c82c148a100e9406100fa408990703029018101d8036100c1007600016850004001020031007d9109001c50811082c0140466885051610f40707259609000c96408011900d0440071841040340c40c5c0a5480f40c898250090990442d0801001459409180b000d0b951400400100c000140528591480780c0c0c0910501e0110350700d50b044c040266004c4604003031090700f0411801111a40182820442041060000a0b440c000354040e5140021818205600d449069980d10051740104066400c0d28450010b903841c0e1991110283d0036408165020f40320110b12011400c601d5120364008516040010219400d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 254172940 1250 254171690 254171699
    0x406261e030313020316060206070e010c031b110406080c03190b18030d061403010f0b06070303090f020d050a0606090606091715090a0606080c1f120c03020403202206 73
    0xb08401f5800780c0050b0b0824010010769070340042d24403440f0502070806a24550441c0c0d00105444154089241c2c801d14600c9000c4c240a0051088010090301030f008101d45030715410402c1c2d95541c0c2c005550b00c244a042010b00140705402007074000990300440100158807001030360400300750400d0040c09248801c0c0701c2d00701c43d1011402102d00900c5140100c03480450644145401e40c0e083d01000340b580707403d00e80d10144644601c0d088498980d01840c001890444529100786980c00d20800139601c00d10026050061107000701c2c0c00100d03148200010441c03940e54071402c0c4103460084c452800400e00c008030402611656049100303c41c1c02401c20f49080131007034200d0070801c0388140c8800c0c1956001440c01720400080d441400054114200200381e400c0628000400c60480203140680000c0c40b10128100e49004040c0f000040442a109111240b00004000e0094002d44002c2e43d5002001003400c00502041c6160307000380801901c510f400000d0814000e102030031801c09814030f40e650b101d0005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 254174190 1250 254172940 254172973
    0x1503020f0409060618080601050d020303090306040305040612051b090d060e0708071a040b1e0706090b131203021803102c07050904020406261e0303130203 68
    0x142c1001000003d2050602c04005c2c603900090500300e0884551110078450000c000420714119034045540b49000c00c2d03944046429405115800340c0c05102d00c105001c1010341040251055510540da90900030b20340f1100c440c10750b4000d650640c03c1071a17200c610901041100c00030440c03004041d08080d000146551a8001c42c0c01c801107d03081d40d00503002c00e000d50001400518000c282c41e4a50340c00c4010912a40e24451007030340702c0c030154040c0000b1a40200800f01029000c481c08000146464241a0034110060048600101c6a141d080000212500c10003e081021940c00000c007460920b40e94200313400a511641908101c0400300042d8030707050fa005c102070903000b406424041650700744180c0c101c031009070242032250140c0c0304011140510302c000654004844084809580d10341f151300105000707203403607005a0b00a140c1d5240b14034454003424a41948598440c1c112043c0e400007043d4481d000000400c0703081150000c10100d845e1348452a80b10a40700d0004064a100f03200380e04110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 254175440 1250 254174190 254174197
    0x5180607050a03020705121b0909011e06061205012102030f0a150c020c061608131e09020f0909040c1e06020616080109050711010e0f1011041503020f 66
    0x1c80c0141d0015400b4030171807e04e00c2854001c000ea030b4004200e210500244040c5a504001c40a8000c001450008020400c250000e100341180b501a0041c060080306018004d480c15000c3e103c0844c408410b010a15462031048904a820309241101401003201c01740003608841c00059a00d841210a24007100205115030380d02c1a00c14076144981851001c0c2c84001d4400021644003035410114501c640c8d501e410045900100343c071414040240510300d020032150050021a04000c0c091039404900350010602c0b140505500b0700c0c50002065031a070160090b8403070045040618142440744508905000c2812504588101c1200107801c0c2c542c0440802c8504200ca100340c0c46041d007004104180c0c0501105400c541849001d4420818114000d8080e02d4103201e80e5038601d43d140c0001d9042c610030350341d40c01e810149100900040c0c0502044903900c55072651402e00601900403421082280380c8070310281695041c03034040c101450718080c2280c4800c540310010074160200401c400d46000c0e05d004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 254176690 1250 254175440 254175443
    0x6020304050a08010b10200d050a02060f061e060d2f0307140d090f0318050102060603100203060105040b040e0406060e040b04060e120c0706180605180607050a 70
    0x55403034620704802c200d2800000e41c41140b5070f924044410195448131180381e1899455401d002054040740042d60280311030500070140d003802610140146141d21000401d40104a88d0032518151101d24919000300800d43e201c0b544440455080c0100f695921800c0201600041c540c609104100c0b8200095404c005406c100c0380c500d00302111a50852135840c00386650740c0c0d00c02c0d07a0561502080c0031300035001013648802404000324085036112102d800c190741c090f501c0420035814841300d2401400c614080000d01c8054a403105011916520010344948100801030040100401490320b6400950000e0405810000c1c01c10000c1240044040108020112012050184c0c6040e00b0f1020072202c0d903401c02c09030590320380140310200e40702052050300f00b500038100185d40c40304042c1d5580780401140004009400100324060080000b140c1c40c411a44c454031541111800448020880c013161301408000c50350900180b02000b4084408258021002d4100d910300700c1c01e51078451030030104090 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 254177940 1250 254176690 254176693
    0x602040b07050f0a03090e0402060714010c08061c0204020c0712051b040209130b040f0f05041202070501020a060213170610090e190f0b01120b010b030c09010509190602 74
    0x14650704001c820010400c9000b00714000e80300700300a540d00104045c0d040d07c292a00c04d50400302080940d51030b50200c030252030780710480301c0703440e0710158071103018003901d04110010940990001c1d409003058804107841c1c1a503d094a0880d030b69540c02c000c000e40007043c039002c19116a10020490883d45101d01800f41d008100400011440c0740c00d60b4200c0307600c009240c4c092070042c0b000b40056100c010b60b00041d1007041201050443d203150101e8018005901c0c21003440c1c1c280165140920000e81c03005000f1070181d41101d080715401d1400f0f90f42d0304101c0c03080a0041c0d10000459000c540d440d409010811b4000d42c41c02c000c3c0d5540c407402c0c42500b102450340c440b150040d13828883c82010001c000b00003041000818400101400c500c103031034403c250301160040c40311301c402c03008108034600f65440b4942d201d142442c240d40c58515080200e19901e03411078500700018008208a080b90302540e01c60442e440702030f894180108011262a000880040d8200d00011032861000310302c403000c400030b0002c590 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 254179190 1250 254177940 254177947
    0x20409050f04050d030212070e2803110901081510030804090c020c01031e180b040501090515060f120f013b0a020d0311030a05090f010503060306180a0602040b 70
    0x1820750400d025040c1030fa01703040c81002189502450415015448a494100000c041d160039001c210411500d1740c4500d00360b0112442e114503500001a01c0c01501d01500c04d4114809254042c400340410a001c4c84145500ca4100c030006030000c0740c0820ba00807188526444425520b40c0d42c48903d420980103005003985808200c0d4925504101d00311681c6001d18041c0819000c540300c201c41c500c4031654080f401c5483c0c6e14292845000410318008580c0c0c02044d2018514150074414007e1a840030101c509004906106460034441e20307115004400081c0b022040e07802e0300e002c110b040d400011405038075002e09481c02d41144406c0c452065180e41d04400504a240040142110401c030030000034105819140030080c8008005a26901554140e550300310320035407800c0c251503051178040030752030500c00040d9071741c8031a40c07050150080e00750079181c0d0150021084010341d007030300084524a4055100c0b0000410511000f5440d0040d17644000541751486251303210001030381c1c400d0300200800750f0000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 254180440 1250 254179190 254179193
    0x5061b0a1a06040903090302010818030310050111070f050d1e1101030506120709020a0504081e1504080a080c0f070b0402090f0108060708060a0f090510080c030c060d020409050f04 79
    0x80e000164080b504075000c01540c40c940d0340150800701c42e17000c064100400c01c2c0020300e00500c0100707c0b004410980341180e80307a01d8611134100042c1000c1c001c050001d1281310300003032400c4002800300180d49d8000e003225601030074402400002103401c4400d90b4401d580d510300146000311031940d180d2090040500c1c8100c05d80400000d41a00c4000e41924080c405000c0c0000d1110004503100c0181d504110380035907288a410012516402a0303080b08489028148240403052540c82072550a846603005070350391a01c00b81101c0341d4030034080740c0150140c01304102401c082442041e00715441030b8000255400d0002190110105810444040312503521650501084d0300e4010095603011900101c03560b00c1d51f041648954032610080c0c5520103004441000c61801e58032052040064031049420802c107136560940c16014040a0380d41100a90110101180512001c50f440089503c05070041401a52507800d00c250755110404001c0c0c215403d00021800e1074175806100d0248460168003504c60405 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 254181690 1250 254180440 254180483
    0x908070501060b0412020f040b030708030a1e0c030c150216020102061f050d03090504090602030106030c1e1d040f020309060901090c0e0910050a0c0f0c05060105061b0a 74
    0x640d0400041c3c8035080c0030800140c03da5411101229906031410400c0c00610f1010401070449805000c5e071600038180e01280b81c09001000c0c01c181c0000b0740d10140701c0a410350803401e0703a480c0e80400c1000689891a120b02190040200110b100d00c101e04002080c51100c125600b281c000200000807600300541880556134104102900a20720f0000b07035000e0451449070200c820310503c103641c06580c0d92414801410700404e00e0748010240a0000c1c4269000c5103400300003580240a1a000300e132400613100203981c4503034030f1029101e0f0700e643c50700051780d5a448242c0e40429600920b08010b2500501802641c9480c010b02c1000d044000380507883e824004c2c2a1030a02200900340c2c3c00d00c1e85480602800700360000f981c182120500c2440000342d46a1641a40c100b4030f90505142e000750600d001c0c072450486a0b84003a00700150b0740d854459402c1e1507241100c5803141c80201805940c004401800f192811074001d00d00f40d0010380140a404030000320440c10030307107406015100c10742c2c3e00c440320242c80342 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 254182940 1250 254181690 254181701
    0x708120c041d0c030105040b0a09020c0a20030d030b0409080c030c0606060c07090c140304030f02071706011401020c130c080105040506180601022503060c0201050105130e0705040908070501 83
    0xb00c4005802031802ca4144220f41c0814410144181e881d18021a860f445e0900e03a08007410f40b0030420741d640d004564a2030741d80c1300b1060048460440d4040c982c0c11040c449011010705260040c0500106856688120058040e60140c5503000e6690211040015565801001416604405076894905e03082000d030900b407000b42410f02a007800c20034902c8185020420b02c0c10303075010f22000614003075000c000b120760b00e044032500d50300100000180703c00e25810004095801003190f08840f9665120500f80fa61450040c108141c00e920000c0180700c0d000040c1100e100d02101841142c00c50801c0382d000be0107030342d03016855229095540d1403540501d54010081ca01405003601c0c00d1010b030524001046002c1c4a039000e000200840d0004616540e1084c01103964a4010f0305942c8400e01420560000010551004580d000e1400d032070070000c14010300810b8101e880082800000801c80c0040c031003e442044880340107800380100c00b04080e610351103840aa140500d4180745c80e040300c0d00e4a0303400c440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 254184190 1250 254182940 254182979
    0xc05010206091e0a0b0123010e030304030204090f0b1006030537110a11060a0e1504080d020d0e0d09030206041707050604080a02090703050601020a080708120c04 71
    0x4000004010100000007140900031401040f45142c0010910007142001c80d52a03004120b400d11000000d07182c0b0200c42619040d40b81c40c0004064240201c0054504003044031001e501908244001c001500c2c00c1c0c4d009078404c82c051241e142032500d407640c603814100310413a20200c80b210175080038065039505201d007542c0450881304140445440040070805114a8148106c3c06001c48403c542e00c1c0c10990000c68003051018008e1b82c60340040c01c8041d02d0240e201c4030748640d0f44030b4480000d102c40303c43d00468000d154088007800c620000000d804194444c010025200c014040210701c03100d22552000f000f4194400c0c40000315120510303251810007201d0780d188801c004e600d40d41400540e894408032011101c0c0d00800007405222441018203042c1e0a40c06140e200c44081030005260303002280b05076805208079854042c81c3d9803010300340c0899805075001d80c0145e00c68580300c00011510001010840c3c00343c0205418004017030512041140129181b81034054041010400c0d203c40504058050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 254185440 1250 254184190 254184193
    0x30e03031f080c0604090f0b1f0201110405090406020708071505041401200307020109020d060209040e0615190905041103060c09010503060402090a0f14090c161416060305040c050102 80
    0x111403400c00203135140954010940d03916941c034510b9103510f6040c0d1149035013100103000c168804224091a8070000506c0c1d040c0030155007408650034070300d000e600c129425550000c024005e1520342d0b8540d8402500056000c80f4420030802c1600049031140c1030803106409036540103d4107140178940b0f0784008242e813644034003981c141424036101d038600f0b6a8181c010f10180080d1522070f6a04441207004d0007608034007a40006220354910240540d60300141304800003500c080c811b4034008000207999031402c4480012529034803004103040d01e0310784081c207544020008000c0c501501c504002c4101d41c001d40b001c58609082000c0d04003903082c10b20030300b6406004100d050f803c2a0540340068140c0c44002c2101e44122340c00a040c01041c1c2e500203486020300313003a1103015021500c42c0280308040a441d810349100d100441c0c0010943d10f419400c0342d0ba85040d080f02070950302070a41d1b409040002045030603004d40540701110540410743c500c100020030702e907500031803079040034240040000201e03007015045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 254186690 1250 254185440 254185453
    0x30b01030b090106170a110a091e0b0111030d0b1504080604060f0626101d01110403020d03031503061a0906090601050a050708120711060906061f030e03031f08 70
    0x45c01010030043d207403603041121a07203071100c404001848204503410001c0080d240101e240c580c0041d402401d0005c0d4407000040001c0202c40c001074038061482c503550b001c2d542c000c115481c5a42d6213a006124039850180a03040101d000c580f0b48282a009600120800d6200b10100300c2805451b0052000e103502c43d007070030000e060800419070140162000d02d44e6400e0103090480420807170070815140041515802041104607004000100d91404198401c1542c240f88a20003500702400880c0c08903a801440c0360f10f01051650207030058450504d032501c6251000e070002010802c180565070000f5036180d00581d456448004015038208040c06c002d00481130682002100d0f608042110b42d00c40150510b06d860704c4240c0341c192500d00c180366804c40680520820b1107403050700070b500c000140301428203407145076803000c1d481a5152821240c41e030303211040c5401e0b4040c0701c0054211520041d40e625010070440c0d4040d05d01840c560080c0d03036000b0380c030160045c1000c8004100f00e100b80500f0000024292 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 254187940 1250 254186690 254186729
    0x6020306100c1214070804120b01061d010f050712030501051306210206071403030604050123010f11010207260301030b16030e1501061404050102100c09030b01030b090106 75
    0x44902d00f00394800d090001280c40d0b65160f140030829100c049600c1181113a81c0d0b9100d0b00051045035070f0300c50440c1d181070050004180e4074003810001d900070704526448044250310000448140200b0100700c0103004040004ac0c01003042022145084642a2400300721549001c007800103401c0104202094546003480501c80c071610f20035a03024090502d2000e601d8038243e03000141041c440da02c0c0041035521302203280082004048055442010211000c01050303a840d4001d0340c80c4080b100303071f84260700c43da851071070f15941c000e036030301d000e402a2032400710043c505200102c1e003244d00002c0c0c02e462000818002071926070300340c80c2d0b4904121035502e103513085500d540d8a882850380e0107846031109480c942c0071281c20754440e41c003021105940f003085480800305812440b02c560001e0041c1000142c40d40010707891071072900100c2e0119041a0300400c02e9030014100307440200899900310041264086000000c20741126105004c1c42c080d40c619182810407050071405c480d107a45c040c007418446900c03210b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 254189190 1250 254187940 254187953
    0x130512160909080f0d0504020906101b031e08092b0e030a0605040308180d090603020c010b0a06120b0a060504090e0a0204180b0f09070315110706020306100c 69
    0x14200d0311041000300340041a0300c3c1074280e600480c0c40c41d0520040204641c2803405007038012902a6000362024000b1341c582c1024482a000c00c51f0822000c00c00c43c81000c40c0086840c100e24121360700030b103060000e041c501c54902c0402c0c0384c0c0090b82c10020f040c1400b4481190020301c081700c0f840501c52680144030180d80781c00700500c4411042101440290412103105031000d1213000b480941c0316800300b1252401d45809006590b090b1038500050240d00c202c0d201401000030418060400c82d05c52014039460050210040d40c440c408004d059500c40d500143d047c1c4860070240003400103078039401d5240501130003030000c649144e08000e102e0090310130100086038000702244c00350b03034907114081058040020303440c0ca000d049410007500545440c18091860b0a48036130405014420245000303140c490b26001c00340c629043c6e441c0e550a4001f200100700062543c0a505503040c102c02001c111040090b01240c500d41000c04291610398001007001340d01c0c80c01c04105100001d446c2804d107000c103400d89696 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 254190440 1250 254189190 254189233
    0xd0602193e03040b030705031f0612020a091a0a08070f08040f24020d060b030c031302011403090102030f090102070c03030509030102091203070203070617040f020604030206130512 79
    0x1c40810210341900c08544103004a601070b100c41c807082542d03420490002441135100b224500544c03039030040803030149a01952840d045030440e035106050310407101c2e09140254494041c190502c00f1070000054101051494281300c1102d0036039840e214118050050100e00c40104000b0810040c80800f01e581900400e6054205410003a0708090300510719001a140001c031100c035441c18a805920b01b4000165001071410690120041c8807060383c3e010f070f002d0749003c240c400c445400fa05000081215140c050140161401490704919941d00194000407552065400041d940d4000080041c0e404400c8e00041e00190650001c40ca01380454441a00e0701041d8000101045000108101c142d03900b501a00c00340d2000400e02c0c3c655882c040b403407594a1b404000124040c1c0039007000050101d00504004003074616021031110660380300d60f10b0708018803641d001242c0c803640501c80440580ca8080141c8030001900030035060b054102010412902041805e1744100e80c0000d40741d06c034590882202 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 254191690 1250 254190440 254190527
    0x9060f040803040228090605010309171315030504050d0e0d02090903090604060c0b0a060e151f02010203071103090604170c04090305031005010305010e0112020d060219 74
    0x560307103d403075610001e81480c2c0d01010100c1d10f035800d00502d4141c0c45d110000d0804560a0050030059603607104015000c0e00d141240c09450400301100e40e0103044440d0700102020f10300000e88098103910b03203c0a9000306021025032000907035443c20407040000c10090101c81900d43e04003440040340b000c1c0084d02c20324a90305d00900440c1303a2000300d01e46804c10001d90b01e404500810f005d1b2a152148002455901c85c07500941c0c21100140c08558075000b03601c030300400d98001d0440040b603640d0745e1500e4009004080240b40e00140900a10302d0800482d1210b6403d040c0603500150741d80c00d04030801130103810040c6c21414550020001c01380d807540e0360000c4070110b44002c2c00e902c0018107110710a0303040c20022140b81d5085030506a000c410164448010341c440c00c410283d4111712629000114100c807003d00500c0c03030341c0120340010f000945961540c41800c910041840860034882d6031400309a8000c540d200805d03045840507840d0341904101c015041d140202e91001780d0326004030016803080e400904 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 254192940 1250 254191690 254191703
    0x40308042628030e100f03050c030c03070c0c030f0c0510022e150b0a080907080d030b1c050c01031103040206030a240b030703060506070c0e060f0a090603020909060f04 74
    0x804000c043c0aa07416011203480100311440c40c664181c17018140c2c0241c4401c82c0c000078502030000c3d9045071540140c070701904a03011903d04545c1e4a46080d41c407180d15aa080c0d8071003079411400000101922804454203102c0e03040c000e0b00d10300d0704081c40000c0c12011045025034009815000650005643ca12041c8200349a01d40320039117250360701d07001446049100e2184055200b40410301d8030310b032030051031010703802d82e07903001669110351605403209054001c031031072508212540001548603800111902c1701c0105681d094034801d10001c0c0c1e0410311031070100d6981d040160754200035a010710500b4000c0091050312071440c54203900244007840010b02c4041c3d01d9660b95a0703002030303158200c3c17a07040c0401400d5106010f244c4440c0a00c1c100d800c2280ea55000904048022a02e42000016500804e602032440071140303041c03c0422040450003010700e50080c2400a0007007003a13480180103001004848400507a050540c01445011040186040820b81c400000e0268a51a0f182942e030701c650041c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 254194190 1250 254192940 254193013
    0x80307151104080a0605070f020d1b080c0a15060b09130e070503060c040509010b04030201050706110f041e09090507030b0601050f030a0c08010f0803090603040204020403080426 78
    0x601145207020b10f030001c1525100b000c0007402008840d500050085c511615600b2070524915022aa52000100c03900c001941030070201d20760b8150245005040c610500130241821300d0303841e07500e107820a4148180c4900e40c90b1214449900c440d4460507006d000d2070000705152104810201e945860f0f100b454803031280c0c3c1d811071828002030a01006001d8403006080c0c07841400d24011000c840d0b04907016481c800c4ea005400042c03805544421a0201e0380c0c1a1200341c00d00c12251210310041012401c62801c00c07804108280d05100c502000b40050301e006060480d1b102d81041e1400c8821441d074000c520400e291001035808200009021800c03290320884036221507441c02d00494142c000c0045075000c000010081c016103801d26001540038092940e58920780b60f99426031004003440a2042c80c2c07641e0010418001641050001107a00500203000541361564079520340055902c40c1e0f0100070b4084001d01507880d0001501b010f003000b0f24a00c801448500c402c2c203000400d40e50340d9121040c00070035a1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 254195440 1250 254194190 254194211
    0x314041d01090b030106060c0b06030a0b09010606080a02041d0a0908190215060a1401090803070b0907170c040507030b1801091508070e0615041e08030715 68
    0x14212000360001610451814140c8500c852040d4000e0055071500d904000320100103040500ca074104560480d0345021410001e0780b1258008107004c0e024a400d806900c0d141d501042c1c024207824001d062510000035040e10f01200100800701c0a000754050300d0041008004404060461b00c0135542d8220040c1c58030745884042800601c520f16000f0000d6170007050030003256112105880710b203a8076409407a01501007140059441c80c044074001c0e40a03a9820b400c0c440754910211503054103606051410055031910383c138a1650300041012500d0095800806c44006410710840e4000d110800c05d941d031502240c4403c50300d4848000704103000b00d07501c41c0003803d071038400d41094a840b280503080000788242c8a80d04003072401c003402840c441d1414a980b000700300f0700341c40c403840840b4024800381241c1070401080d07124034030000d455268003034610700e91243c1c140c0340e00c40100000c019280900c0549042502d03400021101d65008928940050000781c0214849502118401000b40780006444515 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 254196690 1250 254195440 254195477
    0x90708010b090105011808120a0906170c03060301020c061303020c0d030206070f120906060303080606040f03150e07292713020a020c040506040b1005070609060e1c090b0703 76
    0x46c0d9000038042c0c882c0d1066140718150010062040c010f0503030b6102202c507120305040c0c03540c1352255224514002013000140ea0254000041c1d81c02c404003c001502e0545400c030118130748802501c0c1c01c4112660455803908040e0100101c03403045006456680e20701c1d4194401949900009181409000c2c2a1a0002050344150600d0f1078184a40c3c6c2e08109100c0f25003404001032440740003c0740851030700004108030380b4040701640c0c2101c3c00c00034040034203821030741d42003005080d0009a41800da1610a0171034440c5d07061050fa40a40001c941002c00c00c0d40003080700798903001748600d0005044040242c118890b41c2200300ca9081d048458501480d00070329008500070b01c0c7c0404d1042c1c900e07440891002e810590115039a1a803a004680c10300c130315107400d010070049071100b1800f107070300c0800794200786034031f07400303203015041950180c20001554806611400700342e40107180b404000c0e8010f0200140d1400c0e8803021f030740201c00c041c03400c01d9040d82080102da446128202018083c09920101411080e94 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 254197940 1250 254196690 254196737
    0x60a061203050904230702010b03030301083c1f051501181e0501030f18030c030306030f2906031f0f060b03041e0804051203120c03090708010b09010501 67
    0x128291101d00d00c80d60172501064100c0c0035601d0340019420600041150320380001900d06a56035040645090f40071501c0e014260204004400ba122284c49950284000d401d61074031a0110f032035001d4242c880101a1848040102e0b9241c568000d1415082c04503403100700001c561119000c1c202003107406419000001c01c0c1e032207a442401d25403819100310009403200701601045a50a880a00c548244000004c0594180c0003c0d04c0d00078000341d490b0b60200b481230303119150040c024140024081d07140d454075403110390f485105943c4400c225480081000c3c015000c001c429000c10700641484c00c00d100042d0b100c3c440e02108071040a03111100805604850b404009003025080c400c20802d5076503214040c0c1c0380c01c05c90f02900d108401000a58440341c090703008001c1a58001c03030480c50036040004020080c815882e40440302c0c8410300c41e40c0c400301d903130002c0300d0b0140c081e40340c1709501e030324000100c1480c3c10f1407a0071000322641002044c060700d40701d45458a041d11001d00b0a0002d000210340300c91000a03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 254199190 1250 254197940 254197961
    0x408090427030f0e03071d060d150204060e06090a0506030603010b06220503071a0307030f050906010f0915030609030c0506180105072a0c091409060a061203050904 72
    0x8640140180815403c20504004080035481e020010010302040545420312485010b41d0440c0c0c2d03407500d2180d4000052465403011005120005c4403469032034401000d8030040034041c0c2960b000409016040d040881d20010040403610380307103848607140c04a4400510751081d60302034003010001c510b1a582c01e40185442c0d00000c2c040340d4030b9817044080340541d256600441c942c400c44058011400b41004607413001500d60004070307081d070b0388040c0019000135070000341080708040e80c480c9030648958003070080e2801110300360020403065041c058909007020742d5a002108241c58121030400499903001c4503401c0340c5e0061000a8928810704003030310035040040c0c0003403260040344c0400000c50402d0b00c0c00030240950034020000d9540c0c00f24141c9110888032514103012038222765100420710002c1e0900c240c0c1d84199801b102140d55007070280300b6903080d6203200c13580c107003060100028003400f0485540c0c449030b200b03014001e007443c024002c029400140f80c05810001c00080c101440e44aa0b00140d0106 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 254200440 1250 254199190 254199251
    0x1015051201020415020a020a170a060908120105010504150513050901150f17011202012102040302010e0a050609090408090a03060902011115010b0c010e010f1409010504080904 77
    0x16404840c918001e60103400b400c0c1c0035034039401c10310310443c3c0b001800ba01c04603406407a84900e6401c04400b20010b40308111007102c0c6101d00944100050040c1c000c042c0610300c25940503403a159005400e01002030144c0015040000603c410040314600c00c4031030080307205906105548010102d000428120590000754000001c0ba0002922840314201240700c94929510540e12000e806811a505c901580d0b070820b1001c10710005001500c0c40085202029205040401500d000d82c050803050910460400400640c00b00b41081036580003c10342c103642e84100d43d80f0f14600e00f06030010f41d45002d54054680280140740c00542003180325000c4900300765008000b003030911341d2481d04401528030440100c0c0001c0307281428549403c4000356a00d1070614048100c03105030308010080385140c06c040c1c840d008a41d224800d400c000c40e001c1c854104400450140480c81049031031400d81c070903c000d400815241e251408000c0441e1250050b11100e0324116004610850010760f9040c0b5900c42c001b150420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 254201690 1250 254200440 254200459
    0x5070507150810031101050a031d061005031218061605010c11010e060f09070f08070603060b0c06150d06140a3602040e030c030315060c101505 63
    0x4a04001441d030500d42955652215651031904030594145144001041000601d0b0440983e60148025015007901c51800103420040c0030f1202101001009881c0c0b00768011b2404d00081c1d804103c04c1102402007540200b11240308080346c00120322a5a00800702410503007004007050340d0300011259030314030403078640e64141c2032b42c108107000b8146602c4d590041219131801c9a40010f040c05415509000c0b00040e0040d0350b59404010705840d0b00500c0315a41d400342d44804140e0642c2d010400703000d0400c980090800d1401c00801a08641e0035400014044c40240500421213200046642e885101d454285811400160106032401c91090703000380f0450400c10548141d00d0084045486024002c60038014600746ea9a98450060000814061944c074481520b9228040d5003008001c148042c00002da139004295080c0e05580007081200e110350030010a010700c1e03000070480030300600f00c1290b00c17070320385003130070342c04996545101045a07402901d41c822100d00050000341c040007050040c201018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 254202940 1250 254201690 254201699
    0x304080102132103200111030604112503090312030b041406010c0b060a090504030507030306050414010509190204060203270a0e19110306030c0904021f05070507 71
    0x40c1d042055580c58414030705400289802ea42c030040f88903030300010b9403103403000c0b0b00d0b860864800d1401d20044500d0050854007020300982440790380e4502461180c41070300e90820000304401d4443c0d54074041007003642440f82000310650042d45500f10340341d030040b400d01c0040130b15041c0c0d4200001d90005c0d0120040646c500300d80e0b50190014008020211010820541c0aa00900a031281610f0703107800515104071580c00030705440c6501c0e8115030020511041a50b542c1c00c09415980221400c600061012a88008060f010300507030b40074240858042c0504500b094000484440510072140b050601c100441c00b0b5640c4000d0040301c61000000030356840342c50302c1004c0d541c0e50244480c02c2902d06c8003480d200058070550708400580038000c182e000b00500c2e1420164414501810107d90014076860b103151402c405c1c03082ca0801e1100202c46901d03864403004040c00c02d00d60b100b1850088480408200c0180ea486c0d4013254881042100e21030b80c0e041c7c2442c2103440e4002d083e4003c0003445101e40c04507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 254204190 1250 254202940 254202943
    0x2100305010e1008070909030306030b0a06031401090b040305070204020706061401020f0f03030408090312030a0b1c0b0415180f140714090c0d180201081f050d0f0203030408 76
    0x1410384000202d0420315464402c2005190b08107072140c00b00b40d400424041c041c400d03040d000120003e0203807070082a07658490b100c20301c05000c103549100c40303540d440c502002080040c4031b90b81e00c48003242e4020807200009845035200700310003c00080401600041b01c40442d500c1e0780c140c840c0144c000d9000c00210752100840d41c1841000308225015224426443c1c1c0405070010396201040109005941540ca807661580321580010100c0365240c0142d8407150841c0752450003444c070031001890040f84889002c8240590030103500c031410408000e890749000402c0131a00e04940260b885101c0d5240403844681c040024058000c106402400130401e010520001c0307881d444405015014000740c0c442240300315580c5212a200d6400c44040d5440070442d0752a04503000f84d402520800150700d0240c0c0224440119411a030800400841c0c2200c00d000750350b4000c042d40c0c2d100302d22000300c0c00030035421091000000d24a10403c2d21038400ca085110408c1040c100403d00c565001e021651500d0301e610781c2c507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 254205440 1250 254204190 254204201
    0x607020c090a09030212070804080d02010203070306090c021b030c03030d050a0c020c01021f1805031b071d190513051606080c09030a02060c03041806030206091c021003 74
    0x80c1c030031600640411111a11446101e1220341c1c1500140840b402101c0d1014454200041c00c0d14500024440069a94414810820000296400182da070300d40b481003e03084a08540009500c036140c4408000c0d500d0300020100120307078442d030b412004ca8000c000004d00c1e003181c0901542e01404042003a8685000f640c216074003601403400c00348003552800d54101d90714841c500c0c01500592000d0114603110b61041843d8401102080000c56001007130a500010b012804100716100d500009850038203000c45a50801d581c0c11040c040c2480d103161122040300b002c0000c0c0707010307000d50180380400e03080161981141458002190241701d14a00030401060f50402600291014003800c400403400c60080540c0d1426140d281d160848140c40d90703020425503030043c2d81c15a815104011b0801c1c0941c3c1c2d400090881040c84000840d5160305104851102c030310450b00e2280b0950034440e090006030703074240a43c2d012000588542001c00c114480c841281c0c01c11782c401035000071000726185205070781500003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 254206690 1250 254205440 254205463
    0x80114040504050c06191412010e090c0306040c0306050f01050f1201020408070b120c04180506010c020310050a0b0103060f05090903070b0a06170a2d0501050a05013201050a11060702 80
    0x900e03941f0030081c0c0d4030f0313950b41c4600044082c801c8217000061040702034180c0c0c2c0c40d030001302c088110b4110610f030b540443c2c5440360646007034900300c100e4070003001000603034000d00394800b05280c07984045515050114100c050302810ba24800c02d60501d0001c00e00809505860007040701908440700240c2d00c801c0c425059001000322400251074000240307600405004490840307900c41000b001d2350b800951220010a0081c051904000041081001681c0e0402c10320403501d003880c070000f86d14141003604208550740001c450b4189802e0034005c01c5440c1d41038408604440c07040e20003000369610340380500d040d84a61070004050303c6010042c00342c030714025440340c0d05503440380004401607449440d03400e68850640d13100401206000c0c05000250046c803050081101600c030540c00c00e00582c0d035440f4290b442c215070b00444e0550782c03401000801030890030303140712030f005074a21003035280708168940c0508092041c03103042c0f00b00010001070142c03046030000d203100d044106440090519180094a6203002c01c0c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 254207940 1250 254206690 254206697
    0xc1507030b01050310060e1f170907030305030a050903090d0c090507080f151201091109060609010914300607050c07180b190e0106080114040504050c0619 68
    0x25001d00303502610849005030001e18095050b1498900200e0303250216850103500b0000140406802c0d4100210403034000c191604ca14042c03083c0300d01c80316030400004004498a42c8111382c1000801d802a045a0f085030f0340080108660380c0300c1c01c2d590716600c50100c000e60045541000202800300c2807580341c00740c030f001c00400d000d0398407480011900e01e40306403011101c26600b80c001ca440140d110306d40101080300a03281e4115100d4200c500e50841e07150b80c1094540d48902404a603503450300000f4a60b0140044880504102d0038030002040c2d42014000c0000410442c0400c00007940c4042c0c0081104008001d001c004281d00300c000e200240480d40340c0c1d5843d11034600030072071290266040c0c0c0c0502d08c0c0000102590b9292045059821266280e02aa81541c48141c040380e501ca66040c98103000d410584619005e20305000c0c4011704405a00c44030400004070f00510210200000c107040b0000126404070b0a915641001810060401100c6500c2180092030740500e00d908500c41080d041c0c0c0f40c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 254209190 1250 254207940 254207951
    0x150810080c0a060c0501110d0e101109010f021c0f020d02120a05070215160510020f04030b0408090a0311031002120a09030c0b0709090c050a14030c0c150703 69
    0x100c0d5481108801c80c50b840900381e031041c405603210f218010321243c0a0000803981301c0060416020a620030340c1d02c0740d07070700d600d6a01400099000b001400f04203012108100000139001d8141865401550001810404070420420085108214003035090040c1500341e82c00740d180d03540c0540103e03112051032016025503050014814008034440400140a071915803511803841c10803110741d44130313410480c0d111440f145074907406070200c0301808599850a03420700ca60701350741c03c105180904c4001f4074407215004020040001c8503040680b421244e0220401c0000e40b41c601d8030110700d01500074040d42100300c4180000600402d1000340150140607010303503228000c0d4001c0301c8147d20542010001140c40c0001017440c040340b41c1d000e411a60b001e80340c244127410703e50b52038060102c0140c821000181c2400018000312407a407141d010a01c0d4030342416840c142d00400c0250003030900c6c1034082030b030600100024080c584c403907040701c1d800440300b41641c180c7c60100602d105019001e071080301c000303440c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 254210440 1250 254209190 254209199
    0x507030207030314070c02060c1005130c0b13030609031b030e0405060a030c03170f0a0503090d0302031311011e0206011403070b04230406080606010815010f0e040204150810 76
    0x2684c5550041d4616a1081c801d40c0c03054003848078a0740008400b01451203040c04080b02d69249203d082c0c0603440010f6042c45015582c205414581400d4110356810341c1c04110401810080c212080207d0307503c6400811071884506042d03886030b000c15402c80e000ea112906000030150b00c41500a0381442c210790070000b0f900c3d11010300c142803003a400014074000c20000d050010131400741c01d40300100c5681110f00d1030600c2000c595002c50b00005403403000304d1804410b00400090922980c10090440e140860540c40c040c031602c0c201c2a0b6614000d0811200b24118584130391140c0c01c0030f501444500e5140c3c40c2401c80c81030081d61003000b48a1070311400094030302c100b07041c0b0b0081045c00481e41c5844010341030a041c511030b909803041e0b03103d054003808811310706144c00d0b8445010340c0000382510350251002c0d00c0d00000160280344010403a440740720401e110343c05542c4c1c0001a080180000d440c04011075032414020800901c604c0d00640c105003400101c0c83d82580c1e104098510540d0621103c081030703980d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254211690 1250 254210440 254210471
    0x1206090a06140603060a0b0c030310120c03030c020a030c0828030e100915091401020c10050a03020c010e0304031202070e070f020307211403060607020913050105070302070303 77
    0x1d90080038080315203030a29202500d0600d000d942c22000040001c5200c0d9501d0306212901d60010325072030308581010080200d850140545040102102d03a03a00045c40d00c40c0c1c1c3d03403805001c1140002000c0c0300e564040002903460b2650b441000d52703440240040a0381d200c941c101d43d00c2001d0900c1120f501241000315034404000e901c0290643c0c0c0c56207614401c03004120800c031104948401003410400444800a040b6005c0d080c1c00c90303040c42c503403206a58079061142c1941041c03041c002150540d032240742e510030252104000f081200700e080c0b82c1076480d51100e04084020b8428004c20450660070181442c803c0c20000c00200101ca209240d880e1603d180ca0070180d0326415603200c0d99482d60540000181c3c550301031403511019269900c1035a14119055591541d000d101b04004054650301c3d1002d224500e40212802030010b01e50700b00e460552070050001381c0305224440780203005400350004502a01c801038070900c58158000002d100500e8a0300c801402500300900943c002410502d071111003001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 254212940 1250 254211690 254211701
    0xd1d030405030c0d0c090216060c0c020f0d02090406020c010f021b1603080a03020d1d070f0f030b190b0a0e07080105060705061f120b010f090519180204021206090a 72
    0x1744101007800191810700030344000d41060300c40003091102591588000b0f5918459540c190f042d036140c00c0a50079450042c404241010b114040c002d030404026031f80540d4903018190b6005920010150b5120740c1c1300c0059001d412030a2400038401d00101c0e00940d07103003010000c4180c06c0112400c5810b1200c030b403200e842a100082c8405441e0030001c00006811070701c203030000e0841c50681c0002160b800c28001224000c0e209200605a568020b20028444130080c051044010079003105030554690441d1500c0340e24000c0030340f29040c0c14a8003c5601d40600303142c0c100d90010b2200400c0100c58aa0390004003029060440b40c2030b000600d00000440d013803512400b42c911035074001c0b0040540b56100c520070700410a0f14a00705a0ba4581040d0006090740e072890b14000903480781071101c0da2545000344e101264180d5400005d001401c2c24204600481040342401e98a40b902e40042107030030250901040a030311002001e03401600009844161914100f4598000e400550380810320b90b544c8084c6604848 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 254214190 1250 254212940 254212943
    0xf060c0f0f09010203092205070f0215091203040c0f05190605070212030d0b120a12050f0f0f09130509060a020f090901120302061b0f0d1d030405030c0d 67
    0x1003080c01581c200075051400780075a50320600407a890000b6400010f100700285c1d400c4c0c40c581840c8100240b04805035405113942050035420043e042549114000e500d80076034100b00c1c1e0a502c2c004000841446080004024042c83c04403200d03681d040c1342c14142e001c2a072030700840741d40e00e242000014207410100040c01d0410841c0000b0440c2c1c605014046a056100d1101a03a000d1110307403105010880520050a44001781480001e401804070180070b1500140428010203030400010300c070105039120740203203500b0003618080b95241d81014244031540940000c0100740e040c0480d0351506240744000a003400c0750120b8460950f80010801c9000b40c5070103e505045a40080700411440c0f0038940140c465500740001403410300041c100400c1040070241d10410403035500503020418143c040c0845030700070401d821142080101d400d04442c50344a241d0074404401000210000c1d5590150300c0307100101890405070700c51b0402940090769075001802010300c6405440b6034540107141c8110f003c000f46 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 254215440 1250 254214190 254214217
    0x20a09180905190812070c14061501091a161b0302210706050d060b0c0d03110c07060806040906090302100e1621080d0608070603061d090f030a020f060c 67
    0x20402c00207807601c0503000340c021b80502111007444e00000700521580014405000018216440d01503100c132a801e601c0c2c80f00b81d042c010b108d41b060181a244d01034561001c084441040e5840c514010b014221508803d40039113003149840d620941100c0a43c418070403240206e40c1d034140301d649140307051907910510f410f004503940000009c1280e0f03400303203014043c1220420000144035558004502980e03205980c84412074000902d61022582c2511512106902d060b19107801d12240029650741d818403402800b003030100c14000660035507603903004281e149a01c103c05000503c058500079503502d0380901004106400d201c098000c2c020300046018aa01d08840b00250551070b092411000c10002d861409040710030032450030100e452000144400c825424002825524001c09941001a02c4d00107004150600d201004920320b01c49500342c0d440003d41401f10140c4520540500d82095075011890501000c20308142c9681c02044200541d0619015a52aa501d00050309164030528070500c486 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 254216690 1250 254215440 254215447
    0x150209010e0f03100c030e10020403020a06140d090f030e0108071b14030406020a060b0607030503010b031005120c090a150e0403090902030a0207020415030201050d020a091809051908 80
    0x750315142d41404041c64014090750b2011a100308000305450810750340d0301c01300f034072032210001c1c08104209400311009042c100714181070641d40004d01644080c03141230200850700710a140c118000c84111403002160043c01c0000000616203000e164003e044160301240e4156688000c07540980a41403003100569109211561104d00045e00c1680105090f00c640288040080f5880402c00040c006820b207074004010b80e00d518605501580c80c6025410300800080c041c07030001a402000b0303281901c20541031181c0f06c0e41c50500c000d00000c0b8551040e54880c803119205980100f010540708142c0b9000d443c400c4640d5641c18650081d1000c0342000f000c0800c1ca0f0008100c5e0518405a05400c9132007440e04802841c0c1c0e500000c0700f40c0e003040d1107010515a00080000843c86c0a00c1120500da080c0541e8a5a040c0340d500003070824080c150050050a4000649405052090f2000e0003c2c00032201d2040e800004610484000d05003581c044400b84220341c0380c140c1c54079001c079038280391035804024240f8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 254217940 1250 254216690 254216717
    0xb0a060311070203100b0909160b031f152c0f060427060e06130209040902180108011103011211040605120a0506060a0602030f0304020609090901050415020901 70
    0x60070707206050492444103014200040c0d40600c4142014424420081840ca03110800c02c99904006400240f440d801456001d000d0b1000d448118120741170715200c80e480355101d4598205030140c2030390721000a20042c00110382c40801d5028a81d88845595400820006483c4c1400c8580324503440c414508a500100e070840d850a545064600c9501a00c03003802c1075940c000c2d03042c100c0c402c441c114001c5a0220454148040b15100351801001815502c0300d9a09007840410a02c454151050340319540000b001810b0f03840340e420043e02654060308550340c14840f01004000f0503c20301540c5050350800510355145190481964141c40706503e4148a50756541c0e01c440c0300a41c0d242210f034000d07440f00c500151035a00c0240c1c405140800b1800f030104018245007003800c1000c001c0c0b41a21a0107850001e03c2a190700105171840688455203013681c80d03c490002031864021214840d500401d4103040040304070041d00030324042c0b1311410032218501c400b0314101d003d80c0619581d150000d0900c920408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 254219190 1250 254217940 254217947
    0xf0c0c11040603020303030112060b04020301060e12010e1e01061a03130203070e0a05040606060207060c03030e010b03010c0c030e0103020702010503041b0b030c0c0705030c06040e09010204090c0e10030b0a06 91
    0x10031050008000140300b555a90119055400990110301d40c8510002c4081c1403042500403046079080445045166604203080a0f1444e080d461605001750510040000412000d502041601207448200c5d42144004071300100554440d46604501e5400c2c40c0001907081c1042110104440356502c00500310758403482c9101c1c1828481e0400c1c0d83c144034540b8009003d00c0c7e44180c02e4001d400046002c40d40b0325040c1008015142c0d2507002c4002c640c440c44003000129880020101010b61601d004542c640c1e030492004d015041c900700c0e080d0700d035180580380f550b150380000e043c04100384a6102e00c222449514015012401580c00280c00b250b0200006800103042c0111041114040c0d445803141c5a1034180c0d00d40c05400455001c0c684000000300c1848600381000400d00810003180209501150322012440c0b40c0528440e0103295581388021564031042074040c0e401070b141c010b6081100d0f0701e4200c0c0c0103040c800790044040c0100700c01214038802030b2080c0540340741c0ca03d0152a8070a028a0b000048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 254220440 1250 254219190 254219213
    0x160f120305091216090603110907020712081b030304030f030608070303050a020a050601030308150906031c09030506090304030b01140f0603060a0f260607080609100503100e010f0c0c 80
    0x42d03000d4000c07000c04c031000c50410f503140d501070007031540006541d40c118540043d420544020f11031080740d5400130002c030f155001800c0720944443c801c0c4d45658091303600d4a05401c7c05801071606104c103003c0400c500010780040510b02c5180a643c1d840c400307000301c4000b035040301d0a500900605030000101072000ca0b006000404801c0c11038030480e05c03440442c1c0ca4507814500c0a82045001507000342c00d0142090320202818242803040750f4400381c0c5d0a01ca0006551a000381d050112b00e0400001c01a0b41540203543c4080250703000700542d0020b103000c000d20f54aaa00034001115803083c030308004a9080c2c5a01c1c20172980c2c1c1805003243c450000c6080c100301c01c503000100b0785580310f0400c28020034804c2c0201c01101c01464442010244d840903588041c0e45503030000c0001015130300910401410b141d0154825030048401c0e00e940c40161140800c40000c00c0954100c0c0d601842080d200a101070a40c4d403210b8003803900c0074003c01c134000101000c98295000c48071400c5c0000c3c811440d00d03003c1070703070403003030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 254221690 1250 254220440 254220469
    0x6050304020d080d0b030106051801030f021918060617040f1403071a01210602030703180807060e0706140d0b270f010e010b0304030e03160f12030509 66
    0x1103509801c00c554400303e441d8071030a138058202d515100090340909090199070040c000c111000381070658001d02d1403003030490500c0058405200c00004034203641311002c0b100c1101d10003210504000da2200c018410f40d000d2420b40c0c401091034044c0000c1c21a10848003030303400c28990385034007403180c585448a241003007403e0000d03110300f01c00c44200b51081000b00000c2107420b2050400340043c0307124034201c030081c1307030140d1120b20b0000605e4a4501e411002d5807220300c5003540318200585a1702c40030801c9004000441c0c100141d12951035141c01404461405403c1044c803850b03060101d215610071803601d420542c440d20022501c0c011060600e0302c41e4202424222005030710014044940000040800d20900516460007030382080030107610140d40301c02d980c0005002024000e55241118030164800140b00303600c4940c0b0044085403c1600ca80a0b404076010014200c0d0440c62100d07408034071100c01840760001030040404005880b1075042e510060035034140e1109800d200d413500c180620b000c004441d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 254222940 1250 254221690 254221699
    0x3141e0601060f0c0c0e1602061506030103020d080f030403050c0c03012c010917120703052a070f0803101403030d1e020f0a03050106020102191d040f0903030c090f0605030402 77
    0x10080303406900c51544901c47c241895520340310280e480c201905112000e80b640d84200c400c4950014a501c0c0c20b0202d034112a4155080c120110700d9051415050040e807080300388e0f415002060205050744500580850b192030015070341d0555421040608a510448070542202444469648800d581a200c000403108840003c01e6000c0180d072502c4044201490583c1a80c4000c5200100e41c041d007407000d6444a1390381000c0100f400c28511780d9025590b080060075264403000200710400c41d101d0b017078405c030036800f1140c042180700d42e140c03203040d85d0070882d501c82a5035030988001504c03000e20800c941e24203102a0146140040d01d9000002800d0a41c01c0d18100184446284003502030610003007103080480f1541c5612003459440003000e4030b8060b40568110f81c0141710b400d00d0300e002541c1c10104100030b810515130b09640c545611810b000d40d020680d0f07000e4500181040146070316007204400a109035010440720109140954080400c0d010f031416084d040700003840780328041c0d802107400500080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 254224190 1250 254222940 254222963
    0x106051b010b131d01060806101d0f04032001090323030609270303090705010e1f030f14100905040b010303050307030f05090a020307060f050901030b0a03141e0601060f0c 75
    0x500e0f07501b9190f15500c0116294422810400c6c2c108451000c10003400041c1035455404201e104051184000506120b00115012001c5000c250007249140306020f101891620107144168045009102200051f4040b503e0206208107801c0040480c0c030004459004442c207603103443c81400f55140005205540701c81c000c8003400306011181c00781107412090500115a24070303000c10384070304004080e8041414400c04401c0a0102c0d0341c2c1d03644414104100000c0325041c41e003207000c210040d040306400e0a21192400c02590402c10601210320300c24100940c00010065035a03270001c0c115602200d01400010b420030060000038401c1c00119004020b80c075003c1403011166409004558040d10304100780e90100e2a1142182014018880201210704000d00c001c0c0001801030070600c6000e00d07440c1095038400814465944d01c490500181d600311440c410108804400c003941d48180c04100d4038004800d000700c5030740d00e10001d011410f070380b030a030348500496030b0000f01941d020191120845100c4120b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 254225440 1250 254224190 254224241
    0x30d140405060708031503010506090a2310060809030a170928060f0903120b01051306030e061f09050c09030d020303060f0a03021c0512030106051b010b13 68
    0x102c080d00c02d003402401c0c42c40d85c0c0d040c42091501a1800310a034140240d0612040129517680c060216034441180720b00861550f040c640b00800f42003d00b0406049681080f0601c0002c0903000b504000f60381a030345950703c003500d514104581c1c901400da51000000e150014a10700949400b508a03009801d0720110340d01500003c103022403840c0148806410310300440c0e003d6040c08202e01a061131052118000c0090b5031041d200107200395003102c0c00c0011252a0381c01d15070a41d1203041100d40c0c01003803000341c54401e6222000107002d82003010300c5590324420040407035050300140d000d9a60150240c0143c03501c081c84c3c504207501400b0010901035850905000c40e4032a03807000d1103450483c034800d9000d565640341c464104642c043c118510980151056801440140c8681d45071402c0042c0b40307040c0b02e24501280c40c20030320b410741032082179006400110001911540040c064090002c0e240044600c000b88002c40c40d00b00c3d1900d010300e036400792802003188c08070081580031900540003410402c09401c2e0703c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 254226690 1250 254225440 254225449
    0x60f11010603030e100f092702031e010f060504030b070504081621050c0405040f380403120b0604120c03020411070309091802092e05030d140405 64
    0x65100b070f80800c102c8807050b51107260100140005402e40d0074036802d440c4803800010079501040c0035107000300d1540307482c90030044500180d28040765401d040c25903a92401d0b00c040f01194071b4540036443d100070044c002083c0252000b081d1000d49070640e0b12541050300d140c40d031707120003440a409003090190412010450103014008149144105103d038010a0300d000d1284800315249842840c00c1d0001d0007040d40040c802040040304910100c4020030140c4031828401d40202282d0001071034400110a8080741c69281a039a10b518000219038005810389a0302d28441050103d400400090301100ea40c110307005e2507170210107450310103001c0303d0805480d241e201c44801c2c4522020f0f104020b15050400446c0b515001d000d40d4180031140950514000d55009404400c1078010075803150344810842041100f0106981e002c0c40e0001d24040c81800c2c40860031205220801c104a424400c42400340380840b9105078a50460303202400400c01c111700301c0000c540902035030080c4040d603601040300049030b586 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 254227940 1250 254226690 254226701
    0x60c0b1b0307050c070506030105060a030515041d010b0301091e031e0509030609070308040b0d0b0a060305011806050312090102011d06071101140408030a09020a030302010f1a0a060f1101 82
    0x4041d00d071141c0d9079403420700c03845c545007082d4811b52152000700300500083d01e803403082d115080e1031170a02041c84c1e151608000d4511000c03000d200d4000d482e00b82d0105494031000c40701c5d03407001c2001008100740c04000040c9401c2e10300c075140142c9607410302c2d1101e010030345a059540030300d1802071030144d402110101d41400703206030f400748540019030042904442c5103000e00c030351504402100b00505034030703186a40c0c0001704d00851081c0081000049080c510410190f081480b40e40b400410f4202c0d00389d1030740d4010380184000c0c0244030f070800100611003144500c0c1e10400d41654401002040465100c0d0744100c056800002c10314115505d50804502c401c00e000e00801000f0029405449503203030805004042d00b130711059404150f810540c240640c00000c0d109141c200703810034611680c99903207a1524026054002000f90130501035400002807650650222444030700395102071103d41c0c020446610039100d0301648941c080c080b000204000c5002d0303801e500549c20340d800c0080c80500402c0c00503003102c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 254229190 1250 254227940 254227951
    0xf02060c0d030e1510060e060c010e0303041203090507140102030903010501080c0111032106010c12090f08010207020105030109051503061602012a0c0602130311150301060c0b1b03 79
    0xa0f103810650300c402005000c410703540600c0410085440c03401c00c4c0031843c101d4440c8030709824006504040821611500100c3d00008003140080c4800101001415134a0b801200d00352140100c030401160614400c0c083c3c03a41072500200144000c5041c0f40c07038410761401d20700865066200030005010107131001c0c01407900074200c9201078031605a410002501d01000225008000c0d00208404da2500e01a42c00c090441c01a00e000101c49548030070041e0f59511140002411145180c2c105c0b0300a9a030205103002600e030035441c641c0c2040d0340c076040b203420707801051402030100c0c40500050040d80d030035602c410703403010003030b80300528402c0c40c0c2d0003081c24440140c942d1011004000e15808907a902402000d850a1151070b400c0110140d03103c1c01c110145088841c00c1c10020310460000501c0b4850301903442d002103440e101940b42d5a039150200f0314001e0702030080e0044916203061000070407c0c406580c101c0c1c409440c3d81d20300b1300180c0d440303103514080180342c8405021031482d0700c01c44c102d400300554400d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 254230440 1250 254229190 254229197
    0x230a021329030c01110a03030e0304090207050327010e1c02060403050d031404020901120303061e0f08031e07050a06090807030e041b030c110105040c032109030f02060c0d 75
    0x40c0c4101c000e050601400d070508034140040840040d07001c480005140b0003090b01450000ba040007201d002c03505501c110740c4a06546800400d1401c24000007000401000d00380c04aa0001c442180314040503040030070200c5070215020000b2140241004841e2000c0307100b0620482440b000c4e25030000380290403d1304103482a03400703c414181559014170400c40503a003012410750a034541640090b202100500800700401644400041018000c7d0001e5000d048500507400c01499a40c64420403402280714662601500080c0020003400100440da41c0317000e1440300c41001d140344030700c1243c035500c110411a980c1c81440d110602003a454444c600d1040c2c405c00300a03540c1d030503504004010b1001034200c588107510b005100c4603c561901001e82c103034102420081b4001000d24010745201521449d140d4003540ac1400300400c009804244500b680d208030020380100e14650384090340c000d19580904003144907801e003071010500d40000350b0051840100446d1410034549909410240c0360003901020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 254231690 1250 254230440 254230511
    0x62a0c151c0f0b01020d080402150c010209120f2a01050702030f070303050d0b03030c1b120106240504120318031e05010b010c02060d0209032404230a0213 68
    0x300d607414407006101100e2450000d42c9230815030001608103036840d0801c04e0030200061120300c0c1c4682034055030403a11009040003003003504070036826160180b80e0659511401500f000ca102410940c450807042c43c0749050607442d103040840159002c1d4028074041c0d80c1881b400503041c555890801c070400c05148682d441a0712460324a000400b5180c0742c0d96064030982041c00140e01e10000000d04820074002c4a006d0552682e03042c0100301c94a80b9881400300a50805502103144404800e1030558150030302c00c41c1810042010003200d040c0124040d5081d41214501100c000c00d01c100c540c0b440c014601038444002982e03d0b61114207110110b0418500501c1100281e02406403e11500044410138200491007514690024410b4450f9003881c00202c1d502148044090b00c04201c6021403051401e0003011080c13039950031280180044030700312000400b502883c0f81c2119880501e03440e207030000f40103080850240c1d0070444068800d00948000320b503114a92202c070048421042400b0140c10300c40070b81d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 254232940 1250 254231690 254231711
    0x3050309090a0c080a1121090c03061012020604170d020d0305100605071b0602030d0b01031b0c0302120a0c0209090607051603030902062a0c151c0f 65
    0x141d115000b010081040d24146040e04501d40091400d0f901c0005541c000030580b10300034030f000241c0200b02c5407110b01900d0800707502c046005820071500070351425080760341418039481095900c0c5411502e03103021306071065041200890108000c008075100a0550f41031503168035a450220701035221480499001c81013180c5803a03010f0280300546400c0e840d003030180b840c00130f550440a000310b00c41c2c8020400005031280c24050f0780514201c1e00220070342d0102d0748903a606c5000b0341d240c03c64011501c0c1c15181200040f125802441014186941540e4000341d00810a806130780000e00c41c1c03010344c1503025120307000c95441184001440019026100c14142540740c2c01440340040008140707804950240080c060036941141c00d0f25200b4240c4040e00c1200c00140c602140a820035107002500848045011042d2150a012a05425404000341540120b03500445c80e40d91202542803a04201d00009503451240c98400406000647c0c00001400d00350f80d48080c0116540700422544032940ca021154 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 254234190 1250 254232940 254232949
    0x160501080a05070516050319081b070b180a0209010608100e06030703081309020f03041505060d0210030e070e04111906030c0c08070b160201140f0c070b0103050309 72
    0x707800a90700e070000c11103407501c540040d206100d604500c20f000e001c0c83da44101001420001c40c2d0719503400d00f82002d03a180000c007024008510a5801d201c070145420000105002c5c140c0644110b00e421998000554075420740341552801e0540919089004051782407025850303200e20300d4002c19483c1c0e04d0425520385282110409507a640001e640e07081701509114941c0d41c001420010b403030704001c03202e0799880d01090201c4642456070015240500100d0900021200500594401c40c040e0ce209589078413128102401c91318101d17603d55200c0f058a25040250070300c519140d02002013410001203d205440350540713885055444420300000d41c1c001c10003009521421003200c000b095a44407030034454121220742d448000c0c02100304140c1e030344410504d854400c440c9002550f4000f410966100c4440c14140100202140d101c9404182d1101441e5110300c14403440810500e0b040700d02940e525031400c402c00c80c1401800700400c80800344501350101c2c1c0c81011b000d000f180304038000c41d9201e08510500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 254235440 1250 254234190 254234207
    0x3010b060406020c0f0402130803040f350c040204080f0f0d05040b07030e0a0611010e16050d08040801050c1b070605030a020d0609020c070602010b06040506120711160501 75
    0x1140103420500c0108401c580006201c08140c00454584440d0407880b00414024041d0356010fa040703000006c070001d030100001c0010030a41d110044142c81a0780c80301256049400c0708402800c24a8402d00041100d50320070355511034014220040d94803941d58000020203030b811030340025501d50440032940b081802c0401400040300321030405010200d00c00d04025015024510820088403030005044040612400c2040000c034001403c2c440c1403511550300510f40c140032504400f00d0740c6014010703128028002402603d80081c1c404542d0718a01709410300124454141c0c1c2151503050074003002c20644000e0081c24810944519403d8640d4140380100d100c111086005060680020900344441c1e6880412694003207020fa0300513a60707c0c07e01d00035800500c480e510407c003035071001c2402e140244010800a00b2941107038001c2c0003030306c0210100040361240b840340c01c1d0f0100d02007258a00020380b01c0380540c3c0c000000c0c1020720107940a40b82c0749042c144206250910046242014071496801c41e103103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 254236690 1250 254235440 254235461
    0x50a080a06060e010819051512070506041217030a090c06030b0105180f1807030c050412060c140d0207060c0512010e0c040b040905010503011d030313020406230301 72
    0x280401441e02c0000341001c14840d90850400c0042c00000c0c004401c0c903000f5003414114002c04201600d04403200e8100200a00341d001d215869038180780c42c8044001501106554004220524040c80c041c1203440b00443d0841c1154036480d1062110310310034420026510410a2038000b00c3c261a0030700e01020504c115402800915140036007903001668441d003a44c6e0603072800d0080007481d108520000704601320801c3d9850b440740d141820820380d442e100f03035407034020340c84c03074400b070100c00c20025040e079043c00f5a0140e210903410050010300410442d40000c2c490106a00701071410f0003011001040650000c00071840785500020713103504111041c412005004d90328170b02a41440303280c030000c4c140d0310f1041c0309440c82c0080050100d00c1c1420b094007264000d045140c1000c1d0342d40e9442013008054030013441494400e510f00130000c0e000c1200e135141070300c14002c0d44002e589507a48204902801c034031400800e0303030003030344d1200082a480410070701d1b125002c2444140310300c5600d04408250944403001d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 254237940 1250 254236690 254236711
    0x703060b04030b07031d010203070e0f0102010608031e04081006030b0f0f1306020d0c1112070209071d0402040e090706030e070b030406020706090b0106020c010f080610031b050a08 79
    0x41040030607051020f09410003001c1ca000b0500c841443c0c4110078003851403120040c41d500c00024859225046420b5041c03000050720b58448004000c0016403ca4041d44a40121a002044505541c203480740740c581c0902a900c1440d814280c540050b03503c4c10b507040014180701955400309006210610001e29072003208400c0102841c5058007400806070005003164035050482a492010001980c055a4645044030b50421444401c410010200382008040500d54018003401c104400a00402c548000d50040d005041c643c48403942160219051180d161180724030070070024003a0340300d00050005000d00c40d0049500e04001c8a05803d00620364480d40a051030172880c4e00c4000c2c400310700c9108507213540e14019201d58541c1404e1010b840340c2140206242d14004e4110300300301010403010f050b2603d9a00310b4803811804001036031001680132501c2c0c0400c4100f000a045442c204140e21401c1d4200d15000c41c0d004c001e4401440032030b0b004259800821004070740c11301c00c507074400a5240e004440c1d41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 254239190 1250 254237940 254237947
    0x70506011e2301030b01090312120b0f030c1e0a03031e0e0a09020c010f0609050405070806060a0909150c0306060f140403110109030b0103080405013509010915050703060b 75
    0x103440c054201e07142c2907241455111001c04d1003982c092114100110b40040c2c1c4609024995a401003c070380c0501150100c0ae89040b90681503824084400d40e170240300903004280b40c800703040030410261803200c0040c051700c0d080000800141c03684100040210b2098442c00c4244440031301200070004161032070010010185103610341942c400100c241200e06900c40140d480e807d844503580509032807508000c04134240100000c82d040c0d580d03c054440d60094041d6010151540503207510b4000036078006034441681743d000d210a00c0554480c034500741c0701d6003081b6585801201c2d0a81503805800040020039a02e500410070b440d003003480e00e6140181403230441b00c442480d0403105194003841c04050b10140da0b000001060340d00440c1402d010b5034001414615a40c3e403441d2585071a4828010a800503000741c10500120b00c50541014040a43c0070b01c0300d28040c5106808090440d00070303d20f414540d210051000810025202c00070450808a000714080c41e0560001d000d80c1e449610104d8111001c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 254240440 1250 254239190 254239229
    0x803070905090921040b070c061b0f11010509040e01051014061b0102040f180b060301030f11040f0c08090c01110d05030403050405040203070f08010801020a020d1202070506011e 78
    0x2142104c0e20307180da4490405206004001e050070b03400b0b20381055034000d0000400c00140b090035021002228425662800c9070a040c0c501039000c440c903040018a2604030328103502c001180c00c0d80300f00f4651300c1890102d0400100100140949401003400021650b40b80188075189070800ba03003102070940c1428566a221f603413004038809214680d08090141c001c480e4008007079400f90110f60042c059020380e04c16a544402144400000c1f000c0700031461464004d0284241c1002010b590480313800200103400382c02903440c1e80703107000b002022480e4026542c0c2c0e81d1000e070070f003544181101802e0590302e0009902d8103030086850100070303003881c0f814080c81d21030507040340300000742c0c0300c44507115854200c2c0c90740c0303c524041c6e6a900030b54001e5980680040100701035240d00601080041403a5a1100590303661079038910308038420082c9070001a004840b5400201e80506003a8272200605840107103840d143d0303240c050401c00300780c000101404000000a820101c40806900901b400840e500c1e0340603501c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 254241690 1250 254240440 254240443
    0xc06061412010b0d0311071203120b1012020c07090509070f080a0803061504080102030106050309060a0b0901060f0c140f120406080f061206090303100602060105180c070f08030709050909 82
    0x104d00404000e0350200e41580300c401031050600824401550381c501082c40d14002c0d00b900a02d10703404076141e248c403000b8a0f05213460545001c03500c400380c81da42524440ba400c08806035004000c1d1504911407204005288141c9116143c840c6010001074103ca07810101105a204c030035074010f12065000030901c40216042d502202e411000448011030410307407107490001540520307440104294030200c000211960440000c6110740c040e003041c0c8003581d4614075440e00301c8542c5603001e03400104241c018441180505050480c1001d02d0901e500320340702d503640d207000c0d4100100141450350400314107005c0c5c400c81003006421030303141c0448980c2000c0c1499402800504d0082505007130502480109000d510703502c0d20091020340203c03e0716014500219900d82d0ba500640b074107034406c00d90030741c000782c058030110312641030f0381c0024510562096078182614009102402c130b104184020480b02000407144174000d00040d00c2501c405440b49081100074150305050340c0b01c24040c1c0351030010090500310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 254242940 1250 254241690 254241709
    0x10021f0203010f090506011b0317090d14090406180207030306052b061803020a030206071805040506011103041e0f0e040204050a0b1908011d1209010c06061412010b 72
    0xa6003000403030340c0d18400103c81010008c901d40045a80320b00071a000c0c9a40200d400c101c00031120114806510781013809541c0320743c0070701443d00245071000c22070000d1410600802c15480d0081c00401c01c183c079501c0000300241c1c80e801c00300c062540011420201a010300441380100070442d14804824005101d030504810a28060b0610a580080c0c800801601c0d40c4121045008544c1510b405a4580f6000e9690480220140c0140c8036401c00241807511032009080685014410000801d1410b01030102401c4043c00b040d061004021500101000801c041c00060095540d1701216500000d80e0a0035030074580c22040092501810070f002d0807110000746a0000e50580340000d240c1c0e00d01c2090402068480d0442d03510541d049418940c0b072200903204000e840546008220101844a81850700140703c00c040315680c0083c0403040e0851502c0d4080d020585060410001102d0f003039070f40da0202c520070f4004410300c00c107400c4600441e040003040c00f420320203400001c010785000f410001c3e00526 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 254244190 1250 254242940 254242949
    0x90907050307090f0501150203300c07060e0c01020d0309080403050f070e010501020714061606050a020a170f040f0302030403080415120501081b181828140c10021f0203010f 76
    0x48021881040b2b410b02840d641d03840400c0007900c071040e08105202d11950343c0680004d9502905000d0280000040481c0790800000160020108094894000ea0140c0420141920302c04010301c400004142c091105143e0f900880003d4100d007801d05100c1000b00d0710681240d07046600110051002004118400c3c02c0340340300b21791543e01c1e4148002c13804800c818122006003014245014004000c900e42c02130440c10504ea2141c41120406080c504100e0104582143c0381c0f00203c030126020561100400684600038415285010b49980301c5c035615a00680c410404503401e11610380e051a40706000084e103205003001800325514040d515951607500e994043c60628460101c5110340da2020203e805006010740b254445141c11400c221203c0c40035043c0b42c0e2280501e2010340302c1c00d40881c00b501003024001d0b403c03841c1d044003500e5001d40610807141c074801d2885502224201031b036464000c403920b200c3c1e50f07008121880d01112804a4a04d961000801c502e006200510170364a05100076010344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 254245440 1250 254244190 254244217
    0xb030403020d050f1c0f11130303140f030403090501140c07060509060c06010308040303081e1504180f0219060804060c030b090c120f0103030e090907050307090f0501150203 76
    0xc00b0303800401c940c28400d031030030f55210350401e5503010740d1040c454111080f0b615490a00b00329005007000c2c10003113445402c48c01a4092603d0b141840000e0045014900c03800302c440d003a60919001c00c201d4003840c1e20680b41034000c600e540c04c4c200300c20f40c1d00c0340440001c0c03178201c0e1065003410350f1080b000d555141e8a00648050000c007145645190303c55009441d680d1800804036512941e69045c80182c5030b04c1408141d0029040000203162002ca0040c020881018901d0b0a689035460b01800d00310f6903408600c40d42c0c402c1e1666908852001701001d0350041c070b401241c5480c0c120794284100400c074105809880c4002c519440708010039034004141a43c89500084049a00c0022560407801007483c5080154405100c0091003003004041000c3e21886020780b042d40c45d1031311005012000020240300007000a003c00d229a695800d00c0071545070400980402c582c24035803a20002814001d1607080110410755486400c0c0c0641e00303034000c2c1030040c0f0803801d2000c54004a510002c1d124401d00c1400380c3d80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 254246690 1250 254245440 254245447
    0x40806151c0201121a040f14010e0a18050f15070c0807020303040812031b07020d0f020f1002010b09060a03050a0807080d020d02070302010e0105062b02060a0c0506010b030403020d05 80
    0x356409095a030b00c4841540d0350410174140210b00d044030503641c1400c0503000350300c1d1040c14404240240b03c0c22001c000f03810200d1149a1070001d0015480030000c0240107102c2c0c840304000f10f0607510540320740c010f0344280c001d001ca5104c00440203203810303241310301c59404c0d02c00a0244440990400040e441c01070f00110701907a501940d001003440d5110385ea01510481c4103060483c00500c140101a40c09501614500130308140b02282c04a4035004154029500401c400041c1c400514079408800d4844c0c400740c12558417260000009512a45c05020140136035101c00c9420a14507041a1769070740450700f2130319008124103688450380d8600c2c5100000703002040025444090040c54001c1e40d14200e821081503594000b5240c44070041e4000d507004402560a04800c0d0a070b4000600034188129805460b003000813030000c1d0300340c400840c1c524001e002c0c10100d46003140583c4030003000b0000001c003030716011144085803500c10715003a0b050b03025814101c01401480300082d0701040b14002484180b40081d207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 254247940 1250 254246690 254246693
    0x60d0b1c0c0b070f021008070906020105190903110f010203100f080d260403020a060507020303070c020f04090501050a0b09010608040f081b10060305060a0b060403120302120c040806151c 82
    0x31404d02841010754401c640068451496030304c03a20b40c0d441424030f50b0340c4c88a400ea903102d00b0b0b0300340c1e42c054400030300c6080c4180c1d80d001c04454039440046458028507001800d00019162181850784403808890f0a940000412512000c3d40d52010001c20a4034044043c943c03034a80706c551070320700420f081c000300281c0311004503152410b580610040c103441003038502e050620b07260103595001e25400c01c03601c250800340020354260000c07042d640f048580c0d844d0041a45419401c00c0641d41480329002d03881507451000c42c0201e0000d11445109148a400025010282c2c0c02001280103059100408004c1e90b8410040000c4807818540000ba41c040c0a054496003507030204418804200c0686401d407080c804036801002e069044981203034004e034260785803a00c07080390307200665004107101500070004005c1000000e4141268143e109660f180040c10f01c440442c010b03610309410b035921940550301117414030840c0390500069800a201000640000350304001007010400c502c18842c540e8448041da450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 254249190 1250 254247940 254247953
    0x73503010312090b0a0302030708180a021207080f03030105030f0106051302091807050a080603011a1915020f0607081308030604110c03040801060b040501200c060d0b1c0c0b07 77
    0x640160702c113180d111001450014004c3d0401c80c0c82100084807d00410540d0035008115490b10301c5841c00703000200ca603a02404040410250030034854031500b10000349281041c020301c4c81e60500d180103550350354909000c2520b81810584900c0250749041c004101a071b4415100a66842c0016800340e100c49084001984c44034814000d9a207500a42003000b00565110000341004000d94984020944802c1d092500301d607128002e504640504c040e815442d85083c0b41c0c2a000c0e42c803421500c06500782c44101c22951480300e001d400c0c0c05a071126401d44469681400415405486131902082602e0072034030354a0310b400c40d2100034000020000c08a401502c0d1500400512014103010a9039012044400741e901d511502c1580b00c80c2d440c3c0740b004100614900212411130784165a041049501d12454603100c100d0383c81108045e100300e40204905443e42c0d800f8003140107841c2e400140564114090280500300c00540700314141491a142c0000303020781d100c120a5502d903160107030300c500c4545080f4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 254250440 1250 254249190 254249207
    0x10f15020c060f030415140a090f0c06090e01090b01020601090207020f0d0b060310050f070e1f050418050601021c05120408040303030e0a03021c050f073503010312 72
    0x82c1d000140010908003181030100203502451054040021404050b5168400c90712003c0790400c45140354004030710f07071699a800c041040b500a0001840060300d81e580e0466000e22030348035030042885034408221801000b4082401408000b40a0240c6903008000030b4450505015100d07116a0218401040d515040c2c045105000d001d42819089a560706000c5000c14007140c106201e4411000d00746003804441c012540191a5000d503c100368951840c1030f00c0d42011000c016403c201504800012a0941540c1401c060000c0d2121f5a8882c24480031501001c4c0310780641940e90b0402c0c05000d00c0380d82c0007441c50b0b034014902c2200c0e0781ca81c050603001c49103481402000c0c042030040c1e0050005218040c8006c10443e4420b031410800c1450b5012015111360720300c01c020b8090b17000040b404d8070901041c2200440c052040c03405519000c801402c0a10b6500406001e45540c51070200348840008441031b88202e180080400c400310303038580d00b2100320714801400b0083c8555580030483c0f03c00350040380b09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 254251690 1250 254250440 254250463
    0x40f06051b030d0608010c0e2101140406020c0706090e04150204050607060f0c020604030909020a0c020414090d2c0a080a080a080c0405100e0f060a030c0215010f1502 73
    0x1078981d2001039050110282403d80145c4005500e028140c51300d550041d1070150000d84050b158407440a44209100344926a15241d1040f55480b121843d007600c2404056a00c0713640f01c1c600060f00e416041c5241031a1122580110301485a0810203024406414984d6940103074881c0300680041c1c8280040c0c0003030f000c0c980c411030f007081d0081516001c0000c40d41001e2011640c49404001d5004180c400304d03a07461081c0c80150103d10032003000e1040010300d4005040d4001c460030704100190fa9070340420101c501c41c3d58940000325110080c0800c1e2542400201c40c6c0c2c0b8014a002c003000c040d10000042001c0b60300385540700e5046c828141e800b1684414104400400c0020155011440c1d00c0c01c0103030700f0790f10565081d00010004d10008035491460b04c1913809551024101035107501841070300b5a8900d0043c181140d0011100090300d80e0b0355500b00040101605503036003c40c81805603a0007034500b010241c280c20b0b1014800c401845000d4a882e51003003107078151034400c100fa059140c4181d0400035030701d03c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 254252940 1250 254251690 254251693
    0x140a050d1103011503052a010c110a0308070605100e0703180203071d09070f0512030d050405031b01021801080612030c0619090506040206180d06090215040f06051b 72
    0x3010740302144196042c074100c174010030944642c890264811500341541f0754485c5c1102c072102094080652150301c075003105038450f0021400441e08080022a20801d41d4800c90320000000740071004c11215020b0584c0003203a49061024103402c00d002d582c00300c0802441b410030940e540510820854400c40070429064000d410740b20040e80707800824098040d0000b80003510f2811b0404618000e01c0044c021044604c43e040303140c011030410080000300071b00f03400f000f1202d110600070840580f21b02e02ca402c1c0160711410003195640e06502030f1108903481c4081d03541d056403052001d08413511031b02c00741140c0c8181c2460503d11695442c00004d100780078000b40501540300200f0811600b0400085d518024840035001001c281400c0841e5000d46151000017000ba400000c04100141408009440c0a00105074040315a070040008580c3c20160620240d8105403102205025800e00f100c8034040582d6005070b243ca86410442d10740d04000c160322401003000b50014680e021800c00d0719010219a04910 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 254254190 1250 254252940 254252951
    0x14101404110301081b121510091505040506060702090105040507110318010924030e0c030d0c15020309120a12061508010e10180209060c07030c140a050d110301 70
    0x107608594480d2001704203c16120b030a11306031620b19142c25089002c0080c40000d208400c031601102e109004c4c041e117a01c61458441c44003080284540c014141800e02c0640031940b030900c0d1000b00300580b50301070419070040030304010141c09a242c490072681554003c2d10040b40d1600ca1100840f0040141c20243c0740381d0002146080500f05240c4c550303644103500340d03604218603843e2039a6200b210b5014014040f0a10310074841c84880f0701940001070b2800f50501543e09030840c140129050215003070850000418280030f990820141020801d26548180411030840c82c000c00388030790b1152142e82c14001e0520100f85481d40500c510340328044110070f82c005202aa0380d034014104012120b4890308045250750780007180c114000070942d4411070b085015100030b28940441e0214103c00752400b80f41701078080200440310b40b40c02000f04400e0302948024080c4501c0c42c2045d6090200d2904500c800082050700704d00a983c510034150140d0300300302d41c80061030788540352030302d607021003080103036095403c1c007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 254255440 1250 254254190 254254199
    0x30c020c0f0d121106010f06081602011b021018030c02011206050a030f03030c031103060f06090303070c080d0507050601090c18030305090f0f1005070302070e09010603020414101404110301 83
    0x801c0c01e0403080c00801140e010342d882e907e84c034085803080e000e03100c00100c50000040c498001e170140b510b5070440d580000212488440c00961031038400540603800350303001d00143c51810a00703100b105039510380015186680401a600180f11012450000e8100100e40405090458a652090004020003026004459a82c0c90401803118280f50700703801091814014420071802790190181110054a189246545500402071407818030a41942c1100c42800696140e0b04d0420041c28982d018040320034607245000e40003803034049520080300c2042414844080001c10004038203040d90042e2a0104000b14628000c46124440c07079943c081c06000b452000040c0b60700b2200030102020140c030a06104000b940500c4289030440c021150420307000d81c488a48248180050104144684159040360390303034100302c01e080b8806581245003039540d543c08108510345071080c075508a441314950f0309640343c0230180c080c0c00d2000384200c140608001d030008040360303a036900040240d501c0843c20b5803030703503100e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 254256690 1250 254255440 254255447
    0x10050c010c0c02010f020604240906020c0303100515030406110c0d030f200d0902060c06040605010e1b1c02130b1e07020303030a022206021c030c020c0f0d12 69
    0x620b8059001c20041020f03045180d20104403940f0031904001002003008046010100c007400b84411185140d0342d9555142c0050601e00040c00a1040c0034000c5450380bc108100d01d0412040e03a02c528410020180761174820a0750906a9600542000002900701e003120480c00d40b510800c84208a503010301414406c80380c2e00f581c40039000040710441040161040c40c1c3d46080116181d00c2c03190400c00030f10244540031000d030044040c00e88043c0c0460704011244034481e01c1e140c0240c5003252200c1d101c200601641080d010b030568000c1e8407941c00e1039980d100101c010304605c1110702010804004a0a8400a40d225012118420110030310750215590b41c06445a05410011224048009080946822042c0c08003580c00e4190024003451070345e241d00e060351009600081124008803001c803604075030744078080c0c1200300038100c2d40c001d40b0b002c90300920b40c4e0000c0c0c0302c80d001032400d00d86441640c2090a9000135002200d0105a6051448056000000b9842c10b007007031000744aa102c2040c2401c0b0250b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 254257940 1250 254256690 254256707
    0xc03062e031b140f04020f040302180a050919031d0907020c01020717030406050d0e010507122a0c030c080406031d01020a080f1906091d12040510050c010c 68
    0x908862007003800ea16941500e40103d110559564803600341c0c2d0140401d80703400e5000f00454960a50118600342c0e5aa010032241200a0803607944681c84408010b17982e003690103a2540141242e000e072048070301d08203100304c00d0040000c0290070001101d4401022485030310016100c100300038600c608174038203114000e5481410145060042c06460700c00107615206122400c3c2e880202d00c00741d82003a09000b1b08680729000b01942c1c602d40b9440e050200d880000030b10403a4020704940d42c4080001da11509075600761202180c0e1440d40c09505030901c41c0c000f10480710703013440100c0c500d030010f000300c483d09045034601d2580f10003403c8003000090006000360158030070f0f0440301900e00070390a00040c202c0400d08038042d810941c8042000c203c0060750240c9a182c41d1640f04540b0800b0300d0001828040110881e481d9401c452110741ea52b02d41d1054014540a4802201121900030b00f036422610145000d2405644502409048225081030034140a00180c54203818902d001b0442c2c1000401d00910b80346 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 254259190 1250 254257940 254257973
    0xa05010b0f01080603031207090f0806060411070506010918051005070215010303140901031416110c0312070201170f0105010f1e270e0105120c03062e03 67
    0x48041012032003540200c0c1e500b0f1140c613000b8080d504150945000103101c41000380050304100385900301181400c1c83c80007540142400e000200000c0c504807007403004803007007034400550040092140600081001510605562500d107000c5250a00794642114001030254000d20a0140e504c002e0000301956000600c10303040c540c200c403101000906540b421500a000260000703081000105d12040c54100418080106240018040b03440702803407481100300365400ca0418200c41110381d00c441d80701d40d81101e0f5030b9242024261102056001a58802c10454420013a500100702a4203580c0500c5003480a00c0800034003607014503040501c810000024010300b4049581208400d048612074000144049580446c0c1940715042120559103508406c0090b40c00d0310016950b0f138000a121aa0540104402000c020080d4186001c200c408042e59201e14566400610000394542c1c001850076003000007880d00084111803404142d20711003040996000101c2845e50000030002d90401c810160f1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 254260440 1250 254259190 254259199
    0x4030b040507060302160308151e1504061d04020903010c0210110a0f110f0d0e0a0e0c1b160e04060b0108040803180309190f0602011503120201020c0a05010b 69
    0x280c0c95140130ba04030700800d8030312407100b010202104002806041d0641d0444801d6a140b04c40f240b60100184000003910303000190301e171021440c0c00160038900c034000307003045442c40ba443c106809d0500040c441115116000b0351460218070140c019111359044608848000d8001e0007010010302020b50b50350455042902c040780340086400303104504a06841c040b01080e915030016420b00c120481e00d00040d040b06211034000d140f080161120100500c55901815407039040c200320380300081145210a561004403042c859030100912403152a0807180100007034041206420042d0121070300c4d21100300c2c0202e00d80e21011002240340c3c203442a14600c5248a01400d000144d18540115005a0142c400524400c014408074280038643d100d41514040004112420310102600080c03200c01220540180d42e070000209001c5c55944140410107002d4078002409000141c41c8480c1c1d0780711580c8030143c00e1301c1103170000340d566034400c1d0121101c100c00c070802c4441c5000541130607402000304c640ca0703d118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 254261690 1250 254260440 254260453
    0x50303070b091509060f15040e2d0607050705071503060e180c0103050a022703010501062102090d020301150e0907061e030608100522020f0f0a0b04030b0405 69
    0x8a003d40c02d00e180c030440140024201d29102c13440c00318400d40b0302404200000c8101d41500103d0303202c40c410704102c0c9210000070465404281468103486800f40d202c034a444000507070714842020b0018125030403060510305269200c25609000d0f00b00700c07003034004c10150098080380e001056410340100c01603440c4408229441e80342ca04200c12490700da4031518400d40c00c020240d4140d90302a52205920844d11540540380001c0030f250072406842c5c07001c1c10a00c1c091706000900b01d5080c24442e1031b0141107203061405425143c2a540b00c0d01540c04c0b0261090340c0e400151005046d19003900341c400d103c1d070140090100500710001d280ba022054003800280380c0c0030344002841d60100043c01d80459004d5114401e800c02c01c0e00301184140020400f581c2071503204d6a000039000e6003005403029801a69031f00083e28100810007045080c000040a40e080c3e10408405002d6901d1400351f00000c1812142c03000a040e030030010442000d01a4050f0107040303030104000081c894802d0038140305505c00c01c2036070203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 254262940 1250 254261690 254261713
    0xe040302060108010b060a0c030e0a0b0703030212060108070212090103020d18300813170a18030b0106080a1b050703080c0406080105060714120406030c020a120f09050303070b09 78
    0x881f4004d20420400140c4003d2800300887e00440091345100742c0900b02500181d01c3d640040c00b507a2185000311b00283e40000d20188110170000c0a81c1c01000034070700403a150030200740007955415010140900c1000014855034280c1c007070390440d0b031b001c240710109020a110b207841c5002406d0404006455001c055081c1c1c0051035030050003405194411300101c1800c5200340402c8840d00750040905a00c2c80c40c4c1240b80c4046400c00200c680003849024000c0e59502d016600106039060354514400140c2100300e05200050b031040050341501c0f514600401b81d45e4505101901805022202c034000b01000f00800350100c1e442001003038841e000c3d40f104041c584032800b5031410761103584648800034003800c006000ba40317001002130440300c0c003c281090240d6007010b15181010300040051038000300c0010300700a80b036014001c0c2884020b1754009400100d000391107115540401640c0041003021900c00080818014403d92002c0c0501138201c1e40c0b00c85140c41d05440740282034440300c0052080885070322 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 254264190 1250 254262940 254262949
    0x3071509050c1002280c0b03010f09020922291207050d11130612020a05030a0209040305090102071701061a1809130b131e0515060a0e040302060108010b 67
    0x5000c107043e40e0052188518007030f10107003400b10203003103050485013040191021564202e0114090304803600138503565454400350764503105c1c1551080040d5070041c03100c0c0c0c0440c0e489074800c062234400c0d4200c464408092911100081c0142000e0865510545200801005811300503230703603282099880240b644404e1002e542c1d10007040c420590f1040600c0c2c00140024005130b0b900a0a100c0a410320044002590740c520950b50301e82c11041c9502003074520351080d40342003102a0001d14080d006042201101d80204540080081000e011b1000008240a07640d03c20840000204032460303041007544d051144690282484d0b00c1910220401110700c00380c090000f1045071030386000060403030100300e10303141402001c1000a00100c00215404e0510011a51148440e071145407000c0d82a04003481c10b261813111040c928007440d0b00051000507150020360005260f0351401f014180000c400c0d501c44000440010f11350f007003000008002404d100805800065075416103030080000c0c00203590701418031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 254265440 1250 254264190 254264209
    0x1101151806050a051002120414180402060909040809030a08030a0f0c1b110406080d1206050a18020408010c021006080a0c060e01020c0316081b2103071509050c 70
    0x703503110fa41850100854603190200440c40c55490050302c5000e900d6422404440d005988582c02444203110441918a04003140c20b206000840000b035003810250046121401518145402891110003050038403140d4015a40702510080c100c50088006d4a820202d941003940d014211906000c01721610381c40500503800c51100c036949410401c08280140c60300c0039107103401a260038990342c03918040c90b12203002c0c0d94064440d610040807686002c640013403441030300c43d551b0f40c6003900e081003d00003030740d842a0f8001111600403201610b9030446100300c00030b10590340071848540c070702204558059000305404020300800c0320304005503a5501c003120340703551003000000c14404580800b404000c0c081e03c01016009818030444140822071000701e4a0074807181002a84411110401c0050550801015800c588122a0060011181000710f00800300090304e441c20400e40c10a40200d45004109030781d41545c000d072031510b0415070001c40c1401422190421b603618021a4101040303400c02c601c80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 254266690 1250 254265440 254265449
    0x1003060e0c091c06201902010c09090c4b0806040c180608160903080403081c06030b010f0803090306161809050a231302011101151806 59
    0x3980300210350a2030b02c40c1c152804401c0301c00550307400c80e1780e10f04100110b109590400180700e5582c1d0300d03c00c5d400780310007840c1301661030110387c1012000385905502007000310440c2e90000c2c1c00f0030038544190041c1c4052041c02620b151503600480390521400c61107034103a21880c4018010444100400c0503402a503200c00b01ca0008111000007041c1e0500f000d0f80141030701c005c145450844140e189030883e06000d140e600c200c0006002000780242d4401484503d03c0c0c1e41c90360b0400707222442c82e560310b030b07812805a03100251003210701255501d001f0340014030403a8104c0c1410300800940d80c03070f4580348640200c203008090200c0c40c2c502c80815480000001c803145060020000e10b001d0b41c821006608915401208008002a600c1c003140e5010610b00c80030040e0102400104081c50008108821100b4003a242883c0752102d82e02da41c20a040345a0143d08845001035120060b81c00d40010786001e068000343c10f0896280441044080040c0d4400c4800d580c250203042d1800868800ca010503298035004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 254267940 1250 254266690 254266699
    0x30605090f01030807080712030504061d06040212010e060c0a02010606030b010c0b07140706020c06060109030308071202190804020906060f0a0e0409060204080706140301030c12030c021003060e0c09 87
    0x43c00801d101801501d01c0901c640d0103145410025941d48074142150000b00012a40b640180010000c3c9801098811902c1c0100d42d85804603814110795500303000b40c00130340036080182d51a05400404e400c4801d0000125007241d91605003021440c10941c00301c1c1000005519022011625910038007030120b280c88140d44040d05201c507600d986c0302c1607001803e601d0600030454000c0e161409214060039000340074040040e214a0781e04907003420182c0c01040030f81042420340c41840081c1e08901c1603600aa600d2070581080740281c000c04009114020b6906000c4030120110700d883e66010b0702c1c0a10841c07007582c0702a656250041807007040d00515000c290801c005101d185c0105115099008000c00c0040003c01c404889480742e000f203a00580042c095600b00d89024800035422044c0c0328088019444550700c1c0d03603d9a1245240e0b59028051207811038000d00440c02070511981c84601c40a03002040003c3c220600d0001030000c11044c801c1ca81800417520019031241002800e0f034560807000307407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 254269190 1250 254267940 254267971
    0x801050c0d0b011701091508060c0f210c0a0f090303020d0c0f0b0c0a080106080c1603020309031516050403020a03020420070c03060b060c0c090915130303060509 71
    0x84544094000c1c1410b090400c82d103450994448000381030401c1c000c00105500140121905903103404c101155040315812340c1c00310080c010011402c138100d8054141482c43c0d41d80b106e8200d00b51802d0103e0b56078030052900e00003000d002501c47c0303010003003c8404194440f19001a07044c0000d490f502250b22014000d0b030000c55000f090203010740c000079113840c4958100c01159102d42ea40704001c00054580d00790540001c11142c0c910350308010254013502650034034111601d03141d115800188905095801c902500c05c580b4010903000300195070f001d090003003c0c1d03405801880041c0940030011605911109009402401c8030703402501210142c036005002908050704613000e01018100d004c882038079000d4111020340d0f01003003a00141c100c0f00d1154415000d41442c50405c2425181611358842c8100c500b0010305942d8100001d0b101c448800603222150a56030300c05025003460f4404181350200130710711082203007500c1295510b140c1c0034846d031410440345480310140013803600120b446815011040c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 254270440 1250 254269190 254269207
    0x90a06030c022a09040f05011103130f06021215030606120604082a010b012c0405070e06160506070c05030a03050402030a060207030305190513020613052205010801050c 74
    0x404003900c412941d1032601c3e0543c603510000c1201c0d0003045030140c8000d8036140f20001081428014080e000c08500d081d5401c60505941c5c211143d1f90f0040d00410919270301e0002d404002041d015a00d6001544024021078548607c218184800384081d25200b0702802001803850f1400307203043e1101070b14403c01480d00365941e9a40350420f0740440a200c160200c01904101c040d040511480e00ea00036410022910000c004000340c5100c04c40380c40e580410b941d6003180000500140e66840708400c040f540407845458454040c0c85d02600075a0442e040700c00000c075105106503444105554910520841d01c0640e98000c0442c0c1c00400a10014400d4108101003160360344683c00458000303000a007a1040da001d2039803502d04a911003030b012408240c030351040086400c3e4440104000c2c1d080e04405111900c0d000a40038492031840740b000348a0740021413a2480d09541800b1003019010184c4542031800c20300080d036100440009440e009070381000300100d03440308103010700360092071106102800c0c034281 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 254271690 1250 254270440 254270473
    0x108031c200c0d080f0105010c062c07080c1008070f170106110105060d32012310032d120f030b0306010e01060318060e03090a06030c02 60
    0x101140c2542851003120905003080340e000104082940c9000030b03c40300c03849140c0942030340d0340280742103d440b490707500402569070091161820254070401c0041c8041180d59082400070307504203001c501102500250241400014503c01503880300402c4036440a01d0380c00700004175982c420783c500001e4280c00031035001350080300540c11160b8542440d45619010a180c0b0260400903842a00059076102a00301015000e118880c0c201d03030b05071102051a502900c2e40200b60b10514084807004a003c07050340181100200504a5104a40c000380108901c081d00744c0403c50b0f071402c11200402c0404040307450070180c0c4101000300ca034800d10b0450410489404200800102525015500301c0400c424000800355614940307007401b40c1c4c41e20003001c81003200c020102c4101010f8140030f50300ca4001440503081c000e0345141168003529001c0750a034156140309100840140b03005250508112000062038400300203007558030300542d005a0b445964010440540e01c4690801c800b5801501d00e21640c1d222 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 254272940 1250 254271690 254271701
    0x50405030f0c18093f121f090f020717040f05060307050c0609070314150c030402040209030304030f020f040b0607060b01020c0a1d010e070801120c1a120108031c 71
    0x10391606480384c1c1e00c010b17103c915040020100d4070540e1000c01a181403202030715945d08010751085204242003074055910119061006082c000b1034105407181d03003081007981d004d400c0180100d07550500a415031f4460503000780d002840d003283d60312140c501c0c1c00748041611090350b04131882d0451194019207000280003403503201070104020048200403c9445031380c02c100c658050780300300c0c0080a4083c07550400300388802182e007407041d043e000704e841e8191184107100180d4200069990003135494656100250080c07041001c856050b0001103400414010303450f00c030740c5986000381c4108070158101000c010445244042c0710783d01503010701c600400324400390301000d48401306004541400318410002441c50b51240e020350542c004442540c243e81644950140c010f0403c40412100c42c00c0840c0702515038041405241c034000040e0443c6418844400c241074010001c0d134107d18100b136141d80c0c908070141e000389038021844401900000300c0f1031002084030880c201d9006600486040c920000c0007901 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 254274190 1250 254272940 254272951
    0x15050402130614010e011b17070215040905070504050904150f0612020310020a0c1209091803021b030303011412011a03060f0903070206030c0d0507050405030f0c18 72
    0x8220301c24a1140744168410280a03000d02240340b90510020800101131121082110341003128002044070b689510310844c03404a90b22600c541300c03c00f180f40c981041801744100103980700380d42d20f146440f5012040c0051094503a80142400180d95191082e6054801e030700c11a03030018401000207010840c0315a04035200c041c000400f086810144040e01c041e14459085624260030151060302149410407202c826208110010b506200910b00003820400800202400903903865000700740c1203106002c900302074101505c0800c4640c20000b03641e02202e85422040b0054420b0864914140c0d440d80d00e01a6040f034002c00071407440c0c0c2400c0036110b008140318801d0f5000051894611000802801038a1000c003001003146d43c04100785080502c1d040e00904660941d0744214184510002c01008968000f501542c0742c660300d46580c9000c9840d0701c01d4205916041d8a800144014141d11200030b008444040f002c942000c18181c0300c868a981c01070441940c004c440706c40d0040030074050f0094541c081c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 254275440 1250 254274190 254274199
    0x2203080601050d0f050709060305011d06010c0b070c0c0501110d050d02041d06040b120c010c02270708090708030405040e0102090303040902031e07080f28150e0415050402 75
    0x80c42d42c03810000e80784c00000b0584525143e0301082803143d480f10b141c00c003d110f9440c0c10b1060f5490071900d0000707031303105902191740070141c00c0c0041e060f64010040501d425601141060071481c00c003a00900c0c071040103808440c00725407548001a21740c1b10700e02060508004c00b000d010fa0104501c2c0c00d4540364400501040c09070740038000040e050202c80c21900c550005210508120b24201003008102c80840c400240b2038107660200804402000425840c001003e003040d480c294440c0c000110f071000c0100d40c1142101008404401d50400f0030402030040c021529000750700e44803912001c0d110f81c46030185950542c0180701c100030310301d02600507481c3d0189203000140361852030b101090460f802500015980d41e0000184401040303989400e10710b6801c1460040390b0740c20001d000601c034480c098400c0e83c01ca1040c02c042400780c14040c81383c00c100000340d030000c4801b412110119014020020300e20110070400a000103690041c010854412035000340c0b903e680081c06c1d01c1010090a0207082030744c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 254276690 1250 254275440 254275447
    0x302070512030c0d0903080a0e150d0c0e01050406320406021b010c0b07030e010e010608100f0603050c011101020c0604080712091811120703050708220308060105 71
    0x2540c5961084501441e000e01c0990f81c0d0b0031020030114a4500076007055401c001201d5001c0021503120015158107400d0b618001880014450015454443c152a0011520000110108500f4030f562020a4140c0a034580d00305070104a07005480a001d64441c40001c81e00b60100303c10150385014010111481d070900d120040c2e61a07000c048202d030856040fa0000d03903c4035092082d003940d81c0054540480b030918010601d060160754800300900050414402c0c56214480483c0c0c594083d00f060341c0803072404008015103a940c412540e038035001c2d429032a0446203080c0d9000304502d00750041d103040d01c4d0460010041582c0484c01101c0b203c03408602c0d43d80c41d5600340402e09904505000582c0514051398107152110102d040000d881c841141c404424800b4521081000041310300301d00c0f50300290b12000084001c4283c8140d20503109042c844000445041c0400964503010b0b40400d0091019980c0c0f005641d0f140c1903203a100c4d405518880030001101c500780b50029214107a0607034404e2043c50b00a06 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 254277940 1250 254276690 254276699
    0x6070203011104032607030e0d111f090e0f131e08040603052203031a1302070507170a02040c271707050618030c0a1e0501030c0813030207 61
    0xe035a082500119030b030178002804e04080d405084207401d00320340d41c20000352030050380303940c0a000c02040b02d0340c01d0b00481360702d085e620a022449030040d500c100045d001c4000e5a14801f6401400c07d102014100410030b20700000c1214024000034910503180c0900210b42900c0d40340c0107500728a402c02e01211030301801c0f040c0703298880c0030f40508840603114440c40b50f103540c100380c4068203461000f00709054400c184140d2499410b009070805000030707014100010f00c11f00700306441c3c15140c941703050a1780011600441001504443d401400010302800507154036644802c04e108100104c6210102c0603802150400302503e41607020100352180d50030080e910391504002d81c44c40e04400030020003c840030420411403d103421180548200070740001e04000360a000010715107003c0d0340401c0040071002500303010580c13805c01c0804441c00004204010b02d07a9100c1e040e1880811103c4c041d100404403110009480d400f134094940e1204160702c420340315584401c85400c030380d10658825030451003601030006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 254279190 1250 254277940 254277971
    0x708040510020718090f1401390305010e0f0604090c0801090302010e060702101d030c07080705040b181003231504050717011b0e030615030c0607020301 67
    0x41605900b07402520050345800b03010403050103200c540001d0507081000c0000051169a081c80c0901d500030404c000f2800403030703c0b680c01081c01c9441c02c2c8010661808074800361450b02500400c0003030081018081c034200d403208500351402071154101c158540c001041150f40c02803440c40c0c0c003441c0900001008080d0b0349440d00c45190075840309c14565921a0414140341d420300489107414a481d000300f146e820505c000239615403d551b000e401c00d594a00542c43c00c84190080141e000b02c80340b0850b62900720400003284c8941e007610802d081032146041c0001c560806004180075041b00401900e440900040d10912800e4002c0c4403043c00d0420f4000400014000c1c48004401c400d0402010106456504620310b00001c4901441000d20b14008000c00900005042c00c20f4564000343d0005407545500802d016142e40149520300c0079640340c0c8540002c0d0300c0805004606003c41c2100c0e800d4490f5850321820403046540c5c07541581018051881d00d00380701004140d814405400000c0d40305400c002d41d0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 254280440 1250 254279190 254279209
    0x50601030305032505040b0d0e0106062105250c02220b0102070332060103050303040c060507110402030903070804080a03020105010e070f0806060708120a15031707080405 75
    0x71008a0b02c084140071590b0140c19a0507a20102c600707100b4901150300002a00d5400385210f40c1d4011203000a030a454210580c02020342952210024084540c48940c083d001d003102c4035a190101c4101207000c0780c20045409a01d00401c0684801d40003040c071240032010100100959000b4801c50741c803050010380781c1c19a1181d0000d040340d0311001806801e5040401d44554104050465210b00400c1c400b01d40030307080e8090b08041d811031104408425940c4440c010f080c0b010004214000c078000003052000100c02944540d02c9400855035030f6840e554140c2d006e004154024007a12004212101103042a074021600128018101c9041214994855031a507000da081401160001d4401804140d024001d07a405070401c03050501d181d103001000244075481e106075490410603c0808904a61201d5007121981e82c0c1140c460703603540c105c801d4a03820303000040d80d004842c2c0b403502c1c0c0d40011036005905040103880d40207030402000c2c00c184114141e690130181d002d8451a90401000844d99200d1410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 254281690 1250 254280440 254280443
    0x10507240605010f05070b010b0c0c060f030a0b1005090d0c1701020c01060504050c070f0f0f0609030f18180209040603050a0c09061a0a02010e060108011d0d1709010905060103 77
    0x4101d003030500d400100500314400354841880070030300c52080082d401010071410b68a142000340c0c0c07a4501440c0d11032031314000921503600f02c6c20018030060040d2150005510619040f03d0a0018610034800d010aa884201007040001c0c1c0520043d400d80c0b9241e00500017480c050007003414203e4813000c9640441d07211101c6a00c0e00c3c1c0d4001080d0300c1c100020301960004120880e41004985000c8068040a12400000800300304500d40c01c01c040000c1d079107282902d150000141103908000d4500300c001440d0341d00013580419040c0c00c6002080e4441c0e50182038448410181e054003a1500030100710310100c4451480400b5020b0001d600642c8942c45403600a50140e03008040340d00b418104000d6407000794000160071030500030144103003500812070701c2044c4098062079544d820324006c201e004128080c0380740300328080c0c4000007035052415000f0141e140c170121441c20014294880440d580c0c411441d00c40c01040c10074241c0341e10b0100741910750780e06c00790650010031010403541d41da03420314500345c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 254282940 1250 254281690 254281763
    0x3020306150909030f03070f021203270601080c010c02011110060f0603060b070308070c0b040507060e0405160305100b03010810050109020705060406051012060209090702030711010507 81
    0x800401d24900000140d400a4008018524081300c041c001c800b030780710080480c020f008020b0b00b1500168406c01614016840307900e1410307106e040042100c6081c1509488419400c0e1510078080e004603404102207040720307002c500906460500c1801074038140070903002641802a1010744651100040c00040e0a010710881d00140d03142c1000c6c102130301500d8980048042600c2c0c01d03c10300425110100303e0342d509030141841101980c40c40c0c42180c00d248a485d0080c00c000441c0c060008001001881c2c0d015600e40341c5540884038011024882181e038101d41c10605607040405000c6014002d900080e00800c0c079a03e080791a50300c0d5002c1e4540e691003a030042d480d6501020080050903801d210303540c05403000c983c0035864002d040e1583c954800d0081c3c809000d01d562a0b0214400410000c403250041020b2038112214060504083c2d0083d0800d948032030082e01107d0002c2e40061000c001c5072481644181a0201003264a00440380d541003480b0840b00f284580442899082141022000341d011160b07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 254284190 1250 254282940 254282971
    0x102090102160e07140f0c07090f02130905151008012102032d010c031506110303040f03030209041418072106020f1201030b01080705010f080a0603020306 68
    0x8000a140ca80b0220399a4140c1d441d252052141188404441d0f4110a651800c8140200d001a05000b984103082d81c0340c40c5140300056003400c01c2d00108002048030841360040183d0442d0003000310983c0f0a010a40c401500144d8080c840010154081c0350040401c138514410082e01c000418a080705c40c0900e00d000c180715000410005042c0ba600c0300e800c070301c42c21445151030740e20303400b00e903980c0d043c0c60949a5602d030540c00c9051103201e84d0710f80445001450001e000240419034054020110b0b50705000082521040204000f4041c240b00040302400900451842ea101d80341c12440c8030b600101141059002c0004014541d124001c01c0b1200700324402030700c1c15081070210004084c03030f42d000184940d08046410001d0b03075401038481c141900381c1e1184908900e0980b52110081c460f0703000c150000640480c40020040301015105c0c1038910621a03003020307980341c240850f680c01291151500141c0d0000710b007264a4030908005810420030040880c5040e00c940c002418000c01300c1d060006d07078091031f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 254285440 1250 254284190 254284207
    0x1080106090204060c06020703020c060f0705011107030f0f0c02040204090b03060f070504050409030903050a060b0102100207050c0f060c060702060a0f02040302090105060c0a06060e060a1707140d140102 89
    0x80c41010300038844518110f10b0540341c0080a4a10301009001821056000c2000414580280085030f10480c0041c5208d40c0c0318030300800c110550300008030a03550356180481c0e4102c3d10a0420403140c041e90542c8a07051071007c40102241c0e0078485200a800708240c9184030001030700d550010344050b0107481008540c0000620615141050051080d8141032041c2d082c840115001422101a00d90a5801040380c5030142803d81c3ca03a200c5030310003003003031040d0400c0500f40442d560040e00521400d90039242d0681c540703144902030340120a0045c20641012200741c0c82440c042c4401000707500e02802a900304109050740300e0401d51300300d0f18100507801940030068030085038132507103c3c0300b81c00440450600e4156004100c0c2075105019990085000280841e5400c1e01002003904c3e840d805901030121645540c00c01c0741d5402c00760360b26401829220310100c0c22030004103c0b0701d900790301c26005200a514000080b00c000d141d40c4000368205490f041e10748080340c42c910103815604640380001d43d858000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 254286690 1250 254285440 254285443
    0x10b220303021e061509100e090313170d12060512060f06010c11040b0409080a21060305060610050c03070302031314011202030a021306170a0e031e0705010903080108 73
    0x50769183c580b900030204000f524a040e000805196005564140d41c42e694812002e41c03210311500001403920000d02001900d002c00001400c00d0b4201d5550225020b5441c50441d440c02150000941107400c00c44680f1160352041418071401012480e0105941c0d80c0c1e03a0108000c504025000050340d04542d08100c1340b000e03c480381a03007040013840c011321112020384179140707180007012003544502c0d1a102d200101342d0751500000c3c0e059406c050801e1741c3d6848000d0243c0300429040501c10f6503082c055105000b001c0d5481342804580d013100142c00d0640e500800c10043d404500c208030f003805030511000019100400103000014440c2d0011035407006803c240d81382d8111154040220b4103205031141c040c41e40d01c10180502c183c40f030000981c0b20344031904d12074040d02452440006403102400000790342a03000d441d03891050752a6004d0140e03520355a04d081c0035940300740c042032001d609c20442c0c410703018a403040d0710240c1520100081e05000c0290f40b902c0c250380c80d10350305500148000c40180400c000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 254287940 1250 254286690 254286733
    0x1b0f09080708070308131e0303081f1403070305010c0504090605040b15030c0f0304032001050f0115031d0a14030c15190f0c02010b1503010b22030302 66
    0xc4200003400c8040c604540300c0d80e2552103000003040050301080222200340a00041d00c040c18a60188500c201d040c4945002641e546100540000740041d0204214881025619003644841e0b141c94190609100b90b0001c0a002c050003036800d8803030140c0c0040400d1027813284003d000c0741c5981e000c0e44c8520307000007001580c80c40d0f00418815031903c842c050065440d030100c14142e041e030340c01c2540c0340d9543c41c0d0005640d00608820b207501d084000100010190f01c0b81d0b108803200c0c12501d15820504050004600b00e50301180d8070040c52542d10014004105141c031158140112494049514554410181c40c1000f03007107200c160590200d1400000c00035602c800c00e10300f0014a0085007418a500c41ca6641d501c041c01d00544d1000d0901d001c0386520380c258510112161400b01c0c244100050010300c140104207440c072560040d403824044264901e000b010766100c080034681c074079082d6401e000402c54150b0200c04000c0c2c040c110302800c3c840b10003000403035000850003a00506691220982100410700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 254289190 1250 254287940 254287949
    0xc030b030f0d030c0513090b01092403020c0c12010e0706020f06130f0b0405060f01090207021e030703021f2d030e0f0109060e0c0301050f13061b0f09 66
    0x410101c140301c50315600280b140146442440d001c1800252203c1c2030742c0a04c150454501e00f151217242c00b00d21409143c214085d0013100ba41c1d2003403800c4d682c103a038144440c10900708050a540c0344c18051802031098000c2c00c5e19100e04003d8403c003c10460000f0780340802007400030000d945031080144c010714203004c00b80051803140090709401d02090352103600e400004050078080c0e9070402d55801071040320303c41d02d113105a1241020b40103081c642025071fa10801221001e0012012800102d5080e00030f0003500c0c1925406405445000c140646000b000c00c8046500ac0d010b101d01d500c00000b680d03c0c052000064244070201c0b98000c2d20803140101a90520542000c141081c3c82040c0e68004c0f00007901d281e004598540010021802e44e019428000094407244456003441501d80034803003564000004c910040080302d0591070024181800da41c803c4800800b007480705d00c005920100401c1c01c0b28141880b50b900006c07a40700c00c20740052074000c0b03c03c21000240c045150104110b811848400142 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 254290440 1250 254289190 254289193
    0x61b010c020625090902070803250203090103110c0a0c1401020105100b0702130e0321010e060d111c0b0a0e03190509040c2c0901140616060c030b03 65
    0x9140c086062100f0a89605128648415910410b1141c620501c2c4c07010191001410a540c0c800f8142080000754100ba550b0002c0020008502e04a500301c00c0841003400090b500514182440000103400602440710040340003082002110300c14101804012040c51044a01e16030043c20a2050210b42c0383c01188541568940818004c0c984000144641258100000c5982e504950b10104d016010805480c08825007800c4400071680c002101800003461051000c8580c44410000c3d000c04000a11075180e642d46d9402c0850414188901d600140c24051b5054039000d900400210f001000c1000110704201d1414802c0380c208500801c400b03800408503101409480551101e4503200c0c400c46000340072042e800e208060f6414091810b54000700b8004204000421508901905143c00440315a4401e40040e03c180154030b200340c0300010b6114064114801daa007806d01406d20801d40b581200d134400c0c0e06109110904403211a00e00c0ea151060b680801d280e0107004000d0141e0b40c001c00310724882d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 254291690 1250 254290440 254290453
    0x8040303140f0d0203060301150807080d03110909090a17030f06101d0423061008100603020d020d05040c150302090f1e03100c09060507030512040201030605061b010c02 74
    0x2d102c622402e540c108a141c4400503600c1e162140000d0040c50140e17102c14040083d020005a00300c0c001c0744090440d4400801d440c20300d20711040844c102c55038840300d000007213070500c02c900045c1445100241d2010581c000c8031a030308a03a4407241100e50420804400b00440001080a0342c419442d14941100f425100454548010f007000f41140200407105090a0000d2046980c265101d4000f142c1c2c0c405020f40c0480e003003089100890056408495171350044500781c00a02040e8890780242e4403450907410004452360500d00c003180658050248100d099400303104804500c4c0e400c3c4900e90041d4403403102192110318003d85031440804002480301498411b0060181c55290b03035141031084e103411141207595400d100400b83d10080c040c42d003580c1500c1580d441d1543d69405074044150700c829a1146150b141c5d0b0382c40126024130951000800203030007070100c0c030b41d02000703503081c590402e205040c0400c8031070b1141c010a01e150400c81135070700f86681103881404070712420301c109801500b1a1001d0f00344e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 254292940 1250 254291690 254291707
    0x7031401150b030406050a15030b04060c0509030d050306130c0e010f020c0f13020c010203340c06090510050c04030201180f050d030e03030a0e090601090f15020f07030804030314 78
    0xb18040280050601c90b101c2c0d0021f2101020f90340021189000010401040342e100c0c10301001d41542208d08071501072902c0c0300302907890300940986a01c860010300038a090405e41030110790340d400103024030f9001550b0190480c0b180c5060700412085444583d5001000c03014074000400d0071500c11055415500300d03030002e41541d121200c1140944406454440b6800411304c2140024407803600310b1900380d4404000e106604401d4565040395000e04550a1031101c0190864040d055031f10940c2030218401000e407100140242c0c10090000e8014003e40d00e42d8414a4000400d48108480712080020006014011507803c0010f030445e0b0351081d80c0e0300c650355050070f00c400000d526600071103208003180d4401804043c07268040301e604401c00b409617500c1e01c40d2940c01030010340e0420301c540d100c0e03140040010a113500c0707414210104c40d10380b07a1980c4038a103001001504813000900540460003040341c4407003a00000c0000400a5115042a540d11032075401c0017000da42d403e408030310a141c001c018540c3c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 254294190 1250 254292940 254292959
    0x4050303060f0607080a21060b16030e04381005160501020d1e0507080a0c17011503060503071202040b06391227030703140115 56
    0x941c00501521450800050240020038900480000600040c000201c40c169280d10060100104c07408440c0b03034200c0300c010920001501c00500980c10586030034481c031141e60603d048054000d030f0190400e41130030194000802c05440ac0001c482d061007100501c0c80b640084800b0021850303004401c3c603501c01c0d44040b00052041d403083c6c0c01070307010804081121036014641310031381111594001d00840d40e401e184807016001d8500c0c0022801d1108600032803031101d10b010b0003010b105400d517513901003250b551001071000800c49880d02104002110f40d00810803c41c02d440c0a01800c0601c540101d805840b600040503641e042e0000350290300b001c17030308100364240703180e402043c00d504480224400c0c2440d00811503a009440c1c0441c01c404103684c1010003218841c01d011104c5080003080c01031016141e800e1340c3d071003000ba0000d40105404100303c0f072102d210a00c0340c00085080112503142801c681e40007900d00f06440e01f080d20703103a13242031030081000300900ca451001002c80d00100201843c000005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 254295440 1250 254294190 254294197
    0x20f070303020a1b15020604020415061704050c060706052401050a080a0f020703261308031509091c0801030b010611070504020f04051305010e01170c06031509070305040503 76
    0x1032045500c1203040560f040710f104c030380c80034100001542810025480000355110400e4405a00461500411444d50482494400251546a115080084c8140501d90312526004005503024092603640001030303a00c04008202260082d031012401e42064020400311502c0e05101c54242c01d0a020994074a98102d03060703c031001158200000c4507901c0c00ca01c2e101601150702d280d46ca2920003c0e210040640142454003404040b1441251284850600c0c2c0c0c1045070658058050002c0b5820320380000301a480110381c0aa8215805652505e044020030302c5100309442d2560643c02c0b02580050360b40c00d44d4200ca0503210b6928040c085135155445020960070180124020444801c22900d16010100b05036030003004060300c21540e070074144003240047d400502070315219419281009c0d4840d40b4601610b8141d80c24403900002a0f442d00516050246004500c8182c41c01030b0341c410b18840c0d943e500514030880c141390010100d01c00e030a08111100400400040502d031400c01808082440001034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 254296690 1250 254295440 254295443
    0x30e0d050c01050c030c010915140601090b0d110406080f07051c0e0a0506100906060201050c0d0e100f0c0e01080f0103140c061c0e070b0a050304030306090f0507020f070303020a 78
    0x50f070396520200c2000340c03d5204201e9012129030038a0124000c1084e43e00308005410480e01d03040001d4407000e117002541481c10307074200c0d00181c41a0028172600c1d000a0040c500320401100006040c44d41c6a0103041c9508291f200d100898603140800c00c12115040e865a480300680c07505624010002c1c24814840040c20101c13032a241d903c12801d500d440c03003007111055080e005000c03150545880c808505020946000d00e001c1c0c0c0307040c1a00042d00300d0050089034020118114100e0509560420400003007510022800035841502200b50308121180300c0d510b0014110741e40840c84144484000c0d29401c507500700c141c1040080410808007149101d0f03292b065035403007502542145844038a6a01c0d111007804060f61007a400a80822a50441c4c0556a03902d05810710a20801400d4041a5116600c070f126041c5003180800605000c00c0c801c6000703681c071a03c0f900b00041c1c1c0c4c94560085000311808903000940740340e91203040c00410340e010080709034880d210a006188140c15564000d441740c007038810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 254297940 1250 254296690 254296697
    0xe070f0f0203160f0204020c06150f0f060d1103010906150521070905060c070519050904060b0a180c1d10031a12060f1f060f0228030e0d050c01 63
    0x80402003107000140d1641310f039001041503465100702102c01c0c2d1290026543c51b83d4040c12420500c6a44c248400704048070701d0014001144222442c0071b2029aa004c42d403007400c081e6650841260b003030785500c05035000e403140381000205542090458400b090b48404000180f000c1400b071001e080d207540450502400407038003098801d40790302c036095039440680d8000350703400500400c029000308000104c01c002c0310401c44140104002d101c1d8085c2c00e100040c02065004402c200000d00807400c4c0740c0240251110162030445450703602d0459420000c0c0e03201140b48202c0e110701c1c80752411940030001000c548000d24070b202a018000d00001d450114140c400411b26444140c034209251070449011003000d40a0100b1035092280c0e03560036160340044806400c030011860206603c3e60220300081000030602401849660400c0d4068854030742d00e415080440c403da11070230900d82000c40c00f040e06640d4000c028000c8406034680135141c0d400441300300c2c0c01240c06400700f0380460030000d5490f982c84400e08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 254299190 1250 254297940 254297977
    0xe0415021e0d090203030a051201150f080907031a07080f150d060209042c0c010503010e0903160308090c120304060309020a08030c060103170a0206010b0d150e070f0f0203 75
    0x440b0744081c0585440281d410f010100e0005400d9030807200800000b490301c40400c9590382c0314007408116889800c900400101010360038408a4007030320210760003414030001c4610315a030301d90380c1486041814003200940c4d07400109106606411014483d001303114114008054540301020f00f4400308041801d51041908003803000a000483c0d0441d0000030000d042480040d400700442020682102d01c0300d40081030a80c540c07489071a0101e1304501014050f0344a0345103910b012000701c1c52020241c0b41d00030b0b5010400800c20141c840146401c1c040d80309840f105618a020800d2504204228808078020500400321000c1448044104c40943c0d00d03d0400056600701400030502000d04c80d044030020340b000040c0801c0d1288009203c504aa2240451914880c0c2d4040358070300707900400c01c01d0405640200018854410302d41e010b040300a0554200007034485840100b0259030249511191440e81c440090121403680807100c401c0e0400e690508144109480100955900c503011740101e060280e0f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 254300440 1250 254299190 254299207
    0x201080a02040902030901060807050603040f0204020706060506030702010e0c01050a05030a0e0307051006090b040e030306090403110a0b0105090108070f14060f03070206150907020c1302070c0e0415021e 89
    0x1036060300d000e0f0800307200854072442e0070108140240200e000c3c1030300c40c3c0301e8101c000400d490240101ca125550044920a00701e01a500f40320281d0403407a4100d54603500d032030000c9260f481382c9010350b00c120400d900218103d900401c441d820001e1f48400d00b410031004112780c2819540040c04c884d0401e42c0d80c0800034201c40d010030720310308502941070010f01c1405850b80441840481760040c4003036070f5829208020020b001b4003000100c60341c110300b540c956041400001e0b040e251030400c65030b1203402410101b00c14206500307140e08114484a046035031884540040c083c0d805e140500c58050500304009250745414042d200d140c3c074505200314141c41c0c04900c40030041d6100c08056800c80045903400c5a00d0341002000607403036182c200c803210880c00320640a1115490002c049500800042d000fa10300c1c1c00e604418801c00100740b580340c03041c00340c0030041003000658419865001700141a85c8040301e0510b0b18000c001401c008404030700380703801404802100304020368405903203e0030f1110300351780daa0607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 254301690 1250 254300440 254300461
    0x1150e04060e04030f030e190b060a0902030108011d120304121704080d0c0f120c030e0d0503071202070209070c03031d06060109060c0c0b0705150a0c1209020d020108 73
    0x210340200c00300b44007100a2004060700144030400c11032050720140304440030f1003c8280d5842610444410050407224810042102034170f007076801a02c05010001420740304c141002c00d0b6070080e48100441e070356458580030003103000600b42c0d00c002c3c10303000a001100c20744402c5401500018201070f090406001e80070f40c1c001c5c0076103e6841c2000c10b00329020703910701e440d04104246401c542010242d503418400f09020840c840d11002c51000c1075920364003c07201a0520802c0182804103508e4181562a03412140200041010100e40b804590f20559645405400200720003402452126400d00501507000180d0b00ca074207450f40b2000c0ca1070311071a10001424103e000c1c0c01e0094840c46000e0070044101c010060204105219920030b803100400103a46080444081002c3c4001500001c1814010700044055800402189008108581e40c40d04602d816100001040c0c07210707420703166652800345015410030710383c1d82440c01c07601042000340982c2d00070803850000c0341350080c100460800051349204c42c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 254302940 1250 254301690 254301701
    0x11180603060102190b0a0506090402090414010b0a080105010306150b04141c061a06040e010b09360a09080d050703150b090a090605031f1b0e04060e01150e04 69
    0x65009145445541e50803c0c00c42450140c9080c1071b000e0400c400140076081020540d8040c960280035102d031aa1203441e8283e0400d200e403c440398554071242080119030341c140c007110240070507400006980d4074500c3d011042350303030300510404028071840081020707032400070030b071801c844080650740c01c03040c04180006c011001b455600c00c5280030301900e54041c4000e5510418040380c0c0300402403100b07584241000380030300031446441c07092200c0ca03005104180050000d000c03410005818002d0b146140c0021070717100070b180c80c4846080c081c400150280b008180340742d59044030000800308003948558881185a00c550000ca21b202031303d07000402c0c1041d11a9000041c840e400102006500c1d85070310001600f64451110b9504c10101c000c004558800b00e41700314011528000e0091117205451450803081284201c3e0810341706550f2120259102c468800c0b2801c500703901d944882066950000700003c5500c0c0ea04116188016040140a81d461b0841403a10384081da0401d002281d10440020340a803e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 254304190 1250 254302940 254302963
    0xd03090f021f02070e130f0206070f05160f0b0702040218030f030a180e160504030506070903050d020a08180303090402040b1207020a03050a1115010b090411180603060102 75
    0x303000000e42d56103a82c07904840911204541e003907076031a0390740306121400302c1c10982e448035141d0140311400000404250030341e800c480c8054610340c1003401d60745604220414a4000341c885400980128500b000859a80b002500d109290441e1740340c1010710040e00b900034210020300460b40010040e0300d80050558007aa010740007801c540040800e180348545a07005800c813100072822125110350110440304004068a400c03085154065a5421480d044c10080c0701c03a1400b80b05e010000480071440c10701c100b0f031084a850302c400c4170840c558a0290714040d440e52010742150020143d16000403401021510345c4442c509164440040f1100040d042d88a0b160520f54005d00c0003c00190801910b8041d1205801a07290a0301d03640e1103c2042c0d03110400580c00800145007046441070490050307001003080841e9804407200000101d2050305011b10030703008441c0a88001c00c06900c02d01e018016504043c0350311350907504001900d04803100707d007041d80d001c41c45000084009038035a403007000000a00c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 254305440 1250 254304190 254304199
    0xa0e040606031e021602210d030501180507020d0f030b0904050c090c070803040f08040305151b0c100c02010b0a06050d0506090601050d0e0f2407030e0d03090f02 71
    0x3560303400094010804600703c10b5012a64022410143c0118800d803a144c159456100c64049226400c21113608914280e0703007186065400d0813661751404014071101d111b09901e0014680d4100a40321008504c40c91212500d02e0500c81005070392907001c1891450490b15040801c01481c00c0e10094018014150400d034000140d85d0400c01800000036245894440a0750300c130fa0141c43d114a00c00b2248200d078005030045030100007040c00a12295601441d050145c0e610354201500e995903241040781780c001c4c1030140d100d8142800200f1070089102c888010707031416803034600195094100d4a503400006807184840d13598504003035440c004e400c03200301d14000900d0150402e803074680207488c0f5006000404030701407401d00010701c0c1e13050601e01c0c1d034052001611100e0400c0c184006420142403005220040da006000082342c03000b0b010000880032007405d481e00002c0305035940081074951001032030303181018205034494910b4200455035403000b0140f4a000700340c81d212810700b03400b007060360f10000303402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 254306690 1250 254305440 254305451
    0xc0d020604122105190507110603010902070201021203011202010e4618051003201903020a1a090a150201051006120e011b03051815010b0a0e04 63
    0x801c0300c08031038114420006034550300d090600840840701c900038400349034880302440c0c009105e00c034003520250840030f01c12000c58201d00140c0b004121690030030780c0100c1c1d0b000e0b0046401411903030144583d00c01e5030200704e24a41150701d0400e044240c0041d119000e030511144921038070440d180d05400522001041070301c10003201c061190391240820707015145e55064001013194440d01c044116243c210396251f0128502c10300e8403083d110041c0342c003030407600244d0080c0d0800000107030418040b21000201701061202703221180140141404d06203000c08036103414507020720040c0c1e65520103000362148007011401803010b18084400d14800c0324030281c0d1000c80014002102845d29000d40414181640240302944174041c2e80346a4807402d00901e004200c071001003201d80000fa5200a40d40044000085000600041400c000c1b01d041d80d00880002d0311a0100b04454440071252902011040c0c02807218a020910700d4208003818001c2d044103d5001911403800f61013189051401a8010000c202 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 254307940 1250 254306690 254306693
    0xf020c1c0c06030608030409020a020a021002011d0721080706051003140606210106050918370c0506030a0f0b01030e070e0c04120605190507020c0d02060412 69
    0x2803180403890100c0d10415100c601103002c42c800d010f0300048035807150003542014100560f000103074110f0a44481144650711241300503a840416829503882a42c00025200c0c6008400c0841980300406a840399400340c201044502c0c235803010481d03d000c004403a49083e055504c7c020f0a103214030403000d01510309100900c08165201440482200d104000c248441c1001c00066510b03020102c0380c50350300203410603030b069151444c109101c5440d0302c054000150940c90341c00080401405540c42c1101248181030f45841c010104525505100c00c0f400aa089000d0682101c04c0000c408411040302511101840100100c2c4045035000c1c0c480205011b80760320b4a5440320340108080080314a94508100040007154028442c6c20640c15140c409411070780c1c1000310001c036015002d4034850000c07070108400120701442e403e5049140c0d20403100818541028100f0350315141742020b00c0e10006182100340308085400181c0c0f400281d8098444447d0090940002096401140e100c004a040020342190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 254309190 1250 254307940 254307979
    0x2030105090a0b030a030c080415021011040b04031410060b03090706030b181008010912030b0108010b070209070c0602030c1b0d14160804060f081b0a0f020c 69
    0x181030320800d03100980d00755100128030080e074262449040e010b0300b04008850220f4454020011043e00070144146429030b00c0c0c0000e0f800689902050700140c1003152801007040c0b0600130184e20041c9420811b0a00e4203200101055204a110040c211302e00c982940880701c10074445941d4001c55080100052960340d10a0395143d801242c1c001c2c1580260720000c21028028442d020909001601c2d40c85a450458100c0c08040380240c24841200960540040c4150007401a03106a0340b040401c0c68200c0d4043c1c0010f0191149020442e06001410b40148512103894040c0c0344030070f4046800c020f03903407a608400c0c0c5502041c008040c0c8118000070401016400c900010a050b1020b5868400c0204854844e0f40e2504c07810b9207807100248081039000c0705080100e0283c6228600303411000c104840366610007a0740e40c401d902c0f0700b0200310481d603941e0300f16800011466100d0100122026861028a0b040c01e40d0310400201205000e00d180b80d91044038400c01410850030005000040c84000140009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 254310440 1250 254309190 254309197
    0xd0b06040e04111e010f020c120706090b0c060a0b0105070506040b1803040e0414070b0a170609070c06050c070f0c03060b0102030703020604060504020f09150f1c2306090102 76
    0x16100c81003d0400d045841c1000b103401035000315504c00c0d54000a521303500449070401094000800c601c2900724011403a69842010710350120a04020402d0b94039100d40a4080c9201d44e001c0c4035640c1e4240018801c81c0400305032113902c020768080000c0e03040c7c02c1000596040c080c030300c005001840b49004100c06c00594085550083e131000e0305420344000002901507491152303000f11000030303080001207400604a1a003035030100e4010750503184840d440780012301881d0410201170300028110f01001d0b41d00024601c02e5900040260f540748040e00d4220405810312501e100020842540c4900150311010b42c0c005840c1e8944c2d0091700c0701100c00281c10030013252202804262801c0b40b40400c4402ea5600000858191980c5a0064019507407640c880c880101401032050f40c0080c1110346900c819650108500d00c5182501c002074448035842c014080e40c0c1b81e0071070085001d2a644512125031403100781042c2042944480980780440d48035648094400020012850511550042c000d2040040d0080e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 254311690 1250 254310440 254310443
    0x206040c080c060706050603010207141c0f020a0f05010209100201090605070201062d05060705012f07081602041503031206050a06080601020a08041d0105090403140d0b06040e04 78
    0x10300441d141c0001903201d021000005038003078820010390001490580001e903100300d00800060a01c2903e4540f44002d0f00342451340540d941241888107a001e22288003500514080e150500039003052140195481d600390001609000e100300030b4004010742501100c101c1c11000c0c203010025041c000000e0b0103000d010301f003100c1e0b02e4100030000e0b805510522484080351861003025400425440c0c00c019140c0c0320b02507411038090068400300301622040d0003051142d00c618000180380340c412103100400c1c05036207001c038079983c803981e24200e00700300d44010349050079000514141d44600d0035003d4148060038039002504281404500c000d1105c502019004407402900d0341c640042500518004030b900d180102030380000c845909101ca20f10854032550b000c0011300440b004c10000c2d072150740359500a0f500c0056812100f2802072400222403020b50f004003400d540900941c00c00381c1d0040c181810b101507502c110103003c1614a00703030070117400400703405401510a641d91a240c0c4c42c200000881202c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 254312940 1250 254311690 254311703
    0x1b02070803090102030f0a050f180f04090503030604152105060a2313020916121112130609030e0f010521060d0206030a02030403111618020c030a020604 67
    0x100055868010046942c0040168040e5103040c181c0c2000c1122900220101c00410100384035038400800540000d004200c50920b41e80200c80c00b02040000300b0001c990030320f01031824004044c00040780041a070790001401c9502258002041810240c040d91650000200d2174841d80c1903040d404030300340c83c1c050441c010803e6a00320307030303403100d104040e00d1504031144441d800403c400d0002032542501c4507085010303005030000440d91900058068a03040e1040300c0e880103528030420071550049040d0020700d0440000707120f0844019007941043c0644080068100f00000c002081c50001c800c516402d9640030004004000503400c0003040308030705026442c098030040441701060f41c01007064844581c2c4c115a50b18107038030011812802802c01404064005a400c01d45c50010703901c0ac009984030b82010b030030043e264549820001d0045450a104001980206a000303010742016000a0700740d48c00100c046d8800c40100800000074410303012501d10701d00011903140308c96076000c220107018600441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 254314190 1250 254312940 254312953
    0x20106050d050309040c0318030f02060108010606091526010602010c090e0a0f02090303122a040605071b090506090109060f14130510210314030a0f1b02 67
    0x1080c4440d55996950103000c5500c10f2051341803501e450b8100ba61038000b580b43c081468003d81c2180c001051290400714049482440380410041e07042084900400c2214000d111700c914203035000d85a03a0b003600031010103580e00425564518011000e1020049a50880b4000ea4800c010944da8203035081c003a83d0010f5007440074006003544200c1c603c80036500744540004094807190782580003070000611203100503800384104049980d060018121849418000031024505040120204580000380c1d079410303515908504100b03030800c416507042c0d03803040c1002617581034242481c60300c5401290904030b800c0c1d10000c001c03d001c16641c02c01c074064501901e0307403200c90f602c42140d4425141d0a000b04246e560600104100020f400314144450f45d001030004541c80c200c801c0310308140d40d002c0b28903003d10b66011000b008610a180c0d044e01c01512440055000c601f01e581d8001c2c181907000602900855011002c5220f0806a90128140c594640000c0011026110700302542c81e01c40c402c00d001500805 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 254315440 1250 254314190 254314199
    0xf06150f03260a18051f0912030509012102070f1208060609040b0105090604060201050f0a0209060403060b280812070b07050a09030b01060201060312051614010b1f020106 75
    0x903009000d42d415960810b9040c41c1000f14210303124000607201c4400000c00740000104c503210400307114034282d0b07520146c1182040c0003d01518400c1240d00040880c1c0220005a000c40d074001709441d100e040c2468105000314031481c2565203036404000901e4542c2c400154901003150000b050160f10741304170040d62034010030100545d0083c00072142c864206004100d20200f81c034195014414454050400300e082208003004076070103400507000329015039500c0c414080d05040300c1000d50341c090000707141980380203210303030101c2c413103000743d100c02488a600c440c4c3c4108682e4885c015884c00e59103200c1d818802940a00720312807a401c0324441c0350100e000c1c1e4400800da45000208441e1060780000901000d80c940300e000725034690002e9051810056001e20100010710340d2303410140200300d40d80c00446c00304d065080c041d185008040049051003010020001c840526407143c0500581013069100c00a03a5800711a0160034031a140e030780e01042d41101c0a0686070715454403800f000341c0f503000308202901d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 254316546 1106 254315440 254315483
    0x3060509010c1103040f060f050729011205060f0406140a060e070f0210051b0f0d05092b0c02120307051213030f06150f03 54
    0x44100c54184030b40d02000d410007102d4004051440d152801003c0c046079080c91147c40240710510b40ba40d40c07618011025a003143c1d0f01704202d404491b01840301e240614a98410140c8851360500c008a4084c419581000d1401d5106009003010f40b07502d200505c08860044c002c94410b41c40d042d440b0110410f41700901d0252041003804610709042c00d00e00e800515004055030308000300715003624110b030350005130b01500398542c42d0001080d4652214840d4007490100c166841c105c00026195107074107801c0002c2c006040000020040c0c0c0c2c03911000c00da204d0344d8884401c0740c628070700111110200f5403d00000490391080c20428011350203640464008408546203042e1a00f000c84c03480140001071181480419080e101c4ca85010049603a410500c4003500019024405e15032481c000c008980d40612200104100440f0710b4603510360360f00214404601007241c1c080952010403003136540c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 254136690 254316546 := by
  have h0 := BRFrame.cov_init 254136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 254136690 ≤ n) (h2 : n < 254316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
