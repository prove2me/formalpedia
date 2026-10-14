-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:36:10.328987+00:00
-- url     : https://prove2.me/submissions/d95fe882-c627-4efc-9540-501f3438fd8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 10071949 ≤ n < 10251805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 10073199 1250 10071949 10071979
    0xf06010c030c0f0303090b010f050a050d020105040317070303110a2c0a0806090c060901080109050408090907110f07080a0b04020604090203011514040e01060806030c030609030a030b04050402 84
    0x821420100d4428580344445202ca6241c240350038030120f100304e0000741c03210158020300913509182405011105601190315290000180c02e801142c420b0fa03010341d140508180a41e8040d0043e14002c507080200b101a0420004012410b40e1000d02c1c01c50100b0303e043e440300440302504054a00414240e1a144100440e40074054103012480d003451503491240f080181040e01c414003120010203504008001c03900b80700940e641415407204220b030041c4000d2010b00d00700d84c3d015000354115078100400043c50741355400d00301014490a084d054000140c2c4081c403150580c40b0482072817005c56503090750500d8003070040e1180c8628040c41410784d507074402c010313203008035524600d855003182c401040c4501d040c1e500c090a005a810036030044590611000101038415004a0704410800d9007800392842d050415011b15940c01040c000c810801000030300140458604001d031005500c001400c584451400303480981d540d41c003003a40035001908050400c0b2640c1454040c46010b9540100758900c00c842032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 10074449 1250 10073199 10073207
    0x60314060409060605040c0203040608010b0f03010608100305070311180f012105010606110d02010e120a020102090409080a030e03040b16020105070c080709110901140901030b060d020705060603060f0601 89
    0x60100b6243e240d038881002803da0b80e50b10078410000800d402171a02c8034a0080c003c0c081c08016484040c1c01901004070a28000b00442180d0555004d8100355a9613182e21420000401d0517410052846c46481008018840c1c04440100402412944021420801a1850504082a00c1060700941c140d401402964130300000e402d0200005041c09400043c0c5480349800e5a1043c1e12038004142c403400d9415544a0600c4100341070031142c0002c4c0b000000d922800d03603a5442003100d02c0752806011071071040081c403c0d0115078071980c0003403041c090300c600c50600032440c0d4041401a0003207031030003422266002020042d901200d4900030064140443c0310300c2d440c080b80c00400c0880c1041000c00c5460000342c6c01c200e100c0c01401f07610004003211818070590900f00c0e00ca4a58804403070300148983c0205d80ea1042c0c82d48240b03c0c07014900350b180c040c0c01d001600540f210310700607070b4000c13004140002d48110590207804054080c1044406680b40e940a040d2210004e446000c950440d4600280480d402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 10075699 1250 10074449 10074461
    0x1a060103020906120402090610050a08100b0a0305010f050406060203040b2203050304090b060405030d14040b04060c1205070b040303150e01061106070207050105040504091403031801060603140604 86
    0x1810050b01d080305030800150b19600440015500740c2c507440500c015810544243c96002e074040d20140628031840601500501607554018108014200025926001004507800521041e860292a4501d0100147c042d100034007611181c00b10301e40c0002400e14090148900b140c07125009503181a0602102031103d52086500050b080d00010051100010700000c0c0c01c021401000030716200c1d41420010821b072000000c040f4414001400f0900c01583e0205000641040c6418044690b20b004980100079001c0d95008442403c804180020000e8204224004152054030170b00d01c07010840b1400d4600e030080d2000035080040c150000b60019020740d101c3d00d0181c0010a2010794540d854070500d070700003c2604210300080c02010b4500b010702c420070900c0d03042412400500022401c10000810502851184034492a203070340101c0180501180c0e011440794000096030760b245040701c5944030340c1103d200807144540c0b814a000413003d202c1e1041c0c541c01d51201c0740441c03240c0c8982e400c21000d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 10076949 1250 10075699 10075711
    0xc0203032811040b03010306050a0204050603010501121e0e0f0106030c05010f0c02030109031706120d030b0a0806040f0201080108060609010504091505070e0f040203040f06050912040e01150c1a 85
    0x2e078410091640da40c1010141c401800e10072100c59896040d8640503058400103480c4402090061209110f541d41ea0000d03281544c0c402c0c80e000c3c04802c1601c0c2542c0c003034200054000c0c44101d84c440307641c80042035500846030700c80d0f540381125071442265aa80382281c1702c038807010f00050441c280034402d640c41742e0610365000030a858004034480031a0006802c550000a044001c24998004c402c20702c90a030700700da58407901c00c644104035291244d0400740c40c2c105155003c010507650340b450040c40d90350089240081c1c4900c00844100b481c00d454802c118421100090380894451000090040c10001d400b0b4401c00e0040c103443c1e071a03442c04c024803003c1d10110704100c4061041c1d40c0c2c4990082414455184200c2d40ca49d500700949102d5024001e2a40d9100641401240100300700b0021035050094080d80d958800000135060303842c0d45c061420640340384004403800310300107000200c1e0401d00410720305070740c400c0d44814600324120400b03803840c17103070558003d00c0002e41d0030802c0312001e40b00061641c000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 10078199 1250 10076949 10076951
    0xf1d010614120703030807020f0d05030621070b1606060b03060418050a0f0c0305060f100b040501020303011e0305060103080c0c09040203060601030e0f03041214030f0d02070f06020f09040c02030328 87
    0x10715002d404032b041404801d1100c000030030100c104411407070700b5a1540c42c01c03000150f01180d150049100756813251001d004100c06150002041c1d0807160005004560f50f5400020030400e694071100c101e00141d0040d200c0c24419414144000b03000c0001266520465502600520002c6080c0c1d5407180828100c4005803001e00308040f00101180c02480182d11803500d00c00c44a6807480d02c498080e640d40f03c290442c002810f8188014009660000104d1381135648c220344e02103003090807140c84812220301c0c0d08002d25500603440000100200c0001400c3c1d00b0641c0c60580b00180d0060050090180d403c0314080d51560040300411700f194081d81c0404494004201600c00000c651040c0c0c91540d07100c1c0d401405140b181c13918807000e12042c20448150740d8a140061850001d0070302040c04c950045807010512030740d00040b0340d01003018240640a0b29940580b0564480301c051420400b42d4000e1911540180e041c40403140c00d40c0d1020048078450145034014820f20314481d410328104030034a040100c141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 10079449 1250 10078199 10078213
    0xc07140102090d0f030f0206090d050705030903070816050301020306060a030e0a05010c020a031103040b070813030204050106031a03060c0313170d050106020f0102090607060f1d01061412070303080702 88
    0x60b850f00070440380d51601841503208101021714004200c000c800795603004540005042c00b03004c0700042030300850701c01e1314641a900c588845c20010305510904a504d03a1500c5650b00c001035941e00031030b074421214201c810543c0500e680f1000e050903480200c4030030794044820014800c603070340680d0001034071000e00c204442441d40c4581d1114211400c4045010144e072000c0003140805500c0141000c0c0da001ca240558101880c00008400502820b0001064800c000c285504030b203890790110b1000b1030f0020020701007035030b4548014005010300019018481c0b078143c861203450500107070f1340340108172443d0050f02d50b50701c0e401c188100c40c0b542c0380101d841030f81c20180c103442251200003070005202d1a00340000e0b15490803030042c0c68400107241c2c0c0e00d01a401801070781402e036140011fa800c01a041840481c810000c00303c14001000040304002541d0032140022000150560100050341c281c2d000841107907144804000b0720307a82184401140c0d6019600600000784074145541c0c01003c030740119045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 10080699 1250 10079449 10079467
    0xa0809090a021201090b04180c05010e060705010f02030711010b010c03030515060c01020c010b0307030b0a0903110607030b040b01020102040513020708090603040302010f06061b03030c050c030a0e040c080c07140102 94
    0x4071042a4818010186c40e5200d50310a407400c0e110f2001d8215007103000d070074038103056550349107100c03014843c05040c000b8141d4420300c252038203412200c005038054001c000485500840c10020341040e9a00000a000c01c002c100d0814014480c86041b000d05840e9208007455580d8102e010b0040244500325205804154501c10340300c01010f403403d0700c1d005001517180c9090040190850301414074051180d4803e160800100301c41c0b0208580002c6000c0c0c011403002414102500c0401417015800300324800c2d10708201400c0e41c15400140040c00407a000d00010082100482c00d0f03000c1c0d4001c0e103502480460013201c0000c85503004007000d40c407520810f803d0403c5280082d01036001241e040d80580d46031000307805039007403921401000d41050b04019400e2855038401d0412040c26400007403d045c5d4403a880101107001d4415280d6060080702180e680304c04480d0000d2100e0620340c00103000d1800c1c070191003102030240414500c1008007122080c103207441c0740c94262402c442e03048444c0c030555007048070850f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10081949 1250 10080699 10080727
    0x1020c0109051e0c0114030405010b0d0803060901090209010203040909110307030c08010f02040e0402120f0601080d080c07030c080d021303060207050f01090803010501141210080706020a0809090a02 87
    0x80002e010740054024089040d521021545080c490200d0360742241034190f0007170b0313003082c403228082103400d046035181e43d42e500d401d030700401c8a100300325848107041640c642001070721030086126034000d445050440e41d0b140d200d1001d070300a8401d65405030b0401d0000340000345050b0b0240080c1802760085400c00000c4030046410b00c415900103031120204a0303c240204c40090260411146a5900842c503007803501729041217540010300003d205400c200700c0442d4050040000c141c114100009440041d699024820340d00c03042c0c2040301d808580c90000242002000741d00703a8000903090748402ca1640f03915070743c01d121035001c2180303030721800d5007031040d2401c8030041442e150141d40302e954011f941740800c0c2400e51800b40101c0030f4054680c10014101c000444010540341140d000b03007131048031406528550a8180559a150313160490407804220611007241c0301401240d03a480180c0701010340340c0408030380b0340342031040142208004000010950601004560b0b200c003518000500705500e4080c0380c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 10083199 1250 10081949 10081961
    0x20301090203010302100e010c02040203060609090f09010b1f03020a1103070303090303050903161202010902150301050f1005030403080709120b060102060c04031505092506020c060a120c0201020c01 87
    0x2110540c1c0c003200500840c00c1030020380160064600300700701c08064650000f040020a800020301841c2c010001c161035499140c107840c00440020030b840d0042c0751011004080e0f1100b12101415503082c0a104211824030b001001403511841a040705104800b03c030a40203907018030703c01000c001c018285003003c0300c402d001406880c0d10964000c1901060b40c01c0007070940b4009400b80300580c10800554265480603103030100d50562210f442da0700490100b00c180c1c01400f20142c0039400070080c01411200c20041c0c00114143e51044034001c0410324050300f030044180c000b0748098080b07142000441c02290050345503d5015106151400c411911503501d002e440701c00341310031104a070f000000d0107425a01800807503840307101402c10030708051441d00c545c110008810b0a403650385580b5404a501643c0034015120704005d40240ca40042d07441309103070354903408103225401c01030081c0340d480e07802440c24404860b0005499a501862000d0100c0c0c0d02c00203044a019201c01d66500308184051491b081c0116 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 10084449 1250 10083199 10083209
    0x603040503040e0c13060305010506031b04120f140d020a2a0902070c05010e060403290903030109060501030203040c03030e0a03050f0705030709060602030307050a0306030f0c0503102901030f020301 87
    0x103191174615128800b038024015400c007034181810600103100b5500c9110070f41740c0c404803080306603542240102e9801d0b0584520303004446003040d100c00f0102403021681e898034490307114001c000818560803021070345500407142c3c403a005800c80c0c082c4d000461981090010743d0b4860031040d070141e01400714501d0790319407a070348142a1141c000c42c52b40300784034456000a00524082c208141c0100c01c00000984510440c0402005110440341c6000510103c1c102208825064002c081a5081c0300110030741e030b074009108103410a17040100128040d4400d0094901441d4011149503c6a0644e03030141d5200c03c0c91503403690808041c4900001041c41004803158640b00c00d405441264100070030f16080400c0794000c3e0740e081d41007802c100050f56000084941c4003c10b031804a4480340000030841c00707000103900150182c1c3c41202c015051005090fa04012100218100c80c084d903840000b4609480c0d5007071240e001070300312440010500c503440720030020007401450000303449003107544c910301240c1013a080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 10085699 1250 10084449 10084471
    0x3040611030103030f0e04060501020d0f1b0309030516270b04050f1006050c07030b060a030503040303050d0c1e0516020402030405010b010e030f190305040909030807030f1103060603040503040e 85
    0x100c41c2061b0b080800d01c448031b4015541480050708100021b0755540c06e11641c00104012166071070318142c4201e000c61100441001c00b100180d0050400800c5400c079800140d40380d00404d08160030b407000c081d00ba10b080f940c40d10034440d1036048852030610480c45011041104a45400b074216043d603c500c984c0d4030a5400d11310a410a0621290700e411240c4103421000c02d0100400000d00e0340000000c2138421241d109a61100682c0c95101291822503030b540300400d00d11021802004141e0000702900360041d5100081008051680b03003150000300140f4880380d00302d4411f0440094070b200e0001015505803921740c20144001660105089a004070340968080e50748a141010075a8001004060f68200b02c006110000402400135121105038000c524600c0c00d806802c0308060044055a006008141e8208900f41460901030046401100d101d80002d00e1315945400365681403081081e81c0840c90092415030b6600c0003401031960000d44140e0303440c4400e000003d615800e050038180309104600e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 10086949 1250 10085699 10085717
    0x405031504060509010b0306040209040311030703030c0e010804020117060109180203011406190c0f02060c0c01081f030602030c040306060312030b0405040b0609040c180608120702030a080304061103010303 90
    0xd0000c11a40040c151207802e9041003101306c8241c0d00043e0f8603030019011100d0f1003840d22940743c103440d0f460f010310b6010480d000c0030030280103143d0140d01011810306607441b0300e0200401c1c5001125510300842e802404940300c4ca8000307d002d00070009003540001306052038000140c5521651804842e0290b030380d2543d640000c01440300d60021000341601c1041a2402d6080400750003600b01e600c94001c0f401c01c2000307000e541e49024000400503100d1007940180c140396440100010450b150285103200d0750104242c4404544e04402242c0d501d8a02c501c8006940019821665050003940c809482160108001e0001101150440c4074a400442c812084040d07031800c8000e01809489020b0741840c030944c035120070800800ca540c2c462540c01001180c45000959862400e1040d0200d0b98000c1c00c580b12050320865400c0001d80d001c0300c280d401d10401c03244030301289200440c0601c250768009426802401380c94000805000c0a1a0060f100e0500460000c110b540f50a100c0d400980c0241c0c0082c01200c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 10088199 1250 10086949 10086953
    0x30b1e130201390503120c07140f060c0a0203040f09020405010810080a080903010e0f060907050a080c0103050618040c0e06120606060a020a020904080403050f0304060909110405031504 81
    0x3c19248103c4079048591214449001d41a200c80700e503445800c581001000c0d007004105080c01100c4a42d81c13810807180c3c003400c001400049070f8000d0301c012a10808504c1400c1104100001c40c038500c60804030040030315035940340c0d40684541100440300b05600c418040070604a110810806c058182c00900503111894100018a10000075004905d8524881d02c00d0203261707804204440e80580006906039aa841080070a00621503000c1e481081c0c000c500042166103004103d640c0201d03c03103000c03150115120000c0140d021958842c64103d0b0313012441886495000740c200660100000b400098100044a482071265104403000c8520581950091008020209803243c01840c00e44048003070804026035150798900140c030941c412100440d007054840d100308241024240c2c040d00c0005a03061501d44a00d0a800a000468060003503850703a072607202000055400f01c4040c2d907603c0c0030b0540f90100420081c00300b0b40c444a80c0600070003000c01d4544040100304400481c20780c401442d40307018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 10089449 1250 10088199 10088207
    0x90203070e060a090501140909040f0203010f0b0d11060c03040303021c1b02150408011d0c010302070b0c0306010507060606050a02100b06180a0302030109080c0705090106050301030b1e130201 84
    0x2071428640702e0384050181d80301140d40466403605440c02801d001d2000642c03040c40900c0c501498425540c015034079002c100412201b0340c41da07218544207500901000503180c2c0b00c5002d4902d060141c580000c00e498241003c541a00500c0d0007001001d800b03589043d6480251a0450f80b01c2d410960144e07010b071070041402031b0502400d0008504078501024070800d02d17100340342408110600a48540011143d0480c040f00d20f0040f82c2c0107118038002017118030320840444654040385003400350907014801081e8082d5000c1d000f2501a40c0c0d01044141a03656818403a000b1600040e11090400606111000018106100d004040c000d507855054071400418802868a025070340703825103103420454180c21507160541543c0284900d48d100072162400c0001007600080c4681c400395140d0b003040c10000074815040c008081ca00c0154098560250300d4900f440b4094400388600000134004100400218106401403a0808010507101c0d031914841080c529181d4001d4405045c5041070b030740c0584c00c542e04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 10090699 1250 10089449 10089467
    0x507090f050109060c060b0a0803160201090504050903030f040609021c021903030504051210060e180a11090606070c06080105011107050907030e0307050a030503040204060b07150e0c0a09020307 85
    0x400d181c04002c06081c500005c01900c0b1000700202020b444881056036a40e070800580040c02c188000c40e80c40c0c1c0c8103580010703282c1c0d180800607400f1450010011486007014080c0d2841030500c20700461a60303c80300e1f41800f00314801481550020b0348c0792030000c01690313074801c0030400034809400707400a40000c2c010040c06000e00310a040c14507410341400c100098201050780c04441086a280c4000c4003001c21842c1042e80449a80001901d032900c04104c95102054041c0202020505a9003c1c000c440d403142c0d59224840c406001164019403400352840c004c040ca540c0703c47d02410a43c18207840f40e8032420203081913006000031900b54001840656031107000e04410035001c0004000007407803c40403e441c040042c140304201a106c01c20010040310401c21140541d030b111084aa020b9418203008200350801d0350100c0c4950305290000541c4c1100c101541c0c1181c0d0042d02851201e0540401e0b0310007459003402c41c2c4801e01030004c071a040c1303940d400789910051000e402c0140e0b8902c0d0010f0002c0410340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 10091949 1250 10090699 10090709
    0x20111030703020601051e09040c0f0803071a04060b100e0909010603020f060d0204030b13030f080c16060e0d08090106080708030417010b09090a0512040b0f070f02040507090f 77
    0xc818800d010109900160250446d10203840b291440e40010303054240b0081d0b02410f01f50412041130500040143c200821821580c43e404035441d4103440c0c1d80055180d1158900280c0000c80001e03052089440000007075070054480e00000451080080115041d035050200c0480800c550103100c08141c1001c0000d980d00c010310310020000300b411540001c020b103680010705400b07250046105600507881d0f5046402454014809105915003441540d9800c00414030803000280407001c00300807140941050b40c090919074030400c0c10300c203100400a000415070f00003661440d49032582102940c0d4140000c1c80b030030090741e4880c4e840f440c0407030342b05003900d0441e80045402e0b48580020050010084203403000d8608004205001032400d10126000d000d602000603032002c030110920060354000654400264414000c0d41e42d070240070031040d141e9000303501c54400004ca08000b175101c6206444002c00505202d54810501050f141d00460111174044511002003913003981c0502101400148500040c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 10093199 1250 10091949 10091953
    0x50601031107110f040e0a03021002070305041403010f050a090b060307030b0610121b020d0206010b04050d020409050312040512030105030d0c1e03030c0f0305010f0608060112020f0304020111 84
    0xa81ca0a5100700140700d881d02c09072201100d80f03081402599881c01034442c00c0c2008000f40074005682d001c181d1101810241100035210702c40d0f82d810800050f00941c1e0700540c068456500385440d02000350f1110041c2c00e84580e2555a900b041140406144219800340c2110000001e07141c440c2e140c040031081340504403a20a91050108100280c00e50700516400102036070120005540c12005984909044c0007000d40301e8203004a0f51013444c542142d108040c0202da00305ca0b2a120b003000c003070740c0300c01c1300b0f010b0740045007000c01051086040620002900030310192001907140310399290281103801800d41b00e24070b51060020300040c048100000501c0c0e40582007498619454000040d984148031003c440600150180100030321000c41103031000c07569034900341401c480c25464010b004003844490640450068154442070602ca8031070507040c0c48002401f0080b6a05210064446440c002c2c121410031079424113a10450003240050b02180055440003612406d0a10026041c2e00301c1c0d640d2500b4603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 10094449 1250 10093199 10093211
    0x30f010b0306010501030c110109060b0906010302090d0809060f13050a08030f031b091305090f01060302030705090c040b0703090509060603040b040b18011104050405010806060a06050d060504090f020405060103 92
    0x25600801e00b203044aa003400c5c00148280c11040548401000000a00b03855180182c1d000603c07906400c4201c003030b4801c5850000581d42e075401541240101c050f40d0350410141c001e121f0001da1080000c102c814001807185007481a0400b440640394004546009040000e4204004038140f014000019100c0f003000b442c140449104c1850103030100a11940390303280c5005524104540840454096410207001643d44400401422001e0182554012841e200d8070706410304441045c03080e001603a0b801805003509031b10740410000070b802c0c06440c00c1c20001c0704000024410005100628400b48284c44a48840e13207440704026800c0c0006042c0c2d8000c0108208001c000f034a8410300c1584030390310a0005040342c44200700d076010511000185c1c0459840c180c02c1a08000c80f85000e0002c0b50011181440980e8071000300ca500c4440c00c0d030300d203500b203040c60005100040c0580701130804201c40c00c0000400603680c4000405441c1021002d4544030f03042099101035080c14000c1a0703205500382424800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 10095699 1250 10094449 10094471
    0x30e070803030c12040204060302060f090906041e020f0904090308040c0f060e061303020303040609092702060c01110319050f090d03020a050702040501080d020d020607020a060509030714010b030f01 87
    0x120303c0b40480c41301c8041c03c42d0700094115034580d4403110103907802030109610786250f07204a011650002d04994420200180003504034941406840310180001030102e204034020041c400c0070350060980c8400c0b8180901038906561240d1007131500c4540250b03100c08482c1007038103000f00d162500b0780042d040003505000601c049034002804041d400403d49403d0703905c600071148000d42d05440d4000a45c58000040c002801030b0380940031006607406528104640302203004212900284002c0b00c02c6003440c0034489001500d0b010014203001c1d8044000483c0440612109143c180d0084401070000b561001a8400c1c00042e44101540250301000c40001b50600c3c1c020740f039503122030100960405d5000209540c0c0b440c41001501c10560b03002d40309108c903585414049843e8942030340d080005104800041e242c4610003d1360301d00500d0290040d29040446807142c40c0039050080c4501241d110400c91040042e01291242284ac00c000c0c0000401103200780402d41004241c00705400c560303040c880c2240d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 10096949 1250 10095699 10095721
    0x9020904030807230301080111040e0c0309070306050106080a0b01020c010806040f021e0a0f020d052203050d0c020a2c090a0804060c0b0105061801110309030d030e07080303 76
    0xa0881d03094208011103580e41842200c0703581c2410030001501c1004182c8034081000000954140d0b05900000c3c000c1c22242030003012540500d201f4945503c40d1a0040b986a1000b50020f60304909c0040c242d5410b15101d496a106862083e40300c2000903004204000705001244508098203009201030640d4080d81d40c0001c0000070003070004d501c03da640d41504030303e00340310b58102c443d046401402c00031010101c496001d410f070490400b1400ac5a141e0403800001c1e440030401c2203407806c1c2ea4641604080c404801d40500c5890b15180000391400803030040080b88003040502620410f81d692240600840c2c8140904240186c1c0071507074007025104a1613aa81002d09804a009510b6202000b42c0d40c51100062405001040207060301d0b40010700401e4070f035400b1040790b107140d014070340b80103c6917030b1030b000c0c00010721810380c9a52140b0f10000008450758412040c60492007000000c0b00c1c1042c2d200030000e0f041940c3c4100c0c0c8000b20fa42c504003010000c1007402242d006240c9040a9400c0d4a07203641d10300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 10098199 1250 10096949 10096951
    0x16090203040f0209060a090c020c0301061a040b0904020409020d1a10020a030c02030123010602070614070803100b0409020c010b0d050a0f030207080105010603050906090a020f0609010c02040f02040612090209 91
    0x2c0c45604c100d030004000b900c4400e034801c01040e5000081c429004103000203500c03030751741c0081e050082d401c284022507150004051400c3e0120382c2c18903a450540703000161303100e50b04444c070b8086d0f0198003044000780d014031500103040c1c41c0c1080080050b4800c05a00c09000095400845600603000f420004242c1c940102c0da1042054260510394550380e543d20000c0d005012500c01071085020000841d6110211402d210703050314500d408544034a501c490060710503500340d0119800719030f0f003006030f840081c0140b00515000341c1c240140c1c084c029160608250107401540018a5003a808203d05c840d0340424010b0b04559842a540d0342241c0c1e21a4544980310706d0000009000e481081c1c80050405208110090041c0012030080150b540c441000038050071060300c00c0c00d81440f500000c203c4803540424460103407540280440000d069040500c6051703003069a603541800807043c07140e805a202c07030059010703031040c1007c0180c1d95803c002e0040c06d80c2c1c50504102101500e01248000141c50303411280d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 10099449 1250 10098199 10098203
    0x9050f01090e0a09020d06090501050f0a05010b040605070317010801022508040b0306010c050a03020706030e030a120e01230108010606080c03190209040212011403030a021c030b090916090203040f 86
    0x13080d540014004160300241a00000b080946010703180410f2000640c0400d0064020301c120350101d031124902481a0782c400c3c020301380d50300f03000c000c10010640204010901c0b107219040c8040b01e10195202c034458550243c0c055100c60750001801151509610050600300d21480c01581005006464031607a600072401071550114001000c0b170342ca40c1c00340d044280840d60000c11103034805d0b401d140c002e45400291041c800400d083c903c0030707200160003000740c400014441d9511a02c101c01852180b001d00f00c011183c01c640d5607952115500c0d003115100c96143c0341900b80300151154900b1024508461a0354030140411248406000d044200f02c1d0450f50803151612204e046280c8005000000b0720554019640c424800552400350940c658103140c122003ca00d51028030702c0000c028148c903440780c2041c2c2001a000b051007110800804128400910380c94a8002890155400418800c0e40d041e0b52502c1c1c103612803001320384041c0903050303004098641c80c01c0541c1181459075440c06804020800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 10100699 1250 10099449 10099451
    0xd02030a120b03030909010308070c0b070201050a030f060503070308070510091502070c0e0103060b010206070807020304051512010609090b03070605030c030a0905030412020108060d02090609070215010609050f01090e0a 96
    0xb800303a6040044d9800c02c00c00403c1c0711450b503540e10300300c0b10700e5006083c115111807404000103803252001058400464042c2c494a1502c50950402c400038400380305e11241481c0e03281408141a00c082101c3c00c051403107400c1d0f240d40ca652504200e45465801c0806603100c1c1d0401140c5400101345140c0131040f80011000541c817a9110301d040001c00741950015a9018a8407000200b408481e070000c42c0b400000303030242c3d1150b8481001c01c64110104440c041c0151303004000801c1281032103984c03040072000d10781c8200e04006950500b01c00c1030200303030f01c50300010724040010b0190080f18890108010000c40c020403003680f8040018101c0e000081032060b5542011000980e4000c182c0c1055000340d40c4141629507a5849211030655410085030990003c2c000c140010b61504100544085440e0000c207140065070700d910802a00c80780040240046000d203803802c5070035141c0031055a01034009515640d030703480d080c2810302405c5406001c0140c100001c0310400c2080c0301ca80b040c1c0d00c0d000a00c03284 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 10101949 1250 10100699 10100711
    0x4060f0501020c0d0c0b0a09060f020115050d020103060302061303120507050a03030c0c020a06020d12020c0604060c050c0313060f0503070f0e0402091c0c170706050a0306051c02030d02030a12 84
    0xc03d401096141d900240365904005005441698007020103420307101c003a10341401c00306c1403071010cc3c00c07560080b001290044c0c61030402d014528024100300c3c0664814074000c16190f48aa01041090f0418a403024011140600070300800860211074165258a80b61040c01c11010344c880f581e4801ca0160041c0c1419038031414180c00f0380c031402100881d1034002e4551000d01c0d580b000000c0d40d41c80d02c010890300003841040036184076140c40c02102c1c80725490701c0040c4000c1e2969201c04000b001c1e0419000240b00040200c000d000b03105101901110f501c3c1c20314482c0603860401d0280404c0c0c4100e10110800800b00b04000c3c4103a00100300c4a824030403403400118415001002c18001d100b01401c2603070007003a0410484400c08508070911045200300c820001c400d9990b10a22101141c0c940000f40030f800862007800080c2c445d601416045d01945404164103a032000420381c0034010342403103560301303800e0b417a03c41c1581020000d8440380d002510085103046440c440040070501203483c40f8400326143c907 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 10103199 1250 10101949 10101953
    0x61401080d1403251814010207030206030c070209040b0601140306010518010219080d0606020c0d081e030108060406150503120c011b02030429030c0d060b041404060f0501020c0d 78
    0x981200210401049000401031440c04c001e000c0c0781504014020304918910b000c985c0d2208811042c0041e241070f001040003d04540c04c201150f0001845941c2c0130074240182d04c050390b07640c4126030107a03004e100a80c3c01070615200040003200350f0318161941074410001c0c428140d0b8003004071188814044022042c1007081e00040303080540c0d5405038074030300d01e10300800030500082d0002000104016601040350030781d180f0090343c44182c40c1300c400342e00c60340d4400d943c0b012030b495900510540d00221101c0c040703e4007140185040350000c0c2c019003095403286040100700500e0340318084032030307000e003040b0701c0a5840c050000781c2d030310b070489086001004086007200440000b50450491110084614440034100400096403900725200e07144802805421040030903d03aa0000d5180b00142c3e08038034550b41c0c690b461000c00d50b001c044964400b03607070303000c000443c8081080500050505001c00c80d003032a11000800003692007a401500004149a40801c55a80c00048902a110086d10180d00700c0400d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 10104449 1250 10103199 10103221
    0xf0b0d060503010218010207050d02010206071110020f071104090c120501020f0a02010c080a0e15040519030504061103041401030504050a060c02030d0516020a03050c0307060207061401080d1403 85
    0x10341c0200d8056001240c0640a20700096030f5004401003a800c90f00750690b120b04200d1803284101c0003a002d40c00280200b0b082d588600b280ca0140301c074400c200d512040035001540200da20013201c0c4114030f400441c40c44200b211424181c074030450308490030b00481419480741801042d0510500c40a03418418040c0200704081d01a40c203080c80180322107031100d13101500a406025076a080340006078494000594800c0d4903c103130b01d1003a455000504100500101c00c124105015105640700c0c0719910842004102e03408501c82407510036501d042d00c0d149449000341101c0c2d03455000141a800502080c0403029540c03d0060b003041302403a001c00c041d140ca04204d070414545078130107042c003410004c1000c25213400100402885904420420455854100c2c140e944041d01c443c1c240103812400c03695020912410142288900ca10141c91800c00965180b00c100d9000c0c4a044032225150b15420071625a0000014010f01680c4040c24410401400c010462092040480440031011000c21045404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 10105699 1250 10104449 10104461
    0x40215030709180f05070f02030703140903010e010f0f0c1d1503070309050c120a12030f020a0903170310060302070602040f080a0c09150b1b0105071206080105010f0b0d 74
    0x540855408074803000e500150142c59803d4082045500f4000818546e51181c00c0c0b02924030000e5002c0c600b0050349039011038504040428180c46d440c8103100041660b5020b104140050b03d142d000004c0050030841e5a0058130700d0311a0400415140142c5250f2040e080426071015000385450300e28600207030400150380802150008030804008800c200d00075405620440c1c100c0d000d0002c03650803000c3d003000c1252503480308080030400c2e0412000000040d980b0042c12040c4002410f0203c1d50141c11300605049070411a45a80021128581007041c000d090f0021700300a15440d1206203103140c82c038401122100c552191400301540042c02ca01484050740c16a4042c15021460101050b86c882e1855920394800d8020703621071901540008102c00c180c400c50f028030780483c1a14031014540700400005800003210501c4a0b0120110390b40181020310503984682080c0c0c40e1114031214030581031007100d4503500102216032400ac010b0140c00072140c9080211400c80c102c1039a1069100c0280020340b00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 10106949 1250 10105699 10105709
    0x30f120604020705070f0303080f04021302030405100203070c0b060a030803071103070210030507110607080105010e011101050f0f0106050c03040302040209011101050106051b01021c020a09030f0c090b09040215030709 95
    0x1d4100041803486c031005607241100e0081e0344203503003034984100c000705144050320001d51056000e030300c40c400031401d1f8020f560f110f4000c84c1641d4040681c1a10202a41d00807078140000828500c6000200700b61209480d42200040c0da0f2040c4480c21030b540c2000c03d1102601150600204071014030f1107100c00c004840501c1d50142c0624100b00f01c007080580906400d46040011030881501041c8102c00026814810186955801c0f016480c29006440c500c240f6582d0504003c0c02032905038061009004031401386525400010107407812075842ea000010680000c002c101080003c8964400000192400e072501201c006a90300c10400044e2403d1003107050b1182594204000011801c0c0c006002d400407070000c141102607100c440c0c640b50b02701d00c1045a0840900a0340401c0003c5801c140c1c05001049020704000c1c2c0c41d2501c130745030311102400030352049840144042044c89a034241d4091300c3c48421b8213031401a000d081c5680050608100c1031001e030f01c0c2c020b02000240b591485400d030000108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 10108199 1250 10106949 10106953
    0x40c15050913020703020c041d0604050705010f05030103030f05032d0103020420040b09030106052107050d120807021e07050301050c040b070b04020d02040e010203090708030f120604020705 83
    0x110411601818941000311018820254500038060032149070003200c841c0d603490780c06000c07000d031101d0820004161641c000b420307000c0d130385d44c840c035150508000c804e005502400003400114500800140f0100c0b0740310f548002c219080c00104002504001e025002030b20a0410f103490317507202c1c0e03840500b81001114045441000d266503184c01030040b20740324162402a142805100322403030401c20b200032040090011a01c007008200001c2411402078100183d005001250066a5a0008402d9a1148002084100071060390280070700108041c00c014002940c95200c0301225032200300c00d40d610001c0c18018080400002490307a0310074440c145039a5154072035072401c00180040c1c0303030355400c8074028140250301c1e0402041015500500740c40031207000369a910b141007060303a115180140080c0c403c0741c00809079007031900103a9407030003140c00100da048001600d81c90540f030084c0c9441c0b01a40423a455070010458810320b2a00101100d00c4080076800c061156207801c00407070005d00c03429001400034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 10109449 1250 10108199 10108229
    0x5090a030b07020c0a1809060204080115060912080403120c0b0c040f0b0903031b0f06040b06031608060604020c0a05060406020a0f02010c0504090b030102090d0606050a090905030304020108040c 85
    0x405410401c81c0501d920341c2c2201c0c00c4403040300510001c50503500034030348400c6203140e18508240282e003000b010340c1d11421000d414266903280300c40c00d6501120901c2c00010030070005208a980c0528104010301c22a4500c030400401502ca44045e489280800380c069800411421000c0b40500c500015065100b1962003031440e11450424a46e00107018212451448110000b420808075080d81d41d0803d0040245290a01000450040b5a010100000300f4014603161700000242841058403943c02180a42c0c654905035080505041c881614032001c140d104500f4444008000786459012106a400507500c50503098684e01d400c10380403005016100d80c0c01041304000158015000c80403250701c58082c010070300c0c1001ea003030b60781ca0100c040006106020800105095411810a41d030307000c0e0005103802c05810115401d811f603944246c071813680361320082001d4101122104010100c0c003000b041114041d503642d035201d12026202a04120452010a091000c1c04c1c11010040401a00c100c9031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 10110699 1250 10109449 10109453
    0x61b02010c030b0a0f0608090a0b07030506010f1704020f0f120307060b1e010302070303060e1005010f0302070c030b04020102011805010506030705010903020d120302040810020c0d0c08040905040305090a03 90
    0x1e011081d0094001a04200d100034150802ca600781003520128070714000e03114200501251000c0c0e00520080c107901c43c02d6004008901000d602c18003c40c1d003558045224542a000034184061041600c410000806c0d001900c07581110700310380c0c206904407002e01c050f0440c2c8002980c0030500075092680f100d401c0b2000b645030f9200000411403144201c0041c04121040300c108040251b0005906042402c0151144a150309c241d000700b400c980b007400c0c005403540e102c0508640d050412210302a4034200742509000c213607001445651480000d15003903161003900d5a5400001c41e0510000b440c0981c007101040c2168000e41000700c2d5802c1c0401c0c54001380805080081c080e200c01d584640c06800303166000b2400f5442612620b041d00c2d0003900d0756001041680e02c4040c2c810383c269010003015800d100104d0106810b1240d0101c1c959030309d0016071503130140038a05080071101c3d820a0280000c1d0410a000240054103560480391150400192f035511801c0940d82445440e0426078080385080d800300c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 10111949 1250 10110699 10110701
    0x30507111605040e010b0108071220070c0b03010503070302040b04060b0a09090e071202060d0b060a0203120903040303090b0a14040902040305010507031509150801051e07020307120309061b0201 85
    0x100d902c1100d0900010240c000c002e405c81e0320940f00c040c0019610000210401c0c02800f0710003083c007098030002003502000584200071030030f00740300d0260380c200060303180148000d41072168054080310760741600d5549044000b0f96a1070b0b107031000034056a01c03002950115030703407a80560020400f0600c41907640e251184014403100d00350140c1c64107246003100c0003100401c0095a001901d450750503100a0300115020010281c005a40c40c01318242c54454000d26070f00e468014040074401c0707800442c0c0f034555003907040f100301030011b2100d016a0310600040010940c00541c40085556404443c0d54070300c8940e80c00c543c203e030500d1032000301036400100001e80e482c441e80288116030260000708501e40700d00078200c5c15118001e007103103c5002116000d01500c205036000c1c0c0e01944000e00144c03080d50380d0750001400d54004a50881040250b8044004040018400940d00003004d10240d46041e00323560342d4086880c00d1111303081c02c04d6a0384c20360508010302684003e1251103070711241002d8180d1250024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 10113199 1250 10111949 10111993
    0x60a050106020706020303040b0601080a0b0d0308062e08040302100908120105010302070b010510021e01090c060206040c060e040b03031210090b1305060f0604080106050108010e0903030703050711 86
    0x780040c80342c1c500004520b4404803d4a000384d501049040d66922104011501e42e003001d880302803000d0b5201902c81080d516460300501080c4681c80e002403500d040810045101e0001e00505202e04020040c200302c0d60799140f46100e41c00f000d0812001588407400c0c00c903d4046508441c0c03165500d050718820a02480d100034048421f0032001884e00c0340e888100460070b80c02460401001c2184c030340010b1003130b03240c80600b00400c00708910484510f1407810100b0480f04400d4140c41d44a41d540e002404203100c640008400034040c0d40c001000c8904041d6030302404202180310b041c0c00c0241404e240449540c1d0354014403440b07140102100d85031035050184903140700c015036801c4e206038501c9000042201d014090a05050001045421b1805030310303102e08080c2c035009040070341c030403030038500385000d9510310001e000505a420000111541421b00141001c0e406030030005003130005c0b104015082c0000002c0301e51109041c40d02060b1903d60150075111081c2c0404032080d01e0068010600b50306075009051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 10114449 1250 10113199 10113209
    0xb0103050304081605010219111302031603020408060703050618010806100609050a09090204020f04170607030b130902150a05130f050306130c03050109031215051c020103020408060a0501 82
    0x240b15200303030320f130b01034040044103214040c05604042002040601028602d8011034011501c0114070750310900016500314040003d18010756020003070080c024100e22403801000f6040c00d0841c030f0241001d00c0180d41c0c0400500f51403c158450b400146c0326143c0c0000050040903c20300310300596124028103440c1e180841e04003050b03030400ac1c00021203e1040c2d850300120344000e04051101c5052440350030207012700520a0b44c00039001c20103204607500190041c0000d144042c0c4007800e801160818a00300389000c0d00316001c05003030100c0e6a6081e03039010f64001081d03080600006000c1031034408210126800c142e0087d4868010a4155032035030090004c00f501e5540012101c1c0d01501c07442000300500040c004c0c250181c1c491030000c2c0024040e030b210388401e41d015881c0c0c000600d5407a9a6242950039041e02180021410048904403841e18050011148a20240c241c6e489040a01080d0031500340d04810541041c11468039046d64025411507001d041e07200241c80c41464030ba242c26000c0d01e170030700c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 10115699 1250 10114449 10114453
    0x607050a03050a0b0a1503020c030c0109020a091a060d0f09030f0906090b071101020f1209090f130b0705070c030f030e0306010f0e0601050408010c03090b0903041d040503070b010305030408 83
    0x3c2c40407010f6114513503407080000c141d520501c1c01c01204481c0d800040a680c1c051640c2000801d045a00c10005030000344007403030002c50040303c5441445020081c6502074005242072140080c4100f0a00c1c18002081c0000e40d801034a03419103c880401600b00c0001e50407900745400d82d102c00b03059201101102d26a001e0f00c55200384c1e940c1c1d001c104e4004150380304040c00c601d41400207100041c6030b0724811a54010501c1201c44c030b600604421802c16911700d00c0302420800c0000c0d020854201180350a5201c4244406450b41c0d2603d0002204000e50126000344124011030000315100c1c064070585034400e40004411810544034904286c07d403000160540110b9501c4000d08418980000d409040e01c0100e542c02400f20700c0d02800566610b0040d0040c1e0500c4014000403e541c0024450781181d00400e90303010840c005a401c00360301440c030161440700a0341042000f03101407400d8001c020199050009084550340d1036090050660041030f0005010301000c0c4000000e000c0c0000c0540700b40d0307107a801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 10116949 1250 10115699 10115701
    0x1b030905011a01020a020f010c0b09060106030f0207030f12060f031b0b09060a0f0203090909030306010909020f090f040905010c0903110303040302010e0108070309140d110c0901030b090705030607050a0305 90
    0x9000c0d4101000b05003080c01640401d810070b00608005400000002040c1400218078145a65000005000f1200c68141740e00c0040108403203030340350003800c1c480021a1000c5103071440300d4500900d000594030501e024403005980e070b440b40045951007a0000c0010180040c0225203924000032440240d040e01c03084400d1040300400d045030000d080702d28510000b001d90b40b401c01b520078140da0120030786114105500040c09400e090351107481c0a5031040d15800055a5640781c00c0b40050120760690300514042c070b1040c4404142c111005003100e040300030486410507a1111100040e01600e60003000908650805101030707402500910b040c0e046d02e00c2030306000081000c98051681d24000e502c0003038000795001c0030051095005031031164001d08a8038010400d21001d0b12140c40711180c01c0302100c5250300c40120200d00c5540003181b00d59468180c0c025041548140c00000d00108041c000070744000c100ca03004c6010b4840c1086090010130000e01034901c00e140c00751000e00290080c034084004030742048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 10118199 1250 10116949 10116971
    0x3010e01060302030106050603010f030f08070f1a09120d150308070303020406080c12060609040e16140108040503030703020c03070b0f0103110904020108070302210c040501030c050a080c07061b03090501 89
    0x3d41072703034180c50240c049940c1c01881c6407505025000c04200070b45000000b080504081415103000000030b60207614505660340680b9502040c01400070a40042c43d004800c0d031001241d4080200c0b015080c42d1030002c295421400600641003030303a6071004003414000205201055010b401906c1159100d44030742009070341b00040213050340b0940c0021200e081d50100000d44a01d005c0b40a00642071000e003000441c00c84c000501c6242120309900d00b042404030410400c540460907403c640c24680038a8032030b000b42442ea0b00e02d07231b480c0009065081410b030003081c1d2001c140d0b020825213403c03540100e001411800d140c5421000b0101c2030100303551620980d072180105062417408240204e906949461036a0f8801008400070740015640081002c0d81001100e0003c190b031802900070408141c0095803146004000740845070545a080e0a001c0248031840d8256040340080d5070290040740f100b41c2d160b841d403800388010b021841c08101c500207200301c3d02044560607400b1040c070030f1103400208a040320603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 10119449 1250 10118199 10118209
    0xd0b060102010e3f07020402030705040b07050f0c0102030c03040e090a200a06110a06050c04050a060801140103270302030409050106030507020c0a1401030b040e0f03070c0e07052703010e0106030203010605 90
    0x50403101c14108040000704010701f8145e0045034000c0300c0d03181c030b81c3c1040e13290f000070815a0300c03c06090b076513640480c400b108000c00a00441c11086401d000540c6090541030b1600d440380a18403071030250a0072100011f1804505201144a290740040900b0140700108200039100d000c0c520300c1401001000c201140407800360811100d41201d2070b0082104907250ba451300701400c00100179041000050200044a0711600c1204c006030205031501e0305190304140348031088802c600e0445040609040c41410b550210b0019024486072405401c10000c0003424140e20354030803503101c01442441c001c000a8500e516500480c0a04495030030348020600351001c0040705d942da8091080f10030004070101c0000d40c081c0e4800e000c0400050008540106100300007424001f030310000c00c0840d04001080410004c1032107402001c3c0400d0780c1410064141010000c10600400c20b4068007540c00d1011411198042c1000008c0120020000d01c00082800d205c3c44c060220703448124065030030300b80c01003001c2c641 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 10120699 1250 10119449 10119553
    0x30201090b090102010e0d0e0f0d020f0907031104090603020f0102070e010603020c0708070b040e01090504030509091305070807090e030306060306010c080c03030703050f0705090d0b060102010e 85
    0x50395451055810140c4001440e80000c82c03841c1991750303450340d03100c0550051049400802590312200f0200c50384100380b112003000d0032034480c440c080c440305460040c0e8039071054500403002950924295611108240c000340000d00122a061002040004001813560000c000762403083d039000118084003401a0303650b000d0303405154603140c0c1c0b5500602940d40700358040c201c400c1c42c0300304846880384d4580f04182002031941044449000004d01030015030303070010002d4010941310703c0c00c0145203402c4d200104240900134100d4450341a40d004507106c1e09103105010011070304041510303500f941e521842d039a9032a40344900e1007903506054810f15584000700942e84078180203040035203165242001121071540900048130341c00c005110002c8005020000f56110304503640700000c032428580034010701c00307000501c04010804108851032861b241c0660034500b6039804410b42034640c8550700144d003d4131340006500d41d94882c65868195000558596051038527508202031050702c090500e02da21a12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 10121949 1250 10120699 10120703
    0x612020a090507200601080d110601030f03050d0f05041509020102060f061504060c11040902030309150c190b070206060105070f1b0303020c0301050a052701060b0c0f0105090703 78
    0x9090040095a40c25042160b0083d11031510f0000c0040e0720800c076041d0b052100000040750700c0000140700303080d0200051a07410356282483d48602400400c0760340e0b250414040140f4403141c01030300f20300300360144c01036407088604c0ea80d0900802c00c403040c009004110845050b5501a001e00f07218071003080c40e100700056030781c0682c007602a694074014001501907000e011541c001c00d5101c0d00c801c185500902400103000d1540c3c80c9500d080b0f0504182d0b02c40f401440129214034548803e40b00107035400002c840c0e500368250b074926081e034140300342c0c41106e001301003c040441c0507599407002c019008a50070741c400c80c1705044e50350301a240c216007240d03905800c98405020a00c00c00061000c50451505140c1c0f9a104907599100300d00c62a82c000324402c525401100981d21294202d032413494280a140d6100c140c07c0701c104528581590b10a000309030300c11182d504000401c44611625038203400940141c20003403003280da0b401180045598039445010b034004a5485c00c400704642c1d82000c00c1000c207d035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 10123199 1250 10121949 10121959
    0x90f0b010311040e0915090f0708060c04050418050f010603060f020306010c080313050d1205070806030309010509010e04050403050903070e0105010c0b0601020c030a060e0106050a0807030f2310061202 88
    0x15042c9413400200c9034018184641d18072500490b0f1001c03918141c50346104a42c5030002e031910666031460708e440c00e0792039045007040b0b0b0001d4040146414400c8181ca0484004542c085100204010464030440c540b41d4064074a0054849a00d1141815089a03080300d12400c0200088002d80d505a8120300060300c0040c0041c50906600c4081748001d00510303040480c80e4201c501300e020983d01c00d850880c2400300e00380450754902d003060300c4000510425078024201c0c00c1400d00b80c500200080d459110b4013075841d0602c00017141017102c603481250807481d1070101600803c254201030402800a80124240300c1c443d204560b0089030440703410713510504032181a11402c07078161013550b50001101001b04181e0441c8507900d20851f1903a0100000105c20f070140400040c010420305005094995079004280102e0110400301300825001881100312904685003030b0749424103280a43c0e81e404180c3c010f00585001c0c0040d1310f0f01c100c0106500c2c81c8641c041c9010001903941d02c0c041c079040d070300c00300000c1c0d404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 10124449 1250 10123199 10123207
    0x312040308091512010303030b01080903030601080106110703050f0307020a0b040303020712020f060d0902011d060f0d02041a04080c010801180b0a0801020c100c090803030c09010203090604090f0b010311 89
    0x3814007583d6503007000b104900040c2803036444070044407012001d0788141d0000b40c4a4500c0c501550f008503840f42c02260403000385185d49450030029010748011312601c01040b82d044202112004d05001520145a004044c1ca50706d00e40454901e0b902d030014901a48030f003e01c06000a4005220400c0b581165032540103400c4080c98080440c00c004004035040c0d803c01d4008400c00d00a68469004108e280540c2100040c490124000100315562009944030400019299000140d40303040c1610081210848180e6032045841007140c080c2c0201d0740704100d18000d0f80c03511400c214040025000380c0d45602c003154000900c4600440d40c0f00407c0c03092442081401d030a6240750303010350b003120382c4032540a0800800e1581e140c0d001130072030f0310541e8000b000740c205049040c4140b1041c000d82c0306094a905c0d05111081c1032000c07440c2c582c8805040d50b02c0d04c1c400080c3c600900e07402071003a59080e0b80e005101ca40c540b56180c540d00054a2400c00c03142d942450308080a440d0f40c02413040c1c0c2070004500c8041828 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 10125699 1250 10124449 10124467
    0x7060f08010b03090109020406060810090203130807020a05030109030801170105070504030201052803020405130b030607080406090206030103030302030108010c1e0f020718020403030206150612040f0c0308090312040308 96
    0x185030f0001d080039540b55254a00c503000340e121030003040d00409040c1c1ea01110307803a080304813034524440340c1c015105041c0100144080b501c3c0d08403241790710a4000506a6540050b44001140040307658403564040d42081448410305800507000c5040b25011280080004c00361104a400c8403012181c40001c920b0a00041c07000d075205601606000d07030700e4607080b889450044460342460040d002ea0301c0020746c0005061019040c03400315941910345812080c84251204000a516400c000b4031203800c21040600107030074860150031000100e50040c14195907561070f8200140030b54801d00680d0102e609040c41d420601e882940c0b1007136401e0403d003103161035001400080321601c0900d20030078118450140041100c1610b02001c04198202c220010b90f114a1881c0203418000014007000080e25492181d040c180c40e143c00b140c078101c01c0700d100a03980d1394480c03503c14010b5a00020260020300c44103400700c1000080300040c5070b111412002c071543c03803039021984078403440340d4040141440d00034000c00790 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 10126949 1250 10125699 10125719
    0x1a0418020c1b180109050711030c03090108040203030d091a0108060f1b0f040f090605090c03010b03060411030f04020102060c07031409060403050d090f0501030905030712030e03180307060f0801 85
    0x1100070030040042e2420701d0b20503810711030070000385c00018165a42d4010300c45142e4101850051242c4160080e60a0400800201d6200c2c0030b1048000c2c140428440014210b540c03e00488803042e400c054100034240407808c04030100a0000c655100d06842000089110720000524510902ca04140d00308207a0720700c40801c803040c000a04c40350002c41d040c0700326014041240040c102030400c2e8111a10001d190003403510543e400c651080d4001c0012000f4050400c600c04102e80c1035030400c14070741c2d59030703125040403c2c02808081c0c820102d18902200340900078504405850081c2d000340c0c00c40e2a242c4504035000d4003841242030090109000400242c81c0c03001d01c82c05843d0700c4030010090317800c00d0307a0b0752900c50820301030380c00c02000160f10300020702c400c0c0c00d031450380c03c09032500b8602004840c030140d607244da40b80704040000e005c2102800114407010311a40010544c42c1034141680d845400802c0b8882103031041850081c800e000b003202c086589486030000c2c1036014029a198442d076460401084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 10128199 1250 10126949 10126993
    0x80a0e0c0f0301020d090305090a17060a090f0209070818190209040501060b04120302060a0603080d0f060512010c030f0507020d18050415080d090305030f0904061a0418020c 76
    0x20b030555000d0120752031180310340c802d041301c00e40030b074940c203560381170b0007040202800c0315402160640d592011a0496650300261141e40322030301d1080000c4800c242d0900303003814545010001d6020881d01c0400c5841c5500c244c800340070300f86100100c50014000b04610380c41e11a40f0340070701002c1d207024030b091000d03107015241d90350068054000092a90345a04481403694000d0300050342030f014403014001015410000d55501c600309641c108006410350351410540d1207003603805034400352960b02d052882c004541c022002031100618a0403601d0440400718040c114014454001c03d2038100344210501107409000e12035031095024028107040b00341d040d10b0701100c050049568000d41c02e00401c142d00d036445407151014a054100c006903182c00c00341403500c9651001003080100c0c03180100001840002a0b075410054032004586425080000c14010301c003c1d84031700d52071100b90194019036040c01000304155104c4003500004402201c51107030a038803034aa0441e445a102104003414400180380072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 10129449 1250 10128199 10128229
    0x30504051011090907050c070e130602071407030302010b030c0607020603010b130305030c06061203130e0c07050a0803090105060a08070506160b0403031508070e0604020306031c030b01080a0e0c 85
    0x5a814030043c2400f0580281c01154048041100010f01980c01c0380108020801050118542d01b40c526002060340142c19020500400054005c1882ca04020301840b54800010f03199045500305940c9007002030207004010781040c040d00418040d000039040c50f0040f5817547e40c018000d58916440c20004c5231880c0d0144030742541004607410080b00180c810310003001104552030080195007001c004000e00300100340c3d1310401503070041041c000d030401000325200c1101e0214840740307001e554645403100300d48907140c00182030707000b1105c80304200700783c190140d0302500180c0d0081115a940f0380c20301c55104914022544d650380107120400c010720303000b001004d9031845c0300b00742c0203803100c0c3c0d60301d040701000143c5040380400d41b5402c44440184403604075038001d20405000307002881c68541207813003542c03014080600554000001800c1600c00b000a06c041c04280010f4a1480384d05000040003420b20b1a2083e0003c4e50b4038010414603c56400354108884000c4081c2c54861400c900300100c140074201e032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 10130699 1250 10129449 10129481
    0x91506071101091805041a040f0201030b010e150318010c02070e04020102070506070609030e010810060804021504030503040f050f0604180902100207090b040c080c070804080102030c0405010e010305040510 90
    0x810054011000c213402030300001004a814103243c9000c0f010500c0c01d0b5205012110034504101c0842d503030041c0d04039a2a0203080005001d26007400485086000e0301426070016403d401c90503000d80941d0081d0709c80d01e0f0000355482441c0c14151054207a400c4c013101c0200582c081e10003030110078600500c1940251050048810850b512004160a5003041c1c005684080d03484604400741904000400a41902481c000c8880c0c40c024a42d03102c81e800ca40210b104014003640010119141c018484000c032070000483c98a8507501c3c90415541d60113809650400c4649540c00074503070510440d01001c541005000504117805c0c200c69000c00308100e07003c1440c0503141c4200300c000d6150118444080c42c2c2c150301401c0c641e03040c00410700c03d40b00030000c540d000e24a82840c01c220386510405041d081089441050f554142900300940c0c6409150401e005951000082c008410b21201c0100110751083c0c803001d500e00c602170019021114204c501829a1700136050f0b007180070300150712190f60a544105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 10131949 1250 10130699 10130717
    0x100c0206010314010e0a1a060108040b010b07050c03060c04210206030a0c05091305010816030515060d0605010909030f080f0606030604020f0304060f06050a08071806050d0c05091506071101 83
    0x30345420100c05054442d035015032041150102c2c7d0000c103540c440790a003000b105609140c1e54204501a05105804484102007049002c00c8010700c484030341148010120340060400f12030005940c6c0c42440b402c0f007454012000501003c0c10400300e650940e40061103a4110350b01c2d250703104043c0200f02041404c00a041100c00d0040d07680401103542e00444610005084d810120500e00d01b09040100d82000e0081042c2040085e4000a490b40b10514542e0f2460554682c4030100f00c10003820103009004c2828040045200070155000380740842c026038411303010351004130f4180c0e000e2605403601c4003403c60020000b0118100000115000440540010f140504d412400740140d0810341d4100e94541d11000320800d6100b0901462014000031203004100e6440c01100d5030b035888107407182010100058105200200321584240300806020302440032000b55071801001d0410b440c002c1604c54004100440c51851081c610f64001000140ca140d14000d03480c1c40d61081d10188180d00340c10010340c54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 10133199 1250 10131949 10131971
    0x3020309370806060103020c03040b07020f06040e040b180c01030c02031303060f05100510080402011e020102121f0303050702030a0c0e150312040603090f0b01120203100c020601031401 81
    0x4030308601e0001201c03a484500307140805040441c058501da04050041c841c80048540110071203041b00d00c81181a40e941e1003610118102c542c101002c0c2c0d81c406008a0002000d01c1e0390000d50388103a104800c0d03021789035070705070303070010509100c048240a503404101003560039402513005044000342801185c0c10008664080282074001e07030011205503441e1108100002e107107010b00d90704406c0703044403004000c2c01c050101e100840084400020010f0f00004074055900500d210310300342c3c60b038440c030b003c0c0c1080b007440190113540030301d01b00e840010b00200001c68814001d118900c2c60400100e42895140c0b41d51030481c0c05400c0180142d9150040b101942c0000380c080950f1070003000c410024044614000214004070514030740f4960180d0000d02e80c5441c041688001c50702030303903841e089c0010b0b0614113040000c42c21811038401800311800c200046000e050507600662441e00c200d00300c40c114a80c00d1540000c0e2807110390a0000740e408140180000360b40101c0703c200400c020000013410070445 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 10134449 1250 10133199 10133269
    0x15140307020703020102011505090c0a0e04090614060901050303090105070614160906140415050705010e010f0e0106030b1501180b0706050903031b1b070e06040b0d03020309 76
    0x980c0c4950141e03010710810070031541c0a0244241210702c06440024091400c00414680d480003052140c40401c00070f6803102c1d4a0050050107800308010b04100b04076820b5103483d0000700040c2003500d41d4400e032600003c1003458003030030107816140082d020b1030900350140015502608800c0d070445003140c40e2082e20f00c0c1e014403922428858241c6402400c40f00302030301400350407055140c01540801c10b8402003c010344201ca802c840468101007111000c1034640202142e40b40a070740b41c000d005500300030480044410540064041c182411b000b00862640019643d0880d0750a03c0014400724540300020010060440381805008040c181020a0b0340410314001d06040c0b01d40016448200110781d02d4144595403042c0d584c41180340004614504011104104400075480d00641d010400034003c0401c1103130313049611141914204840c45183ca5600800f8540021251240038504d0805591054a0000e545510031030301900070f540f911020505001003402139054405095100041440c94040b413 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 10135699 1250 10134449 10134451
    0x603010e070e2d100501020a0506010510050c030310170109020906090403030204030c030b0114090106170406020c030d05010515090109030b060d0f1a070306050105120a06090504081809010b04151403 87
    0x89401c0b041443d00d0454070462069001c5e4100c00d045500188003131002800000390700d415910221042c2400710501c0c2c00403205031151101201c85800040140018205200c80c0182074613900344030040d503040b48007046403c9580c2c07000042e50204007440425042e00704030703107000e41140c024030740585003588a0321000f4001c0c0d00c0307900031500001802e0042142c90032035500c0560500342100d422043c2d5240200060280580e08403000d85070351208046000c2007a00c0c1d040704c0041c2e14005c1a6526100e980885400a00302445040d00032511580311410100380001250301740070058441007a51425522480341c04c0da0002d21880d04004041281400704140261269202c3d1165131040f0322809240c011031030885014240c2001d16040000500c0381d603030002c054611485040021075866992040030f01e02402d8103038840d800b183d10701000d00003405003660081418032a000110342ca28229203060103c80b000034800d5400c0748800b44000d0280703800342a0b100b0b15402c903a14150f0040ca012903100562588 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 10136949 1250 10135699 10135771
    0x31b02060a0c0c060e0f01030509010e010510030203070801020408030406050c03040810050601031802010e060c010b04060602060f1005090712090c0902040801060506030c03060f030f07030302010906050603010e070e 94
    0x210380b41d00703030204955290480003034a82443c00300c4240c2c005c070000c224640d0310212818141600d0302e00068613031109510800304e000106c0c00901440c201200540c154995078002030b8001d018407040403582280500850f0122902d61b0011403600745007940c03c803003a0300408441c0301c0c24003081100080c0b040040011a07010805200000b540e400e1080015003107a808803600001e20012805000c003607a005185c03030855681c2034840b20782d0303204403208240c0104200000307264840c3c584203000c10750f19030029090707100d03c211200701040f64440d030381042071074500d9201c5c03240c1c000726590009803410304c80d88465844da8001b28001c00c40050390b540d0380c106840c09030080d00845901240402c00d01ca03003400380b81c000346000d84d02e2902d1414403820b0b0714040d00c0024500303030080d0400d66240076180c90801100c0d48020b46102130350304594036454000d002e0040c0305420341d012410500841c0b0103180621504280700d0403080100760681c41c00176980195480200074007220b101040700e0311401c0b6040c0c224004006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 10138199 1250 10136949 10136957
    0x203070203130501030b010e04020f070807050307020f030303091b011214150406050901030609050a05030a050705060f060102030307030e030423090109110304080702040b04022206020c0d031b02060a 87
    0x590021080e06004280f640024101070601340e0007040340e60072800400c8510340c15503015070348d003010024411740c42c8910343e4020000c6a00044c000301f80000840a400e20510854651100b1441001003558030300080c2c88504050f00203401565000d003804504007900581810071800d1800090980d01c21902580d85600d240301042e01080b006403080e801c100700240381102e0411040b0705002c0070405c24001400001c04040d9140100b01c107002c000c004003075480c1d900034101c03941c4010301007005100d40c120241c01c07902ca104050100d840c80108401d007602ca220180c0c0110704680d078241048000d4100282c0c480c1c101d000402011841d48024680c140414020f08018100d0303904a2040c84500401640f00b6000785203001546006011100c0440750001d80020310075440b03241c2c03070002400a03c040000b5541c064800075418000035203d1f0448600f552561250780c7c2c15941c0c0e2542a40c032088404006a0b019420740c4138200080c0c0541c58081210340ba03401c58081c45074a560100304e03194090310f10700e0046 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 10139449 1250 10138199 10138207
    0x151a070f02040c0c0308060406081009020402040306020301060507060e1b1c0501060b07020310060b0a12060803040e0405010506010f02030f0d0908030a0516020304060c110d0b04060c090503060c030a18060203070203 94
    0x490307002461547c01070400c0d03d00f041450701d0000c0282c0c5030240503c0d8001617039100ca950009664454042d41c0c051500420300f150340e540e69040292450b445410300710b80250910130070713201c4e803040400c001110404140c1d5444030030300c030700007001171040c03803841d0a85a44645881060200d0403d20915025000030f0741c0d903c0d5690898010103140940203080d407800f0070f0403c1018010070305004180c83c0845000e05180301d0043d080310180340030f04032582018145d17110120300000c02440c0e040546000c3c50040000700030980f80c040045410001d208181c50140c2d10411011b0303051030585004208496030a2030008aa4a441d07031001415841501d145543e40d4403a818407600c0c000204d00420040803a0004600d0949480400742054407050405040504e00c0c0400d0790581d21155840035945500032100100c0e86454607000c00141109421500041c07080c240c003142c90301700015074a0054003c000e80d142940e898000041c05030140022401d820034070316070380c00005400d40c0007550003010942c02a42d11 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 10140699 1250 10139449 10139453
    0xc060f020921070b030403021c020105060f03060609010b0d02070f06020304020f030601030c0504020f0c030304030309030306060905010806120c0315071d090a0e03090a0e040204151a070f02040c0c 86
    0x8440d948a14401000c2c04500c401030001444a044802d0000300d20b44a035120300307007079040c200c10602078a14001d9001120701010ba06500c6144200030480e9010086005101031591f82c0b60202c0c0e002d50044080401030204070a00300151501200e11040503152800c16602c000807503030316040449145402100b844214a4001003101c0018002e0303004122961444d04c1d402d000c1e2642e442070a02071640054008091110001100d210038200003c907590b038145417400078010404082c00783e00081c074002d00420190b00c141159001c8440596070090241c4075a010814941102030208a1034480d14182c0b140c1520107100312285240c492400c4c03101854000e401503c03002e0381041054401001140080c007540d15080341d540c00400010000500401c0d04040900c1d52127400c3c11107038819110400010b80c0011100c0092085209460a2040c01544500060540054014084000344c140508040e901003213015160141c01146031248108480d00801c086070304515281001800640518007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 10141949 1250 10140699 10140709
    0x3060909010903020303150d021806030106061e120f09030903060c090509041e05060a02071a01050303041503060905010e040303051509071808010c020d0206090703050705100c060f0209 81
    0x380c8508064020700c045411650029101d101c0140300b080380710a00200e20301d607500c0d51465007500c1603010301194110b541900041000000031a01c46d88030750700304080030a010344500e41d504051101d45003500070408606005841070000b070700045003001d954003184d5180382604d008100d1460b009032a043d5101e800c5081180c1a110079124001c2885001007080000d521000c181c3c0c0d07440b07038000d00442e0020030712107002100c2140c09070300540944141002d200e20740d42913038010054140311312511001d1000003138038115009408d10a55501d07401c144410030031449407040403541581c8502e00010080e4035204040d080350300a070001404480b85004020800d07070036104240c0c00c0080702000202c0c080d907070360001d20020401070103038080028001e5021808610b140c40a40909203600080c0600880726030b009564400300d000c107000600c21340d00490349000740442eaa8050b1b03034200c4090311155080005021100c10540c0e000e00401038282e945401144485c400d00e40c01011030307003001da031724148201086 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 10143199 1250 10141949 10141951
    0x13060906081204060801050120010504080c1902060a05030903040902160201030f0921030f05040503070506070f0f030506060904150503010617030403020d0201110303070206010e0708090d0806041104060203030609 93
    0xc140b0990801052000341e411040d4241140c4003440d0920010150500c004602c903a803204070035030b56007840309110800003800040c0010010300011220386200d42030b910700c240c1d02a0030000e03400040c200311458001c0d04c00c41c0107560101c60001280d1031b241c0e9440b014001c0341c3c00100c100103058101c10001d0110341e41400f41c0d980c04000c400c41407000d0681c1d501c0d92400c00c0c0340400c80d440c090b2100d09022002c240039402503401003511900400130f600e03003410300b182c4940c0405411a0396009000020b007650707000380c03500c0d5034810680d80c48412406030380b2400e074020500034001980c811000d100341d5485075100e02411018038030324103100441a00c0c00080c942913070225045410401e03813255412405402c0002510b00b00c0ba0101d079080b4010b2000e00050b02c80480c07903400003c0f607020001c200b014080c0c00151a9040b1101c142d0b42100c20b640d400ea040791f420400742d888040baa0005164403610911134840d01d500000024000942084100034000003980158418405a000030041180d82c2c03400048103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 10144449 1250 10143199 10143223
    0x30f0b161403070e030f100204140907020a03030b0a0e0405010903020106050306090d03050c07020406030f0309060302090105040303030c090503030301060207090515030c060f070209070804050c040605010813021306090608 97
    0xc01403030007003095104154003008080d00c04000790420514555601000700628000080003500c1a05081000301c038065031140c040d50704498000300703201d426802c003c81918840c0e400d65000d00900c0300a56011405440107002c51640052424004030b2241111701e420741c0502d22032000081c020340c492030b010f0300b074480381e9101030322130b81104040210003540460604090240c074030300007030325694607110800b06000c3d020300a50410302c1c15801104008501ca04000014040d0f244c40f402c26645200403810fa11032004c0c46800210188803c2000900907002403040f070041e401d00c0843c8a850303074003080c91500240d00c03100050b07002110070019107595100e040d81150070401a009007111602c0030959032500c40543c00d000d2203000030204055000c000944c1c0705554000c1044546003482c91004001203400c0d03c0c10b45080c014500003c0c0245018803a07981202c40607110305650355684004c0090319402814160b0300300b42c3e003000c4080c925290307114003005460301500010382d850034103420301e00c0d0068070554 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 10145699 1250 10144449 10144457
    0x3070f020a050d051c0c20010603031b080c010c02010b0f03060f011a040902040b040303030c05030402150315040e01091209030b0a0b0a0302060c07090e010614040b0a030f0b16 77
    0x210501140003c00c2d03c582e00b80740c0f400c00c1359880b80301d10030705030007200800080e550141ca0a4112014150b0040e400030400c0f40500072088556031040e00f441c01c942d40c902c002004944142070031944140d81c031155491803400f0340c06407424050004500c42c29201180611340041c2d54940d0742002d54a0010302e0000002000e070005c00b40c3d860b0610400450324410f0041c0c401c1040c1400c3e81000b4294008100ca024160403601075444075654480782e00c0d45d4109001c2200421304042c1c40340c0d000c6104800b603901c1203400500d403480c00003000084204990014154581c2c2d88501b40b4114a240c84901424420722001307000002d0152060038905a5006004000010081851020000300728480381150304a2134654002400c80d0302c900c0060303942161039000a411090104170404a880301040c07400455500b8031040c00319890071803209081358617600980f103980001e21301c400300d00d04203540040c0d080e0b10042c01c4a20303400d880c0e880341c2c1c0780c0c2c590840c4100c40400350380e401c00c05040780c1000021040d07205824 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 10146949 1250 10145699 10145713
    0x11503080d021608130819030507030f09051207030b0f040201170c07140606010e0105041d10080609030301080c010801140123030106051305060f09150705030a030203070f02 76
    0x640e0300140c0c03140c08800c0301c1c110340216034540d0700780360342412010690380000300640e10200d000c007402e00107005100d0294940646420020714406228480045a03030603500c0b1890900b5580d000e8800c0c010036903e01040200060012a82c2e4a41c030b0003284c010f4030ba00c402454060300d0740c50001a00d1b140144481d0b10300040c5024840140d8004440b100d41e07682c1454031002580c2d401d04040070740d00074000b02618840840226142400010541601a00742a0381e030105241805006455911961140444d0380014a00100c04100b2a10390241c21510403200b11341000c1d07640440c1c5242140a503090b545a4000100401480408110f0615200020f09102a81d580341000040c003404020707083c1d034144021001a0850b095000900f2800140e5030643c554495840c0e83e00100903030001003410400f075060400c0802e25103441020b8901080c04040c2c3d072890b00c1074800511040d042600390410075100140714481c0002e40074005880c03440419a401600c0b850487c00041029204000720029504800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 10148199 1250 10146949 10146953
    0x409240302010c0f0f020301090305070501050609040b0a0b0103020c0106060504060818060f040609050a0c0614030c0306010c02060705010f0b0a050d0f02010e0105090a0807091d061302040b0303030403030509011503 94
    0x105084105401c13244041001041d420000903004212000946c0342d46004100020550800301421215008200030445940d50b5402e01c02c000c0c0703007034402074010006200062103130b00c0c242c0c0214400780d00c10b00d40981003415402c1010b0944003580c00c294041500854141700c01a486803002d03900c003049061041800c4c003041461903c8000c09032100001d0001900005c09019260300001c44882d40401107802d16685d60920118000f0507004a200041105c0c180115074080c91090300c1c040ca0482000500c2d6885010066407040c1c15a031303040340c02c000140b00b148040b50f02880740501e468194080450074510001c204201c1d100340da041360744900c031030710342c0500402e201403000c000860b420300702030110030030120069840c1c0c015250300ca58001320084c4041081074010500c1da04072042400188465860303041e04d0940420040c00c1802c40c2c1d4017020002e001e003101201314180c6d29001600014241041001290a41d8000c0f84c059012a86a40a00015580034451701050403034120f41540ca45040d9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 10149449 1250 10148199 10148207
    0xc010804030c0b04031b0506010806010801020a1b0507050a0306020901090501030911040504030318150c0e03060c0a12060b1b070602030a03020d18050d12110304021009050402040924030201 83
    0x3440003e4594001c0034002420140a00b074040c0e0303490b42401d540c0c0d4218505141035981c9080034014402540524800050b4990701402610a000510745803003640e4008d0b0020700d080f0703c0303100f1410368603445201c400150f6510340e51003480281d401100050fa80b8245400050b205465542c00b00d41010300e40000d11021a080c90750741c1d000c0310002c85010980b6102d605045002d8402c0e04c4c00c184c034003c030030000d140400a003035024005820303403013106024914243c8000e41c0c05c512640c0c0f200707030560003180000b08100b0851008002603101400c0ca01703000e1144080010881e01c0c5030300200400000014007081c2c00c5948508000f045825500030b000345410844025224010310031000c0078140c001c2541180203000342c01800301c01468410200c1480c520b42000e50b6108a044254404030b0701104804c0380507400f074001e5440c468010343e440742c9035803519428000c4010103400704008000c00c2c50004201c0c0e680e940010801405083c002040c1d11144100340d0821882c20101114080c180308d07800c00040c1d0308 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 10150699 1250 10149449 10149467
    0xc0a0804030503090f030a020f060105090105090705030405030d02040609050111010e030d090203070503060f040b0c040f0b0702030a1a06031002040f1733010501080f040b0a0605030303010306050103050c01080403 93
    0x49468680c1c3c49071030303611000c0c0c68200c003402907a5403804085100440154009000d4100d100d684003100e415990790010300850b03040c02e018568112480e0400a0810f50240000710740040c810022646440742020285d0120780054002400049040a00300110340e446003007003c106103018001c0124205003424255030380f04402d21840920303111441d07881956400e11648004000103005c0d01c050346841a20185a4241110f0840d42e1800000c0480c20300d20028003660291205400c40b85c20403403c10301d0354480c0b600441e03000c0340d240c4928440e0030001203030f845501400350040701583d040c50400d0010141025058900c00b2495071050004200c15100c003441402254055810381c001d40707030807180d5617040564501c031444041c1d8030300606280201d0004000c0c0030300d0301050310141d20760340c855004441e544001d94030350106103203800110f40411603501903280c0003034144a002403515510008a4210303007003640191250f07a518001002441428000c0104803d02480c01d140300d807401d9a405400055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 10151949 1250 10150699 10150703
    0x10c020606010e0607020a0801020d05010b0f03010317070203030a0c060e0114040803070207081c020d09050607030e031e0f060703090807030c0606090603060207050f0607120f0b0603040b040303050c0a0804 90
    0x141e01c40f07801a09444210840d040544c000c1c098017207090310b03100c0280c080c1d404002d031010b1071031800c1c000180102c0600706031610504c264214901c1c2d03074a9512074141e460411260220382040402003e001a0b90070402040b60940ca500c6640b800400350800c4401c40c0d42d0b028402c542641088296040400c0705010150300c680e010007000d440c2e0301c441e0070491408026030046242403080c07048101d1074107003264942020090b10b5003182c100c0c1d110300388200c500d080079100741500004107001500009009642003008508080c044620340301ca040f00703100803500c00c90340d01521078000c1c90b980c42000d80244403040e880f1405050503c442802e580d01d08005200b41500036013040b03d00010041040700d5030300810018210000280032607a140d0804100950054000b103c040c816043d000942c0c6178003254141c0720382034540b43c11303003001320210000000d440f1740c190344a515603803030500d141d060380c0d007501560056014210443d4140b038140760250488201400c001030842c0288800c120701c031351113801154080c2e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 10153199 1250 10151949 10151957
    0x3060609060a1a0f040e090c040c08070503150301050c04050a0b090105073e01030f06050109120305040513020c0d0203120703020a11060c13050109050607111903051501050102010c02060601 83
    0x42d03e10081400038062040d20a2108000140000784c01946005c518001c074250001c0c1e440d548009800c200883e0355212644000c40e280e034000070712150203000a903a01c07607011045038026040743d10000f07084032001c854540c0c038a4004070b028070145c28444801005041694141c5240c8480c0d000003070b0060180701802041d011181852805201d81e050f140b20403040314026081c2121800041e0030011003500f10070500003440c20504402c08095406120121401a10b0300310f541030510200020b0f0283c0710406905000c0100800146030319404110001310a405000580703d1022078071103400d00340c103180c0c600f0840d0302c244180313812042489003954000078207050050740d5058180054884060708075803008540070304001c00c00380400440c0140b90210140c00b5a85505480b440190380406035809141c0e04000e01f40545000960078500c480b83d0200b00814404520b034040803a41030100e202d4008985a0f000700d4521041300f0704005207103001d4282400240078048610304000d60b130303000040c1098108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 10154449 1250 10153199 10153229
    0x30c02010c181412060702010204030201031a0d1511030a06090b1806061b01020a0809010b0409080702060304081b0c010e0904241e060503060c0f041509090603050105040203060609060a 81
    0x10742d904d1030001c1c50300d0861404d0794103500d00100081d0003508580302c1640880d003002170390703100da01401c02c0901e5000002040e500701d0f00e1154456890282102c1a619100341d0350b0101041f21051403805503204560840000c12030743c3c20810070340261a03541d8841f9004845031150070b4103d000e01052140c1c440803e9507925100c2c10351071005414211080880c07006940700080506002c1c0e03101d40b100340320b929903030002c0c420390403807106110441e1000c0d000501403150078031190005281800c019038000d0b000d115240e0800310603a080c0b090842800c040014280d010244072041560400755002d0001411140390056107056241c3c601d0002c8801c50010703a28860491040f135080c881d9000d08400296a180356211107040c0311500c000304007900a0500c28825030000a44840a410450316048600240c15007401e25114034172030903030f1203000701d64244181000c002c40d580071548039080055004200100705800c05006160030248041d001900032440f0008001c499190785032000c044900c0d4071004041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 10155699 1250 10154449 10154489
    0x406020d0305090a080f0a080105030c030a080708070605090d02011401060f0c050114150307080102030c09010f030905161701062304020f04030c0512010b0102070510021c030c02010c18 81
    0x51044104000705103030340100389010020101b50241500315201c0d114810182d0301c0344109955842607030b0000d903040d800044298001560f10300908841413003800800c1c28001c2503a1404103540080314450300725401940303070010141d4240680c0208054501c0031907415410070303100a00d52445c5004290070b12182c45840e0040040075480784810740c2b01c81007202d00c1810000c0c0600016040c2c40c482038464400d83d1004a417001c410b2003220b01901151003e5031030481c01000640390040c0003001355003415a00c0c031540780492014001c1140062404109400c81420401200f901c00401141500c16a01d0a60140311942c11014401d1201104034908807581c40b0307080010300039105104900003043c1000c0390000800c40741031140f01c152402261032001e02e81070110440c0c22106038005050050f0b200c0a4100301c941400d1038545149005481601c807550316904210b01d06540c20031007507000035507881c03003403280d16420721800221260928003904a240b50400390a90751106018101c0e8000588a60b01c0d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 10156949 1250 10155699 10155703
    0x80a090521071a0709060e03070608090a0503030a02030f010603090201021e010605030f0d0807020a110609040b03010905060403090609064505030d0309050303160e030102072004020406020d030509 86
    0x302a0f540200105001c0c100c8035410041d0981c00d0b604000400c0c0712107800b145907409004610082d07000900140641881e02800f102e5410018040c0c0011340070f41e0a04a0201c0c40034001540b003080110000760b983d0602000201c0300d484140e0081c81058a08540c0c1d40060380c1c0450740703258070045582000a03190b42d01000303900611700d6500244d458498821180315a01c00415000721250300358507502107603650f022059031584003c034401001075004a108140702c1c5014009050202c0c80a00005102c00384400840c3c00c44440c1c0030251900e521038010002010303481680c10015242e2481d28044451401c10b020f030072915101c4018071640e05400c1d80c0700460030751104c400120614010070601400010809070034040c0750380a90f1307010f40642051454503130300034080d1807811507100c40211703e15900c090318181c0c0440400160020003072101400750203594240090100c0700e00943c98451407510030901400602072011000340280d00501c0104001600820812a812414100450782e81c0e501d040d114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 10158199 1250 10156949 10156957
    0x120708070e10081605090102030703110102040b0f0316050414061806040f0e010504090c030209280b0117070203070f03090305060703060e060f03030904021c0203070305040201080a090521 82
    0x160000c00084030001690341c40b900700f44c0a80d0690002e002c680000c06000c5400e80b00b2030b41010b000d68410401c01d40003d220340751005080000700001801c1603200c0140a80c01e80c00f802c81c0c1c107614940841408642075001d1002d1400003402d0901514207403802d42484415980c0c42c2030507104141c0031031a032214260044981204050041c180e50341d4940385c2184010a180a024030204004004004601c90405100b046401ca81244441260300d2855080201c6900000c0100103011b118a02c01200c42e08594200850165042d01c040f032541c4050000428006c904200036050030102004d02c060b43d600072048464040e00031180688400f02410155200c0e0070700c0d4402482403040700204a1101e925901c80da058a003603624506003522840d0402c116801502d0b001030740f5401c2041003480510702540288940c041100c480e000130000035002c075080fa0000c81e0b000e1b011a48a50811045690250215600c25400002008410196290141c3d03c6144c0c003d0840c840120103c0ca11519116a00351 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 10159449 1250 10158199 10158227
    0x20f040305190b09010902031509010f050108030a0e01020304031707020a03080a05040306060501020a050d0e0307050303070b010302010f090b0a050d0212040c0602060702070803031609080304031b090212070807 92
    0x49000381450b408034900746074611825940003081d180450780144040c0588018182c004006000480f130442c8490100c00b8050035040c05907503141010f071503032159800b0745030080131450095612194640030242608030100032032411504200001d100051060801c0d403940410440600d481c2c00d000d10200340000e0790758102400b03c0801045841e0b100d0b0740b100c000d0044d02e00c41d020030300c8115a00e400583c0d43c0d084a0310700412030f4000884442d82144100e202240c0c0c610003c00710f41416903030380c02290555100200c286c1d028080c000c010300640d43c100c00a260070303080c4c070b1a140002c01c0c98403800d14420701907500d401041140006620f04d100d80d007a015103107643c400980f286403d0400d071804413030044a61040310003500800000401c05400455a00f04441000028515580c1c44940e88030100c94840e4610040c080701a0700032600b203000700090710103103100d041c0000160b110061082c0c400b003c0d50303014034a001d00400040304184042480079401c1501030811018a4035a0182668504028240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 10160699 1250 10159449 10159453
    0x4110604050a030f020f0a08060a05060118060c050705090601050406030e0304180b030c0108070207090b06071415010b0f04060c03030b120c09060a031e0807051903030c08010315020f040305 83
    0x2011090003281051042c9461080380c021183c2589038017406080c130007034450306846d40c10210000d0142c2b40f50b84c1000e0350001341450451904040300654003041c8629070030000004240007507034030801c01c0401030f10001d44811505c0000f03618184000800c00c0c0b00c1d0b0f010b400d04040d2240140c0e030b00260200182c0b40580080b001c580758090b4540c500f04000d203254140c01e03100b44550b2076804581e5001d0b6800ca40202c140354058001541400012400340014103000c0c0cbe0442d80400c8030801140300c03680c0b003411812603180a0101848840c15017440703440e068028112210041001c8042d51034081d0803501120b03110309000e54640c11908080c0d004000b441800340d084480c5402c00c0084e040040346c3c0e046540400c40d00e078003a175142ca0040c000400742c0303400018400718020404800000040b400c112030203104007a0307180380c01059501c850070050300318110b0700c902400c0d0750b88804140e003600500c071001c442032800303059640c95901c99001201d110490b240701541d0025000104141c0c0104407030145400a00b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 10161949 1250 10160699 10160719
    0x1401021303030c06050a0507080a0c02070801020a0e031605011205060609041a010201060e0402030703030e1201020c010b0a08010c0917010e07030807020114030702030406031a031902010305090706080411060405 92
    0x4001d462403d10020442d241e6150100107400b0171080c0c0708150042145998510456a03851000d100400c05100058190b10590b04006072101e000d000418094116558100e00200d210040c149081c0403040b06a4145044080601181e42d1100c0e110501400e820800b02d01c0b61248404500540300d0301c60415006030410540b44568011050030600c0204281e000f000025650455903000f40e400b038800a5058001400c00c10105e44501500c44c03040d00018410007120902c0c803110fa0032a80300c0b080c84031182c2d4456500300240c0c5000c120301c1c401405694028004945c3c405801082c03c800e6000b01e11050f03485421101103800e00354030225182c8104002c803954151281810711280c2c025180807800200b07110181c010740c0d0101c000b0b81c2d000e903000d9001103041034200a02178001d0120001003482e00e401004840020380c0e0308100d030307040c0750b486045903052494103030000500b583d800400400c3c8643c41082d0401143c3c0c0d201c180c1c550b200d50040c950008808984c000034040b441160310807644018410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 10163199 1250 10161949 10161953
    0x206070f02100306080f160b0703201605010c0807020103050c09040f0f050903040b030c160213091703060307120c1d1806060901030b04060b0301020a020a060b1c1401021303 76
    0x10740110190341d00c045c01c4900010030940a59a60705485550a50440c0110801c1014030341d00c0002d00710003031080c180340180109036009440c80c407000400e40c40740d6510a035510104500c0d0a5410b5010300300130300c0e101c02c240119031142d050350b114940f002410107075104005459036050105898068200030400e0045010304da4290025000f00d00301c4403411850400800c1c41c1d190008116008c55071140040b41c1140d848210038409500054600c0145c202c010f180880180d80c0c04c0c00640320710304140da0008520b003041c03d00090320201c50281030f212507002c0042c0310160f0b0700058083c0071107407108035101348a441ca18266020300d269a03c182e40d642d071001c16040c822511043d015104021003d03440904042207031510396914010340704950041208001031011940022040368010b018120119200c2e408002280c2280d10130700f000001a00911941400c0005a00452584d034000711001100c0d0b411541405450048a41005200380b840d200e8401d8126002c0d0140c40c00318410901e1002d50359528 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 10164449 1250 10163199 10163201
    0x71505090f0a15081003081207020c0a0503070506090d050115051002010903050d05060612040303021c15050910080a0510050a02120105010e01022a0306060306010803070206070f021003 81
    0x8082520700c03581008100359454140040040d04076006041c41080c1110120380948440c43c000d0244591403c104c00301002180c1100c0041c0141d205a420758042450f00c00402030800e5950901e070351043c40c50180030405541c0001c0c0a50989204944466603400500005040c00e403030040010025400d0a40d003441501e1100026404c80d08159888158203000001c00c0303007200c2c201040100031078818071100151018a81c8410703844600507014526041d8101c8a451001c40104d804500107900000c1080789900c0203142d0003908100c02d03000784100c501c850703100b0011648501886000d06000d000044910011140344002403c00070140c400b0070040c1c0c107005803030b1026105542c2c421420800400c074002e4840c0f00b19801039141541078952a400c000c0111440c0c0001340125045200d0551050380041b24808075401214041c92142c8030301760160b0a160401d10700510701c5100b90045070040242300408000c4400c450b074121034482d0b5481003460040350284c060b61000e50002400d4512440480d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 10165699 1250 10164449 10164457
    0x4090f06020c0616020d0e01110624060705070905040c0506040b040801110405010c0f05031e0705010c0203030f0712020f0a08040b0906010605070201050705100e0304140103140f0702071505 83
    0x251050f50029a14405820030084080c0c19180059001c114a442444c0c410880646c04aa0501d440940300f0322100081d8075018080c1c40000c010500c07100a8001c001c8294801d00c20680241d0304a0700307040882e01ca40fa01c03000e451292045880d203c6000034100103032904484043c181c000c2030303140c68940f038082041d402c1d001030050404030762030200c040760701c5071001040d201140c1c4141e5418168011941d6410000920f010040300c50b4801030043d168000c02481c000c04541c60b0b807103112071300c504031030900d1800e40e82c0851914096402c100280318407540110459075010304141410b250401d8240c9140d0000d2045050308400c1040104805140e1070748a034074180500c0c06185440900d40303407083c4c09a142c0c4028030030b01010820030000700d401540190702078007401d8083d4080c0d59600c1e003010540401d0310f64222180002c0d400c00101030150080d81080b0f408240002e19040100003055010b0182468001d400148a5414480010000d038820842540903004e0a05801e2842c040a04040c0980d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 10166949 1250 10165699 10165717
    0x604081507050301120809010c0503040611150103080306010f020708060403080106031a0906040e010605030604050703021003050906011206090203100203010f210209130b0403020a1502070c0e0604090f0602 90
    0x8080115008030b100300292810394005981c1100c0001d400d83d5a459140d110590203418046010399002c04038a050024200405c800d440741440c0301502d05581c3e041c020784d8481c4c546d8800300b01c001400860745940c103603603100e042130070302d0812a610710000340e142002a034441e00e45031041104120401d540224658100c6103a610103000c24003003400502c15618003100c1c52a003258105001907450314094211080003d281800040c205854002107402c2003030407501a682a80400010030850030100c05440281d401843d04000c141040e02480d078440740d040c403ca84000350201090824820303150321141d050395009040b107070412010520840a03400900c02c3d07144011000c0c0001503401044159a5840c83c01101d40340b040880719403c01450341009003548010020b02910716000404442c0203a0007a4042c0e00182070003465890300203000c104220031130000d18014003c03000000e400f01c103103605442400c0744002c4166100400304e0300400c6e030040040d0207040c96007110020310216900900c42e40c1703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 10168199 1250 10166949 10166983
    0x9061d010603020c0d05030c0d0603050703120507030903020112230103020a08030702060d0e03070f030804020f0406140121110c07060c0b0a02071a04060c03051b07031d060408 77
    0x1030381e5520140c00301c0c0512000200c0e260810201d101e0303140d229400660340003145100041c14820382da094041114955002113442d607204090030700500100400003c1031441070f207440c40c07909249a500800140e05480003d05200d9502c00d510380d51a001c0d002404140380540c4152402801f4120804007000c083c40280d001321705ca140e01081307400c0301100b114100c64010700190305d840d00309801c2c1c50040401c1c941c25600b600007880441d00040700c100c01400b0f00c50280c0c1c0d845815060900420042d4072040400510462910104000210280244004090302400c140300d14041e0800ea24036140d410000d85041189090303a800c8900541c07202400b600c04468040761031094989005441c41c0f100d00502400c5400101c0008441c04c034160001c20241e807080c20704410001c1c5040e6200e8070040240e40c00c035501600c400005140c40da01d0b102d002c0c0d0103c09204987c808034aa0401a50144240c840207010801e076030030440300e044000780d01e409000c88007a082d55929903440c1c5446840d110107240b42d44800c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 10169449 1250 10168199 10168201
    0x2032404020f03060123060c030403030903030e091306020c01240e0a0506030303010b0f0d0203010609030501051005010e10030b0a08010c08090f070902090f04110307021002070c0603110409061d 85
    0x2403c0004205040c3c580b416083c032040a0074003440c82c2840325490001d940f04ca0300300482c1c0f020603418400380000310300c686c0300d018030740d415464080c2c01c6c07002e011051402100c00c4000c01801c030075114403a440c0070b40c202200598be8030030118100c1c00340c41c094041e142ca905035050365038040725521301c0440407501204d1040b8100d0b15642004c40c2a00c01c10742d1016030580c4240014020301016000400d40501c00550903032401842240c120281e800903440303c1c001c01d055040400a01000780a059030100d1400c01c410092401d040c0040c04420705048824090003442e40415802d0303000f580515000040185029040c568030820280a042910755270400521800041010301500042c450321086051010f03110060400d140d9000a401c29960507903c03205041c0340385006d0720b492040c000626170429100341d8038645180081d15005174145104442d510421a410124410400180589034145800b150b031040d64030003441c0ea40074542042c20500e140c0000003803617007404201c071040040c00e20018411 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 10170699 1250 10169449 10169479
    0x90503010c030e0c0913060c0315050303030f0408090d050f2b080a05040309050409030e0103060b07020105071205071b0302010801060c0201081807080f1605040501080a030c0203240402 81
    0x6460303c03d80300d2142d941c00b46150429a140100c11a40d21180d66800740740c6040a6803104e5056680300c0303c0c0500030a50303c5a03031304544104540c440c000380409800075859418511196103200000820240004001043c00c100541c0c85410755407045410004445c0c15000c480c036542d4881c4c0c0102500e81c03000740c41c80c40b1f0900a640b01c080d6080c0000840c2c88561481c3c0d03d80190a001d030030000c008800700b00f511100810780c0d9503103102d800300c014002ea507001c0c1c1c40461080090201e401540100e00e40c4e10b804e11000e40140c2e400421180c000d40e01a828105c4031032030309002d94080c01168801030101044906540740c0003e00240d4030103d0b4002d0740c0f800c075144d03602d03202551210b49403030000e400070b800c101c0000e44940d004150000307040040740840e10034bc3d907a40c1820f400c0102003c4003200315000314960000c0c0240400480700500000c03901003169502d00001d81d99550032440c401004d000048501405568040c400c1000400d103081080103000c0c00450340011580003154200e20a5204190f4611 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 10171949 1250 10170699 10170701
    0x20d0e0703021309060207020a030308040c1e0b25080304050c0a0302090a02090a030804090f0509070b120a020d020d1b03050403020303070e0307170609071505070b070c020d03090503010c03 83
    0x20841c2d8000e4260002000d010300c0440107810b020b201600c00c55020415100142c40c1e0038440f00007103001e503032800d6070f03401d0514060440c5401640a031281154182ea01e0b20713418440240d42085503d074201450b038800701f170004038075a52160b000c40b01d440e03240c612199003840201e90040d40300354462026501c6c0d803400c2d42d08010040d4107901001e908039007400d000819580c581d0307006000c4907200a00158089580341d0341e00700030380d01642003002d016483e201c0100e100071440c010103400100480107807002c6400e148031203001d0b0040c22407001c40a01c1c188007040f1980050340c11241d0345100b1241c01d643d1000102c05050103003200140c00a1510001250310703005501c01d220b0503004a5040e030144d4a551a405811501c0c01d00410200b07905000b80d0307400007910a00412a02410709200c0003501c81480c01e284924208003040d8001c26031004030303586884072513030700000703c488096001c1340841c21516041000c071420401031500a401c103100390b0040e0141508103400e00212041100284400303505114114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 10173199 1250 10171949 10171963
    0x9030f070f180203040b0103020d050c090702010b01030c14030402090408250c060201051003060203070908060a050a1113060f0507051005060a05060f07020432010806010e09191410020d0e 82
    0x90b014086c2000103000528145c1c066010b013a0103041219020000400007484210081d42c440c0050307999540390740c02958050042d21102c20090800860340350250254004a00c00140700034800c004500020b0100002c407001e54424020705030140c10080d01d4401111030501c18414203407015001414005401d038414003541e44100e01c10503103541d60b149543ea460300a500040e1212041c042000c1011461420400042d881160b104102244d2420130007000c02c06c680d403003140325110300010070602800400d0707107001300c08079000781c038101b0341c1000c0b0424121100d020b0208010994014500c2580340300d103041d0401409801c0031101c070f580135036503441081124842d040508090300070500005c405403800c1d078069103c1c548880107070206d040c3c1c201a4444440072a0302d10550001502d03005010150b4100051341c05404a005540c4050921444080e030f5a6100103250071103446214240d0100844e107403a040d400849002100c05859000003082d000e500490b03e21005d0a00c0c105d040500f25400140d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 10174449 1250 10173199 10173203
    0xb0a020a020409020f03010908041503020307020d050705120a020102070501050105010305072304030b040f03120203040803061014040b1b03070b071206030203060a0b10020607090b09030f070f18020304 88
    0x14610344589600b800003810308600c00f039a000340145245d50081c0c4080c001d01419074801c04910b40d4079410300318008411020102c80c8800c044c8140100300460b03800041d0710003400b95a0401035111402445c2003458000125481342c025000070600b0304c0100e4054000d81426840f0782c009002a0380c0740c0d40110300700e400895401000401000340d100a01218400405030100011540740c64541c6a440b4007010060a44007214210480104241490b81c4880f5004c00c507608a402545103003000d1b11903900c14000688183d100b461b07091230059074a401048e843d60340810f2035140da519240d8030801f030356aa80181c401c420031801c4e55407540d1800c0030080304440e6100d40c05061907175151141c58048841d04001056a07810395501c00001c400342e0740030412907114042580020402011040500c072040d256040840150350210080c880c0c1c481d000f103090b00a0f00d40e0003030141d8940200d0000249007160031414408540101007010802d0815184104140ca1641c010082d0300c0074160300c410204e11080b200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 10175699 1250 10174449 10174453
    0xb07080f0a110c060c04030201140304020604030b0603010905010c050c0c0a080a11031603050304060e01050309060402010e030109060501030f05060105030f0c09070302040806070c0b1305030708070c030b0106050d05010b0a02 98
    0x90440051540503001c00400c40c00700604000141e4a52480c0000030741700c40c0035000001c10104210741c0e10103910309142c4400c103051403c504165020030f1481c015800010f0810b1102000229a0384003503000402e0300340c10030024441c5842c08100034101d6440300010072098000d42903065030600b0903030108021584528000c2540d80d40907140c0094081400310029450b00529115802801490b64007030b0182d8011405103079200c0c0b80450251081ca10181070b01d06002040c02000408400031811036032054081c00c00000712200200001d0042c60600320080c20180703014000701c18852840c2803000032512130012203456980300c0040580d0b0700c0a81651642a6100750503400c020309003e540390740c101d22a07040250400361a40714071428403100715802da0002d680740480030140728840d42900e800c04a164144c1c4c40d51a12501c0352a224071413400c1c06447ca0600181c00750802c44044a180700642d0407500744411561a200024200d03403140d4113202e005801c1c4030002c54605076413002c8803400445900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 10176949 1250 10175699 10175701
    0x605120318010306051807030507031b031a0d06050901050117060a0b0310050c0901020d0f0f23070c1401020309090105190b0318070806060609090a110d02070b07080f 73
    0x1c5181031040c1c814031442e040584401c0005901c1d1a0780030030209070301c220742c1d4018031417800940080807150005c0c028410036007000c0f40b001500807540c1d02d19004103260310340412017840032000c4c40c00724004122004e4000051412030024080b859200780c0c022600c160007808982d90300e0040407d41600141c82c070307e060f0000d13000300341505000d0784241c1041c42d000d400d85101c24980103442c4200d880484410200600c0040c4800700c80d07134140144101c4d03801038100a021810405d070001c240c0313461001d0400074042049040d2060061440f034100703041498408165981505103003211006c42c480c812520040c1c0c0704112018690300100c00d85003844009802d03071310540c6c606010004505010140005140c0c2480008290640100b00440c170594804105611001c0080002440c146580c0d02c9507202d03801c03035014481661744410441d90042c0c02107400701e0042e2200ba101c1d50090103500b2444080400006504000b036020780c01900d0f019004408000360780d50b42d10001d442c183c108842c021180d500040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 10178199 1250 10176949 10176967
    0x60e030c01080c03040317070302040503010b1005180111011b0206010e041709040b040c030e1006030506010e06011202040303210c09091a03120304060e0d0503060d0201050c06130606051203 83
    0x1c084c0d980580289003603003585e60009000d0b041c101040c1c440c400001c3d000501444642005d0080840200082d5050302c1c81030f121003002003035805010a1a0a1820180020b9607940c1c4960907200035506004001c0051a00400309030307840c030030a82c0542001d40140d4000181d0b240d076008001703102d146c1082c803041c0c01c03001000c2c079150561300103090f00c0d81c49507a40602c081583c80f944240b00b0b4546060302c00140c0080e455103a1442c0020850212070b100f400c00006000003003000c12210304503094406a15801c0e02d03900c0c0103031000c903d10400035540798030224000003410b500c00007440189802032122102e0500c03503c500410b4580c0543c0704d10201d41c030210200032400302c2e40d0207500001c04038644c02c2c4040d103007480068144447c0480340e8100c980301206200500c03185120b03944481801d10010301428a0b000700152060000074201e0b4404d0301003040c00c03010769000c7c1044905a0980c0c9098501500d0030074a9101d001b18161800c1d0703403040c134114002c112418800c0c901e0b05400c0700c6100941c00d0a1080e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 10179449 1250 10178199 10178221
    0x4140105030c040e0a0905061302010c0b220501021e0a2102090301020c060402090603010903021213180507020d05030705040506030903040b04080a1b0e0403050a0207080d09060e030c0108 82
    0x26011612140b4100000a40c2c81e00c0c1c80c480390f0269415030008184014603003409481c1034000303001e1100319101a42c0420060381c011040b03981c02d9500503400e81c00c9a4070300d480c62030700c1c200e440711071080c404400c8001c404001041d8010a5511041e043d450000c000084450a083c000c0d00703465008500070b400c01901440345881456000b01120310301510f4a10b903403003c242a0b8104211a0b001a4010800c0c8030451402c1e15400f40c0c0004140c000700400d1217251402551099885a07004042c28001590502c00159002801c084d01c0d84010802d001c107040d035851002802d04442800040c000cbc504c9030000b4520500442e030040400e44e0b41c44d410181404208000356001800400b104d101c10040010005d074004043d0008008440261440c42030b50f0a090643e8000700c203208d00d150303031640801c2c001103074060f1400d078200341c151820039240c84c1c1c0c03503070164a040d11940010364103104a20290f0440350340301e85200706583c465036510050403482c80626544040c2d1490160103e00e1200c00101ea4510f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 10180699 1250 10179449 10179451
    0x906070807050d180519020405060d0210120902030114070219030518010c0204051f090209030d1b0b100602070605040b030403030c020a0804030303050f090a030e01080a09051203010608010602030414010503 90
    0x4c41888041503043ca81d40d45d860158040c00e804400c00c2014034660942c5801c1c0314003a800741055034a00b403021407550004200c441d60300f02640c01c0c08010380c505251440c003540b00398845c0c0d40c040d0003008106e284007885800840211480c10041c8240c0070701c10181620151221481070381038840500b82400560903403d51044828440d0400a408208001581c0c6500030240a500c00401050002100350312410310003019801c00c4c0b6401e40100490b2429440000c0c6640c8680701da864038180a45140c12003904411501c0b0010b07200281c02024058803a0710ba15001d02100d10302d4081f590180d503036000a440784c0c041e07841501802001403000401180c001d400c1000a0840c910543c0e001a00340e90762210141c00c0394009800099880b401c0081410100c2c000c180c029229038014008409a036800501d400c2416400a040084900118140d8103103074102c0b0308230992000a41d803400c0322000c002e03541500700340701c1c450015000800024038540048111425108041c4a8444216803c2e0040d20f40b984 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 10181949 1250 10180699 10180721
    0xc1403030708040b0301050306010611030708030402060904020a020c0f010c03020a08092403090d090510111204060201050a0609050903040b071505040305071502090f0d08040506070305030906070807050d 89
    0x10401503003000402c4180280f001d8500400220346a5040006052038a08142c01c018140440e00507005041c200c00020742d416a5031041d0300e45d0b6607030ba49101080081c002e1464250308203001003694941c154011804040e0680c0aaa15485503d024001144c1c800114203010b000768200c4c006810100d00880000c0000100c040c00d0b100300b403030080040c502000340038682114a40400b1003070103c4403500703101c081c594101524059030b1003800e28000032902070072040c01d54180040000e1019699005110710940166a0b50056440390fa94010107030103007e044540000d1246003c1000c600080310b0700c10b0324000c0103028019401c0a082c01002c0c080395100e088181d503054180070503103001030024010039209501c02c0d60380c2a1501e00a25007240e2030306400760500708444c0144100245916498082c940d9006c04071030010440a940c2083c928620481e0082c6070003000c0054191305158120000350701880f40c0c80101d0b82e4a40d07035054200c40e480030030b48410780003810402107000b0030411900315410741c0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 10183199 1250 10181949 10181953
    0x1d090606071a1e010b090105070512030c040302091f03030503090f0d0e1206070e01030b010302070f060e0f120316020c03060901240b09010c0c091104050906010302070c1403 76
    0x411a1550002d070b80100c2c60810400c00741d0010090701c04605840c55400309508140c202065061000c1c0110034041d50420a04100001c40c0381001d01500300b008408142c4010800c0356642080d800c40350040c2c0c071902041e4010540346010400d40303d000b0100180c850503034000c0120b1582180c0d400c80b400e41c00030f04100c82c6403061076072042e6400c2090000702c131051020f40b101d0107002c0081d414051130651594100340c05400000c02c10245a810612400300800c0920740007911031400001030700280611140a04001c0c40300c14041c2c108002940804510a401070448000301c0c03c0807030b860340e141d4a18040c1d042003181403012810901ca18456042a00171500541c0c2401c0340381000708c0d1400a00329540a020f039164040902c40b142c503034020254614013819541c0c246810440811080d1146400160411004440e00342c140b0402030008000352a81f403100740034810f02080c1c8001160001d00500d071041100d8804034000d036010740300716801c4990040842da00c651812040d0300424954030601034041c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 10184449 1250 10183199 10183207
    0x40b040e0c12010806040605070806100e01030905010204080705011103030103030c030e06040305010c020a210806091b0705010b011706090a050403050405060706150602190b0603010207080c0a020f011d090606 91
    0x6000c02c101981c060000000203207035524003418008203a07100505070405000c00e82003800320f60303203440f036038855044444d060528041c2c8000c0c004a00416060b900900315510215022894041c08102c1c141241c400340d86240407124004422a241e220a200040211b400b0b07080d1080024000e5000721400140142590308150366074442c00d082d502c0c072001b04030058125409800070424420301d00c070408000c0920721000d01c0402c2201402d2540040e041c00e11030700803003001460901d404104680803134070311044c0540341d4a6a2030140d02030210041d5031404282c0300c0c81c0c120555202d20540702d2042c440207003c410f0b1626528104d500a04010700142c0402c0010000420941c070b489004198603442248002811178025032004071406081d08288115040501e2003040e1100b5102400045078000304c054100340c58200001c0e0080c482c0000040c0094000f0840351102080460307040e02440c000d90709505014600030044030403040d02111010403031480748174542c40c1e06180d10b0b5070398450320141c005494 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 10185699 1250 10184449 10184467
    0x10090506030a020607110a0801020a0903031101060807030c030c090b01090b090a0503060106180909080a050a021603120305090109021e040b04090605070908030304020f0915040e0c04060b040b040e0c 87
    0xa9004100c161000c0340015011002c03407d1074110b00d80108496070085061007984400204a02454030000e0304000004840c014404800c1d84048010b0038200d0858020582c4c03031500089501c0988019107031074040c002c1c0024030036032500444143d128143d6810000b02d040800c100501e40001707103129003100e110702002c03d55880401c8880d020740000c1d00c130b08001d0341c980705d40302c0c81e00800368010103465400c1c410554000350800050b00c06981042c00d00c0d544800030035208030f2074903070fa014008041212a00700081400f607110f2440754000015030f014405607079440421400e0701c000400003500010f01d90010030720000c0b00004900310920040c80801c10300256000502a81d201c00e005a82c03841c1e480e020b01c04100c0e00815080003c0071490040c2d030862034103400040c070800314000010b0003624032400041d82145544515600300000030420010004a00d44031940c03074444814447c05285045e00224807074040c2c00c00c0d0741c101d4580039202c4e450581440011948842c02038910348544000b800704030a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 10186949 1250 10185699 10185709
    0x70206010b0a031d070807080109020d060b030f010513020f030a050c040c0905040207050d02010b1008040803040f060c0201090512090a03080d090f030201140105010503040b04030f1b0b0115050310090506030a02 92
    0x80d1303680b0203005002060504107403905145441c1e000c110070760716001c2c0b24030050705c40084001003540c102c42c002030004070b15800300b8202036002d5500411540380508105d10920400100780c0410700a903040503c00040d0742c180369964401c03010182290303005140c1d00c146407805e80c000b2150300c107407850038600e80da580720301040036038014030300c100d41c1c64200001c11b03003c243d82442200e0b41c4001c00c581842810350384080203402508050130140007a54000002800e024079070040d100c1240d03100e6401c101d80241071000a00030085081d0441e00d50095040340003c07c0d034903209981b216000242480300d840d10b1584c612403158080d07004010850f4880e900800800c1010b41e01000c1c0310301a0700041154802448181256841600091b0511406205001c04a140d104009502560605203406910032041c020b48a0f4030305003441040e4070101030100380030400303400b00d094101d03000c8942e12001207070381400036540d5002c00c882c41c60081c1c80700401042102030540001e07401a00c041c0c140ca60800b0f098001c15 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 10188199 1250 10186949 10186991
    0x30201080402090c09210f030a080a0e01060f1202040501050102010501080c0d2d15050103080a0302180619030605090402032508061005011d0f0d021c050a0b090105070206010b0a03 79
    0xb81b0320104110031003103401081c8440f110070a02c1001071460908132520241c03a8103405050240c0403643c40b03052040d02c48095000d0000f5041c41001c0b40030607a503c4414069001005000728015800d220000603e5401401202e05031410400905a940c40d040d060140e21080454269181d80d880c4030a403546261041001002c6080000c0110120085041082e480f000c1101c000300311030b10302401040800e0900d4180c4003ca401c40c1390251307455681807540c00c000714501d40d00340d80c0305800080544c1400c031101d000c040749208988050041a6440c41006010181203901942540100443d8021440117040a600409513001d007001840d8940000d0b520b0081b040740ca20180c4103000100340015030304500031200c1101c0f5800120302e4002404042200b503921024481e0049000281030130440d074400e072060708400301c0a004034120a009042140e50f401c00d04009a070040c10341004944052010b01505109450701d03001054070f44d291030b01c00f0020364040c000c11810590f9404403080074041d000008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 10189449 1250 10188199 10188229
    0x91009030f0507080702152106010203030c071b060905030c1503060f0a0b030a14090f070902030a020d0207060504060c11070e060f061902071e1202010306030b040303020d05010f030201080402090c09 87
    0x1036880e080020023107081d02c005003501802d0044585c04102c1c00381e0380001143e510280b51148983c60341c03100c1c900382d84800400f40c11030440d60b4410744c2c04146164480c048034220f420031021519280003080900c45c41224174030b901940380727904000250442c14000c0c031140d641540501910481c3c1c0c0d031807210344291f40090b5410324000351503e0301c0420252198000035000001440900420319544282c550f407143d16204141b00e99401000045a0400640c1964800e803283c2a00f99940c03001443d0110040000f1101240d040c3d01e080c1e1001c044500c1040100250485d000051001504054040c05a2070004182a600c40d40840340c10180e905c842010b45000364140b640904841020310010341000155088000c4440380c81c03540305c040c06480c11140f0110355030f0381c00c9400711030464001200a00303100d40018142404076030a102c1019855070040113000030000342084907903254521b082c0b042d02e40b40700103030004007400041005403602000c0d064124804680c41c80c030701940c900204141d9803150b03140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 10190699 1250 10189449 10189489
    0x903070302091305060606030106020a11010201061809050f0c13020f0706060b07030306061d0405040c08060403050a020c0109031101050a0c23010b10090b1606060e091009030f0507080702 82
    0x36000404c4010840182c01c4001191000e0642d030410030300070340c0c1c2c8403400400f9106000b0b4000800203a4001c1d480030000d802141c401c2c0780810740d081c0c80300d00500000c01d01180c65200c1d0722982c4100e08004a424405c3e000000c0010490b5a5a12502800b9400c41b41c6103e2000a080103028009903091140000070409a00220348500d510304010301124150340c405028885602102b000c00010152030141c000d408540018070b070303115414002d40224142d044039620b0300c940420310003071640180281c03040f0001d41d804c503102041d40340011101103000d41700080080000c40c2e00c900c920341c025405018510800e02c0d0800102549071200902c9601002c580c807000d91b002d00c04182e01c13003028015515064008d40314441c0e01d0f09482c00007029803a07944125041070300007094004003101000035101c10301b50881c0080c40180e850341d9281041e06400d0f107008110b0b00c034182c00442c5800c124043c0c83d4055401d81c5500c3d03441c0c0092501602d140d0b020003c121881c0380b04100c0319006a0b9000480300b081140056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 10191949 1250 10190699 10190731
    0x3010507110c010309021c0f1202030714160605030a1829060f040203040203030c06150a0501080405060610020106090e0709050c03010b040618050405070c060606050f0403020402090307030209 84
    0x24514240800d140520f810541030480344c00260716101c0034843c010f1245243c00040d1125030400a0340c901034100000d098403110342e2441180c80e0300001400010380510496000d4082d410f41d05903071000c6d5003c16003580d070181c104c20400c0c1409000a1a8001c1000d200880c4115011003440311000c01c80d01d0403070380e6090350341185d401d51070300c6110720828605510700342400d41480c0c1c001918074440c0c1240c0f03d108a40020000d801c644041c0196108500032400b254081d04040040911074402c403814a4040c0c9922500060158840e00c2c1d0b0034041e94001c0045c1800d5154403041c00102011124070405564980d035001610070071a200300076101e0345180141a040e41003288071000d845004e0310300b0b41d03a50420300050201c2c0c9681401c0300c01b1a0700740d041900c03001d644c00104180d042c48036030106030311a00d4601048225074110794164100340c0308045c1001851b80342c10050b0f40a0281c1200c3d2100c00000380410300042c14075034028031000d83c2c020116018150780750700241058604507003030701a4010b088 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 10193199 1250 10191949 10191977
    0x201050708090a050304230d050a020102011103040f0f080f04080c030d03060302180712020301080c0f1219060f05191103010b0a05130e011502070e01050f090405010b03010507 77
    0x95003102c4088082e0082c07514680310145d4178060742c040c03550402504c2c40600c0340500c1103080f0030940c1c00302800d250aa80e0640c2086038403002201d800f079015501b0450360b0010406410112440399900001807240c00b040380e15080200c1407800c1c42250301d01c00401c810602c10701203c02400c01050314800074a00f440ea4a0b051604001c0d020104e041403605000045c0016980e408900c000780622841b0324020742d41e41c0300d04031080e1608150000c0f41034400400410400000318480c0021002a1599000b580b07000c41403090400d103881b480e04054202045452405508020318100e843c018107011801d01c0c00414003c00b10b03002901c4105140c0c18500d40b00980c15107500481c400c49c0001c50016085600d171007420071442c42001c0e641c40c03c0050000310144503040d40440310005d02205440c00010b507844804d0000200e20402624000d4440e034000041e4000c012403115040c1c5030040c0240d40c1e01d9440d0b4043c0700e00d4001c00b41048803155220b00311040181c4007442414400c440c5540d810103024210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 10194449 1250 10193199 10193207
    0x80c03040306180c030b0c043311031c0905060708060109060815010309020409060c0e0f030102030c0f0309190506010f1707141203070605010302120d140304020d021002010507 77
    0x41c201400c2c002c031101c00c0702c0e004506100310f44c0040725080420b40100d45d64a4500310740ca03116035000000c110b443c2d200070074024030080e4034482c0c1f0100035000e008900710440d40b06544a002a092060090740200040c0e9150401580d044d03003500f00c00300300800e01800c10790b9101e0038001e08a5103400040e4000003000703655070748100d40d10000c2240b41003c0540741080c1c8503810510341c5c9041c1803414951601c69580071925681e000b0703400a5007003001088082442803005041c50311421161b441000f031a0100c490307929041c822039000d50030740c007a1a4a44003803000f51a2042d003008011542d40d0003018280c1000c081200e58040c20036201d800600b8840d814102c201102d44440d07005011003070101c00040c1c0246100241ca6000d4880750302018960700500e0f00001e0300c0c6000ca5200713408174000801c2917130420443c0e80181d0305030b038801c80b02c0a0444d850f100340181d9a10380f41c0d00701400990049803855460030003800858000b030014221065086a603000301e0b10310300c681108400182e41d03580400101c5540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 10195699 1250 10194449 10194461
    0x5030307080f040305040302100903080304030206060a0503030405030601090507110609010501180c170a020409020a02060910020309060c0706020405040504080306040c08060f04110c010c320403110d080c03040306 93
    0xb0070100d0b20141c1401d44000706030740a2030000034054040d01343c1c1020000d018501090055511600469580c500f03441e000b5208c11003902c903a409460510381c0443c0c146004170a507400c1e41c0c400380060842e80c0ca411152009450064020000d01000c103249150940c0184041c40c414090700b40081015403405c0b080d030318180c620b05a450340382841e00c01003a6119a1210180b800c032114200c1a045540b640c0c00740c4402889150f1000703541510005260148503000b1542d41c0c031500c158003c0d201030b29402c07051b0754107030703c4102c4521086030001c000140c0340e04460340113000340c04e00429005040689600c0032034102e0340140d40540d00c81d0404410424a4501406000c044071902d1400050781d05100300403400614840f0540d52099848801000c10540c000082d1000104100700900100174126409481d034284c0c490a1035106901c1c1d02100740c0e03110340a5030303844420710211009280c0362440d00d450503ca20601c0c071035540031003141e007484007250590014040396080310016640d00c41c5941f80000803208 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 10196949 1250 10195699 10195711
    0xe0a0308100b090d0803061201020c01090b010e15010815041103060f030a050c011101020d05040f0302070b040e0601050d090f0b06030f070b07020613170304030c0e040203100c03180503030708 84
    0x1404028042158813040c0401d013840c0da20074441034a98454034001003c1e4000f603a001c108646c0f01042501460310b05420100710107004000c0c480301d59885034491240100d0448001c00481411002d012003035100d8164560710040b0113043c144031141c01d0001500350f90951500001542c004410b0004a107092103a024034254203c0040c15100025600d6030349400702c0c030b030010b13040c01078a26a40b505030340c080d0100c4044c1050701c030701040f0b01d00d002c1c50b2041000a0005007a030040c03090000c0402d08052a408aa05891381201e0000c10369031424011502c0340d020350541c0441719152100140000c0304d8600130400c80d4130400845403e072405201345854501045c03410030702548090b000f0442c0b481071404643c5803680582e40140c0e0303200311890403602d081480d80515840c4444420403400460003101a1060b41c2c030401104030300d143e80b143d61604015040d90041d61640210900c1c99030100740d0b6008124400041c20042400311003070024898a01d00c0040507070b07041d000002003080d2207a000d248554400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 10198199 1250 10196949 10196969
    0x212010611010e060601030f0603050a0606030302060c040f030210050403120c030e150403080c01060302030a0b090d030902100807030b10050c0601080d17151201020a020c060a0f030209040e0a030810 87
    0x14610f4540d05a031004081e20080c107041c0d03640d1015010a102d0340000340515044021681c20040900d0440000d040b80c0c032043d00180503043c0407401d081400012101103444041c1d07240310160450702086001c005045400d03040c490100800400070390b000e00d00e52014102d94440c881c0c3d01d051410090302c2c4113500c08034123100f0481e03144d00d042a041e031301040d20262604241c100d03841d25800e01000307005140ba03420103585841244901d008100e4242c034a540f0031000c0d0415140410803208003603056034500c0600951112030000c03400451441025480c2c0d000d940ca00d070108000000c41d0200b1030103421901c0310000520001101180c0c01130400030300b0300601102008001c140f49031100280704030b84c004184001c0c25081408513034101a002c01c00c14071240c0017004c00301c01652290400e4000e610500c003a078007502031a48084804d15080b001d540c4807400b10307116181c4500000310200e0003940f1611000c0d903c81c0d0390380b00c030203a1560208664408240709031900c502c00c0c00c01c04607a00c8005400e91106200c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 10199449 1250 10198199 10198211
    0x9070e15040b040902030a0b030708030d1401061407030e0901081501080d0903080a03090501020f041e0302010e01031d1c170103020d020409060b150a0f020a020a031212021201061101 80
    0x701c0b81140403201100c2e190100181c6036110481d042001e030044a90542c5d00d482008404296000040010407843c018110104052018200b00c0d1500c0383d02440b407000410300c42e8071003004440c0448002c01c0a1440307480c010368203485080c0000c46892080e00801c001da801031018201d1440c14000d0b45016154000051081c0b03a070300a03005114085c1d5000081180c50041142c881e02402a0041301c0580d0703004000b5910340d4030580c4441025080b6104800c800c000303111881102c0300c5428003c4084d2130f01a910038509050302001503000c1c24071078000c0c140443d040701c00c550a02505100503819031040d10041c1d004200c100c0e1004003030191528550180441c40001000141d4608041d0f60107940d040e00c2c040346002a074100800181440c1800d03a8216008002c21400985203000400c180a002d40303803017501042c3c0c214100da4a03030402500039002000300314140045800041400901880c40c6484c038415041080990140e801061300e0382c80c03821070900148001900050f0b100b000340000f0f4000c000f0307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 10200699 1250 10199449 10199459
    0x3020906150c0102030f041104020a090504180515090c0102060705070b071b03020106051003060501050f0d02040b0714062805060103112101050901050306011703070209070e1504 78
    0x204680580344520603040c40100090000c04001942e54036030701940210344030302e80a03000400000c412203040b00c0006030f500c0341031218a064401e840141e42503941e1448064105030511005044024107107403044901c8040e500003035820000d8244000b1030050207912810b146018070f2078032941348051070554104030104141180d005064a1403644c01c10224a90703910b0303401d82600c0554a0002d0306420040802a440a2580542000d400c5881c10303210300403400c5041c1801c60856580b4010390f400240104903d4120201c1d55000e07041c0c0711240b10ac014503043e83e4041b451915800b02d0301c111601a6242c1c544c2050718010700c500c6a001d04d0300350080550f40300c40310069200f8014a032060140350346e40d50110355a80d200f03900001c440202007840d00d6840c10a0070891000144203456441c0c000070110004c6014100000c219048030300180c01825641d00300035555401c0390034000e6503a4503200901036840940c1d52003e005001d500561182200100c0000070b008081c2c1802c101c0c1052140c042000b000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 10201949 1250 10200699 10200709
    0x60b0c03030406020d020d05010803030702070f23030f0a1b0603020403020f011101090209070309060b042f120109090501050a0b03071205071203030510080c010c0201030209040e0106060302030603160302 89
    0x50b00a600c00030059603980c08280c548002c0c02243d040b4240e961a02c0004945031000000641c00348a45408070741442c2e60f2403050b40078800d1075000300005000d64a51342d03845680001241c011400c001415103400c0719005040d28a07195a411050700c0400102c0c0c4991080e0320425915000f4113117518040d8500350560b00880c41030041c50039042e04100e0200c583e80300f030b02c40031361000c040c090780142048400d040644c2c0040250980b03102c02d40b035080c5030a20a0246141507c81c8120450a19848001d200b1021448803640c049a00c0780602808040010850b44000200018043c11040c0f500090f44a40c2e400c00508507100140a044403915206914a00355400115001100c10301c1c001042100c00360320f041070515166511010310500000c1a110070140c242d0401071184034120740010800b981c0703e10450741d42d02d1010495000c00c00f0042c0480141d44a41c00070304074188050030102e84085950002c608454140c5d000d200080d6011003800b030b0500d0180701038210344080b01c1803001618151340000e2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 10203199 1250 10201949 10201951
    0x20a06030509060408031f030501020d140405060601080405070f03050312010801180b060109030602030a090605090604080301030605070c080d090c050d02060405040c030e060103050607090608071d01090b0715060b0c0303 96
    0x5d051200048002031040c0d0400c010030a801860203020b042081d60f9161039030103908010344103016a800c040400c1503080204603201c1c8550303040300c000c1505858000040d61541c0010700181c501d4010200d0218080c2000300501d001103102c1e9004583e5609540c02400014030180c010f1413669042c12400d229119400d11154050394011060101d03640b60080140d030000302c10340c002401580040100b009400c00c41c2c0c01031200c10700581080c030280d40c0e0080341c1510b8440c2110003c0480000b403005202241c0030b68080c0f58489040e042012080100e1340b00e29115410203a200c41c03a180e12040c01104011040f92a00c00415040d1340745e454840304e0790b002402c940220b006141c025030750f90480b8001e6910940114081c4645402641c60650b181c0c101552a1001200e44c000071581411740041e183c0c0c820041284103650300d40c0d40d00000305249904e890300801c1c3c1100641000f802e00c00106042c160b43c002001c3c014802c803520384202245170100010b40d200e9a12079004d20782c040c4009800510048116 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 10204449 1250 10203199 10203203
    0x10e010305010c2d0909180209010509040b0f0402040b0a0801020711060307120510052d0102060c040302010c030c050f0c0909030405030d050d02040e010902030108010b030109170a09150903020a060305090604 91
    0x42c62907400490130454072905203600c0f0800765400c081a8441d032000314904900104d0003545d00720302c0341c1e80390020300c140320308161402040c810744c49000400480381c44260580051009001090044030b4000080300490305030030110306a5400284501003100b04003545a98036400d680301030941c501044090182d0304e50411030040b2603110400114421012044100a010001c1a45a4041c2c181c2400d50610f500c0000030403c4030f444907403c201c150b00010700103118407000007000d4649815a0b0045400302010b100803002d00203140030110000710b0600c500021580380c2001400240812410000e103030720040c1820030650410070040c8041e0b1030100f4684640b0001e802c0080d030b04c000b1810f03041c00a02c260f0348a800100c18407800410480010703001503041b5440c1500070f00610200f0810942214095000104040c0001c0c603040361008400c40503000183c01e60401021255884070302c2d2200002c841b50300000504007400034811031800d81c00090140009107400c101c0ca150030b0284a5a1b65405400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 10205699 1250 10204449 10204517
    0xa020a0207051306150206040f0818040f0509010c0519031107080a0302070308150306040201121103010f03030917060a09060902060705060f0a0e0601050d0503090306010e010305010c 80
    0x15090a5a0003009000014100582a94881c40b8603458140003804140100c610140751702c80c1c090020351000a06d64001c0340c000d4480300744003540380e40740803096100f126110040300340110001e1440d03455100340c9a041051640200da9454009085070845811a43d44410b0000900c050703a408505038210f02100c030150b060003d000e101980b400015802002c10040850f680024401b0041d42d0640240c00118481c2e02d84130303620f4880c5170041c00c043c02003c417a2905a8402400580950311414580074400005c21001500548000c59100154001d810640e050450300c1d50420406034880c0b084001803004400103807142144040c81a1141070240010308003e48600d07010782440090340c0f064044170360040419980c2c04891030295141c94044030141000700c0c428000070100c00e000d0145154000d21130010780380e10b030308041c1004108075198906440c28401801100041d85042010358064510a11710000540c5545406401d444204004a08108901d219442e8007400c1c820070f58211090080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 10206949 1250 10205699 10205707
    0x141015020307110a0b03040302030c0709060302010e09060103110403060618020906040608060105040906090516050f040e040c03050601061d0105130e070c050303150f0d05030a1b06020f0903061e0a02 87
    0xf0014061010682004009020000c180b2041503000030080400480d00400c0e00c0b522075031044030780e00f122a0382c480a40800c0f007810a10702240340080003d580075105043c0000d0307031a0350005072403258100350403c4407255a81c080c01c0c08504442082002da602625609510b014072000200c0d80341d00a5201d50424401c1070b0021403110f0780200d003501d001e00106003041003100d64901c81c1d20080d010175030b0101c00700318040407024511031098044451004484d4030591034175240c400c00b8115030b08010801d54540f000c0311004800940144034540c001d01081d80c90008030802504540c001d00b02c3c030000541880010040211072071003140110040305c0c82400210002da49940040e1900e548070070004040780000030800400f2001840201c24115080d50495800d4640b138041c0905a50303d8000034003154400d210b4840c0c3c03e44510764080c08044518610070360f507140c43e0b0755602680c1110442c07010752680814604850b007420480300ea4015030b1040c0d0124402e640702840300c81804040c003443c1080350002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 10208199 1250 10206949 10206983
    0x609030703091211090c0306011803020604060e0301060b070503090a06050301050306070c0303020702120d140f0301170a080c060703050906040b0106050306210a05010c090e0a0f0609141015020307 86
    0xd040303a054900142c840003051600c07040240c00da40c8208c80d241d0214a40400030490280700c0d07220807050320340c00b4000d5450a400d010040d900d01100b880f8842e490364231054007056050700c15002c0c0c61b141d4852001107444a040c00c0400001420341d4010700100401031004000c60399001403240d4110300d007410010041d10f41400c040303002e44981200a074010140ca810120703218000642c0c0d01000c804c541e100700044002040b85036051003164141c501d900400e00040c8150882841211a240204022a1201d13030481d071b40c201131900414038200a5412030810483c1281c0c042c01010350001d40c20018110328546990350100950042c024401000404000500d080c1c4500090f1101c80660000070031030400070801169641e40c400c4400c0310a5428114440a01c50144d10340000359510f150703901c409650394143c100003c2c40c104001011140c1c48620016102c0807501c03c400382078101445114451801180640c104461a0702c4100540103030344054403020343c003000b03641c2000c0d444840080054010303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 10209449 1250 10208199 10208213
    0x6141f03020703030605061804060503010c02030d18020a03111504050112090305040b0c06010305100c0804030804031412040201021b1302090409140d030b010e01080a05040c21030206090307030912 86
    0x54003d03031f8101100048800e005e03408d219103a2281d8004403010300095850380181400d9a1b526a81c20015900520a2000e4030040c2d810500d4100d900e44800c040015450700060900300090340300755224030440d24940000d0401e6500101c3d50071800306901d242178035140000380941284800c3d0204d0300c1d81c0c0c2c801001098841d10446000300004488a91151086014940c880100384021240b9100d4000c10488107a154024400c3d1400140c071268982e0b42c85403400e0b00c0740e84008100704e081040b010010403507140c1c1d20014000081041c50390f420780e4a083d10019141407130303804202c03031890711641c110507840d07440e1070f8030f6200d5100d2500056125200b22010030040d00d2140710003801c2d000d45948c5100e804100041c0b10550b03541c203035018098501c5550040d514548800e2800d400034883c500000e0700440941c0000c0d030443e05c5452003150781680c07081d540007400307803010038901803a4140540c0d00c24035604001c801d8000c0c1d1440061031070440703a6500035045407800d105982201d1440b1030340710144240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 10210699 1250 10209449 10209461
    0xc090506010504050109180f0c0906080a060509010506030c0f0703030c0e090f18070308040602030702150906030a0504030e040e0d12050f180a1e021e090621030d06141f0302070303 79
    0x42c01b40b00b407180c12740f082c101518011040c054503000521010005640001c6ca0080504950028103802c4082c0d00300400d10034954001080c0540d0300804001403007010058a0088c0729041c029070340007d000c01e410000902000003c2c1d105880b0310320403800d1000c0450400907584d04075109030655040c2d810300005040c10283e041c0d1004e0031b2688042070024129401100030000c85100319036a034160411080304181030b000f9aa40309800c0341c024000144103079403030384c821600180241800f044d12481c0c200000c00b5580d0300881c8103e19045400514100c540046100c0400c0d00140404c0c0700510b04820102040c45005000304401e10303280d808807070a01d00a1104890301504001001a0281c4600314400001c40d0794000f00c0c0a4136008001c8004020260a080309541e00185140004d450700030400001405c03400c941c00c12025990410b180080042005048240c00d442c800300e00140f07041d4140c82c100d6081114a030258001d04414081d01440d140d069600007004d040040c5c03500070f01c1c2021001000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 10211949 1250 10210699 10210721
    0x70503030d06090c0f0207050904140604060603030e010302070201020a02060f0f0a05032d06010c02030f0106080a06050105090403050a030c0203040b040602030c07062303040213090c09050601050405010918 90
    0x8001568034061003560008001c1d03c000120601801034000390031101c10720742101480040e04801000d00079441c00307204480c0c100e401400031500c0b01c0c00c0d00c4c054a0030140103a50448605640703010800406400000c40da112010900b03045007014410740000c1c3d100d12284d034001344200400110403c00c49030800a90740850f0640011a442d0400d04802405543c0242c55541d04030002a80201c072602642c8815441514118844c0240d926080019541051000c004030f0381406000e031f5158040000344501402041000300038949008981022b0702200c0c0182c005a00408807081088007190b000b0084a400107801d190000700f02018142c100d05500468100015100c80060001442607000003e040340c00c109009507060f07581d44440136144104e140114803008100f070281c010881412001669001d070010300641541445107403c0422981004022070b00d041d081c1009200100f514802c00e03900200138200189440c0c10480080c0088065101c1c010444200900c0c103039a0340c04d540c022141c290 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 10213199 1250 10211949 10211953
    0xa030b04170c0d0e0a0303050d020d0e01110703080a090f020d0606050414010501080a051006030209010207030812010e09010c021005180a120212160f0c030b0a06150810090e070503 79
    0x121441420b8a0704041004800011301000c5051001c1c944028400116589a15000d2070311f42c00788002c20107500300300d00c6840555603034400c204000000703003e0564a0700d000d242e400da841001c1d01e005040c0780d101900c859892450300d004100000c0468603204034440e01200c000c1c0540d002d034a07006015044940015402c1824601803419138020b0b95111030503203600742c80b046030a5680ca41c03104126070084801080b5524400d0080200c14020780c000e00480701c061065807041c41e00c03a141e00354903034003c1805420007094000104900206489413030380024400b00284141440028000d503544100c900c0d141c030050b1b80e180803541844c0d42225001d00c0c1d841d07000030740310f00c44498107040b030345034a80c028070744054044c01e1301d4400c2c040d00000886100c1480b01d82c200d0140d400e551601c100c8191310400807294428240000700106032101d206912403242e8101c0030460504180c0d10b010412040704070350007404929070620400c0c50700c41d224141654002680018880020026036260040c10362003140c043c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 10214449 1250 10213199 10213207
    0x4030f03050f1b030304030305090a0209010308030a02040f140f1c060506130504030e09070f02031209030f0f04030606050405040f02040b0f040e0c0406080303010503061602010615030e010c0306050a030b0417 91
    0x40f400400074500c210f01a89081005603126501c0035201e04803800020b5008001c08018000640c144000d103801c1805107400504141d01d80c400c0301c10700d19007600f100315807030304000c5921900c0c0380036404941c0700001a140000c10305400f2070384404000783d00728002c3c484ca80b034000082450721203400704054000001c205100c0c0f418682409000c40c071803540f10034002e2100030009800c140c0101c100700c052444c160f009500d0001e00000492518001402c0d9002da80410400c0f80c42400d16240940185010810102d55070b500d03615103c404c442e0b407584400d00540c140000c0001003010303c10300900c2c150301076501098030403194002960b070a1903102d00d90f50140c40c005412036015000a803d01554501356000c2004646034079a1303e940e40424812654180e010340c0000b80000340e030000d003c48000c1c250001080f469140c003401c850b1840050301c0034000036590f11450044550901480c290400c0783c0c02d0410445007020080388031200940400b410108154003c0f804004000403100c40ba540c101c11540e841d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 10215699 1250 10214449 10214497
    0x8090c0904060c0305060402090303040603090f0f0c080f01051003030c020102070b0a03020403060605091308131a1206010815010f0521040b0f070509041109030109140d030204030f03050f 82
    0x24048850003c000910b40f1000071020300300b901c201c0d40d2003100180110708003803604104a01a200c81001100c1e40d201c40c00010b800240180b150503042407040c4503131500c00c0d0402c450b0602e4500d001c0d8400301c0f40d078107010520400715664071303800c400c0e01c0d01403038a1540f40c2003500050f0f18100080c2d220390004040020711a44503176143d400307001030f02e10411040c01000ea0310010045a00c2c0151a400c01c45c1c00c2281800001401c0480106900100c1500155125543d01d10003403040401400d06005020300140900450180c1c4448652115090030b250303d00342030a030841c4c00e528035010200e60500500e0060501034a000b003068811007a00103104207041081000360110055054a0456410a20001080040401c1c428440c0303e84060f0f640e40341420900c4040101509200001034040c0320200095603054400707003d0303600c2d49805201c0c1032802d60b80189480d0b18199074460f500c000c00d8414441400051108040c01503666010300e80141c0343d0069041140b014032402c0c1e80c5080c2c02d0103900b0221a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 10216949 1250 10215699 10215701
    0x21807020d0909050405030906130315020a090602010e07060809010209040203090309031c0503160c2009090d0914010e0316030c0b030f04150f0905010e071a0a08090c090406 76
    0x108080c00e54540607a140c0d221100d43c03d562098500400a41061002d500181401c0c2d02400e03d40b511440001c0f612a03a030b84503004800312015803114034580004910400c1d54001d0321540080480c0c2c8000c00020b4030880d8400e0301c0d580b41c0d0149a040001d41c1012034031540094045d20801174005104566034107011690b1543c070341c401040c4900a000724110424910380e40354a40c080104980c450624554842544008032404e45000f04280810b2510311001310f404818a00350140c1c00404200d56400300318100009000300400340e0407070340e0000c1c11102c1c0c1540d010310f00c101200c00d100d030040c0c11440b0b100e0042c3c030740e102d08041031500340c4520141e0f0b0a80e0002d034602c05040b01d000b6004190781640f0760382d50400703600c0300712111654520701c880424001103041503a9610240c0c140400910342c100485158251303603030b8010030f171510380d1911240d054020f010b1145600504c03200e544041a2298856692042c2c00707410201f40c00d00800f600000d41e90131062019849418000306004028075151503d04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 10218199 1250 10216949 10216963
    0xe03090a060806040e01060f03060b0307090c0509091b160c030803090d0305090106030812090a0c0f081515010c0305070602030a050a0c0f08011202010c060e0102030f160c080702180702 81
    0x240308604001744020314940c10300c9040203031029038003002c0302e0605585400c4040d24a18103d01e07010310a0010006181c0150b2240386502c444e140d036840d664800c40170410821000c064007030707840a040b0407803880c07121043e0000c407513800e10030b40e00400c410b507124203040c1043c1885a20142040100104101110700041164800380140c2d407810019074035a084020b00302e82650100034901c0754100441c0400072104a0046c1d0f0001c0c8400864004548a50b10311140890a17801030075528084441840303108014810034003c2841c148820030340d89030000c000d0000010403480b050510a140c4464000d16116904444803a078100806654a091003100d0f40002d080407038107440400d103002d070f442110074811100c20000c0308039a560ba80e25139080500602000807000c004038148000d41c80000000f9045019510b05c005c403a200050b10391800e9a000082048014280c1921201c00d41320414140c2d0000085990590054502e580700c0c40c80d440840c40394140c004202c4e502c1c1040c01c040051103a8001024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 10219449 1250 10218199 10218211
    0x6032a07030806010f0903020a0b0c0319020102040f050103140a090807081c0b0319031206050a0e01030221030406030209010e0d0c060e030d080109020a0203130801051f050904060e03090a0608 84
    0x900e4910545d1602103032840c40700d000003917002901c00020024041c2e20406000c2c0380d6412011740303240c044180d221b555002a01c44042015035004a8100058904880c0c0800108800e08003800400da00e20410f81a001002b00042502c55461105000340f0003094165214030f9031103a60b940e91254004003004442c40c48109078484213080c0072031250355080c0400c1e02440640c0d103072100c2103c000705130740644001205501e042d49080c0d90300f40029244c2c1d500d03064a00144500182e00c0345550441c014888819590821711007070a00400c0c4c0761014000000454040f5441850010b03101c644980040780e0340b20340c0c41e58040c3d2000341000c0040074000c1c400c41030002c0318010b0311020044141c41d400d0585a000304020003007c41e50742c2004006405a9400504d820000c0c1e1041d28a81100340b00902c0004007960826051a07540324100122180f0156540c10300650003440120a0361400300058100c5000030002000e01c0d4941d205418100030070016500c010030014081e2020940740c020090401c0411524 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 10220699 1250 10219449 10219457
    0x160c090609020c031902010e190b07030605010504090c1205010806060a05040b2803050105010b03090706020102070b0402010309060e0f030703120b030d11031309060303030b01080606032a0703080601 87
    0x1881e40e8640c821541440e1000c4003a6003401c02d42a10080501c0c0e140d84600c1c155501c401ca40c02c032450341488807000c0890030f0309643d4100d000e1818802c5400300010806001d1620f0241c0a01c201c4c0e07081780507542214003440c00842c1001d103405c01103944e1001c407003580d0b40b05814a0004220228040391580c40380f64192182c482c1e240d074510030030050310f004642e03840d0000c01d60f0786a80c1c0d1080700300b00e0303001210a041c1c1031403911a41d20307a541400c48000741e00c1203403400804400c1c0a090300c814400c0400038400c0784000d50506240380c071103840d15440078000a061554645e8080100142500000d040c25400c00681d030003901005400d80e160780c003140c800c0b000506400100c0c002404144104651034201400401031a0600754051380c1415204014080368031041c41300c0e22405401c03a01c03c0002d4211034070003252451035890040e0075941f082e603000b4180110103080202c9a1280c9013500d90003100304c0f0f102c021002c0040d00303103051080b06a020f420004c2c0005694030902d500482c9490003400280d071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 10221949 1250 10220699 10220711
    0x4030e0d060e060f01030209010b070519030206010302010f050705100b010c021807030f02030f0601030207170307030902011b051216060204030803011d04030203070201050f0d15030203010518120a05160c09 90
    0x1c2e5000e040c42408002d512840b0440144a440ae50303030b0241041901c102e044035906003031001c03405450044030303000710b00682c0010b0052003196030008a04405503814101903080152555a0755100c03283c002c0c0301000d442d41c0340000503460703102d9605007c4994014009007610142d000740d070800407408584540c003084c184141d420280d031544c400c81e84a020968801c024a4581e8001180039601c8103c043d213a0350380ca10394880785041c0020007180181c0c01600e002a28141500c0003401102c4101b1100303104003091190480410008200080d507034001560030340d6560404c0e8a0040110801e50019100324400f00740882008900c80055050700c201d40c8208107021300a5001e202c0201040b1001801a0000d104c0d031401540100050814000042d01081c00c0c030111180140c2111041c200c0c0c0100c05d0365800080055007020305c506078000c42030b44400c0911340d142c0c080859444c0300c80703140e40e05040c50000c0c03500c4442348030314159000255a21000822055942040c8584290034068060300d40c0c5068 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 10223199 1250 10221949 10221961
    0x5060d0201120504050703140606030106050402070803060d020102030c07080f060a06050114030c0f1801030e03031308031308040b03040507051c03080402180108010207030905090f06060304030e0d060e06 89
    0x182582106aa0594403050000c404004801c080c00340600212090f214400c00440018050b40829281ca6507560042070790780b07041c0080600b0758036603502580c011131041140324046864203003140d900220640e08401c00c8002c51004034a14070950303000e2801805004400f048401c400b0030041007402041e001c5640035150111100f00300c0c2d81d0b42c8074190204120300108e1b80400c810318082d56200d030b0a0154503051800d8a0361069041c0d001010b040c00c5440703142d010b8251381d03030103106d07110b40020710800075400c51403c800440900b00d00c2c1c2401a014000210000b58007030a62403118141300d9000d20410b44990f0341b44074444440c1c1007036608896500174020040303450b080800d0440030360032121803c44e50105540d10161458000035209a030040000d641c064001400034098032b001380600340006a0b00c01882c1401000c038016500043d11904050042c41401c00041c0314140d0440402c5800079903a8507145002c5c0c901cac0c100f000c0d00c00e40281e00075a1010074402250310044442d03000f1016070342e00303549803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 10224449 1250 10223199 10223209
    0x20f0705011a01021509010209040603030e0418080f16020a060c03020609010e0309090402120601030804090b0306010308030703110c07030b01030b0a020c100c02030f03010b07060e06090d050a0c080a03050106030506 94
    0x311880d2801640003c60560171070016200340c503004442540014584404072004c541628090781054001c1980380154804a0070288201c124a110500107140b04110030350b641480c07032003051182807100d6404030741108540d001012442d0800d50003000b00c442c00e40d5a0b00e010b454591300d480c0c01e90140c050040050000b0006001d041c1c901d480c6500a540b5040207602005480d000c06071080c0d0700015209145024014100030b07407806503000f8140d55407120300d0941c2c60001d541c989103c890007600000d0042001510740b00c1500c0e080409410301090402940ca41c1d5079180c0580074103c0040c0c41540300c004103000140c3c82e014140d034010314001143c0c0d039884022005a00c103070b0701c00030040d51100c00355120062240c0e2140c0326042582c030641745001030160f1a4003480c1c00a8210130048039001038400b00f00b20b107038829442040501c4010703041c18600307524416112200714a00c0c0091000c0042d420000c60f00c9400c4076400680d2001c403198450b80c507098014000c01c000d01802d0301191801c00425454608 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 10225699 1250 10224449 10224491
    0x103060e070c0b15060c0105150612040204090303020f040312030c2a0c0f0b0306030f010b03030715060902030a05160e060702060f04080303041b14010801030807020a0306020f070501 80
    0x495142c04440e8000c6a03902c0b24259002031000180403039440c80c601c001da803024000c0c807825490030000709190900100c1d800c4460749002d002441074404000c284045c00907029051b40c401d404441c0042c40340918141a000780c410899109109140050040108a4540041d0001c200a070f40c2c10007109100c08801d0701d09614500c1d50788140410280c01e00c4000c180c0c008011540c600c50100541e06035510b81c0f0f89a076140994216003103120000c410450b040c1000c2141b080e4800b220002800b0140c15840425100d1280c2c0001500500e2940d02034842c41c41d1940190b4001e0102060455492a0920b10400140b40580310303015000e00d8000c0d200100b61040041c81b4540f480103001c20310f0004c0aa0801141740c1c005144440c0011060000142d00c0d001880614031807401031642c2207001031002203031295402580c004107241403030300c2c8600c945664001340d05070549a120310144d9a07148a0f0000038201c00465100030025800040c010081620200242c10500d00c940c0080c0680ca131004460310182d28 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 10226949 1250 10225699 10225711
    0x301030b13020102010e06010914060306010f05100c02090f010501031404020901090b0a0801050103030203040e0f101403030c0625030e030a030203130f080304030f050309070b0c0106090207050604020103060e 91
    0x348080201d03045070580d91032000c0340351050000040c075030f064082c07903414494240d100c1c00b0425680c0c44d680500c141250304081c0e02020032400791000d0b604228611040c0c0c2468095180201c4e8020f030720343c0d0a80d001e11042090300d900140b00209924011420f114103440900429000900340b82ea00c00001c1080c69880b401594024140c003016803c00d1001d4000704480c0740040e62040e4010300c0010705060a12446000c0c6000358059030341c4e10308052480e105401c0141c85510007003840010807007030000311400f0380d0a481c0c80800112101000c00006032440c05031140011250107154107000381c21100c0e92480085500b0b8940d4249050080a0300340d040300c60140c090034694104100c0c2c2c040c014800d81c000d540c013140041c845403d007981500c92070403002e4601d1084908403000010300c01496000f140da0b0081b8030413898180d265103040c494135922230707540d4415501104004610703c020201c003034003e4005421036040071901d4444d60b04001d551542c06540580c0031038503141010480c8015240c00910601c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 10228199 1250 10226949 10226963
    0x9060e010c0809010306090f05061512010509040c08030c0f070801020c0304050f0415080607030501050901142e050d0c0206060604120501020403020603090a0204060821030c0d1104060e0105030103 86
    0x48401c1e210040e003a4420b1082d030f4101540d0b00c4001c21040407620402440d01e2140600207214138100d01445480403000c0040d214014bc14464401004009000c650540d4025a81e40785e0369281c1c0d2a16102ea203800e60000300389408081080d80f1400000039080c040100c1010407204159911001c003401c0340b094914004039500108000d00450420380c1110541c00009800000c42c00d641e41c02142c80c035086034101d0200707038005e401485005641405800e0240c6020bd0348000c0c1945000262072030801c5600045000c0c3c50000741c40107405000910200d40101650000e0304104030201c0d0041c5180e01a80178011150314141d5200c000c58030000f0b40134458000501200d140c10709050340400ca071910050200c860b036400300404001a1184d60140d4080c03480d080017424007054910400060302c55640142d4a241d00002c0420945003806030601d00005960100c10f54a031503041d0315200c03900c03407c0c1100403454101061500312500130402081201d90740c3e51356034204000c150045980d80300a10000d0030507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 10229449 1250 10228199 10228217
    0x60c090605180409020316030804060801050f10030b010210051501030f0219050c010e0a060501090c0815190e04030203040303021501030302030901080604021209010b010e010c020901060809150405010c09060e01 92
    0x2500f4150f00003603180340020202c900510010080e0514012280c20403524580041810047d168000321024050b10080780e8104508134180049403110400800c1c51080644034180c1c25400e034001e0060341c030a02d42c80001440b40c1d24107540c143e40342c04090f200c4070340007034034103001b90440c800d02d4400e460f0035070480b408101040c00c02c0c12044031660424501c400740755581d020468034006040100d500c15520550300810304d580750018402c01c49201000800c00c2c8810b1008200e401c8040c040315168883c0222446141001e4420340d0030252910303500440e1050607540140814903800001500449102e5822942035035070018074248170f0002032200074050b0b8070a0194180a60160301300391b03848980503100604040140d0180d0415010546045880b80d640e0305c101d60055901076084034490400b0300303082990707014660100310000b00c140724000800007804c0105503941d60500c030703003034045407070754074030000d0b41460300345207000340f05484011011401c501c400080e40ca010303440458420105842d0a044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 10230699 1250 10229449 10229497
    0x11401020105041106090102030d060f090e030903060402060f0408030f07050f0714040c050d090c050a050102070506030103020405060409150b09060a060807030b060c0f15010902030903040b090d0609060c090605 92
    0x11b908003074100c0c2c2c15408103100c1c06580c00020301c21b4400a052065050902c0da01c1d0542c200101c51044901c508140c204000d00c80164800080041c0c1003581922401c0d0703030740c07003040c41c80702540200c0e00724000c2400002424411403802d400500340d00e501036425120780302e5616040d42d03031368100e03840f409110900e01c00c110705082c074050f40140c815030304c81c0c2052403074501108008000c680640320300303c9203504076103003d00c82801c0041035032020380303403c5c0000c0c080f0604060000d8030b640030520000b807042d0f8070b60000031100c0d10b481d0001c0c1c460b554401d010104140f04080c2e410064001c0c140014010380030f210003d4820720301941000e0843d0f80e591901401d0707864a81d011005441000922500b00d002009807101e080d000704400369080c0320007405080309210701d551402030010184d01002c19140103000b403124074100401120211415031500660340e4145001207203040c1d25500c1c0150140b0b14040c03012041c0081904180e800003015500c1c1c40324561a190156a6400b504000300786d908800c40a43d45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 10231949 1250 10230699 10230709
    0x1412060406050c07060603030215070206010506161104020a090e1b070305030a14090709050f010f05011101090b0a0212090a05100c0c020402030103030e0a06090b12130c06080114010201050411 84
    0x900107005451240c82c0144c103485030b006944c2c0302d5004400580c40300709250061100308062a800071200e1014105651626000a01502445003064020201d0b1540c2204000101e04501502c44000e4019500e400b000f40d805000142144038891100740181c1c0003e41511066204610b00700c1510411810072556440495140d00014501452180d541038114070418811028900c0b071180e80c0004c00c1c149041c4108407042c0c400140c41ca98408900c04014000d00417074480c440700307071082884c0828000f60782c1009640940400d0101401d0514190144802c00c5501e800400c198070100003072500c035849491041c1e039103c030485400360032500b16000607410303010a5000361159070b51070300e80004002d4581c1c0000d000c980c0284d00460102c2c10403a81000030342002d0728500028003003410001082442c7c055004070070300c174000340c044079402c03200300269001c00d00ca8000d6000740d800982504c801515860040c05414081c0180d454449504016a085600c14000c03144100d5002d8519160054140107202d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 10233199 1250 10231949 10231951
    0x601090207020d06050f060f03010b030a1410060b090a08061003080f09130207060501080613080906040305030706270519050a12030c080a0203010b1803010612060501141206040605 79
    0x360301501801c003e1021880314000e80340140d6658092131414100b031380802a2488084070194066410004140715555003c182c80e00101e40041c2c0c1a00041080349205003800d101030032080c0c500f480d01002240080074803000d82004503054410303544c19900e451a143da01c0300100da8403400701d1a03500b07051000460003409040c075100135020050904d911100000c81c9803810b160480b00300d40d40031943d0400c4c0542809131600601449019005a0800030f0080030f00b40c0108201500400c400521000180c5549048a0003141c104d41501e484004515050f0041e0019404404c0c901b84034a424640a0b0108004a911950310800801c03401805c11550001d41c4050302082d03640d80540b42c0a440410000c80307055140d0185d50760005130380821540003800500c1701409000c2d88510600050105120706000c4454404843d42e44410000348203002a025007401c1d0404175052000d841c46408018142d0041c606803110450030352860307001007040c0082503040c3c20000d15240e1280000c280031445d942d02071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 10234449 1250 10233199 10233203
    0x6010f02030408010204031a010e0403080a091707060c030c05030606040302010e0a1e060f030207020d0f020a031b060e03030f0304020603071404060504080609060702070b0a050712030615030507020601090207 91
    0x141c0e041a07503074824103017203811503841501c04200750007110f41a43da4201c5041e0151199142c00b40d42d500b030949000340a5040101109122544c03860f40700140922507800801056111000c0c65442041d0b2400c10003400444040c1008282080c0c08020f00c2d50262050b2031282c80c015040341d060615580045809050300da4940d6000510b084011850000b20084c000c82d5400038114030f0328852420600601160041c4000010184140500c6005030ba40250f9501d0350b07a0400896407680c04140005002020603074001044541800890100c114050041204607182a1145031000d80c0c54010300d0744921528521031504902080010300502d8844041d40d00031603c1d24001d2a00f4040b110750f031141d94095040200811800301d01004142c0d001c004840d48500d46602412003400d08400c065920001070003a59080b0b20041207007031304030748150240e51020b0740281590303d2107a81d08401400070903003400386842c00000f104840d4100c40c005d01419024030702d03650080c00140e203417086002c020741200c002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 10235699 1250 10234449 10234453
    0x10020d08060d1b0b1b0d05030a0c020f060403020d0f02060603060705220b0301210b06130207020604030b0106020609060103030503010b03071101020304060f0506030106060507060b0109050d0c03051203090606010f02 94
    0x701c0f100a8000711850001e0038150441075a10312036005c416102d51104002c1c41c600d90300c14214400c03000d034001c094070780060700c03600302049500110b4402d9040401700341e4a0020340c86504108814140d000a0200f460241c42d2201c2c00c1c81291602c00f00c0c2c0b640000c4034501e415030300c03030710100360500d00c520001d21514070f8108600305041e0550000c402407001ca503020a01d41880400107100403c080a9840416003000313440d03c0c1b8180a50307940c46401380c4000c009500c51a007280e5001c440c0800e03a0111241640e00a1009a4035522442c0c02131103401c003030080400520400001a1660b04002010740c182c81e090303152141541e280a00210040d4001400f107403c0000030035498818420900255004500c6054007041e1200c3d0440f0100c100e07034000f01002d220303070305000c01040780c00d03040f10480c0e2080da04080d02103180210440140c600700f406603c846c5d08081030100d201c041c041050b644109582c410002c1e46e200c0314940f60400c4580c041070f82c8506054101e074020949035030191051030780114080c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 10236949 1250 10235699 10235723
    0xf0201020c09040f050d08060d0b040201180b0705060109020a02031e04090e06061002030405010e0409080910120f0c080112030c05030406051e030f06010c0c05030a030e10020d08060d 80
    0x480c0b66103600341d6089406491419107a401c00a040c401080040c2d190300c0c04941600e0103c000902e1240041805800300f8041e0003c64107592240a008084403102c0070980440d640c2c0d14001900c65005003001e54050040d4000400c017104c0c079000b210b11048240d4011801c01718030b21144c1da0030140c4003d540c1c0380050b007040000340400043c0510802c58010f90040c0103280303440011b02440c040350610a504640082100380580d071b13081006c084a0140940e00003034030505516001006204802110340d108805176180410960300854812504a2080090010030302d212110000c0d2880480184040b410765801482048000c95005800718000d1810b0750303400409403a407a0440e07025820020015038001500c0c40c024240c3e900003c0c0c490a005d41c5c1503c1d502d486914210003c0c009881203040100b80d14004040c0035810b28108064807005080d1243d0a4140c600a8100c5091081050040c42518000540e4900204450f0003002c01c98884554680d10349003017284c0303031a8041c07086130500e444035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 10238199 1250 10236949 10236973
    0xa0603020904080d0b01020706050f0a020703050115080d030902090402090705070b042003150a0207141f1d1f020408060c131703041a090301020319060503010b0306040f020102 77
    0x80300c0640164020714405694001c0c5815090030340d45ca0901890640d807114504100c042d502408071007000a4200b8941d0725102c01d050101c2c1404042d03031015000358201400105c60400c40000c00003150100801c588107691078020607000c1e40d0300f00b04080e522a656000107405400d0298074158411040c0c0f038400d1074044607aa498102640030f99058500511000b09030014030011300058040c0d0030120000e01c005d0140b00c006a40d4094010804d83c3c1301900800c0700d0003005907201341c0c1d40d12070400400362440a4444000030440c00c4002028079081400c202400034100c111400000d610075030303203014101c08941c480b00340e040c11000d4902e066507543e0030080000c46100070b1003041e02550200e42000e0b0f8070464040d440c0512011030b0407403001806005900d08000c0400400c0360304036149020a01e100c01403042d1140a05d025207803481c2d805500010030001b034455503d80c80700501c00c05800401c0201d84032028542229002e8100c1500f5600610210740421865868000c1145c4144102d90a02d0010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 10239449 1250 10238199 10238209
    0x804030b090105010305010c18031e020603010603050a050109090f02010e0616050a050d030507020717070914060a0603020307020c15040302060406080906090109030804080c100615180608010e0a060302 88
    0x45481c4902079654000500410100b80076222041f041440c0220b0704094000da500f0320b10040b0300c4020036404000d80c401e803507800148005581e00c2c0c0c00905c41a12580e55603000b4018040803112800c013107240200103e4070030910b1040e01845500300c11074003900794503540107540c00945000c2c560ba10403014072680c1310710140c0d003507002001d506c104050004e03140c0700d1401e9403402a9125903034042c141084100a04540c2c005010800c41788030034440c0e8101546d00000c1400c1a0741504003000c99800e00100a547e00041a0001c0c0130301010356070098110399611040f07040780010f940d00740c01a0445440500301e45000c940c0030400e82d82203203000c0d243c02d80da9400202540d209a100c0300100300704508210b044001440401d5102c4441c40007845001318682e0004c0c046180100300500c08803010032407050b1a0020003200e1000c0e07514100804c031040c4c480d090b0303451001c0d424000c4c5002402d81041c4101c1c05024000050850b015034503410902d134280030442d03185110080c41c4066a558442000025a8407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 10240699 1250 10239449 10239451
    0x605060d050712150b06031b0702061201170d0e04020f040801240902130302090702011b090816080a020d05030d060902040518070e041a030715080105010f0c020108040804030b 77
    0xc075081d00715000364980380810240c89010703140b4440170300d014240400d036114501203a03031000c1002d1001c00700c0340c100c80c003102550166081c00380d001507010807011020711200307500b00d058441150428003020440800940c0d01d504c108030400000c1c91040c1180250300306a0050300c00d046048450a0400d9100c5c0c11032421280c102051008800e40708185075041803c82c3c6c411030181068110641c5450749032240d0078218291031000034003548104000842c500d1003903021400800e00c0c00a0001502500507004010303402c0340c003c4084d280140d10100706402080e040352400c0b14480006845031682a400700942001c54120544180c0005c000a01d03a80149104200140c54200401a01c0f181010309010750715640140508842e440e00e400e011070346030410f4480c90040d0003181c010030210b58001d60010b041088100050701171164410100c0c0d04c6840f0380c50011034942c203546035410360381d032040112450b101740c0c001540881ca11798000005135201e0201103030300a01070894986031070350320341d40c010480b48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 10241949 1250 10240699 10240709
    0xe0a05060f0901030b060c06011401090909050615030a0302190512040b0a140406021509071208120604050601050409020703050910020d090503070501210608010c090905220605060d0507 81
    0x7000007108001982c161003481102e080c20b0b581a804c4c5444154220b0760351754103001d64250740c0c0c00d501d6501c905a206075030740e00180402800901c500e42c010310300b040c0d48030000d0b14002848001c04120f0801400c1c001881440c03150554000c2802c2c0e0000410b03030184c0391003c00280e03418054440018a211a2980100003e1040072040e0b9554a0300b140300810144d03174484410080c0f03004200410540354000b442e10104c0441503019400c6840354040c55280c200194030031100309042c1205003040c41038481c0600b2983c210284c031483c190f904c80c400c01044801c225606404200d007800103101500d159406000441d1003418924545207422001481045122248400581c4100d0107000c105a20100d110010401580204010b6041c08000b9050f200f15664450b4240c12010f007421000d41141c1011009200c0c0038000c00641d1059500101032503170500615921500346004510000b581c240d2030a0395021203c40d11203982c0040c1d0384d11000d41030203000c0d107600a20051204010507020700c51b00300100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 10243199 1250 10241949 10241977
    0x3070507080601030b25050a021006060c02010809070f0e040503130b0903010e070b0d0b0105120a0e0d0e0609040b01170a0e07050d020a030b04170706020406030f0c020c010e0a0506 79
    0x585149401056800000e0070041a041c8050b054589290748288591b12502541030480d2100b0145030200d103850407400c61030030300c40e0901800007610398014040d151554002e90300c4504503a0b64400d83c6030384040c24400c001450f1096501000a904948495600305d880341f402e992400e503030f030b90100040511640103078a808400003622405480c0134400c0140280502020b0a80c01e49840c1c4100c4150148240c520b00e456150040c80343c0a82c420300440b00e10f500400c01d0102c580c10003200080080115024a41ea0740c460140c503010250b0160310402070808000b408189442240c1082c00003410615400034180714402d640310880d419400d08603481a150380000003040ca146284003450803106521060151840801440c0907032240c1c0d00c00c0043e2038109102121544640c078110b6a03550342550040414a008640032003000950b4004004490490764284210000306030300350f0032102c0001da00002b41c0e0100e4680142ca500404880601c050006c01c081400e41d65034010a105900502182d0441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 10244449 1250 10243199 10243201
    0x507080c0106061b0209010501110a140a02040b0121090809120604030206150a05060f040b070807020102070e010506090d060e01020a03050f0c040302030604080c030702060a03050702010b06180909030705070806 92
    0x3c6980300c22180540e401040055010050940108010751410b0084604015104e6004c02580d4020000401e4050303003c0d10100342d40980c40b1203541c80703d1355071101706e1003541451150440c41d8410104a403101c0040308050214891400408006200800c01102d05000c24880c900155540d102d151503490780d044050b01e034038a424070b03000381040350041400c120b01d2010b140350051611200b002d0005c0d200709a03441903561042224070800e5014940c0701c8080c00f440086d2610400801e40003405143d4400c1e0210382a4944541090307000c21424011250044d0041c044440da5140442d1b100410340e0003803070001040c02050703803c242a6400000c21401103034644042c450a184c5080016500c0961110041e0401d41180d00194032580080c0c0f024215010114103030402000510456401c41e500812143d603034010500c0140140c4000c41e02600503501c2c08100314080c0c01c00c2d42c11500d20b288940c56034400c001e824001c00c10000d2002c1d05c054800c2c07200340404000200c00300041800b8254140042401e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 10245699 1250 10244449 10244459
    0xc150108060a1104060203040509130f080c0106060201140a02130306060603060f0801060e070503090c19060206130305090103020d0f060905040b07030903050d091b09020a020f0304030206030708070507080c0106 92
    0x98072980f041c40700d10440200010403c040d404016907040e00c4040700c00100a07100c01500c1c4140d102e03020000340070345454207942020400540300403c0d410821800a2104507130f107550503401c803541f0148920b040b03400f00c0005010544142c1c010102014480b41c04071610703490f601c1e05030032a14190170640120350740f0715083c81070a8903440d4180007045c90b00000d10610f8101107503d20203072030241080c01800360103c040340340c625003400f4868080794040c10050040c0400c21503007650000b0307886180c0140c0100e0022685006104c1d11140c00160182c41d420b00d050900c1004500941c03003840810b0541e55a103444100c001803502811004140784840866181001d0410044407a0058425803e052038003000317000003600802550080e840c2c0103000905a003141c200380d00313030400301d01c0f15a201040302003000c914140c3c9175000d071242020a43c210703281e4444022000b90350744124000039500c01400d00004111910035801994441102d05c3c0080c200310499035122055004681c01980c107945440b02402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 10246949 1250 10245699 10245701
    0xf0608011a060f07110a030501020a02030d0b03010903020a12020c0301090606061b0f06050606040308030915010b090a03081b0d0c050d14070204050601110f0c09070c05030406050c150108060a 84
    0x100d84001190b15074a050030040b07209040b442444d00082000e919400f0307880040d0340303080c8804019504100290742d914110039000352282c2c8103c540080561514036008081c0c141440b4610803507500d60000c00d5506000d03150003508042143c592011440b40c0212500c1c45d0302e0030300414400c144280000724110b41050406454090b4240e06c02a00e104106d641130081a0014420091603800990001d29030311a000403c1c11032251b600080d110b080004144014203000140502460420324118280d60b44c9441d0031400d035100f40029190302001e81c08003440440c0003400244a10740300c640480400c17030b800500c03441c1400e001680361804900c0d40070885041c40320612500011288a1170702e4850340d4640301001d8014003404c400a8015507031000000c5059005d60ba0302170078041e4403811a40c800c809810f030075a071201c151081030f0064034000013103618140504c016510b07443c1d2000c0030314101428140304450703030342010210841900c81c0c098844410b540648000d4042c00000020705520b10301849148 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 10248199 1250 10246949 10246991
    0x60d06020c0d260c0304060906060b0f0304050c0102060c1803010603020307030c06080c0a1b0515090c040e0a020d030f02120304080301061803080d091104050903031e04030f08060102010f060801 85
    0x1c04000f400804c04a6003d04d0100c079402903101400095034002030400700c00800d81038205034441900060707248031844491010314410740c46042151003006080004a07102c0009440c942d903040b07018450b0860303d40ca403030038240c40c022010740000b4050740d9a40029103130000650068a02e541c0303e403014001554003101c0554804038001700c0a2801442080080100501d0318400c084010034540c504c04200b818010451054640600403e150609510040d1034038120905a40300702d24002c907510280c02c011441301c04280d00100400000340480d2020b88079222030f058100214040c03100c502000e0102035018500543c02403000f642c407076042140140111041401d29508541040001c0000070000821662002d1140e4400300b65201245070202c0c0c1c80d00240811075102e4140400c00005100000c00b0314405d0202c0040b4000a01071014103070300070320040d100074000070504103075000218007840c8642d4101c501840005541e400d40440001111910b170813030301040c1d440b440200d680041d00c103426 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 10249449 1250 10248199 10248257
    0xa0809060106030b0a0504020a02100c030b10090e0115020a0501140f0108060609011505040906080102030a0b011e0804030509030105040b010314010c0210050606040513090c140603060d06020c0d 85
    0x308211501d02c40040d245c071802c0d120301d502c120307000a55041d5043c801c0c8a03200d80004105001e2041c0d280b041e40140c05800f278102d801d40241c480300c0c0300c202ea00d403046c4118811100443c62500e200e0342000803404040c611004d03c2001c2d48585285000012424421075038101081038505403a411b052450358101c0c48181e004048036444801030000381d40e10041c0c1e4604560303581c0d29908407808800410785c1e072030065078040c022191a14200050b0740c1410340007984103d04400301001006100c40042d114000c3c503020030744803000e1040200604600840c101c0303400074068205942040c0144002909603841101d007103c41680f20001041006030501a2402001c082e00081c822007068200007503662580860950780d40352602c021520b103442d14421180501009054107904150044404000d40310902c030413264000c20744000142c1c00d5840500351081500200742900d15140c000c01c00920510350035040d03441503420441c0c521a00c10401035007445444940700d03030800c3d104040406031220118004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 10250699 1250 10249449 10249451
    0x6080118050d030f1b0201060e0907230402070602070501020c0705100e010c020604080601030b090f070b090105130b03071d0d0f03080712060b0414030a150b03030706020a080906010603 81
    0xc480041e0300800e401c1e0080c0d41626000440c0b03900484610f01404841c5802e568038039081c4051000e255046d0028000d403071211058520503182e07004041d540b45003d1003455181e481c00142240e0031354040600c0c081202000b48090300745001134170391100300e0b8807090048900e60350004c1c20381d50214040c0b08400c01420102c1c0c980703884090320540940701c003103e003144904203d5402c10341c0c811565428165000752500808a8001c0c0d030316032604505808040d5580501c42c4144081d00b90b441200041c41c00c140d80c951200a402c0c1444e0301c00548280c2c00030010500b60500f100c0001c00d40b000716102030751290100ea621420508c42916141c3c0c10500780006660190100d14500008546428800d180300c0340d0501e00803000d07a4031500e041311068400da25803403429080120000d0700c442800050410358025009410400031180105a0748010f200170081c00e50186000c1c80d00c03501d1465201307004025018080e070307181c084195140022079000c46150408600c0f02c00508c41c0050703040201901511003070030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 10251805 1106 10250699 10250741
    0x609030a090b040503070e07030902040c02011506030e0a0b070507050d020a02010807053603160f0509040503070b0a09061401080609030a0c08070602040b0a03060801 73
    0x412000010061a000700b052880c26040340c084440007401070507464508180e0f42d880000080415043c1507845040d00056261801003c10700c3c007103980000760f440b00225880c031420105800400c2058132f0034010904607a0005200c0000d2900b10005145564403010221883c0c840e14030002c15900070365648118098001944404180c0700740c90300c4480740e43c4d525084580b4015038104074020b00c6058038014000340c1d041a232004c1080001c0035500c6c1044e203200403e1802d0202100480410702c1c2c070300300304050b41c106580e032400f911045420305031500b8681c5509550b4041c074440907060b503000c40301003504400325a000c0c400b207513440f1030144841803200392a046030145c05d01c076812090140c031000035a5158084100d4140440f107842c2c1d400031b824543c85080d8640c002060441c1e68690800002c181480b02c0d4000d0010054071380e5000c40c80a081c40805404d40f010801c0901200303507511 = true := by decide +kernel

theorem cover : BRFrame.Cov 10071949 10251805 := by
  have h0 := BRFrame.cov_init 10071949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10071949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 10071949 ≤ n) (h2 : n < 10251805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
