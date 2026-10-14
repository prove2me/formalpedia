-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2651
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:31.154271+00:00
-- url     : https://prove2.me/submissions/d1fcf3db-ee18-41b7-b9f4-69893b0ac16a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 476618705 ≤ n < 476798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 476619955 1250 476618705 476618717
    0xe0114010b180f040e01050109020901030e07051807090e0f1006170c301008071404020d0b03061609050d03122316090e0f1812121006 59
    0x3501d4101e10b042d0250100451158140100420300f5490b01d80042d8020212103000f04a19030311441c04500030b42112202900107417403e00b2100c0a0480040c0c01c4041e80c1d00202001e0a040d50010780c12003002004049138204551410001603c100c088001401950040700000f603c0c540f510f0070070b003840e04550004040040391240b001c4000c80004806070000c2502c0c030b00d5070f07840c42001100b002450100311644c50010700c0002e0751401e0705260040b140a800c2d604103408007070369a020160398442d86405036016842000004200c01d00d0a03078004c0104c41c001200100b40c1040e0440046c0c20100b08070340f11030b20441400c40600640f0343c0480550090700003240c990080c0116500c00420940c07100c128101401e07076403861660388a282d85403400110034011554903031894803203074010140c48040720410100d5298031002c20b1003e06000483d100d98401c07490140c2d80c1e0b6070b41d404e10343c01c1c000042901115000d00440b200070b86030f103c002042c28192620380e00580317003060023516018404031340c070020810003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 476621205 1250 476619955 476619967
    0x60525050a030b100e102c030c06031b0d09080f0a0e030d021002252108041707111005040501092114101b08060a03020303031303050d0e0114010b 64
    0xa00482c00d81d680c11002d903508446590111001e5440000201c3c7d0b014201100c3d0040c00c06a0201d10000420600241c041d541800c4120041c8070301408161030003406942c03841000c10300000f408010341614803000d400800c0c070b000c481d25001d00071f50044404040c180b01c0040c0c8101c5854100f8100c00d24041d056004010242410600a44030310281007024511031f0001900000280402981248009035021524034801c1500d4100000303954844844080c0c00b14070f0783c094045015030001d41c4600e80003540039414010007400c40c0516403201c0c2c002c4441944140c40c040041e1134200300d9001c21a02c68403020344e01c90400300003500c3c0d00d1095001401d06104168034110030014080d03401022540112030b02900284580b03000d0a00781032284446111303140c010600c0e00201c0c20b50620024860584507240c3c55200c100500c0341011179400082c4d00365100308045500000b07100300d8020654080d240050034140e80c803a1000a071801008044003581d160340034803040e500c004404500400d000d04405207090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 476622455 1250 476621205 476621207
    0x7140f0a1d090a0c021e0d0801060f0c0311030d1109040b04050112031b08030a021306050306030a08090109051201050a0c022404020111160806060f0d060525050a030b10 74
    0x4000405400f1119190107032440a10700030010f03880e081000400c440d80925404201c10703910010381c0f0b0140300041c0c8032000010054054191050040d4842da50480d6450311910280c0c1c0a00d01609400000d11040080c2c0a90f102e1610680c40e6921400004a030795255840030441030ba10380d500824840d030310f0003004025441c0c800910340500b0798941020340c00131500c0c00d868001420b1103880030b0017100000003000034a01c420760040000d0700f4400c40d03000019480713000803505408200d0380250168440002c50003c9004180a44090681458010350302a1518040341d440e8004040011030741c0e444409204600c1480d0051000c160800e100800004450842c032041d01c1882c0411510301c140c00308041030a6921a0300d524182003000c900311040c1c2e20043c0f0705c007a043d01c95881001600d0240c140498400d240203460740d00400e000030000019200a915031a004040c080c0030088240808070b08007104082c03248504018000382c1d2030301601d514960130080e040d168240f0440d481442c520b40143c03001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 476623705 1250 476622455 476622469
    0xc01050f040c170601050d06020f0d02090a15020d08090c030706110d031440050c09091f0912020706180e0117013e0408030306060307140f0a1d 63
    0x4600407140100e180d00036048c103000034490344c3c200000c100400141060f43c0c05c42a0014001e494086e0b41c038038503591340d40943c15000ac102b10141c00060300304410101291303201707008254100040d030081da206540f44030000b9140c000280d0217000424400c0880f0401003030140f00d820140a5035040c144112855911400c8000c0b40013002a50b85c0302215103680c1c1d0f40c500d100c1e00800070440d1000c40106868565101600040c001202129a031040c40752002243c1848107a1900031a4035500400300c0039080300c0100781c3c042c0841e040414569603042c414010074501e81c00604080380e181c0281126500b0824000c1c005100c8280c0101004209a42000481940b00340c2c07504451800c243c884462071020941405016512182805070300009060124540700301b010070a09455140482020348101780c0451060055124a4210b6081840060390904041c0b0085521403880d00d40312840318026080711b0743d160401c0c50110b1440d1400b00e040d8024513008110b541d081a4030100c28070301596034400240d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 476624955 1250 476623705 476623709
    0x31005070c1b09090c0e0601020718020717040e09070906030f0206031909061b081608070c12090515130306021305090405030c010b100903020f01050c01050f040c170601 74
    0x84030102d04901e4404410204a08050222141d05200403000d6003403e50542c251400f03020300ca8401e40c40402d105600000e1000d00300c0f02078540e1400c0c2d140390401c1500c029040400c0680f0304400d00c0b510750700c88480340001040540415401084c00d0b06100d8506498802150003030400513207010720a2000c1503456500d10182a8101c2d48282d0700d55400c1e0081001ca91340c1c10a82120340d0030262000100840e0790880148034400b105101c03440c071a43c42c012a0b03004804da030360b03415652041d0001103440d40b0a00c0d100340e00c4280f6003880384070039086a0b541807180341c030002074000240710b40342d007441649850715004201741c01001c00a8100b490b40d00c610b0b81c401e0700c0b51000512191780010b000c141101d007640300d10020a0020000003c030b25040c14003c0e141e61246209069551034400480314901e004801c40580c41c4180d44c0e04840b071360450303003801201502200b50030305200043c05a110119401d009840c03040641e40c1c0740c0c0034681042d11344114110f69030303040000280961920600d60120010307403141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 476626205 1250 476624955 476624963
    0x40b090a110631030b0601050f090d080712081b03070f030e010e031303110406080307080703050f04081e030418020313020d0b040c0929010e100e031005070c 69
    0x154800200c048003050f1400c1c00d200300301c54a0314034641c0c000684020310b4001241d00440b40000a681c50000465151242180050900000b8800e241060400400344103680d44100c480c24544880d586880c1401600c803403007880006c00900070002401e0100040781c01e1741c00d03205100c1e425820034a20251100c1000400310301010b60b40d50000e41c10b10425006050314503e41002c0e00d03603901c1000540c2140c5946400141d483c6100c04a1014140c02c1ca4843c00c03045403200400765050080350343d031308c007039070b0348045820b0b0100202442842c820022240061000308038010040c1260b01400c4020102080e866140441680084c0000c101f81100d20000c072003480c0d90014010b84e00c4d640e246a0100014811074080d420510384800d00081058030070b840e0307000c4e03400743d01684d403103c1d40d4100032401d5030030f000b0740c000301034014071080304515802a03202c696910050401413030354403511001c42c01604e060860240000c06182000c2e02e142420b00c00c168141c401e00100380018546070038090003013441008010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 476627455 1250 476626205 476626207
    0x6080c0105030705210117210915120a0504021003150909050a05010509071e050f0904141005072c0d031106010603050a060b070c061101060b040e040b090a1106 70
    0x80781c0f14610326019448800f40c4030f062211947c6654131480450010051040d56108050001d1089410351030b080701c0a9441c142d80615004500b014442c0c0504000c1c84031030340d05000e021036682d000300001014828a6402d82c00146840c040c010002d40c81e515021000c149031030a8080028003150060100503503a01000c0840c210045243c001d1401500300c1003e1b04035441c044c00d114880b007003c2600c10840e0321a400b800f4403880c030011505045500c03446040c1e0303c0007020b0781c6003130507091800071941d0113801162500c9c2030b654200c01040c20f001d1032200c0d50800580d680100700d030b9190032040726144268045101805004001703424100f140721442c6061185e14103907035140406100709a081016002201610320390b59482030084c1c0070780000d40c1d800c2c00c3c0f5818140c011442005100c00d642d07500e034010400c0c100c0c40e4508001618013a00d002d504500a540b90f843c0402d20620100040c4010140031610705018606414102d02c1312070f010b050382c42103802205818010420900c0c070f800200c101200c1d21 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 476628705 1250 476627455 476627467
    0x9031707020a02280503030301060f0e0a150305070807051608090f0d030207181b030e03041d0a0b040c0504091104051008060301110c030f0c030f070b0a06080c0105030705 75
    0xe078546800c06030025440220240c1d08800c00103d8030026241076a076008804c0c00030786a03000c158403404240149000150303440c01000111f4824861810b0752034000e44040c4a590b02e4899002440403500b5500010980b00c4050085455006001ca0740c0030001e4a011810315690000185c503030208404050186240840c034034415549002c0700069090340204820589001031170041d440b91340c20300c1030a18240507181d400c09150214052111a0f01203000c03490360b40e0000c0042500103012032150020144400d20010581010101e04600c1c0c14140c0180d60880f841d0180c1c2550a503174007080c1c40c5008505103651142095000015941030303415158010414144071001c0710780c1801503620035503110036410307480c6048540081005000d0307070341900203010381c2c2d2040c8450310a601c10f00200034410340c07041050743c01c0507002c035018040b18503088050340d1074040103030820800f0750004d884c103880c1d00800300f05204009400740b04400c010070604025120741031045002034014000101040144000007070340e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 476629955 1250 476628705 476628707
    0x10c050c06040e1504090f0303054206090901061215061115061c020303071205030105130e07090b0d060c02030d0b0f030303040f1a150a0909031707 65
    0x9010030008000e0521511180e54034a225500042a903031000101802e0b001005542414043c44210300c1c5c01005c2c0c0c0d444002d40b550224000d000c000d01000720b170108004948512400d101d840703020101c060340c0380344c80c2c14115125038101c8a03c140d0b9462080c007040010352060f442d0504043c0c1150500d0802c02903400e444218100a008070b001c403145203200092021071525004881c40e80541e0040c8c0840304144040340095422800031f40d01903500c580c0700082c0307868200041902810951020b42a039003082c1d8990b4a12890f034072180c00c14801b11f10040010b12243c24048041d03803140d841440c05203e007a2101c8070381620780b1154000d00059030b0305e403401d19150340c990032180d01d031a0758049001c1007020f054080080d102c0d0000c98001f060b95003042c660300084d14100e411200040c01c000e0103545152240c2e82d90070511140742c0002c8030320203c60300d4224299094804594441d0080250b181d500a01500c10049240d010b60042402d0a02c0c01c031004010aa10000040f0440b082a02c0300246440d2110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 476631205 1250 476629955 476629963
    0x31c0e0f0907142206080c0c060406051306050a090308091204050904060905100b040f06050303090d05070e0f06010201060905010b0703120e0709091b06050d180c030803090c01050414010c05 83
    0x200c11301031600d0701400e044501800b1038520440700c890b69820416103e2640c0072100b48202503a00800b68404000324021480592107980c102c00e4040b0f0b00d00d010b00c004d17551b48064031170880d0292101d81e0755a100e0710038150412105a0b021848c5009448844442d0703524818500450080602680144000408109447c0d00c104402ca4125007120f01c002180900c18001d0429021801d00590414880510401e03103409070b10240c40000f00a18242000481841035401032020162010311940000203804410201d01a005900b0381100c0c110714504031001a0a440259001b846a94600001004016541d038255100782e42d161600300c0305a100c0840200c09403076100c5402d219800380307080000340c0820360345c01801e400d031065401e9900d101045105a88031551403140d100030920070044042230002941c094290841c1ca1110104c01240a80b280002c00d40c16400446003544000140080343e90304000244001609203002c5181c2410001d000780c1c01d02d01d410301c5905001d4420b40390807c01c00284 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 476632455 1250 476631205 476631217
    0xf4c090506010503071b080f1206040b01050a02030a05070c0f0f170307120c03020f07080102040603060e040b04030c0f12050705150c0405060a02010605040f150b270d02031c0e0f090714 81
    0x31060b10b4494027140c410740f200000640390184034516081c0c80c11405d5008000341ea400c500c2a401550078240b603841c094400d03501100c001c44450a8940c1e01180ca280c8000b40390014165150401044600340310081e0f40761208000641200e80c410711030000010301c480001c442003000c41c908001c1214441c0b60903032030403a20715542d01c110b01032582c003c02c408005602620850b0302c07543d024005996030b4203100c2c021001c140c8018089089010004012a0013000309408541c030500c0d021209102d04d840e4446615841042c001c00101c0003d000414071034104620f0050f480c04051000d080e091814000300e1078801c522403036000340004507608030514000e40c0310000070b0078050000d00044c200c0d400404001c0c405004409291003200d00301140e01207100055138890300c665150402080c500041c40201560545400c1707600410100030480140c4050040c0007481d0684d020480c2840007040c0b000e0090720000040902031401c00c4e4280010350345e4120709130342010391820a00d0010028441010480c441e803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 476633705 1250 476632455 476632477
    0x40807140d0c03060506011404030b0c030c2b110913180b1005240a0302090406081e010c0c050a0209060103090506100603050f4c090506010503071b08 66
    0x4200200341304164112520403403099880d101040045441511103010300c0c0409083c50800c40e000449403040c01b0002c5420400c060700306814105400c0d4a0040b514413040303100006801900610300c107014501403a2050040107070b0075403c00d43c008010600e04081807504050f0715440e805520003241903442444e01e01e94110451800c6490850041c1152054a11802e80501c9100e0010218a0129514a200000070900103440c003a441d1a04402035000b24021907882036a6400000340050200320005162101c4041400d004042d44070090858006420036418804207541c0d0000290005c030300321803030340c0e0f04540340f840645440300101e00404107904000c08500c03c1c0d01c05d0004801a01940408407030040d5411b00160780c810881203d0400103031001c42da0041c01460030801581c2c801000425010285202810300380352074541d220010a645590200c6294540305100141050140170b501c132000b0b003402c920354200000c00915012030780e0400481d445c030070104c600402141c541118036901007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 476634955 1250 476633705 476633723
    0xf1504060303090e0c0c061b0f0a020a1709030c130908040e090f15062202040f030614011a070602040e0709061106010321110a0b040b0c040807140d 65
    0x2203140180ca00c1e000f074007541e00510f25880c0080d0704460740c0000c039120601d00c00c018080035111000b40384004030030380c160940741e2402408030f0060001140090160a60b1135402814118aa03090402c2c00d200d18081c0d900540d40704000c1c0d100b0a480010b200b800342442a501c40c034007640d0b5458484010005c03144003c0c55203800180c00501b600b110042c1342c0c0140d111038245c1c0c000c0000124404e030760f450300c0b030343c580b5060407039030b000540030315146a4030300c444861810720482040f0304c501c24a00320ba02035000f032015054074190074400d00a2601c00d292141d0030185a40120754103140040081d1556180f0110300b00400051520420034030b0f4040c0c0d801002c01e940d0348440c3d403c041c5800345c40d8aa81c0c1c0a80380000d10701781090300c4101e85c0091503504894101e000c01000001c004050004041000e5008040c82000000c2091050081268500f8503000c1c42464140f4200703031400c041410340203424554510030600050211b0040441c01000302d614020340d41003580b25960100ea14500001006012102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 476636205 1250 476634955 476634959
    0x1020c13060501090b09010c150e0604260c030d180c091b030911010f0e06070c03030237030c140607030f020a09050d080c070611160602060f150406 65
    0x2001c0e0090030984401340ca4000016403100036025940c022544a03e0000351500e401402003850134180c40d1008002c0301e40411101d03907480c1e00e1450050b00340c03411540d41c0e040c1d10a0403c11005d8111070301c20b054200b60a40d1910b403001140580c0d80c02020340c0911000d0707540c1c1540303201d00c041345440d06480d0341c0144004107113540c625650300108880c8d0f2000105a2410031000f0805119101e00e0583d5640552100d9002182c007004540da80d80510300001488100d800070142c4c0d80d50139000d845503c0c81072860520b501d003540fa0090030704103c00c2e184aa40c9074100340710140444140c0030f0168a031840b05110000749028141141c1d40c51365030901401461003080d04140c280f902003411031007658162414440c3d081070480c110228890303c0060000240344440038012403605104102c4154020000c0c0e84c00c1202124903681003a120b40d220a0218120600050040328107220030080c0c201e02c2e4841e0302e402407529102a407100001000000d8500421b0300040b08130020400b90b240400c0003a0003040419 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 476637455 1250 476636205 476636239
    0xc0e070201230420090f060a080712020a08060105010206070c0611030c07020108012705040204020c03120a060f0303210609020c010f0513020a0302010f0e03030a03050601120501080d0c0201020c 85
    0xc0c0540b015a50000c3c0e180750300c10000d6120070300326410131010b0034012181d91000e40320015494040c1120745d100180c141d00284801040210b003020300b20302c89203002004403d01c104881c00400c0d501c00021600310710010402680c005c02c1c0154002040d007805011840345151000c02051400d80c84010b0306004010300c400064090050840b8078802c0c3c0b216040f60342c90300c4440b41409440002072141c06404d8848441c011419007040d504644040c101609207241c0d02000c90560300091002002c20180031308101c144034241c0100130040ca6000c00102e00366007141c8004100003014034007885c001c00101e508807005c00305540a07100915821341d08648860640610368040c10380030481004090070b000118117141c01188900ca015603000307081d201a603107160300664102912180341c405000c40306d0001c094644091000f44051101540d000816281540000d0428204102048042898a00140607040c00001c1d02040c40c0c010f81007c1d6000a20380c0b0040f0f183c0342031000541e40101c4030300c004400d4a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 476638705 1250 476637455 476637521
    0xa05100e030d081e010b0301120507030f06050f0a02070b0c09180702010c0e460305011e0504030c0b0603030702031204080606191e0801140702010f090c0e070201 71
    0x113218201c3c404c00c42c403401c003a84610000d4003802448180c500c10030040100344004c4801c180118458026184010364946030110442602ca81c10b81c6e80b1074a400400a00041c1c400c440c2d0303840159288110f0506c450707521498110302c2c00600c80058503c000503400510381d00d441410b44001301c00190b1601c280ba21000003400f82c0701e8007581d00d0114824020240c1d061803d400b03c040c8035006c0c1000410f04200650b0141054607200580c80ca5170b003c440940f05025910b041d080c1702450144002051071000c1c20300d0140039010481070008018508002c4c0000030381e0125002300310740d400100c0745403151200800241503114495000b036040c4244200340405c0840d01c5d02420450789034200b540c800b941d5070400c2c41040d00c143d140c071a43c840c1e514130007440001c003406400045039003184801c0051319117501500d42150700e900310b0301c40d545c0002010480c0c8641e090060880b0104188000d002d40b860680d113540c00d0000318020544c008042d140000e04a501c01d60180d05000b030030301942d04210390a0407d803030350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 476639955 1250 476638705 476638711
    0x17040b0c010b0f030109020f061b030a0201090b0c040605120907082401120b0f0709090903082e050d11090709080c100f080612060c130e060a05100e030d08 68
    0x51078014183c0c0d1484c0c60180714401e8007507000b0f4100f0030050b070844204542540986480c00c085040010b04a81869042014005400854000284403803441c10201c012003401410925690010072007842a00d81c0207080c1c4d014410b031003507250996220700d0031a604000c115004008107100f84038682c0003842c0c2702c1c1095402000141d10b83e854598031901a0741e44a821100d026240d07150384400710b500d903000010b07861ba1111051501042032510b55541d00c0a0351020007003130300010041018881608845051615181082d002c11601c40300048001e10444c1d01c28403555101c3c080c8201000d060051400c8a4441c1b6007004001e281e203840d015402408110700c034016180c69215144601d04103042900c0d6450010805884069403850400c2d8121500d200040500b40c11454107034416030200b0040048a025804c03141e601074582188240b2a494008140d1102d0f048112076424449140c80312881c1c0c2c400d0300d2003510400b100d12420f050554107625100d40c0c49400d44074156000b04020340c40301010380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 476641205 1250 476639955 476639959
    0x50d1a092d0105010c12030608030304140114100b0a14070f03021009020105161b0e01060f05090d0b100f030c030b0a0b151303080d020309120c070317040b0c010b 71
    0x8010711624071486070300424001d050114020700c5803440841e83c245035407041e064007880c2c085021a1691038050035600706039421950b450341018038014070b00c000c1c00f070750303908030b0391261400824078000c4e240c0d2812660030300c1960303107a541c000341025606209003000714800c01c141301c007265074011914010319400804d41040e030060182c4205450300c442140035003c0b07160380513598a410180d804008901d400802e00f8215201505001c58500a451060403030000b004003c0d28000d0645c5012405041034420302100c07000c2110030404840540c0e24000c003a002290000e45c20301e140d90b182800300110303100541200703000340180d00700081004089950030781528800e001d180d90302d403a078941d00c07010780702d071818400d41c000203100030f03001019942c4028041c1c0400110294041c55038a890f610215400100d0300b08a1a40000401510060400682200c00144815149040000790250b512807002d408000c203078922a540013034a0100200554001d882c0420440e84e40780e10520409009010010fa4a8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 476642455 1250 476641205 476641261
    0xc0512010b1e0f0306010b070b060a17010504050d021f18140703050d080c071119060c1e05030a0e01120e0a020f030613020f12120c011407050d1a09 65
    0x1070341c04d01255041c12181058161403c1144550300e10210740c40040610340c00840304080011000d8200c4119810020040000906801c0606140e420074444e00c9039803040d5806034240c2e8030002144003c4080e03511003810009060808400c8608052400c4074016100301104039598020807c00300700b500032607100b070301200ca003c1c0c0c0d0910240da03041c20403104422200c0041c0300751800b0036440913112452280080550a042c1c203142c4a42107a0300f2160400d000085d1a00440c10400500040410550104104070138030f07641c841c0c4e192652482610340700c0040020303c1c101421b80b80d004d061501201254001c00b40847c2007410709007544c0d001503400c240e1090760000795804039802c01103001d90003808614000d0040c10841d400b8481c00c2600c420f07859420250319828142203140c14403850031603001c0800510707581c11002e48000d094601440310240c1c031040030b109024890340c0010407600206039407800400c0e00b05803042400304161202d00d105400199000800c8041c80c00c5402c140245607400d0f10301c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 476643705 1250 476642455 476642479
    0x705040f060f091403010b04150305060c07081e04081e0105060a0f1e033005091c08070b0a06060212031e0c0c0a03020a031b0c0512010b1e 61
    0x403200100d20895030302c00b148a00c0790621120f81e07250001c0039854000750001c0b60a0455102287c110360400003069102404284140108407040c4010b6803c04a98040c150500702103890f001350510400c4034071003495040f4000c00c41031f008900240d800802c1e036003003030300d034491003007030b808030719000c400751030a00320b500e00740010b0001d260102290043c0c030660b00c160005141070014000065041c015018210318060800000045000200c03403200c05049165000c42d0480c44003540007403c5201c081c0b0240002402141c40548840b401c800202e8a40c800c25144103d0608100e40c0922420001030440c0e10480204552804a604400c0485480d6402c9620480c4829046000c40c001a0b8003444089841c0e01d4042e00300e10548443c035001074500d81c007685401c0c000c181662801140d90404c0740560490386040c030615810481c035904000c0c080924250703450a980d10f884100d074650107128030407035600d5105094480c00f54051424a000a00500002500c1c21208000c403507103103040700d1154071b0170348107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 476644955 1250 476643705 476643707
    0x13151509032904120504030c0b040905011a181c0b06010e010c170702010306050a030f0213050c030a1d120301030605090304050319030e0a2702090f130e060705040f06 73
    0x1640d8400441d0b01005220303a12260740351030b0b00e91800d00581040007000d1201202144260910900800002801c0760350749140c0301390305083c1c580c1607110f520607820384950303241181b2109046603408501c00c0d605002c607158040024805c550365269102e18049008481c204000c3c01500312401500c00342c881a29501501004440d52054288014810844000e00c002c40c410b8140c0645491441410b01144070340c3c50b4030201700c4003160359005540001c5d00350401c0066040040d2440c0c0c0307644544c101031210346005421090140f01c05411700c0105c40d0f40d400f244940409445101414010710782c1580c100040134480c0d01d10b03030b4100b0301003501c44a2500c004189495000000c403030494101801504d000302d054003980e4206034104a0a41c107000d058464100c940d40c0720f20b08080580f03450201c500e140341000c6004041024030403403c00f441d51041080e13000715900e8aa00c0c0102c031384212011210103a4612485001d4032500d955140700b44646000d001089070050060310584050101850385155a910 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 476646205 1250 476644955 476645003
    0x717031209010b2e0e1f12060b0f03041104091502040911131707031e11010201060302060d15170109030f0f050a200d02011b02010b1315150903 63
    0x2520003022030004d810042614042c0c40140c00c042801031041c00c0884414290240041e4404104000101a20700c443c1c0309052912404000e0300c0b00e15140c03405d04000c041c6050440c400508054000d1200160503500da5545400041565901029501e80324030840a070740041d4000d405051205828804144024404d91040d264412803003102710781958030740040e5a070082d07000c1840b1100c034000c01c4004400b040c141a003400c50380802c50790085001480d400c101500f5085074552a0442e418040300304090b94659054843d200c0403030000282043c1c8640341099280300d154030542054160300410382c000001036214810760ba000e034480410101607104201e6007001c54410200c00f040060111105007031041a542c2c2d448860300d00360001e03107909100036900d4800380001560050b07450304909485403911a0110f107440195000070f101c2030300c02c03a00040c031050040100100081d07592140b00103028107410704200030003072050818074000314040c0c001e0501d540d6004c2540d11045000c5c00c2154088898 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 476647455 1250 476646205 476646259
    0xe07051302090a121506080d080901290f03010e0d090e0c04060804060b030105181002090901090f0902060319050c0309060f093d0902030717031209010b 67
    0x20820f61205081004034070300d018441c0800d41d03044011070524040d404452003400080c00c20300c402405041e2080100a080c002c0c02131140d10745034103115030741d0418243c8805941101c28001410042100002c0104040e00b032101100d61b03045d0300300b021b0442d0880001ca64803052204da81c0d1400e590030349460400104400940d09440580d90401082000e607204444450300548241c43c086005110440082c1c02e40f00c0580b0100240701401c41d680780103a2040106520301d114100043d400c1c603860b01c0005820180c14030447c07030000e8880c0703600030090b15240e110b916031540c001c2c001522820140c9040200d10107100600440070f2401d030208401c8400107044d24460f41c41d280007041140d60707a6600c002a1000a0824450b07445900340d40030380a00354103002c61501481ca00050071414521400c0c408800301041c29885040c901304402e0050784000c5034080a44855041c2c040c00028880002d0b031a601c501d526a10707a01d24104144069004190000a64104210340c071842c50200d00014100080400f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 476648705 1250 476647455 476647459
    0x70605030a02090406050d031e081e0a060b030708070207080703080403140c100c020306010905040c231e1017011802070203060408090909030301080615040f0e0705130209 75
    0x1030000450905298000b030100500151010400301c0d901c0c0007194124100010440204030149102680350183c2c0c041054089542d1502c48618103040c0e021100005007800c02c80b0b0325205d00e00009280c0c00c41500b007280182600c400c8240e4900d8078200083c600306060300e03003c00500070b6007000908003000003001c100b03894200480314134081c550713540c07070030030302c181200030386441c0189a6118400d54444c0110740c0f414000d501c0c1d0b1110707480f0520405050041c142c03c6402e0941c500300038040895403005010064920380e40d5080c602d51030002c0541e50b1380c030700c031014954010b8012280200100394100403004011041d0341c603410074801480c043c1d40c0030000c00c01c480901524100104030039040c40796017034035015100c80014541070050300841d01700034007220203a81c1c032180003d0014442c01c19104a90b480b128003009035040d5410610707401d0326400d0161410500c05a01300e4005a96034690b030050f0044030710b201003001301318a003101c0b49885040a1203114801c00910340b42c000400c0072030003242d94039400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 476649955 1250 476648705 476648707
    0x3f0e0c0916090b0c15070320041a041211130c020c042702010f0309050106120506090d05161406070201092a0306020d090803090102040503070b0c0c0f3d02070605 71
    0x442c9070b00e9030b400c400041c40c0346d003090303144d005110041d00c816400b00c01c080b09a0000c65511070819a01400600c40324404c10359046042008201440544000240d29980445900a00d41200001800052849a01288851800120000c690b40004110550b918103a50900052890701040c943c4d070348090300b2040409981c4000580190b00c5108280900241401e0000340f612080d100e0508603455504002d1003503440744512014000104510395205a0b108001c00400000d13050050040c003032aa842d1821b603c1d9036a2751000c1140b140b00c0c00031117500320301c00c0360010301d098000203010306817980c01520030100c20000c03422081d0341da91640c000d0220701440411b0140c60355035110020350101c00782c9101030356209012030005654000441c044d90b010800581c90700d00303090030541880003550046014078020030a40c80d800354027240c40794004d0000c032282c5000c451180017158901480915258141c0d46141a0508605000d2000c0074449030200c19505662000902641e880100303004a90200f20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 476651205 1250 476649955 476649973
    0x4020d0b0703270c0509041203150b031e06010201050702150a020d020304030207090b030c150d0b12010914120f0d0b030d3f0e0c0916090b0c 62
    0x281810301160814120719000401d11142120101d410411100d2014042410102c000074424490301c44005041c044540d02001c0c20140d4030421240d409545d50014151240b64540c441d041d03401c0c00d040100307820003415642e8a0110b20701d0b40d860441da100c401500e2102004030b001944148507807403080c06c2a40040a00315940a54214000741c000c0000c610316400300720060741824580061800390384260020000c250074440c0450a441104034114002e900c080701800080c0c2d20028929140c54a042c8042c3d80d811041d040c220280001030300e1f0ba50445905141500c01c1b4005510078505240120303600003c42c480010310b5a110510086ca81001550500c600185c1c0e000000c000c0c03c00000c90000040d5118071800800e0800d40e0f524022004250340c4040000d1039003c040342c0b866201290a00c842c1c1c4110009420a5034508803a940140709903100412101c1e02c4041210840c3c0840c0180031001b11700c1e150788445589013400c403111000484695000481008000580705404400009080ba4203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 476652455 1250 476651205 476651213
    0xb1b0f0c060c0f011d1c0f0c050327031b10030e07080f0d090b280c020a14101403010e0601090b0c0106142422060c05010f0504020d 58
    0x1030003480c00e41099000e8401c0744641800c09200b0b81602d00d06800217003503060b031011340b03560515070401d00c08030314102050044103502c0d900203070042c0d03050003d041036446400c05050880c90360042d00c14a82100c440502c0fa041e400381861244030340a407040341141c2e400c908041c000980c0306000200d494102c041c0c01c82005a050082d04021202c03201c0d4001c8a49450f5290740c06480d0031b00e00c00c60307442030b6001034485440c0790740d03c14445805401c64410140c90202444603069215140c010f50002c80748070140510802446007003030424098000340400051a100c48545c50400381c8440050f106500e03451502050318000ca1401d9164178107100d0789421a8684020280d10f100001c1045040207481007000c07507010031001c06080d0600743c180000901a0030031f918541919416505940b24a940103000e4041529000080d007060641e20006922000d5240242c000f00340014040c440d4048040c502207079051344002500b2595006030000d1054513060351191085030407d07600a900712000701c40c030304085 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 476653705 1250 476652455 476652457
    0x20a0504140d0210030b010813030203070f03030e030c0f1605090a0527010f0b1903061806021b0c01230a0215011202130c020717010204030c0b1b0f0c06 67
    0x403401c090401c1c41000401c2e0f000604450b400c0c10104082981c40580e4025175030300450895000c03507005004c5548205079200a1b5803030260301c9006000503480d4407a9420940709802001110400d0000c40786c441120388116600c410b8460b00400881c4180f0003507141c02003030072911504030741010781449201d40364001c80d00068000200720415840da803000240000408140d0f900c04141c0d0480001680d1481800107000c2d0740380041000d2048201c0200da08030070301746071210800c4903842031001628000c600c1030b100e0403041404018008a00c0860b52488041c42603000072580a04d20381982d40c85da03040401580d0300c0025145c5040d0848402c041c0c40810000341000709400d1040d0300450344182d49000014038035500903002000340180c2c030050a006c50401d98816160706080120030f012421800000943d036450f2071081001c2c2c0c3c648440d0a985e502c1080d412070b406190003802c00d0b8001c940b166890311056018194448800543c805c40403a0840007050003a40500320601a0498041050070000b035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 476654955 1250 476653705 476653739
    0x1060503061504211a0408090d0f0f060c09170d050d09020a08010213060203070203100c050c030c03030f0106020f0606060a20010605100f090b07170c0f0f01020a0504 73
    0x250480c10080402e2918042001c00820800300040500000e100d1414005c0400480840c95030b0984202c2444002203402099980d060000c2e113824a0030a610304000001200c03e60b4081e0240166172120410b10041d40c0201a1100c51030f11180703c0c0560310600344c1941a40706206c10780d60b80081454a801501c1080200000000c109000ca46042e1031b0b00010600c040f558005405603500091081445031701842d19030080109002940c203010450300483e8480303013185840c80c00c00780d0310300e040c160086c024401e1b1090761444400322504d0300c500603680e50382c0c0d80c01a180c078041c001c1c004000155180c8006108401c008010300942404c0e12202d0a200d56070b00510401d50501000d043d2010251492a12812502025000201b2814688010300c101c60200c1c600240400450306075075692150031580070411104020002692040300b0b062039864050402c0310f1800900d4000303182101c4e00c00001d4801511201d1034261090240c2c00200c8508030b1140ca000280440c0d4240000c00c0b0103482d10006542c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 476656205 1250 476654955 476654989
    0x60b03071805190203130203060109090f11060f0304080403330c140c030d050a0b031207080d1a150a0207051314091f06060801030204050601090e090705180106050306 73
    0x40f5181100402c82c2c00e1740c004562034140c5414420101065107810041c4900402e402e0300c0c00c000c0b00c0850344982c0c171501c10800001c0e0500722400000603582c1c49440846e40e03241d50100b81142c40741002e213401c1c401640320340b10980d942034158459041b01d03074441d000000c181c29060131000003002c0c1c450460b00504000e940f940b050081c9801181c02240140c0d000341200740d0800041c40d03413404800c00042c2140c401500f41f081180c6000c6866205450004004656492100c0c0441e103400d0300e85010400c44c42aa001015018204038182c1459614102030200f07900d001c940031041007003401d401080c94096020501c0040c0c0c010b48d020081c03424018501405525800b2012904402c0c400c502c41c1c0700381042c0d0311544543d0203059241042500204100d4208001100c1409607920380314000b0310004d0103001c007a2080390727540082a01380e800f4449a0008000c0c000244070b2520300310111680f00c2030070340b0990b1f00821081c49080c01189401010b00e050381d04d40e071034203800e41e190034050180182d8102d11801e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 476657455 1250 476656205 476656231
    0x40606030203030406030e15060d02120a06020403080901030f1a01030c0e0607030e0108100501090e1e040302030307020f060105240408030c010203151c11030705130207060b03071805 80
    0x20001d0784042c0018000b030100c980700401d0705040112418a01445a00ba8007402c54a1100f807000640e16690401e10858049aaa08858403c01e00140c200303600100014121480081c001007003229520141181e020249c0f020020300c401d1906450a5805511805c2ea800303070b20952510041d030181d400040c511040b46005840444d00c1004904284e01140f002d401040a90200d10080e40e4042e036560740c408160701150781c28500e0a03001801250003401452405428080080c00b0010f1000400c003181c81141d10034002402d1500f40039480b07601c03e0b1010030050141d244481030080c00003e03c00d04882c805400c4102c004101c103200901e124070100a03955500003040006140784041020708102c248800c00141d4a04000080719155a12040442c1c05110400c4000c0300c03140303316003034181c401e0300204100010020200042d06060380d582005900010b0740c26242e4116210340e02501e541c9220301401c1100c08401400c050752001d1620403005032900c01c1d24002035001080c1c110540020841c0840 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 476658705 1250 476657455 476657459
    0x90604020a180f180c050111030d053309010501090803030a090201022a1306080d18050406080714030303040f0311030910080406060608091002090a030b04030c150209090f040606 78
    0x5507098502510b5080881032104d2120414840a1001c982c014039090825205501d5801501d90b1240161980c03141100d603182c001500d065900c404038881c0300008500c2200c1004031186041000c00081d42450250511000100311540142042c0058801d080000d508543d5080a180094026014100e0442c0500a500b140141d00305807000e145580f0b503035142c00d80307105400a00001d1500202401d00e4181812010051140c001c43c0c20341e80c80ca41841c0c0503503583c542041944c401c44d80d9034031031a0064035044000408d01c4000c601c0a042d19801d44400e00903101d01020160340380010340d00034108160622002001030302410540203210044001e03a41841420310000b1034000c0401001f03000700b4099000c2004219040c8203860152113682031075075450800c1043d0507070340c0700290410301c10540d0000d1034044c0c1d0790740e4142d448011356110300c0b0700950385440d10b4020080000c0c004e00316040c1c4900980140760b803038103000756000f500014000c8580b0b50b459042000b682b10700500300b031354525038807000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 476659955 1250 476658705 476658731
    0x10080f0a0203090a080c2e0e12090910030b0108031314030c06030711010203040c05010206060301061a0d02040801060902130608040803060103091e060203160804050a08073305090604020a18 83
    0x4000d81f204510115003501a0079400f00d4030030742c1c0440103030305d030250000c0c1858a0004500c0003625a03440c0103a401c03550030740c1c1c1d0010540700340c1100e400151004070071400001c1c4400c1c001000b0001c0c201d00005044201c1d40e40e07030404002c4500b048940c0d905400850142da0715041600155074481c0d0f0b64075081c0c0c00305921098890880e40300b55425948501d01c00e8051006507010440203800180580080001038900202d0740c506141c7d203030341e0340507c04000a022540084580640300509030000017041020f40e80e4104100940c80b080811030104003002000680368043d504641c03085800003240c91455072001d00450050001e4581141d40714007902082170009030f0541c40c2040c084c460040103039281080301504001501405507c5c0c100a9290208400103502040d000c4025034442c10307140c2c03503d07643d140201c000944100d40e4402e500c41402c07081d03e1083c41400306101e490b03107503408101540310b0600094407203804803006500411100310801180030851490810726209080c0041d2540320054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 476661205 1250 476659955 476659993
    0xb1219020c030406031d0d03021b060f0915040b010504020a0504090c0909050c07050703080a0219030909060e070c11190f1403030304030c0803060a0510080f0a0203090a080c 76
    0x1042110741c8045024404903400d40b140c4040121b102d904118060040d01d1015610a06001403104042d00400d80b0700000048814045520011b81d0564a8500d0600d1000781c0d4480c080b1041101882809181030445c400802038500682d005082d80115a003010b050001940c003121115080100070400011030704601d02c02d91510440e5035942c0400640342409400985601402d50b0482100802001d0001140011410f00301d980c889520358894081c840107030b08286c02060940e031200c41d0310390101c040540c4000c8220a45901e44010046aa2582c0c0c60070317410402120054085500b05000c080400d43da00b08007949004000d05684100401201d0030041c03445030b0340a0030030700d12101c0c4140800d1801482031121428245d00440c10f514090b00d004180c103602040141c00a04000046049a1156040342001d8500074105e43c0d000207407120001caca04442150241801d80e165808604c48034114002c4901a442c01c20041031340c062140c99810546e4001d21a0343c4045c45003121603401d0100b419 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 476662455 1250 476661205 476661217
    0x3130c03020618090106020313090f060302040c0c030201180209060607050a0c0b0714030f0a050d0e06040b04021c0201050a050f04090507091802071a040303140f0709050a0b121902 79
    0x110032140e1803051209000d01000186c203c88191b40062101004028400036808100d452000c030105060000300350709401002d10342c1000e13412a050400c203043d15900100e0841d078451282d4006c110f41c0c0003514080d102101009802540a40c00300045001071902c40d028142450294080c0c401c5908240d03a5000c48100c168808115004041513641c24081c2285140d0b44118110000d03624001010321401c003140300b003160490500001049460000b03c00303500c1400345042c803404071881400e00c0d0801c0c0c550a0350032103040340301340c21000c540b005030705420400c10011681030b10744d41d003020030342e00c1d043d1955003000004840e858000d00c0001407031903440c0210340c024800350321000c2010381050a0b41403030008032182345282c0b41c010007404002820700001d00c038404828000401d569216480d088000c1c0c031150701c402006034403c3c400c1c0000301c9000842c4601520280d00e601d07403a0355841050145180044c46605c0314041c0034070004a44018a2041e0743d4031018184d10b00020324800c507000d01c00c0f60044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 476663705 1250 476662455 476662477
    0x1f120c020607090806090c010c1a0c090f03030c0c0f0310061d09070e061c050a061a0a14090603011e1e05010315110f0d050a0501120803130c030206 65
    0x1d4030500510079007200c0442c0180070ba14015080d60f00d8008030b602e80d03a4407413000d00750400501035441414001603030040250600d61451600c02030400d0140d010700394000c980c1081c40b03405c09441e218100c1c580081169601c1110b5000740058002d903900b0803505038110b012081d09406000920004036101d4410700c0040c00285140180203071581040c41400100203285031352940c001801800300c0c1c0b040111007548a03134100c0e5094995444120240c0c1a86c0848038000c2032441800d003550304008140d0002d0442c0c021700c12001c0002000341c010481c0781403280c8982850f90040035a442058244951403992040d1b014002040440307040b10f200c3c3d03080b5000d01da180d00a50782d9603c03240300d21810300800164200b0f244002d021650440e215a40248072034009103400e2aa00c1c240d9581c50161603043e1341c10080790003100f075124100c0d404008041c05084272441b40f4180381c03031700114110030f060080745c000e9074002090600f165140c402c031700e2100c0060041907a82c855007100002c0141c3d40c4400070000e960710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 476664955 1250 476663705 476663713
    0x915030f010f05070305130f080409020412150501050a18110a1e020c010906050a090506040b0c061b071b09020304030c03031a010807140d1404020109090b1f120c02 72
    0x30030741014110f940140c0107604141c10700081c40b0f00301000d9001140c1050700062001842022454001824490b0b035000561203400070a0014402c0c1060f40c220b40300b039001c3c8074902e602640c40c4040004a6500b4001c0c139070701c514407610a0008503070f03c3c103003d00040090280020507101090180c1d01d03030b4011552090000719026424101482c8441d03824104110354001000288016400030b844091603000b040104a4003146501e4214850311031980100005088195900d48944086070540d0041038010300a100d0780000c0707100e44000e001d8804030b030008602840e00344030259603401910601100001503070b12100002042e04521807000707500492103a100c1d10145d40c0e243c500a17041d5203050b01c6064102c920034540c0310301d03070340c101246503400003e41c030b04038112102107103a03040503000d219001c0301003520300341c001603600d040800c5d4540540c3c004d803640c01000e5a00d11a140c252480c0344c503c0e07908640210700c4d1140d00c2695001ca00c0c201b00c86814184a0722021345054030840f041c0078240c00041e80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 476666205 1250 476664955 476664971
    0x10c0c08010605120601080606100c020a080c01030c09121b09110405040c0503042109030c0e04061404080f0304060204090f0c030501140901140609030f01020415030c0c020915030f01 80
    0xd1300c1d10401c005011024050113440d8036000722103880e4000101541e000341c140340d241c0c1240c1d605c034600c02d00b20b0340d07030003880124629220102d50760340f000074400c0e1a001c00d141410000c40140110186021510f21070300d0303e496500540c0c2c4010010b54013004e40001942d14240116250125000750b0440342c440c12602c03920707540340904000580b0941000721081c41010014400881c0100c00340a2050b0250310b1b90405080301d8810440b1031031002e0380007a026820910000c0307040c121f81c032440e50085005a03c00c3c8820407488051032200541034800404224040101601c450807103805180c2c0140250001420716a803001403009032200113403004401e940d01d00c1c0515150b81c2503c1603e000d003002d0841c401d2000251030124220710018000d904060000d0420341d0b155a51f000308456104001600b598461210201c03258040d404c540107405c5038030303994150035840310b00c42e20401c0e8039900c8542e1600301c0500250207001140c1005040a44402c81c014981c850701c3d01d04000b4207090480f54400024080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 476667455 1250 476666205 476666209
    0x20c031f1d0c1f270f080c0a080d1b05030d0615110309010903060207021507031119080703030b010309080414090f060d03120209030613020306061210020702010c0c08010605 76
    0x71100150003900e0f01081070f010710016403000480d5410f4003503030400784280601e0400035182c42c896a004090882c41c0080c080703850f480110701070030b10341015114020343d00d84071141c0d540c1700e0221140340e60015440c0304000e0613001d1114001c498150003642524585800049802c050700c90f42d8000b1400c0b1415240c0d04092a603100e00c414203400c0b042406141024013000009182c1c02c21448080c003100c2e00440c07410150f540f6001d11549403103504044513911180d41c94054162200c08003c1d0398136000b155054084c6090102c2407101c4164800c0d1003d2402c0713001c0c0e40c254003c100e181951410103940d52100d0700003c0041000b88094008002c00040c90a10602045510b40e4000d0060007012381000502c0740c0c50316081a1803202590600f049d0700e0710201403c4002c028090002d030594944144c0d0280700c81c1c50859540101940d000f9001d039040d55482c00180116403242d600c031141c485c0d00000889603290402d40c05007030320301d00c14500801c0c540c0303441d1507800d14114540c105805036551603000304028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 476668705 1250 476667455 476667469
    0x4030c0b0f1c2c06090d080112020109090c111203010e0601030e0f1e0705040b03032d031608010b0307020715120f020301050a080a2103141501030507020c031f1d0c 72
    0x302445c08005c080e006580200149a0401841050107007022000e800c011603010721074400281000520800903005003000040610440310070003260390051303034261a041e0321403404aa042c1c5268000d8180a502c90100450050031015000c00317082c059070b260400520404d020b03242e01d8209070014032041128604640c0d09080300303548414421480c0409241060300d0110a6418500d501d41101d00482d103050180000801100d480c02010040001045660550030a00c030709001c40c10380e01c0345820303a00c0380c94028136803109039180c0001d80e00840080120007440701c92000a00301520b480d9081c400c0c40ca4030301084e580400c1e003000c40280c0200050280f42003540740b00000f0701c188001001950030036201c4503040f0780c0009840003a090403180440489000341c2140c54000a13407025019107107800c240311542c01902c081650b00003410400032403a10781c4005501c90b40103600030058025a64100540b005001c0064200c00750140c443c05c242c41d50705201d0b13002e070000b00ba62a01034048a20400f00b00049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 476669955 1250 476668705 476668711
    0x2070f050d031a0d03140a0512100b071101020f0d0201200f180f0607080a03060f0b0412140d1d011d06070510050c04030c0b0f1c2c06 59
    0x20145004200701c4041a55041c503c00508240d4010f1080320007070070100c2e0600324000c000c0014880001d2010142139018000348040e0015a40b40106510780748130060744c07116a072042420300c20003803090f4030104402c0b00b0000c580c400140102d45001142003841800d0070b200d01016000f6035561103980400c5141a100700c000c0d02c0c40844428030306a0360110b52010f50203400c920290340c0039200d1512000351540e0564140800e001070069031900e10354a0030503495805003803103000103410254006070100800c010403060743c95408080b4202400c00740940300c2c1c550210300988000010301e143c080d403840c0c00c0c410f4110718009582d0780c3c00070500e040e82864209070f40c443c0d80c504105140c10761111100c1074610700f0004c8001101c082d40c1e2100c0d02d0400c103191201d00c00c14521200d280009010041e100e0000610480341b050000c40f8000f0b03a569500c000d035010304138098a00c5d001c200314903c03098540b4584c2d007c0785005008005911170f00f0340145608030440f070420317000030301d070117182c07041c24500400400d58 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 476671205 1250 476669955 476669957
    0x7030905070f03030c14010b0d0b011706010506090613120f0c08160621060e1503010908030703150f080312061903030e0406080102031314190b1902070f050d 69
    0x41440c0f842d40d008042c0d110341a009085810702c80c2e50a0b035a980e0a4100000380311f8020000c00002c1140e0803c0d1440560030300c6002145444101509011070020506504aa40060540d41040c1590b024042c0907801814a00040340103900040360350003507004541106401841c00b850501c09500e8404083c4403a908a802103500c04052900b04080c0c04079800d050710300500d410440380010090765902003600c03414102d16141020400720300341041d2a42c880c400c01d5002c5242e84c41c0c7c0094410f01d4200c404201000c1e260358030420011354500d0103078110900902c003c4070082c0304642c3d551850391032a07100e034205c8030321500000740b00200140801c40481d00715004540c0e80c040b039107500c900200c030340c520342c80f00400707101500e282501659140e81c012002014100001c0d5034a107000403050342c800c9030102c0225048018856500c61070742000074000d074011160b06528004078410f448491041c4030042005c0c02107401011103404c0b00a0f00d0000c7c0c18204e00c00d251002d03091300c0c42c0c60003a050a2403084140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 476672455 1250 476671205 476671229
    0x71a130f180f020904020d0c020105010f08071401020a0f0609031206050306160530090313060e06090a0905040201080a0b061602040b0423010b04151809050703090507 73
    0x10261080c1c58600c07141101882070300095400001c500c0c980680514011035030b220f840854000159030503074110803aa5980350f402040260388810404503c010180200c000c2a0300c6034605000300350341d641044001040500444182800a0360b0302522446d982d4401c66050b6240d0045000f09604180c00c0075070000b1000043c05a5414840070a42c0c03a00010b001020300c610360541040018003c2c41201ca41440b015161407000841c6041030700e9440120032040f0404601000142d0b5855021007034400e5115010540206a45890400c486800e011406544d001a08101443c52555280d81d03031401007002041c0403581c1e15042c00050142c05008122840c11030800c1010707092036840d00d088410600030801a4203d8901d20700224004007940c40b02030360068a4452490000511080721102038444070005144a0fa01c8040341703001400395129215489001048540c85103005800080d5401450039011349040e0f0b80304104003c0d900c0581303e040c0803a68550003030041c064140000005803103481242 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 476673705 1250 476672455 476672459
    0x601090308121b0310050906061602120708102a09051e0301020304051f02090306061c051002030106030f0b030d0809150702030901080609040203060a0e071a130f 71
    0x22805a100d84112016000002e40c0010a40601c141c89002001d4603401401d0300d82c60908102100301510340941031155000350700042c21858000c044a500a4101511400c0d062a603400c0c0b1011000a8403518024000e608003c80c0c0610304100c1c0c0310030f80d0102c081c0070a400b48003900401c04800c1105001c51403e040300594010b5270341092a10007214400d58418201000b20200d042e4220749401907540e141d40008184000e10030006401c214803222285050603519110070460200e1040b20b42e0107805406c400009950380c82c14500004080c46181441c041100c030b903640d25401c096840701d6001d42294080014840d136175140c07255001d2081081d10410403a081d80c0700280d6075902e03c80700c0d18100002c4000003400e00700d0501c401d0304040c00100f8035a81d1801c2529010b500d0350044c800b0280010300420000e2a02e1518404141c012600500645a15155280c205010b0040800c801e801e509c01c04400050381e03442403003940b4030003490845098468251111485c820000b5074000c110200c801d03481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 476674955 1250 476673705 476673713
    0xa0201090b031906080f0c01111b010e0d12080a150512070f0303050304031407150c0e030d020f010e0c010203031911040915090c200a1e0b06010903 65
    0x10a003501d100218481c0c580d0342c0d1410f030700c10f0004280004a9a01c2c1050400110320100062510760002c0070004e0303a8040151000444041c001078108914641c0001c0034441600c14000e101c402c044818076106d40b07940c580c403020881010220b042161204540381200e9440d55004010075041100d00c1014821198400c1c0414440509401410302ca03c1c20915080c407d09001c00c59540205011400100c0c999900e040250058204540c141e0204000043c50103685120500710303801c9507403240300501da07000d1001146006000307541c40c503002d10003d0741010000342d0342004031840c244456230003860301c1c16558181c03600b96003079034484415680c414461000700c0d0f0380100070389501c101e03141040c44500c1c0640c0490000b415081420415110001401080c02042c58200040b2010300442c001c1c00540d4540c42d0b4405c551900c11114009040c4116280070401c2c008040b01c0c3d04043c0c1c60031240b0740c4400b92103030f000400c030915404440c0c40034004804100484803510692200c0e003402c00c807858501d5519 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 476676205 1250 476674955 476674967
    0x2303040b100b19260c030f060a0303050403060b010315090204031a070e1306180504020319020a0614040302060301140108100e0c0f0c0a03030c0e040917030414030f090a06020a0201 79
    0x751000d004102e8000582c0c1810440b8500002c41300fa0b08220130b608103100050025841554054142c460090000d10b0508282062401700c0340e069803101d10341899500d86400070803010500b1070401da211010340707520f11f4000701e442d005040149c4005a80c0e91541c90201091344402d14200c4082102c001086080ba4103c0341503c4c00c0e03a0242c0c1c00c00c011403011540480242119004140000c00150701c01c4c3ca40041917001a200f9403013603040351505110210420072403003043d40003d5021510650038042244903801d01c9110484032144a030408c3e80780e2340019001c0e08260490280c0a50420352550f0b1503901224090f0049500d5120b895018140310003c0d464201c000d21034102c0c404001901e11440c40c07480103d4a031802c0003010390341445058034004001d00366403071901d000200a5007060703001d45030511481d04110751002c0c0a040e168030036a100551504000c20a944540401d40c400300142828401000103030070f946d81d8203640e00c00c107038100280c0c1c140c15007240382198070000719200180d81081b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 476677455 1250 476676205 476676247
    0x160308030a0c020f01020d060f06080907140301020c0601030b061f052712060601030f06210c0f1706011208180406050d2d0c062303040b100b 62
    0x307080400c07040c0b10b0210507440c2c0507180084032025031000402911550740b0342d01100030f60700031409400d0b08541e104404c032001c00301540d03d00d945800034a403c004900d80360340038100c0c0403000740003d4141900e10490505140c0260300903034a9080711000c1008600d4000e031101510004101500c0c0da07c080701320000c00500440400c0282030f00b25074100d28040800514282820500401c4001d001518000e01c903150041900c1c5207001c241803076100743c50079205014203001d9400c1c80c419507100e214605c410030700250560744280c803091301c2120701003090b000d2986520040c0c501241c1c0b0503144108065a1172070302a050784801035100103200f10400051501044803045e41140040001c460b80c5c62000500510441d840164864107242c441020042e001d295840c038049001c0c886010480800c180043c0c0f655011401410031026101c14081d00740210341c104201c0380403c8418509212001444070136500c20303127060b90f44250300d1040218001c01c92008402a000b410b011506000003d0800c0403030124503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 476678705 1250 476677455 476677471
    0x5030f2e0f06170f0a0f1107060c031b0c260a020705011d041a043806120403092c061e0607030c0b0703020918090703031103130801050916030803 64
    0xe013000c20710b110000e070400064010319550800c042403901c82000321641c00315004491082c1460380b519140c07030180c818440032040f41c0d888208000d0720248100c5030016030314000c0707442c400000d0004458440201030b0250914400751a241d03104c0040ea0040c1c90080e881c5e118604100046640680d03c031641001181000c10595011841580c0c070115005000c80c62040303940c009184c00c4a210711b80ca03544148441d030007502e00601c21407103500540c0d071404040300b14806401c25003c02c203303024140c050300c0da07503030050092506c0410591158080075a6402481000a603481604410302082054045803070700008110741d403c0d43d09240005c5140d60701d5100c2081480340402141d10018940a41030000d030396541700a00048a150042c0050300035007100480602503500d0403c030f8107107071048014582c001c1d181030000b415014595035080303501c10740b04140005c0303a020501c5179002c80109144070001500c107050001c0340d9850100503c40c0350204040595a0608141008002003601700040b25088070361 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 476679955 1250 476678705 476678731
    0x1110f070501020c0a050705010e1c030e010c1406010609080115170f01020f03010e010b0703170403170906090c0f0d0210050f0403060903020706030b0105030f2e0f0617 74
    0x103282055030090180003a602c51038011020040d0030010041007210a41d0b40c240c0b10500403184890600091141000074024610204c040c13200c0424000c4c1d0740a000050149030291249110f0396401c400e0007411442018140c0c082d80050100541000e030a002914110303001b00aa00891551a5840070b154422800b81c0050711144020204041c45404852000c80000350b513242035080803581d55034001d04c11040000b904100102d4520031003c01c450301140c0503503541207122440c103e03503450400040e1045007071100505140800880510f001c61141c50740c080a440e641c542015080d08158003500060300c10b0f08074802800407a41e0302400307083c3c183e0301aa440050b030030a50509440e58814000a05c0b440c00001c600042000059040040894401e501341c0e04035580c0d800e029400e035a0016003090108009000060b000c451007114194000b428591220610301d481c030558520301c00000513181c00c3d1703121090500c2109070b00d1a00e20002c01181c40c2c00e120700c8100d0b10f130349203203044083d08007002c1c101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 476681205 1250 476679955 476679967
    0x420031b060d0c0c05010c050918060a090903050a021b0a03030c050f06010314010c03060f05060306130c020f1507140c0703150f0b010804080d020f0c06010e01031401110f 75
    0x2540c000307440044802c5001000f0040140c0c00c05020303c503120a044a0355800c0005c42d01e10079202c1d005584d0070f45c4c00038003c5494407076035445800a1103001002d09812003120000060f141d405400740c00039080c00394070390302d95a0b141004002e08010300c02da1002c507400442e01d100395203611400004012039826103007201c241d10b4a49401030516450200621030351044200100c28002d4000e0142007991544008200c800100e86054080d11418440c010040315445030030041420000d00543d0b000c0c10081a02000c0c0840c0d40395841140c1c1c0c2400303d500164052080c1c805200340811600300780c0400c083d41d00001c1c0c80c1c0010010100c040d104184440e0720340100e9258a2504200110406507034026000018150002031620040800301d02c0c810116040c445083c4040d4010001d41c5e011b29008075031240380440502031480694003044281c90600710820207400da0400c28030282e4040c0000501d1a41c4035459802d140240558135412840c00c1c1c0d1602c1300b2040c4c2c030410b040032280200003c601a81c0c40322 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 476682455 1250 476681205 476681209
    0x40f020906030d08180723010221091c0611090307050f0609240d15050603090c091b1303020405160509040510030212010c0f03060608060913050a05060420031b 70
    0x80750700c681500e82003104107d400000810400002c2c0c4001c0e0b080701d0310301c1c0d0402608200c450002c120000710003c1041507582e90b0030030210415a0100c5015881060107807075032100c04aa11385d20250740500000304000d00545010300002c0b0050404540c580313040c200d180f0000c0c3c441d04c10f40c5600c5201e903808400349107205220803403403951180f030b002a0359211500c4240080152401454034a542c20800c0d801180c0d520340b20007a24010250307240240901d2040c5c1080c0080140d000d400c1c0600150780c15058041100030780020b0060302d1401c250500328518501c1403109803080600602c9111825046020049a010040d9001c80404039008901a00c94924000c10920103420194200c40303141000c000c00b2005405c070790a0b0252613540c412403031000c102d04504032140350080000007100300001ca00303603140100c0c5090f000103505c1c042034017a10441d61020714150300f40004a5440e04200c0030041400280100f40416443d03c40403400c11040c0180081e0310ba41005070010303102950591650615 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 476683705 1250 476682455 476682463
    0x10e06190e030403032a0503030f0403020c04020c1b010e011202070303320c090a062304080703050c09040f0f0f021017010803040311010c03050d05040f020906030d0818 74
    0x30588803070a49036650749900f0000c002e0380f0200c40c44e0420707803040c0004522500000740c070182c80c0e82e08000a181103440d03000030041c80341c0c00034000383c007180300720060203205955600c0280560711510300280185c045500002c0c9142d50060003079814080903881405807641c11600d401c0030013011640069403013456240c1500113001d218841c1c842031180303050901d0b03c40051700c044030030036903218030391000d5070b40d144000d216601c070f00040c043d007201400004201550290807251240441c101d011508606030090880c40383e00294084111a8009a805c1040c400107000070400b045003554030020324034250f01c41410003a1030500040805500b6811b04081c00302d09602c0d072440550040c0100e40c0600045401000300022440052034010150000942c2d0440001202d044941c000c40600c0c19292403401556071030100a800d500388003040080c524165114031643d84500d2291444410f03521050050010710382c00149440c2c0a94002d004884100c2c0e000030340c4680c040512150307a1511483c030705540e424 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 476684955 1250 476683705 476683721
    0xb0c071e0e0406060519030201050a0e0301090b040f15060b090603090a0611090a141c05100528140c03070908120a020115060f0f09170f010b03010e0619 67
    0x80301200c40070b0108005a50b0801d10449004455403420000480800140f01103103200c0240402d804121a1410501408489100700d100800010301c40615850380807480000702c82c100c44001002d14201d00b00310303005503034040c030004100c0100b040300d0801c1580c0525100d2a03000c14810746002c4001510f605080048000300c03980041c05000b8405d000c03043c060301d42c1081a065119004100c804140d06c0020030440340030f0600202441c55100901c0001222400c000134241c0d418002e003500007214640385e016007802542c0c0c0030410b80303c0300c2d01c0034140200c40c0340d00c0c1d2580c0e150901748001c0c2c07260480c001c1440350300300e581c910300307039940b525205010348403040c607503002d945240a01030310304984080040c0540b04d07002c01a0000c0c442081e4502c131800c4200d08600840e00072440307012820cd1140c0c422607104104040b12f0a003c14485e03110840d0800b42009900400c0700c0f903120100000c00d600302802884501001900207010030001c444500fa260600101f901e460400940c140101c6104190071000c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 476686205 1250 476684955 476684969
    0x506091203010522150e01210602030a0216050706080f04030f0806030106050a030f050d030b0d030e06090904050d0f091401050c031204050a0311070e010b030a06030203071e0b0c071e 80
    0x1c1400c001c4424000300417103500c40c5013400c00816000003030000e51502500c0143d121000303ca40301c42203075610740000303400240550841e40e07030910402c0c4e811f20000d100e41050781d0007140140880c600d070200003810310000801d401070a94010081c440001c0e0812559002908070b42050650b81d5101c00220b401401543e010301e80c41040958000180018101040640c600980903a03c6c072040d030b038030140d041d1200d181d00f9680000c203076a00300c00441d100d4100d0040e0940c0007441140340c520440f00240d01c2c03500a4605462a821030850740c502c0742e810440a01d08618282004003182d0b140000c00d2140255407010303035052143c00942d8000c07650050044440c0e10042c0941c500090801d030400c242d594900110031408121505e9640020220000d101003c44061510f40c140070f030701b03044400030b15410240800140d291036040110060b0b40c01e001c11000b43c180449072100b814003040442030004210380c0f00d80f4031007104114905851703d010030050165a86125003000c941504c0c608102224940d9100340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 476687455 1250 476686205 476686211
    0x809010c2f0f030d0207140a111302070b0f19050f010614070501020c0715020a02090c070807062f0c0c2101060806040c150c06050901060b0c0303040506091203010522 73
    0x1c141c0820702c5c0c0c090300000b40a256040030b8150003254581d61144242000b819070301c8500804400c0e860410799002c8200700d110000340c100310351680c9000741151b0544204454280260800641c0c103580b0314240000c3e240b41500340301a040c00e0911a95401d03042c00360f41c080040500519013444030303110880c3c40f06940040215650002d41580700c0e21048140601d504031001c03016000101c0303200240070030090703030000c0a926140c0c44a044400c6141d101e050200d50100080c0300b904045030ba14801c152100100c04c42071041c02403c11100050303a02e810407072040410060141c150241c0d00000e448401c1c2c8070a4507a004d100b0b0801c007200c800c24000d509440b03202d608001012480150100b0b030180a28400c5590110050700e41d40108804083d108070840020301d080150030118100340c01254009107440000128261100d08089259110208014041c0e10000500c000c1220400c4030311f80c8990107d014140f40025011501c04601c41132149520402141080c14a600d140303064000e0a000c00c400c0030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 476688705 1250 476687455 476687467
    0xc0513110c0a02190f230409050601150306080a0611070c060905010f0f02100b011803031d0301050106080a090303020d05090c040c050c07051c050d0809010c2f0f03 72
    0x40307070341d074107480d181280664002282c1e030150f441c04d42e002401303070380010325924056803c18081e486074040079100341024a05111025501740c031107201d40700003d8001e8018100941c100071364110400d030145501c0f030806140550403c2094004a03107100c0c2c8940c020b00100c2c0031014608028028041c80d0b0018000c034521038000180d45412807540c034100c4a003030f200c0718004403070950262402040c45101c600980c000d500410764060392039000c2181d0701030504000c807400010252810702c40741c486d00201c01142c1d11100419181d40300407403020803130300c04030024071403581031800041c5041030182c02d406e40c1c0741d12860301e01300301400b0f074066900500e0f41c203400f04aa8500040410756513020b07041307094015480d00b0b12180a080c030071011245a018000f0080a0b80c0e4507040c01c1c800d0f104584590f5001e110f030000e100304001542032151941d41269551050120708103104024212003608507001c0a01c403550050010811405180c90703500400d85003000080035803087d6840c00c00b04100301c44d0a80d40400150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 476689955 1250 476688705 476688727
    0xc100c06060902160b1e01030b04020a0b0309030d0b060c070e0c21071e0207060c0203100c0804050708070f030807050c09091e0f0c090405100e0a03030f02070c051311 73
    0x114000180c0104003208046e1518803880ca02181d00c5001d08038070384201c000500105e810744000703c1d0002c2c8041c180f4070300c550b41c8006011554005540c0700f40325400000f000d036440c0c0380d94088c080d41e8400464045160441c0c4072030980d612034242c840d07240700704620f1000640103420b55041c0c68006211100d00d0f001c5d40e034110740c160040c1e14119100302c0440c0d4400642d14034103105030038800c980135040e0001c001c1c56041020542c0c41c1400190220f078584108041406035000d2409880c1320880c603915500094100361808604003000354021002d980c0c084a020002580b2144400b411290045034171a40c0d102103040c5981004654008540c10130940002d20555800025001110b842c4901c20b881031203400701e07000350711002003003103805c1e40380c8c440410103c2e40c0c64540495500f00d07104808650315109800102c80c2a20314024008040d03401040c01c0e078040c1909030003844070105031000b0442c50480c0d2a43c801c10309980c0c60240f10f0080c48071a00c40c001720041c0d0340c406807080101e030352421740728280204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 476691205 1250 476689955 476689987
    0x606040909110103060e0f040206091302041203020f06042a0b2703030f1c09120509090a02160609080903160f05151b1501060518030c100c06060902 65
    0x51400246028000121020500d45650087c98685402d0029403941e408111031604109101f9610069a09602c2c0c0c003000726200074001841d484002c0a007110a80c1006414110035803c0052103802c4801084009104141a08114840c0d900401a016542400041d501030076800c038000c081800a140108441c01c8400115a6442c02c400701c05a00702442c1410303140d00492804284c107010600031041c2e2000005011120040703030060000300410151100d06000707050040c803a021540029500b601401d00e0403401c0c0d440324240d6401d51800690b240c1490401925150281c03295642d2000f110402440c0d00c111111048002c045070341c40304082034184440746407441000213a11514200042a04060801d00e400b4074246a1b00380c00c00380da5296480c05c111000c44c0802c00c40c09401080f003210b03c441d04c000381c00790005585841d12101c901805804420000b20102d100b50321004001605130360300c10003101c5010341032514128040c0c0907d80b94000c3e0140e500114100c1c1e001140c3e05200c12400b503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 476692455 1250 476691205 476691233
    0x5030d020c030d0605060a140315032a010f1b1b060201020405040b0d11010c0507050607121b0b0703020f041205010905070e0103020901090515030a060f1505060a03050606040909 78
    0x4403040141d03a030745a080081e00d204a800d41d2008c83c020f10304841d044510304000c1c6500801c0401d42c030111400400009003841c51260001c1043d041c00038010502c0c00b41011544800c8000b801c211903802180701c806003004000b0101c1803003468010462800700102182c581c101c00703219405241d00542c841c1c0780a03020b50094000e2600481c038103020351105152416680c40c0d00d43e0400c0044420710000030044a0440e5610000d40d46440792140000340ea40301c020080c118a0300924407169107010040c40100686410100c200c0441a04441e80001c240300c01225600b0140c2c41c02c0040c4e0b1482c620380c00036003a0155503c62844c01241540560a000d010740103243c030103110300180e03a20592140c540e841903a00138040a0740040c042401031007030b0601a44aa9008060700110141c91602280001d00d01054481c08507003840d01c89216810325a07030383c024034610046035244814010300b008041a0340740500d00c00e41d020580c454002c06c0040d1207102c05c4401a0401c0304060280b06400c0c24004c040244030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 476693705 1250 476692455 476692477
    0x301020c01060f151d04110705030a03090b0f060f09060d02030601030c0f0b04080607030f060803070f05010b0f01120c0903050a0b25020d140f070507090c082205030d020c03 76
    0x40300c1e4400f0b0710070000310008926030000d0405da001400e0500c40103161010801002e002d041020741e01080d410005440080d117596030100f158440c2e49002d4507a160b000e400c4458054400d01442082e40d154049015052800e03107180c0318640d202d4000822061100b000650180a4500040240300202d0b1540058440840c0004002070b541e507800c080500c81d80c403c5900a03008240880c040912030713017201a901c0c400843c0851460b44581116040d540000300483d03504d5044206042085001c3c010700e84228000c48002014110030030001e0800e0300a410294107040d9180700e6403040c40c1c00b49038000065604101164040205032801071550303c3d00340c1d520f04518000c4a01d1444000404000b1500c00c5800c0d40a070083c040d2007113003030b123098031340b40545400a04244040b0540341484805001c0c170b42d00071002041c4051600c41c07000c044454000c403030010414054100000d510f40d885400c0c07072901392225810300181d4203003040c41c00c0d4007900103c40c10309800080d001c2080d00300000548889619 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 476694955 1250 476693705 476693729
    0x4090c030501080c06040608040b0603030415021e0c0f01081b0c15060a03020604030204020a090e0a0f0609091a0a060b160501050f090d0e010201090c0b03010612090c030f020301020c01060f 83
    0x80c49080111798041c5100b100001100400041c00040c071106a080d000700018084030f041c00d0b251001401080031040d51140141e01c41a0500c0d025840c252080300c40c00314500280660208010220b00c2c083e10801c00030741407289132404203090728500b1001d0044404015102511440400340c403d44a040c2c9401e00c0007409c040c1c030042061450302810134402c4950007000c1629052955080c04081d4000301c1140b070070711131980c0340015005030f99120b01d440b9000070100040d030465400b03c1c450032500541c001c0e14405140100b80307400212480d544e44080241c092180312555a4a0840e41c06090560080170003d440841c003140c9610007003070401e202c00e100b41e00034002030345c510440c0d80b2103c0048030a94140e600411100302c0490185881002c0441d040c8000f10300003400d43c031007150540f01c80d8040e10410600000400c01581e02c41c1c4504189100c00400740210f544a03110760f01d150503680800740001c1c0900c07402c402199000d504480340d00340305400a000041e42c82d07030180404071070380c440c082e03803204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 476696205 1250 476694955 476694973
    0x1509050a080706091406070b0c040810111b0f030403060b090702010c08061c02090c0d0c0f0903020103051512010e010506010c0305041715010305010506010f0e0907080a0204090c03050108 82
    0x42680d1040c3e400550307942c00441d1034071035105140f400307215045800c0340c42000300001094003c00014450402c0d000d40a80d194940802107260904040340e40c0404c3d440e102c00099082109004c40c1c0780f4901a01d00d10000801d0000b250f4100601e90b405400203200004c0d0010401c03143e40c00c51900500211184c82c140d0340c4207401030b801d8801e10041000000c0a0b180010340301e1031300e6512600381c0d14240c44004140383c8164040b40384a1300554400010309030203d044000c00e0382e01c0c0a09100b4424520b0180d070440746142014280300402d0200074149600c5200040c0c840c04200c2e0001c10000005140040080014000301e009181c0641400b0b004d500308000200070754010822000050361540ea101e10307140ca45800306045290603002c1002a02841030205600c4040d0a1850702071402680000340c0340c00c00b040050142460840b0300c03000c1c4804102c0b04507084da200350007aa84a010342c1404903071581c50b0041c98001b4411a08022440741c94140400324031541540040d050300c00701c400b00c0300c280d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 476697455 1250 476696205 476696219
    0x6090d030f02030106020307031d0a0806150102070b040303081e0a0f0c0801050616050709020f12010609150302090a03050717010b0d02030307080a02010e100c0f030507020c06131509050a 82
    0x210007401405c0150380200300a00c0000e10450384c0c482e000ba85001c5507014007003080002096000913500403907440d84010240038206020902c0e204000400340001c00c0c0b0301d4a40580710301d541c000c2c1e22000c1d0a00c500d000001d02c518100941c581842c05100400050780d01d46401b0302c1c0f001b0400704481390101468001044545401400e01c503050b59401490300d8141050070300008201c1d0282e00c1d003221380e4000c0c00300002c0c2c44039081c005410140d10724422580c40f0350010803000d001200581c040b904100001d8404c1050700c0d000d08030f8400c4289546000f503952050003000c40e03100641540300410610601400059840340d8020403041007070603000074040c4c05201c400700704200714803500c0a5455001000100005088880246902e8140d40004218002d401700403c0c00e01d070904041f4010076403641240c60f100b40e848101c001d400b900c0e600f801c000e42d040c85c480017540c031018110017500800000805150a00300001410000c0c000704864101440407414000c1521041d0b20940303001d44660003001c9441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 476698705 1250 476697455 476697457
    0xb06040605150c0a05120c061f1a094903030c02010b0a0b13080601051503100b0408061e042f04050a020a0e2b03090914040b0c071709030f06090d030f02 67
    0x61071080789c0078002410074404d0342c50761000c140e0f1400c170480d08210702e00c1030741c8a15001002c0e080c00c1600581c908000c9851409060030610094680c1703002c40c41c4400700e44030354003981c0001c00c0d81500c4c0c0022000490801a801400ea41c0c0307115600c07078001180055098255001403031880009100c0c019203d135142841d030768400d02070003510b80c016000031003440b0a90001000d10740c043d901c40d1070001e11660301c01c0c030007038a2340c49030700f203205243c01510400c030028103142c103040c031655040307907411440340b6240c0c44101c4422114000002c0c038200c900000c1c0854401c4081040907003500802c2005075041c4140140020f5100b0040301001c5424010600414034140b00c0d1140c11741c0040e00400700304040300101034420a104c25046050296030800130a509010303110b80c8100e4034013014800c42506007070038000046a4000d20451000c0c4003002403200040007004049807070800d000e040d0362200d101a00080c00c0c00000701700c0f104244580e10810140f4400015061040c0c0000e45040100e80c02c425004426 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 476699955 1250 476698705 476698741
    0xa050603300f1606320a0f110d2306100305190905010207030201051b0a1119031e020607090b0c15130b06040605150c0a05120c06 57
    0x25001a6614410340700c541c100600c885240c2410040ca001d81248a03a008840480429070380c156030382140840603c10800040c4d12554106420340025100c081e035a200c500c0010300e05400c85440392046007414000e0b8003c10a134103298140149c075555010301c041c005101c50194203032811661540c0b14001d06003200c1d020b000d0032000d0017422041488840c1036000e00800380005078178071f0644104528a440500c1803825044c403c10016a82e0300322400c000342940d0000d041c1044030b040410341c1d00309900c44041212052109420100380041c10080751500f081c02a06540c2c0381c01070a0301d0403604050307202c081031581c5112540f40c201c1100a5003000c9035100811500c0d40c003c6000d043e030601c203451160002d07001c0d0050a000304c0d07000c030f0748011400031403180a4030b41e81e036601d5200044400300000c07410b03081d6200740142c404121981c6000c00055046014540082d0312000000740400c041c0c80501c4a002081e4001c4c0c1101c000d101e000782c10603000ea004940c1c1d240240100b03004154202c0400c509820 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 476701205 1250 476699955 476700013
    0x5060708070f111c030e010206090304050f0117130b010b120a051801091209120c09200a120b010302131703121302040606080907030305030c040b030a050603 69
    0x801c0094503a900d241410340788006480000441c800c00416980b684013005102d0000702020090070f5491a010340340402c03d02c1c80d42e0540d00b019040251100c80001a90308449088420100c401468401a1850b00c8103240b04045503c10200b004074807901c2d1120030300f80030303c00d80d1032208aa98500782078195006080b40001c0d00c000c00b5022480f40c09003500b003141c01212802d200c00200c4001d650081c2100c02c9100c00b12420380e5940414450745811522110080589107504c40000c001d41da42c3c42d400c02d4050041940b86a900d445148a80112103001c668020002081507520403c41c2d4018101c203003048000344c10741d41012148541c41d4403070300a0711840e230352011400c886503013031040501c0300b80400c01c42000c03d4030050043c0a1780c5d0001c3d42060380901c1000240640e841c0060040c0000d407020364121005010a4800344150041c0000b00300c011a80c040c6002d036100d0700e03030100c4c440007031203180d0200c100c141011051103150a1168080b5008080071404c0703c8500440800c031060075049542042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 476702455 1250 476701205 476701207
    0xa1115040e0a060e041b06020a02031c110d05120a06030b07080718030303060e0c04030506010e06031e1b040c02031206060909010f032a05060a09030c120b0105060708 73
    0x4030703019040020a4101a541e54041100d503101e20040e0840001100c041e10084180c20502c680b41d2803d858250203000544090403100c6c0d419000320381d45104034030014924049240d001c04090748a401c48011801c0030409403200040754440c0202180c004c40700c80c1c80d00c1403104004c22042e6240788640400c50b584051503090a5a850130291001031004040806100c8076410400c200d07100482445c01440c8243c80c0020715500b0990200c00c4001c2c01000791524420400045c03012070000070f80341c0e045440c1c0f1000400302d99200800309040440c4200085054101e00809a000c8071002c20400c00400541c0c22811a8007080810081515222a06203000d44c01c10000604030b40400f40036140e0104019019525100041000c10400d030003d9005195400c0054000d004100c803230150721401c03070744805854001c02110f0028268822643c0f08603840b45a00082900003e4028080c02d8010740c0c2001210750398030382d00c049881c21140d0b82c1200300c40341c0d0301440000c01c1c107103010300c03d072000190010035031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 476703705 1250 476702455 476702459
    0x611071a040c09110c15101211040f02030601020609070515210106020a291501120c030501080d050c070620011a010e0d0f260c0a111504 60
    0x40240c40c5000c0c0c0251003150320761030b0125100e035860040140130940d0f1807150740c0d00e078480c4040c541400204010380415414141c02c0c44110b514011100068071103898000b41c8481003880c02e10b0714029801261078109060100d01854190554055489404281c00f0741e11146c1da03080c5040c0e101d080d44d01450341d0026460411000740c00014000d00742d00c60050b5000c1503006070ba160003400c1d8010980c0f00c0401a4043e040000402c1402500c00151041c0280780844c2484d44d0701100000350740080139802c10705040703c140d5007582c1c450407440941c94003d00703040107003032030050008000c2c110074051f640c05032240540318030740301c1c0c855021900c0000d8084007a01c0c0c182d040c41c4c3e04072175100c1074140004c5581c58040d5082d484400a12840341410b0302c8400c10508001d1010014003aa10901e0905100700d461551540100d1000000e4a00040d0b10254030200600c4007082c070b85141840301204c80080d100481d009200080c001003a000e824010280044102100800c00071000e00c00311407031844000034481 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 476704955 1250 476703705 476703743
    0xc060a021605010e06060a0e041e02061216080907140f150d06061b0203100b01051e040503010e03040506180303040306020304031709011b052101080703061107 70
    0x2410311090748800e001c1001a080d00ca02d425113201004000090704180c0601026207041003041d4010201b2540321103081c60951544d5a4603020b85003004009240c241541045644100841c0c00e15168418120494103080301500c0c440ca4192003a40e00bc2618100070840d611030018149003218500300450b9003400c000028084415421155650480a520802004001d42d00d002c3d1040d24080c680c0004c00b145001d40c02000208031000c6039142c5e240d80c0c82980d02580300400c06000d0b14415500220711107041400498440c03003052074503000315103071200900c1c40352800c4005004540b01200203002540d10142241d0301c0748030394401c8591046042100300c03209001503c9a0000001c02400d490400ea50790301e0300d205a0380202c908800040281c61030541204007688074907000038609000300084036100403072a60845449900c2000e1200c041108500020a810950308100c04140c0414242d60340d11030650b5107005a0204550381c1341080803141591000c60140c6e54140d40140040c00303048210a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 476706205 1250 476704955 476704957
    0x14010f140702011805180708130305070b1003061506080a0c020a03080703020712050301150c08091c0507080105091b031507030b10200a0c03060209060c0f010f0b0102030c060a02 78
    0x9907802e0701034022000040c0781e551b07548240085203180480c400c090714010720002c03c0d02000529114003052840400000320741d008084d50502e950124600a49490ba060310145c2101c80c0d40c0010105420440140c007120204a18a01240c0c01034a03003803225240e02041e8015104810b10b6000140d200040705008280709030340c202d4002246080041c42c00c2650384031341c3e40390b500a501e09404a44000010402035803201140700c0d41da4800e14240f09540141c3d40c4414035841000d030171511801080b2210031000302c0182517000c00c03551000072180c1c1140c8c0c811201e406810220b5032800c803400b4085900c62079565502e560021100b00074007400d10001210607054103030202a0140c0d0405a994540e03280d19160111000f2202030181c552010b0303080811278400700c998044101c1e2034240c0210300f0000001c2d1030003051600b5694480000343e101c21400011601c28052101d0807031031486040c04c41050704c003040d0b0040e56040b05101c0c0c1884113042420041e0b07520f10a026141140b98000b20000e82250840c0d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 476707455 1250 476706205 476706227
    0x21011010c080c0a05091c0515090f070504020a030212010e040c05060403120c1e0f140708070506090301020702060f0702031011030601030c021627150b03041a0114010f14070201 78
    0x71f18500280310040c03269001e484038020f00721031580c440c1d4a03040c01c000300031881c80d074400e40d02c50040c403600000e851200d0312034081e442000c3c00303590003007103002045001c1c1d01640c0700111071813650111903030b6600c2030041166040d1410f40324415a02c0011406003840000c540c162a0450000300301803e2160f0115652081900184d40100c880e003959001c0446940354a1810342c010781021207080d159041c084d0480094000140701540000790400c04c421000c20807034200d80c41220001d4658031203002107070190ac078404000354004400103e0065000420b00541a4a4004c0e002c0b5a01e06036260004030490700080b035100b0040c0300600c001000c6601c65080b0310162219032040e40c5407181d50320300845c500c0d040750b0880301c040f40d42550300403810740c00c2c002c0d40c481c10031801c1400d0010640641c0d8120b01103149004482014000100140901c46001c5005802c6022021007002940e910002d04045400c41c1c0b4510303002030060908074010301d200354910011400c8bc1203c0c00c1c074043c065401510030b64540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 476708705 1250 476707455 476707459
    0x103020c030708092b1a01140904052515020601180504020f04020301090b0414010303050a1808030f0a1205060a170c06070507080f0a050304090f09021011010c080c0a0509 75
    0x4155400d11241c2210105c00c0400c6400c1c040c85042a003500d0302c0c1d4503604c9840f0310403040c100c0c214010086803404a4001c40701903403e0320000056112401c0041c201040006804090102080c0142202711a14440301c222810005014040310100c1c00032601c035035081c41901400b4454007040303819000035602240e00503200402481c10101640049000d0342c00980c0305585103640d51007040c2080c10103000e1942c4442000448040940c116036015040b4050110b20000300081d002d2603000c403000c5c041f90f81000c0c25000b0226601c81340300c000b20f100caa9010b00030003c0080c12142c0d00300c102000e140141801010000c3c10300d603405c0d003811700c01035151028010003441c912900e41c0c20940d82d00e5010003010801e0003030028020b10b90415544500c2c15105d04a244000d902c0100c20310040740d004002d4906580b031740d44e000708654000140110140a0103d0081e40c0080e0740c5030b0814005420071400030722030710208024800e6042d0275070141d80510080b140301400003010402d00d80c3d2580300340d00405041ca40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 476709955 1250 476708705 476708719
    0xa110108090c120c190b0304030509032505120d0c020f0406031e12021c0507060912030e060105060414090402060f1201180c020c091009020c03180103020c03070809 72
    0x402400501c2c203a00d10305000c0d00b0f941154031444d4190503d2100b200103480c0c50b40070300b80c1c601d01d401c1401000f8403000f08094100f2502007500c113516642445801c40308101d00708803501001e00e4000c01c10841d60144292449103c40c3e40d400c1301e0040001c6101413000300c85450745000c010841d005d10101000e10810b4542c065030782e2f00c011000445c00742c00450405a070004031065120300d8034050942e02c1c0d00c024241d041d5801052010b8403075000703c0f986081c20700503142c40c0d5260306040c41c02202a101444005140003240d0388045412a03140d4848500611920100c9040340da8440910080e4480d500540005800c1d00c44081ca090811410341c90304603102915091800042c03584241079074108802c445146680300c4010050320440300040e4068401e03046080085491060010750b4502403600300a0003880d200c2c001a41c1140000f60210041c8503141040d95182255607403a512980704802e05510f101c1380f0030324070540b540700b8421344200110342c1f0015898404142c1300ca107a2504200c200a911a903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 476711205 1250 476709955 476709973
    0x209060f01021f0e0706020313060309050102040506031501091401020a0611040909030c06050601030c0c021221070c0f26010e0304060504030201170f072f060609090a11010809 77
    0x20225101200f08003140c4001035a400e4808145003401c0e0b4a611860841d401800141d400303214121440084a03094180004c4d484010314160740a030117942e00c050750200011003080b81d060081e481c0d049a1510903039901030102d0b00e401c1080851500c03405221700580c4242e1100000900c59841002c400c41c43c81601420030760b541068000356070012104400007000c0c03840c10410003c1602582d5001002401c05003d6100e80c1d11000f1703c10141c02c0c001901c294201c020101c0300300000e015280c00030401000d468074920261012008940c4400700c1160980780c910000030305e0381a959004015161807601740e103a6111042c1c891a219104507950480f60f550791040142c82210400041000304201e072030746522a845c41c0009020b1155034000c0c14440030004080249890403510540d500141c6418607146100f800718070100703c600e81d8078041034100320320110040b40d803000113a298411002260502555518840340c0303611b92049030401007000b00140382810656029410b004c2d07002a540d0100c541c901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 476712455 1250 476711205 476711233
    0x60a0c050a05031b030408101a03060a0204170c130509072103030e0a030f1206120c05040507110604110f0301050a0c14070206030a09020d15020301060e0d0209060f0102 74
    0x502444002c031000e600000f4180d0215098801d00c42038042e001014504003450101801d855084003215204a2030341c1c1c804d03641d50304c0200c80182580c040040c0072642e0f00d280100c9000020f5000c0d0060103014116516004003070300e0000307080c02c07080030040c10501030740c8901c54100029050181c01d4078114065a000481d11030020503004a02c04010b41035101001110304000d012200e100807188041d4014228603400f1a82116110080c04800d00d007030404880c524248200502c41c41d00401183d2011007882028010041c0000c025108119010061500c43c89001d6034203030409800310520340c0140d800900840d1208400301191701c40600721401040b04040060f08585013154038900180d52410381c1e0481a038400300701c071301c0b03c2c0c0d000b52500d2a044854000034042e00004090f0341c11184c80b244040304640310702c040f4102c40c80d8007200b940421500c04078040c002c0e4109005d4080000e4214800c44064603183c0307045100f482d0007504060b095107415040c06904080d00a0745815445925100580e107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 476713705 1250 476712455 476712463
    0x5160204060b070b10050a080d111c0201060815040c180902100809070b0405010518151912060b071e080a180b0406080606031308071a130b06060a0c05 66
    0x1041c031030f150612180c81d000208200785c03038081d0440c5014400c030810611440e00d00040a0030781c00128204401d030a8420b2a100d80303031a812039540c00c0190940c0d841046161f4054003c00c0070359490030203a0b01c58001980341c1c54080e0800711740142c032840742050708003d14035000084000321081c10381c012403810400d4022401e140d0b013250313003000050703a054100300700709005003c55400b0380350404085252500d45400201680580c07444410304e04000c075031209881daa100c028080d8170424046098440c14a28200a14059488002d10111301d47c40c00254985000740b14501c25181071107101800e24042e03844402c600c00180d04072211104104000300c000c02c0d0f0110140001034103940d1000565015891030303281c40070040e030004a480400380400d10144c0d41060100e540094107848258495070344400c900b4001e0030112024104200000741c600c14000d0488103401d841c1c3c1d07070a80b401d21640300c1c6201c1c6400c440d0b985038041e101c2c855000106041e460000c0c02000608002c2c54070210301d403a142c46280c24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 476714955 1250 476713705 476713717
    0xe1014100513060506120f0f0c0a1b02030703050d09060806011b02011b0b061206040803041e080304060f05090c0a0b0307050903031201080105061215070c12030b0a080d05160204060b 80
    0x80000e1b02c03000c10034940310810103180c0c4070a09403030b00485801c7c882600c0106000d0700440300f0074010021054081220009010160b0035001412101920740d40d0504c943c441100c3d01e10302000485158010030303050300850a0600500d0107035240c900200303100384040b042c0000311a04904203c94210716585241010803406441070042107240c04908140d001c115a203908501c4901680c1c0140c4100000320f80303280103407680690822603e00c4481c12070312810004100341f0710b000f42006808810b010500c1001c1d48180c60350f10040c05d08012545274150032a90340d0400028072070380459898001d10180c0f11100166030032941ca8200581030543e0840000c0c2150008002007001d01a07141c010001841d090041070b4103e80107840c0116001c00c25510341340c03544413000700824442900000300e03103454406d41d0b81c8540d440d080112807100e4034a0342d600501138070ba2030b43c8007807180f5500040458200320100304000024030030f844880c94440c1101b84003410074401c1c070060380c2c01652214005107070b4000d00c0c01009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 476716205 1250 476714955 476714977
    0x2040509180f0a0314130b070b0f010b09060319020d0f05091002031e0c1b060906010609081b0409020a030804030314180d0f02040e1014100513060506 66
    0x10307400e500c6840007480e040410410802c140d03c5052641c2c04640c02c07503151202c0020390308a00380c4c3c8491410081010340c86a0740020792075200040c026092180380301d9503034043da24041e82044540d913a250000260700428904660014003000810450444901400001d010201c00981002041601107040f1052410001c2c10243c82e0810407070504018001c1a505604a410450450a10b41d0b000c0446051440c0200c01842160001c42d00070820541500c000840c15414009121030190102d0f0b02c420090301c0d4210304e44100400840c425000303400b56000d89035608001c0a4400841d000001840300103281c0035005540d82c3d803807001685400400b440518002c01c122070b80c3c1e51840ca002031116002c0400c903224417800f40310003920ba100c40c03111110341020443d0000040d0310a402c0c081c2a00020920003580280b42000c500400710300401e100c0b00c04801c06801700010101080f0703050603150111210750031070035822000c0c0528986551814030b21802030200040c22a11540407415540c00008112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 476717455 1250 476716205 476716231
    0x6030903020f0607050412030201240603182d020406080d02120a09050906040f050711010b19061407080f18010e1305061201060915060912120302040509 67
    0x801030540411a12000820034001002d40b4074007010003c00c24010703402688041d0b141c0d1000c840c00d01d8400d401c4954034010341c1840c0c01030480b4000164045850340d02c500c0e0b001c2410310f454007680c40d4804510005c4180c001a456001680386046000c03000c2d8404a2031050291074450400581c80e44e201d903802408980300100301102858802900e410703600e90640c02c00348010003420723500d140e2100c4451308031101503c0f512015210701c0000b6010b440050099080d9610b810f0401c10310a91001910130a400404000c122116140081c085180210540d100e00c01181c1d490400513148145000588980e0840845041c04115600c07031002c0e50007100c012141840120701c4030a12568071000c014181d60900b404c07000d00c03010700007084828a1160704501002d5403a80000c0081c2c407441050b061101c05100200b0a0940f00c1c0440402401c071454660301d61200c040010528602800396401601e801d0f0b444184c0e6a9995981d00884220b0011010b040503024840010709482d82e01540b4054041c1507130351 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 476718705 1250 476717455 476717471
    0xe0307150218030304032103020f18090a020c0618120301080d0e01050301080d03050603120408060103060b0f01020303040b1005100e190f050d0c050612090601141e030a0c0603 77
    0x42d4a0703102400c10964440e4008000400c00110503200c0818000911260040c8407100300100b50000d000b42c1c000b021010b000055584042c548003100c000761032900b11010301150310340c00900702c100c1c0a00c0c0c0d20150b180d8401c0d0041110348413844c442182d8103c0c2a021111541c0c000038402140d43c00a90001140394070441c10849290f8000340f160710036600072300e0450f003198036101076540c4c2d40c040d82032001c0a00d41d0394070100304583c40034400003030103001c9070b540c00707035116540c181c19940e5030307824401960564917081d5410243d01d010a241600000164000c50031340d01e403515900801413014009211411507150000f485440c2d8003040240070300b041e194046504441c00900c0326080c2008000001c00041103000d200d001d0064203040240c075825501042a48d0361442e010001302c1e10354005590084010075140607000f002c8481611408944007620b0403a42d0b10300c21020407940b15509264818945c034102c2e451680070340524074151400038121040ca0099869803900c52640350060310019844080c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 476719955 1250 476718705 476718727
    0xa0605091024050603070507061d1e07090b091f18020910020609121614010b1003090201120216060504031e090b03161812150506010c060e03071502 65
    0x20b50002c01094034001c0c82c45c50500c1005200b80324080d002041c0555880c1400d403401c54400b10305100c4502002207491006941e6810004c200180c0a2030031503104046e008210700d1303c2c03405410541c84015128104d01d480c2c0f90400624040c40300e0061060f02c030101400a090415517030b4100c48003201040040e82c88a4603424400c0c00041840070009640c004002c1c003007200710006a0380d42241c58a04500c6e200c1017112440145001ca10f400078019104160151429090640c8204071142c1c0c11242c0300e40c4181c0800041d41680c4286502902260705483d50031a0640c4580040c0b01b00d00d402101052245865962501118016941600004d08410a0080c4c91690002e03060144240782800000b1030700d413854020544c4802050842c0825810460100240c0030300d91301e502e4200444014188643c441c07444803d028850b9006480500f4289058009000d0030b110700b074040c14040c0d40d1a4142c00264407807601400c000803103040c45110422900010070390b5a0032101c0c0d4140d0310038006d81d803802c403100303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 476721205 1250 476719955 476720021
    0x11061309021806160201050a0309050114060a051504051c0203030a030b04051b070f020303070b19050709050607020411040b0d060801060807180f060b1210090b030a06050910 76
    0x880d10303008400401103c1c240443c090301e6034132100d50910f0f00b150340c0c510b0130b0f41c110060b000a50000300650b003414029050328440103036051281c8015a200d84e00d031070b0f80e03c013002082101c50100d04c0104400300424481410003403080e80c0001c2441000910441e131503804285198021803034240040d5440c40d03404210714050240d5a005840e0240e10b5442900c0007a21020f24400c0d00030080865103030031180e100315141803080e9490607401040b01f00451074283c0845214040303641403a00c0c900e14080c00038120300e004108150a07648081c281604205866091200416150354900e104003410b0200080e140100750051002c1074262101007449407810081c83c0c00e5450a42040d6030b15045000c00740410110041885400400b0709130104056042c02424030050400e0f4102580094000603010f00380f4406d60080c60080c0706245201195960310600c100c03c440410344c03e681e0580242c42190040b61180c1c0210707400500c91402d84040110310f5000c803081340d840f6503c501e400c100300384e40b0300ca400c10610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 476722455 1250 476721205 476721247
    0xa0b0301020903030405010c0c0b030709030311031201051215101d040209040312110406030914070e130320070806090d050702120f01050709080d020a08071106130902 73
    0x90025070800b00190002901c034016030148604018000b0141811f02842002020041150381b210075a80d0600c00700042449445001c2940400c0d80c8800190742d4040020445400701940021444680d00742001c00c4520002140724030700c0352190826018504400204582c00b41030042e544070203d03413414000c204000840c0d00214501c2c241c0d03104000258031100c003041e9200d81d052401c4020031042c243c4d0040204240e65000104100100d4041a096090761000b0384450040d25003164800c10071822565400b414050582272880c4a40410742c1d0010304024844054400d00b4903505e04a40c44601c404402c148500c7c600c443c0e030003c3d8041268200500810b500070340984090144811040380140192207030500082c0100d44040341c41480007014041c0100e62029600207000500341203000a0072144140501000d5019454480b180240006503d42c5000c0c0d01484103414005d2a894640100f64403081168000104100c065500322240c0b0561b030180408110060302c4d9914801e83c400455010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 476723705 1250 476722455 476722459
    0x92e03060f0e0c0a050f0d02040909352a060f01080f190c030203010920060711090601270303020d0306082a121c0201090818030c0904050102030a0b 65
    0x111081c403103c011031900701c94268038541040ba945035620621034009108080951082e80e2000c10301150a80c0e85402142d4501e0040c0201f07800a800d40c000c5150f242c07995924001002c0c0400701d00e54a55143c0e038054204400c8101400118024280300360004119148519103a50418002c02c00413203030400c1c1c044d014181d004003c1c40c5047c1198046603a920705184240900340200081e44100b041c05038183d0059035001d0001d01c034051251605202e101c81c91050841c142441c113a98034040d08100d4295104d8540001d110032080c0d1120052100d80d43c0003a00341410003d41c040741128800100e8003000c1d5040d041e683c80f4103402d00d10b040090401024118040c10541400c1c410440755000185240c0c10804012000500d14141c071001031240c40300c7c03c0200d070030038142c2c0c100382c0d507031000465001c1e030b01c0254900c140e40c01c21584404034221390402d103004000720b105001c15010b00c0c103031942c08148404083d0454080c2d9980d00b001a40302201114211040e80d0000100310b0726400500842c0720700481 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 476724955 1250 476723705 476723729
    0x90203010f180f02150a0c02010f18121502070807141b060a09150302044209030f0b0a0c08010305210f0a05072006092e03060f 56
    0x3004400b00d500003084060440340d010600d4900399907484100041008045000302d0340c2d08050000a0202e80c1104026801301e2051500981d9250051003040310004401d101b400005040610404804104003001e5907284200b52101561050603c0200442e5000340d21241d2108040d00d41150b007543c000c0386007041c1d41c100b0510b0458000c0e110310742d1100c020007101c1e0f4503100c54428100b259400c0050740500b54801e051181100b40300e805034010800d40740c0f00c5126100001255110705d8002000c41d51480c1c9080d40700d04901ca15660001e0b002c0d0310303060396242c6078404c03541e641c44a8000020722541903448410120912041e4107051103418420086030514450540c0b65403604c5441e00300c282c1d11084643e0b20540300707080b2460b80104803400a9420700e02c0c1500c4881100c0002e040c0d4010303603422078040c00a045424015200b1841c10018958001c01140c6050051000d020300c0183d03840400c0c1c00f035000c00400340c0104004e40130440742400a03607000281e883c80c11221000b0603a80740c2c841010029 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 476726205 1250 476724955 476724971
    0x303072a12060e0c04050f01090e060114060f071b15020105070c120306050919050c030118020a0306050d0f020306070f02070905040309030503070b150f0906090a020903010f090203010f 81
    0x1034035202070801a002a000100d92804050715801c00d41d90007a015486803402080096030384044402d14165040078404204c012440341560741c0c0d9501c2800b603540f0741200303a08108141d10f40b590050030b00065403c0003e05019040d03588462041200c0f010992092040341c051098400c0040414500ea0b8244002c1c882801c10341406445000c2c045406840440c0f81140400b10b00d002c0e4005030001d100c0a4060601407900c494840620a484455014291304180c04a0320180c9010181d03411380d98510692a01a10701907070240080d40910030060a1540382d990018066540c401c002040300d000e501d00e103042070054410107040c010020944000d12803c0d00350000d509034001a2903084c1c81c440d50f80000c01e9103480c10300742c075010010b910081c41c40c4000964501085000721210340900c28100d22160f040300410108035036002060304d0b01e0340003540e0342c002442a242100540c1d4010a03440001483c1441c1d640102c0c0c255142207040a60168039188201c04608003407080d110307289940c00d81040488 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 476727455 1250 476726205 476726219
    0x6031e070905100c0f060b0301200c0613051f06050909030702040b041104050616140f0d02150403051803010e030928151106040f03120c020d030c030b0303072a 70
    0x40d0703503c60003500303c075641c10124019823402d51000d94112040002141142215003424280d90b00c20141d040d52400f4205c041b0b4a08282031414913070195110015003440e82881451911040c180100602041d40352200014a41c8920310300d1070060040e000690f03980c0e803290041c4000d50748008082da00852030030804080c0c010240003520113072281100d0044d40c6030411400c2d1b406400b400c0e100a0701aa10150481c0f0082e080090903241081e554410b0750000c090071034080e6107800c0c080a004204a040780c1c00280000c0c414001031407407013141007810107120308040102c2e08495600303c21704c505030300004400995243c49070b4803a0856204030104103c12144210f0306801c01032900c40c69002520003008041094000e400013020701d4603c02c1110100d10b800d05140b80c4041d0038400c01e0340841c0e41d065071882c4000060140307006400d05500100142d50105504a0040448003050002c240d55500300030740380d40e014002840202d0203092081d02e00240489402424440805102240b0270070280400c151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 476728705 1250 476727455 476727473
    0x4121b03111b0f15040306110319020301080c0d05011e0c0905030c0a0603020a0c0602070b18060f0f0601140c060f0108190204110c0a05010507030c0c020a030206031e070905100c 78
    0x4400c05480d00e03001d102e8006420481c50042e41c06c001c2c000c030700741444085294100c0700558494603050301c114080303201d0242c03010220320081c01404c00e5500000d6404c0c0041c1000c0d0441100180b00c3c40001800300549081a038100c6101c10846003160346441500309031961000d040409441c080700a006034600080014490041922880f001d040e008034a681803140112184e0024940009081d50b80d4000e600d82403c001c0300840e0303040121441104848a00c610014140d44a00c804242c0105540c03140e80c2c541208100c0240024100a141640031044441400103080c03256201002001d55040003903d00c550044140c2100c1c0945d40b26681c207280d008106c031914080c007a01030f500001c00c108480c0d58007507284034800c1e1012007440369071408400c04c001513008070311840d0140c0d030801c01c1c01200d040c102c415140c030385806580135100d44414000f5140c400000c1da0026145800840800303140901104081c1f8211610400320f03540c03180c10422810704040c1070070000700ca45803181210340155500004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 476729955 1250 476728705 476728729
    0x18131a040e030909252622050a0b01060c020a061b06020c06160e10120b1206100e04080d09051f0f0f0605010804121b03111b 55
    0x41103803100c07081009a00140102c60340c01c80082e16140c00c034a8a010580c02e618008007405025080382c0800311915880b44035a001601c088501e0350682ca100306800f110024009405004601000e0010890100e004021084464400c00140000e203000c0e0620441020050f4025801e000381c800c600e10040e59080c4000081d1000c3e8100700301840103070640c0001c88442c648000740324034400580c50b80c3c403110000300940315208043d216900504010350460300706104491143c3c0103800800485100742c0140d251180100c10040005451032000001969400007096160b215410910501c110700740c41d55076410203043c000202c00020705090740c13001181d205400304140a43d5680038800c08015083c41a001e9030000d4200040c0c000340d119070300d030000301104000300841519141000e540240d181c0525400c0714416190700f401c035612511600b401c483c901480508001c1e40d0300111000080390140d0030b14040c007a68480140c081401400c40c64040c900b0507000c1c9411620004110b240d03078240034649 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 476731205 1250 476729955 476729959
    0x618100e15040501060513050a2004140312120402090106020a0b1308070b0c270a05010c0201170a0204050907080412120e060112060b0a030c0e041718131a 68
    0x10a9465003081130040041d9004250301182d402c03404c40500c0c98940240f409100c03040700800242c42841d0309034240c0d5059503c000c800d41410b02c010006000c80c50682080e400c40a01510104c0d061240c400301154080050352200350006410b03c403d500f800c0100d24050042400200034816954840706424130b8005c25910750380c802c209500b0108000602030f54611035020f485a800c42c1058542d0310b841d5007161510039560001180d1401007500406070321090984003504410f650340c01c020044071a0000a04107a0610803a03403540014418820780759882244000c5006071540d081104010a0080c050426000c000c07540702070001045103112480c026400d10b0600702148218030307503000f000e0201141c4c1046980038400000480c1814481e014a68034031840c000c0040080701c50030030507510014007010702020116001400603104009229410900602c003800b51103803500540740703450348060345001c8200c85490b01100c5500700300c000641003a00c80304052143c11070b1646e0700c3d030700104401300c507074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 476732455 1250 476731205 476731243
    0x611030c070f1707030314091501090b01110d0903030e060708120402030c0301020c0106080c10081506090603070e040605031b0103050a1d0a1208010e01060e0a05030618100e 76
    0x402c0000d43c420807032008154441c02e603125009420068005e2002d64039034010300c00800300048403400041213a900300c2c400c082421295900b0540240018a0500149814000000c01caa40129000c0114250b0580e0682c1d82000d10360642c54020018600440c0042c0504d038140040b2000426607015109403c04202810700b0b6a95130740000391404070b8510380182c165100045650f9210419001074041d030781d04d64100d500440407078051012a1244103800c400284010700411800103203018403051070040148681e060005071000640075610a4a15001040110f40b20a160b420306010700b070000c00f001c80182000e120381003000c006a00d07544001c00c0c101503030f80c800103500500b0b950048030341c00c0d44c3d92921707492000d0b03160071103070f135904480400d1312074180103ca44070390030b0b1041c1c402c0380c166034010070080c40c0d50341b0306141551268400300359030b0352111440e1404240c1d0b803420000030f44240101031180068010b040f50305820000b040382501c210394180b01c41d0300400940042c104801c180c0b0441c0380 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 476733705 1250 476732455 476732483
    0xa03060504020a1d040b33032a0d05070809010b04060e0a020a050c0609061e010501020a1e060c18090506060403031b0614070306090509070306150803070f0611030c07 73
    0x340003071140d00b030b08030340c06050f1507032242d0a140b030103007c0091004c030b2201c42212074a0714543e149141c0011a031080320840b40c6251190400d86070003450940c0302038546d40034100090806441d0a0320741c1102c0b40030002e103d000402220724024041c49a00c0302b420341d003c1040500b40116451949002843c1c801e407070380c00084014000c2e1080c000c45d105802071000790342003410045d030a2074662109440a1405002c1d103031028001103640f01038103040720350580080803001d1941d80ca4076180d05103455220b0602599441c90404284603000c5d80c0304103182c55030350641e606a203c210001101045c0c005c1000c451800c803c0015940320342d4100c4090fa030700350810a1540620324602802c04804010040071706080a901c01001c1071450122401040181c80901851340c070344801030304403801110780c00b0003503010040c03c002258150784136070045101100d00d151001c2d180c00c4000e1560b032111008039251103c1d01d002c60148980352007030002080c030340903046c0e196092200c029400c8e03002d4140083c1c0509540c00c81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 476734955 1250 476733705 476733709
    0x708130308240324180a020d2d0314071109181005010e0f13060e070f080307120806060301060e030715051b0c060a1d0a0b0a03060504020a1d 62
    0xb00328403141005045603042440c0703d400b46501c0c8007860990f04004482c0340450061041109071088a8101c140144200700e8117408110240c4004642981d00d00c840c11250f952400030107540c400c035010060181c000340074003454000d2200207103844800c1031400500910000450440e1b03082f0200d8411261003040b500c600c1d54002c8401c070b401d0041c0005101b044c00f0032245140c1a0801d074126031242401e44900d41d110885242591300440c0e100180c520780589108c009034841e400385e440090755104803811a512843d0502040e0f2050304441010750000c180b6070204000720700074400800203032810301c41500300030700850800d000c1070164402780402c501c80020f0760b4400b08084001041441500702007280c0700c0c20080c10070b0f48820081d0300920302c555280b01d0348050010b140c2c501c5080142001d0b29124543c103084481c0300aa4015120080da5100e055000b90f880d081307036201070725002a8031a0b4501c408407024044519a51159008900601c000703000103420450100540c04403410402c020a0b000300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 476736205 1250 476734955 476735011
    0x60506060c030403120305010914040f170d0603140a0b0621070605030412020604051b12120901090e07020a02061828120206030612100e060708130308 66
    0x800080300e02c0040307000824030001c07500c0c880300e51180741c8003009166210004181610407104e210101c0790031110204000498540d180340d00107000f1000140c3c00e412810081c00030368007000b0b11521950721a0b40600a0000c4810b11291a11483e030090201050b00d42d40d41d03102c28002003140c0c2c81000c030b50b07204032403031b0301c07501c0480b068a4000000e0304e403581e840781400f500741e4006840a413601030f981c400f0026803d00000d9180d003ea600a4020002c840780704a421030707245c99078206140c11011118007030752803c074100592021a604a5105500d4082c0a0001400385a0350752041e03242513540710600c05481d0700450005280d0b0f13019101e880e40d81e525101d500d214004000340c40380c2c0000c5105030203180c50300041c007908540fa804122107450256541ca185061054000c400f03580300c1e2081002c02c0d03082c50142c0070007414401610654460000c1884204101c48a00d40750200c4cd8001c4010017400c158020f140381e03842540c07400d0001d2001d100d901d00404c00d180091202c2e0804914204000426400b91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 476737455 1250 476736205 476736217
    0x50f060307120207051b01210513050307060f0e12030a0504140d082a0f070204200d1401080a032024090102030123010e12011b180306050606 62
    0xb01040d580c0d084d00d841c10940e280085070f00580c0c1401d021410fa04690302c904404d500e8000c869924595440b00741282d40001e01d4050682c3d45401c0013880303c5000100c0500182c007003079018080000310300710714a0020060320480d54841e96141c101c18203e0321103400c10b9040d0303900010747c0c071400100b41d9150b1501050062505003460302c980305032484982a80d900260107840756041c82c003814001d0700580302d5604000044403068840700c2040c41428485100c08001d007070901e000034004a4103155000a00301d140ca440d034004c001d041800950a080c04100380070320341c01841c0d03414898540e98501625140c45542d07000d4010108054508501244c10b00303010705400e0094004203a8604507140814200c0303041e122000360000c407588d140024110079040c030136a8121807500811050402e104100c0c0c00c6080c920303043c51814802c01c240c0c1240c540e154564010741c7e5600900001078000c1e5032107600403d00c42e4880080003008801c00341e51080c2c10400104004983d4410004070307181d00d6080001d11503000344 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 476738705 1250 476737455 476737487
    0x204050904240e0f1216110d0c0602100c08060a05060705011b02010b01110712030f0306081c110c060f07030318050304030b3601021303050705040c09050f060307 71
    0x49a8915010007240741911107008900301e070516403803e08407400c0b900a0b08030551000310361072404070104041211180034000000d08c12600d0000d80e80e81d160329001c0c160403030001a40040e151a4406904d8414240c01622030f0800120500d420320001c0c1c1916644d0040c0341c0500004039441c020080300750071210b288148640c501c6408946600000d000f0101354000c54000fa1203c11110900d520204914042c0c1d1941c07014041c40ca02c4949098405403415040a02090364580000881020034403141e22080481e01c49005094004040109403c460b80101803035a00503207450a425500c00d0220750034682102012502c4900d10b040c00e0b4000d00c2d190488d00720400e601c000c48800c104000c001003003503a200b00ca01340c4954454ac0000340d400b072002d12151800004000c070074041c03050152640c0044010071400949000c0e18440c1c203071214046640110b450394402d140a107c140381038000c0d4000c240f90707468021041c03450903000443c1094070107101c0340584400408298401d208115981a82c41a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 476739955 1250 476738705 476738711
    0xf0106031e0c120b0604080a080a09091b090e06030a030e15040f05090f0c0d051803280c020a0509060402131410050304030c11010210090308100504020405090424 71
    0x16100a03107444103443c0030b01042450a0a91910f07468010159003d60f14500300410380a01140c2d10351060b517120304402001d1200b140e60002e54408036000754407205002c041c4008500f44841d1014041e041250080ca1a810341c0380c3c00c10541da100060161070b00e540603e000c00440790140c003c509002141d4207010135a880001c1d0100350f066102e030004084400948030f4643e9590744000d43e2035424015110b254030315100304008a11a42c803500410f800c8507030140582501200030702064030b10b5105440c6102c5000098078254031b12811518401c8030000241060b400c5036135184d0008112003864081c561281d0242c20204074140c4032070341519550307030782c280c0d06041013500d618040c2c52403138413070352074900c21043c3d00c074103800320b91061080e03a02455154490303070301003680c903070b41d146c03c031455240240d04600c80c22180c4565013001d40242c100c811b00988940c0c0d09810204020fa520072000d0704114016401040100540d850b0741d411254400c0e0800c46607550faa44c4417110a010321b10300c0004407001c0e41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 476741205 1250 476739955 476739971
    0xb0d141501060f0f231b0a020904080903100204080c10080c0906130801020c0703060b0607030e09072f060906010302060f0c0a0c0b09040507080411040c05090405070908060a050f0106031e 82
    0x785100800c070000c0040d651b603845c206012016980c895203108000d400524400c080b0b000100c4800c05412101001000d541c1d600b00008a980f04a801c543d101056552102c03002c5102400c10340c5010420412901d006030803440d05000d140e05602c51204614000c0701c001030b1101892101805503400b03001c100000350364604a003a200e0b41c2da081c807400140c07a524a82038141040b071400f0001c4401407981519464802108001040708855009280006200c0c101c0018070940c450007003121541040c4e0720104c911111492541440c1c154010411501640101300600c05a5140b10641c2c0d103100d660f614140da110042c05c105806d0103101c5034001d00d03c40e102c00c004940c8034804c0c0e018041884041c0c0d01000641d80c0d1500456850005460140140d903601e46400709504040d00500020b014074141645009000b0012904449040b284940065140d600138840c01d41c0500c8203941104801005100c18100100000d4124006105803c245a40c0b45070826010480904c1000f024503080801c00c02c0e94 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 476742455 1250 476741205 476741267
    0x1050702040509030714061003150e0a031d0301020403080d0b1908011d0c100e030705060403060608011d0c012d09180603170306040b0d141501060f0f 66
    0x80c0248100705c078400c001c030151901b28107000130707842e12032425041101c202e00d146844500b10043c500e10f40c80e00c140d403148900318442000f001003086031392103560303401c803003042d042202540c440798940703000e2103070f4010402040487c0c40d05095500c689000040040c15452050025603030228401c01c4401c2451200c5000403a5079041d8005501e0608800101e03442c00d498480e10343c0c6801850421a83c800c4d20541c0f0108501e20600c55004828801740444004030703103a070001034840e0003070381c000c450254441c1c03020300809800b0b009401484034803440209080940840360342c2c8603044000b40a0420841d41ca410b1140b82c020300c404002c5081038900301024010300100140344075080e0181318091800b210b009171007004a440b80c081200e030040c96a103042200018610071a17480642180e900a0325254241450380c4e4500c10228094418594940354510550307060341080115125480f03500142ca004000c000e0b08154010005842403511030001c7c1c40c41c0c40246c0b4209100510401724524105008000c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 476743705 1250 476742455 476742457
    0xe0705030a0b01030e1011041a090a1409040b040204180503070c0605130902090303042115020f03040209071106010f0509010905070f05030a0204050405130303051f050f0105070204050903 82
    0x5218a07040a0050a0b0000300640c00e8916203502c10302c01c0c1c2c2c05440c802c1c16892040e8402d0f040645441ca45170310700341ea20343d40740c4200070030f0301c04500d50030400140c0100c140c075000300c44000614240a11035076001d5a1400640d00403002800504030060802c0000c003103644035800401c503081400e4240d00f007070449051007640c0741c00031034048480140146c5c0c0800e40d2030040c816641510400d001d410725030781c2051a988081d4202e40d04c0690544001d000100d102c0640e40020600c10003a519291282c0807141803100441c0381048642c185c441c4100200000b130718407030302102d5201ea0156407180460701d8010080b5042001080410040e0181000200c1c10108607500300048401c202c6032080103980750030641c02219000e40b480b0000c209074040701341c034060041e0040e40d40050346403001400c103503841c0c0119054070030403940312644826110340d0108140d00340c415240c0001015000e40403923102c00d01d152511200d5402071a1241500c6030440d0741a0f0300c258101c0d9044c0e0360260091145003082c1d41000c1e56 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 476744955 1250 476743705 476743711
    0x7020a141c030b0f120c01050d0b03060405010e070905071b1509080316080c0d0c0903050a030f030e0307050607080a0e03070f120f08040807020a0306050f0105042009190e070503 78
    0xc40d882010b001c00242c07030202505ca007085200809440d000b4010341c010b55081d40030060450749035844000350aa40e6406020142c8a28000c000209a00d100580258144202034005150040c0f0300428007003ca40e00202e25145000000c01803408000389040c031400e0b03414184200c000590410001108121312680514080c0e07803a80d03144441c003e03504000303440f001021103608078604018402a03500e40c41c0c1c0e402005080545003481400181c0325141c550500010300c9054010480718040c44020651511642442548400c00f450802d03100ba9500358480c074000c0d060104100e00c40011905100341a030007840107520a800b01d81d81e503030103442c00000f160000349045c1c601c2c01c3e994801c2c41c44140180030341c003000383c01943e4078240d82d51244e8030034020350800784060b40c200415030b81c00f00000d0214407415006451100c0305898962502c410807080d43d03941c0714074040e42201c0d00b041c0f02c011194242662014a0201c40075514034131400c0c060b8003124590f41c05601c1d00503400c0184000250080d0003940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 476746205 1250 476744955 476744959
    0x8190e0a0b21041103031206032b030f320f01030c0614090405090a2102071406131503050c0f0702090a14072607020a141c030b 56
    0x90103641e9140d0501507020300d00c0e20800c02082140324a001d1492420403503071041c80340500341c03208128403000ca491904010200b1032020282018000d007031904104082002c043c914400e0848140d111040c00103c507410b084600b8140c81d44d070107800c5190250801128811040000b612902c601d2541c041c4d40300030030791403805030810140810319a00903031344903d05aa8000c804290410300c0c0680c121004060090340c101480c07000c1c04060b00960b00c13405546d009d0b5210390000d0615502c0390810740721003079840c1618041a90400f0b01c03007880640100c1e43d0070898402c0c982c0c545907401d1401c00b1550702e00c5490880c4800001d2404049902c0c40c2a801002d5030021585d8104215500e0400300410b41c440c0121920101d070741404600014a881d6195681c012045807010881e41807824001e10010ba059646030007042c409900d00340caa0004c4100f508150060060b009884d080615010b074440c2501070300030300407a521000100e2141e9040184c00c3e110f5000d0001e076183c1c40c40c8110010001c10101c0b43d070034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 476747455 1250 476746205 476746219
    0xc07030303150303090302011d1302030f0601030902010828090305190311030402060d29032503171201060207061b030e040f140c07060608071203030908190e 69
    0x42e21070004980303900140c0f50300d6215008071500356001916002c5510016003507890340680d200c00280c448414448007564400e07009a1a030401d400181032805008000e5130415113003607000405030781d200794440d07006191101e903400b40010b800f0360000880d00c4041b2118210b41080082c03030406a004009000c4610801c80d0983c080850400440c252100070010b500c40c15024004074001d480c04000611420100400009000c3e400f500a481040b0101f0718204802085030041e10183c01c0511804000c2c008650300d40100030f01c004050701145000b800083c11382d088000300d100c1030748010411a524600399580301040c540c1e607400020340d5202e49006000000340c4070341c0031003800003250103a403082c56410348942a1004044081c04000c000314240300280304c2e203441480c0c0340a0140c04000780516904107406a81d4040e60070008217944142c0d11040541e80211001c21604507c03680804940394545070101c1d4554550900c44200d0040d080907020f03080006600104103500140c038540781000591b814 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 476748705 1250 476747455 476747471
    0x30709151401090b0d050c16240e071a270109090203070f0c02040f0606031505091b1c050c0304060f0b0a12060f050705070c0e060d0803060f060c07030303 68
    0x444445945110301c01c0200400e2220000c01c040303d81246c1e40c881d0b07561018034242040001c80c0381e0503600c1d03024183e944000d481e040d800040441800000c1e0644818000e112710040303462920307920f003164450101000c00e200c1c1c42101310410082111200c0d45c0f0010039415546240600304069504003072068040b0700100b00009a004050081d03a1040041c0d48400980801c4070344103031500c0c0400341c1c00700d0780244c0e5080c941c078007000207110b083c01500448c0c0e40091031031000101d0480307032a01508124030a40310325081100701c8503e030b441c0100d07548450000341e4466081c0302d84604102411450940818180700030010401c00319030103148140c2c00342d03c09011010701e03103101c41d0440d4442e102540c3c2002c103d03481808100012252050541e215140c001802d010010340d960469505031000c000103040050a9010f00401442c03003c0030785401e41d0003000c1824407900040683c200b52400038100540440001d1243d42c5105890100c2c0001406c3c10f503403040032030140c9840f0341d02800110007082c580186 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 476749955 1250 476748705 476748707
    0x31a01260c192a11040608160b0c0a03050a05090a03060207050c0d0c1a040b120105011404080604140a0605040320070e011215110901030b1c020f030709151401 70
    0x41e905002002ca881800c0101c0c0c16450262140b20308100f9104403000c00a43c900a440c1c0b0700c1b42c80003c00698001e0603240e002c5603051416072034940d00402c10940203115405030b8990100c3d16882c2540e150403e580e40d190416010740d02809030300c1c9400c0c3d10041c0d40a0000c14000141c00900c07a0034891020b42d0721100d151000c1040040d0005000b500001c131846081c0030801070300441e01100c942944031380313080030b50f0341c0b0340c08141b948036a005040b0951b00d80c00420841d600825040d40a1119006031390400d418111a2641d410000780f0240c010203030b0a443c04045c81b01400002130451708024103010504d82418040c04108200202d0301c210b80040020601d0a030010680c007064804264202c402030b46080341030b043d45482e1034400d0301c840b001d0b4090034120210510030502c102c1d50035820691120b08a40000d01200c2c42045814000d203096282c0c201c3e05541d1100041c00691304031045103071403a00d03601103071030415142c0010110a281c0841402d440062041c20400c270340303c24400c59800484030300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 476751205 1250 476749955 476749967
    0x18081005071e0f030e06090d17010b030a020f0702060d0507110a03090e100806090c0306010609181a04090c1404060e07111c0f020d031a01260c19 64
    0x710b1403008100006415228901042c56042e0070300d4041074051508a8a90400781c0c1900c010825600101542e20b000e5040048a01041039802c043c071543d40c50260804554030000749021a419400240804030034880c00640d002c1c950040d0000d502e40300720012800042206a44020205910361503081c552034000440c0c840982e4581e544c1c825803072601c610350b140c5141c060071048200c8845500460414000c008007441591143c0082810380d504d4000c0c18100382c81a08402d0402003003002c140207010a100d142036861a034100d000420f588404410302c801c05005109030790040c00e000094040c801c4000ca0b0f54103498401e4400ca0403029908204011910b480c1701c1c0304250b0341c0b0400080d603441c0c00b651561071660b8a0030300f900d200200c262030f0600800d0003203010030042044550310211031981008040751000b00790500b045116841c0741c8088403a48002d618604001c0c0c940c0c020b201010703005040e03566040c4100354101e070034248140d2440690b007240c20398100070303207490903040d440500c905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 476752455 1250 476751205 476751227
    0x90108030a0509240a050301140109030309061110020a0c050115050307210206030a050f0f0601020618070f0326030705040e06010c1a0603010c14030109020a1808100507 74
    0xb450301c91500c101c0e101801140c1c00c1c00c500002441c501c00004440300c40340b44005080e00755440c0d40d03d075525810850803c0001040c0e405c40e6040200d10780b02440001e8000c500c00c820740c1d0300d508000411514206542d40f801c540c1400740034a090010a00280d501d400100d0401000e108600a0241c00783c038508601d2a09100d116072075242c1c2c000c072403c0040d445400c44854140c50300e6203028840007031a0300461041d5005542001d0f103a550740d01040442e0001e1441c042d001070a56150510390b00700000000e5403150b0240007925540e080050000301400c04000c51402845c00c100d124080b184c2e2410b1000410742c4a400007900c02c8440385941d440580108120b900c91012610303403a04182c184051120071500040141d07051180452441c070200e4440040382d040419204009205031030000281030944032484d00c40400e000c816400e060655801500340c9065a414500042c0c4911320824100d40d42e9101400e0000c144204000c04101100c001c00c140031000d1315400305001d640c4840b1b1080352116540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 476753705 1250 476752455 476752457
    0x112090b0c0703090806010608190e07090507020705031e0d050c06010b0901030902032512020d0213060f030f060615020c0118260606010c0803040b09070f0e06090108030a 75
    0x100c80028800030508002d42603050203481d014003c81d0302d440c4034600d819020f8001501003540300041083c0001d0585024202820140040c410001c021502e00e60301e402d2401072502480e210070000d44214420414031004045c000c3c01c40340c3c1c40b111142102048403e00141f030300540502c078a15a403403400390045802e5030b600b290082865a191400b402c3d01d40d0001e0385500d040580315482c03070016035020499100300c200360040a040c02d0025031031521504251754012a0703110b2101c41c1c11000360fa515005031154580640b84244001090a102001040f80341c2240303014400508021050241d02400682c005110381c0041000f20746400108203071640c080b00d482c005034800e0884d41080d500c50a52450004516011690358640354424211141500d1100e00b466081c18415002401d2003080030301e0b0041401c0c201081e0010690700c0307184081c80002c10141c0460040d81c081058003608206220003408545045c0203415210344c44c0600224058411714030482c440d40c00452203040200c102e80c0030000c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 476754955 1250 476753705 476753723
    0xb040b01090605070f0812060310061d090304050603010b220b04030f03030b03100212010902040e010515090d231c0e061b0703050d03050f0703022511011209 69
    0x1034441d045030f00b507200002c1154045440140100010410006400c54420320380c46c076840c600c0e00030185031801200d51070100703115041c50002c004a800350401c0386003019800c0c1401d9070964a15100515620440d888a41c20480000c000030341049813070050041c42444100b5202d01c010802525400300c503060151020b541c00800c0108001004a102448100e00c60300b0040b4107000d8240001e401c1c146944e07050030510703400050040d12201d681c614030340540b403210b40c110b091a04000341003181321014006c10b07008484404501880c50358031000d980031802c0044c06080421120324103004040a000b40b0380d0f00d945001e45460300c00d640c01280c00c01094100f500d40b50015040403008440e0300020209960b080b12080041e0480e800c100d503d80000d041d4408020b0070382900e0352401a2900713564415141c1010b14146c01e1000ba41c4032807541c0e5400c0b400c0751401523121040302c50b804851508095214200d4090304600c6003c010480004058680c002d03260300f90329500300700440c001e8a924260041003004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 476756205 1250 476754955 476754959
    0x4060807050309010b0a0b030601180b2a12070c080c090a0b040b0d0614130f02040903090b03040c06020f0c0d02100c02180a0c0f0512061c03050c010b040b0109 70
    0x2210764007540c0c0c40090b80b070021440d01072010102e0b4090000d038020800c82c00380041008200c0d600103074a42c00c1030140e140d80d0b021192030110000b0090050b940c00d0b0742005a190000441407809c41c207158140801e81003664011503032840050000c3d0312081c0102c036843c204040008246101123103140200f040508403a40580e0342c2c4002c00001c0503082401a40036580b50301040942c5ca54100d044174043c4540000260380f0070440910000c884000c0905940d12016014030b80002d01c611540c5e00d030107030f050f90041444a16454261030866094100c0c1030314003004003c0109114408000c04201ca40f1a000d8503289461114015101c5540c0450b0315000313615131103c5401814005000b21440e1000c0c0341200d448421680003404d14181032684421100101c401e01800f00c00c103120f0492440164100b041403002500b0003e05917001e5400c00601c12900c410005540d81c64a80c060303514240704241e2440b821115240c0035060381c2101c103034000c1c00e62034144420f00d0750910744a4a080c1c40782c16116651442c5c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 476757455 1250 476756205 476756207
    0xf0b0d03080928060b040b1f02010f110a0305090c1e060c0a120314011a09010e10050d05060405060f100201020d09111c0b0a02250308011a04060807 65
    0x840a40040914030650301003140b02c2086940001d1644460111820a41898100f507000e070380c41800802d01c242d07d000c081031406d81c1c941c1c040c0c1140d01c1c1c5a030854440004c616100341d00400000d056101e00e00e080801d00300c800c107141c000030004c12016031410010b94640c42400e07980c5a01d14035046800c40244c040c0d070140e80b000708011030321141001740303110724040c1c019903901d04017407604004481031120f9409004040c0d070507001d0020140c0242840132095031501800030380a2100e07103d9141c80300c0002072200b4040e4440c181300300c0702d003201504024130388801c02c000504a030b01240302800d48910b4900868031516190207000e01a0384028144510101400d0400000c003541b4181c0300151342d82000761004201c0c540c02007240507400307400300804010048003400700840b0a8a60080901300108240d4006040c4c0008550000ba02c2440140c45800201078910b1641c0403903c0904840e0080c81c4130b004050340151103906036454030441d440c0482513981424660f000e10f006244c0402c11f940006607401d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 476758705 1250 476757455 476757467
    0x1701060504090213180b1008060306180f06040b100e04150c09030c0305070306050105090f07030b01090503100e0f0a1109190c02010b032a10020307150f0f0b0d03 71
    0x1304003034001d07042d122541d40d880c00151005000344204025103074841044641303040d40c0c040a02c40070505000003240303050310010340c075407500400c5c060840400d10f0341d4044110b41000405801d45c3c9040c01c440e02401c1c1070a003049000f074212580186580c0700b05011903000302c000c07030060041c2c0e40280215540b18205850070042e00c818800300d82005a02c480000100e06244014001103014401070514503046081020546034140c00c164003075941c100500c420f5004141c070386a84003c90b03141c000750b03030802c0100485a03002030b035203e564144110300240c0303032090040e4840d10302c000880d000c441c011034107818440d894894005000e029042e07041c1d050703005407c0208040e0b40c40310783c1d40180d82012017640859000c440713459040100507955007080c19880d042c01c00c44841e00200205424558602100140c02e0003465144a81c1c000c150025000e40c50354000c005440c00d81c0d0344010b001c0d001c1200c0c41881002407809040b840700c400e00b0842c0302c00c005600b6228130300341c1030b9014000055140550f2429190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 476759955 1250 476758705 476758717
    0x118060e0f0a0804180209011d03011b09051f0c080d11070506040510050c0405130f0501081b010f050d15050301112205010e0904030c0204050408090117010605040902 73
    0x501e00441501904105081c882070321030512501c1d16689640c109012401c1e4084d040110b00c1030680304200c0450030b81e030005554503a900c010708284600800500c04a030140011601d0401d0b03991a0032441d815664002c0b01034010352f80c05a80c1032a9040c0d480c0d0842d1045520100124085a10480060041440c01e401004c815242d1540428144520504042e03203621140b01a21070303811a6040c13004201007881f440725410907441050050341480d10001405104911901e8825207580803240d0541c2d803260001c4005480b5084200025a0756a091f143c84001c1d1035164260740c1904902d904080d0301031551003a0040542d52018185030250b29080001c10740840c410f031200e03d1141e400603107960240203000e4804d2024081e241c446258a402e907055000720f1000a0207900410400d01299070300000e1a1240d1008840012243d1a1402c0c1500c011703a030364401a400900701400c04c01480084802000d005030282c2c0c500f885011803000c81042c074207080c0140400103000300001c010461854000e4a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 476761205 1250 476759955 476759981
    0x11030f0403090e070903030f021f0b040605090f01032102030a0c030c050a06020418090f060b1203040e06150a080f06040e03040806091c0806130209060703120c02011806 74
    0x30442d078841d0944290307000c04440c08000100084024020076502011158181036580010700c261000300c0c005528595148000081e21035031003441e0034240c3d07a83c0d0030040042078058005981ca0420080c0204100c1090000b0750700341d10400709503c2d00210b802041e8a84441c0c50b03010311304104580d4400ca030304181100c1c2c1a03040050801080f00418000d11042c9440b40c4181801a50380f0701e000bc0c0304034140600c0d4102c1ca005494105d5060103d80000920180e442c0c0c0f01000054540000e4000703038514001c00c484054900c00030402190010744141c1c61806070000711400c000c40e02c04004180c5061040c0300e031010010b1a88008075902d1075522903150742002008001207864003980c4030091841d0025400b08565a00c07050078845810301c24012881982c0745003a40320304030102c42c00090040302001d81058004d103901ea054145401c2c041d410780b060701100410556480d46982002401003601c8448442c1852805c1c0b40c42c0310242c014841c80c6103680c030070108001c1c00841510b82000503d00801814 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 476762455 1250 476761205 476761217
    0x181f0507020913140d0f11060f070504030f03020a020a09062919090e0a0e060f0402060d1107030e030304120f06020405044205040c0e060307030e1011030f0403 70
    0x4400144d921004aa103480380200600701c0141c443c43c02010046e0440040c010310030f000910080c14080895019449849507009182e15200d03c1d01c100c52510699002810000e0720148507800c141c1e010417040300d8603008a50307a0001c15203070300305101100e400344203041c540c2e669001590040d007103500110018100c4075a0749420016803400e800c1008207103800100014101c01c8051003265022083c05800045850b810272810404081c0746944440180503501c402c1d409000140842d41c98804a0784202d0504a00b4490300107290070511b104c0d04010821004900342c80005100c9040002c00d44040701c000802c9190600d9840d25890922205a00c2c00d9815603001c002c0858140c64074042c0b40300c0c141404a02c0171400c0003e100002d00c00041c41c00c8501e07200c0800e00c0c081c1c1011200070b090001d8030002c0b00c1c00034200140b6141501e40310400d1a2054102c0004010401c290707405610100340740300810240e0307002001803480308003191082509a01c0c44641030000c030703120142007a801039000d486800c1107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 476763705 1250 476762455 476762491
    0x106181e0204090606030e120703270f06020d0c03090b090613031211030403120f121422020604121406040503091e01020d0809010b0402181f05070209 66
    0x41030741e0168100c40f4105860304410032050303501d1710030b5007001140707040500b031080d56140341d4400d01e00c0384480c007900704000c0140b0944040803106540040545005480140765a11003d110740da0b0b8191080c10054090b0143c00d802841c050a07104424a60542e62801d0b021300b05130b55041aa00030038407258104500b4081ea111070000c44000e4405580101e0740705482017616400200302706800d141d09140ca030002e20040000826102c3d0007040e1344ca260805191904032400e040303440124000240340b0050402001100003112081140d010302c85400700e0588030030708840314501140e50310000941040c008c100820440510203000303401a0f2092800c18402d0413500f40302032030704000303480580b00364100043c510002c2ca000d416414103200442020b91219500c4c50000c5d40b10006400c50005000444c40000c1200c02c1c2035210100401005108548030811400300c40c45800c81c03141c29601400701d06107104c400105004c400d00324501c0e180c0d1520f00e41100ca07402d10000765805004180c0078803c1e0322007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 476764955 1250 476763705 476763761
    0x2070302031207121803020402090f06160b18060a05180304063f110d0911030601081612051005040803061e0310020325020609060108010618 62
    0xb11001650701024030740c0d103c1000d828400c031200e192403000b4091056110207580b41c03001040c01d0b1012a5011a0016110428100499035440030b103a010341c0d21240000f041a080441d07048440102c0340900c10016103a5203d80c4450844c084500d103108880c1c3c40300b400550a4100d541180d0303401010480c1c2c06256100d28142c00c2c0c07641d0401e81099000c1154022800814081c001442e81c4102d05142c001e081d11303001c00000d0700034007090074110099035250000000343c102c2c0b540844800c086d90f4101000501854142100c0030380065040510a0007081d000081e401c2c00001c1d550001296840e211140314130b0a103102501e40c1e1010021a4107026281d00348150a08910075076100b41e001c2c0c0c3c1030503500e15042c5c08005000842d20056507500f1062004100551000203c03124035140c20400165a44c407241a4000e42e5420403007501454a03a002c16260081e901113a998019403004045401c96600d0f80121401c0c1e81290045060210710031031320681000064110303040c0c0031010480c405e440843d00d29 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 476766205 1250 476764955 476764963
    0x30405091e010b122203051605030f0c01050a0509060c0a09091d0d09140d060b0a06050c07080c1305070522060f020303040209160909150e090307050a120207030203 72
    0x11001d107403c00c1c04502090751521040b003a81d840503040c2994014990b000e00504c04100c02c400d80a800c00c200418000c100c070b018451540002a00941101d40354001c0383c0c1801c2080e80034070558461542000d000c10990701460007001e0107500c80102418069590700034101480c0c00c1003042d1420440d800c10300082643c0ca82c882c0714000d003201c1841c241c50300c1010060524048480032854200040326204100068800c22203040300001210006d401035400c1c00d28102801882c100c2039030100165000090260b0090b004000c0d041040080d0380c603883c1d0b100e28454881fa030b00c3c0500c98014590000c5002401025070025a00800720308280b802c013180c000b81d040400e0500e9082c0006060954000d201302600a5200280c0e5001071000f0340c078505d0540e002c1494010083d1004000054008071007203520300401020002e0100000b08004c81c040030400c0b401840d803948500b41042c141000132403004d804c0070040318921034021000f411102743c19034032035500200c00760005085000d40400440181d800344 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 476767455 1250 476766205 476766209
    0x3170106030903090b13090b04110d050703150812071401050f09060901021e0717070b010e060a08032a070b211e04232103060102030405091e01 63
    0xa640000e40102c54503000d04030501c2030304040c24500c0140000d903001d1030302880701011f490b03000d24003082a40d928004030300944001e0407001003200e00410380d05d07904446544240d204100d15603040c003c0c1c045055004807152807d0003040d015400c000030401c0c8800c0404010086148641142c1d4901c1c07181d8601503003101c4050341e03400050a41038060000c410f0f4104082d58004039110021860300c1510b403003900c0740c1d604105121407035140c08220401400144040c1d4070b8000c0220f90426a66080c130300e080d0b42003940900a00d05503441c82e401003041030a100740c4200507541004000d624003c00600c10b900d66900b121700071001c00714040403080000c030007800b8560081c952203070725540b68400c9890f5083e41d040700d01008a1800d048070204214050611040c2c401308000e6081080030380c55509021144540400b140d0425040c0400300c6e00071728030009412021101281c1100d0034400c0004003a14080c4401d41d00ca90050b8018070003840140340103c40140c02c040c0311080e5507501e0040c1c2c10b06a103000026 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 476768705 1250 476767455 476767457
    0xb0109291c110306011b0f1407080d0801050607020f1908100608060f0c0307050c030310140103050606181c03030c0206090d0f1d0d050105240307090903170106 70
    0x80c600d03050400a40703015201c20518007110b03050451401c0d2000030001e09005001542000c10403080c10240810240031010b415041a44000c0f05240f441501d0398401a510039503586101d03403058903051038410981c2c83d059030350047c0316030b25040709602045064980900007561140c421b0b00e03460f03840c242540d40840148040b1010b0180060354014160490703003aa1b0200d4034940250b4100b0035151181c1d00c1840d80650a41c004980300d4451013802c9481d4003d03103c0c0c0090f02c3c0300000900903501704000c280000c8509058041c0607490a0000440c10b031081900d100390404070510200340c640d01502540070070311402034040001005143d2000d0382c500c0030345d0000d40209a648014201c0603505000d500d51061840340100b404421822005107a010007074144010000c1103c03240155041045514003100c200601110f40b5000508005008143c01e403840ca1181030840c0c440e0815450714402066a40f4004014040c001e2900000201400c4080800c904104503103800d0700700800c020345030501a1551b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 476769955 1250 476768705 476768737
    0x90f010e1e04061a030606130905010e010e091615020c0901030f0b060a061d040e0f0106080d02011509050406140108030304050105010b0f0d110f0c01020d06090b010929 74
    0x940341c140412141c59800c0001958150310742410103080c94021a0b4000b04152105c613a245140381d4030031507104d2941c01480352141880000201d20036030b122454181c0d44200e1442032143c0315030742501c0d0341d00400182030b071080c0030b10726040080303405130301151941820314010f80e214142c0c42c00c002084a0001d03002102c085000040d2801405440c038180b50340300005594098049060020207417120341030051565800380b01c0309072010300d600c89800c001038400c0d80034202c81619651460840c0a404070740200040307881580c05a05182c0d00c1402170350500e0500341c085194041c101000781c00030703020041040c1c4607a82c940308840c01c242c008181d014001e1500401075600d0741000e00c5e0050a4410692103c0c8060f00b083c4520b86440108078122811091240000110045000f4500380b80380070307110351481c049030041032421300d5032410f4005006020700841d04101280e140c4107640c084030313030003c4003600203242d4140c14801c01e00124041d085002004e08181c43c01000310300951000d078410a8810000d107a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 476771205 1250 476769955 476770009
    0xf03060902120901060b27060717070218150d0c17030a02070e0c09040e0705030105090705011103030103081e16080406030c0c320307030e100c0503090f010e 69
    0x400e12490014120711001d1502d004102c58004189289000382d847c2140d0200c8a100311030341e51482110060780d403248e020b54605501c10b8032102c554214240030390140e5011884880c00401803a001c5100f01c0c03002c40c20300020b82c5030206000440080b8501112115415540410084910450701500042940055a44060002c03009040504070b43c00521442440014030407000040015150f0208003030300c00103902d40c0c2d0703a01c6592502000d03030301c20303074155180006102410034042600c00c161034003a2036540160300c0f50b2003115624482488080e050200c00d2000c406500408050502d907054000c000c0f9040500e4103030000d509114141046491900020f4100300030b581500a1004c0c0302a45c0c01d10b070204805549a20000f580b10070841d4904070320000004c5800717900707110500481000c3d002207940f40d181529001d0035614075000c06601c24006030782e4140380b00340700b034510122043d032043c055030508480d44148645c0d0205000501c3c140a1108582d000c1070b10b0301601c1c241d02c2001c241090484103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 476772455 1250 476771205 476771221
    0x60603052103100b07060207020a06120c020a230a0b070801031205030910021c060f141c110604120b011502190809150d090210050403050d0f0306090212 67
    0x70602082540006500b0700c10091000000040402180e140c0d00700e4954854203450040028405e290000f94090445603000c0b40141d80030f4004541d40c0e941650030492649400000da0341d4241300d21000b4140c0c07110340c10b04403800010060504407694650101d0340481c1481d60351880c940b100302c46003800658200c00400034041c5031181d40c904c55045041061450034503907402500c903642c400020003800c0d0002508a9004107130040340e03000d0407182404110594850380114850340061042d129500244030860400346000d0b40d8103254000d48140d000340020715561000506440070305aa540840b05200009440d0030b280d60f1583c83c01e105840c00c044c20340c1030001c01e513603030324000c10710104552103004a80c014500c124a45003145420401490301c034000c3c100043d00d080c403010400c013982030020038151080f144607085a18410300c200c491080c0200c1c1d81000311803500036844040c1440c0e0004102450060144042c0b030603051440c9008100242c0301d5000c4003e990003411950800440041004444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 476773705 1250 476772455 476772493
    0xf090a0b03150703140105010c03050702100203040807060903021807050d051308071a15010903140a0501110c010c052b0f0204080a0c09142d070e190501021f060306060305 75
    0x2d007202742403407048038855807402440390094002c024060320741c3d4500d090241d4020400d0390010301c80c040071a031135540ca84800600f02c0005101c102c1c0100703c0038049071100704445003c2407040802d552920300f020320404a0002826020703213070340b42c07481c2100007000c0807481d143c00034080b090040b51582a4547e442da580107800100522014010640340c01d80c04083e80c2c080c080c2c81c21660418a0390f0410341c0c074941e02030300305258076000074007039032900036101400500040a080c1302c0081c10020001c2003810403080e10a803003442c00098425503000c00d400c0303452075400c13602c8001d01c04654001402e02c0c03503a8940c1040b40d01c0741d04a420540c1c020030401c01041410012040940440d03c01403010140014810001c064003600c0d1341004100419503000120456580c1c0c0c0300c0480400c03411005003071061b806041142c2200310b5901814554a10f40da8042c0c10000c6d80040b11030603401080c0100a041001d00c485080b03504c1003501c96111440040440c00ea030281c14095405000580244d0080e06204a41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 476774955 1250 476773705 476773709
    0x1014070b070e030d0327030e09131b0315020304150e070f0504140411010c080a030b014a0901090b011106041e020d12020d0e0f090a0b031507031401 65
    0xb018180960040a070006c0751030f000100c2c00c4101520150384442c070303041d1040440801032076008028102048034104413442e94a0030f01e03009102c071170702c440a40501d803140c4408134000030308407291030a10312842114550003141d10500a9400b400c6040080c006001625010681c081c1d05920008050000148481c2964020402107401308203158805042141e0550020006000e80904901d815003a07400346005d04400740d4850001942c0380b00d48503000d8000c3ca81961440c4c00901481c202da01c1c0d02c5820300304d2404011407444114802c00c0703200c0c00c0c1c0641c42c44049019940108044610b04640c80b900c0c9a140a440c1c220f0f004964180310000040c03080c2c401c80c600080e10b500246c14400400c2d8601000d50a2800144101c1c17480c200300d001203640301002100041c80409d9811038030321055800310b200341c80d607001d41d9100d98000074254100481541c51419076948a0450404101c001c2410f91141505190180607681540811410210b10704001c64000010075284da030040200389000d03800d240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 476776205 1250 476774955 476774957
    0x151e0906080c072003010b270c04260705030d08041a01050a0311031c0f020d02030c030a0309020a05040e07170321060a0509090703020102060a0b1014070b070e030d 72
    0x10614246485001c103030031307110f08041d20455091300caa815685080d04034000507000509540c2e42c00740c4c0c2d686a04580d400d0150b424030400300400207c0c841c0c040d070b802164100d400c08504540d2581e40b070480300700c00792002e00e480c4006101c1e00b407001405445c10701c0702c1e8080620a44a24105241a0a098400c0760307240d200c500d241c50074800148000d6031131011590640e600b010401c0501c104000119243c0b5030002d00d207c078041c540260311003103d5800000c0c41c0b5984215402d0300e1710402d620205a81e2402030b4071440c0c0143c1c00a0000d51043c922941c403c904050008090114040d900d001240c00c0340c800c60740080c0d240d00001010302003c00c030a20360501405110004528010b05a070300e12415803201002c1c0350b6441100000704265581d070745854070281c03400174040f5440d410110034883d0b0718a101d00c006c074058005c550019885001a104045005070040d005500402c4076802c02c668010300725031030002030201840128041600608480d04c240c20340c0e00c1d0b16400d0b9001c0f1007010316007110051524 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 476777455 1250 476776205 476776207
    0xa060320041d07050409060306050105010e030a0b06121504080c0d050403080313080903060c0901020d0203040806070c0c09020a020615061305040f06030501110a03060806040804151e0906080c 84
    0x800c8a141e412040084140c10042e900c035150050119028443d40d0b200c650050700f881c501106101d240d600c200c0c101e0704246c892903100c000f400d0a06856990852000d40200400000602035051410130402d03450b01120a441d51500740d00203081810406a4058440810103d08445000320421403000c1c0d81c0c105041071410540b650f62108407034400241190b0701030248440c2c034410030104109440d0750743d800130241c419a181c15200d440742170b040b0760010381c0180305515000030414004001c031002c0c0e55506014210550316a00d09651406001c181103803c01c2d040c2c1d20014983c0c0103440500070200155000d07203141d040030b1908440c250002c0215910510342008040c03005204480c4940c2103031402c1d10301080c0681e8001c0840002d0240d40c1c00030345154203086170044081c69202c0140b50321143c5403010040f05480d81c47c060b90b03070f61044030000c00d0110200402d001d409000140707903002d20418075140c9449001d807060600100007505103036010410405081c0005500040016445a040b03c441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 476778705 1250 476777455 476777459
    0x40c0e06090f1504020408010f090302122502010509060d0603020906100e2806080103060e06060a0e060604090c0e09011a0a1d0d14060a021204021e0a06032004 70
    0x4142289006010142195043c8200c4a06521981c054a009102c1f4000801185145400c96809071504880c2100140a0401c0500002c000d40c801d8a00c01c21984010b48089007440441014800300031506a052007000d1080c241d16a6801c1c1c0104100d40c10040007040d59851803050115118014280300c3c4100241540482c016074401c2d1080324a04044510325542c2d4a0444110790641c00c50700e51108042c00c680340810540d1300000d0540c122031007840c0c108902c1001d54412600c8a000f50384051388030300380e01001c01000030b444501941088004000e5031403c4d6903800300781c4c11070300c045030b0380c801141c04e42c42441018580b45013500d00404a00e084647c1440b80c003040019035100d407607a040c0031b02050b440744564040440204210300400a45030300900c44180c10000000210781c4100b40052003004002a00c001c541e0090301ea4010b002c000c000d119880e55400c0110400806000c041c88031850001403980343e44040c0b01070010700468400060841440c40803030001019000f00d9418407a0030001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 476779955 1250 476778705 476778721
    0x3020f030a08070c14070617010504060308032701050f01060e090702120a09080f0703050706020d02060604050910112a12070302030c24090c0109090b06070803040c0e0609 75
    0xb0307484103062408040b0f00f400c0d45441d9140d85c0d01d040014003180702c2c2440104a05802c14a184400008000424031036a82da504110a54449003c000d10244042c4040f50101a021851029400394006040c0c00c0c80e00d04010a421200111802d140981c40c0c000100440ba4014000c4000494203807000c004505d00001c002c0c0da503440031498440c01040000c0c0829a4501c950401c401804c0104107030b0300c5004100c26130030395075001c4d8003090b54180100c8a000481900001e5180d02074842c40d00a006681d44a400308401004001c00c419498042c0c1200407106404501c105600c110358041c1d419152400759981c04c81a0b20314590f0300507001c220641890705c24000060440800480214099503100c507450200d0860007140c1c5a80c4486c441c0080144600c1138000d8407803005100c0e001c111412341c3c2c801c10915551201ca181c0c032404a84030400a001500745900b000d01001d00c0a4491464041e0640c1c079603031f866100315826141445840014030049018200c100c1e0001c00850b0000d000e4201422 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 476781205 1250 476779955 476779967
    0x60c010f0b041a1518090a060e0108071d07091d04031e020601030b0402040b12060105030d090e15032d15010308030c07050717030a020d030501060c061e020403080703020f030a 77
    0x4040302084d804a4040805803000305a0340c4d400f44043c124445500302091080c001d842d49000d62102403044d0300011401c8000000d0702d504a07050300d45100741c1e0b204445103590081901400000400c0040480801e00d800c070200240407484018100c00624030709418010a4110280c010203d810544080400b40d60360005030036043d283c10031841d07542c54440f48001001010040b200365008034410000c1e00c0868008600e80c0d0403100141e0a845044601c110122540d080b54010000f40e4200c04000c5810705115000d0303018519800340455040440f008510345540c1c10161890811504a0f1940c0c0341c010340520008407501100c2c0c10410040d4117694546505020042118800d107a0110707001083c007104006603001030240304681051000303041c89554990344400c0c0b2560240c81205000c10036103119108180c100e0f020b503641d1180c0e060040c0e80712005040c0b0b1810390b09088048540203030360b0500e030f40300070401540b2502c1619551515031801906020001ca900b05503504107115424250f500030b0f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 476782455 1250 476781205 476781229
    0x3040f06080a09050a03170c09010f08070201090803130510021608030406232403060a0911060c03091306030804030809061605010b04060e01080318060c010f0b041a 72
    0x1007031800d40c550301c2681c42c2e0010140501c0107031162207850821028141c01c01814042c1ca88020000d500c03075500c200a0050364801d001400340000c802c24180d0480302d21808120f6000700061002103200212034882901c0761704181d8054900041010030142041802c1105055505918105500f4001c004045007200c0428480241110800100042c200b28082e406a0403000d440407080080c01007200038041ca18804640b0290003000314160000c0b002c01c0d000d8218187c86009009103016510341c0c01c0301c4042c200b200d4003110050590540f1269070743e51a0060400203d0140c000c5499115406c10803050b40c642000040c00c1c2d070324106040c40450682d030221016690400c01003036581c8044030100302030707200700e81e00008091103201c040303401c00c5010f4019150001c03045909100f42a25140070301c40e40d250a02c940040d5070700400038407000c1c55407200b0b91140d0704802002e660900c0c0303c00740b5040c02d4410f4400d6244105135500800300c2145868400d24030481e943c01201c0360042c0c03c020205a00d020344c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 476783705 1250 476782455 476782457
    0xf01090503092103030f0103110301050f0a0f020403021c17040e071b06090b060a050a0b0d09060605180f0106090b0a03050402040209040213030b090c0603040f0c03020604031101020d0203040f06 85
    0x3400d5095030030b980362040d0300e050f4800c2c40480307640c3d2502c24040c51500400780000c6500701d01c84104110305160501645010300800f4880003400d440da02200f000800465403041c000a4003840000301603a6207010012440c4c0c0c61664041c0040b04034900200e100c1c02e000d465558080050201b40246a10a02c0da00c1d404bc0707590031311412041d014481c458985000e031000030a0503083c00c50702c44c00c0090b00ca40c09030050301c0130740310811b010303460740708100c120102c0340103100744950300b407001025000b030a03003190766450700072600000c0443d1030f0000300d0201e11450540b0f4504981c1ca0091002154501e80360a0040038a443e00c148018240451040244180001c030b60426031144046010365580303504641a0140080c8115604c01c00303503048401c1c10082e88420307140306200400241614102140c5c1100701e2038000c5c1042d280d0790b540c0d600d040d4500440300c8140c5400c0e21000b40400140c60784c4008101950050303101d0b0305a142d844000905c1c1146418103401150428001080600006800b040a44d0b4039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 476784955 1250 476783705 476783719
    0xd030219021f02030714010b060909061c03270b030f3102010905040b0109170f0a14190209180109020402070321050103020312031e010806090f0109050309 68
    0x1400002c00c5810b180760b0a030001d90301103008a100c1a0000000d10090744070f004010885c10400d1401402c91304071101d9180c0100e000c0103c3c00540c030701a112150710503001003400704000708000800f0356255840c50700310082640244012960000414000141e840b00c410001c40c840c1003445000c00d81c000a4090365140b007a05020030003c491404010082500c1e58070706e020401500342e550440074920312016808501804404144d0742014010441c0320f14042c1c44202072107203000711071040e40110301100e0845001e54550107038075003003e00240c80c3d8140104030a94265140000342424070504403011540600d04404117401601c8100c051584030295440041d900e5054220700c602420185000070360062000800c01c04060300b045803413191a030802c1008000461030169002118402c0c000a54903500441501d980003100400842c0d00a00f0340801c20025a4001829005080203800900090b040001003190f190010000210001c055000130f000b5610291211a100d100740d507886405964 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 476786205 1250 476784955 476785003
    0x403020102091f1d03300a0306050a05010c0308041b0e010308030106020105060a0602210f07050714030d0905090c210106031503031d0a08010603030306080c0d0302 72
    0x4000e506952202002034004048040b04103803103c1c607101c1840c08040450418800440c2c02c075140e084016400101400512041c868140080720084100300300c0401c04136a0000c08407904009000f80914500c25100840c135903081900f0400044001c0c1c00c00d174104000c40020202003603002241c2a040764020380c82c5070a900f030000c0303582c40c000c6142c0c100410006085000004000c405c0001314100c0f00a68000c1005840d00b401708010600d040c8200c2d0f0059000d03014510405280c50203130313006e46641c80541454003030030203414002070300101002c0d00c0c00d401c022410001c20309005148400c6007021406001c4030b00c10600003408500030b500030f484c0140340e10b00000b509070a086040b82e000c0f10704002160003c2d81d05145e0408090001d0003200c00280c1440c46a00046208a03070402c00c0e2541500c50343c0341190100e030101040710034001c0c119400704050000155102080c071404000c0e5000f6600416068105a4103030702c0c11384081c074903e00803107240312a040820350108416411221000b800d0030156 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 476787455 1250 476786205 476786207
    0x10c050a052208011e050112050307080a120504050102130602031c02031005090924040f030509030a02041a090c03041718062b0504081b030d09050604151506080403 72
    0x780d00e50000e0403e98680350f03840e1405104103400c6403032811170103820701043c0e2321030804400d03109903424014281c0c5e205100c28800200c0010190100c0002443c2816400140e00306d141c0a407502600d00b034456075070010700c000640c1101002d8401510b910b0000358a84030388940c2c80100401001901441c295021021078081d07040710010130001c10000300b000303129040c844420740e10380c1400341000751449410800110321100d5186164402d54112400700c900703000545040c0c89540c40740c032580d41c0c035010720762144006961702e1040001605071a0205034a214600c030034012000c00c054000d40d034601d411700400002400b01603d032180908204002a03d45940c4642c002c80750044003002a409080030941001c600b2503c402c2d204408040319900e1074000c2c00f000e409c170484200395006000f1400c01c101c01c401c10440c48044041034004402201d1408445410035400c66110f29000c03111604040144001e000548010141e42d070000c01080003481014617020307048503d6849110280032119002400345 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 476788705 1250 476787455 476787517
    0x23030705030a0303051e0106050307030203040f1b090b0303040803221d1b0a083c07020d09080a060b0f0409060b150703020a110a1511010c050a05 64
    0x101809421a80010b20030314015001d032908480030900b1441c49402841480c00d15210141202c120b03031685403854680c400d0860107540014000d5401803039140210000606409001001d14000c00d101c0144034100b120020030390b161050514881d50042c8014440d0000100c100e500e41d0b070a940c0e0100d40100611040710040f00341741d00a01c40800329500c40d0100d201d890b00918070074841c100d22510866407007004a182d60081100340c0001484050000c3c0d000c0306100d440348070000310003c1075415141e030b2840c00001c0c00070154120070f00840c41d9091104440e01000070340c80d00300445c11301080341810b05600a41d01c168580002d00496110410405c1a4540d106540c1c030114019000340140156070620002a0048030300d000d000e500c07140b0107000203c42c3e210980b40700582c95405820604455290342d1030340c41c0b412483d42ea01c0b407941580010f03002198141510842c141e900d80c848420241800182100c41c2084000e041c48810403070482c01030313031090445020840d408540b01e000f5108401102c14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 476789955 1250 476788705 476788709
    0x18010e0609030a020705010914040f200403050120030c03100f092913051509132a0603050405120f07140313061d0901030809031006230307 61
    0xc0c0968018041540c0340400104250081d980031034108564680c01161400c00c00c0c0300d204501103140c0042c41040c5481d801c1802d000403105400f06000000305101180120310300c004490101d0b00103400c20420100703000343c02c90103001030b140c0b20301c021500c20403034420b10000b8200b40090300004005620b00d04170842a0b07003e410040b21101c5629160302d429030040880812a001c40340e095800000100d0280907525480b19026040806425426441e43c0242901402400c0d07024015800549180c4031260b0140c41840b88c400d203000c90810300c0c100480f010f801688003181c60f00c0c05207a000c501c40c0f0440301c410100c8400d480c00281d16a00e07810403a080c0751051040940b001d00c0084c0d04040d1005aa0142400300c0c05001021680700c070652465940780300e19200001000d14a070000c010603030007140c505080340040507a60000220380e10010318004026041220156070126140f140e504040002c049000c02001341005020304010081c2d95900c0314040164604840c10221200754506016001c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 476791205 1250 476789955 476789981
    0x10f02011113080f070609211401020702010809060c0322020a0609050109060c050601050103021e0703091a090108060f15030903030a1b12020f09121c0905091801 71
    0xa00e80704810b58841600700a4411000c2e107124030286003000b02c2d00840c02400b1104c00e0784036043e2a500d085101d64055220301c40785000c0c41904010b001c041084d04240b024240800c1c000144d4854441c0300141800c00040c05150031540a001001784202c620401c580d00003185000804a00c10034003c07040d4060741d8440001c1d00300c40303031000c00100d040c0c00810040940e10b0980b901490749448080c00c460b0800c010304081c10719400100100482c0d40690300400001804d40540c01c5e80c64070021100101da40284011800203214402c1003040b0841c0c01410032190420011440c90012a81d00080440d107020304142d11039813001c1107044943c0c2d01c1c42c0400181c59501c000194403454000500b42e280e400840b0800d00147c00c02d8102010001e6100999070b2108117a21000c1c12101c82c00a148001d4101c100d500300d1b010710401000c00e481c4d40c3d6161413420f2074901c0300108a00d880100c0007600f44c060011003803040c0040c03204107125650351004400d80c0150080d0f40c4c0000426080540c5001d0140401602 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 476792455 1250 476791205 476791207
    0x4150c0b0c0d1d1e030901080c0a09080d08090d03090b040221100b1801060f0309080708030f070e0f010203090f031606020d17060a030210171e0c030402030309010f020111 75
    0x890100c0c19510115400c403241404000700b07404607449111b1081103500289088001510ba140910b02038100d02c540781c0381a0411a4554040914040000e41ca0704040713108c0008008400308108401042850146420300881f180b03903442038020100030b400248200d01141c0107070407291b01056407a0147e01c0040488201466403c1814018295000090300944600042c601c04021802e0818100c501e656207607660400714030012001010742003030444032000100701c1540400c81a001460040c01000d0380013180c0d0800b5240506101c0d199648140540b40404150307809030380100903a5411742c41a9501f4a168881a0010b41007456901c605500c104501c0c4011900d55800115400080c00640340c08400385100410140c18290442c1d1080c0d118000000500060500b001c41034901d2044d81805011143c03811002c9110b0360007200e50401909844124a08a51550754030355001082800700b146141040e4011030b0703c038419525214140b004194598076241c0c400d41c4840b181401418843d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 476793705 1250 476792455 476792501
    0xa0204050a02070b06060a08010e040309030b07080a0f0905070605090103090602030a7503060b0319150905040308060a05040c320f04150c0b0c0d 64
    0x44003d402640007070310800240e40024105042800c11614103600507107803070034541c0c41c00d001203030b2141000b04110b0400080ca00300100017401015030034040e007011b8481182900d80b40c2d0008048407485a460601103080c00c8a110124030003080b5103090311344514105650788211001a405082c1c0c01d030000340810310000400403c0702c2c80740d02032a030090f0100340c2400c0d60003440801c09001819031118034418260360102606080b07410140c0300c41f4240d41382e18410301c1d031034580c490400000c0e40310107200545071040d90410b4442e45481480c01030503281c0042c5085051008a0322082c44070f20000c01496a42c50225078804203c1c000020f00820202009211a1800c1d00d801420381c203003925030a000e280c0504002c00d544c47d10780520500c022440d88c413070b0303e051010103011460751150907501c01004050007030106500300c840000c040080406004a65441c42c00e400c9100340d182d0b0301007181c2040708807201d401c00640f21100d52078001c0c0542810070703200c0c414050003000810f10702c1200c000040b425610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 476794955 1250 476793705 476793721
    0xa060e0a0f0e090c06072001030b06070605060907051222080a05070c0510121a19330c03092d06020303010b0a05160b0903040e060d02130e0a020405 65
    0x80c251041e460001a01c44c101d0a00e0244481030040c444000c1001c003070034503d40014410061030f10310780c1105141c04181c11400c1c00200c0c07000e5201540035110f00c1d844a08100b5581404103140ea0003002c0b500c4e0161614100410b2800c038074601800703070401d02c0c5039913805403044541c0317010800d1180d0308128915a203030f001b040f0261003540590000c880011002c50002050b1801441c0c0502d8400d02c0c0d00c44c00d9645034a110b29500400d100090036120652064281d51940c441000a20f400810000c00c46c10706c6061220341944d80c1070014107460b6052a44a5080440a5085c1c140c041002c083c28003c0d0000111314080e07950100682160b0b0322088d640801c507200411400704000c07000d0309550148403140e100c1004030303120301c4240120350500c0801c1064109840c419801010740b082c003204044174200c0703155a07201c144e110a8035806625400450103102e03004003c07000341c4d0088411941c2c05001002039002c00e81a0b0a01c07130210400d0340d640c00801d8401c180c14000140c149500600400c564645402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 476796205 1250 476794955 476794979
    0x30b19111303112403010e1302131d030f040602062d09030d020a05180a0311010c080909070e030f0c010813060b0a030c080f151812070f0308070e0a060e0a0f 69
    0x10920b0342c403d03042400302e02c094030102603010385c08e41c0152282031070002d04080c840207001010b2003220210500405103084d0001880540325020000441c15943d0b460024003e103400c002411404a41e4607520803401c0c4103403c8000710100d00c44000b440c0000340e964030103003820b40c000c50b640d6001650001030340050b1594080700825410340c1407501205009042001d00030b00114074040101403d6908042c0300d80c0f5802800e61060081c031813001c0d07a00e03099110300807aa450f00306441031000710f02c1c83c1c0c0b004022450280310188402c800d0b40010240c541e201d600003802d01102506018002060f500010b0a10845400842c007444c0c019007400341e5280d41e403030100801c40c007500c035050043c0a80b10b004903d028010400c940e8100b00b9140051039501c802c0c104a512140c00c00303080d941e511414141c00c1e0302101e000040c140c40c40c021807425900d8111030a0243c210300d0700603c00e0040000358251502540da0b0100100103440b0381d86010304519102c2000707d038000e182c0745c100c162240c64402c030006071000820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 476797455 1250 476796205 476796209
    0xf080c0604121e03150302040e01050403110f100f091b06030e03090306011406070c140a0b0f0d05090f2e020c1c020304030b1911130311240301 63
    0x451140c801c02c074445012540065901809080c4a40000f07034907807103034400d82003803205c1e090121101e404144c0d00e81c002411a034419840c80755a945440c104801d050700003010064010501c0e0240c45858440d00e07a0301d407502000d0000450141ea01c0d06900810621644410341075a480090050007110107803540786040694490040000d08014190704140000b1054660f01900036004201c10307400c200c2d500c40e1040c0464034498000100340b0003240403070040d01265000b000c40c014210300300d8821009002c118482c2c0e801c038040018081000702c2e160b42860003224106201caa2001030720b0b442d154410f501348480100d04440ea0300c1400010002103542100500480c0c007045410071603d00c28212480503400341702096103441c0c02009140380a8000d11462221203d1244150307450030b07032203903a05026440159600041d040758046201407010040c41071303012002082c1491414400c003600404051645404020041c110400440c10701e40c4400c54200300224418407a5250a0040001520035030070134 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 476798561 1106 476797455 476797463
    0x61202060705100c090f0f03020604031e050607170109060f0512010b060316020c041a040209060c100903180305031207260106090609140d0f080c0604 66
    0x54440c09110700700c6a05d4100303503541051840b0190118580008400700460b403c1800035954900036241181c0d0b000983e4500d03926071004560f40d5030b41c0101c0041403446140c3c1440b146a4000041c5990f008004c94141516a41d030794604050311810300c2a40d170401d034010000d11550030b1401015010401040021070307584002c4021501075131007190443c80340e20314280351a01e2a40d041c0040a004041250f050104800501c6403581090012940c00c1c4190703070000b5051116140e410503643c10103031030010303140707003440206641002c0e040401048000420030349a100903000e40c045902c00ba40e070448015814074140c0710341d02c0d0a02002400f00070a00ca24082a46902c0c0c2d82002e03200b03156501c603507084109500d400c6020b800088103411130000c0c060340c05c2c814022603041c404605003600d002c503031005081405050030100c00c541404041c0001d04009503003295582c000480c2ca01032849 = true := by decide +kernel

theorem cover : BRFrame.Cov 476618705 476798561 := by
  have h0 := BRFrame.cov_init 476618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 476618705 ≤ n) (h2 : n < 476798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
