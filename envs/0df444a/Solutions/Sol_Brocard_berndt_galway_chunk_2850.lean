-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2850
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:39.068637+00:00
-- url     : https://prove2.me/submissions/08784ac4-7419-4504-a9d6-23eb4208019c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 512410071 ≤ n < 512589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 512411321 1250 512410071 512410079
    0x15120b040504050303070e030109170a0807181502190528020906150d0212040b0f0709030314041d040302192103020903011401030507051905210a0b0601030501 70
    0x503000307190155510001460440d0fa81140c1220101003215096900d5921640c03a14041214140c0c2400c0304840c8007121a0b0300d1204080103080395401078085c03410080c1d124820404842d550104006580060310380c81d03141605c4c10400ca01d0450407194031a00d9803405030403401088170003e81140c030040450030030000d1109280c0b9401e803040c016400a0b41000207800062402d19141150450010303e61202904041905042c00200c2c1c10242c485c0600512040900051100c0151a245d02c1030b184401103899140c00c81c4003c200d4546840300800348004c10001d10b82c2d5030034040c2528054826805200004041d000b908154084242e03802e81c090b0040520404023822040c90100c110358103c601c0d60704840104101c1001d151403113890404166080c010400241d40a0140d40f1071455502505075442d41581000c40c1444030f990702252041034001c3c030101059a102c0c440c42d0855104031014180300080c821002d0030072000c1d0f030404040380500c0030580c1c10052440c45280c0682c40030f80c0c040000d45e032a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 512412571 1250 512411321 512411329
    0x16090f0509060d051903080402030105010f03110d0309380708190507140f0105060906030a11060403051614030307170702130c050703031a090105010c050715120b 71
    0x503008080d0000100d07000100242402d002010b15248204100d81485c0d4030782d40a1454440304082c1100054049000c0c001945400d0298901400c10120800815851035945104c0c1480414645009000c4400a00b050501a0704480c0c0140100011152103000125284003080041110418412400381c140786281d8002c00580348155481100a45404080104c8051552400e80818200700c010480e810004000750b140d01c040034185001001e686020b050710601303440e40100600e000b4410401044507235039002031060050f503080860300c2c142d1460403010524612540e080545240b20b600040b208800c100c01c2351108807054138400400c9140500e08250b100c0c407403000082d0800084440c0c145903204540020b00820707100412081144084500d114207646201c40c09030041343c03010802030709050f010300400c03034040380f0500364104001d0113900040a0040602513a0304000d401c1140c50b04110040180d00d000d4509049c9034520349101c2d010082842403440003200c49241008400151410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 512413821 1250 512412571 512412599
    0xb030319020613030818030903011a0405060306070504050d030203071a07020d05040f03150902040903020c0f01110a120c06141503160e0705160c09060e0910020f0c061609 75
    0x2504d581c0c1c0c0c500316200c9030054034103824181050035490008204800c8640d0b000d108810050010075442c00f070051040c42000100e44004007860702941041e41046105a4008100e5068900c116007030b050017102c50a0482c0345002d01d41e0300801e000040000007088084060495115480c11340c00c444400c20b5000040300d8901540c40362400242030040b003400020519000f96000122243c00000c035000386400040a4034032241d400c0e0051b1704090b490752858180319261206814003800e044440d18140c070401556071400c080c0141120511003058400c861164841d4188150010011b01c511769030006007440b50002551941e101502181c4040224240460240402d810080c0400040f500e40035a000c2c00b100010051020000100902102803101c5091020700a01408200340c445003408100404c450060b040300703440d10103440c20441500800266404d280510550158517901a038511441600030b040800c1e125001c1d8004020400207070b8030651034180900d983e005400c50360f84501c0c5003020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 512415071 1250 512413821 512413823
    0xc0b0d18050a020f041b090f05010207080c0f0d080f04050f0103051608061f090503010605031f0b152b0b0a0b09060d0513030311030f04150b030319020613 68
    0x1c1c000d108203101518001016130360031349002c4c1001c140d28092003407080b210881c40e40c4030008503a107800240309035595100d004000d05001c4c00209400360400b0700e80d070381d0341098802c42813191420a000903010707100c544500340130740c0e40b0240c21500d5012090040500c2e420901410340188115501403078198442d018590041002e402c0c001405203030b4020460300036100400d441d4000b03d09170740200e110f48640c0d181d11b01990556a40306851418441051309546c1644c0c083c910030781c8410340c03481182c9984e902d4008061540280000c0c50003070300c03001c240000060400d0300e14061000c10006071200c0c00390081c4201000c441c0c81d51118013482510b840886e20030035001d5800042040d0306002964200c0d0041c18000e2008006d5420194002c0131001038500484003600d003200d100181108040e0140900c4941e0503003004001d0541c41c01241e01e038140a4000c1001e803174101910140e02210403198051641c416001c0d0070799503100c1c2c101c0b5004a418024030541c00041c030509000070500c03074232400356244107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 512416321 1250 512415071 512415073
    0xa06020315060a11210909270c03070e09300d0b01021e06130303021603090f060f170406020c01060f05011701080d05250f0303230105100203070c0b0d1805 68
    0xc0001c110a1000307043c0c004280302c0f03007503002050005a5000143e85400c13210b660800400e829034600090608081c455401451050310410600620308408100c4840c0d4003400070030307401800e206403a0ed00391003040200381000c003400020704100208403900034880c1400c0c281c084441041c02507aaa602e000742c4550104600c1d003155010816255009c00c04084060007490050b00704140c1035a03070b013010352455104501007407046500f017080c0340c15880c40d1001041a400c0c080590108a90007604640c075044e2411801c03016000010b041140c154152003c050a1340003c02c00d1a4444e002a4040211800f4090200360b000c100c21440074034203181d1318141d51213100036041c00740000344107031030b250807000d4200c00701c0380000000d946080c0602c030103082d003d0240f18041580c07401803c001d0216402400c11a00300340212034500501c50000d005181140e8098805d24560801510120304600a005004080400042000a00c50700c140c01504003c44080810410100e4690000f0010103448000600d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 512417571 1250 512416321 512416327
    0x19111005042922200303070b0901050708160c0314040b0a03060f090e03040e060d02120309010e0105090904030c05120a020f070501030618230c120a0605030a06020315060a1121 77
    0x1d00141324a22008413000740c00c89040000e0396581403600042280c015203203070365a504100c80c40c1e6000020642041d83ca51042108410b441402000415041406814000074201680200c0316000c211030062001412305c0b82c0742d0079a150000c001d000d080c812070500d04403200300032410410714132542514541200045140a107409504c410b109801020395038170030795050100000d80c0b038001c0d6010305403000c4806983e848803034100161004000c1a01c05041240901a02da03581e103034003072510b1300290141400c007032401301407911916000901c03145105040012540c4522980c0001e040094880359105030740d051a2510300442c2152007074401d0f582048070b040300300303000e007841035104c09903a094075122820701d44580c403054901800280c8030000a19000110030f082440c61000c0b094012100243c1400098a8000065030700d002c101c001030081a40000440d0140c85440409480144060301154031180300b100064045030840301269454010840c0c103c10890700340c003180ea00340d9209820b00d42 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 512418821 1250 512417571 512417603
    0x604080a140f030a0807090911030a05040f02060d06031e0809010f17010320090709090b04020c15090f030f03010303030f02070c0b19111005042922 65
    0xc4544070341c581038428010b10544030740710801840280520301103500c4000391801d00d03803030080002d04564424080329140c482c041e00500c0034541100e8000034200c1c0041aa5150340c240b44039005074090000350312010000d200e290890440d0030002c1180d000e01030760b56070710f224528103902c0440e5001008083c183e0030082034409601609a22890034614540103850080a5250204c404002e80041d15040814550549025007145403d41404025240003a9034200f568000c0c0c2042000d000700610951038440510560300c40ba41030b1142142240700303c0c0c0420785840104120200143c92104840c0110384500c4181c1a000085980c1c00d038031000c1451450780313151001c07401014299064003005808000c5900030070884080358001e40b412110050340d403031202d5000c200d00c0316034044540520560002a0080f85404145003901c0c0c00104c034040307034542d501e03e85249444001521a1a13440000394808030120300380050a104161620740c003010846010004042e842d10240020054540700d40040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 512420071 1250 512418821 512418833
    0xa02180c0f0a09180b010c03120207050106031203140907060507030c0501020a200c01020a0602030a0902030307061a0f0303092404031a010603060302150a051c020d0b0604080a 77
    0x26032044403662028201003080d1148085984002003410010310b00c50014016482c040004d03007450311500c2020003c1400400001e400800240409818064088114210003549804070350203103a202d0000c005064032480d100e9001e50a110040c0000381c6825076081003440300c0000b190080130030300028188035190540407a074950159034110b0070050711242010001d40b090001d01303580f07601c9889980603940707044a03012010b812000c2508065100248128150b6000b00d010101d03d5004800540d599503501d2860340501302d003d0001b0b416100c0040c0010034066281c1c0200350b181d80b450540c1450308244010484182903035440f031070740b540040200500d545051061041a44002c03250101454086d011800443c1c0059009441914081040c00038080b403d41682d800740c0303820f0400300116821500420b51501a1a03400301900c50f000075540d48040c02001550800240c2c0d00c14544030400001c0e4200c082e42103401d803480d00d01c0c148503014000749030450655040d115000d000340311700c81c1390741c941d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 512421321 1250 512420071 512420119
    0x301080709020904110703020a050607020304181a03060c03040606231903020a0b040305061f05012d0c02040e07032004090209070525050309060a0216260a02 69
    0xf0b0b070f6101c1e903660280c0c200443c0072405820750501a030054090103d4506000303003441d000030542d4007103400820050016001c2d40c1e06904841105080000e83c210485400c5880c40b050600015454420201045421a0040011886188100703c00d011a03079441041c4500c3c021448024140301c403a0111503981800c008603800e400c08a4180044042c039501e0f0007240701040507422640c03010100140500c00d010042200a41080b4030307840c041c01c00c40c0580402c0c4007074141800b4103810490500485502007400e91039900c5c00311131a05031004c0d1369442038005484259102012402030f801d003151008040c0011481001301c82d00701160480303003052070340508180c0c0010015503900c6aa1101d0600168a510b010540f180856440c0c083e5240034102040b00c0c40c61003000c0146101180041c1e400c0040e82c0402500c2920780146c0d42140ca40381c000c0303410303401c0032010080000003081e0b9002c005442180d4180c4198040041701005c0c024050f51054541c4038108a2000394000c03c038100e080b900d0809201075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 512422571 1250 512421321 512421337
    0x90f160f050328050405010203070e0603010e0619090c0504181e110d09060b010206012309070504080102030907031b0501050f03040f02030f0a03090b07030c0605190f02071205030108070902 83
    0xc207003c4200d180c000202103a0b03054501b510702d42c3d4003100700701440390014901c407034662044a02d9030441d890a1244416410024409030240c1c01140b0390b4403400036101c01c1c1c08003410030703e54140032510323650070018100e401ca4840c15003850410300101c0080e04080c4034000d64590707031314001410a05640b071a400034100c0140004c2803980100078071404013885124140405125031000300d0000c0404000914000c01038202e412201001621628161140b060b5050101000d440603816546d031007100b902d40b80175030383c060000c41d400042004003a080209504054a204490240d0ba03400003800301802d02e000d82c01044e0104e034080103c40101c200d00d0015690140c81484001c01c1c2e043c1d143d02003420155000e01c412500d9118800c040b041641200c8030b00c0c0602400c0703481c64240000c41c0c50007084401d8454020f04440c1c0c0c2c4801040d6804c4442e4005560310796000000e0200441d0302d96410020361000b00283d075003050018092070158030403000c4034100d5003150b0060801a0810000700d000f0760164027 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 512423821 1250 512422571 512422621
    0xc03031d041a12100f060e090d021e01060e0106080a0c030c0f0e030a060c080f0a0209010516051c18090e03040b0f04050d080a02190b0123090f160f0503 67
    0x8208104115600414005c00261440450306620b800300d100203c0f00003138124181c58110022080040e0360005040046820884003d015445070200c118010610303600a951100790690012900c950040c0340c0070b00802e14001c0401400d10000001c9044540e0350020303e0015044000c3c0c2c00316079100d0541e500008030020165480420295101001c46100003001408241c40000700003840c41213414a60744040b00440643ca01a900b000080081c4140299000c03100810100da100f805010482020700759800f80c660702c2440d0890744090100d044255884401118480000c21540114001c80543c416081c006505150400e8512031964102c041c81c0d0003400011701c4005810384c1c07410303400d001090040c4446503031012030141c000d0030040482c40e500c02c0c0c0c039000b19410000500580e81c5904483c0341e042008450100c0d201541c0300c4007442103c840d4004028018001e903408140101d034020f5216003100c803008040303d541501c80403443d5100d1008a01c003400013032982c140350700390030b28889541d031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 512425071 1250 512423821 512423833
    0x1d06010314010510180f060912121101140f0a06060207030b0703021c061d011202130b01021002070602090907020d05030f060d1a0a0b120a15090c03031d041a12 70
    0xb480d45c4200b2880e4011070305c1d034051042c00c1046a80284606015101d84d03240191504150788941c507044850348250b8041003901580380051580c00c1d13100c401003504070410441e40b400d1040d84038030034920580e10a0002880c00b0b000281d03043c000038414080300d9208941818039910701100381c0094000d9180c4c00d0150035164610400c0c21690b11800340030300600d0050712402c19418842d11100c04050b00034005081000600c0e4002d0381c0c4849091410407811400450320041143c0101d007040c680300742d58441d060011a1400422040e0780180c21802400c5d0307029490360740c50034000c903511030007c0c4a5001103441000450564070040c103400782d121202421010404c0f6541c1d0350807090b82c04810f078140030052902c05021840645009002039108121442510100341003042d5484211002d402050302d0141d00082207205c405400c01203613190010707004036201741d03a801d0261403004d00094804082000041f0344c80c0ca860648100f090340070141551030440100d80e070a000c450805403840b500340d40300d81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 512426321 1250 512425071 512425097
    0x60f0f0c080c223506060f060d020d0f1103071209031403090303160302090a0e0621060403020c010305041e0201020a0818030601050303041203050d0b06041d06010314010510 76
    0x80350500014484d0344545503420345502c410031460361040b05030000004074a061000c01060000f50307142c02000488180303080c40205400140b081c8a110200c440c810b001007080c8803502244d60120f01c0c000740d04c010521403c002499041828841180e6550118210485c3c803844410305900c0300d4401ca02c01c0c2040403483ca035508649415400c202c500b605254000000c002001050542515901510b414194103005203c030024880d03d00c0d50080000110304480002e0499942c00311812141e01e04000c4040d000d8101d411403602c03400121810340143c1300c2c030058602a54880c0c0f040700d00c519044142c1c1c10104040c84801c10922101c0f02050741180f16011810b404146d000004026001018800703001e801003d02c103250420b141684101e100c5c0e00b0900c0104501d401c5030b009080d0381945442d00c0c13a41c2e101000c9a000081c061800c0003038000301c002c2008510458804002c0c0020106001d41c01d0b86a59507000440680302025004c2c0c02012006004000e1414040b05110404075031381030a1102d2005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 512427571 1250 512426321 512426377
    0x90a0e0c090405011202031b330c01020a020607090b0d02090301140708090c0f0303030c090307080d0203041802031003120c20090c0f040b0304080c0307060f0f0c080c 73
    0x20a800c85019000d03044405c000b14982000b8028582c6480800000c8210100c40021111840c00580300310302844017403220100001826502608813401c107440b0348841034490030742d000350008a150300251107400b02140c41c040c014088002283d40101030185030540c4030140c040a5042034030065095034907810a66130705030201c22a2486005141d84810003443d0a101c010300d8603005881250080208180240701500c9c04000c90740d00403000c0d422255500071080c040307450818039901c14450703070051150749004560701000410440e5000403017900f140c503414401000302d100030390350091074a20070101040010200041120805075600f800f40b08900d40392101026402c40a504200d030042045642d81b00740b40ca09049a0890034204105007041440b501003109403045008803130603254003100040c1040344840c11100e0503000c940c240c0c1e4541140d0310380701d000707405800d51100909047c0b00400da04410a40f20b12807640c8060b60700c100f15511210602205a032040440021042c1c40540c40e0802581c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 512428821 1250 512427571 512427581
    0xa12050c0a031829132105010501091814100204030803100806070c0f0807120210240302150c03040e091203040b010b0903100609091403090a0e0c0904 66
    0x80203468020300c050100b05403030440051a00a07160f0045000180152802c0020031248000340e0440c04c40c1d95110121180d00594003d5441280300840c54020650504820384c0500c504501c20402400941d880301484400d0750820162641c01d0101c141000c4040b0301c011454911038801d002c2511038081140d4810310076681711b41c006444101c400024840d00042c05a41000105001c402511060401050003020101c5000c0007900314000181e00c4000e0200d0f0404a5403c181c1c80f030340800c820b003401140a0744a29907030180c00141442d02950540a9591a01812841d058203160028042c210750820002510189000c070002e40b0a0000b0340c10400104000e1000d09685804200b480c40d1400f4814a01540c404a140c500c107400d00a03c000500003010302030546044482c4185c0324244000403078036016042110094403400d141000521321101c0d44590728031401030a240c50301c1c040200f02250740f44940340c021504400d40d0141001410036864016401c00381d00d182c1d0703c0c506590f071400202614 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 512430071 1250 512428821 512428823
    0x60f01122307091d0114061b060412030c090602120c07050d051609110a0c02030102070b0708100b0c0c040b0a081002090405010905161b020d0507051008090a12050c0a 73
    0x80d80e0340e80d091104a0916084020704a43d1840101445d81041d000e0503440c10990354180c061708000c1115202e00107001c1e80c14038034400030301c01c45030b03d0324290a00880040a00c5030020120780742c0b070b0a6843c902c4c8942841d80c1981c1454004048800c0d401510300c8080d48001400400741c05489400311342070356500101083d1902610051045003045480003c1c10080c542c00401c64a14200b5030078611800c51065803c0d48070b131400d000e04010f0f5140003181c003920075500000c101440b403008010b4aa900181c10a00950b0200258164103888000d039010b2842100e0044c1b03000c0d400404514520304d4660010340404401030051182c4c0f41e950058036160800d0300420300700725500495a040141058071032030780104900d5200b40000c0c1803800c3d00d4120205d0544a920400c1100400c6610590079240602040c41c2d0141c64580c50700c50074104245c0b1101140505840740c20044286000c0b1072103401828042c48085010380840b060a40c1c4200303c501c050003031001030002c203104244e03103982c003408141501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 512431321 1250 512430071 512430077
    0x1a010e010c02212b050706090b040b011502010c080a0509030c030a030209100318200307090204180c08130224130e10260607020a0308060f01122307 65
    0xf0144424a1070500400c00000440c0c00303d102903002d0071602c1110589006070140c14019518221401d2a0026140c01d9501410440b240e0701840204000d0300100c50484041950320860000c0803070040b07080ea900105507000266000c404108603074044e82c411501310310308000303c0749000301540400e41503412908950300030940c00b103800b17659820103071603c203ca2851445e04004c040403140340100c0c00984801d0191000320311914034161307480c810415a9015200034210b840f031a9546e00888040e5000d8090000714016048841c401941f103401342030800503050311200d649a680c13100152007180700300380c04d90f4000300c00103400c0340030200741060056201d4200c0340b450f550514400e02d00703491090f41d481004000c40d0320040003088003022101c02e082e11901580c8404010320315840d255400203008079200c40d8000e09050100181d00000e800c40c8143c46074030b506645554007010403d820280c0110203000ca0520703002c22a1b021019404070000850300d880d800500582c800d914a0310f0001243c089001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 512432571 1250 512431321 512431369
    0x610031118090715080601050732010e0705040203091513020a031109100f060e040f020c010c18080c06071a04150e07050f040c0519081006031a010e010c02 68
    0x100224288001003039104d41000c02c03003400c08400080c40741c4075541005d440e41590810048440e011b60310300b41c0e0284140010138001c90303594480c440c0244420340044205104940d80000c4505050007924454400100030b0a11189400810042031000800314004641e003c0d1842006039101e86011020318014106403010a09010511003503034001781640c040c0e1070711030303004001d411000c101f4070069075110300c0c1c081048414080803502600303013503941c4060180041801000c04105501045090700e203039440c45000014511840546200c0e4026401d21f070700102441e8109003400c600034aa00c0d81b060304042003005078200030340724400003541c040701d10000000c856010900700d40100c98010400c0310290030004c2c90000010400014001114001c1b0740320031004500c1c500800658895454510700f0b80c061601d00300c0020003440d0216281a1012581080454058440e12981313078800807040d44401590035440054a0904c04001100c1c1040048140031006844220740644084030501d06681 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 512433821 1250 512432571 512432579
    0x30f0609021309050723030a110a0501140f031312090302032a090a060b22060507050c0d0809060d0f05060108040c1505190f0e0306100311180907 64
    0x10120300010200200c942000c1d81440440c40200b199006c45411466805201d1900c0c007540036074403090181c280d410b00404400409021080c3d000d0035082c0c4007200c05040d015154001543c06200e85196034014442c188141288503800c0002140c001440c01c902080842d800c0d505c020200081003001130010303048820030021410100100c01451198010030420030a5040d0742c40309100100c241e5502c20b40d41c640109401c0100b551224026100c80c840c1c0c680d41f403015400c3d501c2c1c1c861245401c08544815034400041040c41041a9031049601c03801078040d031110401000340a80301c000007921856400c000c1100c440d6074050083c004481410707004260600490446402c90b007009041e40e061080100800c03000070603041e0702900340c6000148000000400785000c0b10103028108200b800c0c1c01310110504910760300a2004082d00308a5502e1040c210018001d044d15000305540d90f007210700b290304003840060150283d0090006000c1c00003648c143c4000000c0304014000e0300d9001c03142e0030089080c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 512435071 1250 512433821 512433829
    0xa2724061205060108130b0c070204061d060a0f050409051219080901140103170d050f04051006050603070320040e04020a060e0121090c03050d020d03090c030f02010207030f060902 79
    0x140d031180090800090300e14040e00c05140701046c0c004000c5c5011002c800081c40308164009885006402500800106884048042810402009402d11400b01c0c2c00082c9040c0380c08610382e015948400c080c0003229150100b48006494170020841e4603001340d1018404448451000e0a85811606000741100711020300c050710352030010340036200f541d0410850114520035035403800c0c11a0f6010090380b0117000141c4014040c0d0044090240303d59041c6000d11011f9801044018005c600a1060f00c49040144018104a8116205440d08000300f80700040400340642d00c03040306000410103202030751610405070012540590401c00701c4820800a01040d802c02082c0750002d002e080c240f07480300810860005e080100343c1c1c8121342400c40a25021740d40c80a25400c0340000a51107001240d5036601c900d0b00580711039140101200500c00e240300440b5144c420700400c401c1c203421000050380769055031140d0300c01015022003641980b01c0e1030300010010f51180190840a406402c00141c004540d20400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 512436321 1250 512435071 512435081
    0x82514100b01180b0702060c03210606030603071401021f0606110f0303040f060b0603130605090a110d0c0b030403030b10050a120903030e010216020a27240612 70
    0x101d41041014040400111180721040003610360840e041d0b40c81d4602480015220b01c80c00041c90118003002c0741d8900d10b0321802229000e40181400001020741e582024001d45010454103994103900c0b07440204a038010810710b00100410610550341c841442c2c40058288054483c0c19524840e40e17107804024240e4044c2c5d00510761240e103c0500310400c00584855503900006d40702800f501c0c84000020108041135100d0548001f029040c40d03100c0c030b404056600c55944814054490b1414000040c3c44480c005c160301d2800e5920040d032281e000c854100b4400c00c420011403c40d012070b0451808500c602460307001d18440e51190390080750359041d00d4140602d0080121012040c40410301500070707401d80001d54040b4000c5036010020b00c1e2041400c0840262004030300e0744034036520002c3c0c843c0c40304180c000104d45103802580d02c499040d0fa00e104051521016142e0031007801d403444101d00d1211016000411114400d2030b40c3c0542030800f031135041c0c209105074814008141a0010707040320301c215001d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 512437571 1250 512436321 512436341
    0x1905061803030123030712060b01090807181109150a111501060f030f1a0910030f030c03090e130b0906150411070b01121e08251410 58
    0x6103040d545003d080e103410742c40001501d0580704c04404130010a40307040125500030412000a0300c2945002d0034a20700400001000e0b60000d18030200c0072855240000e880e42c00c48405401c01052082c886910200616403030018101c050b008002e401801d64a80c1d501c1c0c03038a00981e000a5540c4d00c83c00d040603103d034aa0245110480c2c2150810082c1004440c001d141118181e0802284451405808600a080c3c5d102d81e440c0d12864000807048040d107080d404a07074407d003901c4051082e12146070b01c0e042c0707600c1031100902424041c001e040000744030703104c04102b5501c241402a462900c80309045800c2004640d000e03024000c14045505100c64169681d4006401002801d110b041020f0301e030030295130078528640030329101c03030740700e03100001d00002c9401041d0400110001961a08850011185800c405441003120801959007100c0c0d1039121100480d03004005914003103c1b000c0b181340c111075a41030741c007043e0300440f10203001c1038020000802e006458005025000e04000300c00d8120744881d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 512438821 1250 512437571 512437573
    0x100c11011a100c1209060906170c070c03060608030306011b0b040611160501090501050105032b051903052a0409020c0304030f060608010c0c2319050618 67
    0x240400c2400301040c62501d040030607220158103440c60344007540e02491042004050a9890032514045a4040c0c0c1210644201e662440d80e441c0e51000100d0b0f03a840d4510049080602d000c0c045074141e0341e071000500449100708195800e295032515844111039460b401031030303260000801c000043d0784c4a0310420300071046a0fa035803568405504c8034944490010001030000e66225207402080c80380c0e9054510180c40c0c40d2401e034199106140c103901a0580280440d60b66007424000304040c500455220540c7e48141032150713440c0c0950401e0200d1741101c0e40108140b20042003896101d9510303040c084500c806545000c01c50f41800301c91201009420702d11140e08070300240079815004100d000300c60449208100c003580745c09060a8580c110320aa510040c1050b5495410001304103040c0c10140c12602844000c000c40024420141c1d41066081c030010070001040841084c20410500b12040c00c80542c01142d81e2540300d001024604584050b054800754080410003441c040500344124590342020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 512440071 1250 512438821 512438831
    0x60109230115030b0307051c05120924190512091c0305100803070f0317070f0503090705130f0b060a050702330301170d0e060f0c100c1101 61
    0x2207075540d9444020602c101c01c02d0744074180e018207a80d0810488010384001400c0828a540a0303002d180c3c000c0800340201c43c81d01804603440e40c503c243c10700351210427001820308200d40340c1d810704030342c0d58204110000744510300612001402c030b5010b076020b0340581c502da10b46d140c0e90624850710480c4468010691a89a070201c0c061540300b0b450004e040b188440c3c2d0382404a1a901d41c80c0000600c1009600b02114511003c542181400031017580b6a40d198003988074071911500039104518121002c450b0342c000b155180040f20311603803045000b136a00070055425500b21030b807100006004d941d8a10b001d48035154603001201c0c4521000e114001c21020202c912031314040c61114064100d001350304000c5d201e0100301404482341c8050843c0071941019410401110040322072007441550030a00a03158102006114846c1c440301c00100c66000c140940c07a4009510300b04030800c03c1035840020041d140075014810340794254070030809600c0301085c841c004220299480d00c024104072890002d603046038182 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 512441321 1250 512440071 512440079
    0xf0f0513091e0204020c0604030509010801060809070509070e09070203180f09010504090f05160906060c170a0309060e03030108160e060409060908030f0105010e0a0609050d0203010b030601092301 86
    0x108030304507152107081c410b0010b007040e07000280090041100c010201d001b000708020070160f100c0b0080c00001c07801d0300c1e0042e090362107143c00c503800714048035443c100364422103081c002d1b881c0007450554820b00c10700e405d0610081403000311b80b00303610585101d00541c0c40802d03983d20880391a071000f9424441581d2030305140c83d039140000c04c0c045040c40741500942d80c07180b018090005002c00006c030070360002c5c1220310310441e0b041c0c0604404441d200d1581075a142640c08507072a8450f01c07426082c1d035003003254404030012140390b01c445070380100000c40c1407640d5000203030001a654082c03882034402c1a4095600ca40c90560507a082001c00c2001c12180e500c25441403005604040b502030300a0301c00d03140013505079918540b01004100790380d406051903001000f04140f40485c9580c040c107854007079030b5140c0c001d41000d00340580070441c1d003d142c0100c0e02a160902050a2990030700c01164001030000c110307021400b000c68100310b02038101400d007035141c07003116041c04040000d2000f0302c2403503800c5000075850 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 512442571 1250 512441321 512441333
    0x40c0e090c13150c08040e010e0105090609060118051005031b0a05070611160b0702011a241308070905131a060a081e0610060f050708040f0f051309 65
    0x594041c002c50950382c3c00c8410301640c42114021011a80f042d005945c598a420060191900c04d101d004d6000110302c002007982d06000100602860018000500780d0311108015103001a954048901d08100c0400005081c0e450070701050040b522070325a507542c0e043c5007034000c082c10b03040740040031001e400b000200780c0d155001d03044a400e00d400c9640003460b0a44c0c0c3d2298002e0340309410000002c140b4400c002410f101c2039500241c0030387c845400810110441010311100c1c5680500b040b9880f044012421340c07040075003110400c5030560700403800e00d480b030700e040d49070980001c60300240d01540c4140c900380103400d07071849003541040820724100c0114540382d0b650f16248a10200c00d0306185000d901090240d03e5502c05503028107005020307900a0050700414010840d00ba6100e440c0c1881100c02095051030b03429900001c1c7d4031680e99280c00381c90f070001c003501c4552000d8030850345406c0c10000010354201001031007020388580c494510013149071504006245020403080c2600c40c0c0303401c0c080e00000340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 512443821 1250 512442571 512442607
    0x803240d080403140102040e1806060102070605030114041b030506010f020619020a020a33110a030209120a050c010e03010e0c040507092403060b0406021218040c0e090c 74
    0x5440000581c3e80d41c1c1314411035029014541c0144080302801c8103000d5110f0588280f0710905591608503a02c07952003c00481c1e40d183c0c18450000450400c10042c007040c0c07000381e4181e80000e0050004188203502d40b010f0b0344050302ca1211040083d69075818846650783c01107403070f2080c80700d80c030040c070b214241002d142900b09031420510700259800a562042c0e1402070002c480b0f0a90004c07039000c0290205808101d407401c00080508218079170014061025901703125544020150826050610341841d0041d0000c3d40403031103456104000700003500c882c00c420041d641c00710f8801c8001d00700200d00d0b80300150004230380801c914481e90400001810780c41000680e80d002000c03c44002c14161142101038522041c0c0350482142c10310451008004804114440c144a1860350b904100b002e507261150b403003900407406500c006800100703140b0310020113400074120002180000900070071208002904441904500201044c40030351403586600c2c028005076400b941e0100c800785030102c00c4500c245040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 512445071 1250 512443821 512443823
    0x1a070506160813172106060703051207020c090109060501030f091a04020f0307080f07080a0b0c07150218010e1002070e0903040801151404020405060706020c0a0803240d080403 77
    0x21030703044420fa081c030211004480061128054259031280d01a20141081c2d07402d40ca5140c19001c6400419903a0801c1003c4404694041d50790782c0c00c1070700c828040481028080c00400c01c62142004100c12a039070000843d000384840100000c54601e00800034013a6214250345250452601401c000400e47d41d074500d148040c064681000300d90303100d10008520480980c5590341500c1000d030080760100300040c5108000700320030201e407611070352203074000d0741d0b91050b0b00014080640d00d4042002d2180031800b07000c1a522583c500c4e07802d2281c2e07031502000c0b600254441103c1c841a40b803030640650700001c035814801c8056441c0003008004410180d680e5090f840b4000c110030749100020420142070040d0750140c50040002d00010b01403620030084080c090086801d40c500004204000e464940b08072012034202511190802200391036500080d08000250f64440c00341c40d40c007c1c0024001001148180c0c800b201c8084100305031044800c100303c28050040c00780b940326100e10045800d02007903808403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 512446321 1250 512445071 512445091
    0x903010606260112110102100203090a1421030a020c1609050a0908091002031b070e0703090309060c050f0106060203220317163216090f02041a0705061608 68
    0x105030000100c2c80c00c8c420300714628001c0d01c04801e11100d60804101054258051005d402c0c1094211a0b0507880701180c2000444524195030500400c03140704000d1584603245240c014100f4022452a0741002160020140a11200c443c2400070010701d115054010a04100c1044505a0b6584441051040d03403540c9115460051940e204c241c03081046803a072449c9104040d403507203481014160b40b0015801006021100000002d4506200e44a0907201d15090340d905041180340440070355801c90004070907038541c0944885040031120034000c00780280403650045a85d581c181c50381000e99000e20143c845520803903141000403400c0e0074420302500b91100780d01c986d640302c00c2402694140d00b00d44000e180100180200104022030440d901044602003181c1e016236031170482483e196218880364200b103500408090040501e10303403041c801884e00fa02c00528180d113418128481c1c141c03c0280014215002480e402048024004950032031107070307024035420a036028809001014001c040d6991 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 512447571 1250 512446321 512446343
    0x11030c100203060a03060f020310080d0e1009030602030f1605040e0103110406080a0b0601020c010509091306380102030405030703030e04090c1404140603210903010606260112 77
    0x5a644d50f1003581c0c0003140c0c010010048001d0003111034001c7d4000311100101440e02d03040000c0c02a0300403804041060043d07540800c50000c1c4410025611243c0c091041040031100f000f10020701c00e80f00541c082c4010111000b064680700c030100d01c803401142064400c100d41030004202c40d90300750b1049810349030b01c000a002c50841e143c000c60010a441d60000449220300150001446454090b06004030030a03070a669460015400640ba54400d1604040e0043d0f51000000d00724400c20242c20b544034801c200101c1c014000b0040000c0030f254148680c0d55214240070481c2070400c019840c040010f60030300107941014034002c0081c0d254481444041d0034400c017049a02074507605c0358066912180c2c00702d01d080045844010050045c1c500c010307000e000360320f04107c0700c0036100743d1039025105140c010001c21456201d101704144c00b60f041c1908003440c4006202000d041e6030b081c000c03e40030303054540e2000c030358a101c20ba0100d030000340304151203000c1810303000510030030b0f22807030300407407815008008040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 512448821 1250 512447571 512447581
    0x60203040608090a1703010e071b110411210105180f04030201020d0c03020904050f10050d020f04050708160e010905101106071d01030b03030d05040f0b1611030c100203 74
    0x3040441c0300c000105a40e4044000c0d0005d0340d42c01c2c02960503107244c02030f182090b5440820564400141304040c0401a0411075038000158032118007a100180203040494065400d0900d80081d40100510514402c0c420f0141041600000c012034014102226074960142c2d459082034045c0001a2400f90408201400181414001d40445000c44003d0742d041240d0b01c2c0c4000000c0087d00801c2c98284110300b4032001c0ba141e090401d81d0745008000d86844440268584801c10080d0f00c001d050480e0090200e948403100383d5510b2152511a580030b4803180403a1030082d0080d40041d00c80d15548040c09412400da11150742d202e0340d42e0003a0340f019104003040071215201641c01d80e003450b00b402e2081c42560104403030b142d03101d00d080c95294101020940c1e48004540103500340d9802c54292601603105000044a100040d000140c0282c0280000040c1696640307a90041c2881120020b12040581c0c1050301d500c5d6008164001c40003020000d10b0901000b103d4981c0c41b1406d5112201d2440d4000c0007003a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 512450071 1250 512448821 512448823
    0x90106080601110d0906030f020a0f180503060a05090c19180f051302011115062404080d020c04050f180709090302150a020a080a0e0a140307140706020304060809 71
    0x5034000f02c0c2000321250315400500c0105100d130070340521800242400c55040300c420440c02681e014000ea600c8813000040690f5048800391300f481140005540b14241c00603007030b01c007409214082c0c2600c900c046258680308000d24600520980d6550082c0310100300c2710900c0307000c100b124040e030301000c0300f1780241104c4501c02c4014202684659030401d290400340000849126044c00d010307407003030303c641c0c0c6a04100c3c240152200000d986061801280c80009503252501c510b040b40c642410311960209500c2c03507031101042c1d81042c0c02000840d40288000c40301d1030f03010000500490300480b800d00461400d003d00110004024010003404079225948040c10343c002e0280201501e8440300c1003014412504000b90b580021103400140801c0365004502000010f0003101c40e1400b443d21103c0e60b6450709185200104003100024413039000e110700c0c0c400000d407050808000c40046c84000d581390f1500c0d00706002c01542641204c00503500c1664100403281c1c01005071012101d10341401c00b55580c501c038010f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 512451321 1250 512450071 512450087
    0x203070309080a021501060503010614030408360d0f060b120111041e050f0d0305191205060904050d0e0109080f0d08010f0b04151710090b060306090106080601 70
    0x10300704038010440c3c1040c2d96000940000c01e0030300050000301c0f6640c45009aa00d031000317026503400251041d20000c2254007901c011a0858400da103824500400104030315584a01e1120300c1040041d280306040144440411200ca0200c0031071303040c140ea225aa44400918162480050085460f10300c4420345542c1c41c10784040c0e0b40407620003484600f4542e680c03080140d0280c0101e0b40c050b501c59105410341c1e800c1030300c21021303100d0141c02d0640c155100070420203900300e42d0344114100a410002403032245104085000c08a00a0b156180c0c41d1008050103804d03138400809160003528038100304070128000045000441c1000d08024104038001001211440e074542c001e02c0c83c900c500c3c200c02900102c0001d8012904404d0340d0b6030b81060b40c844495182500750f034858a40b00141c140000d20462840c05400240c50b41941880c989400d651802d246040808485104101a00c13520030000380983d0f009514283d5001c4070040e03d14035004d00003071000d00060203203500f08000c001c0003600780d9028285ca = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 512452571 1250 512451321 512451323
    0x30d0504080909010e01081e061b0d0e070302130917030a0605061b01151203030c171017010605010503010e07111f1103010e0a0b0a0f0305010603020316180203070309 73
    0x8641c10740e1541144080c6150a01c560025807041a01e03200c030718454850840419141c0201404060715500d4a290261400c0d802b808030310ba40800c46100c129621340b18030f130945400c04014065040c034500402084c1160f070803821000a00702108040040d020f0024070f056070110003140d64030390301d5502d194070003407400350825a001000010703410002c2c1030180400b9a0078841000a10241c00000c81c003025216043c072a00503c0813074055280002402030f004481203009920741211001c04000faa10701a51044d1018400130050b407100740300c40702e0b10042008500c40250028400c061074400020000c3c40705118801c6e411007160082039000c0d1069088801401c0c80d05c0c11550192100100241c0140076410345400e4036103031007640c0c816018200140d0303040310b83e051003044455a55402d00000f900e81d1070b100e00d92014200300007040d035440e00c0080303201450040000040040c194414940350400c07110750010b550007034001c204062041120700c9060810760650241c1c0300d499001065010f0102090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 512453821 1250 512452571 512452579
    0xa1e0f020f04120c05030c061c1401060f021519110919150206011406030402030a1e2604031e0606180c030c08011505070c03030905150c030d05040809 66
    0x400284400d003d1244524150080c05002960b0750ba810400d5912050003070700a400a01c180720035000c4c03444070250008001c10292000c1901c10000c1c5242c80000381c02d81044010404200d40707004500c0e8100000440903280c408039110301e0078610451410320b00510581c50b61780d41c55141e440c903042000b0094420018001d000341100d001c124070180300016a80c0038101000291140851081d480090486d04842a1800e170030312048610b414041103034402401030382c1600c1200c4c02100010480c000329519038021300c1035515550140d00c1c007007000303040d005911100c9016402906e010000b4001c1250f08407940410241401c07411030411084a40102030060a01450424005281c6070ba140b480c010380440f0540400540389000416402c81e98140f454800080c0398000500003030741201c02000b20300c1c910303003060782c1000f4050b900d05008400a400c203c0014003445010007040c1468503042022080c640611820000381e000c11665130300649011201840c2c440004c107041c4140721049400500000d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 512455071 1250 512453821 512453827
    0xd020d06020f031603050618090f0d0e0301140910020705120708120a051b1b010509010207031119060b1527010311090d030302120a140a1e0f020f 64
    0x42201c800d40003200e0413500c80300110418500103100f0f00c00c3c03d1203403400034070704590305548010f21030643d04001d0400c00c041c400d41010000c0403404010007030040d02a55103900e0300303900c02014982034a5641490384081c550042c10f1100b50003011460954070240d90500603200c104a0410500d007502c4030b0b00140425000081078420f10403804002c0c41c0c40d4040c284241025182c2c480344404944c42102e84210b0300001c20703e90014031311000001c00c5000705030032807a9111703500186c400342100d070142c0e0750b442c0f20384d40011110201a009540d55038602c0c43c45028142d818445002d8038040c40d00b005c1c0c000e011603500c0d14840c041e640c0c3c40c4021080403242c20400c940710b9030382d54120b45480740820150f8035120044038064129621a0040602d29035029034400e0404110a086c0704e034408004a0880506400f8042da180d401c00e010305c2c0c584500b00c0c04030042081e0780a25000b03040750304040c00d10408a8105800c8100d0000c00c4020782100c000300c81400100100b540485400902489200c4c2400034000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 512456321 1250 512455071 512455087
    0xc0b09030c01050f010b0313081e0705010e010e0d050c010603080d0e1005060a030201080a0204210c0e1023040f1d03040501020a02011803050a030503090c0f0307050d020d0602 77
    0x4080e107108032580000b0407264645600e0707050707040c0f000d04c03c4003044d1004100003206104280c1c500a10750b03218100180c101604801450800c006560a45a0351ba50120b00c50040c49000d0080c0702e0425050340007000304d8505031807255152085166100107118001543d840d40c00f40941c0800025500840d80a85426030024140301524450341e0000140c80b5400e0507500300e0b080d6106450207550018110401c0b01e1640d8015103458800802c0303841c4d9140c0c28400003600d002d00910200d81d04040700c4d005580b503100e900e0018a602815081010f056a03100b00f000407000350b001d1301c041960803840c02425110603e040b000800950300030368541186c10179903000041e00c6183c21400fa980d60f00702c10360103158014100c03241d4a0085201d402d00503800580103c026500841ca44042680c1c1080c8403030403181c513074658510f001240d000c00c41c0010f500204100c00b900062012102e040002c42755150342a01c4040085c1e540d900ca402a54840d000a40e01c4c2421940c504194905951b400f14040d503d038020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 512457571 1250 512456321 512456323
    0x90301060b070b070819090f030305100b16050c060304030c0203071d060402030a09021f09081c08060310020a1e0c050d080a020702090a0b0109051f0804030c1a01030201120606050f0a0c0b09 83
    0xb600e84c100c9c082410a00030800b510081945141960450f868050800c102d030054040310b1070334210700394cd003801102e80006054a03240007d41c13182d4029141c00560101790b106052800c20282d10604c482078445100c400c2c004607010340d003900000111005a01e0341c40f120041c100910300508025408100380d603007416104c0030004070705401c174402c2d00c40d603403400c0ea0b5441709511482c0360300c42d802454450486042c020340c001c2c0e201c2c0d41c01440140071101c3c0c01072404000403c9a002e00c1d00c0c0703008988080c920091643e40784100c06035500c82e1b0310f00b114150100e03545d0280d4840341c140800c403d0119000c0010003028142c0e05850030150024401d241606208440c81c000700010414540000c28902d804146414042c43e00810044100c01d0f00802002450048ae180780c4058011001c1200d0b01b0f4072000828003409440f00410060403003042294910300c005419103002400705100380d030414808200c915004401e6071020000e8041c40d60340c40310a0003084401166503040280603241800500180d604 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 512458821 1250 512457571 512457593
    0x503030a030515010f12021806030705041a04240e04090c0f09020a0c0f020a0e01030602030601080a15050409170c0616020307020a12020a080f03090301060b070b07081909 75
    0x110190300d0100541203034004407203074002c0211010201b80300e0010415402d4040d4020704a155070404101014424040014904d5006840f502d00007240480c0520440c02d41000c10384080c428414024a41458105580300c1611800307640403070396407a40701140301c460044500d49251074006004005075100d52604000c000501d0296425281c1241404903c0325518400c0700c05400140d02c482c10800e5039a0b41d000d100941d01c45040341c1125401c0400940e24820307a101030b029522403100580c0705c0c980310f0001064207100034440c07844c290412405020818401c50700e50256841a100031400078000d0034484031040850080c4042c020300051122100d080100e0742e01c0c090107210042d80c82241c1405012641d9004d5160b001c0e50004881300b00304001c18940011580387c03440608a0100e503642d803400c0034100490f0307050804060b000019180c03000c1c035003071140d03070b01600700f540b48182441c1c23007600c842c0b5080c44007c00c1700e030912203240301050388074000c1d001e0071440320705c440c00c140101d0516207440320180e0303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 512460071 1250 512458821 512458831
    0xd060b030f0318030712021c0209070e01020d08010b04171603031701060e0f01030f1d0d2006060f130e0a0c050d020f06030c12090d02070e09030403110a0503030a0305 73
    0x21a40710000715103400b01d011422140500403206c000c0203290200b0070440000d214015000e40d14170211001600d6482d43d03030b40710300701030b441d1000c011194800180c01c2c140d0a01c4018100250f020041c03045106510a980c00d69100c242219140f140043c03a884c5084031007140ca00307018885400010416602079080c0c818008401604031490740e88010686a004001d01c0d510380c454059071000762154469408181003500341013001c590380300090204031010544d02c4400c9256080585010001d40c0c002443c4d80a040c46400c0340180384c2c078480c2100d925810050111481080d614062904a5456801003440c07425032000420513440750a42e00c1d55118407191084030398140c0040005642d2910384c2403840c0ea25006414454106520010040035500050000d0356515050111100f15601011124440e91101d00144800e09191601a152880c00d9010303041540c410010080b603c4004004d07603044070751003501184103401c0007000482590141c1c0040b034043c84080741900f1110342c9500030380d0050f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 512461321 1250 512460071 512460097
    0xe0904060e1504140c010212040b0304020f040213090501060f3609060510050702030c040f180804080c09090a11030717010902040b1f0c0203150f10090606080103020d060b030f03 78
    0x5e0b81d070840059803240508a030852002e9002d10040144200000095034018030041c0b80b407010b4042350000604907040910410f51030f0030380100500440002e07200b954050121420b2004565580c404000c2c00458a1703206600407244401c442c065080d4541640c40c90180210281c0c0052611415204000d000c240f248030710416500300300e0348907180568100c0b048540c001e0050070318180c4c184c062202908500808840e020340c2c81003014620003400b01003600e4644119015a601d606c0d00b0103082c40e100c0083d08080c4500c1c00300060010b80c0344006030352180541e002d940701b034001c0c2d90800064104440c2d6800500d94910990003019004419480b01060a00c21a02040411401c0e0b00307000c06a580040310b8000f00e00f9003074003000d41c41d0060004440301c520050441d86001442c1205d098500c10070780e549011240322205101c4914500b81c074403006481240400c00400b898410000c0c840c0c4010711019001c2d803002030b00c0034107010b01c1d90000010448080c0c22a00449010200315a07203078026281c00c1da80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 512462571 1250 512461321 512461333
    0x312060e0105060f0a020f0709020a080a050105060304020d080d02030a0605310f09060c0e0a14030c0d0218190617030d1d01111206010e0904060e150414 67
    0x426415980440d050382d0b00039215034140003481009013003a0380854140710a5100700024845410b804101c90343c0500301151002da1141140c40d0f0180885070098062081182800d0040c003050b140c54007920b070302c01d070110b540c0d0106003224102a811807081ca80c001610307900010030403508601e59000360044032000c1d190350411101218901d54603c030702051810b0802d00c801c0c204060304165402c050415141c20b41d0000d000011035032a401200d11143d0a407010a0b060500a0350514003110544018040c000340c1c03080d5114005c00280d03e41c8491a68640700d030b102c2c00c0e154425034903411002c41109039113455010550821001a42002c00600c500030b62082c00c10304041204100440d03807000352640c01c40110b041c000349940490243c540308040b0901103102020030340d45840c0034058111504666015503503100340301101080c0e0603500600301414821859481d0315503403150664030340d01c04e800a4000803c08039400e546410030500b0f0800c0c107003480d41081030005104a1500c0040504260411104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 512463821 1250 512462571 512462579
    0xf13090b09090303040b270a0507060207050d05060103080a09050405091b03010e070513110d020a3b241b010501060c060924020c100b0f0625031206 65
    0x2580c0d2004440003803846c024000480c00c007030328080d9400820b06101c0035004031560104081c0b842e012080b101507900741e00a603001c025154042c0020305c0500300a42d208440c1c0b40c100c0c1c590030b5807008180710085c201800024405080351050008002034000140140071b10f00b01840c40c1c42e03031800111646030000c00c208104900e02c2c5414443c80101c070b61001e0141140d240740c030081101e00140903062a01c407d8850030700098160291009245080c00d038800161a40c1881c1c40c0101002010070b4002141c00c058a0302d80001d000080049042c0704030401100ea44a10701008140c4080021440502e64001c040007212454840006402419200305505803410050609c1d5402d941080c400d110104020004903004a0099005802424051058001a581008400ca94440c003004204003002e9002c81c003030410b00e00610128444501542042c010014214001401c030402c84a08070311a650015982c181101801c0320b190541580301140c0440040608002d049060b91031000c103201440c0001c041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 512465071 1250 512463821 512463823
    0xd0e04050126120c07061b150203040309080304270b180c09031623010f03090203010603060f1e06061d01030b1201061d090d03020f13090b0909 63
    0x24101c5500c90108a400381034040c884035002d10003400342045016111101c4021400c90004210307200d503800080c9085880d200004108500800d101e01504282000003000318821b07126400981d0711080005a82c1e85907458180c0d02540103a01560881c000840c0015445028501d80d02680c0c212024039008202400e40580484240000c8154840b0071081c4c00004006031000041d8000c0006440034a04142040042d2a1240f0380c0c402c03c110040300c000c1070210410b0980760160700444411503d2403252003138006042541140040030416603544450380039076400f500140c008603000b12080001b69452240c04001d070801c4401c00c4c26403032141e4968000c0307400768850041114201d980701808481184075007560484c00c1202c6a0415485401e14903250381c4480b50100706092003400041c00901d80000f0284ca04112003001d0303100442441041088031012070403142d000007625006960303450b4020303080350601600803840b03100e02c41e4000105a1046503880a00552001c581008003590b41306481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 512466321 1250 512465071 512465081
    0x30c0406080709022b0516020a0201080601080a150e1006020a03050405040216020405150109090b0603011509080d0c0b0f15040906020405030111120c090904081309020a020d0e04 78
    0x3400942c040c000030402c0c1c01d100d07405011455581c41c02680004145940140441c022041c4101001c3c1c1e01c038103024034541105400310208500d4000303050341c480d0f1600060f0101d02e00405450611402800103079401d40700d540111040c031164260b114041c3d440713000500c40c1e88401c0765040000401c040340440c2d40790001800400c502e5265940526007824842804003a4004145000c0700803081c031203182c0140d4881c00b4403845004812a100018035083c400104940040e44c0001c00e22460504110300d9601e07030f00c00316030554841040781d551110843d8822283c004141e03003c0c071041d0040f001040031060b4021402c403035040c042ea194945e00d443e001807400c055503003030782c40c07a090417203601e440ba2050410760491002135000344001810030b41c0d5003000c6403e43e040b41400b00855100021840400c500e07102210b600b016141d2840d0741040781c0381020a590b081c0161010340b41c0c00000c1147c900e64030002071150b0150038034001c29500e40c000614040e40c0c0e8100d41e4400f03008100c541c0032410450400c0d01c20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 512467571 1250 512466321 512466329
    0xc020f060606120c0a0c0c030305180f060901030b0a090c0c060c03020f04030f0203071e08120304020612040c0b040303030e0c010e1302090103110f0a0206070e01020318120708010b030c0406 83
    0x1c004541e04d407440d4024042e0b112120140c14428512101c0000c10030700c0020350000c44c000e803580c80c0d803403a0a100360901d4100b00b0b00c0f40751080560650209441c1c40310000d0300d0183c01e0070700300001c1c02108540060805142d035844407001c5802c01100c60319040e13000320782c0c0080600c00c410520010580d0582a000c0c0c2c0182404454400070902003080803610907440c0c602c0290016040c0c42e6211344860800c051101075405c1c2d00d440211b44e01c0e003000000c1c01080020681c0340014505802c504155002030540c0c4140074140b06840d00000115085c0541401d92800034104803c40a0317495903649005409400580c44a450501070102c250003194090500240f080304c00402107240c4100201c0018002d4000e010000d04165803012045414001d2100a00003400c3d105006512003040a600030b2605600130807071010000b020001e0481c50740c0000907030381450340b20b03030301046454501e101080c0000c1c1b03010798000851113800340c0041c520b075042d40011040e4500303800381c4080d40d100700240025030305c5070b100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 512468821 1250 512467571 512467597
    0x204180506012a0515101235180f030604050a0b0702010b0409050102090f0109061e0c05030307030e12090127051914091303120209040c020f060606 65
    0x2981c8500c031218204882c0e4901144031418608000c207845040c03409180104240400c03251030248086d20840800c80340003400d0008207844c82c003100742c0c1c500d002800004520841001310102daa080c04402c10074000403080410040c0e0380f5004803200b8011242c03a80000c15010b4a03403502a5180c82c00c2c0420035511480d0880020440c41d0619940c640d03c2d514001d107110219540c419940d40541d43c0c2e4010b0401c2140070f0000582c8411030b49041020031000d1903401e80c1444651001004429000912031030f011451424106848429030030035111244003a4004026000000801070a240c25500c01c8403000d0741402221800038540741c81c03040510030030344000d01040301600c80d1b00c4e0210910750840d001220500001c0e05840c1d80c2c0c408101d0404e000942183c0d007880e411018000c1d84c200c440b01704d074420301c215541c2e8014100b80c03040301d10612009402400b001455040001040c2d80e07901140c4141502500c02c014040c03292000035240d40c031001221400d03010311030200f40186005002d907828044010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 512470071 1250 512468821 512468837
    0x504090b13020103022104060c0305010501020a03030c0e040501170706050a2a050717121c0203130b10030201262202040501030c170a0302101e0609020418050601 71
    0x1105030800440c07160400c90405800b085803641201040c00507000000041e0040a0300f81864074000c82510340c02d0b20784508140c505001013000360382c0014026611034042c2000165258184e40841c1c1c602e44812680350050b04020000401058490350a9464602c0710141c4480d01e848560071a11072086000c09000285040c6030b0300002400c80328066440300040101c041008541e036103680c00c05100342e2045a00344001c1c92012003000301403002680d4801e9410b211880d110f4054903146c40520001910741817a54003200203200c0443d1071104054160b0024058003080c5803248141e031070740e0003a0000300d00154001d8410130301d608004040200088100342034940070394900d00b021090f0414044942c0d88200020801c00160300c1e2445010702960182c51805c1d4203905004001c61408900380c050a00b9501c1121041c01190740030448000059408001003154500c56070b11030727619510341403400009841c100c0b0002c0c1030f00c3c9981c01841228562100c990301d0020952090003120000c440841c04201b1f19 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 512471321 1250 512470071 512470081
    0x103050105032d0a050a0b011403061b0d1b02161202040504020d08070c050a0b070b150a1a0705060705030c0304030c080d021303020306010b0406120c02030c060c0a08010504090b 78
    0x190142c400e035407200f481101e4551000030400c0c503241c121041503d06821000059061015160640e03000d040c041c1e0800c039001c14050301080c1c0d5101e0013130000070b01f0b080c06140e80014270b0356030f400c131032503500209402d000440065103d203411926036a0210b0144c03050714024600c40c44010122001c0750100b42802c10110003030307001e1001a250061041b4be100e0038540b181800100064058a10039000d8030300504002d0408003400a070010300d0300701c113403480170a000100028268011595001107414407015038104600007240011045800400e03496042884901c42843c0840c094400180076904072107040e00c0d0810b05864510040c0c8003450145c004000180c0070031b001d50704030a507880c414205249404c051800d10030480c2c02c500c95440d04a91903003002c005601d41001040c1c050404803030360a140a140c13038406440c0b000304a43c6039031030316200c942c000d0701d050080c81500c1400144005482c0e070b03407500642400303940c0c3c0700c0d42d4060042400d0321b0000c2544d040c288201d1400fa54800c803168910780325 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 512472571 1250 512471321 512471353
    0xf0b030a1211030f091305090307140111160b100303051608120f09070b0c030409110714070905150a060516021306080c121c090305070b040501030b010305010503 71
    0x91070700356005028603403480ba400380c2400c20040440e0035000070320a0302c5100301002c00c140c8541850381201c180741060f060042012001c412554090303440102076060a001800c194013502c0304145030311000c8004036031031001414a2401c4910944240c2480c400c964482d41403020400c05400042c0000b1014000808441000d00d0302d00b00441c02040c43c40d04080c0d80c413000c0c041c80301080783e4401d0f0b800348c8072042c010001010003640c0003078408080304600b48911408090f9032030056214050300541c5500c3c80b124071007440c404984015400c000c0748208003015541c180e68035100f0b40f0070500030340c1c0340c8400508100140c00000604c1c850052411544c9450003030300316020f0b0410495906a1506c801510380113a5030820280890740b21240042401d0340b401c000d0f2400d2401101d88103000320124140303c46c582c00c010805903841c081d4403505800d460700803d0216025680c40d00003c1503407240f40008a0303404001d001800444009a03070a001d580954401102521028400c19030160712240c912185100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 512473821 1250 512472571 512472593
    0x7080708031b100203040c03050f0109030e040c0c0506070503040209070e0a0303080613062909090621030a0e0906040207030206060f040e030d231509130f150f0b030a 73
    0x326a001c000200c03c80e0101ea0042d20121380e00300040008004014080c81f001c601c0b540300000070072900100d40c0f8003400b40a4050403891041c2d56908510900b01c2c044c202d80d40406400c081280c2040c500a88050641d83c002e840513842812070301c0000d242d2520418080c0d51a40014003415074240c45c41e80c1c1034610081c00303420541d0102107059203188100262003000010003041107801c448000540d001c0940903828500c440380710030100458405c1340c454281c80d51300f1840c1a00c41010501c000d28030255a03070141c40407020070f8000090045425648204d4101d220700c030854101c5442c1d1100e600b00400ca101d842c4004000d60007180000f1040e203800078042c0140c0c00050000310f036440d140f0842c0d50442c1d100300c080c0101c1d260744e4076141e0b500e45410b0482418110b80313940000340da801d0000c01d440d8405680710082c4d02c07800c05100050380e900101c0100d1007130190701084411140c0124540120520018103e03841d200745403c3d0b0307461481000d0300403031440e55806005842c10318010740719650912 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 512475071 1250 512473821 512473867
    0x1206040f02090c0703120c1e0906110703020303090f0a120c061d09071d180124120c090918060b060313020d050f16080d03270c05040c020f0708070803 66
    0x2d08607081811401230398a4034103405c2980ca418001c1c2c24060064100c5220b203045200070b5100030014001a00d00008a0380d1102c0125600443c0800700400100850700351340110410704102d90700e120400142c0107440e41615082c2d281c4580c1170807000c018800c0503e071a02c40d694014441c00125207600d00809405414896940c0ca0140398000030300450b440900d120750204c104000300300100b140f2258842d98100001c194000c070b01e0003420b400c0f802004406000e49002c2215520210106440e015111060090044420510401d1900d4144220856554000b82e40c05c0c0c0c100308000981d032420784100c074416020b0322040105241c20703400340301c601c4101010840c1d0600c00d5248103c1c16441c01c1040c12180c07240d000610583d58144110141802c070200454010725041040d02440714044048450035140d1101c1c01c05061049404c002d582c0c40030a910668101d8600081c41c1c20441d400f182c041c491801c0c010440d0740c1c40b50782d13140ea076035510b00c64480c00c48190400e004e813041c120514096407143c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 512476321 1250 512475071 512475077
    0x14061c0b12070f05030303010e040305030712060b072a150c0203030325141603170705041703030c0702010e130c120c030b03060705091206040f02090c0703120c 70
    0x4420004081034001d2018200440c403544040c03000c205107800c561150002d400305502642c119407410320080301c1d4403005040201409004000135440600c50710039410801014501840407079a5448200e03ca54850082502c0c0080903a01070354403203100302ca000c0480e9081d80f40044142e4500700032010302180300700851040202205085015a070100301a42c056a00c580d044242028102481c0c410b5000e260b50140070300c0143c440110810001c4010794600300000e0707203c04010100b0380780440c0c3d1515800b019460f000c01d41000d000c4d4559100010384141c890450b40d8642d4400c03403801e0580d0701d00080301c00d04840141006941d005500c154202008aa0090700c003211062240070040296041d440200740003800b141c40c07017001003120b03010b14540301d901d82c2030402c4001403100c0401d81f00e10300142254144403002503001041d86640d19072090402040307041d039091713040503d0107001d042c1d040281a48101d804201051401100ea001c036144145e064841144824424514030041c1a103803005500b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 512477571 1250 512476321 512476331
    0x30b0117014101260c0a030605010c0809090601120e07060f020f100213031205120703090f03140c01060902040515040806130c030b070509010906020c180411030f0d020714061c 77
    0x381310104c5803460107640e5000359030fa107840700c44800070704580060303002c581042144206c401c0420206000c841c0181000e07200301c0381c1541c07400700589000300303400450b003045413808108144040c800b24100c030980b1f1030350b80c4070580d40b80ea0000899980014051800458102184000122402da0300810070034400d56580c00c24aaa02d403908020305804546601c0070480004001e0b085800700c0c403c2c1907104904d41030801100e0500d440d41d50318102c1020b0b0080c240504180c4a02e4119824416142003110703510090000c540c030794020030065000b500c100740c013501010085040c011108000e4405a4410074003c000607501d00400145800c03042d001642c0310501041c0100c045000240c00c240700d040d0580704c480d9564510000180b404425500c502d04540101c41c4114156550210402c0401640780080031152102d040000c540d00300d40d48540d515201d050440d03503000f5008601c1c0500400c01d40c007076600b6140c1c1c03850f010701c128a2084207283c1c020310401540080c3d03940c00d0400092400d207410300080e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 512478821 1250 512477571 512477627
    0x7090b0c0a02121b01180b0702040902030d090f0503070821090d0f0308090705210312100f090209060901050d150306050a061a0a030b0117014101 64
    0x10b4000b25044a009180c000d4100e1155410702c84100724450319083c0381006e1090302400c0c102d0b07115030305801154124880011076205554803034022142864009040c0c80300400300350b0000e018050036108580e42d401c444800000c8070314012608404403000040981040c6142c6280c411003c0d601e900c0c510b00c03902c024410016035407500e1080000d09445154402c0656411313081c0988602c40c000c103143c0003a441070000388941c0e11445003070511007000074216202d055150301c019046008502d040c603e00b4102c0010041c0300008100d03080c04880100645456032174440902e8401d074420041503a81003582040300c80d40d41d500c9070004004d54014000d001401822403a001e01083c40c183e4801d840c03850b155002c1c1711400c0d44511403000200440440300703140034200d40c20f8908074010240b1202c18140e8407400d2800f107034007410048007400c0c001558410550b840f50a0301030040c1894501d820481c8500040905100080e9011124000c4a04580c0c05031300c4031400450700b0740c9005129503c1e180c1c48030244a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 512480071 1250 512478821 512478829
    0x405150c04170115051e0907050708070b0103020405100825030515150105040e220b07020a0c06080601021c1b030e1503010f170102160807030207060807090b0c0a02 72
    0xd00e582d10303042d00100302c100242ca50034404081c9500030500c1486c002c001d045008101c41c1d165280948242c0c1c00c0c1c401903940c54030655903070240d024090000710380015400108440c00750400d041e24070846e410080d5884400041603545043d01030003500b540801d42000281d411851010310031018890307441340c0c00d03840b50f451070f0400030b0590300d01101c0003d80c03091141402d0880240a24600700b80303010f0342090f25117550320090600c003800d107103080a510680a151024115003a517226500a000f013000742c100000001e6842e00721810903202201c1407500810241e03c41d6a02d82c0c090b0805900501c1340d0201c020494425014000c02402440400c2000003810013045929008990090316a0b561020b48402485400c4a824183e5201070a04000506c15004110301074000c1d18034610510320300da48410001402449400303002900101203c4d0414200020300c002042154030a03030a03900c01e00d03940c3c071082d21141400e803054004111084000d0180540c10780140c05500100011038189007501e40201d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 512481321 1250 512480071 512480099
    0x6050702220b01021005090304060e061207270e0402010806130c090509100e1902090303040308041e0312050d0615081f031e11130e010b01080405150c04 67
    0x144045902c50304664015a014071081c1c1005031160028456460002c8126882c0e2142d809524140f242254100c203046c0c0302c501c2650400b2031494200700d2035080c0218040d00b1100e17007180170014200d0615481800150090142d821035942d001d42401a45072980192802e1000400e00d40c0c00000c1114076207105011070198401c0d110b01c82d141c04c11094280b10901541480050400142c0e00c0280d078100603a80030041100e600c9a00c800c01c00d020048900a0384c0080c0c8070b6404525450320011501006002030038009104031a801901000d0980002d64035031103204040c03001034281c0b010499444030140c040c1005107041d50401100041c5036440d0708050340c030345146140c0440041c421004020500c00441210003c400c125412006014a5590f407203d00e42410040380001600c110071803c104885103a9405203058010000103d41c08035408101c0104542c142849943d800c11600fa150755002d00a00c82c041e5401074050001e991491901082e004000762001456030000c110001c1d00340502c1c10740c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 512482571 1250 512481321 512481379
    0x904050c0a030c0504050a0303050306060c0706030c0e10020a061d0a060203181902190b07150c051804020a05071401150b040617060a05040f050417030f0106050702 72
    0x21a44640040710000c08503038443c20341c1010300000b00401d010545d80e148440003240d50500e0641d5a994071040850b49a01403250408201d01c50420041031058143e080b010820344c0a50381d48180b100ea441c200180441d6400385030000da0000c0d08030a01181d881e80000c01c420000540016001d00170408191808003100302c203444440e0301106014406c40342c031200c520514221401440700c043d404148510307036007608100070311883d400304140c41440298103a4400070015072010680b10185130030082c10403008032030582d07145440c05200b0702e2220b020b041517500420500079025108403c2c01d042c0002035010803025403d00800380004e100141800c04281ca00161034800481c6100d8800d040344001405a08551052721080c442408003645c000141444007605401c084140d4440304040745004c04c1a40000b034020b405c0400e80c0403801c0301500b1070360055100c6e05600304500121140b0072154002901d42c164841e035a040108910b521807405020703034900003014001070800700105442301e4269124 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 512483821 1250 512482571 512482591
    0x110a05010506040e030a0206011229070201110c070b0c12030c041401020705010c0303051305120a1b26040f0e2a0d0c0903081201150306050a0905060402090405 70
    0x1c01c000003820180a00064401c403035000390300b050b0750306c00003949a5005008105004d1810011481030184088d41600c4024808400c00b1514000300242d8010090403200d02c005503090101c0190102c402e02c04441c101e140d140050600b80d030400c965030515030b215200c038010500c12140c03070074030844481c40294019a000c0c26941e07581c0c0c1c0303062151451204c11181541c19508880e20810441e6040088041034a9042c580003a8039920028020103030600700b0b00162540c440e0303900c5070207200343c80360041c05850055142d410300a420f0400c035417100031407548000c110781e60313821806800ca91a101c0f41c07100120030491203400c02e500d81c42a0101c00c60346a0000d074801c1110010f0002c0c10440300e001c50702c04694001440d1416144503982c0c14240700750034601403210703910508000e6451140e01194003550340a00d2a0381c0e10b06400e1607070340c11481c1c00e0281a000190005403c00105d001c0c1c0314650850388060442e8034018541100c840060034000c10603a0015020080383d02155a9885428030400980b1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 512485071 1250 512483821 512483831
    0xd0612020310020301060806041d0f010c110a08040501030e0312040303140a0b21072c0609070822020d0510062c04020f06030702062a0a0f110a0501 65
    0xc0101407070804010401c04100b48100700601c1901d07407000d409540b0000540b4041000690071003080e0300b4140b400c200b805035000d400007066510606400c094a5a4519030324080b812003140640340c0c6481880000800e011f0042200300829400ba401500481da281c0c0d09490400002c0c120811070900708403400c5001a65811b48042c003500c20f600700c2500803225180c10000003d50ba00440c0c00c0351044030402245040d000083c070501c41040040300090300d1440e05840b5170440c46007899103d805018065101e00003180b0018000b414055000c41c81060f0554501c8515212015a000d0542c00008441c114102507807017400961112030541e410980f040000340b000300400b901906c00c41d1b002c0d4205030417243d809100b5082586405420107002454690500d0160b150761000403070305201d90005941000002c420441290740200d4814403c155007001501d010030194401800c5000c03801c035289011100384241c481302482380c025000103a6403403c0c4200c03100c2d40381309030034500f5081c0581158143e46070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 512486321 1250 512485071 512485073
    0x50a030c021e03031c0b0a060c050c01030b030303130f0206070b190515040f201201080a02101107091b1b030e0d08070c3b1b0d0612 58
    0x4010020140582d095400e100e80000b400a40c8070321918910800d010b20008070895403c0040d0b03c04c0540010051100c02c0081d84d07460044d0100070000d109032001c3c0141e01400f1034950084c0a10540c0280040c0603500d5070781c41d0407005200b0751716284195440940c8030708080050700e84800420b2540d00401c0c00b8201d038a42545c043c0c03103010700c8c0d4441005481c104018004e10351004403808500352000c9901017000b003400d140b410300816052403002c464014900403001c210720311000612000c1006198640141e88580c00d00d07940ba00c0c101c2c0002e402ca92244800c0c240984074506a400180740b60054070916580c610500d0207803051031080740c494407210900350400030303009544918200d00d202c410300b20700d08103a20090015240d02840320700505d8015041010000c00c03d00304e980c00c1ea48400d00c203c041e510b4990a44042c0440d00c2c503172807039502c82e640007004005082c203603400358000700584140a540700c2111980300711025180003183c04082c003122681c1009801040c001d000710303001481d0702c0d001c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 512487571 1250 512486321 512486329
    0xa030f2010051b0c03030406050a020c0616030906091202131b02010e070e0f0f19060315050121200406080c0f09040b01050607240606030e03040e0a05090703050a030c02 74
    0x1281e654103d15a1000c115020b083d2408003e80b41210f40a0900341d8541c140c540017a42450f1030306c0d0b40785174072400001c0c2c2490444440b003030f032030f002c58041c1c4d0b6110310f0140c4441c02510b00320142d001c3c0204600a64a0160051800e50442043c02c10914004203184d1401e218a200c02040d400c3c865000d80d45070503642d400c002d0108240002400b010b02c2c0c240039030410030b58404026202401400384550510300040d40401c03c0503c010140643d080100081d56890030318129900b6448a91001c940c2083c0002076030b5000250707003641c40f2542c0e0400081c10410b564a03100a80c4945060282020380f84070842d034990b0b201d06c100f1000b8074080c40942005a100c00c100002800b40c00e0b0344d14421890a800c3c000810f16500ca528150f0308103a0b036182d42c41c1210b051089030450703c0291003541300d181c02c0341001d004c0441d41004040ba20141c60500020310417401658482c0075074025851945101000a40100d200e80c020541189950041c7c2d0f060903220703250a0300b0500e9030304094010910152440c021410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 512488821 1250 512487571 512487607
    0x60903230a062708030406180203030f030a0c14090103090222050a050a050903160503070606170606030106060c03180b040605030411030d0903081e030106120b0a030f201005 76
    0x803484051000d0b0f6200e83d94070a0f1500002d8030203407c8664600082c104890210103001c422a00141220f0315510100281c5405c2c0d03100b1900ba49510341070424641500340559a000003032443c80040700c5c1007c05a500440042074141e100382ea018081390b10000200c41c03010203d903201c92a11070003007075628041022005583c0e001d00141490b602d01020032480540100585600905440944440000c2070520b17503e140180783e400340c0207920b45000080e0800017110907409084404041c1c40007560b0303000c00c0600b02e039a0761040c0c034041030412041d030f40003d11031034210030840003040c9951b02d0240c40b0100b1558680294022201143c000018081808080f80c91110034100480c02840b04100a140c018030548003444001d048a00c0071590202e0381241800095009448000302d58683d030351010001c001d8850071a04941c981c0c41c0c14031086850800409100030341c2d800c0710542281005568078440350402ca09800d5032030b107041040e0340c000e661300c950303108000d00803a50ba0b83d510b071a0001e1030440410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 512490071 1250 512488821 512488871
    0x1060911210f01031b0302090a0506030615130f0e0f0705012010020901050714160515030606031b040b0a1d10050d020421060510060903230a06 63
    0x94402081582d06040300c8650640e941314004d00c40d40a440031481c07a04078910f07000251300000e160200041e101c551b030310041c400c21048088134810388561038a090441500001140c00023134030f01048940c3c0c42990007003041c80252441c0020307104c1001d0102403c080110907014000e8004200402003580e2014a408a01100c84c1d4903c5403003d4200d0301c00d6036010715558504500e40c0129100300d480c0c1c003850070703215004d410100808801c201900c0160700c0f4101c03a00d88503030644040901269a00f04041e99000304c2042c069450300d561601020003100d5080203044011405100070180c480e82d105c54007920052500d10005601c488800402910b0f100e1100d401c201c0142503107a16170080d0380d4084400403400030392b05000380d403036000141180180c4203541103914403600c1d80c040e004d2802c5510504010843c00b496041146480381c0c10040c5002106114030030006104c804248013103120000501a03003c0c00a080d10b035400f1505514900782450b0441c00c0d42c441d903543d140249800d1580e48400b02107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 512491321 1250 512490071 512490127
    0xc031b211a0303040b0414190e043906030c02191403040b09010e010e03151510020705120d093b0a0e03211509040b150406030209010605070501060911 66
    0x211400201ca000948d0f202d11a201c1d03858038010108080c403030084940c00c640c1c4c0c800150301c0d1340d95004190f0071841c0d52403c0042c45405690960004400b4442c0c442c2644101469014003008141c800d4a13042c4102c25040c2501c2d031a040381080301031072400b00300802c01441107003001c3e81c80300d080200141022000c1803045062202200c2407420031350303000ca11800e44c004002a1082244c0b60324031000c5e52406076110b419008403403066541c01e03443d00000c9400469808454020394164001005911503041411450125207114018001e82c1e0002100010030b84010840c1c0d01810441610011100d401500c04419940c1000a00c50700100d075018000507840424001e524203400d07002143c1d0101c110303400d4041e03080407450200c0d114804810f00300600700b03001040501c00381428140401085002e80c1c0b0403c541e02c452080317244c14140ba0003100f04032030b0000c0458005a2030414152110390110030100d455540e1010b010400d20300a2241c610340703d0640c04000c0d1a41c001406070310029140106a05a0f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 512492571 1250 512491321 512491339
    0x3040618120207060e0a090f0b0316140d021014190e12060c09121e060f18070e1e0411011d0907140c010c031b211a0303040b0414 57
    0x26a88444160b002115440b000000755603e069230540b0040040705100e56042c02040c0708100c0c1b514000310a030040c2e0b003403650041c941910250030002c040c20380f01d40003500b01020803803416615020711032540c41d0040c1c0403542c52400c10f200303c8612080351a0b2036558042005d405114515040019001e900300324820014100b60600482400c014000c1e007031490300c500c440e0381c415070904005000d140080c14946c1110400485081c0425880301d40440302c011400000200054084a65000003142c1040440c090b003101400c2c204d040301e1064004001d0025204003a5184802e10202c0610358400ca00809091079580000d20006111010722862101d07160860f400f490460740d00d5200441d0000082d04115110044ca00440b21540c00740c244100c410b175203812584115540c161304110031802da006030a0100250f204026103400e0384841d00010520020845012422032a502c21940c01e807408180c0802607030840c0000c0c4c5158400d030030091550348003050800c65842c5400d43d00341c40040071140100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 512493821 1250 512492571 512492597
    0x1908070306060e0f1807030501050115030b0a06050315120a030f080603011a100309050d02010902102109140d1110110313061803180f0b0702060304061812020706 71
    0x5809202a22007103004070300c1070110b07810749820040e14000312340c468003c0c4000c0d80e44541020103071400c0703017948000c281070869800003460f00ca0317040c1d0181c40705529501e0554403031886050403100b442c401180c10503598071480b100e4103410400c00c01d101e4802c1d40c0704c40740081c030307140020310b16440604594000da0601800134045100c3c0035403560a04002e0700c8aa10054000d4800c070003030050781401902c1070140000984803645c3c107420070f411040c029203484110020100049403204031160200e1403801e6071003903207106c40031160800c0f1200c40c05011264446070550915038100421824000c0200352080044100d0400a00840030005a900020004a0350f0702c40c281215200081c0f05401c0541c402d499501000641d034824919031036060301d501c5440d40e0303070300d4044e1041c0502a1451031143c06180c0010340303080f40d10960300a0798820742c0c0e0b80b810041a07500748030141e0400707401214482d0721260001c81140035072951440780e9002e410000d0108444400190502d119500080100089005a88 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 512495071 1250 512493821 512493841
    0xf140402011706130e01020d0603050f060c0a080c0901020129012705010809010f060b03060306090705131512080306120303060108130302010b0d0b071715060304021908070306060e 79
    0x82043c0a83c1ea001720f5003140c5020f41c680244621040b0701c001516094001c8280480040c0350b030080c6007000100c68072602c50b000585031034001c2035100720005907102c0002e0700c4001e0640240c0b2000c00d043c00046500d03000311600c0b44540b4141c404508883e01c81405224044d0303403001300c2c0e10501d001844441c0065015030a00c48038070700140100c6040c00013100100d40400400d6100080c10005194104219500d910003084a076105480c028820702c40c02003c914015004554403040301c400924000010880914100240000c0d020b00403038081208800200490007100e02e2240912882d4080da0301c0c40c0c01307003c0007151f6007400003c14140e03000780100070031a60006400350b000040314081811041681c1b504a01408180107283e4110701800034420400030003258903800744940b5103c05182c2c0c803641e00d2203d241801161440400c0c00c4c103107850069814074000850b0854005012503641000da104681ca1014156002401650201ca810414001203201d10000383c05000d1039403203c1d007048402e032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 512496321 1250 512495071 512495089
    0x1503020630010f031403030f0601110114090a0615030f110f03030a020609100e15070504080a03121407050d051012060e0106080d0503070f02010f140402011706 70
    0xc094484010040010003a66070700204551502a0030284410360f141caa2110f051450361000712005500c0c11041016280c0c080162445165025040d041f02c1e6980c070011141d41a02411104c000e550726a28110805402c01c0c41901c141090b000824a2002914001088400040c0390b008413040072041800010081c110200b80160014401001541d00f80f00280c0300015940b41d440d814840000c1983c2056000316840e4810a20082034440b40081112000260360b1464079506054001003c88054800140b54003908100c1514200d820070380c0b241c071450719001c8000c40c03d40c045070090091030240c1069010b9200102c2c0c2c0d9151070b1442d4201050040d2840c016085550085521440014141c2c801405260001c00314a900c00040c902681426070040c803004070a00e5495080000100304000c001070b42c0b0912178216078481d403441d5110701003101d08036046e680c400119501d4120503151503440340260000040d007000480c00508188c4009000d850031a03000c20701a82e1b00400300303c00d0307644d440c10b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 512497571 1250 512496321 512496337
    0xb011a07050d03020a020304180b01082406070c0f0e09070f050d23030307111006031208090109020907030f1a010f050a0212071b0902030c04050d0f0606060e010315030206 75
    0x70260b1240320445c016411409540c11101d6140398104190900000316004164a1103080e210a0030350f440307150116006000c08001c2001e542c110440310151420700000030b09010b070040381456481511101b965104010503840354034055030324000d0120f100d409100200040c450344450b281c0c960301e464007060f20545008005822441001e00a00e00014008410002c4d00351000030b40b40d0300e240a020140c0b0401040382d900c1003d11408181c10380e0030344030780300705015690005040910102c07500001c03102100000c0c044d82c1c0079500c40c8501c0c0b0068641110b4240035001c40e48003c00d02c1c0000e4045003044500406250034810380084c041d03140341e40c000f090604041d28501d00035030b45000302c2c0800d03031400d60004040004418002904024003052201c041400f00c1864032621005554103824826400240c80840d8001c404010400061170003540e9030080e41c0c0708a1504c100410551070303c200720b90945d4002404243d038a5085850b81da45440388888201502450039011810350300031541c01d001d1201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 512498821 1250 512497571 512497577
    0xb0121170904020712030230041e050303010e04021c3504030501020901031128091706070305061203040b13050604031103121c09140a0b011a07050d 65
    0x20740d900c054907541c04482c9410b400852800d62001e04903c02070003548054800518442c40d0a2841c0e20100244984224a25024003c2c65152196154030b070321810384170814817030440300c00690300000704240080c500a2016840d64003071880e09005001c900c0c104180089034404c40d410011001490b005107800c04468158103819444411904480c0140d689012402e0f1444011400101300041500200b0b000c08081e80c00b40100c4e201c40d5108801402000604100328125020902149444601180510001e460000700d442d5070703000e81416084008000074a160403080c1080b000c2c607018040c031a04128103503010a11a0090313111680c4a018601030f01c20a00b40006001c441d040c1800c0c48040a413100408540d078580e80da180401440c190440c0a60282c0946d100c050030b0b4848502c2178603d11a030b449004030040c103032815450014480c02204039524030821920400100b4200032548401e441070b1140d02855040c44011001006030046e4048848410081070002400c0803543c400c55030183d037 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 512500071 1250 512498821 512498827
    0x1e08031302010203090d080c01110a0906210614040b270925030303050105030303040c090209010221040f0503060702033f0a05060414070e0604030b01030b012117 71
    0x480104d08604c10b50391003560240c448030861061000301802040c074143c00c4802001810f90000c041c403c1401404941408184007003010003105000b82d620388110440550012100c10707500820408586540c2c00480000700c106034071405504203445511420360040340c04c003004080c411605046030704040b09980d1241011000324180600030001c1c0500c0c607042090b0f0074078054040342c1e4480c14510610086c0c0001e4244030000031603040c0442124025030704800c0c1360060500b400043d01c06580300c1d586450441c4107840481d140c604001111449440c5812541070355a482c0a590a00c0c940b21a04010320a402804c144003455030000b0444601091342c0070a00000a0102d0001b0503102038070603c02004030007140090000d0207800900c61180354802010042a12100b041c04111008441c072031962011100c00f140c0440c0c000c41e40090800401406a468580c495403400405102030b171088070940003140c0140314442c02002c1c0340041c10851100520040703a01c6e02e4050080b84030000b0710360841307400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 512501321 1250 512500071 512500073
    0x110606060a05070c080a03020c011b0b04061a0a0306061a03191d16060306080a0b010306110c10020d0c0c050c0114090613030c080d0203120a14010806041e080313 71
    0x203107150b13030001c00281d001d45840d101c40e4103010f91101038a0b2840360000d80003051016110f418100f0f402805500711081032110703641c40d541e6000911071101e1091100d0345080740703501c1580e01d241003440a50322401c404140fa070703d443c0d148040c405560451140d003140c24000c000c4241180100004d0007010410080766018a0100c1c03800411080d602d0010603009a50425200c8600c880f0041c044840c81d903400c00c0030f103a540601c2ea0312500405001003403019503200400110310f580d00304001845211410034580080741051525204241482c19a1140c01007013545150381340340720340c0c001d001d0142041640c03100030359034a1380c440d8002141c190510020b40f020140d00d0100320240c4e060404090011507031404100c4407029805014802200c41f840c8401c0d01186001c1c002c0f49003c11741070160001c500380100640444405000204094903881d600c4030603640b80110064998000d00b000400361049050a0402c6035070041c00310300c0d2580c00102c084081c0005801c00040302d900003502d803a0030f4094401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 512502571 1250 512501321 512501333
    0x9180e0c0f04110d020306031b03030a030c11070e100510020307120201021608120a020a0f0813080703050a23090603060109050604260d02060c0f071a0601110606060a0507 75
    0x140c1c2c002e480c80075101080542204d0081c0d03000710b0040e14200c01b01c60502c03031104258a441e00d1894507050b095003050149100b0640203401a070040301050a10916070b1418174400351624445508c1101e412507a00180501e1341106a03442002d818190340701c203400300300d00c070010799070f8400c1c1c0720000d11940d400300c81d0241c110f200f0742c15510112900720721260050114201610725410020b0f00503103090000b0042200046603208580510300c00b81c80d5046070710319895060b56107035030040072043c4882d400c0d0000d00001d000342d001044424804c0d100e01c0d4950091441c0282909030a542215040799443c0c2c0c0c5030800c8544e802a152049411901c66903643d884a004841e0780021340d1005400040114011603184078040520703481d0102c840c40e882e00d82d03000010450382d403040002d032000540c02c07900200305602048801041c2c102100c008040c0703883c0e45940d80d820042c400890340f4400f10080300512250b0340c1e00840d00c041411006008100768100320000803018801c4104550900c5000100a410001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 512503821 1250 512502571 512502581
    0x702010b060a0e01021c090b0715092a0305100b011806020705030d05030f01060c051e0718090c140321030403082a030c070f0309180e0c0f04 62
    0x10250010380c031242c182601034060403030381410a000d8081c09114080b00c4c5051003028900002d079550f10003800d03250008044070790740116002e030307282060f50300c00781003840d464090f41c0589441800086410b50107840b8080e8003156030740c0300c05100b0651882c100b010410020740d000c04d0582c0c02c40000384058070540160340ca10782c07003e035040000c40c641c0720000d0070a40114588003103500690540e003501444e51021952448101c4008415840800040c01014400c2d0f0782003911501c01c50407200c50b504030a030210a004100703c0035100507030180d08188a900c4644041c00d0300a1b4001c041400031400c16078680304a01224010038060320400072400f502035400300b00d601c503540010910a0034480510040038455441110309801140300000440c0345a424622408045540c4805410541542948501743c41d07002074003441c8941b0381400702d403021515120710746603140d10a40700c00d03800794584000c01c004414520003003406140750061102c42c464012842d038000e0202143c0711940c8047d55400500244 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 512505071 1250 512503821 512503841
    0xb030c03060d051c1107031a0405010b15030103061b0206060108040327050901060504030f1104271b140108040614090d03060b0f220b0c010b0405012408070201 70
    0x201c1168032842194802410550300e1000907505ca01c01408140411503894a0502c4010310180148090540c9204070780c2c0401d401620900c000709103014204c000544071003042ea0310800b0020004010002c0000a100d61fa0070440d21444821030740000f180041d40b0390074010000d60503c0803100025041502c524400e161042c0c0e0a4004648160b1800c09007400d00f4160060a02035100d100000c0798584c00f6209640c1203951003040b40300008400e942d45201a640240c01c95001074603012400f06d08152080600740c405d803040c101c0f000c042c216050142100c04501e45c015014440f10a0038069500c080c0e456581209080c01c2150040c1c5540c5002d000400c1034118510480101406102003207501060301c0341c0240507558180042c0342c231103042ca02244a44441721007201c1007000703454840b91030b20201d9030346002c207100e40b00c1005a442c101e080030b0398021040c00d031480e55102d650003e545400d107e4a4050f000303103e10940c00003c40c010250986640b03450020601c403010700020b810034401d401400002c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 512506321 1250 512505071 512505073
    0xa06090e090c090915090a050717120a0806090a14010627080606090109060f06120b0301330305030405010804020a1208120109020a0c2406030f020f0a0b030c03060d05 73
    0x2e81343ca00d100a840e90007003411000c580030351030085803030014000340011165401c000600044c91602054118a1038204800e41040c050039001d4680070404101a000803906ca8803034162920749071341000100340c0001e00d440740c918036000700303505845011349116054034414104840001480310a1803607240c117680c2c0d080c00c10941044040b81440d130101d50103009907403d03640094143d884134659401c2d0b6445001d11001006160b00400025108030300703151942404807800101401c100000c2800d4481e02a451020501c00c04149540c401c0d401c1030820901c000f14900c2c9908074110b40e18981c0781e11071841010304000300c0001050940d918440c0300001000007441c00c10804d4514a0076503800d4025805840300586070b40000150804036000300c800d156050750b10080c9900003503540c002c580184a843c41100b10075070380c4452034001580300c2c0c0d40196000c0ca04004080740540f040140ca440d107406103600543d0716074403c006220440c2e003580d41010500a90680342e5861001060000c0344100c009002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 512507571 1250 512506321 512506339
    0x218090c07060203090114280b010e031b01110102090a030f14060a0509060c28050c0106180606090e1b09060f12060a051c060b0607200a06090e090c 65
    0xf5003101503000c019850301240000c0140d950350481c1c649070100d6104041c40b0380d605d103c0c5595409203603070b1101275050300504107540000042c0c4003084c0383c60070f500b0612560000c0c09150070718035130b00020044417203070356840254600031000b8081143c45000d80b1000740a019031a00140802010031401000410340343c0031181135190403020b22014250079110102d1502403e004209100c4a480403501c1241400c03007403030301c00e0794103114040b21180741007503c00400c1030078070041c2d442d82028060400200b501444004000350600c0402044034010340c041c0c0f0910007110b46c100007812070211040c2c0d01118001c0380302d442d0a60b051102d1014484e20581a51100000401e0f002450020015004d1184143c81500141e40d0b0042802004090b80c01342e075912082e16180015000106043c000c3c265124200114102e114080071461a40041e00c0c1140c220b104020300201c0e030702070000316801050049130909226407820340041c4c080c41050181e0716030000441b00254100008000004031201c0103000480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 512508821 1250 512507571 512507581
    0x150e132012030703030f060e0c16150606020f01051510050906040f0303080906060f0607110d050303010303261501170705030108010b040209060a0318080a0206040b0a0218090c07060203 81
    0x2d01d0360702c052800c40100e4508040c4c860003101a01c100b0054030741c03180c1000801e03180d1642c04031680c0c020740e40f640e914191072a070306400101014030a13400a41d0001001c1125810004017030b0501c80302c0d000c1c00046a15080c1006141d1410000e0303c044450141e500c20354014172110200d80700e100746c810281c0c000d007000030002a00780d4520341d4042281d001c0d42c0c44074600d0315030f80340c0b9944440c0d0540f43c01e5445100c2c405c5444442c6410001400b146114000360201c140c514070104041e1103503910280c56582002c030041051507007000702c4001c16140c1011076545c4071442840d200c2e580c034002e0080c0120f08504078440000382d00030304d40313240345900c070022a0841740307050100146103600c00d020383c0d08654209200c1044d0f5090500a441001034000c0c0079505202428a04400030040b10440140c400300f415881e1011940442c02040d2002c4154040c240914282c10b14bc0c03802170008d050500c3c164030400610303410482c0c007441c2c3c40201e0002c890882c02901c810b521f04a0030300407250050500d600c00000d001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 512510071 1250 512508821 512508823
    0x30a020c0906010c03020606010521010305010b0102062a1e0d0c0905030703110f0301020412030809070e01060f12060510090e061c15061503150e132012 67
    0x100c0100c00494050015903a04001110204a401c500501580c865400300e041980640c01034510701d1407095a01150702d00c0e03048009450802a801510a650340340761056207540d050002c02d602600d40c110048442120f10381e0b814034802840d168500c50500411110b1510740f5541e1413502c0101c00074136003920b4008482c0c0b030390020401007007190701041c0c101100103514100441ca0a04994105000e0b04c030f21824401030000301c0003180c69182d4155401c03c808104403601c1400c4a0301c5e14000d940e403c4040c9800a805403800e04c054105803104520f6600402a003036212041c4c1c20395600c42d01d410740740c000e4041c000401400513500010703480001c480346101c0c0107602ca00c500d412640c40424011994503410b050110344010400011181c028071300040010820120403000443c8800400141c4542e550010810ba100751a0300400080c2c0c07030700030300111000c450700c2001c042c4c10180440c1200341440b4101c503650100444000301240315515140c002405085180d01e08014054000c0103403049820f042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 512511321 1250 512510071 512510083
    0x709051e011b12200304090f061e0e0105040b28210501110c03030103120504030203010f1b030b030c100e1320030103050a06020c0a1a011715060d0311030a02 69
    0x403c000070102c08480038440b9400224200701d90309000a1032803c0c4c10032045001600c4841c02040c4055240d4400081d800300e10114031008012100d1107820b41810021400c10002c0181c0c0a90721840c00c01d09904100c0c1c1e240c001a6803040c02000c101e0b00c1c408100d070744500802000b5030050b0300e4842030004154a02205103800d44800d48180003c0015884441456289010341030f00359840c1e50051005200280304c0324400c011124039400d044c1d081c03550380e078002030954a805941c4407100d605c510392210603e8ac0d4200c011590103441c24180010107106010941c0ca04005801074801d882d00140030850034081c204040190750050490b0180c2001100c4280c06400046110900d05a4241c6c00003108003010050f82c0c1030707a5021000d40042d01540d00c0381c0300a5007144544154a015120300701000840004451461200c500040c507503541c9880d1400710314054801c029000c17500252007090001011040340ca5024604507208240c10607941022200e0001d078243c0102036101c0003c500a11a40029107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 512512571 1250 512511321 512511353
    0x60105011b0c060917030304050717070b030c09100e0d080f040f030f110a0303020309091b0307020a05010b030309010c02121905010f0c05070b15011214040b0709051e011b 75
    0x3a420702580b03170b03141c0c05540f44400c5502800c150003105062103000c8110034082c00702031b610b000722104151038841c804404c1d13109448808401400058074601ca00380008018800801c4d414062007590f54030002c51110a06054001d0107403000085e0617450500c8002641d02500505c1084880310303450f4944142c01f11803940003a14540a910580c0c040c0c1c0c43c0064151701665419030195081c440b4542c1880b5a005001e0b105d00c010902400200144803400009144100e00580c010070701c085690030200c0c01c582c0000d142074001c3c0c204000100307a6981003020041110360607140a95030080039a1070f103041844005400aa080c03aa001070800c0c0241500f000d0603005041d0810007403900b000006440314802e12000400d0070003604002440c810b00c2a4540680d080181400d4a031043c400c4406d00c1180c1400300c1d0340200d1401081403100344604d80040c0303035100840c1e0602e03c0708c4a0400c000940a100902a07070090805803051451182c0d02c6113070541035040c0180071a211401841c5080f00b80c420420003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 512513821 1250 512512571 512512589
    0x2060a060e06010f2114040c0b04150c1a0106050c0c060a120506030c0a0906030c050609061c06030c17060f04020a062003030408121305060105011b0c0609 68
    0x102190420301c0075800c40c010b1905842d6050404c0300150150307408004511088a03990b130002003820100070346e011390412600040c030707121030f54503003883c01ca009130340303076410254400710284000d1050b40300751003003405080e0700350906035101001c516140e00c0c900d4503103541c51402d0220000018044c1d030840e0140c16080c9410040d18131403208002405040c0c02110b40c94400208035059188500119034042c940016000d820703107801d0107003400450313407012041d0710441c2d446a54107006c009001801d01c8640c00b602d0100c0d440780c94040c812000515500944040c4035000c1500f0413400346040b4a03030f000000a6901510061240380c3e50100c00701d90001d10301c009100380c09000005041c61a00204441c407443d03008000c0304038130b410100d0441d044000182940c0c4010030b801b0088038040340030400707141b01d02d2040c44460b07070381d641c2c0c51401c8000043c06061000c01103541d0211000044000c01c000341950801c0c80c1a060401407040d0800340309901540207409101c8221010941c0d50b84420380f0320079554062 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 512515071 1250 512513821 512513831
    0x40e1005040309060305040c090e030712080a0b01081512030c160f080607080a020f04050303030f1005060a0c060c05070237030f08071109070216050612070807031b02060a 75
    0x910582c1500c0381247c005284549940b824002c80249502481c2203007840001c590504840350b850288459602c5503800203d1a024100140c0004902880c0350001c82841d000101e82801c00b071904039008190716842c468150704554100c2110104159621038900c181210302282d0900040c6121400a005039034007445c0b00c40c000300e207000000500340e000740e4040d0355078619540c825100700003e40126003c41c2c0740780f00c204800101550100082d50003000203034032030140d80c03d006081c9101d41c1d2041d4030282c0100014003140e1801504521100d5401350000000300d01c50b104414115601c1c0310b1550f0007075005160011050322040040e58006490100c0e0782c10840c81c0208501283c108045488000c000c0080e02102200147c0ca04015080852041c6400d01242d030f03611002401e0798004990400040c1d1041340d41940140803070713900c00c0042006a030000c1c42c080c040e071032160950000600307a5007031050700307004500079510135809070201440d80c0302c0c50440b9450a030b1000b5101c40054540d03007901400c01e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 512516321 1250 512515071 512515079
    0x7020a060507211e0302040f06030212130807030c0303060b040b030906010f0807091823010c03090b06040c0210051602071a07031b05030f0301090e010623040e1005040309 75
    0x520240f0200269440b084480c50200a00c0142c2007404014403007055003d010000d1480d40100c0385c04040c00664030056103a050080100412110041800003078145401c075031000b2039504022901d140c0e0b058908090805260b04081d805080349034403041003410001400958800c40b68040d60143c089007095900c0c0d660384030341c0c18100d400745000389401d0781c00510042001442c59489005d02100c005d02103907125541d0348800d5181000c80e01058100e1000d05c0c0040c0d82001d00388a0f40b500360b00369040410000002e51124061503500601d2a0700560742c034440048050300030401c100d18250550418005460103e00381c1b07e882a04060540161050f454085407220f2100a030180b01402c4800482c14101140c400f15261212070680d904001487c1c400d51011500a000410005a04e004076079500d52510440f101100d120566078001381c1d00d00b0000f400754004620800d01c1c06480d4040158402c03082d81d0004008000030718010b240e03803181c0091102c40786c80740c0d00400c0c482c1e4002e480e0300c80d040c2c0e91 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 512517571 1250 512516321 512516363
    0x5010b09010e061f0e0409140a0302010c1803080f0901050c0a03030204060f020703050a2d0f02010e0402030609010311060f12070818211207080f011202030307140307020a060507 78
    0x54040680820031170340d0303d100c02c0e041c00d9005086850250445502e2000282031403410560140d0742900140d45a85821495541281e0b402c4090744080142041691858684030110302030100c020b1041680002c2101250b807040094a01440c150015280041c1c1e06140180c029849445540041001c01c00c014507541d001107540e1003140d4000f005070044d1101543c401441544811105905414000b08200c0014141e98202115486080200c1581040d40009482c8100c1c0b002901d05c100c0c01001044030544a900d2800c3c1180d510034840c0350f6040800d40081c03294042d00c0442441c0f100301149500c4410180b03e501d50240b42c40307403030b10001c40d11803200c5103140c56014002030307600303520420300050402c80d0400100303415800314440504044d001c40310341050410541d80302000500101c02e0250030070580c2d4070340b8010015007182c040e5000729035000c6078513409034020280400c60458509403184c04c00707000700c0b84d01e99070042120320019100c68015116810038441901e120500d40440c04002030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 512518821 1250 512517571 512517619
    0x3032701020430120801060801090c02101509110301030605090a0c2c04060b040506030102040602070b0d0b0a0602060a050c16021309080a03020405011d01050906030405010b09010e06 80
    0x43e000d040303014035184800d8410581c0c4551058031103000744070a4a501082141055403081180341d80e42050350b502d844001040700c441a049003800ea4038100702c14000c2e0b600019441c03c81c0a2001d0086466041990804409681a4003140e903075414403a0649101700000029410b803441104104401e40700c0d0780d41541c0e5168a40b00c01400581d0307040050098845142e03260910782c41a03150a0b220312500d555902020800b941c1c00c0b150b41d601e40c100d0034030303d00d01030051035030100d000d41c0214145443e014000356111841e00c01d5841c10100041c0c8660980c2d101d412512007600e01900182e211359482c2c2c002503440310100d44110800d031414000c0b5003d80c004401316030081012010721800291980c080007100c29060b41025151a0744016550000d0700e00340240c800706003640c800603101d40c0b412002420f00211882c406017800d642d040c0c000016130f08801074070304001080d81c510751a6500c3d0b00c0c0c0b2702d0060050700041584072a60000010700c12040124240c485c540580343d2034110206d4006804042d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 512520071 1250 512518821 512518829
    0x2601060b0a091e030c0e04060b03010903050d0b150a030b0402091e03060709030503090108130515090c0303030c03010915030f0c1418010501050c1009110102390a08030327010204 78
    0x48801c5c0400c14600c0880030319802a0003501e0006120301c07500c00103401c50340749000480c0481c002281b03660ad0003100d8800d00382c800308281c44001200311a4600041c1c0c134410141c104060607503414400000340c1365541034404a150103040d914010b10006940c40b9038500c0700c1502c91283c4500c41c00155450710415070b210460303038084c00550400c800c05d801541c001c0301c0140881001001c203400320001c282c00700180003103408010410100750030040c0ca030500f000c00d140c04043c02035004001b440300f141004011681140c8404900140d03400c480a81141607160651018005080340d0030b03040309028601e03d02d84100c801701c1d200020000c958070103005000c1841e00546400703048540c0104601d5000c0c20080c00700700c0c0c0446c1030312003032070300000310408846d41c1d004140c7d803002c1c010450320250750701080320f00c050859650090201360902000071040c2c0c010152130360a00020722002858030703101c580001e0054029501529120301c0c1c00b1a400d01e4011883d0820707003007011003110401c0c40c003c061085409403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 512521321 1250 512520071 512520083
    0xc02030709053102040504060b04020310030c120218060f06040b120115080a0506040e010c020106030605130c0b0c070f0b0c100b030c06160209011d0108072601060b0a091e03 76
    0x40f0b0864080000615004000b698615104e25884c9110756071440214414042c2e100100403560850402d0003c3e6507140c2c00481c400d0742502201d00c0907960b41400050710a068003041c0c04c156a820011554054400c5a07854004402060128600d03172120040c0410140084104e4856a41d400140420220070349490002c2140b482c041165800ca58002d198001c00240004c41c00b14000c221503400c4400500c414401030f59603c01c14000c01155014964024102d42c81e49812002141c4442141845902c140000b0f414000f4111015140912101c002001d2041803c48000d0f65101c044440c1da010783d0240003640a00b0440140c0e0b00fa05218842c600c8030064002c00b2480b06001c03c2c0b042d6640010492500c501c000203403040142d07940b00c0da050291090200207544050140c021003016107041c0c1118040360080407003405200b01c0d0715a12848010b403c0840414030384a0113a42d80140302a42102e0f00c902c0001500c6581541c0109032601140c0f0041c003c82040051100d00c03584900450000801d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 512522571 1250 512521321 512521411
    0x604021008070c051002090f0d0203070b0a120606171e070e040e0a050309090a020c030703081306050c1306031814070b03040b0114010e09160c0203070905 68
    0xc01446112181e91211550402c400a940c0070b40751240f50031862042400f08940001c0e0017081402d151121040e000800e4400322000b808a07800291a200240240c40c051100071a102224912840110750040c0e18131404000f40d6880d001d00915002044a2100f203080c452008141c000c031400c1c8402e15113090791502a03040c0d840b1510200d55114040021950103511000e00e15626030003840103c071081d00c40c40c015540c60005070244503840800800182c0f43c40c0c810302c005020310f0808002c807061140d2519203140306070b40d0041c03c1a9a1000e01002070b011500d000d041119180042c6d000f00002e041d200300b6262501d9880c1803c4064a9450000754509140302c01428001049441c51031102202d02041c0c880740d50b200c1c074483d20b00c0d030011a01030341d508980ac0b004000400c920262400e40e03110a01e4190664a00880458805440903042c00310448601d810803086a00c5010001401d07070f8024180c0d02081d5640d114032024203c1134908224104030714940860380d054201c580006880003000da400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 512523821 1250 512522571 512522599
    0xc0f0905091f09050603061b0316050705030705071a0c120f121612140f06130f0b030c01030c02100507090f080d021507170c07061b020d02060402 64
    0x8a104025101c0b14040c0962a610300710448500150809011030030300000d41494000205850444040c0c04121040c1c482031400c003c006213401100d038400080c0e5924a0141c480510032180751040045c0a00b550101003148000c2000216241085031054180c0c0907031071040c000c11030790910500c0c00c60f00ca2a0301c204c04101c44811200c01410b031142070b003944903007840b90089562440980490b00a910460a00c030507000303042e00035102e4210304405100402c141d40c1480290543d0300c001605180e205190780d80021030560710103640702e490b001c0c20007050050741d04c44096000a1310800c2c803158880c3c003841c0d9881c0707441c0d4407901c64440c403110154000c0100900000c0e460002300707400384c0740404201140b080070594903400041c0000601d075003001042c0c000c00e070304002400e080c810100e00003080489420701c20300d03960010203017002c502c6142c034070851071302d441003c00c0d014810003c004003102d08100d07900d144c0301c0d2203240c2c4810301d1500381c080c0c40c2029504030313007207880d040e040398000d500c000c0c100e59000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 512525071 1250 512523821 512523829
    0x3f0705040504020f030307140d0801060905010305090f250e130b07020c0916031a090c0d020403060c030912020a030f030b010c0b0f0117120f2a0705040c0f0905 70
    0x180c2c20a00240144900d0304250000c80d0656121790400d441400c441e1a00323412080c820050f4880c00400c0d4600341d1000e50425034021714800c8241309141c101038940f400f24110f58018010082040c500c03001b20b540740701e544088101c05030140c05050304100042c030000681d25140c03100c190b00c500011004c80d220b50140e66158035030b02d880a00303408114460554405015217800c0300380d07802030102000c441c003051000d040041c1556045a61002c40e400000403102c00754031080b0b1134076008100d003c5526110661200554002c0c012030380060484c0f0f0600c41c00c540078030303010761146407003074018400c107600d08000001c1a0780d60f00700c04400a000800b0341088008061180e400b40841ca101450005448801903d403800c04480c00d88144c10002c1000b4010401942c806c0181c00b000b104a40c09002c450380540e82da03600034001c0040d0303200611b000062804106100078089100060040c4140c00303080868141a07640b5190386c000c00e0300861074440c50041c0507001d80d900c1c00500c0c0b00b81d40c560750103c0c2040140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 512526321 1250 512525071 512525081
    0x106030c090908040b040806010302131b050a12110a030b03030310090f110d270b041202010b030f0d0e01140d09051c020a050610051503070e3f070504 66
    0x90303c0100090002080c00700300720740140001d050702401000fa6504500402c0004150800c0402ca018500714100c60342000500041d8280c00d4181082601c8145641c07040d0b80c1402c9a07d40482c01c0c525052550790f5071803064004d060f8400b1266070402100401d40d0500d40d4078030060321001e08440451030100036a1505422151000c0008000460425041504c403804d5070401250b00d800780d078941c81e1100c03800ca0401ca004408004a0a036180001110345450000000140016108806c460852010b8600035080b4114031302c2c0140c12a0b10052070f1041890312803290317450440004a01c00c0c0c40400365889400806607185603c180304d85046101900c117402401d410b20111403274041c2441c00c4160714180e014450500040f90050000d0202c180752480c1803400052000350000c2c021502840030703444104001c14842e985800840d0b9030344032181c0503180d10044012188d441000032554814525040358200741e00c81c1d40c5010781002d414001108600350f00744c0b0720b481440342e000318400c01c2940b410340c201c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 512527571 1250 512526321 512526323
    0x31a0c2538100e0708040b0603070b0909270304171b0402070c0b0a1805041a060705070e0103030f030c0305010320010309140f060903070b13210306080c030106030c0909 74
    0xd40c0b610290340c0e020043c80d42c80b00301c6482c40800c104000300000d011a003046503911240841c003400d403450408080c441c482c010303000568018000600041c3c040707100b03420609115103031a00f25a01001605080a5817130b401800b0351501c45101e07105007250f4010004034800300d11400c44c1480480380340c0300b00f0300009400402043e0b0b50b00a0b004c0c0c00140c600d03101c1000b0701038035026503990880d020030900280c0c01080c443c8e1045005904c1c10b984ae007a0b20394141c0500480585c21100d45a40d40491304001c4c5ca81803150b04804000b00b0f082000208064002091440c0004503450500484084a4058086880034800906428a0b0b0043d500d00748210009409000c4014100050f0383c004071b803500b0002100b444000802c03940000d03034442c4544000c10070194405584401146003085039a50803c030550040c0502114917608038103601000382c0a10181030140429031104e09241401700e00030b0240c43e40340701c0c1c1c032618010041c262031181010b00589041d6078100031a03880b083e20301800d00700100178080c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 512528821 1250 512527571 512527591
    0x50a030308131b0f06020309090103030302071a0c09040506010315090507030e010216140d1d01030f09060501050a0506040605030c030c041a0d0510031a0c2538 70
    0xa0001a401c0304080340111043c14049425401d150b0704152071442074100d4425036000b40040b000c07550765036030b000f410b40740c0c50f02d800b41c2c0701c0b025032a00c0d24124455010942c0104907038400c218200017500d000e00030380d40003200d09004c40c0e2690b1006400301c0340d002500700725201c0c01d00350a100c00034183c1c0105810802920b000510b07070b03890201003400c82e00640050076446400c1081d40f01445640c001806901c900003000c1e00c1c0043c0c1180e4003400c103414110843c4d107010f16a80801400d60301991001c2540036907541c00b80820034035803400800408090049500c2284003103c04251400c4c408150b400b6100300703403111440d548444911445903040140100c51160702002302060942102c500b4682c5200d000d100c66403900c1b103003140c0c5402e03204020200c00204c2001c440070800326000c0020722208801401282d01141c503000606185e5110b1080c1403030011000010b080d50500c0520b084590060080b040191b440348007984802e00350711100d00740c051038090800c5120000c04822a11030b00880703660 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 512530071 1250 512528821 512528851
    0xb03041212060f030210080601081618060503090f0d02150a090f0b15060702060a030b0d0c1d01080a030f2109120e0d050325051903020f07050a030308 66
    0x2182841602c1140d000b49141088000c0e00f00114140703840408403d9140b401c01640c20300e06980000d00407040100700100d8180d80e0303d50620b4140c0030b20340d500c0419000350715080c2e03900c5d100e800c094130990041c0c80030452446400e082407094400400c188080d1030059015045a840050304503900850190403800040d60300d441c01000680c161000d500703414410b004825092030f04c0c07150090641d18504415010ba10100259401a51060202c40441d001030400140c800b890102003407151100f036200400c00d100080021030b00040300882d0a000040b600c01210041c3c0e26440c0c502e440e015001d00080102d5500d20449080364007640011521035144140324094030842d80948041d9140c401c0c0a4030079054050045600c3d95204d0241145024183d500c0840c1e2045507490fa0b50320310600e036890400282d24502248610001ca419500e13464001c8122003668001c0b00c50320000852a800c02c402510030802840c007100c5011070f295044800050480f0310652868900b51044d07540205201e01c580809 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 512531321 1250 512530071 512530097
    0x7141c0521090a05100b03030f0c19030504091a0d02040b0d1208180606031203061302070c080c0a030c0909021f170702030408190515010605090a050a0b030412 70
    0x81080305100342d5640340102516042c2e400c249003002c4103000e4101c1140c1c18000e40031003a84001003200c4101c0b407401850396450512244580c10840588803808003100103210400502d80d22a02810598401070400c0080c000900ca421016141c14401147c100194003039801c05494141e01000300402c0260650b403651a072903031003020010611f0000004941c1c842c061100038680c038020121819140350007810300781402d40c0025950941e60304240100d4800200081080d02c030410915040c4e60551003c1d51205154602546042c5003402401c81c00d1043c2e5a840305649801c1d030648007100d0704004100307403031030400c2d04030300240000c080c0980e08440c01c070f50500400c1d4141250181d03500c90030b603528501c0e0f40340240400c10301d07403000d400c140c2194000c2c007050100d10340100d03414200b0540003106e010159a90310303010381030181102c41455048418400007460382e810500400344e0760030407205142c0650320b0340200081c0485501a071812603d06000203000617104c6000b107541d24441c0c1c2000401c0000c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 512532571 1250 512531321 512531377
    0x1c2d020c030601090609050a0e1504021207121101081b0d110d0203070f0201020f090f150a020708010b1e06030a0912020f0f07050d0b040c0306020f07141c05 69
    0x4203a01c13511900c3c4c1d42d82d00411086460303225583c0c108a1426060200041088500380d81702500c1108805076603444011604558640348140801407480042d10040759640081891180310100300f036070904070481201c1350035031003444414070501c6920904240d141c150552440700b030b006035952500e035aa40d0448540019400400b070b10f00400c083d400980d582c500042c2c000e1410541d4000d0701c095a005101c031460500b1450305907040c0200540b54510007010440010350910400c40e21150484400100310040300e43c00300320042543d004400902001c52100d050203c85070082403240c112007000302804001d86001d4000b5600b0104008000c540c1100d81c3c6c441710208801e1420320401360b0b0091450341602c0c402070143c1004000c1c80c0300505015803900000c10280098001c000b40f0200340b80c030000f000c000380601604091070700b041d400c54031140b0350340c000031a69010031420303a105034600300000944100021340002c1d45100c000c0300540b41c030309004141c070590410184030b2100d0034010321000709005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 512533821 1250 512532571 512532583
    0x1008010204090f0e0c0906060702180a06210c0603020307020f010c02030a0216180b011b1a1f05041d01020d14010806010b04050d02041803021c2d020c03 67
    0x42d0000000f10f03d1041c44104080710400c1c03d00034801c0c1c00c05440802d40340d0392042551340c80102030f901160390307510034400211040300403c03040200c010244c003401040d800300d40c4100199020349102200084548100c5e854540021302c0050142041040500c0300620940142d40c01c0a0a80125900050b09020190a46405041003070060f1310100c0c03090426581000400150003800d00100d65441c20004100c03000d04420140222803912600c40e00d00d26441480d8145041c0040889158900e00e075281001410050510030007003071650101088100b66400c0144c0500c07440352a689284a02e0601440003900610344c140c00404500d42c2caa0118400a000030704040f09841800030300c4580e180211410800103030483d20706a1f0117500184400305a42017107170241c5004032101031085010b131002402402c003540002a03943c0850305480d007095000a850104c0150f400d882030b007036540c140300480c1e481f042c10b800e1440d01054804120510944100b2184803440315205882040a002003c245094 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 512535071 1250 512533821 512533829
    0xa030f0b12060a1104061b02010207170616030212040f0809040e01020409050709032006250201021015170708030a021f0b090a0b03070e1603060905070203121008010204 74
    0x1410100c00c1010709a036500c01c480081a85000c1542000d003000c1b00146514000c0354a206503101c120303a440b080da030082140ca001000d80d41200c500d00d0301540b40f1180c980100361210759410000c900c01e040340380c1c000d000b0381c0c000802c800c1800d400d6548a8a440099208940b070035100c0c2502040b0500080e1114000d00c0d001c1401500090b030348501d09510401107540081c111410081194000e01c006402c940034a001401c3d401c90b801c0d8600c1440c0c0029556100c0d201c40c0c80c1c2481071152584086990440030700780c0080c000d809032820b80c03e01220200948000309400302c906106104240502862074040306008a9001d0894802a44a03241c5501e150f000050345000759001c0030100407010f69030781410300e0851034000180100210031003c51281c40c80600281911a16404400790f03584003085403030020600e14202c0b002605000c042d80c0c140c450a5030750140081d09086000c00c105d41c141c0210f40c0070b81e074075074011407500300c14080200e0031803800307800da914186228078002220402400648050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 512536321 1250 512535071 512535073
    0x11071109150603070302040f0807030506160318141e1905010207020a0905090f0a05120d022214030a080a0507020a0905041a071805010e0d0215032a0a030f0b12 70
    0x46080a15585203259030789d2003400030740c0c0301200500c0051000b040086c0c000c0d0403060701d40340300310b41c3d11016000340004012010401d088148108240508610000d01c0040321009a480d62681c44407142400e5200c00609a420b510503440c4c185100d0003c1c1010120354084d20005060403540d9000910a040941c810060b5030f45810a020100c2c405004c2d1851081628004250080080c0d40d078075202e011140c18800c040e1804503086191100c3c0743c0490ba0800c0d80300440008681600080400700f00160050740b04202d0705440035110fa0800088040d03000d900082c0c0c0743c1c240320004400b150113500c500001ca8001464400024101215010f0070b80200c4c410041c0c00314034020103d01c6220300b0700041c200020404a1030681c21440202400981610420b10704042202c440c0c40100307c0125400714001d420006901c1c6200480c61403c1c080c5004241e62005c011065141d000c3d103030030303040421000c0e805405082203400030050280d0b111131141c2c411003c0100b030b51640a8005000740074010400c90039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 512537571 1250 512536321 512536327
    0x1b010c0b09030a080c070c15090302042d020901090e0403090b030709050f010f0e010c0c0f060905120705030312090a020a091d060108070603020c03130f030611071109150603070302 79
    0x2e1150014134485e1301001c1301d42d0b43c030f040040302e071200c0501a1061140288800e040c03010301c82803521400c1d000c009180c0150003408280114a03515103500800c3c2e48902540c0e000e40c205850205190088440341b0780140e5a41c070800d0b0030311840c100440000703841103041c00aa03070740008080c21100055840f440d12070b291940418a04018442801c10300c00801341008044034101662503000360302d4685644003032070071030700f02d820b10300d040d000d81202904001c0c04c840c403200001031000d43c0604094145d03003080d5145141c00304940d03241c40d40c8032040e0080e10f038190400c0c0103c00501c0c0000030402d034403100b01c80442d01c0c0008160080388006c1401e8014040458945240c90314509044503402d880721b0068005252540c5000c08064030750249015120805400003140002454200281c03480c0090f03a464498815595003d11262540a40300031500d0900b0300e50b50103a00540d0308141c40c107185d04500100c00390886001040202c50008107000070303000b030115603000503480b180040c40c4561015100181d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 512538821 1250 512537571 512537587
    0x90305010b040b09011401031e0c1107080d080709120f110906100323090609070b090603010501030c02030d06090e0705040e0a0224030702061b0a021b010c0b0903 71
    0x10070740d052106180d02403410100f14071078503140d40c026141100d03080c0b50000010411800100c02500f64481c0d000ea048403445134122881c14198415480c0740c0503500c601c0c69880d4000511905c41c04148101901c0790041aa0040b0807405019125800306092500c216040e40320038824403184001c14081da44800c10f051500708119402c80d100c1c40c040012520440c0758500031001541e0b404680b000003040546400585194403814070510704c0c1803411500344041842d1009810307548000032151001c03184107200303001034060107803c00c0f07840b5140050005440d6070b003820019000380c04100b40d401c0440c4010041c40b10011018425180941800280403511a4120000c1c524111581c0c101a2186161110000b868180041c102800c198103450854014802c4001141c201c2400100003280e540e00004005480707901142284c8a0744140924000c40c0403802248015070003103031300c1c0740301590140c0c090207030300c0d4560758580c20440c205140040303e40368980d0b1118074a0b0000e0b00e510201d81d0000c02e00c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 512540071 1250 512538821 512538823
    0xc270a02040626160c050102030a02031501081b0a110318031b01120905070f03030c03021e0a020d17070609060b0f0a270c02100c0519082203090305 65
    0x11095401c108107a000d00e05282503c025185015210b06070020000e1000d084850103010369040954209008545038944502c01700044e43c012500c00780d09110030101d2541c02d41c0941d104078010002c040d58062940c49608441c0103139070110f448102032154203903110707030a0341082008210812600c2446024406107400341482c0105007001901040425600103002d0390340304078450f0010300d000501140c2c04415003052410088160807200e0320f484440320200c141034000c3c00310000203100341e00716140c01c00201e000c0c1010f481950800e4640f600000030741d40141c60581f040c41c5200c3c0c0110b254903c5801844070360303c043d901070541100d600b40c0325101ca905008203071142645107401030360140050340c1400c0c00500b1041c86801140e0791040706141d0521040e100c0c4105100034151584200710070300c14074034080d44c0c50045070b500c0d80802c0d040400024420b0b03c0344c1c0c01c1d10b0000a4081d980000c59141c07800507104001d004041c410aa10082c008042c0c0342c00340340e100403c280c060389485203518154203080e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 512541321 1250 512540071 512540087
    0x61e1b03050c1206040b090103050601062601030209091e0a0201030509070e04020d080705010603060207060f09030e0105071707080a0207091b0302070501090b090705040b120c270a020406 82
    0x800103061810040200c250b00c0002251483d203e82482032401e65600c0303000600070b2481d405401e8100c04010004410084001103150607070f070007900c03000c0000c44a03640000d0140403121004a0407d80c0000410050604452045d00016150140d8901c413814404110398490b40c40b40ba00c3d03099203c00382210944d41c15116594004c038092014120035030074448800d42c2a0030181000740924a0201c9240c14055003d040d203e00c96480002401100d550f4282003000c1d4000a0040d0b840620740080d803454032030180310301c0c001d060380740d00d0700d81003035800e00015030302c4d074024a07000e50303244e03140c00180041c1d1040d8800074005d441c0f04803405611a03a4120000b4640f484942005040340c0c589072191000f0320302a25a608030b2403017450090381c4c5440e18a8501d001d40f40f4204010400d0f486d4005111420b44045100019182d007603030200440741c00342082028100712070807148090b800200400c3c24038100070051031031a02c09140260030101031104602d0142404031355195403130f41e01080500c009a27001540c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 512542571 1250 512541321 512541371
    0x402090d03050d2f030403050c01060e1e070801092004081b0307030f02060f0415171b04090f06170a05011a092a07200a030b0112061e 59
    0xf0480e105501d5100201c401c803800c022203130100c0001c081611400403180a804041c000b4403501da5246444c0c00e1401041c4e80c0b00704145122005ca4004448419002d8800c24155461010603481c00a80f1002010034115440380b034058051304124941041c001000180310700d0008184807480800d80d071049031181000203200c0d402c1500100081030b09401903145d62a0115072459079004c1e00d90b000307501c5100390303408940c02044130020054410f820021410f2500030480a00c42965103a00c0000b140d140a0b001c0004101801e00c010b000c080f6655001e0988202121800910781703442d2403142c008038107111b1007800c45070301401a0074108442805000c00c000c0a2600f541c1001d074144000070071305030b8010075642c0070780e120102d03803601300c00c420844a42c5900440b5515076580070506103440130040f0702217904840214907102d50030700e007825004603080300c3c2c10619040b580d03400e02c0011010042d840c0d4007610300700c1c1c8400c000c00000440100da041100000880001c6078240295078505c15400d001e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 512543821 1250 512542571 512542601
    0xc04060e0f010509071d0402040e010806040b090705010f18030813151e230408160509250327021c03050a030e070308030705090316180203060402090d03050d 69
    0x380005d094204900e6040f000060813000c0040f1100e0020a00a00680e0301030b00340703558036100010303681e000800c50601403402211804030f6642c0d1500401d940380020300c5180d0014880c00c4000b24a031344510000b0102c0c01e00c601843c1059560b13921150080d82101e08ac5503000c2d2050182040364070207240c1c04e4005021241041da00b0340d00362885031100d01b5001c04946041c401400b14140c42074016800444860000380740103038842d0349034050380743e5800000f4a00d50740300b00e000c0400f241318a4100126440f84e03110707400400d14cd036851100800d295a0112411050503214075440c02c22911040507951050240700005608030410f004010465450f100314803c815100245c10303011981c4181190f0011f4901c0c10042422040510f0706442c0104940c0b000d0480340c008420b02c13072001d80c054001e180c031000071000c03a4500300840d080040105264072503521494080050f1009850294000d543c0c0140000c00041c2040c06480c04a5010010a40c080f80051030005005010400c2031040b1402189101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 512545071 1250 512543821 512543839
    0x18091c03050f010504020304020d0b01090e1009050705010c031803030e10050307090509070e150a230d0b06190903030f0e0906040f0b060408070f092a020c04060e0f0105 74
    0x80d03002e449038079040c003525000b0b0350008001019520790039141403400e82d00c4248000c4540e981c024500091480c1031507070b9114040e4420519035584540101e0307081c00e03004005440341511b0710300103440c04c0302851801c6003072043c03e26007881d196014081820003540652290041c10520344208445800c0c044071120622400788140203031241c4c0301c2403600c15203106613200b000d40e80303035440300703481540b079603255603610001c54140380040b00c0701ca2014100d02d20150315001550000fa0040855800c034070203501c1502c51007440080380360203180c2c011030403104018158078500080c1c1101c1c0040e10f448084010040780741c0b01c00070003c25038440c1040300c40351640e2420000482446e800142d0042c40a0801c91003280c480f40c2e01d000e00ba8240d8804040e4000c01005259150703962481079440760402e22442001c117400410002e100c09040c09100070f0034000d1220100d0094400c090548000d18100d007030011071040401100c1107480e2449550f0182910f18800c0c441c500c3c02030030014203807030140c002038014a030300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 512546321 1250 512545071 512545081
    0xa0803090d14180604051e041107030210020901180806101a070605060402040f290703090e100806090c0405060a0302010e0d110d03031406010c0209070e18091c0305 72
    0xc40162601030500f4004000303c2a560400034503c0c0c080e580109a00658030425000900d40361200b1025860042c0c50500ca200506014080d5a01411704d024015800c54604500f0410160f40248070002050504100c103c1d10b1a603040c0c2d620002da001000c16a010340c041c400ca010f00d80a005004003c03607415101d00d00e03401c15494030640070307074040100280d440f0004a03003e0b0352241c054074080c0c8a03100411a600342d41e422510034440360054904000340c8100902e40c030300c00c43c1001701c88081c0d8068580d019103a24001402e0718900d802081210030b034890400120b4918402e000b02c5018248480040c480107131a1010001200c1d03029110505c1075070808002c01c0180d030072107003203685440c0441d48040120141d04091514540004501d0307032080145903648e0825400d58000500780548107000350b880c2d51100015900441c0c5000043d500448020000722498405c840c585c90054014003050310529070000728418140b801c0d920421aa0440320241e038100d5008110f045c4400210309e01401a070401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 512547571 1250 512546321 512546357
    0x20a080708100510110c1225031e0201021f0510140907082205010606032d05070c060911090603030f12040201090b0d0506120a0309180e0a0803090d 65
    0x1110301104c050002502c000d00030200107100740c090b1a003010344020704603904991216118040101c202001070300c0f82d100710408401108003101070f00c5c0e10451001c5200800035041ea08c1c040c1c2e00904034118445c11914080100d0a014000840d0000300d6001c21182404030b01d210742542aa080345505c200c0b41c1a50541c20768602154581101450400c00040c0c5c9540000d0204046040400c0c010441c54a400d0780403c00154013840c104c600c0e0b07903410410b2907840280342a044a0010100c21003d404440030007240c00396070b2119030806030606112003a00070a50341e0f030041da8045c40064031603079008101c0c5281800c01c40803450303010008034061031504031a289804254019900c40940a2a9000c0082e0843e4001d00c001000707001c0c02410a500c541c01c120740c810103424116021801801ca0310003480c2207203030000b40440490b91540340d2001c020700341041c10450492101303185141c142c51310642032075030409112620000303003c1c80d9070586c1c0780307800f000042c6018000700d115000c1105035801841035400f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 512548821 1250 512547571 512547589
    0xf020d1a1e040509011d0615040501030f03080a150e010f0e0603070608060d06051501020724180f030f11190b0702010314180f06070f140d020a0807081005 68
    0x1002c680001d4141c0300d2803402401080d41c00810320640031800c0015040b028000781061080500c0c80a000300e0f95100b00030300042d01c000780300040000c4c11449564000a00555020340d218504000005076052001003904080e401d81d0b1144030206101801030007000040c000030000380800c001e85412030304000011968448003849404108104140801d40968900d03520401054100301300344464144000303414910b0f0010304a103405449180400111003c2012401c0d80c001135001281300c16995012041c0c400e108002c0b0b28010500d0701c010b001c1480c0785100e82003c0554041c00002c0d0070912580b40007440c0c12860034520b072007034216111014120180c000e500c426910034a0030b954503a030346480141c2c080d089030403114001900403010000c80210f880700b06800c40d510207040300e10130800100300c6926518180c1c0c0080c0041d0b10001041a80e42c065180404200401c240b014030348056850108102e0700f203415440002003c403804d01004aa04c510f4940e040001000301d680c42920700000103000704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 512550071 1250 512548821 512548879
    0x4020a050712020c03030f0a021510140a090c090e1003020d0210020f0f0d021908090402030408041203020606012607110a060e0c0306090706050403060b040f020d1a 72
    0x1034448105090b034802d204c0c880404d0009002c0300c0d141c4000706405009500407031881d50041c4103c00700401c260300000d5416020712200c401511407107091000d021384c0020107690b0180c100c0d00803400044c1e1000c891140c00030800481c1c5d02c0207619400c28030b2840c0f024101070482d0f110002704580078030260765034050204510382e04803504612007161200507810641d411090480e0b07402000c03c2009507900c04104074a01100c0e0750f0076120750030400d00541168a8000d01d01412489003400b200741c0d981081e600070f5030803074004ea160078140f583e20070850301081d4440e2401c60040c1c00480a00ca900d581008500d41071101b048242d20700c0d60b03100380b800041a4001018141009880241484212028042140072903003002d818412001d4002a480c0d03501c0c02d0140490080c46060009210640040341c0d400a880455850f94500342c950b031a0800078040c1303010041c0d8440d69070b04017440740f22042e10061139980d01d207042c08125a00c0003284000305040c0c1400d0180151800d03503503203d4880210782d25030449 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 512551321 1250 512550071 512550083
    0x10020c0103021809041506060f0203090d0f02060c0c090a09030c1212111c060f0e330114032215050408070b010816090509120a030c0e04020a0507 64
    0x1c0d10301201803510304800b0148650300001340d1018003040c440080c1c403403002510b40d0340041c8081940c0c1e00c401c84400e8009900c0b40f0068005003c5010946040e14050381080d00828a0220905240c0c00107142c40d030041b140f45605034005c0540b506181010f8003405d40c400d91802c0300b0003102c031554601078916501804001c207e050313186198240d06008002d074040700031925504102c4001c00c2003000e00343d40c2c004007407041e1080c0c80d17000c001d441c031005010343c0054a07049442580041d142002030302180c000609145c1d28010f54403018a5502c22902d81c0110b0450041065418102180005802d56005400d003500211b002c0040250012440c200c045002084420421102c03510307081c04681c03044490003100c1107a00300002d00c014861400b01070311509001c2c0700e00c20744590740d40c00381e25528415030700c0007415118500340070081d050f8207038010b59012101100b43d840c040c900005111380d90b0300c4110000d0120b0380d02c47c40b000905510041400381c0e220117a030b085150405441c000341003401000c000500c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 512552571 1250 512551321 512551327
    0x3030507020d3e0106090510080a03051605150601080f090c060a0c0b0406381309060606050c39010212040303080a05070c02010827060f0406060510020c010302 70
    0x904280e2160f915400019140d030321542190580301a80a02518462500154100b10100704200026890a4122128030004040e0307403d0135513081d910750708240354020500440000500c08203005001c4060620440700408155107452400944102c0d00a4007001c400c540740740400018000024000b00662030071102c09895600140e4101c030f0700c290b0804000d043c1d00b0301d5011300c010010075410010412001c04003401807035034100440c0c804150008003880601b00c902e0360b6440d00c3e0601307a14a58424a1041020550340c1407030300c44000b41c0305541c3c003000000b84001664828048140590500014452280e00c0b800703460041484a004001100c510100d02103a8007032039982c000c2280030b1020140d0304200c5c1d00c8599904003d44005030440d40c48544078240310002d02282d2148074602e4400e5416103403424503444100d06540440b01304034821403460080c28040b9000d0b1000c0008510079400030066130032902e090b242070070031b6541e91307440140114842880d848006401040c4144c6101e0f003840d0040e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 512553821 1250 512552571 512552627
    0x10c091412030c0706020111071505070e0303030f010303020124050f041401150207050604030b0f0415090605060f0a0b0f07060617010b0a0608190b12010e0a03030507020d 75
    0x361030318061400d80e0291000103084803504001041000844081b900204080000070015220500c1010401003041c040148841851262030703110716040001440c01000f1500d40c00003203841c5030300c00e0380c03000100844034004000b0154240140c0c10110000541c2e1142603400071140090b980fa41c0c01500d00c900c0700707000032034615101ea034804049803040342071322082ca5944640000c0a4001c410700840140a001340204460030400202c2d4112544a011800e02e42c0d1848664140079101401c110794055020110a840c944c0601a100486000e140001030178149002084480c1100d0340c1240e014192403102000709508680c19200ca58080c03ca40d542d40e8501c03840c00c840102102e07008102c084807001e040c00c2d0566815801442190001d40c0d40e681201d07103503c0160350326032044510b40300c071044103400003000740c40c00d40244031800c10140c844102040e941ca2160f003911101c401948455110048650038503505004230358101d182070010b0401d00908510042c0860300302443c8041075000355024803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 512555071 1250 512553821 512553829
    0x6052403150301020304030c050712030818010e010501080304170d021c02160b0909090106050913022413090b010c0623100f081903030c05040905100e0108010c0914 72
    0x754032580100215503d02c1c0900c0c000d03110880d445400d58984c03040070004583c04004030316131003001780c0503140c580c140d41d034603200b9001c0c481d8624610b410b1552101000210b454090150720f0280c4440400703980c0ba03a0a00002089210007121030b4080d650003107000d8144260041582600b60b60740e16030707007082480d180324260324005092005004000110100040c01c0344104040c211000c0106c0d0100303180e071a000d902d5402e031101805041d0b03001c030050012481c60141c01b0540000315101030400891008042c40080c01c001400c90750310104400014400890406d030302581e00503080410041018058984c0000c0c007602c2a514000c01c001c1d5139184600b244c6041002041c102020030042d03850514002402c81d041d800c0f28030031142000600380f03002c28201c5001c1183e40c2c500c066000b00c207440403000d0700c00310041d0424440e000e060100800010035079990500410b48129032000d1101c1d02c2c1032514a1a0a030510140d0014500380d01d0718005110140c1d006c0c0c039500894941c590101c0840340000700003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 512556321 1250 512555071 512555101
    0xf0307052a010c110a02030607081f0902040302100207030507210b070216050102071208030a060e01080705151204060b13020c01140c19050a0e04060e040606052403 72
    0x462030340a1500ea9001441c0e054020001e004010740d5500c0f0b5404c500081641e171841208002541900443c1c00200d550b44544582176000180c001c0040b411550780e1a001000d05154009445003900000c0a00550034442000d042115940c4004c001840c9186c980d240c0f1745519000340126051181c0c0b12005c400a4805941c003039035049480c02415040035400607503116002c01c1a59007052074243c001800d0f40c0003280000448000c10004103403e0b20310382e44c0103107070303400180f0100d661640c445000c1860001c820180c0e000e0011000200036140c1130100300008045d245102c0301500408008210040c4a5401e4054016601000125118203094005091622000b40c4024040d202140b092082d40e0f054110001000903146880340c2038590320360358100b83c443e10002000c00c207a42c400c1c0460311031040000380481c9090707181c0303100e21100c0350300018203649140e840520b00c5840401844140907052040200802c4211524840d2000e504441a0491410b5260401d2000c001c000100c00f00545ca8075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 512557571 1250 512556321 512556367
    0x10080a05060a3c05060301060b040603020705010207050a24020f0d0c02010e160314031812070f06031a03070302101b0b0f07120b130507020a0c08010c03110f030705 72
    0x48030b945041940f04242c585140003490214444c14240070030803a0606104560035150180c01c414601418400158040e52102d481110150340c01c01a2101003002408540c00c01c501c11146603255091840c10301d00c50001d030400c0c1c220914810003400d00800d003204111a95254400780100c1c4102d4018402ea0041c510801d50300c40c54004c04d9100415440701041030020b803446001c104500c00c10141000e130b528021000b1058604e610250400c0031842c1545044401d801d11000f120f486a407503040c00038821002d036001001203900d03100381c0c001d02100040c000000502c182c0080035450314580008a0891010129400b40070704074803c10103407007200395203851264011a05030300034180385502c180e560004580610001e90fa01000400295150007480c8030001300601d14415041015100d000516000d0300a4041d4412880c0100002d41e42d03903806001810309000001d01c5400554001e400d0300c419a48004031441c0400c6141011007038041a40d412044501d4916111414140c00e0101a0802c2032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 512558821 1250 512557571 512557631
    0x12220b130b07120f0905071a1303121b050c06030c0c0307080c010501060c080304080912151005030c15090109181a01050304020609040506041107030810080a05060a 72
    0xc100010990880310240300940c64060030000c2401400a050031145078005c020300c580c020340003c105000807100503040030074185080a141c003640b0541883e908103e076000700e598599140e01d105880b038200a4210504583c10811220b0301c1c40c9554082c0c840602c038003070380e03c917240100200c0c0c0c070815003000746c2d0f841040603800c0380e0307455030302d41003003141d9411144204025608160011910601c2040320030b100382d40c0242240d003541c0740c50360f6840040c0c006480c0d19800c0403110340f41c1d800b0400c04000c00c107041d203000d004070400c4c2c0c00d1842e40c96007075548540010b4042c3d48200d2020002c2d842c0e450307030902c00207075100070191031340c000e40d0040703502c604603500080404103018041e060110041d40301c1480403440307040f00441c5941c400010350300d030f01049070060b50150f0f06020b80f03555410326400442d0310a030010f000080b45c0007540c5024003150041001030f00052114420040c0403281c80e0724001c06000400c006000c08480c6644942c1e45550041004039a151285a001c40001007001c20110a1400d03078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 512560071 1250 512558821 512558843
    0x31e0e0d0c09110f0304030f02160b031e0c0d0e01060302060a0207060e010c020a0306020c0a060f090b01051903240203191d06060409030e030a050312220b13 69
    0x1080441c1480e08501814000520b001d03c2000d103006807038100e0301c010001d00902d074155501c6450a031604200000444190300440109015000c1c0d0070038208003924081d44035a03164100b000f88070800400782c0c10310300a41c00c220341c184480c00e00c4c910180e56880201d8100481c8c6200d00a8041e4050100390380003e4005070041100c1510750b801107000c0e8280c03195607a4280240c10074800444e26842c3c00310010f900845140c10034008030b20300ba0000e241b0865507e00b100d5180019541354021280d081c1c0600f00f07542d0b5144020400c10a841c0030880c010315040390000300c030032400d202e8111101000d00c002000c030300c604ca4091601050182c24240c04204c0d04800b10340300c2c0b9200c1170242e90503040c15032552001e0725200d0340c0d40084800700120b242c1410600300918031603580c9005c0c07000030400c0131400d0b802e00407814820321282c2c1e41080400900c0d07201b50b024541b9010071091901e002d80c00540000c03410051414054440600d505000403515004144101c2c1c50300c82c41c00704001d500003580b02909410200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 512561321 1250 512560071 512560073
    0x605031002070b071403010501030c0e0a060f0e030c06123705070206041511070203160306060e13060c051204050a0c081501090b1f02010911040504031e0e0d 69
    0x1941c09030120b14080e48072400356960b505800c5580d03a403171103c0d074400d0100510041c0065403081c3d200701c10900d02401c00f00c280740c81640000b1100307421039000c00300003482d2104d5420f039141d03c6035024880c501d050f0000c103500c41c4484005a035501525240c0c10030203404070009581c5491b000a0068046031000003c410f00c1500503a9443e40b40c0360700d00782120303581001c0c0811110b51000810920941d0403210410701c000035203c545016280c014440c41d40b4100074450307140942d600f803008544805010044078240f42c918500141510313000d52001d50100c02401c208403501c2e1406004060131540298000341040041e8811399844c080c081c0300040104c038000400c81007000c00074a00c95003500035181403205990380d0321283da9035151040c0381001080c1850040100c002c158101c50000740000b040500c0302d41d0141d1242407103c2c088842d24006070744403001842805504100700c44103900a98040c0190b15140e20081c1c041d842803450307488110b850709068021142703d6070300c90002e520000c25811032503440d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512562571 1250 512561321 512561353
    0x3110904020c010221010f0e060f0f040b10050c010c020c010c08030408040e01080f0f0309060405150f0705070f081b1309060221090609120a0210060e01030302011a010918060503 78
    0x24059081f0446410102148038240c075621980324440041c4060041c2200c5000d01c81c40d083c0442040340c0181d12480c03940e40e1592800800504060203a6403941c541b40d02000c01404c1d80c01c1001d1740c1c4199006000f1810341642d0041d400380e00190071008844e82c03529980f8080c16203104940c01042a14210000410446808504003402a00880450b40d00d500c0445040d5107074403441d1001e07035003e6000c00080201b410300248151020f010200e0a908003410411900c1d043e03031000078100c520340c000341000d002c041441c0310341c4006007010100401440403100d0307403903008207508103004d0710920000511091003400c40c1c2140300d01c1c41e8043c00c155120200d070082d500b00c0c00d420001d03001180d1850800140b81e05000582688181d50500c000c100d07496400041c48482d5125451803400c60180c0800d2a15081c118003401004104d401b102e00000e41c51420001d0031900c64448008200d83d1020b8103940301d1f030303105902806445402c50040c2490a151102c407004120340e074007140d00750080f10000741030035003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 512563821 1250 512562571 512562637
    0x11030c010236060912071203020c0111060108060a020315130501140603060915030a0b04030206071202390a060606180e01120c0e180d03110904020c0102 67
    0x16034000c000e4004814104168810302c2d0801001d42c0043c003d00c2000010300c4c0100082001c1c11300101a96450758440551003d107541504090300585d0040d00e2099041d60f00909012907501d500001e0810707075041c2a4240e0303d45a01a006000e01d0b5004030101c0c00c107014401203a94062001840d01c0b2100c0005c540c140041c020901c11390703540f1000c661448120341051000c4131301c5030768010b00c1850180e40d00b007011491a990102195054031407000340d0800a0a48180940114000d4000b0256440d04020040c03590104044084025006110007000c1c4c92505040c02c0001210b01c01700c40405090018905480c01c0f5040402140d1084204440a1040740e40c40441660813aa03100301280d41c10b0311101488642c0c0c4d129606081c08e01c9401046851440480c6944483c0300704100030200741c2e10220108101426240389040342103401304080507020030421400d0398045410b007801582c0201280050034054201c000b8012600010000d26288007941150212180321010000c07500c910500303152494 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 512565071 1250 512563821 512563867
    0x1c1d010903090807030804030b0408070b1905070509030309210109060209100e10081e04030806101107031b0f150f0305280b040606020102070605130302070611030c0102 74
    0x150b00100e010901036804038a010a0303d801c444880c0c5018603550701c010064200610079903414005003c01000103504081d15030051f807a502c02886000e041000203000c650b80541030348280142040600707151348011064640c1610102c64041030804250315807528400400b2104075603500e402030110401400b80e01030400d440c001d0343d008030020301090056404841803000b0a0f0700c0100b20a8160340c10344518a159802942440641512881c50204034942c0405580403030100340907804000b0141010f00740440402450715140c1e191445141100391291620301002e40701c1e0403180400d490100c00c0c0c1c00001b00801054080f0f83d00710f03503900c40c0140981041c0d460b0500295810344a54505403080c00780c2809552400f20300700002c50100c0030040f4901005400882190b02c61042402640d140d208200c01402d03e5000541e64440030318019084400040080103000c401c010280082540040e00c00b06403400390524144040ca6021445d103107029030b0482a41d190b00000b240d00c4406800940c0120b01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 512566321 1250 512565071 512565077
    0xa020109020907050726040e0c0d020703030b240a11010b0a06020f060f0709150e03120901090905041208090724480b0f040b0f0103081c1d010903 64
    0x91851000c07a0b501c00508040d0403840b40d0087c4018001d0b41c3c0002d01103508202128811807030701c007040074250245e0b081040c003a00441c0c1e6070242d40815042601900303040c4a00c42c024142007076003001304054103010b01c1c0b12113000c00c014840c0908286a0943c420391701c0c454005c10303a400590351084000d544006114140d0050300805d4007155000105a102e0350003003103d40c0b05c0ca0220b60074200d202d850310005220f01c008100800315100c1803a1810301c0402a414403036900036545581950006d4034840780c0c0e83c002c00040c0e00e09402c2101256082e80d4480c0c90400790328050001d030725604002460310050303030452140c500c0c0802c1d25044078000300025064a04494075035103500f94198220381c02c031294020b00480307841500301280c0c4c800c0d41100c610845211f100751030004040c10a450b81d410f980ca08079001ca1040c0708480038042400b01c01003d41e584031440c8169002c00d503040da50740308214002c80f600e07520703205504440d521301c2d0f442d0341d0021900140107a940d01c0d090700c006003a103806009005815804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 512567571 1250 512566321 512566343
    0x5040513110d0507030204050606190f0e060702130b0406150f1425020a211b08070b0310090c0206060a050a050105090909030c070b04060e01091202060a0201090209070507 75
    0x102e00b4110088030000d90001c020741845440c1d9003e0001a01d0020450b03607019030b007000581c00740306d5203200070000a0b000395213861110b8140d42c1c0151800710391162051094400b0f01c590300041e900e0100104401012071400304001c40c1000c0442d01909d82508807160f86a0303407503811300b0a19031100e004c6080c181550b983e50b681e81903043e0f260380b040c071400702c100c00402031004440c540e40301740f048c00c800024405000075036a00d41c1c4903840c0604a000040310010082c4515450090050110301031001440a0700030f0a4840d2801c15a2552403c152041c2120440040000b03081410070006000040506080501a408169400a40341d0108035001840340c24952804076036414603c0d080d1058803c182c482624010b00081002001c0c0401441c441c0d0341c4c44200b100050b07500741030004000602c2800320458842d0b01704030000e4446010011500d0401180580401503003e102d81051050f58040e9074459032803442003022405481c040c0806034020110340240004c083d402002007d1a030301600341c2441e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 512568821 1250 512567571 512567603
    0x150108130311010e07120611070b0103020f010c12020a0b0604020c151005090a0605130608061801020c070f061d0904060b01020312180c06071709030a05060a1506180902031005040513 80
    0x2303c5000d01c034005480f1480303542c014001418210a8600381e000141003400e034811455840c140e04003500b42d6500d0050f080100b200040011810001e03800040480e015814400e440d00410360798107a060614500094440c080b075200c900d081d032a180601000785c504200c52170a0300f84540034000368410300b402501504c4070946400f42e0f921486041d1403141d00607220985a40303640d40030110707c0c0c4a25135101d5500304004a1414020800749008000e20324155900d54a0302801910206800008032001403248034454004c1c1ea480080c0c5601543c000c900188007120000101d14600806038090701803402041442035056000c1030b64a045545c0c081201c908222000c14003a107800b62200040a04190301c80e240030442502020301010b0001804456104501c2c1c3c640600e4204203035101c68480351344000441c9011914007132000500740300d081856044611688491041c600c51050884007580400410140350503c14a0001060000c03c1071002c0e05042603d168040f8469000716400d6291f104009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 512570071 1250 512568821 512568851
    0x70803030712090302072705010f030b070c0b0f040305190305010f06090305070308070f0206040306020306040c170a091e080913050424020708030f150108130311010e071206 76
    0xf10500d60690240c0f04840c9030104004034110b5120101001d5580c500070120820014490f0034002c0000c8000d02c1c00d17540c03130760804054200000d0880c2e020040200c1c2c4d070340c0c08034036880903e60f040703500034185803465070303460a044420740501c510404410100c4c0d403c401c5965813503040503050781d03d0f0051516034580c4d2180180c400c01440d00c0001d007160482039081011507010400703003070514016a03588031900300340d5000810980c003d410440d040c41e404018080701e4101441a40590303c014249581402203050856a04480c020203000d540381d00e0b1203002e400c000078180c4208100480308c0c0011140d50306480d1000c150303009840d0039802031401030068010b0280034020b85001e41e4001000d201074011b58091721110f14410114a18915000c11100000400c820021442150883c054280307d051000204207090141184941081070803030511800c94090000f841c0300e607a15081003070040000724429805070080344121241c901425000040340c1201507404900c983c46800100040c9088040031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 512571321 1250 512570071 512570081
    0x90b07021c030e03310b03010609090f0906184b1e0213060803340c0618061202090d150e011a100806060c070803030712 53
    0x1005040c8080401d00986400303580001601c00c040410780c0d1908051000f00a2900300710070014290b00310150581107480e8075107481201500c0c417588480e1455140642c02400c20240340180c1d0200350742e4065050308140c2d180d01402c1e2050340240c06000a80400d88444400b15010b00160b4200420203010f10841c0c5540c0c100ca0034401c004410302e0403140c500000c00010440c0300b4500c0103d01052411007005c200f03207480c0010040a40b418441c000c420030b03c10700020744046510604990300380242440f54600c00b00584904800e0905180b05104100480c86507002c00319110f20142d20318001c1e54010301040f0444101035840702c1e1900c05404180364060898280903124007000540d80e50f051001f00f002c150010400000e00524041c04401d25488181c0311800810300300006540d078410307040c202c010070f00442c0303003180c0f158401c400341b0750498000c1074215001d15070380002c00c100480001c81990310142610340200420341194000e64980381195500c1c1d0007034030840007040300c9101302c0442040f64055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 512572571 1250 512571321 512571343
    0x4060f1e0c03110708060105040b060c0a020402130b12090c0919200c0706030e161406070503070305070203071703071b080312011503050c030114040902040906090b0702 74
    0x8010380026800204a890440d40c0c0c0e0110100158008020100c403400c100e00000752000c040541425494101004103c0f0401c0c1c400c540120428409901c1030b03c4082210030f02c5c10340503500940e54864113100810030480359080500d042d0400305a0b1448800c0072107080d80306221441c00c48450035010010000d4076941220355140b512030000c03102482207250b401245a58112403071207007842480407041c9195412000301c000150b445010f080002c558140030f0803405030200303c09015218908801003490003458014650b640754500c0c80fa440c940c0355881202c50064000054a48a0b101171a004101ea4068a0300740c0c424030031940b0109a001d5403a0040c64010b10000055280c440c02d981c0701d501240030b80d224a03186178030300240050040e8040c0024803a40c040f80341602d48960600e0b4124101900b0034807441d003014542000c200c00d14203401d04803415600000001e00f42c030380d00400014080d00144100035000380c20302081c00d0800600f5004071154501c11102107642c0d41d00c8000803a52000d0b1510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 512573821 1250 512572571 512572607
    0x21c050a0908030c0a051209030712080709030f05030906040b0712090501050d0b221d0a030c030507061112091c02070915230a0b070203100f090c080304060f 69
    0x130400c04000c01c4010a80c40d0700038180103081c0003100c20051000300e4210740650550f040003800d201000201100107486600b203051030707c000c0c209039400401221860200800c0da8041251007000d0100410581c1d04d4001c004090707a90700c1e80c403610000695002000c00b00c0d0008811070008040034055503002e41070781c1c1c06070f6030582807000003413000c0d000e02840e1046580080b0340514100305440e0200380103e000c00780680106000030791454a500d424800c1c1c2c05501c10350003400c0c0d4036000a81c000f080c070000d0342d0545013a0344ca0b10040c1c20020020000d52210a054a0000a007017000d4039410034040d00c00c001d0700c8241d42001c420004402d13140114100b0b8400142c0002400b40000c0c03126520213816507a14030310860300da5850703214007640000c4030f100c041c5007040c0040c00481d0a1a195405501500802c00c3c5c01d418075515038046075860715481175662445d51a5580000c08040503400301a9040c2c0020b2549400c030b9441c0085900ca50090045000095402007a5400c2600511400043c84a054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 512575071 1250 512573821 512573827
    0x10f020312042d0819032309100204150305010e1b0a020f011505090105060a0807050f0715050702071205150405160305010c0e1008131104021c050a0908 67
    0x40d5480e0310700004000c980714a2040c884150794001c3e10304044001140c03050700156070340e6140c58070009000b0f000361766003010076003402d0705100000c4003a00c25609a2000e00d201206c142c071280342c1141085d03510702500c0306c068030100d400a60940d000355030818005440d10308000c00e13600c4810660311024111280e14100c0503005009011440c0000101800105481600c8440c030107084804c1c01d51798040201c4007200382281c010b11a9140c020fa0090060100702c44403403800200da030020f0485c8400400f00750900902050b12402a1034400c00c440d0000e9114541180303114003c60010000c0405076074400040c03044110104801f038040c1d0040e0442500200180740d400c01c456100d00c0c0740000100204d40c1c0d0700031000042462000c404001000d1440b440c00841c40080c1418000c02c000d554501c018482c00c150079042035425000140950441d284120605a480c00382c20000100c6d0b4100046d2a00f152000800101c81c00b03c9100c0f03a20010014101845940c84480704101910741e180c4001c0d050301810 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 512576321 1250 512575071 512575073
    0x14060a14041d0411040603030c0f020406181a120a1401241a0708070230010b010e150a0f09030f0804090e16140103020c160302010f02031204 62
    0xa56084040400e8519441c0c5455160301005030601100e100e1401d0391020041804100300d0070f070321840c900400540b0104061440d40c2c130010042110210702402071107240240c07070155161900001c0103826403266422902c2c0c94004082d00424071f04c0500070002c0350f100850055840e00503071608a0a41010052110181d15192040b1014000560301c10f69940c51190300070350008541035400442c0050400b0600a10f4281e504210100c105003009911204002003c0011420020384000035010360b9000001c20304140c00c031070750201c0d6111a5127440e41c01c0168003079001c01504514401c0000380c0c2d800b04c00700705101c140018142c8141d14044030b8807050006e14000340c420030854241078040d1600901003542c07a1100c040c0f2550318442a1444032000400b401040100d01030000b03920b00f0360f0004d100012940c025001080b03560f000d00400302c0c4000c805415641e04caa01600e00700703400601501c0701d0498a61002c221680c00c0d1000701e0101c1d42c0031903040301d40c0d8008001e5451903403a080840306680e0356 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 512577571 1250 512576321 512576327
    0xb0708060906120102120901020c100b0a0e1e24030c090a0b060409021809070516060b0303220e0106020d020309091306020316090b0a090e07091203020a030914060a 72
    0x107040003008150b500b44001e146e40e510b0340c08014003441074400016a107011140c5890f0920319151810103002c2d080500d219000d440300c0300094200c03050f60807241044c3d1600e41d03c21034424010303d5408600003118081c008804120b0303500408020091102d600002e0701c820905468a950004960b4444461000a08a003186401900941000034045071402e901c031410709080f60442c545a03100c034034120341994a203040400e44a034105505c0d00f41a41008105085180c0c11900c91a004001c0c584170610411300f52820001e0702c007c045003c5500c5981e80011200080c9046144641c06a6146004c00024601e0020a1811803808035901030740c900120b49041c418070140141c40c130b64060f40314900304808100c407840650b001e8556004010140f80312030800411003400744e0040b18100b18104812160380340c03c919050111170040685174100d65076441c0079101507403d03500642c0070b03415028000040503400720b001d83d10640b181d154011000d0b1190070311400b180b45e5a000940003907040010040c1c00d80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 512578821 1250 512577571 512577589
    0x6030b030a0f0201022b030605091302040e010b130510090c120504170414042a14070605010305030a03050a0516052a030a030f0e0601120f020d030c0b0708060906 71
    0x40180111001c1480104c450102900c0180b164084420051b40c005a101d6141c042d500050030308844840366410031780001e403e80085a00000d2141d13541d4500c1e19014002034100070329000780242900c000010301c0415402a22044540301100e41c100c00380440c50000c1d40c824804084041e5442c181c80e624203500650003080c024000795600c620303107100742070380c80c46020003803020307040c44841030514111000903c010b41c3d40b640d1042d4808842c4058801c403203c20340d0554443d0603003620b00810048940c1c00403044900c0b4104000d41241e08100c004028030900100030302e03882030a81d40812090796424a09003c8481c1510034080c2d40c0c01040414401c180301d0806002401001c1501d0302060205091b400c0d90310701540600e01d243e03040407602070340c11a05480b501c00004014038080c401d41e2050450b407600c6d82030500481030140c0551419a00b0301c030302e03841c1c000622903002d00311030075124a5040c090700700d10381c0e43d80c1100c1820704e0700c000864480c8685669401550060144211600c410702003040060b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 512580071 1250 512578821 512578823
    0x1e011109100504030b100302120a08030714090415050310200a211a060309030d020c0a080a080109050112030804060e190c0312051201090b0409020306100f06030b030a0f 74
    0x880c007488048003103200c21a81703d0060000f40e0303140c400c0911b10710600607034044043c030302c0d0416040506c10070085401c00c42140e40c419007503c1c0c112607800c1180065013490090844d0141c01c146030421000880038682100c0d41030346c00803412650f44224507005101500d65004000c001c2007840c20f5031480d28001c4101412030b0700c1a500b02242070003603d29504c00340540c840d000a03da50784442c207400d0461994128000c0c0b80000342c5440341b41d4035000742056601d10074025030099107903000030704d404142418811114036641c44800e59070b0310710035400000c195040c2801203a82d61403508000107141e01401244003501581a01d4070f0b505990b503030f00c8000091848044070203042c0605000811700c400b00042c0707910002d2107905440859421802d04060740d10a55440c5818050f041180100e100300c501c214604580c801740000c5a02407101000c580985888200250980300704000c0c0962417511810104c151181241c20818040c0d4030710b000c4040d039041c10b03401905a04003640341c1c004a00000c0d20001c0301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 512581321 1250 512580071 512580077
    0x9020105041d0a0b010302090a05090402060906040e09070f03030f12020412060207110414011a0f0c210301141201020408060f0f0a060f120c0905091e01110910 70
    0x2907039031003200c4029003403030282c0b030521200141006001d000074894101580028642182040e0500000c14140c5100d03004d503130b201d0f0716203d0000d030456130b5400c103d0700016000382c1410348455440c3c1c0c802c01a54020758805c02203004201010400b000d50115400860750180d0300e42c29a0704030b840d0b040e00c001c4c114120704d07504550200804540740e065415105000c520410f401070b81c452860804e045503129030304000c0d20035428000680304420350450000c0c151030709588070304682a1443d40d440d1444c495119207070041503003c107421100c9400030a00c0202a115080078516400c2c5030070764814544001d0040e808040740541400c041c504020041510b012900400186407a403a502281e14101080742c070218030280e136004104540e45072012803070b04010b1a8400703100b4941010f05950058100d07001d0084d100343e070004291306021700c0d11090340003041c484408000b2800e01c2e000c15500c1d910035400380c14800c9240c90509440010500c45d800b0000a0100c0c41c0382000c0240c0304000d00c00b05080241410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 512582571 1250 512581321 512581327
    0x311030708011a01020c040e1c18060914030105072307051507091703090103020a1b0305030105040c022107020607080a0512012319080304030b0f0c0a0905010309020105 74
    0x1081801d2048003510211800c41003d0252580c00080c9013030781d0458254003c0b402c200030710305801c2d4001440812411990940b60380305454400c203c4200c165000465500310603814001803054220040805407000d5011005103952035805040c240c4030283d43d184002025400052010441c0a040c1d961010407451390310302d45070007900c0e8203180856520700f0306c58141f00c000c14000c070b00b90000361000041c01000c071420000040c070340380d060301ea0158012641c149600040c10364a000e00c184c044140d0303840c005003c4e4400e00410309000f801c9800900481c0e001e24500800c1030141b82c00000c1000d000d001402c00c2070f00312752104203400b14a0300100e1040f80c2120b410300520f0300042c3c004019220341450307680ca4640359241d2903d4420791482c1039200950400482c01516103c4015500c03845868409403503c400310080342615400c1e4a0040e8044440c6020100707003c800c10810740300040c051401c010001440d40c450031a050b00c2842066071041c0860b468100c104140d50103600015440c034014140142 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 512583821 1250 512582571 512582579
    0x5030f011e0b070b060907020f07030b0601030b1207080c01020a020f10180b0a02010b0f0609040b030309040908090a14061c0605220f050112020d020d08070f060606140403110307 78
    0x10700f60840d500459510044d03108004d0707182046501c0640c4592284000c040038244450090344800c41c40c000600404d100000280843e4002d4000ea0b10f0120050000401c044280d0103652300c82815010340003050140c481020b146620028449400c00d070020104481c0c540b00f10100081f0420742140c0c0d03014014442450b582001018100d403008040050143da030b02d8504200003801c65a400d181030380b00710059002c1000c180c0f6460300356160200192000201c010503440001d1943c0248000c85501c40c0c20820340d0390401c40c12001030070400e64192071452007103859800340d06c582c42001c80c01a4001741c084c841103d4100101c14070001842090b03000050043c0c079913020800040003403078000c52100180d82c140403c205107206d0b040d52800701e80c104100c1941032240e00c0c1011108100083d100380c458085a20565403001862a28140d00100b010341d194841d251001a03502161000e55955161003000580b540c0910040060f600a520803185003509554801e424101000f92446e014490280041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 512585071 1250 512583821 512583839
    0xc0a050702151b060a140c1b011a090604020315010c0812070e1009081f021326060603062707081609060b0a080c0d1e060605030f011e 59
    0x2003d0000358403046840b103540caa0079280c050041d110f40380003480c0c01ca00c5401145016401e0350001c0b10004031981d40c41da80c84440d040241c0400300d41d04d89502e407500c5402c004070129240da03112501a100c04d82c0369a03440040100f01e020441380c208261054880c00f0045611030841000c0043c032900140f400d014460140c03000c207000881d8100b0100e242d8541030381c1103140c50b80b441e40c11040c6501e0169816402c00032569103424035048041300c4400307901040424080f05406480fa2a00d0001d2070b11101a5070710003400389110707600551a030710201504148400c641c0428000c0c03290002a004244507102c801c031001c00ca2003080340031050340880303d0b0070380e00006007071050100504405009107540781071841e0b00030a905c413651080340c000e494003008010620b4880c0503200c5844941c18203120b641e44000c0d01c50481c1c440c0ea18100555443e11542124005410000c0d0301d0078034941404002003625514191001e2006440c40691040e03a000108104400a450030000e000c03111642c41c04290345071150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 512586321 1250 512585071 512585077
    0x4030c15020a12052e170a031403010602060712060b0a1106150a0b18370b0d0903110f060109112a1903020f01060506030c0a05070215 59
    0x206180e00050b2400080b40d000300c1901003d030640004000604003e018145400505031081012448400c200c0350070451203400e0100810802d00c040456082103804d068807080d41000480105060700c40c61808641d56605503810790b0005c4d0000c110315140c908094504140e910314010b003881e2668400300b1407000c1c600140211281c1d5032141e40c440e03003000c030b422030901720000c0044c5011811400081403036942c907081d4000f126444602e0641e00c490101100014000005a072904021201907807002e00100039003103501c1440405d8000104803074200c0110070320105100d80d60030001e050041e03501088050740882113103446820708100086001c00000d08240041600320340903040f0b0320040060881b18020803103040d81d080007030f502d803c0c600c044100c209080008900e91880c40395041d4109804100100003a10f00b5030310210300f8807031240c500255140ba84805108a0754200000051541000300a4a000b0404000c4860a1880048049030305402c141c209a9012060b4610718801e0003c030002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 512587571 1250 512586321 512586353
    0x1a090d0204141803030928020a0b0304030809030a08040206160624050916050c070305031b010b0a0602030a030e012702011103030705070f140709021c0603050c0904030c 74
    0x40156030303141882000d200030082c90b403c8010ba4104004000c1c2241c00403500074455403c0c103240050008144903001c0e9464001e0000a42081c0102c2010800440000183d482580b2950f00e0690b0307652040344c141d032240647c640c24404102d401020900600d0200b0180443e103910310740541c1e1030006900d03141c05a072004451865641c100e200d541e80c50601c90031084000d000c0540d40341e4083e04050f40009a03118242e922501005000300f0b5a081032074081c0070001c02141c20804981c0c1342c0300665410581d0b00603c031003616040d864542d00d102e550800b000ca00e0202c80150700518141400c081e803d80152007c405881400c0d540c50340c4008114124410200e810061200840042c030700d284000762104404660944c0c0c55403042c4100039005074040204d9400e240d002d0488020382c5020720300282080300c1c0711450100c0740105103011440c005a94040e2201d402c140c42d40c0c50401003610036040443e250380c0005402a0000300f540070303050400803d42a002440383c54030300e8003100c054403050b10600480e41c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 512588821 1250 512587571 512587601
    0x1806010f0609080703020a090513050f0102030a0501060f080406020a210f0506010203040f230907020a020102010b010e0d0615030807120806041a010e151b15011a090d0204 75
    0xe02404115030001148000d810544010001c01d405c2d40c00042802100d441a03190303080d20741c000215014080389071002e0440c1e0000032540c01210004005004c2d4204a6246100340d14140c00040e04500c60100103621404d19241c0d0102500c032511b800002e5030002c4404414010707420004003042c80041c56a00296910080026508080c54001e0003a030f0303005455103045500500c0203101c0b05c400700c4026002c031000e242c80715a040d11001440d0007150007200b141e951098540b020042e005070041050340659100364020402e1203100e10042da1103024200549402c1035400e880200090200d1f88441d58060759803240e40c2c426540da6a440c0010b42c802203040b00d070b400c03900100103e401d802201c4190864011501442416506681031a400074981c0c9210b0400500310002041910351050380c0038000c180b02129559440c045944070000d4100000903100751141e041c0b5000c0512036009141c1c10313100b0800c1d60b0410600c10000c1c0ca01180c001c0540d00ea440414041c3d02d0700141e03241c0c8280c00d281c46030b00c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 512589928 1107 512588821 512588849
    0x3010305010e0f03161a18010b0103051b03100e010602100c05090d08070c05090a200a020c0d081201090e0f0705010912030306090c020309100504030f0b180601 70
    0x46e889040d00b5042941400a81e0f502c042d007084850f00400300912a803607482d00110211041101c0369a0980900d0844140c0364580d40300454104405120b00383c1225141d024507001410203900c400d003d0703441004103600c1030682c0d0042840d0003500d820010b007024094000308a4682d494030000b4254800010341400f0880b845079040003510020303048032218646a903003d0024814001c03024406403800090042480c1908100d80d683d500030350141c1002c00082d07080c4007428980440440c1c0e651003c0c4030100c580381550041500800020f180800c094010280c0241044009000e0354019001620140103698202c039640040700c3c5000c180440078842414100c00800b45078001020b001e081020f005040341c0e000010340110b51040342c5040c507450f044034041d6075520480c88002c0131254181c54100200e0b040601f182d5002d610550405600b000c101c00c15410000d0076000301480c100c4ea8 = true := by decide +kernel

theorem cover : BRFrame.Cov 512410071 512589928 := by
  have h0 := BRFrame.cov_init 512410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 512410071 ≤ n) (h2 : n < 512589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
