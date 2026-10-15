-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:56:29.829784+00:00
-- url     : https://prove2.me/submissions/116bbb53-cec5-4152-9701-a6b15b98f2d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 927697841 ≤ n < 927877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 927699091 1250 927697841 927697843
    0x220c030204082107050303070203031e10061d090a0b04060914070f090503060c071b05090c070206071a1812030103110d0c030c05010201060f05150c10051323 69
    0x241480e04685180a038101c510a20f40003a601d00503000f0302140c0d200e241884c40603685e070b80300359201e1400300c401e038041d042480e01e141d20244c0320b9450b0500c20b0018034500780c000e82c2c08119190350102d40c4c4030740805c154020b0f00c0f80d00907c1d10503041004e0129500f80da07101400201d9034150840900141000d500030345858107038048540010203842c110501c10383c0c0100c1107a0100c00e503000031794980a288203205a500b030f02d0f030140c00c100b8001c030101d01c2c94100d902003c10000c1428854190810078103400680c840e5007581c007030022240003074902c92a1400d030380c1e00c0055420030781d0009200410410240030103a480389001c500d101c800800201203c0400f503c03501c4990205102c0102480000408024152110307503800c20050f50043c002d03441583c80340b07489003502c2c02c0e41c0192030040d031070650005100000003c2090407180083c00141c41031451603501c00b29503208515003e154806c08c203203404510b07020701c950344c860305c1200401500c40e011840c0c041c00320081d0003040801c05040449101c00441c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 927700341 1250 927699091 927699103
    0x706120f0912092306160201111203010509070519050a0e0303030c041d4f0506100b0702040911060c060a0f02070b181207110906010c032c220c03020408 67
    0x28181c0702d0306d100030468130049400318800c101848250040d0b4070f032640c90700b080b00d01079416514103ca04403800d54441d801100c4c1802121040c89440f405518010295406080144100031403407409130b48203058400484e1845d8000e96041c4980d08001404000310346040f0f603281403100414a1031087d41c01d0070304a80c2048040100101e0640c1c04403800700d2113401d28800c1040700742c00c9089000d00502c01851040c3e54181c0741200681f654000e0000040c100405131b000c4100359240041d40a00b4003406809000052195a00454105901c003c0c0412603540302c0b00600b03e01c404a5000741114541f240d103010590703045248400c0700c0c0340144440000a90100d030a150320150300e541c290b01e041124002a858032180e005200d81c2c0a00004802c01031001134040c00500a5083c2e4070324500b52140070045603205072480000e4005031141d004010030b81c01e401004554141440c1201c40d5024007400021040d1040c0f03001d40308840203a00c6244552900c0e406004140300c0c80e41011030510340380c000c0040c4c85d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 927701591 1250 927700341 927700357
    0x80a110f040902250f0308010e0702151e130c0801020a09030206090102071703070506130c0e2d0a15050906040b18041109090706120f0912092306 64
    0x15004913000b09400300c0c0c4504000c500548080d01181311441c0e0400d00004080500c040d0005036410340049051b00703041c01880d00502c1694000d111001002c400c20241c0f44001e018805942c4149111600a112026155000d1405007404001c03e000a29040000180503400001240d005000020401d034100f01401c1c22250107941807680c40f080701d40102d0400740e060300641a101006a0f04942c981000806864028030a80803144103498170507148847d10400c2000909501c50000c3c20f00880c40c00c10891a00464845503000202c9008220108803600407a00205103440c81010428080304038000e18141d8089a0b018000e12410312000c243c1c14100102200e0080b911540c0c250141d440b51942d0455044405840f818682020316200307c0480f5a00441e900c214440f1000c00c506800204440085078401e448203a501d04550a02c40003511640e40b90800090750b420030039005c40d0040d400d00c9110038081c0d69031f0500701e051110781c80d040300c0b8001c1041e00d0390114100351001c0381c4805007210101d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 927702841 1250 927701591 927701609
    0x21e070e041502090301090b161403040609030903150f06090c0f32040501022401151e020726070b16050d0f0e042318010c080a110f04 59
    0x355944104042d1040c04e581980562138800c1c108103004203041200d0041500234403c10980350402d07000c0f6100700e092110041c5001d81000818000307107840d0720a100441c4a400e101000940c2e0340c40f85103c004982da404003c2ca0b40312403400b46808106d110300001341400301e40401244040050080180101443e0307a014000300003400401c0000001c6020300707440941c51208031254003254041050b8002d4402d46001d0700c602d600c4603100105481012955061800c95454660710303200e0600c58024006c10001c007404241000c0020b1004100c69844003860302d9001000001d01d4400c100308042c4000301501c050340d000d0114507400300d030080740c000215040300d200281c0310040c031a0707944118019900700030100d2180074198800590403920100d095030040e101c0d408485648401e001c02d0b14580d4445d016581c400c445103190076081041e005401c51040f180f81c1d4a00b0020b900128212282c5c13484682c0455881d50400c2516100380c0985440b034148000c2090410302564080101801a80102c90f0b003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 927704091 1250 927702841 927702863
    0x122f010f050408070f0807052b0807060507030212010501080108030a120b0a060210060f0e070c05010b0406080c030f160e0c070516091a060f0a09050907021e070e04 72
    0x110038460400c0c1c07005081000141c0340c0543d80c2d00000c1103075144510903400c950103880300008d00361525040405404d90104820b19610f5040f418071000801c0e800e804554420041c000720001c94a50b100f0144181101d8400598032220481c20100540b0164045410480402c00501c0382010200c269100c0c20403a0030720030b80c102c40c0d00340d02078040e126980c1c0b860341204583c60300081440c0d001840d078583c0881e00104000320754442102041c961080c3c0035485020380c085c00481c20f6a44205405221180548000192214060000380c1940c069074050140c1c0e6102002040e03140c9014001640d098003070400a00c5041c000319049118030200d40b003141c003290b01c50b60000b00314403d00b50031501c0099221042c0c5100030400c1305880044241c83c0100030106162181c4400e0300602a4030072041d4440042c585400c01d090340e1040c0c3d42991104241c201040348002c00090991542d000141c064480340d00a00500c2c2517010711000e084210f07920218640e803008504121070140c1030955500b00c0e402090700d41c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 927705341 1250 927704091 927704117
    0xe1c05070f051507090b0a0f0e04021303080405010f170114060705070e07030e03070c05040b04020405030106090506010f052706071e052a0f0f0a122f01 67
    0x203046a03041c02401500803004501960341c44950014030429083d02d4520010751114110324042c05202110808207040c12440c0003100c0c000d5a4038054003200030000f600d013400315050104401890782c41280c04e01c40105042c000d40da0041210880c501e11850054880940b00114125000040c4903c29008080c0b503188c20309504c2c0c1d801151000d582042c200d560710740e5201c03080026147d00700c401000107440d003140da0502040102c200e5081a400c203c0700c522150500b42000010548022001d03885a4200300020301c030b0710280214402018017807800145031420f003002408003035002c085032042110030482e591140c1d00022328403061680700c1c11040d00310702404012801c203100340f0030003400720040c0c81603240070940c00d40540e04500f40328900f524115075929032407081c10003540608078114501c060040e18107040001c1003039141c54000300102d502c0000d00020440341a42c580000413090412070300e02041c0942c451444401c510b210603150590b031441a41c4400c1124903a09103410802e510111407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 927706591 1250 927705341 927705353
    0xc100b040c0311120406090206030f01141005180402040f0b07060c0c23030d141008010e0c130609230f0408070b070c0507060504060201140906041407080d11010e1c0507 74
    0x242000e9015103059a40e0526401d4084031201c0dd1281c2e1142c00000c103180740380d5080040d10b421b81031a1545a15041c103020a41c4214100181c1c102c03039400513800e20002914510b10302d140300042c48158074680d40c0d8182e074100f1a05030f980903032618061104601a080005800340c010700200b10405034468251894811010300718810101d402d00c1190400e040c920302c070401e4444d001c1c003c0d5242c12071050050750b40c9941500b6219004190741140c3c014000141c210305041c40307410011101744100086550311901d02800300c2e0402c050200c00000b0710406034001603042414243c02c418040401107403441e2a581d50306991085100c0101454682c1c40030964030f50042c0c942c40600d40c0e200e819505001d845120041850708140714200041d802c21102e8900302d1201884107000710302c00405004242d841341c4540404241d80c002c0300d26203200e41500060308003802d00807030301110305036a1034011a170101384006c1e09443c0700f8030303c400d41508401212801c6c920f0360900f012441c0310074144a915051142044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 927707841 1250 927706591 927706601
    0x62709030d1506020c01020109120e01020304030807060c23040b07020d06060b0c0c19050609010c0614061203091026160807080903030f0c0c100b040c0311120406 71
    0xd000c0609029110302d8420490301004180d90843e82200c1035543c1c2d641c012403e95a07080c40140a02c901000b440000c688a04151f41e80700078180116440c19580740d440c10000c1c1e22043c0192059591194a035904917840080c80d4822082405000040c0608007440380080c81144100740386039000203981404c5480d94021002c2c8160004010090a0350707070a000c1125521a12168006001e44403044d025407521521155054504a8840010038205028400d8644c4000c400d241840040103e4000142960161640c1e11500428110b800d003418001d000e007550312120f89584a4009000000154540318980300c8000624980300c5184410204840311100e4032405900703410480804003e00803c6044140c100f80006503214102a99514400c6440d03100544001000b41c004202041c60031300040303196070f00300c0b00a031600d0b4984181e5850752841e01d15040e0000070341644408202e0040e142a124074003184080e42400c0c40030055030b000803013151080b55550b0a050454401117024001aa404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 927709091 1250 927707841 927707857
    0x11502070b0310120614010b0c100507051c0c1403010b0901030504020a080a030309110a211505130b0a1104090f02090402070308011404060b071e0b0a0c020606270903 73
    0x14281d50401418032202510b0702006c10b040580c1c0e102c00000d9199520b400316001003284901414040f286140d10401030007019104c80c0030040c013030042e10404c14181402e54110b080904c070000d00c80c40040800780525042400080d4041d070700b07100410a8007070040468604210074600003039296901c2c40000c68101440d04001c1c0c1c284901e50301d5600f0140c140d800007032000c2c0140351500f07507030f402c060400c0341b0150580078801002c4146088440071030107980b1700c988042e12401061924000c1508004111003007110304080203048200c0780c40074820300c420102e8001c07200b00d40c00e02440340546010306d04c6101d94455025016901c4080ca6021600c07035059503902c500040c420355503408207043c0100114400c0c040c125149081c0401000140760038410207088980c47c1201c142040d074030b0340b80c83c041c003141200348a25058010342c84070005401d088a40744603003441007001070400f00200000f46003040c018061070082a0021480c0141c5490140061450059015504081d603601041c1ba04601484030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 927710341 1250 927709091 927709109
    0xa05100b0c030a02010b0a0f0b0d1b0e090603010903021903020304030611091f080a1812030c030e010b030303010915080a03031b1d09060f090901020406020105011502070b0310 77
    0x9441d665101c0044010a41c16415600910010002404000380221544610001d1580c000c204101038840b180280030000410040021030000241c100c4c484104203803a402c00207402d4050301f00c2d5510702a100e407900040c080c0c0080140e007400da0b801030340d00c04080021070300f500300c9580340c501010f108204031006150300c03443c2400350010b11020044907401102041c3e00c6a01c0041280c107007044444038041c504200340c1d030b80c11580c0d112030348070b4401800303480754000350a0100d00101000c0303100025156080c1a403541e0010b882249210018110b41c50003420030030b80c0c0d0402200130603e40c1c000040d01c0c1501c54280d80003504504000058142c5800d5511080260040f400414103158269000302c0d424400754040104542c545030301121640d21804501400307420442c041d0a040c2070622605c1d5200d140541094150764007100010f56031141110f02e45010b82d00040c2c140050b503420b0240900401c000060480080d0034032101079250645405184201d00f40400040d0f503103402075048100418401d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 927711591 1250 927710341 927710347
    0x18020f0303070c080d17071d130507020a0605160509150403120206090d090b180109050d0b0907120803191407030c1805060f0306040603061103090c04020703080a05100b 74
    0x103213035198181000d140300880c42d070306400c1e242c20444003a0188121540d80e1004a80d00f150b24044040e00080801d02e40c01c0b29003040c0f007036070400c100d01c58140500341c1d42d00184803100ca05c0c9801401d950303005200c2c5840c981c1144004090316040020b841a0341004c03600400f2901d200d8000c1c0196026070360010305101a01c0e82001489500440d105014200d444203507028495401400c0d5a008c1d411301c907206240108000c40c81400214a2031f83c0d5604070145020308119aa0700c000440b85c5256007029a00310a04c0018040f41c000100603070b000070203554441c0100d0100d6515034a9480c00001c10400707400d0582c0002d1540340f40390b58803010743c4c1c52055a0300001401c1c000402001400b000c121100801c5820001d1816049940c0703080d01202c0d8020801407408420042126850f000a0102e60308203441d001d02000145a070b000b00307429480400c1d81d450f2245000801546003139071440540f4080c610400c494030200e5481051254010b12032000800d01ea2200c1044482e0314038642c0c0080b65a08002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 927712841 1250 927711591 927711599
    0x1201030f0b09070608011715160905090f070c0c03200f1905040c110f0a030f081003060207232a0a03141e01050f01060318020f0303070c 60
    0x4014141a4107010390040256540c44401995a500003401483c022501000040241000d6042681f40001c019800d81d0708081c00d4400620698801f6641540500440040107000300d60003078401c0000c007011220a00b0750705011740250500c1c4005800c640400c591701c42c4810a0002c0405108002c507400080001b91650b143c0d8042e4042e408540c03000d00c2100840b40329034640c900301c8108030800701c600107401005490401080010103803844d040c028400400c40010407254103021040044804002805480859143c000e00080b00c0a407284240000c00050081045000f2000f41c00d44c1d07849240143d40e8810350514100b5a01d40307601401488034010a40710401c0b1010500c010f044c50381c2d01e0304000c0084e40d86c446940d01c600c1c5103100b5421400050003040410503210307070a503000e05000c00fa9581c5182c000c12484801d021128224400e030f440e84144090030b018644044e00418147c58200540103950b4501182000b5101c0080c0c45200c003501111102c4c0e40910031240c24a41c00110400c8880e91 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 927714091 1250 927712841 927712853
    0x1e091e0c010e12060105090711070e040318060909020703090e041b0504060302030c040b18010b0304151107030e2808060705160f03050717030f01080c06120c120103 72
    0x300882900050b800c0680303030850300700103000030103040440019100580c01c000078800d80080007809031080183c1008079035001c1d0b505004100c00390004411a06143c905800c2c098600d2400040c0b9031039080100504210311030740209101c081c1d441c02c07100547d40d0070890900b02ea801c070681e042800e00034068801c2c031040044406141c0c64440905401c1c20880342c0c8c83e000c00049504505c0042c0d01034000701103c074030600c1c00c0c0d44000c0304050000c01c0b001441e0030025604170462400d0300310101c0703690000240018400e0008030001e03e03010764034060002e4101d001039100a40603c1c0c40007420310082009401c2c541c0e80b00403403da040c080c400d840005602a100c3c0003001698244030b24a072602690380030400303240c410012030780d07404041001605069800d170380d544120201403100b0780400c80f041c002d000001d5050380c2c05454401040080b551030781400d08040740c81d5041a400700404d94400d45c1d00b0285a160841943c0d8208030100036500c481c0c4ea40b50800400b445641031406000740c0e0000003208200c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 927715341 1250 927714091 927714103
    0x6030c0605071703011203051b0a031205060a050d0f170a050406090f0506030115021504030306032931031106010e06030304050d03051216171e091e 65
    0x1010b507603035290202103807183c10010f200070f0292044500c0203140c10360200340a000240f4003035039015000c081e4094004403682c201075074640700f10300090007107031450b112181e90302400342c0046d411581040c0d038a1a10f400120400062540103010518880079131050107a0340b07010114141c00913560359581d0101c010000d0a640c0301d40945804154818804502c000114605205540010381000e2550342008451007502240004032030443c450410796821f2124030740c01c0c20303000b98841e48000c240c0e1360544c034000c1034034582481c200300c820005031444a90311240702213003078000e00c2800440790301c03010040902040001074412a1041e40c0000d070680105648568800301d99111802550f60360303622182d00b002c1e1100142d910a0307040d44240001d02c420304d001d1042c4000d8501c6800c1180c44c00301135200381d038000e500032207000e4081080d003001491460f4203d0410610840c05514801f17492a0040024842c00c04a110301112405400001906104104800d00104503001115018002c107201c22554a903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 927716591 1250 927715341 927715343
    0x20309030d14030705280c061116060b01020f07081c0f0c0201081e0a0e0d1b110f060c010c021606020a0609030522080c09042406030c060507 62
    0x220520401203880c51142400380200d0142d41101c1e07181d51684030f422100b580000c4245031065400f40506001505241459006807200fa125070540312a54104441113402199203140803c80c100403c0200007141c001016026074024030011701f500480c00101e00d00104039191450b68460b103040400c981038001464428034041c400a03000c4000010350884494115150240110321912480c400640c052122203a000e9a030440361a00200c2c8aa080c0c609a40141c0300c0014450fa906038981144809000c4410410b409050252400c1140300045241032810301c4050300c0503802c03116210700d175920601460310b502001021961241c0550100a000b441d501d14000701611940d003800702a004080762003001c03a4110380241a917800c441d11814080e004103102141000410080c60000c0d0b41c40c0300940030a4028142034403440e9050072002450881c00e0200907100740a00020880021b1071859038080ca0704841c1d440e0b030a0491003141507005130089800081c000d444841000c10244e034407101038170311a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 927717841 1250 927716591 927716593
    0x70303050a0f09050a08180a060e310902040e060f0a06060e0625120e03060c03010b0306130e15061906090b0702030313060305071d010504090902040e0d02030903 71
    0x81601c0c03400c4120340c640d4000901a40109407014003142e420306c06040304005829041d03490601035000590802c50641001001c19480d204244c0e0354181411a0503140410700a540b40c83c003400030000442c02114090038001d13507141ca4011045440e26000b1183c81d0015a045034010704024144924601c4122906001a0320f07141c0e001800d0740c030980d41c4400c40f00d009881c403450714410a10107561001c3c60b40d90060081d80c80308100e00041d5031100b0809403c41144c0d214040c0d521601d0405061040150405021920031300050240e045101c00300d0340c200d01d04540880c0e1151911203030300042d100510b840182c5004844506042880b041d031114410401110b0544007002d011042c14400c5615000b810001004c00b4002d010114480c00280300890008040300e0800358103070b1202034209499040700d00000e890340240301c14203030452242c1800900e64034211107182d40350000209540114400e410960703407034485020a41d1582d5001040801401707090f26102c401030341010b9071b41c3d07100030041806 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 927719091 1250 927717841 927717851
    0x1503122d0c0f0b0f1b12090109050f06010f05011d0108040f0c090504110102160501180e040c0f050d0503070201030c110102030f070206090a05070506030c191107090b10030f060506070303050a 84
    0xc4281c2c2c2d140c2c5d40d0380f6411075150640c201042d100300360043c2c0e4401048001e00b0742d070301c0340c010022030b070104041091031120070001c1c00b041d8180802d0034012846a403005041c0944000b240b00003175006284c200f9069000e1034103915aa48a003000800d40303a4846019102c00b42e110400307c2c4000e41741c0c124034132031801114101020501d0000499480100ea603d00b901440001424440d030341c4224244400044504409a006500c0b201d01800e03ca006440440c2c0051403010b003006003600300b0242c0030052038100c6041041c20a140c0300c0f1a200d103e010710090415a413180c1c3c1c1400140601240103840031440021501ca1800306060121380710140c45a402510602c0001025010000346131154076a101014101e194548018045150800380c4584442d00003804000d5540c1c0f05240030011040e400c0d40d40744050f800800b280350415046030000004a82040c012071400d40700c8102014a201d01840c000075001604018a130091407582c00880e0f002d04005041c5040c0344d403503040b00b40214a85601005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 927720341 1250 927719091 927719101
    0x9130207051212360102130b070b0106230403030c03030b040506030a0b1503190b011203140c0a06050a150b04060f11030d1503122d0c0f0b0f 62
    0x10583c000d82e61000c07210b90b4141d000440545080220030014900d01150075903104d0030200540000c02d0300301e0003207096940810368000080743c40c01c20700e00402c40041118501300b03040d15000885a01401050107105001005010200c41e0b910031107500602d00b207585452343d03241e00d001841c1d980b0038801540000c4c01c181c2107180b0384ca4a4422540030380001801040c96400b030380c4c0c2d05401c000780102004485a04a80702e251161400d0013170000d2000150311186021201e45842c3c541c010040e0880c0c103d1100c55003148000a80060381410502c0419185980356000003c0c0030346084035903100140081c1c1010207010007011207070482ca45198045030301315601601c95082d0a0b49010354031891000520401019060078000d018014040c030003101a68501003005124100b91420241002203074200c0c2c0c481082804006050519000081c1c507080f440014010030010b024000820581402c5001500d070b41039042c040c903580d80072594404503801d59159681002c180640003192072096403190100010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 927721591 1250 927720341 927720373
    0x1e0507090603051501061209020406090f05010f120804030320011e0c03090506010902310515070b070f0201150806060f030d050f0d1d0a030e011103040306020f0913020705 75
    0x45c1a6445e0b9038840514000ba2071201001e072200300c2d41a0381003035440002044a54141c02000d00031546030307002060951500c8560b042c8130300c45170300503c14919151415000070b0861012602200d4140c64611703112118a0142ca51082102c1d5a69929600e01011020003010040c1442a802070f00d440c2048170403c80e401c258103549500c80010b202ea00440014001440c80340c2c080c0048040c0e02c481010240481911104c040c0c10002d5001040f100c202010801c0e403400b12041004039020840030350074840f9950760b60101113400740c884824000d00814013200b1034030035031020794503419141600da4038940d6407201549407030094400302d02a13404070003440381e1400c00190128040c2010350700d0900d80500c20326002425005030b511038480742c0d101d4004089516400d8201c080c0030380d0742e070094054000c1c0c5141c040c100010f0003501506001040c8641d444011000c02503500301d070741100c805641c441c9689485045445551134035070740220f586440782e04e428003590161041c01c0c4500c0850ba04e403c2500502 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 927722841 1250 927721591 927721633
    0x230709050324090a02120106051318030305040212010903030911120d08040f060501031505062209020402220f0f14012601170c0a06020a1e050709060305 67
    0xa01248a03082c261000300c0940012800d50048a2000b61003000c81c1c15400180c41c0c0503280d060701d03c0d81e03450301424442c1d4074001e04101c04401c260401000b000080da0050007445503d00310140c10725644500040c203540342c0241e545c00c2544020000c1000c405540783c090003c0240050550720b08000d1540010780741007040300c50320185030110003418031107004c69044400410050044415400700d1201600180d2180030316030103140300301c800c9404c0481c1040d542086800007841c881c40359007240e504182c04010000f140390503400c080408900f041603400401c000e881161100f519240d01c01c60f034201c0c2702207140c90b06c0043e14001402643d640303544001c2501048424014205001da030440060b0007503003d4144aa00020080200f5140c610000b0040c049c140090380403c510718915600040c1d059801c0c800c000807200c044a00d01e02c040c0c00c0441c02075541104500091130301c016180307c01500340100815420440d8410200d40c1226201c441c15809006035110841e400e100d600a0051020314403450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 927724091 1250 927722841 927722863
    0x50f040203071703070516090e0a080a0f0504080d05090102160503060c031f09020d0605010908030406080c04030807050114012c0a060915050909061312032307090503 73
    0x103040207401d0402c0c10f0840c01c030f2079003034521a1004100420000e070003030050a80404102c40010710446c5007804801c1602d900031146400e81c1c000800e070200050140058411800140ca802090613040c00c0040d00c2910958001d0502841514204112203510000400c2c0c5401d080e425500000e8800c00c0500c000c191900405515401034000500d607030020102540d0700c00601e13041240a150303861a00c88490020341c20501c40f050b000910000c0c4e91006014500040c40b0130318080741c00c01e04c1d02960a40f01e0049010326010008a6004202000d10490503100699000101c40d540c0d0b030ba075440c00718000e11a000b03280e0b450300e803184000910100c90305082e40e00b00820000105014007840e12001002400a0090038041d40d1060045170280d4540705842122071612407000c01182080c1c1000a00c000c01421340d01644d002404000c901e801150401e40080e500170004068581201c406501030a031003e4002d5004027450140f00c1c1155000550a00030030340b6498400d41152a2014940c6824810325 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 927725341 1250 927724091 927724093
    0x90f051e0c090405070c08070309030b0721180c180f0603030f08040c0f121a07090902090f3001020c0c060d0b0a0b040e070e13201903050f040203 64
    0x441642c0c02c0c141500415031092041c90304a803000410366409071603811650050b00000c1c0082000d10800000a48136500451107040080c202d085440e40800d4200c560500558038035210301c034123500c00c010610000c1c03403554041a2000d2050302c9180d109501d0b4002d08030341c2c1003241041d01c4249034640c144101e2050701c1c2c2581d180380e030800c036441040d1142c46020340708840d1050740100c0041c0c504001c07004500541041d204008100076142050000500c4d4404001e140c46a80c605008a5582004050045441005001d03840341e040c24001014031950041071600512507005400450b9502034442c441024084415400c03541c60010070340c200e0295240380e9507168802c440075081c91074004068190002d083c2c03030109081c403090000c030381c8103005644032481c02040441d0a00000410400e5164424034528114120110001c002556040080e200c0224682d491b0401800c15049503807050101030704e41a80c641d5100c6c00c120480c00d0440c080040c0001a140c940400e4603120807240603806150024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 927726591 1250 927725341 927725347
    0x21060c05031609120b0415021b120a0c0f080c031c0f0917070f0609080c07091e1a0406031112010b06220306050705093d0504090f051e0c 60
    0x40d403171480000300640140d4a585251044000d1080240010002c0016003e50303500c0300c0295924070341c500300454107880c1d2441028454105000d501404030036a031500440401d407040c0407410005000e1051829521050000040d0128803481000f50741200d203130390020030400c06c400303100414119100c110004000c05d24101001d0302078403154000e001c009000d030080c01c3d854000c0f691104126510301c42d0440711054007240501c9215030500c446002006006018015401003540008211644c00b190000c900d55a005030110980701452010240501900401800703440c7e05240444403078440403d03100c4c01030540e0101c4202d1040c0103c0d0503072607002d4051401c1030204450150140008420044501d10880e800030203ea03084c00790601448840c0c84281c3d03500040d40074400d21303e0b030900400d11444941d00c06440e9603000a03d03000ea50410540d03404440b152207030f00071a903522495005100740c40c20074580ea409000b01303502180c0103c9060b8809600100c07031602c5005551400c449180c1c48002c00c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 927727841 1250 927726591 927726593
    0xc06130201170f0c0a0504170a1406040503090411071a09011b050403110409020306250e03030a0807020f0a03021c02011509050a090f05010c17060a21060c0503160912 73
    0x41e00c017a00320b0500ca402c0c00c130308154a5010a0510022380303000074103554170545040c41031040204401c00e000841402800e010b01d8a612800e65911480d0311140c002e65690160f00805840381c02640d00c0c095010241d000041c0c210340d172002c040301782990b2440455107014102440007260b00500c030380703e200a864190900c2c0ca0340d2181450a599590020f40045d22103004a00603a0180f006500c51030800c1e06400400e1500c1d005644a000c01c0c4030f00b0300a11008007046912960300105a0f040c501a515042e100742da940c400481c1480c1d0320015034526442000d00010401d030300804c0400052200e48140f2a20103521081213090740e20700d428501c0e8000503281c003402071851640040b548940100004030311031140750ba42038800b0003601000c1c0c1d860b0b50f40d054601400c540c1b01e450032600c01254540c0120f281403400009a401240b4840c219590f03507138140c6601c10724403520117600d900d034201c0400c01a2000c3c0716805402070784115103440310030b400721104c240c88600880c841800d54204102052100c0c43d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 927729091 1250 927727841 927727861
    0x6061204050c010f031a0f040608070e04030e0a030305090609030703020a060c020306103b0109060e13020a051903080304050f0706020a0b160e100201020a0306170d0f050c06130201170f 81
    0x42c7d10107a90440d89418012403403d0040143c0c00c01130003407508114031842c007400d006021a1198180b03511071440c441c0308001196118003030382d0421108803040d60756050240000f034a0010958402500000d40c070702c000411a800508a0072058001d409176000781d0340d02555080549690b004103003e00b4079410042801440b00b1000200003200c50040c2c102802e0403102807202404264094400152107482c14040046d160740b400d40c01c07603024100740c65030000d964000b403103803016401040c0c0250034501001c0c0060b540c0300d14050007103810011b180c4d03417400c0906196866040203041e00200d403003407160000304507200060710103c03550003201501c0d446d220b80d15022084c2c11101c02c40e60810000e1200d9000c075a8030003840e4032180040e50001a80d42c511140041e003915845c1e0f003c20702c3d004901e03c0ca5500d401c40840c24800a01d2180703021401500440c81c10340340d60080310317108001441b81504100441b04212000340c0c4450003622039201c4400200030790030a002e01150610039480005003c130740d160760 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 927730341 1250 927729091 927729109
    0x6050d021008180613120e01020a11010e19140303040614031503060712050a020a1403040c0b0d09020414070507170c011406120102090a0b0306061204050c010f031a 72
    0xc06807000790080034000c2444c1c94401c058aa00c0021300121700000204072105081d4014002030703003080401d407111540082d45070101188098183c00b28143c5e10039541c2e102d02c10360f14031038500070700c1c200da000941c560506074400715020305448060a981c40500d149000401d88040319506d6940c3c000c40c0c6248003c0e1236243e000a454010103c9424914194564040c44614800c4159035100081c80580c60040c03025504003601204040f4810000c00312459480700081d51340c0b0403481c01855580e01c0b10301c0c18034180303082c075030107807512030404650050b600c030b41f40d005001c119000311810b2040b400e4594212800700420303900301001c9081044002d001825444606ca40c1200c508521420304940781d18047c2075480c00c1400c0d04000344e02c0ca003040858034104000344918100034000710b041c0b01200c03011a00c0c10007680202186600044009401903071054115014a60501507607507950030035162407036442e6005409180880c450f0702c6203000d010301c2489545036815400c02075010200c0c041d010300246030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 927731591 1250 927730341 927730351
    0xc010b2e0518090702370308091603051e1b0f0a0305030307090608090319120f0c030e010506010c080412110d050a05071a040b09040b030f01060906050d021008 70
    0x503002d03440e400c0d1941da52100b403440b90f01d2a401401204007690301600c9a188034059807224640d004141c00740c046885092124520f60505000c54241c41d18000c40e0311703001c083c903012001a00c8a010220402401140301960f40348801001e51140500c0015030b038860409800d0125500382d40c68060000c0c0c50080724941c012100a407643d13040c2500d0717840741401c551049524001050f05008200007050b0320842c8207a00409007400303181080c0d01004014001200a081d040420281d0100300220060030350122a162044030030820050b020725101601a01580500c881316511b0300001802c00e5008000410071980c0c401c003071031b1600c1d082c18810324070140c10203400d54899000c41c00070107075a01c821001400c00e500440062006d0b0806241c420310f0101e458000c03400c88006e500c1d40c1c1290307034884000d48058400d601c0c4580d44408000d400700e4010804540100d61510522010842919041d4010400c0d50555002401420b450710306200b110349400300020f42000c81c192140c0155442845015040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 927732841 1250 927731591 927731617
    0xa020c010c1a01030b061002010216030503090f16030c06020a02031f0605060d0213120b01120809130f0f0c02030f0a09080a03031e05010509130312020c010b2e05 71
    0x39484034041d840002001360021203000e0460741c1444910f1800e54819503400e0020b01c025450a200062401c4080600101c018140080440071518489003803041205585042e002c070b0b200300d0030341350011015509520059810301c804100200e034262000c1144400e498000d40141540300c085600040050014100c0694032a82c652000c20280c0d10701d0001c2842c028081c0025031518214001c6413045e650070b070b005104540c44e030018600010f0007580350b1030440c0e14241090b00b030402a070030040b0551207480c000c0c41d402914441d1403d0203042c50f500540c1311044900d410030105040000c0749040328501c29000c00035038414058080d40f180b8113401040305011500d00000e00c0b03503844030f010f45411200d03001100803070348603c0701d102e191400321881160824102400c1c8642c0d4500f801003110002c01074034800b40c210000c0251014140200e514000d40100d10b80d00b19907170540c0c412090300a04d424400313903101e0048001d421254280c950108440d4003036607851002004441881507650740d101941c51954 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 927734091 1250 927732841 927732863
    0x1b2b0f110a030c080c09041e11090a050906060a06020703060b0604090c0906080f1012050f160617040b010e1b0a122901030b0f0a030507080f030a020c010c 68
    0x154a59030010740c011440303401c4038408182030904460415046141c103d00815150b0100b1010640190000c180d8016a2001451503003041c2840c504400390410f885401403200300038840c584200354030041c030409030102a548151520700410010407a644980c400503030207110240041003090b40f004051240c01080145420340e00c440d001d065844c04006040070440007013007000740369000a9015444840708142280d90701d06141d440d9030458050080300300c1e50303100d00100802c1040c1004100100790300300301150000c12050111600c4c1c8106030040200050204280340e0300710305200880c07401079130311038070900310b0381e00b443c0c450030000d00000c100c960001c000b00150a280e065400007400c030080385942e9055490003085c1d00d0002d032003038010040c1c520b02111112980c40d20002000c0b5075043c3e000d10340460300104140008a105a41c0460aa401416101d0010412100249810031110344c8829200395080704880c01da00c90191514000150b003044030020030ba58410842000c0d0300d0b02c2442072500c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 927735341 1250 927734091 927734123
    0xf010c08060f0a0302151b030a14250c090b04020c030901080402030316050313060c02010c2004050a0203010602010b03150402010e0406090203091015030c1202121b2b0f 74
    0x6c81c0d003525402240460001039511071030100c2c0744c03200014000f010011841c0c04d00c6800d009080c0c481c81c003000c0e0864100840c4040302e1302c403d41f020004280c601c8101d040f8003406400d0082c0318643c10f2240c0c503001d900c0c0540008144c14113009030307a042c50341d00024504052858005485010008200726414001001001c14244520300b44201c2140180000c6480f841c03881c10014105025070410014441c0030510100181e80c013040c244a225440b280c0b07018511a102402c205c00c1000c8405c503980582800c0400c890401e042d40503604881403a03000b40080e4904c481410f481e00e007581c141131050039400d0005405540220300015001c00d02800c00204d075030351898080201d80080d2580302d52600100000400720203603000c4c0411580143ca9030141051940d034035a0b4040d02144241c41ba1505100102d0341550f56150880d03810b804240706990030402d0282100c04a09003110480388200c0241228140c00c0905282c214942e91000144a4000b107842d103881c40d0401602000700c0e24103080c149014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 927736591 1250 927735341 927735349
    0x103080906161109070504180b0310061e060507020a090509100203070f0801080105192c0303010f0b040308070201032f0d0e0c030309270c0304050f010c08060f0a0302 73
    0x41c0403d014030310300714010f4030140400c100c8500152404040103404c3c0014028401441e10303032102119501070000756060781038082410140c56400444a651800c0302c0000d030f010400e22000c0304412500104031015456030000d584038028004060f422030032600f420300c190301c039940c003071500030800d402100c1e415002098010f060383d0080300e05800041481030403032a0303250481c94060250241100a005d80d280c0b1070440c401c0c4508010042d41c03030039213800d0a04d1148c290b505848a000711903401c007034104100d92480310382c2d0380e10130306c81c1040b83c501071440051140f40300c8082d2000c0d039a02400881c9411601c0d0011406041018004880c07415400d414130030031125025a281d81c950174444c02500c0340740000b0400304490060001241a42000e8010307100c03550040b08403410420704035100c100e110000200c80e1004520179000e6a01140e80b02c00707021015610001640c81a88120101d545481d0030004890a80b07500310400d102040c13580c0c0101e00385141c001c9100006410103000c42c668240c1d00e0f0005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 927737841 1250 927736591 927736627
    0xb0705120c04060f11030a030902011403040b19020a1d060c0105010906180b031207031e030b10050703020601061202070206040905070306051e1e130e1c080103080906 73
    0x80d07948554002000c01c4030a4010020010000039801c15510071081c00c2d004503124031880301c0842c105036403800c00104581c02469120071086481c2d8409441e85401c0c81c5c0501c420b1001e80d24442d14a4102054402e000c15500880e4001a00c958403804680519040070750002003d68001d54805800c0c441e44140c10824410140240340461001c54810701d0000a01d60070034030280910f50031810000c00d09000d40340000e05412403000c81e03402550381d041505046403015081440c007d41c0b0b05a134000c095413940c1c5900000c112440c100d41080300d180e14648145d038140f080940080141e0804001003003446e0080400440c0070030103080151138a4001d5000441e5548680c003c40941c981c0c80080c800440d40c58412040540410b4a403214015410401074402c140c00300041803141801c21440c3c0c01184001e840452043c02c0a000320500030070000100340940150501801d581c0b24400c0c1d10340c07900d400b0f88180311a24045458209942c0d09585900400f6481820360310742141040080d03185041d148440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 927739091 1250 927737841 927737851
    0xd020307241407080c040302060306100e06070c15080915040305091c1b0605030a0203090703060915110a0c0f0507030c0b0d140103020f0904020307081c020c030304120b070512 77
    0x3900700d03280100000c0c04208020b802404000e000f070201f0b000685070f1201301e9406c1030f812a2106a0780e1050401240d00401c05010640c0213003010629800300b0841400308810345e05010441e0031b11141d4540219210801210b140d41c44d40c1c04142d08040075041c5200c0c0c2c9422074024a8034614007a03110001c1540301c1007483c0171201090b07003c07c1020521203e03500082003a04020700007110203107000002403442c04050000441d036540040881c200c1d0504114102c02075038400c0c008d1001e200c49048c10150382030f003120380d180720500745200d80200c20200011035803483d00750344030413036a84042e40f0340707110041c00504c0441d2184110000440800c0a80b010303e8020456141c607165036000d006030313180603500300c8502450215002801400140c0e03c140341c20b0252402034030074200310f0740c0f1070002034980080c6512209060040320034038160144000d0344800100019000c4407691140b41041c10780d0ba10951040d00039200040024000040302601400d800c50001d150050401215417600c058609003565 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 927740341 1250 927739091 927739121
    0x1b05031305030106080109030c02090c13090603030305090c0901171e07170307080403020402210c13050f1c08040b040f090b0d0c03021c0f0803180d02030724 69
    0x2004146801d001c4c84024044580003802409200da501900c11408188000e2248500c3d0300028a00c461140c01d4408141d4030403c000034040e55020440c0c02810315010540000b801c001c009565003d001030f238403da0400103414118240c3c42c145803407201c0500117000d00480d0283d40c5c050310300d98070f41c03200481071402d11a0250119034604080d400250500d42c0070b2152503002845000b011500800540c1c007260b0301640d01503510b40e5103252080710a142c14458043c40720020060100c2100114050f00d01b0072400c0001da0307401910341c020000c0e0310001041c080e6115100c50585052041420500300c2401d1143c02d00c28181a00d0b04013404c2503812075081856140c0e08450104100803460150000ba032800b17441d10f49001e1490340b1074056520319408080e02502c5e5044140107d04260100c0680c0c40c1c1e001800b00007044d4003031030701c00d18940c030566100250713000000c8001d0002802081014007102a5001940752081d1a6951310400c101c1125007101148408400203015009006081c15540016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 927741591 1250 927740341 927740377
    0xf020c0306160905031b06360120030f090f0a0e0f071d12070504020d02031f0501170a061508040b011e060e061b07030c09090309061b0503 61
    0x10000400380c2c0f6059000c1c1c0c5c0300c0d900084000150481c0500107460410341074a2080d621206e40d01204a41e50001c00ca5801c0b07030341c3c912094003c00d60320542d0b4064880b000d0361608001e660b10342110080701e62000303101c24960000c0000a0180c4e89442c01070100e048064658010f804250380002c0c0f200000d58000103212030380340104103999913460541544172245040480e60038042d50204080c001e070702c4610740d005010420b10140c5c0701c00108180c0004020040c401e6696840348207404001c3c2d0800d0b904050140e014001a0b140f10360600c6000094400607500c2c2d090311903082c20a11213402000c3c2400c000541d0721035020800b40250541030408462607101e104e51703030505181900d900a01640401d204d4141e044000394940801c1c900f5800b11007592421000c00e2140c000061841d01c51900300b11801a661185401500c201041800072280141c0c118030106680d000308000b5140b911900500049510300c0c1406030a000d0803010304281000c00d0b400403000c41e00d5a0703161442d8812071540045030240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 927742841 1250 927741591 927741631
    0x501180f062006070c141011070611090d0b04060605030a120f080115030c091517070806181302030a0b0604230703020a120c0309030905041b0f020c0306 67
    0x42d801100c041c0076880c00408041c5080340c002060003020902c0141001a250540c00001404100000740c000c03015008011000f12100000d1071a408480c08542d9242421031210751503480c041a29401c0b000039119052215403079951210504004008862490380c80d200442c1a4504000e039200c0c5921600301c01c020280c9101024000140900c201010040ba038030045c070034200da1711a05840e50003a82000b2800310b24189060303071320985681060542c070303001800c5255029441803042200030b802080d260115114040300711140001118000c0d0406207107e031449459042031034050f0b2049506074644c01040f0540d000030f0030544501c2d0182c2d038040010301030164501d070520070604900d02b41c112401c0050022601442400b00040004040c554003240509040d40181800c0c1d041c130348071040c20020012510300c0540200080c08040c1c00054401a020610f4105440f402008400c1d4130f00c24180305e050788808a40c2d40c28074403440030441c024805102e072542c4003082850300400b8000310340c62a011003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 927744091 1250 927742841 927742877
    0x1002120a0302070605091b04112101030606081204120c0e07110c0a030201021e0703080a02010204030c230f030313230d08122215150602070501180f06 66
    0x103040207440d034106005480101414000c00d229403d003e6030081502d440030a581107850062100c403000ac0b81004029491218803415864140d0b4411642008480d441e0010665295000e0011004800c0100030038001907131513244070402c09115a400c1626643c86951202c050041a10610082611300750903501c0301c2002e200741c0500b000140d80e070001d80c526540000355100d807061203002011100030b01c070100c2e03850103000720006183c00c401000e9807003a0420009000b5401880192903007100142c1c0481c40c2e50342c2d003a0943c0c520881802e200c00707010101d0200b08100c00c0e0a200d0715070500c001c1101c2c100351094142510020441403101d10660081201c907058840661b0603076030310420300421400c0c0011781700e0301915844447e4024442d06603485087c140c5111040025200740180b200e2241c1040200d080301818500c551054144044142003c010148801364000c402c00742e001041c080c822940b007850310f00500301070700495103040c03030340d07444100449062a040b030000152020306000044d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 927745341 1250 927744091 927744101
    0x1006020618103b100b12030721020a1a07032409151d0a02090d11042406110a02041a031902060406030207050312160e19051002120a03020706 62
    0x80f0702d094180b0654020b1021511442c482c070189450580d6040184103584891058103e038030340030320407280d03102082e04020700b03070002e0002841ca46a20000c0010103407031021906142c050b40c0003041c0c0ca00384000180d03d02030108024218001c05a442c030101524070803c0a0320583e1850070f40000030300c40d04010381e180035503100b03c08403042410790701002c210b10803181d10711842036050000404010345891900b5801380c403400740b01690044441c0d0481c824050380d07080e0901082d5085808104d1003102c801640340089000341d8003034940c161031804200d014082c00682100288030030503691060560781c00501140c8c519400380305031401c0c200000e805400d040040a044012170125030340400d046070f002a00520031402004200b68020942d181042820400d48281050203410055180f0b8100101502c68076160721030400110000080034080c01c0101c09600c10403403000c4a040a58103040074407850798070001c0a60114800c00d109224801c20000140200c400705580c05070340e0306c8880c103109040d24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 927746591 1250 927745341 927745421
    0xf0106030323180103090312020f0405041a0102060c031b070f0b0603030717070f140d020c06070309150905061908060406050d0605040816050105060405100602061810 73
    0x802c1046002c0e140100030209182820b002d02e400f2034124030790318080351040d6550038500d4842e8004160004181c855201800c02d46106031002c11030b440350f5001d250404050f03080d240b80960015008210070500c0c2a0040d070344a122502c020171035040c1e1060b00600740c0d10803c0d080e5001c0211280d01020400024001908680103d0041d4200503140d1140701c90101d0000000b10281c00008081040041950000d1602900141c0b28800e641800d100700c0d498640203600710f80180908185a4080d240c00425200d01c0c3c0e4155444011080c10008100c551000c13010072401400710f00d6000052590f19240201003400b8550484075900100d140060121300e0094072702407040303044c01810321007038813049510040103400c2000410f03540c403117081420f0540300c2c1090034550745000b0b0002c3d40c00d0100541059000c3c0c1826902003155075a00801842021403e0142000680101b004204591088110086610303c00c100342d5080040282e0010300b1200031600c0305000b00d0040311122a2000b03581d29a107406 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 927747841 1250 927746591 927746657
    0xf03070503070e07030b1002012427090f050f06090304060815121b3f1002041512090506011814041b15020304030f02030f01060303 58
    0x558141400252100386500a659070000040d000411152084c1c10250040c180a0b12030090343c1300c200d20089c00f826254007050301b0b140100204c1c0c5046024901000700311104200700d42549010403110024080d050100c4664064450030308902044c2d150303948901051090009003910b54182c62071364101880200100d6440c1c00502040100700d400c080c1d5187d000302c0d4050307100c100825460004401c0b004d60307054009503102d001070141c0142850048035492444c1110300c02441d01c0d24030400650703c111044640028180010f510032202e80c6906031241c8406500150780300c08408800c40e0f01240c000d81e0025446019000442441030781100b825001e0000802083c410b01d542ca4507a590780d1030040c45900c4020a840c0100610104103070720012444035105031514190401e800d201c00742003001c1c20481460b01c0a242c001525000110381c40b442024150080c6040c60f245031500c09040342c001c902030742c050051030071500c421070f4203126200203544031303880d00c005171400c94601250145c0a00701104203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 927749091 1250 927747841 927747853
    0x40f09050f13021207080706030b040b24120f0a050112230307020a03142407031805030703030c0206070f02060609061203030106030207031d0f040e1c0305060f03 71
    0x7070505101c4159901180c1d820240703000b0402d610103d04100d00504003c18107000e02c4001151114000c20900110750340d0f0756080c07000d0000074040008895144801c80d0740710a201340c0d241c1c004110707106612140b02d240d8008504101c21201c04c0001d90038200c8042aa820440040203c0c180d0f0350f2243c0f0340540722144030b05488242175640c4140b90f220030798490036003400e2400111141101001141c4240e9809042d400d00541d581c80e081d00b108401070701410040c09504055000021031a0f98007807603441000c039031040364942800540080c90007200010083e4103440d0a400400d004200a1001611a1ba000650036100280003404c1203000b4141070200540314100c29041c6030700085664000d0000c5030500100e0311030744000b940c0c030703440008440d0443c080400001041d9405030701805c1094000d48400e150b0302071400c00c889558250241d080c2d1b0004409152050605096100c031514817030100840c0c0744007085111080110030360421000000c0e8541041000380d007004200050706480640c02042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 927750341 1250 927749091 927749101
    0x81b130603020d0609080d0908120606070507090c020712082205030c0f0301090605160e010c1e02120105010807170601030c051005040e0115170601142d040f0905 71
    0xc0403c1c0ea03040c06400701e91554440024000182c0803a04002c0083c2410040c01016241100c0c2c1608440f103001250b0b03c4810000c0d10354204101280c2100c0d0340003002c0e22505007428140070003001c0c640c1281d011441618408500c5040e09045070503a80d0150b0300a0303450f0188040d08403640803440060908440c80040100131702e440020742d41c0e41410040b2117403600c15080c0d070003003801458800c402621b5281072800b80600e07200311480300c10001d03940340c1d100c402c1103490900540e4200001440248144004040304003141002c9a0104c2d1540c8000c0030300307003a80004034145080d14801e81000320a42c01418041002401480324645040e402c900903080340d41c596107440300800403900c80e0340c2c011400d961203403640c43d1203841114040d0600848000041d40c590140c07002115000c0c1000011503203c10700c803a400c0c46c038903108506c54003050b9a000115181104100100e4006002d01c01d8050b1000c68810707149100503040441c1c1d80f10b0b40407044d4413645019404200354109901048140c1e01c0c20060003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 927751591 1250 927750341 927750349
    0x30f0a0605130f0f0906092906090c130e090f160302100c060e06070305070503040c0605160b0a020a030c0c050c04021e0304050c0a140d1209081b13060302 68
    0x1c000c050318540d001840010704900c490107441c003413911806841c5000c0715a81040a90350041e40c0c01d42c0111780e4855800d682480d502199020241c03240e01003884c4900040c0036282c20a1400d601140c1c100c0c01c03600700300007120303e0842c910343d40e0044200400c20201700801c402082102c0c0c02da4229076801004c601c0c01c500b8080b44c448500d40000782c02a080304c200c0c00076150083c1540040b155000000300000c11000007450348440080d01c0c100d001908181c0460885807054040d070380201c0e040702600e11031501c1e00c0c100b42c40c01e034099541002c610003402c3c55100030443c00c050700c51040d100b0000140c0d4520a0100050841d200e01841c0018004040000f001080740046c541d1100c10095500503039410125000c0020009036580041210000204101c2005004106102ca01c202901c3c1c030081c40f0344840d420740600c10301c9a5010b800400036401d4002160051f107016002c5079060401250b41621500c50b0360901e0301c0c00749800715400d940c010002c090b0a241100501e209100c0c802002a681964005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 927752841 1250 927751591 927751609
    0x9181c0212121609030c120b0109020f0307120f020408150a0603030203033402010c03060506090d0b06240417060c040b180306010f050901080102031b16021302030f0a0605 75
    0xc0c060500c43c290345900c442e800703110204041c1d900b19200e8000c4a581d68482c0040d0f588404040380d00300e500c2c0d0000690792249000f5140240141d40c622411035903050030494040d01c0180740d02c3d524980710140341c00508598401480900300110160202c51152a0707840c410845c098001e902051420000f000425408800e980d000746020410010882c103d0051582074004c3c500801d006051000c100d022898056101d81c1e00c900694070700344900382da0740d0100718440c020000ba545d044007002a00d078002881d00300c0721642c8004018025410303414424207002c40700c0c180708004804540700040030b020406220744640c0100005400038a01c9190116036081c40c3d009070301c10f12081110200d030384502640703401c8000b855000060700f01c0d00f0b00d603591102d4001800e0344e849501d0084020800200e503041b41030003101c1c4a2052014400c01a400702c4102034401d80c4000d0090a014048140010050303547c56010302e85d00510210151326401c140041d0411045d000c4c0c101c20380280b6141e41000252a2101c00e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 927754091 1250 927752841 927752851
    0x170901031107260705240907060f0e04061505040305060a091208040231140c0304020d0c270c0809070312051e1b0d080609181c021212 59
    0x2004a051000762840013800340c80002481400751034104018030704021040d036240001701c000840242c4907405019111101ca004140010344d111803d208502d00440c015030a40002400014603981d072000042c902c400d118620200044000408101740641001540d4000060039010882c03030030075580e40040c40000c000c84e54184450440002c0a5640d80700100301c030210001c64110b602942a003141642e00c01411400c22402e1420038031201c8030304056511841689080c06a0703182d80c17150707001c10107915019a030407101203d03101c00108201d0420050340c00e26030500c6e103107288041281900203050300c0c01107608400f0000903000700701c0c000700000380e80c7d400c480e0440301d0001e01a1060004450300d100b0a00140f0254000010000c0030381c03110ba008240485051005141140208a02c9034030340c030203075001d04000f03211000032900602d4085100c03500030000420303e401c0440c0d180f443d6800c0241c50301178208400c1c01105002000c035014401c161800c2560310906142500300741c00d07500c40e8040508 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 927755341 1250 927754091 927754133
    0x14191112060711070f030c090c2c1305072d02030d0f02160b1b1903090809030a05060405060907050a0b0a030b0a03140c060c03070b15090f160c02010504030204020d09170901031107 79
    0x1a0004d2f251002c150132071030a4a141070011b03141075500900f91000d8000e800220314a9009007400100f01220b01031054109039015614154001100304040d02d030f9008000b003419420001d8808000c51032071044045482103101c003849260202d41200e40d411040301100612208010031305040401c4904890b00d1806420700186910843c100344a07140280d400984e05442100d0301401484000224284528440c80171620180d40384100c1580741c00c4240b28080e04034051000c140804e010a2002c0c000c0300e0400c0c0f90000c1c402000c6000540380c80203591080e5103a2403c0354422f000c150701400a0841050140d5500349400c030280c000b1359580c4503103403015020100c0c0102007100488000b0703481034401801446038429060a0380f080c1a00710040d903148000c1030002c06ca500c64580102ca62464598050b114141032614503020b0102031361040140d0440180e681d80840b0000300659041c0d40740704a052251900c80030310744000b404450140c100c0c060b41800902c0003500092007212008880e40c004a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 927756591 1250 927755341 927755417
    0x50105040b070f0c0602030c06060f0f31060302040e0d0e120a05060c13060306120b0c1611010e0f0d020d14191112060711070f030c090c 60
    0x3c286400c100700b4401c402050720071a40c0002074840d6002015002d9203c081c2c0940d01c0c0d90315040100109400803180d050b401103820340c0a0941c901d040300700c3c400c01320500c410300c0b040d1002140c0240188180100715580d100d42e2040c083c000d60134a8410710000004000080c009418075540c00b4000d490840c1400744034440020086003806001d0104100d8168401c0481e00b15040144200740c032504607101e6841c0c00120b81c0e00010f8118440d00401044403152244241201800d460302e01c80000c000b4140c0c500b0600c100314903485401240e425540c0302d03014014405828815100042900042c09280340c0303d15960f00c010740c2c55903a204c180c02401c41c1c1c1202e40c10172041c51840d2805844410307a0800d01d10b13001c2d100090303910341012841d0201c054864001c9000d1130480344204038800003001040d0100350300c0140000c404900400d040d4079002400012200e1056641000c9107880701160800c03121003c8066040040c400d15008000f41901981400c50000080300180d203d0081c2080210000309255 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 927757841 1250 927756591 927756593
    0x60c0903070902180f0d0b0106082e050a140a09020703020718060504050c0c1504030e06070309181b051e0d0c020c460e0703060807050105040b07 64
    0x1c2050380000c0150180641d00c542000091110303104026015502440071508565000d1401020031154980d100009806a900304081140c841000414000351f941c0103000c40ca483d90b40c050414001c0040d912198400389041c0740a0001c0b507032103079002c091080034008050915684141d410020b03282c25610041c2c644c885070a080b0b00d440004e90021500303507100c10412400303a040da08003105552064038148580d40b1540c50300d680c240b141c620300d40003d4201d005010300b810080403000383c22074028900ba15650f524900001d41d10307408010210b01080764030104004402c05080340a402d000624400c101403a1400c80e031400804620112a040183c0000c03002c24142070140c92042160741c4032406515100c15418010080c0800070b01007015108502070348a442c03800500b05500708164000c880d010741450f010304c81170396281601c0b0f500c03403032070343d62540702014003100c4103200411804800d0049801e000d900a803c98072550400d2800750001d90040c00641d801c00101c404542446110301d82e18961 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 927759091 1250 927757841 927757843
    0x120614060307210b072c09010e0406060e1e011e03080d020d0c2006010f090c030e010c0504030b1501090b0307050c0106030b07032d02070836030a05060c0903 69
    0x461034024640d840200c2401045c551025190f081e0409600c0e07019100c44c440c02070f640c260b11040000c254040b143c10b0040c86009258031015801510451010070a41d0311048031481410f0b08540b41d1000c00d62880c602141950300402450060150140c1c601600381d00040f03900690701c4600005d0b10100c0e00284903000c0980950480300c00b150848020050a603484400401c0380c0c0211031302280104440304050b892003000b0640030304032119613403100001450081e144010b0400d240c0c0400c14190303104020410741d0420300490300d40440c944c0e1004d81e10342c00e40c9005401c00d000a4404d2001b1716100341e03241c0d00c07030342c0100183c400d8960314804640c41e55903060040315140301e500242c4040d5424000008204003a00282074081c021a840500814a2071045e40414403003240c0f05049055030344500c6036140090343e00a0455a0117448017610704040a40c8011078001402001200c1544445494260b00000c40c04074490300b10441c0035086d0914107403203141da0340401420300f40c0a1070002540a1141d50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 927760341 1250 927759091 927759149
    0xe01031b09050124031b1b0803040b010504050f0906061903050a06061404090f060c14040f0e280e0c18010e0a0e060112020613120614060307 62
    0x4040c0307014491583c48843d403400c507002031007084c41030f03402901800003603901130301a50056042010103101c0603c0c50701c42c122440e5003610301060306414041e10850205813000300842c030841c091101c81069500d0202440211070004058881080a10060000c0f041c40801d1441c3c0003a0121001c00a455507451111026407403640002c02d140304005403002000003940041c07040700c1e0f0004440c2030040c0ca000c14032054130901000140002184c0000f000020307041e80c054440d2a4091801c101d641c0a0100d0135291544540c02c028810030b401c00d0200103a90203501000c0c0d20207004000301c801200b440190140350307103090050340000d54442c2d1840300d01c0c00d030810400448000041030040841002220003100d07820030701501c02c0d03a14500c40002d07c0d00055000d8440884141c50080c071702070303203002c0e482211800c07150fa0803a480041000403620072809075110302c000c3c1080071060881030305246421011604003680d0064040f110b00304010159130007245110899100d80c0c10355101100c0e504554505807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 927761591 1250 927760341 927760349
    0x61505131205010f1422050c040c0909050703020901080a0c110d0306050901080d08041b0b070818240a021501140102070915051e090403031e060e01031b 67
    0x1040c60800c078400d0000541002d000e80c405500200040502e80201c2d41e80050104c424400b0b6000724949800d024002c0f000d00e01e1041d005030305440c112800d5800050540d1016a11000080c02e030050622041c0b11500c60355412002c10f00702149003091100001c1d001040040041111558032004038501c2c900170400201c07214140760a40f40254400380001d8000d103030790f00403c2d02036400e000010405e22000100d41c000144076445501c150b58540c0d58800545c50f86004d2001e2910301908001804c40d40b010203007030303407a12403400180c843d0041d600c23a5007841035441c0418440c3c03003d14001c50740417000300903543d401880150f005985251400040e483c16140303400044492400800001d0013003891144030b01410000d07800d4401243d82d0b00c03c41c100351080341d050700841314840e2800308624640040b50b564804200c80d0401e9841e1140300000745510340071035050380400d0315110320364805030203c58400440404024104007039402c00c4106203580324140001441d40c0940001154100c1010086800038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 927762841 1250 927761591 927761609
    0x10f0e0405041b0803040b0706020304031e020a030f08060f061608071202010b010507031b1a18071512020901141819140f0a08010f06081006150513 65
    0x1400d052411003d00000c00300704000ba82d07404a0085034550340402280c0c211038003441441e04201950300d0b040000c0d8400713442101441524810039034002000c044000d0b10300c0380340d0040c01900c681c1d0304024095000c84a503020420402408011703150fa0383c000c4403085c010302515010f03190f0038400d40c001000c011055002d4072075500480d50301e08201c0402401d201c030f00140d0b4004d0041402000c015501c0b03000c3c03402c0043c040f552941c0040508a920050f001905005d04000c003035840d80d102101c5210742c0c00761100d00202d00c0f26003084001030f5040000c540144031101c4000d800c4044000b0052a00c900705501040302600000d0702c1006a124604c808054085104080e43e100706062000c9041c13403003130407428000c002c82100b800071a451411450100c0c0c244021104141c90707681d04000d071000c000e980c81540184005808120030b9402d11034241c620248003400141107050001581c548110721049440350b034100f50050264520070f01108284a800341000c41e104c10400301030010b900d6a6401ca4141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 927764091 1250 927762841 927762851
    0xc03030b30030702011b08040e09010e010e0708070605030a0b1002100605041b05030a1409010b011803030e060f09060a092603190905091003031101060e0402010f0e04 73
    0x10418012900c01c5888881200e030490340001080700707a442c0e004504010b804592040e50b00d81400110f160501901842202150301d41922a0000a9000019216118a60b40d01c17802a0b1600d40c0074800c608481400c0001000c8076481d01c405180e403070110380945000c114001c00031441030007154115181d07820009101c03043c581c11048009548807240c040c44a02c143c10140c0c0014a8240761040c0d607100f044240440c410194162001c4d00c4e503a01c0a010070210513643c403100c03611210401002400b913560b01d000800c40b00e654800060044041d141c4104000428075810400030350402040300c01000182e43e4581c0324000710b00c1d601d8840c021011a1a00003d00051340240b00358041c103041d00b6260010fa43e481030105054000b0480c03004a110203080d0340c0104030480c14688015004000c202c131500e000007250f81c60300040748072114156200000c820040d03c0134020540c001302100c52174141c2038000c01c86145050803a01c2d800d140504081c3c10300100e4031304510894032402403000074400140082c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 927765341 1250 927764091 927764119
    0x12021804020f240d050405070e0907060c020f0901090209010f020319081e091e1506130905071d0f100509070c050303070e030c010c05030702060d0b0d080a030f0606050304030c03030b 80
    0x80d060441c6e003141c0d01d001c2c0c031754042100002d41e91224020b80d01030300100229410300c5030907110004c100700c00b070364055600030107030a0540d078800380d0070301800b80d510000d40c49000e04030003d07150b0800c0c00302000c00c0d90000d200c040c00780b04048070b4404501d49245014403d54480c2654101034440755010031422401e00301c2040320350070001944140c41300b0101200d01d5004020f84010380c0304c0484904411500080d800851a03910307220702c5041a101c08000001070f40d58050b0f403928580300d165486000400c03407400e104400d02c0301c0803640607800380301c4401120003450210880c80e221082400b038203110354400c50108070b01c10302c10550701e0074082e8041e048903943c1c00c103e04d0140c000c82c0c89002c1031b4428818a01c2402c1c441d403185003064000341d0700100643c00c0c52000d41c00c001054101011419202c0e41e51a80c0750076950f82d820103000140d01034941310750798001140c401000e60b41c26100b290382240c1400c10801080303078403808032a030254040c43c220280340f0b80c0e0300d0300320094080452130b141e002108944e030f02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 927766591 1250 927765341 927765367
    0x5130b1326040f062c040b04090311060609160809120a1e03150e090f0304030c0e0c0901170612070f090e0d09270612021804020f24 58
    0x1558807445000c0001c80e540c040c00c070340c1c003242c0340500c10385c18242e0701c1c42200380c0341c044a040039258401071012900445039408602165540c01c820303000143d1007010684030701814003030107403c030006031225800b914003013607100714040d0703100014820440d440d40016401e00c401d110200b08a81030a18054ac1e900c0c12003002088c0740036a541000c0002101d102030000d03a4040d20030400c0d5542c441040c1c4d0b071103600d844109102004020202c0480b0301a81d4405940b407141403006101a500c101c8074515002e013415000e0760040d80080280f40c01d00c50420166405a800c900130f07007055245501032901540d80d5401040c2c12043c0d002ca00b8036a032068110101e003080c0b0080e002429075500180400044112040c5142d4502d8006440d0000c00c50740c1c10244040c0c104884141041c079060503040c00d000815900e031030301b26291a8404100c6100301d0400f8011481c080200b050094544004c0e03c055003415000a80f008800400c2d46100d543c020b46100807403007129680c0d4082d040041c030303a5521751300649201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 927767841 1250 927766591 927766597
    0x10b0306010323012303030a020d2606090a020d061715250c12020303100504022a0a02041a100903030e1e0301020307020f0105130b1326 60
    0x310301090900012000b800c4402d510f4000880c81e1000e4540d0b01e03440d240c030802440006600449102101903503900c01a04c00304014891841e181c0d0043c0390340c450703240005041c10310308010600e110450840038003038148100c0e145500943c0c100c4400f15942c4810110200902c034921500c45107078285140060640001d4040e064508451780030340c0d0810408160b01400c844049500074080c0c504086602071415601420945c842c5843c14640c040090301d444101980c0703d54601500140e20000400128502600718ad42c0142000d071415404c1c400d0485c40c0c03012000d442c2d100a404c000b8180d0035a070710400104040e11505030007600030410266002d54030200d94000112240c007600401c0301815030684225440011203415690740341441c0389100030480d01a0b402e88208203020301c082c40707080355a9428802580144c80c590010505010500392060030f50340001d140001c0c0d255146070380e10100b81e070811129400401185000380604c0703149840d00e801040031040005040c1c4c2c0158207800702e8852002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 927769091 1250 927767841 927767851
    0xb190f0b1e091b0c10050402011202040312031a10080a0e031e030c09091501180501050d0b030f07060908060a06050d060e0f060907091b02030f0a02030909010b03 71
    0x4061400030125441d00300c400700034201160440e550100144210849141507008818100c1016141528a0034242d29081074210b1501d1019950001d1104660300051040308414030400c080d0309140c9544ca52024280540d46002c00381900d0f020312441060101e5076800380060010546512101d8040c1d0040c500803040b0f8040c84480d10740300e1a03e14550002050b40c010031440742d00d183c7c4045040106c018507820180070122001c0782404803030166601c0325821481003402419130b100b06691031000400039260744200c10959854000d0a000e2030f40e000381160521016444042201602240402d01d803500b505000c0030b10303004039480854910b9204210208a4000c00200e605c1915044190b40440d030152040f16800034907540350a000900769089032260340000c009458280940c2c00c1c07201d0810008940c440259080a201031001800900c26901582890b0011117500d0118103800381da680310341c8244c44403111000c00e503159802d10030400c4031500c00001d4041c140c19655400b8840503600290b40c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 927770341 1250 927769091 927769099
    0x30c0b09031804060e06010f14300609011e17011b0302090109090e0109150b1003051b1b16180203060a051003020f0f091215040b190f0b 60
    0x14400107285003d0042806681700040003010a80382c0c6801550800c0f0b10010f03d6080c007554803a444c014a00c6d0b080a40021600480c0c00108804920851645074000c001c82c400d202e03240340c1c01c0c08240d80720403005505451940c0006245150380c00030300040c0e05025803102400ca1850800880c1c00304c810f4000e074013a03000e1a00080c840d400a241c080d0305034012504254000359540d80100402c003001c1d0021100f04900c0400002d060049840f03240500c03012612602d040d0340c03203010030403403810040350f030408141251608128505205842d50094140307090b0486d581d100108500000c5404014844182c40c0494211022103c00042c2c2011610039807092690100c81080c403542c4c080d005008403441141d000b8030101d06182810b04000000c201e452464082503400e102200341c0211420042404075407081c1e100307440394003400400080c2401200c01803403e8014070800100c2d29909914a500a5802900940980c2e64850300855060109440010311800c114040c2c90105680c1d00c000c02d5154161 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 927771591 1250 927770341 927770377
    0x306040b04050907050a050d080d200705070608090703050a020d0c0e0924010b0712090b0a030e010b010f0206071d060a0818030901141e04030507290301030609030c0b0903 75
    0xc3c00c124003541c000501509c1244100515002c0201c2e9500240300082e2605201d88280e03510044070402d13802c1030504032140d600c5100107000c401d800107003895200b03081350300501909046503580f54840e20810701c001e016031201149a42000080300e03004000d0907511140440920f4040080c40d69440359040181d01c2000c5001d14444001c0140e20311410f80b204c100b01d10346441c0741951041d040104c403607000410040700010208050389841d00800609000c0c0d9004100a007241141500b11042c06455505110741c040806443d6a00400c4c240c1c2c6c040001d05140c02e00c1300224200b01707011040c049a955010400240c0440d81c40e4220498a000d030300b000034042c0c0030341180b1220b01c2eaa4840d404200740407811202260112556400041c103946403001507604400c80a143d1464031900103410454490f00801e409200300c001c28a82d00412881311402c80c11100e1807401c12500d24481070101400b16501e683d402c00c2414051288500a29441050102c40b460981e10743c50f141c0c1c2140c490049091008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 927772841 1250 927771591 927771599
    0x313030b06060702150c010f240b12040b0c040503010912200c150d050106050403051204031109130b1f050f060406180b0706090209071b080306040b04050907050a 71
    0x2d202540c04255002d004951400c40550182d50b00b60400f401c03080296403500e0b0280038201003402010000d242e500d00c0e0b04040480811182c00e00c0241d50030003441c01c0e20520001c0d0b6070b00e5641c3c140d140c0103a04810b50329055160315a02482c41d21031600202c0d010f60a101301c003410048010003251540d4003903503841028802c50050300c84503c02c62000408290300c640105405131502030349070f041c903028404c11586050b100307c0090056400036840240030900100f42001803007400c1c040e480080d04000354042c0341c503055540e9407014403c50400f5a0040060354001400410900e413040303682a0003084107400c070701e0441c50302d1a440407002c031180340c40d81010780e0014036810f00300c455046581c001003500e4209410954211401400e80000765160560440c0004503d4091305c01401100e001c0e440c0414900c113640103200c103113070000d8180401c00610b0051188121200c0d810310b46401e5100300030f641c1c0c980369000010003808000821641c898503000071720100c0c010026800c01220750a40b8910402035039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 927774091 1250 927772841 927772849
    0xc0308090906030610090c022d0d18060f11030d15172515050a18150e010e061204020f0102060403020703060908041d0603011a01170a0204080313030b06 67
    0x410781d041810036217081000d0101030510b410251703981081d44102c503c61a504c1c00700f03181000c51408400301002008008284004048c44011140421400c0440c80022025809846a4032a104410400c0b01c1641f8145103244035008050151580c402161f0b190113000440e60018000c00696081280b4545000038110130f07014510300b640704081c40030b00f0091603007912040400506490741400d0701034070741001c40c2c0e0318608100c85030440760556a082e190940c03000050989030300d46a41c803038205000002005401c0d042c0101c0612000340b807801014007aa0f090058802003208052075501c04800300308820044010f81000c1c2c490b9000721070b84c040701840300005a0b1200410b44c2c0140050b00701c1e66090000c11102c6c1c0100116038452a1440d10381503880c1c2d6148001200d00d12490000d118035028420146003d0246082e0842d510340a404030b62460381c006807024481c0511203034446103890025200d8051175058400034080241505c2c0c0c2c540d00522420503040450104030303943c155100c082840d90070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 927775341 1250 927774091 927774103
    0x3100e0c030f070f0512241e0103022214090d1e05030f070915030203070f0e2b061b0215010e18010f091101140c0d08070c0c030809090603 61
    0x511341c01e81c1800c5508010a0120100c07819442e08024822080401c40d541c07440600a56255030500c802c0201c5d062030030358148004401c5003900303a0420005c0060001d40e4905203004100b21025261010200d1a1a22500a01004241e851b8403c034600100103086a0101e480c0002c0c11266a071031001d0441c107008122044814620031000404c24800540002240e17000c513a004001401d291030411390341c3d25828a9008801380c400b00198011041c03010741a04491285070058450805200c22400c40c004a546941b01041401d22141d60202d02042180e060710342c2004680c11007418408608154000103903a1091121280103101c0c0c14548207801c500d10300e005060700d0300035000213407030384404503c4e0b140b012a00015070059561800c0601401c40c0c184184080148182800c103c038544e030400140103000307056140b510004003003207003014041e00414000c10612090402d81025101e003c011942d0382c4c01030b10b0040440d00d1912011040c0403010020386002c1c0401c51707030403800741d035240c0515403262 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 927776591 1250 927775341 927775349
    0x11010609020316030e03160c05090721021b19050c0a0f18020d0f060608090f0705041d120408010b0a14090604020d0f06031401181103100e0c030f07 65
    0xf090646020032920a4114014200e0300004983c2061059006105242c6003841d046415503072902c1c00f04568105104500d60010ba030341452110302000d80c072001e8040d070100c400342003e90360001e5041c00d981540203010740928010411140680c3e003e00380c00c03407002d031404003e0f1154810358014800310310300300030705000352850700380d100d18030f00e182c166614100f0505008007042c85800f8006005169030b1403007260403012507054041009407410300050001400a0003081c0c04e074100289480c1410800276644c0c0440301c09542c0003d00c0007000208001e000465160820280102200504000a0440030b0015501c2e0a070007008051685c404002c58507809208000e40c9031080c6a5043c254503159414540c0680c0242c0090b240070403d0003068102d40c4210f200d8801280c0c0c07140240f003404a0302e1100c0341c04914140080194846180e0b038400c140300111001064109880802c68054400f401117801002031031105000c62040102d2040c0c03036118610003540603114108603160500c0001490108403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 927777841 1250 927776591 927776611
    0x15090f070302130e03040e0c09010e010e060717091f0e031507230a020304060201110c03030105060307050f040321021203160c0506010e010303120c02070510020c10110106090203 78
    0x804042e1484080c0103113035150005400207000c002a00c441074050640b003005a004415955000c200002d010614121902ca04021064050112940741c40048880e0281c00c501203207201c05541035a01414481c0b9000144c000c01c07684181207400040c8001415003010948417184410191400d145e5121012180d2448008042000c07502c024011441c0c10f403280100c01d000d07d5003000c50f0010140d1075000c1042c0a006900c0023038100300181d428401d0080000c52490040e00d0b00c0c000300c1d030040d03032800103000342441100000003180046024500f10fa08048504d0f080c0764685035282044103035071991120b0f510a140c1c0b0100c16003133052001c81d2440071034804c10075007400c5842d100484a01600e441048000b0b00400c02c0c884030228000b084454000e0181d000003503199811480c0003072440b4510703e200c078a0b080c00e0840c1d80312040c2d00803400d00e00f030f500e003600d0300c0915900b480400c034604000740b00b01d42d400c02207460802c05810750207200c401341d15035070100030300c001c540e00d1407004203d00c011207210004c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 927779091 1250 927777841 927777859
    0x1211040321021b010e120601030308090d0305060307172104240c0308060d0501020c100c050a0206150409080d050a0b06131a0f03010f0f0e06060912070815090f070302 73
    0x184d800703910001c1c00c45002a211201c0400d0030b020845c50300078283c00c01d402084e00a004c1140080c0100846c0324000c006240078091424000003180c0d482a041c00f07001c004081c84420085108420015030703078140b661407801d03c11026101c403003120640c040d008240c0070072f48001c65015513038580702c00549088203543da44ca03000100d41c0c40441d802c038005080c1a60040481c0180c0c0003190090000d07040c9080c9031405401d01c644881c07681411540f43e881a4014450244402c403a0b482d0046119030348100d240b09038141e040040070014005005e0710b071006041450118104c88803803515880b5900ca40c0c10038004011800710a0104030721405105050790003201d1490050220342c10002d210030b5403105080d005070500340c044030485480d800c240c000f00a00e000080f410480c0d4910854070070020005009001e0403401d200c800304400c0c0c85003064290160054030a171715a0003408100d510014056141507a951240044180c0c444200c15900000240718030450480a080040340d50300407a5070080603101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 927780341 1250 927779091 927779143
    0x50901050313020301061203260103050715050927151c1a04031809060f09020315120106030b1815090a0605040309080f06070807121104032102 63
    0xe1100282c0c102d13013654849800181407003017840306403d418401e032610003102c0e0000d141c000c044401e03403d0403914029800010000300ba00402c034103007901d07100000d1240c2c070710607403409036000e10992003070700d800856040e640c07648800450011010405188810510ba44170750300c80344002c485101d200f6a001c0c149a400d0900c02e0840408034402510070709a1070403c0010340c540414002044805801142c80f240a8071040c607805c48041c1c014040401c001c11590303050500d11005111507019140e8010350000109001920101c000a0840e80050a200340001d201e02c005010301464801195080c0211000c980c013051040100400131111200801c0554109444155a110042c0410500e07008170122440400c00d203004e15813007140a0340b5032114051500400f5071816102d400442a550040340a20403139039070202031190000303120300c2c10182c40003100302114001c1120901e00c0426a42c0043c0010400c00061107076501c1903401c061100040c13000c8107050382c40b100000182009032140030040c40b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 927781591 1250 927780341 927780361
    0xf0114030601030507150212040b030105011103120412120501140a050103092d06020a030903110a0f02100908100603050d050c0c0d080715140618010e220f03080105010509010503 78
    0x204181d4403441141d0b2540343c10008d80c54561310030303004440d82100c0080144401e50300261510410140c41000314031307105620905890100002c0c1004241e05000c00b56948414401c540300600c0d0142c6013008c101d0340d65200d00300c040d40c400810b1140c0c002e1039007941c002074940c024070803028003e41020040a045586a908441500d0a511641403918812400c0008140c0e01c2c07014000e00c002d16240020342c40003600b0041c2c8989618003054ad5079070b01c95051a8005101c8a0800748469410342e64805401ca4511017500e646078182c1007488a4072940c04011001105a0041e40072039005005070b41039161040380c100c4031782c81000405201a440058204d0842c10480c0085950305e005541a908042c807582d0b0711441d4894070b040340f40409881e09603441c229103980361100c1e04081e08940142c0250304610303144120300d00512079003442c4404138000403052501c1080994206d01c1005594628040501d444040c42c20442c1094000a038040300108055000d00100d92030010140c55850031580c03001021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 927782841 1250 927781591 927781619
    0x605070f080702070506182407031815140d09061a010215070f0341060a120c1a130f050603040816051b1c020108130c05090f0114030601030507 63
    0x1900080442c0e004880c42c06a00c0d41d250302c8e420800c188607174904242c1001003070381d0144205941c0850070903804204507001540302240300b24481c00c0001800f0005101c000981c014540040c0c03010b41002003070b104025803544038030283c031200b000d44104103c0b003c2c0120b030396403500000c3c50070042240c00400e40710750044000d102d00f01c5242ca8003144c070712540110f0310480c44056001210140c4001110301c1d00c0000182c44001d0b2409000101c801464040c0009040010310b2081d166102c142107080414071498280c0c1002410000b00e20345415500a048410756030f110398010a0f0700703454002c0104581c00300c14800300846500422040c11502e603502e4024440d886010f0789030b8111880d0440324001403081c0711551a091200404041130340b03040c41030100200d1f6044010418448604286d801030380c00c01c10060300050310704c1c505c0400280e40d1034441c40f051740580000358040900000c200311158240d42e40c40c141d851840c1c500b05007100c548103065640600780030060241e04028030610564901c00c0355 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 927784091 1250 927782841 927782887
    0x130902030c162918150610090506070309030312061d0612100f0b010806090f090a080408030a17040f03080907050a090e0c0d0c0b160605070f080702070506 68
    0x81076100c0742c0c01581400c01c0d0041c000d625601200400c025840c40560380c1049404c004002174030132251402000810180c0051441e07102e0034104070300840662060007001c2c05007001505407030755030791203080180501e1040d200882c0001d225480e0108038510501886045865990080c2e2135605005080d58040c0d000600041d0440c1c41e900e50300288400401400380903c035200030000b098071490700100280c0d0030000d24241403010030000c2c88100d4980342602070f403044079000c5440c115194010500d00344900550041c00c414004100480e06010101c000c2482a60986035006001c20520091024550845025090aa80c2443c48001c03900403880c003a48094030000745c1c1c05203620f910002e03914071641d42000b000f61b696a00c03100c217400010820703400784c808202d9003034900040603903810664480c6400352808600c40850702511040034080c4190701d9a0340f110007845640f0f401040207150089082107240003942100c0418903a80c00407802c8801d445015000900e0441c0c40000f160a00c030744044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 927785341 1250 927784091 927784103
    0xb09190807020f1f030911010203070b0105150405150a1205060f0d0203070911450d0b010e150a0b07020f0d17070b07030605061c060e0c130902030c16 66
    0x14241159000020b00e0f120130740280c07400108001941807070b80c50b240100d11a141503520070010640800c07000c060050442d682200c139440c0024041640b80d11502440e408650040d035000036000c2e616690b00c003d461404d404c0d50b5130154800f6560840019510107981058204682c16413841c6a81451001010954006022505400d940304800c0040303920a000f825441d1001207083e4034015000f00d607821b5440c0b04081c2022807007030515840000341010b44202e0044841d001541d010340d4481c0202011517541000e900807a43d039494920380c50307211045603151280c07003078440c1d038603801c1ca0004022003e035078030102103a082900590a01c402c000b0007603178540d4000c1c0d40c680d04c0000142d00080c80d0701ba00701c148584548942585c58a8a502400034103c0d00070704d030800c1c0041c03082d030b125030302619000b000081506000407600b800d007000500c000c1d00300161040000080107282a81d00004010390390008840d080c00340e036101102d40403804244c0782a41a58030403c1000f1240840c05a039280c1240200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 927786591 1250 927785341 927785359
    0xa030b0a180c21050d0207090e01050609010b070507180e0d0c08040501180819120305010303020c10050c07081f02090904061d03220605030403080115021002070b09190807020f 77
    0x24581d01d01c5c1200b108401c0d80140d0084a00b40000020ba00801801701a0380009202c6810424000b594501c01401020304400012a850342408002c000f5000144192568248400c04820000f40603100c021400102c030b204044440c80361600ca440d001b143c113900f024680381403505000044402880c0003443e6840f4070071142020aa0010602908600360741490410742812524603107401074810701415101410319041c01040400e0300403403588400c0d1001c48021a2411402000f03070350600411004038168810b01c1408260801d0000d81c0202024950880109504040c0400001d03881201541d9070824040b00220f8009101900015921010805204040040440620b2540c1c006950401d0244880c802181068600c8461031028242500e0218550714250310041d02554041c46155111484081168461403003407001d04aa22181081590703a5816400c1c0700e10102d0f0140e4801256004500450301000c0150421907881070380013240710b0905015808104a045121240380d4220600c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 927787841 1250 927786591 927786593
    0x1103190f0903080418060f0e0f250c0c0911070204150b030c030f010b18012a0b04060b060c070902030606091804110415230a030b0a180c21 61
    0x24400b600c051700200d0980c0d445040e4240a21058811960003215000d002510501c185900460940e5000200c90358009a613181d07000d03103c1c1c81c2c4000b00c3d07101024403c036075480031034603601030042c0200d2400340d1142c00c0350a44401c011800c40d007006804451885003008084014100ba411615114420454400455545600fa00082c0e841102ca2800740440002007151050700e0f40442e81c09005c0c4001e010f41071020650302c0c1c510340c0c2c08030000f05051180c070582003410f01d0042d030048071103200351704004190a02180741001500310140ea0858070181040300800711410540203860b4624210001843d5542c98420752030000d5001401090b00a0010082564540c446018050202268412202042c501400d0000160040c0018184210304088001d012908124030a100790b601c000d16204030280441100480d680c80c00d80003030742040f013450f0000306100d441e0340e03070701e1144036180d10078412503001004051611204440040c14035041400910100d02c141c1d45001403040103a00600c111246 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 927789091 1250 927787841 927787853
    0x17100e01080f0f0303040213020d0f0f0b010e0d0c050d03090504060312020616140d0915020a0801080a23030702041b0f09080304030f021302030a09031103190f0903 72
    0x801d8204803110b9110601200b20248100692008005807401550a6040c564001403440781d145d180d03010900e401007003190440000390b108011a090400c0c0404c0050441c1ca06c58014100611880780480d50b00c0d1032181a50070440740780d28003280d00214122201e400c010070070010b0f131841d00c016000c0040e4a1030110f115101c500c6070f04d0195000f4100c0300c1152108240080c0b629000910022201c00511510383e403881c2c0082c01003105103900010591a42189000307070303009203000769000e0007101c2c503401c101003d0b8000740c0c010b081000a50b40d52072266070326045440d40d41c00d41071400401410001c1401580c445500180340c012000030340c01e882c078054a61300040c081e038400315030010b0b1200303a0503110507056803c0051a03603e0042810095400344c82c096a00c1d469019500c005000a03024440c903e00310341d82e031205070500c4013020200315200d0502c5981c8200030a0012070440220349110f036500d000440000a1f40c4d0010340105c00c03580300c99192581291951603403038106060000442000c000650 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 927790341 1250 927789091 927789119
    0xc0a110a140319053a060f0503060f01060c02191d0901050a060518060103060b071a061f03090201110a060b0301180209151c05010f05090303071710 65
    0xd1440000c54848640ea040043c0d101d546168040a000302085029450650a40d203103c561804040e418210030a0207658a01c01202c8070400001c1c52138240007007104200194181c0660728154215011680d40020a02c4840403c1c001c0202180c0103640c66801817814148910050016074400f2504603940c0050f440149051000300320107502010401c40d00074804d2085a5010380807101c24001d903490280424403640100c0066122031064400148440e402504198010709400304600e641d400d8074103004001429444002c8580c0b000d030004110180b81462642000100c81460010820002c500a40081c0f4202204905000494040982c400310034099141ca141c00f031b0002290385480d1200301821a40000c103501241d039034404550001d42c56944040e544020400310030740c03060a130130b000900805405a60302c3d112048811400d020000f041d040700c211a40580070a0250707071104128a512030008a40003000120100742d101e41e4500f1003a859600300079134485591405480300c226a503240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 927791591 1250 927790341 927790373
    0x90602120f07110c0d0f051204030804030317011a180306130b0612032704020403032624060904020a090f080703151a030105010f051203030c0a110a 65
    0x5210208101c9100d4008034071100d0410440c02500c5120300709070001740c0321403c941d030181c1000a02940507080000401044c282d40d1032802455480319501d1602c101e06c1d038040e000c00c6001403044468061091440c181c980d05a4a80308500d15803a00e40342640304840e000340b041205410404070110340940c500341300c010300500c14611064014070480c00c10300011000a00080d0180b0348440d04141080c40c044180d0f03003841506c58450384a01c40c031100d0b9043c1c441b0840840341e48144000740001c01c15400869007a4440f5090041144000110b00310402003402200c0d6184490204000920200e92500d10b840c40707684000d10403400c0c80c2d000804034080740c0016051038040740c000769051046000c14528a002001d02c0b0004065007820b41d500e5403400b110803422548104c0d1a1040248070426034403000003131f4107014000708810340e034400d48601c1d241194400c0f02d014005004020032042d8001c0101d03442494130101301d03484e001040300211000d002d01c891940d40e038011035040c2c10000c0d8000856034441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 927792841 1250 927791591 927791611
    0x30602040f170c0906030a05121206190302060904060308040305010c110d09050108100b0703170106020c010819022106012c0d08191d0a1809060212 65
    0x3860900500400e06060750b0030900c4800403004200c40b480d00c0001d0b00111a40c01903802c920585c4a84020a14045040c480241a40600e003d2102e0350035900300a0036a07443c0c0c10f0580c1815844201c00e0000c840400900c15410020303604052015060560042c024402c01400004a040da00e0b21050319903000382e0021181079445910000da66139009821060030844000a00380071004204054491551440380b1418803082c40c0003d174408051024400003003486900c41640c40c561803a000f03140003600d800c0010f1488a02002080c0c0620010b640d82d086813041e103e141c01c0d5203901064560030381001868201268080002e0300085804000304084400281030040581c10504005013610980440703660505200d0000700c2c2d07125409500810851300d041e901d00314146002d0070240021310420114051221405a181040355440842105880c4160001c440020007501c10032140000740c1c840d488100c0c00d0005804d01011581d8040074a00c1d20620005261206e1040030400c1c0d090304071405820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 927794091 1250 927792841 927792847
    0xb22050c0301060b0306210a1a0f0f070c140304031a071d1c050c21070506070c0506130807030b07110c10030c030f051305150c03070e0f0a030602 64
    0x101e050900401e009440800e2155055260440101c2c8008559448143e290140c000340801c6015090045407540c40e00a01e0134007800329805248110035a05480030465200c11200050540042d24000c41c0505100e6881500424040c5c4a42041d01030a51401250b40410480000000ea003092104201c0282c0355401105140041c0083c154051b80702d02000c000301c3d000c000703010070381c0d428601904c2c00c107454150b0008201d031400d24a00c1d081f000001c40c0e41048403001f005d0321246000440041d0120700d441218052178031350050120071b02a2600092045800709014003d03403030b00c2400307804a068036402020606d0395981c03440e490000b0543c41518400814004c1c0181c29038011010b03004e540706c103002000c0c4c40b1940070103d02940307100c0d0041c904065039000100b80d40342c840d8100d5210000445800d00c441d0911902407419140c03946000c45042c0f14103071401d110403400c1a5068440c03900c10454509564401c04261150a8683d0f022070b0710402c212280140b55031540c0c11031020394040c020040c0c27 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 927795341 1250 927794091 927794113
    0x30a0e0a051908120f090904030e1306150c1a061306060f03050a0c09140d05070e22031d060409290402042114030d0506180f040b2205 59
    0x1007082d005504001136a4010031400c10041d552000b01c2d400d2080030340300d0f00110ba50f2801d00b2203a4070f1411400b16031000a001e01c0b041c08800700e070491030586a660742c00e45003000b54400242c07003260041d200200756aa411303000800500c288103480c0e03444603002c0c1124680451180c00c400803a15140c03c224003141034044818561a45071043e19801040510300b00230310f011541c0050446403440c0310741a4401d10b8600c2c0c0f4101a103d44a50303c1e0f034a540b245c112806c1e6901c81d0809409090304460290303003000251403904e64983d41040100f03005406848281c009032149001c860303400116041300340c1049080000281c01d010510135884000c59243d0352050111242c0410b0704100c17160080c403846240140402c2c0840c05d080d80100701c60301030219048000c0122858a819000c1c0620780080c820300020951102607a10750700004d1107a042109c101c4c4403000d16056000094000381c1e00c1c440355051400010740012480c4d20416001811055100c648013903540d50f404c031111044000701d5140c2c003d566524 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 927796591 1250 927795341 927795343
    0x40e0c030a0b160c0807060c0315030b06090a14010b030a140103060c1206081b0f0306040302061009020712050c0115120b251b020301020f031609030203030a0e0a051908 74
    0x7091501c800d1405680030413994841221034000c0d030304007a146d69aa580c840031711a02a5002d007600400003411680c1d0030b0358038242803842d2082110610b0148504500090003050948100c90303030040305900072a680c0e400d164882c031042d0001440701980d1039580110035002c104125520b4021440380a01040c201c0030401c0062425002400c841e0031242008410300444901065a100500ca072241c0134a5011508000824200c0342d00d05154040c0264802c0c481850303400b01e4281d2042848030801c882d007540e98030000d01288506200503000b04c400c0c007000d00d00644074400404405804800200c3c504100340c680c0102061a58844880c0402503d800c508205a15003520792007081e1b41d030350f0002800c1000d4140c01080707401c48100100510302c50504503601310310100c521000c1d0040e00071500c40ca40d04140c2c070003e500c01d4400000d0100440308051025118082047c140c99018000e10708001042c0b80582d8414103100303001d07900c106800c1012540b82c80d04080b41001c180013040203007a00b031900500c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 927797841 1250 927796591 927796621
    0xa0308221a0a0f0e030d0f021002040312080112020d06020a1e020c1302160206070813181817091c0605040318080319031e09030824040e0c030a0b 64
    0x1000d00c5003085a2401c69540868801ca00e400e0604100d1f0702103204802c200c1c02c00e1451507229103528070124012050140081c40a01114515268070700e941c0d8840740c03030b41801880500029880051a0a0100045c25a801418000d6510b0038822801908240d0820440380c4038208400141d014a4038440342d4a0000440003c52580820440c641040203840d0098081c024001a02804000a007c801c0126807811a00c202503000d41d4440803a0320344c411010704040d8102d240e00c606041518220200c0c00c0c0500c9080c03155480170b401c00400008040d62600c40c0c0101c49000c1d848207514115254801c20508118581d51240c0030000c2d00b840e00340760203040b80203103503540c0240c2c0c500d0f81020701943c5400011030300c0214101c44900d00801c24604101e025002002c401d07903002c0359040c45010240600d400446100d8420345400800b40e4828042c4103540d410101c400f550b055095085080505183d800161510400015121802105d0000c07034940034440310210340c0020443c04000d0000c10007441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 927799091 1250 927797841 927797867
    0x50a0b06040b0312090f190e0f0108100e0708030d14011d0403080c070c030f0303110a020304120c080607080a0624030f1b050403060b0a0308221a0a 65
    0x810111541001103580d42101c4e503400a0710240c0050818200d5850401104500e40000e2500290151641c0000a08840c03880b032a41c0b10f110800c08190301440100c1d400d41a05d03083c0005000101800c0000d10280502030780c51500da019503480171500103800d01c0145a201e05560001c1a0030000701940e00203c10140d2084500100c1070100b08040c400545001c0e0300039170103241600c0e864440e450200d80e2032242940060103120384a00010401140118801446009443c200f0080c0c600d43c05020861103034481c1c07240142c00c104800e000d80c0c0c02a4101c145041d01070741c014804540c4586150f8503100d01602c496000c68203207001c0040001843c050f43d03002e0560803a242c21404602d00710200c2e00c3ca03c0441c1c20303042c561502c1051900308e80540c0b100001c16100540d40d041c13426810301c0541254414041600d0090a00d04c10390014100502c1d0030307003200d5002890b1440c1580f2540302d28400c146022521030709007411400002c81d40c800303284080e011500c55080e50b40e02c24960b41c000e0039100035a21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 927800341 1250 927799091 927799099
    0x50c0705030d09030b040c0b0706060306150e061311040e0612010c08071b0b01031b06020606060f0a1707030b010f020105041110031d0a050706110a1518050a0b06 71
    0x1820310b081d03501180d1902204e6100c10340000307a4450b45881140395040d42c000021002d8042400c00510882d500f2030303001c590007a50104105030302c201b001600e0484038060107040c0801c00000c00e4840c00c0c030b40c0c10052450074a404c0000c000540c0c011880715680190700c42200000320005126440c41c1007101c455400440344020001c8252840d80542401c50050096041c010fa05500c480340071400c01060244c075601100c22030207582c480c6003600c003076181041d0100616450b40c0000c079042e4000a040da00500d0014500c40c100280920074a43e075070322240c151005c20100f105000000421100001d024544170386001ca04140b0000004004000621550302103a0401040c040030070901189900c04810982e9031b809154140c50b41640501400c0102e1061042a208000540c0c000031940c103400500c41c1702074580352a62210121018200841d2022490b08580440000a4071700800a04005d072291400724425040041600100f804132200707070348641182010101304441d00e0209503100104072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 927801591 1250 927800341 927800353
    0x103140f070f051c020a1e12060f060804120e10230f03240310060e1b030a0b030705120307050c01140d090609061b030f09031713080a050c070503 64
    0x801584c0c00c403108003040041079a0f00083c0040100c5c8682403007000441250f4020848295007403008088003012401108002d00d0210301041050144892804489195440c17604585035074aa130f400040080b424030701800f12103500c1614540300c29411800d4807010b5215074145c41a0780c0c5c01e4070082103a6003181160940308008900b00840c3c1c42e41034940241c0350350980082c0200c100341c50304500c000740c041e490b403501c501b08070400003e60301c2c0c00c41c400303442c14181e1400c5161a002e4100b0224404106d015411080c00d000203861806280d0000e08841300060071552502d03501c001051240b86609402c0d00c107a0400a8a901031110402200d20206820720380b02c160285011202e5003e4010211941c0c80ca030340380d51074503044c0a03090300108252500322608001e07249465401c10380c052912280040400c0c10320014030350b039840901c10545a1501502c07012041060000c0d0f86213600e500801c00f08403180014644c80104000038058003080c0f64540380d60355a5140c01402c1c614001813a8052403180e030000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 927802841 1250 927801591 927801607
    0xf0b011407140f0d11030301060e19150c03261603060504020313021009050906040506010318081b19081b030706051005010c050601050105090103140f070f05 69
    0xc0050103614504005009072a03401e5442c0201c01298481c404a18a02c226035030700800d0003000c569041c0001054440c4011908501c0d603090f10380c0000d100c3e0300c0c0803c000d1014068681001900121000c249039440652940c589480c080e92041104280001915001f601410590801484000a0b41c04064401d0900202c00c490111880043c9041c1a84084640e013508203400b075007001c406420024815034992821080032109044600c009900c96840c1a40e05102240603501a000307584000d004002c050352030b481400040c120103010103040540d50741d01a024803072110002c0f080c4c01c2c460803845949019440f0300c840c3d5181c90700920011604502c80c2c23418801c191605140010fa400098541c4078221040107904041d140300e2007086130b000c0000c002e4100700240c0e10041c42801182210f10717205031034100440700c001241400400a612840041c4510343c020b00280159050526000ca101c111152042c0710058040d00c002c00c1c0c2803100c00034001c255411001035076140c40c15103040f9080c40300e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 927804091 1250 927802841 927802847
    0x5130503151803070c0305030901081f1211030607170a1e0e0a0209011d0106090302010e1909180b0a02030c1e040b0301171e070608130c0305100f0b01 66
    0x501090320801c04003011001c081010f00549040c182c010350080780e465542d041c19900d2354000076071580000c4030f400000301c00c001c61500d8940c00080700b5184451072814110b000300300114200065441100d02403030000981c0d4104507181c0700c0c000983d44d01d008001004d100b000351101c0501031024250a1203a8007501080b412004100403051a04c00324600316000e24403410540307604000b0750400b61040010860403501c1548646ca680001000072990380c3e1040110303207503003403400f00900040c0c14070178890041ca007500300000318084031103c59074040d940d48414422a40192402c401d081604c49140d01404074002510f51b0002e0890400d40ca180b0b0301015400c560b02c00c2c1c00300d4007604a0900c1c4040764100088090b44e000d06400c02c5407641e00c1d6124240d41c4d540a400481c000100e1040c2c0181c500c80480d03c1c034001c40305216180c02002214104070080e00c54220003007200710066002d000c0c01c1c0126005040d0440210f0160340a0440180044440e0341038541000308880214242011001c46980c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 927805341 1250 927804091 927804133
    0x1829090d0215090429030a03090324150306050903070f080309011e020405041b050406030f0905070b0307020d05030c070320070303030515030616052805130503 70
    0x64111a01011141c02d000d5451150089280c0c007500240307050101c2940704072408803c1d035a041c1009100d010000f41d8410156200c0c03918000a0006002a10410005510380d14400c120000781c0c04195002c00c03070135001c0d811201d0024080540c0040e40c14100b0070300c80f030382c440c8039045140301006c5c40c540600360b100d00d038604501c2035004254110010002d00500d40a40c404e0040002a07001c01083c07400e1620403401a400600585205501e02514402d9103100d01c03922103820110b684403a0704081c0340450a40044c41040c030000b40258840c1003c90000c1c0d42030205002038880c004005480342042c0c03100074a8000240007100500100300240500d411000060341c201039032515281c2c10060110398102c4040320b42d40f10b080f04910a50f503000c0109609900414400d610b22000768018200b400c00f0159240c406840d4103070f0f000703c5030074410f82c514443e1004000105820005c0a00b41044003c8980522020620040003c2005c604006100990102c0c3c0e801804100c6c010516003001c0b04010b61802 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 927806591 1250 927805341 927805343
    0x18041e14010f0b0c030f0310050a05031b040b04140f07090f061407170c0a03030b010c020901030b0601210b09070c1e060b190302040b0405070206010e071829090d 71
    0x820200b00030399139100c1001180c0c641c40800d01a01e031207060100704100c00118a02989216000f01c090216150800050307052650002c80c42d8006542044000d020040400d0150182c2042e00d60700b890160010f5049854001c2c14800e1a0210f20314200030000e16050180d04103074000a18404104074140c2d0091005d074440c140e4040705a80c41d8001d01d84030802d48000c1040d0342d0052800308180000c0034000c24000742c0103003e0f48052164a148034011609201c403030000035400046680103202042440701c2456129406040440e00300c4011050b1001c0d10054900c8603084903118030400c400360800030300d65904181c15043c0700e01680c803c0d41d076582c0c3c4164600200342c090560500240f06000300c58000f10300d80301c80507140040c0d04001142200e0f03c85401d01050340103a04044503070310103040c1031046501c42c1c48140c0c080c000030390030014480c45045025094408016001c80581d06000e6000a84da00070028683c40b07110f07100d04217903804d0030b0380ba000d5100403050205004102d40c503111010280117903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 927807841 1250 927806591 927806609
    0x30709021318020d0b01050f1b0f0f0a120c080a180308041202183706061116150f090f060806120f030403020618041e14010f 55
    0x910750909044440c401590b019081c0702a0b00c0e050742d14600480d500800c6248142c160900513205a600151820302c140c0c0c2c81c0031810390042025542d4941d4045002c05042c05c45000d031125034040614080c82c10090640c4081c5e25003000036000708001a06100100c41580c40c288035005160703e8840761014050030039005e003404400c541c1580814011806180a10750005180d07469039110000d2200c81500403c2c101d0007104e0503d0391082082c10007400f244219070000440414289114400490725006c04010b04c120116100d0346943c4881030103164003401c11a9681507404065002407480c1c400400c448070081070100e0300c20301030f080d0780302400d5211106500f0041a01041000c080b5001c03a030a9004503000840fa078800300c0c01c15030002c0041e01540b021610b844c048110b15403069120190010150155402000300708014142400907201d07481204541d1a11381c010b9502280075140e0840401c41380d840704491040200e030b0306218003800c038001d8058001782581006240680d80074980250111 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 927809091 1250 927807841 927807847
    0xb060f3a020a0c0203070801061818020105070f08070f2a140a0e09010509062401030f090501090c05010230030c0c0d050a0e01050304080901030515030f0a2003070902 73
    0x600d01540061800c0382d4081c4c06c072841c9a075a000300500800541c00303100c0000b04020100302c1212941c3c064444d0329150b403c114041b105165005603050350184408640e0160038011180106083c04090107100d40280412400c82003d8a82030b401c0d015003010000c9000c1c80000390800e80001c01c03039950256001481d064400503038010000380c00f100964000c00b039810b40c071003c101e00c1c004103420490007030b10305908070782440e112403d20031030380c5541c00c01341d9002e0211450306c0401c562080d04094010f00000e580041c00e040503440701400d40c0c8040e401a40c10b1100c4003801c1000d940d041140365032468803c011208201084105403642c02c03014800502d116601002003090018032204079842280080201c40d00400034400c007034102e420a021040c04101e00d807070394010395409041120321555114818520b0240020010340c010400035020026202c61718a81e0f00c1c0a8274200001c410615102009110280c050719000050708504e6480c240722580c00340d24031026880020300041039a540303440251f2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 927810341 1250 927809091 927809107
    0xc0f030e060a020307020f0d05120310210302070501081e090102130e070e0612070302070c05090a1a04020909130302030c0105100302130e120703030b060f3a02 70
    0x5810035640c0e842940444000380d60200c0b96000002003445502c01e0340c100521014410412603421800a40500540c00482a000039001014000c40d488600882c2144441f070300c441001002c1942d40b450308981c1aa284900c41c00d01d0380402000300180703400d190501d61450244100c002e41c0d225030011240d2010580040781c1c00032001e4066030001d1440301034904132a6504c1c80810700c2d09009440010100f807034104110b41070b080103021522016500b0182588230344460004034001c0d0f00450f810b4175803250090021409070341d01d07400580242d52009020495101401401600c00c6c4a00421840355204004e0708400f0349030b42012546c0000303d8000400d5840361401d0580c2180320700030b84403c81e940b0702001c000070784420354510001c0d64000c2d1142811011003046007801c0303658840750030700194002008850074403045e03401402c4661083c580811102040c1010804a42005200120140d000b00f00404414114083e0002e1506140702d4056085c0c0828103030310300e4100a04980b030401c6d0300007a20030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 927811591 1250 927810341 927810347
    0x1506050c0a060e0109141b22090506010510020106031101050a050409020a0c0b06040b0f0f010c06060906090c050f040603050a020c060a0e061006201f0b0103060f060c0f03 75
    0x11072168000400380108001880c5040c000c0c0001001105e05042448030a1a800000078140c0111044a884005011247d0f81003100313030840d0344001e44150119a07411001c0c50128003810000502c2100200220b50405041024121a4809030400c581c5028000c00c0883e108058804501c00c00703007012070351151008800c840307230702c0350380c20020807039000240110340e0603884207000c4615406580384e02c85644400c8100010b0316110016150302c51070740f90306059540b030480300c242c541204c14104039074110500c0d40c032030064866660090304d206036030748410401200070340502480002c442c134009107840d203140f02d254868052030041e201096603c0d070005035910825411a0601e1601c28100c40451800016102c0a010001e00c020554043c01e0082002c06003015048020f0b40c40644489038585044406096203a01140000d120b0f4842d680794016910018206248445241d03800400c08c00c02e450300240585802c0d40c0200121010940100401603001c42c40302c4429a10206084000d40303a81422 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 927812841 1250 927811591 927811603
    0x30f0c050303240607050309040f110d0b27060a05030a0803010b03220b0403090b0a0e010c05070909050a05160e07120902040203070e090a02190834030f1506050c 71
    0x710b801000c0050b14205101b0000301411044604481c140603d5032025840c00548c5e600010600c034020b421721905d440b082d83e68000305044600540b5070740b601e1559a1007030160800b1002450030081070a02400803508040c204038002d003030180d000b400e0140c0c0035550003006100500c118000742a010000c0751525142c08004902d19482c002c1c9600e00d0602d60824030792182d02903c1c01c40104071014000582c1009550a43d122212551102c1e80400f81d00001920b51445113042140e45001784400031418019510a00c0301071030240c03000341684409850b001e864203c0c49524400c1e003c0283e4010441195081c2c40542e0250246c54405140d9200450010180184010007540b26002100708a0b801c1d90080d1018101350b0111200000ca0700c85500c10405ca01c41d4a4000c166a0011603a87d003a1501031450543c2020644804841c8901c140c0300b51a5411a0360f510540c0326000da01d00c8048081d4107009103292110244800c00c0a0340c0043d501420b090224418241803140210302050138a4040c00f030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 927814091 1250 927812841 927812911
    0x40308040b090a0f032007030213021e040603020c16030b07051b07230d050a0f081c0207060b03060934120c120f0f111804030f0c050303 60
    0x2a02400c44c2c501d00d800b03003440d1442d0241d2070b601d44100d4081c44010b00005807081c1129005000c04c804072500501d41701c0a54800c11a02d004109041088001eaa090707a000384014061941c1c01622082c000143e64245820850202c005001d40b50090000ca136001c1c0100d40c002009048caa80e651010901003c007000001005003294054042c000541040c100c001c00041c141d200c0d880c225042d210010000c0745140418094901c7d800700d121440061105410004c0141c020b40c81c450030440c01414040d4118603401c1c68120154011503080f0030030201e07028940035614100d0290429161071180ca40da2800d903038040c2190341c103000e0320301d05103194030450019004000c58242c19116440300ca04030b00c80030806204a901111140000688075403640b001d42045522500745400e07a585034980211844c1c2d01c40c3c0582c0c0200c1c440030040b207e0f6035440380740c00b210482c00800c1f40d0503150604002c1e00c044d0002c80508248030f503030515140001c0012007141c0d80701e80b0050030300c0d104140f18100500d44a61202e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 927815341 1250 927814091 927814103
    0x112715090d022101060f0611060c0c030403050f070911090303070b0c0409141803040806011815030605091605011202130302030604082d0702120c0918070905040308040b090a 76
    0x7a482a100c044d045502a6000d0b81b1640c01890340d80c24045904520708a80305c040d41d00000c000c1401038650100900400010364102c9051503140c2d00d809003002010321b9940056400070008004140d944d0195446d141502e4050034142074410000c02d86a114042006045180b050005114184184103680c0a45621841000780b4100b13200c4900780490705031603048024010455140340c00c08000200c03026105402c01030986a4a0100d0f0900543e01c042d80e501c041907180c0c0b9401400910b0280a44011405600042420304040c05c0c15814840042c00e4001d40c1201001d042c015660007640443c80307a0b01e041001641ca04074500b0b280200022508025414062041480b0520031400b0281c1000c0052135464007280398200c0034200000c41c00752458541e01014422040075140c051090b00c2004051f6042d14800501e1200042440500b20f604841c1810104404601e031842001307450003800d81c0d000b08014506243e02c0161082800038401404911001c0001d8000013040c0041000f256206c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 927816591 1250 927815341 927815389
    0x91c1a07020f0c030703020a0e0405011b031a030106060801060c050316110a080c0306070c050c0301060b0a0906082a1b0606040b0913030302030703112715090d02 71
    0x10300c000e440d4140696016624801e0305072122492070003044490489034000d00f0000c0480c5080145040000014010741d001d560310b5400f10740180340180840f05900c010780c3c0001d201c107403007941c106003071480c642441e000b680340c50390601260783c000c500d0398152646070030300d00794040440c58441d02d98800c0c001304a0b0b984c03a16503864000c1104169401d100301c28201e88140440351a002000e940385498248194154081408903581c5409000d0300840580940b06070746202c4406000b0a00f5521710340d02003c451a00041c84030500c50b07000b901d15016050301d1600e60840c0c00c00408001010400da000c002c00808401c412840d428164811204002805000b6078071502545151985901c02125124003e40c1881417000303036031405c5181c003841010b10300b004050010303140d1022402500010801002c0c543e4590a5600162070940541021843d00400385403a03181d19060b240c04c021002a002c0c003131031407500d1161008141106450725600c0542c0c20a0845495000051040d00301c9800c0c0d03502d0040034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 927817841 1250 927816591 927816601
    0xc0b06191d0105040e0604050a02090402010e0d0308070306171b0a030b04030e040f0b031020040b190201050601231e090a080f0c0d17040810050606091c1a 68
    0x107004a4100c41d021101042400c642c000710544621048030018400e8010001c1c1000502e0a42000d50f0468010315020000c0c07101c0b8408104201301c09002a400300b0511420040e01a034103004d041e01900303242505080034600e07040900d0742c90608440741c0300300c2c400c500e800c2000764841c9140c0c28001c50300303c2da00c1500d0b820305040140400c4540d08880d4040c50801460343e64885160241891201d0301800801c4030355052800c1e4001456002048111003c3c0d804014843c00030000c0908058040d400d4200d984807000c9600d02e152580140c10002964180310070820aa070f000b41c4c0e46800203004032900031804000c0095640f07540701e144041c682c100d03070700802403611304268005444000401e443e00c007402502c0d11b01055480c401d00740e9100242d48660010790440c02c00320b88055003148180450080d030203000d103078000c86030415040542e6590001e0500388802060f80140381c0c0141040e9001403a181003070001c9029a03501e2954400e40e41c0016520b18104862146e03040e1808103690030807a0a0308007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 927819091 1250 927817841 927817889
    0x611010f0c05071103070f06120f02270a2d150909150f1a04030206031312050f0711030a15061d0903090d021305250c0b0619 55
    0x20f02e006450000c280c020000b91800c0000c0e402003a0340e010450500b210b441c022040310803105c91515aa41d02d5201d50b0400f4401000340064070440310701c01400c06a44d101480c80403603c0c255403921502c581c102ca801045404140d03201a003103002d803550420b11719090070202116080850340400d04d948072140b80b4109150703101c580841601d000c02814004a05c00f40c00400380150303180202581c0440369101001030310650900152800714202031503003000da603500040c1c80c0740c00c101c56481500c0c0101c0b5260b820080540d680308045120341c04c20703506200703403100000440d010303404005083c420241f250f48100c4c1c0d020001031500341c0c1e0041c1003000182c5248491809401d5a118803201e01e00035003000440402c2640030503125010f050003c60514881904001d01401640f1090fa0401070401103010001c1e0240101407083c59000310070750500d03000005404d0301241d4201005c0410000400c00e000081da07411020790459404c582c1d11140c0440142c0f043c07008240c5600400d4004580c000042c11414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 927820341 1250 927819091 927819097
    0x14010f110d09030311011506031512060b04140c120403030b1009090c0516080703170a0510120803070e03120d0b0307050a033504030303021905040f0611010f0c05 71
    0x700c6135840083c06417440f8841d40c241e510150007209101458201070158500c25400b0032059510943c45004031075880003c900a4414500281d03903813038540d03010180c1d5040c02d003d15015527000036220f500a180c00710801002d80110081c843c01600500042028180b00c0d030400d110380d00000708442150140c203070002d8181100b900c0b541c0142401c1c580b4a5440c140242d06903503000404540e802c0010890703035640c03241944802c800310f003404181c0e542da02c4250b020441e46413042090704000200d6081101d0026050401d6500604110791904a06800540301d2401d90b5009035203070170480503000b1036100090901c0303c0d804410064000100e0300d004181416007140031078010a50980340b8041c2c48205007e80c0c041d0a0101900c440c006460714521030704010080001c802201c04410001700408060440b5540a030303000b40c0000b0b802107081a80036203000c0e008001d048090130018501803a0030b50300142c0e08000e01c0741ea010b019002440102608003900660081100140100b00382c50b07030408040c00701e030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 927821591 1250 927820341 927820343
    0xc2c01060512071112030405030f04030c1703180f030c090703200906030c03100308040b03070210050402130f0b030f1e0102120f15030609010b13050114010f110d0903 73
    0xc0321003400300302a24060510134138002e500384007414480c901c121144041e644007900072a20340c4030800c1a440c4080f0100c016201840c071910540080c145003100401e02c0c0413190009800c50340041040a940c01202c0c005480b0aa00a55061a0b41204100000d081112607126075030022204402c2006142c3c0c194080071074910741118140d075034000e94008241c140204840e541d0444403c1020034515007101000d950722182c0c503607d9036a11a2a44d90389101d60b007055101400d01800807040c8250f05030140010051100035260402092816800080ba500300b086004400b5039a00c010b00798403190183c019a02c004800740482d80c40c030345a02c911665039802c001c440c60800141d41043d88000c1010b00031680e2088522060a030140c40310500106c2400000e81a0f5190030500c0803100f1058505021007441414010000a02c050400c0c0501915020388c101a41840c0c3c9010014040d12001d0070100f0051700080c039001e000c1440300441510341c6030b40f4004a1215200b0002002c3c840c69000764070106407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 927822841 1250 927821591 927821617
    0x607020c0f01110703060b0315010302030c041805030703090e150d06050c04120b0105010e1507110a0806070905010f030c02070b03220b01090f1802280803090a120c2c010605 76
    0x841000c9e0090740d9076039080c00001d502d900411581401450f064010412400328a60102417078445590b80a00e10f43c0281011404103c8403002002505144d07450350354003100d0340c00c1021001074078034000740101e00d10480040c8541c0d87d407004100f00405603030503a07018100280f4049215080c40c100088000e500344905c600041d6a45500d001e107081c1885584d40c581100c1e401941030801c0d982d5154401841c1d40d030640d8018042543c00200600304004103402400d040d00c66000980c18130b8001400f411030310b0b0f595400c0c18105030007405040e0340007510300c00f140c2e00341024503143d45030800343d00384007010200c00d04448185940301d0000d0200040d8224100c1d188400c0410082004022100c1510a0310711b140701c4800e01e1903506070260030000401c3c0c081200700c1600c030142c1a1800c01805841e0140e030801010b0303034000b1a40080303c0c01d28040f00006040304850b81c001020f059541c0c40c214a500d401171006030344104000c07070350608142204100300500304001520540c0c4a4400910b1600240c140d03d0314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 927824091 1250 927822841 927822853
    0xd1109090106030b1305010f0c0f03060b090d03080a0e0a0b0702060703110306040518010c03230c160314070b04031b08180d0b040c0f080607020c0f01110703060b03 72
    0x403400c14401c1d182141d60102403449103640b000c80241800c9800b4205407040d548600f281804c0343c41c81e1040300d502d054207848403032110700710b188004c0884946420900011408000300c1400d6624801d601e00003c0c3d142c90541899039403a01040c001d0508c0c1e44209819114101940017001219412244120b2166007101d49541d1420411416a8405401240c4121007000440e000c0d0074a90451580080d4002204800c0300a01c0d024500b1110842416400640d851055202d41c4071035540024003d04242c01c0e503103903810310125200051094000546841c40c158040b103013007500509408007031800070058a46c640c041d5080080184000300c4040b40026000c01c420b43c000006080f202c403840ea00402c41764200b00c0f404544803151402040c0003948a8000400ca00c0081c00f4091701901c0795115200c0550161316081d101e8004070190340244006800c11000c1004465000607012216001101d8080160031020016607401046043c80c422034001c4040110500000780c205030140d0000381d0880d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 927825341 1250 927824091 927824101
    0x160305031b0106060903030c0501021e0306031e030a0c031101050c04090f0c082a070501021824072108061212090d061503050f0d0f05030f150d1109 65
    0x403c8500390b000f01c002103055440c4c2400403078420340300401000d105000040c54911030307402b80c1d0404c03400e910501d01d20b05400002c20105040910440c4a04040c2c5912a05070b0104007403500d80368002d040b60300b0304021a10400c2400c2c9803203801d00395081c1041e18000c200f035080a44400d800d035032050061146860800c90020302801d03248c42068015156a84e80358038603203603032203110f224180780003018000c248c1c0380718420f80500741c010040ca6070310311031800103a440c0a40102203e04001c9120428840c000a08e0f048244003c58903244e4502428a5440c0c0c1d603500451a204000390790b1040f000200c80d01c100c1d52118401d407c00306850007900122250007140c0785044200e03a945100c240001400003040c00401c402d0304290034140324007442194081002541103038880c141004030740c42a69554000c84280c035000005100c03001034034482d131070700102040d45520007a01d00e1002030841004401682c0001d03400c2644034007400b48000c0e0042c08050188070a051002001e104540761522132049480451 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 927826591 1250 927825341 927825343
    0x316020d08160f230405101e0f02120711010e0a0b0d0b0a1703031b270111010e1e01020a020601030305070503120703090506060a0501051b160305031b 66
    0x82c0c80b580382c2e0460603100030b40c0b020040b41c0903118000c0c85014492480c1c11040da0740f03114a0009807502030306640540b40c900d4101008810503000183c0002e000e51100d0744032009180643c0c080b040c1c0041d0800e030051060b8001d00701e00d8400d003011a56030400700802d4440400c141800900b01c41807090b41c4238502c42c080e078803c200c2c0d41e1203e17200300c10120b10304100c8450020266040600030b40c100a06062025940c0d104150944850b04603500080d00000100070aa20280300742c62080b140200c000b03400c0c840f00b181c1c11000058020000009003500070b03800d4019a01c1501e018031110201c1c030082c0400501108020f903500d0304848224007220380c80c104540c00c050148203403065030784c081e4000d00701640f8688090711240e00905041d65a80002c03c113104024400710525405400c10b40da001a0000b00360a12504240000c1d02030340c03003003441c810300f0041a80d1000580d01800e8079885035201107281000014a0f04164134201c41c2c4d14080b2120002c18000048058281d48852302c6400a41e820421042 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 927827841 1250 927826591 927826607
    0x8060306060306060409050f062a07050703150e011409011a090f07140f04050a0501020102120c090a0302040e1005160c030305180f0d0e030111040902030a02040b0316020d 75
    0x154259021000007055403805d41c211546a40c010001d44e0001258000c1290501c101200d840d80300c0e4038000d007080390300307a00c141140c2c8c240c00102c2c20603420285a544c074a5129505440042c10a0120248900e07018545500c1107120300070720b8000b0058075603124081a82ca01c0200c03000761080d480c00a105000d9049100000d00601d4000d24044050751401e034000d00d00d480140c0700344100f040c0f25882c1c18510250300010b003d86984000e10030b0300d9514040400003611050707000704e070447e401480444490a090034025030081c03400141c564846001c000450145070f00c47c0d2000e540281080040385d100d100100e0800c0258111440c288460b943c0d01103a400000402554080010084c0e00a1004248254000782d0804441401d031451401e01c910058640391029140e64582e810120582175101c0d002203c45104030015030003400b50740140c00114045002d1407041d4207040b900000000c0881e121941280c01400907920300d103440b0b0170f00c5044101a50404460039001d442541000e580ca14010000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 927829091 1250 927827841 927827851
    0x506090606091324080a230c0f040e12030f01090618020a0c021216080c0d080c07080102040b070506010602010b15070606080609010e011808091c0204061508060306 72
    0x20000003e594800000400d9010303250307150458084008601205888003200040c030403000103100d007400b5400d21418460017110031000101e10320100740c04c1c2c5600440e1590415000701c0c0c42000651080c0003242c09007401c2c00311501d142c040c84541d00586059500614000ca01400e000c1031180e0300c1e030400e0002c40301d00b402020140000d140300d0788000482034000705204030b85440c140c184100503070302180186070350140240c234540145203410015441c18071400c004140010040c0700146070b02010401901009001030503640000510b0100311100304081c0340102803003002156103554680c05000c050304041000c5811b03001b9800002000d80c4140180105104005c02d032030b590076a60a0780c0000341e03200c118116051619580c0001e60b103001405800c1c0315004840000c21018441040b90b82100e0281c84440312070b44409007040c022450320800d40e001c0e5207003941c0389045016420002c1c02c1900060340c0003584242030250204d42e540040d200d280425109440d07426654546004040d1034103011070b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 927830341 1250 927829091 927829099
    0x12020f03041511011109130f020a0f0e090114060a020f1509190230010c020303330d051213030201140a0c0b22080408060f07050708090a18050609060609 67
    0xc0a80d10529142c038a0711f003104800180014041c0320b441c3d584090b6004910010046200344225410054104030400c000010407111410158141400c1e610303042a41141107006d100003081f00c07140786000700301e07c5010702c6400e0100c0321201c40407090303024808007c8640724400c0c092544610740040041c0a007444240c1d005010903103c1407401048010400020f900e4004450414180c4040b0b0b9001e110b42c4001c030030030b64003842d92454640c2c0b608090b6090219502c0140b80c1d5815803e4403070298002e14120b10381c0c1250304410740074090814610f440000c2c001010032503c0083c0c1c00c9201d000e04684d00084a1003a01ea40c4041584210991741a0107034894503004100d0301415040000c0c0811701690b8032440c10900c0303800401c18071705400701c2d60300f04c15000c40c3c1c0c10703c00113070a1041020800182e948403c1001f020394940c0340610b002022801404030003007a0407800300c5d030001d060750f441000c00060844a15082c0340049020400e402900c400c0d51414028140d1002207000d90801c4e00c206c41c64004054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 927831591 1250 927830341 927830347
    0xc0f070f050d0b1605091e09011205060c0d1413020406170604260d0e010506030c010f030f09080a120510120b19020f0c010c050307090312020f030415110111 69
    0x4500598074140c100045410170608000c050070503900d5031941c00d003140c4542038901c0c18025482c00c2c0041100103030822002d00d001484108001140080e000350303c0182020041d444440364841903014013030401d646d05100135140b0030401c1c4010541c01c0580d0032802214207003d4581d031540d4006108801c804503007100c0d0403420016000c20540b0132808280c07240f102004035001141c61180140790451811402007948840d154498a1424041c00d500701008901411500000e00f0001c0c040140081d424414141c0311284140c00140a07030161403101d030003014250707849824000007025150120003000c0f106144c4000b1810144a2402e9042902c6148000307412800c05a240c140b5480340081c880705400034945811380f212030080c000341941e100c60008254440406022482c00c1d07440d500350702c1003009810300400012681c01485501201e07003101d0a042605001d0100301d0a15030307821420f80b0944000500000d0500b0300294020281140b0342c5e85002d1003102c001d0342405e841c0c1140241e10415014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 927832841 1250 927831591 927831601
    0x130c021f1401050f03070308030a06180606271802070201020d02060402060301050103090611131503020906031339061e08070219030c02040b01110703170c0f070f050d0b 74
    0x440d0011103002c00508694103140eaa64070007623294030840ea1080380c107442d19810010040054014680200007480910240d8200340303009142c9001c100002c030303240001154460107400420030440c00303011500010411441c50f844680b001e54882801207005100f2041a01034043c8003003503040c05280c1c0186450714591a01d00118054003c0c4001910322640e00c5203034001d18141d0000400000008141c1d82e0030051a0030441c440d030031190240e9200741344c010441d4580315a54502200d91240b855a8500004480780c200341c950114031b40c4401c1030b20b1075400c141205080080c003015091940e805481c05d20359480b840d003200d0340f02510601d03d07080f41070500480396582c011400701c0d92140d1184100c40f070342000c014504840d86401e00302900464a550702203c20f5003418082ca100004080c204845121001c0511a0f80c41015101c0900070305500c00031074030518403000c101c0301c8004841c000c81e1354950601c1d6019031074506501c0740d901110f44941c2d001a0600f85144540340254000c15000c05583da0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 927834091 1250 927832841 927832849
    0x105070309110906011e050c1509120a080a0908040506130f0b0a120b011407030804060606050306011d03030f07060b091b0a0c1110020c01020f01020f18130c021f140105 74
    0x2a4486e200510001348030700c040c07030f16040180040140f0750604140c2141031032140e16080c42960042181001010403d079104250400d00c041d4000c401d0a40014900030a810843c407140556000710b90f011600291a0703420728110381003a02500c10481d500c40c90f131035484042c00700d14403d5400c11000f0415503005907691510030760007514042c0c0181080035910408280c008002d0788200801c4011440200c144810b1041d1442a040504201d0501900d903081100000c0e00b05071100e56001d88000d5440310100d8551402e0040e558020000d045403600d0314290b1401d8000b820b50755462a010b5005000020585600c01c0c8152108100340112a0b2400c8084102210389158100b010381c1e102c4044a000106034a68400c5280d2039106640a4481c00f08410002414190782d00c008024030b81c0103014441c0e42d000303a0401c03924015031070058804c0706040c200205007004100c9204044441c6000801c0c12080e8000c200c080300c11071710740c0041c8030303400002e0320182c1180d003214143c2c508036902d000103001c1818 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 927835341 1250 927834091 927834137
    0x10c0209061503070503041a100522060609140d170a03090b04060f1404020303040b0a0905060a05040312050309031602031504060b0114040b03070f11010507030911090601 75
    0x22010b0450700c1c00c03000c540030b041030a81c0180d0701600010700010410043c8500440c0e4100c50041d480030926480c1000005090050024040c0d640320303203003466514000b801880300c1140d00250140041c01001d40d20400600a602c19101e4558081000c800e0b050032403524100c2c030010b9a0740400822411302c80090f81030300b950006140a400d065480107481c2c04220031200c11445248140c1d07000ca5503800603a03d04040c0ca9035242d0700c0b00c2d14150841031000590b8003005407019034010712041c9884401d102c4084038040d85542c4020f401c107000059008046a02c440280b0503070b0302540250440e070101140c1101ea501c0308841181264209001f03044004100d090840c15442c0001e08031003894405140c0800c007200c1c26101150341d10ba440700f94403000d507000f159000d00840c1c8100803a060030728014500703d0380d00c8020440303802c0107170050040d08003034052940d040001440000811140c07800c0c1c20007800401a0714130960700c0000140d01da500ca80742a5000511600c1c3c180c0d1150003820b41e280759650303012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 927836591 1250 927835341 927835351
    0x6061707052212060f14041b05090a142521050a09050f12041a19441510030204210c03080a1812060c0806010c0209 51
    0x84042000d01c0c041002d901954000340244000b803012901c0985010703021912245c040510a90404045007070103095401807590141d000782003c1044075502201d06554a101d4100c0b41d17029055100340700746142d181e4042c01c000000546528444d0312104c090001496048a031110883c03030140ba0f1048040c46804621040300000c00700b0b00d04195011501c0050350811034101900940ea260b081c41444410028110b2040c501c1c4050b20300401c4011401c419441a03010b4441810403200404d016810b954041b1140c481202c8101001070200000003401301900c000b00364860740078090341e2190705034030b0707500030046502c4c1040c43c501101d800400003000c240020803d000380301074a41c14441903200c010501076020446c2e980103075206d0500d0b80c00040c402c40e0700c3c0380461040214072010001000550f5a10a0700e4008901c1611548980c0d030032200422501c240000040042d07100140642c12100c408141510808052019410240c4101c5030490110341c2c1c0c41c005107455114102604108800ca9001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 927837841 1250 927836591 927836617
    0x40b01090e03040b040602011b08071209080c0604030c1202031303062a050d050c0c030f0f13030b04021c26070c1511061e060103020d1407030606170705 67
    0x11960b84d02c072180180e000356100c000940d44944600210f03905c0c8858500c6010759908100c00c041c00c0c100c00040c554480c414583c04819621410b81d810320115a090340c1010400c01d0440f42640340501e001090505405000caa42c0003002c05200d050900120036145410f031086581080c0c1441c60300e60002410000c42043c40c003005410301d010038621240c10080784034203941c03155699885925020000c40c8c20040a120900000384081f1010714808003c691740c541d6140520354894001c00e59800c5c0c07910920f18007440c4010034030400810004a040061710440c002c40d14009c051070b0081d0003000b1001c001c0c400810b9080004600652841002c1014005102c061380c0c00d0b00303110755130b52901903200da00e810034a0a04003484034442c00c20352041914401410100103810f0078182407176030548030705103101615a0302c180080000c076164401c1c0e040c0c1e8a40d081c00b400600c023a4510b0499085505800d032903410001e4148440405c0c001e02803201c4000d2070811078041520b0355240c0c08204c0b04c82e00800307203603000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 927839091 1250 927837841 927837847
    0x7140907030b211213090203100b040801050a0c0503090d2f030d0c050414010503150402070f1401060e04020f0a0b0309030309011d1e0f030a080603010b010206040b01090e03 76
    0xb107a00d542c0c400120114501c2c454000c00c84007030701603501c0c04d800969400300e40c0d8401c011442c0c0700380b0140c810300125115008096102d454032480c4104481d007607000b1013400b2001080c0042c0c40d85054000078011040c0b48003c2000241102084600741b1040790307080c01c1c0d5481100511070380c038460315001e401d000002d11841103604907052825420f10078100c00320742c194004241e4640f00b07481e911844460342c0c0d19040c1180b4251600c807442580d0017008104034103000c00403001034030000741524029007800b8000d008550343d031600e2038030100c01c1018140a840034441c0d49140340401505208070340941b000640c14130f2407550345508000c1c00139000000f068000c0c2041c03100188003c262000385004403c4000903646074034203010314900f142c046544000d10410714950480b44c42001290b030f000aa19002d070944400200854500d02e0808041d9116810b80700020308640290350243c011406010110300a003d00050301c801280d440c0d40070355000e4070301a414001009443d03004d5000c030803240c0420042d241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 927840341 1250 927839091 927839111
    0x606090212191e020405090601050723100c02152409130204020703091410120c0201060e072a02030c0603070221030103060f060605030a201b0f0714090703 68
    0x18403020120f00c1e140d5000d801007010310003490400708041d070014007883c1042c2403c819440e800610091034040010184103071526801c244801c0c0040c01000481d11b0b400c1c49008407101000b581c0b01444001c4106a071302c01c00c0403515107545418244006400450403054200540003000707120342c1c001e0303d00d81500c1c1d551080030380161034500151403032500070345a000c9482c4ca0020080c01100d00280103d22401e401c0809000407500400618010002d0900010340c05000c0035050b40100003d402c0940e0103500c510030000308540c008d40e60320411f107e6441d0700211180380c140042c6113129013000254590890b4518850900b0000c0242d40d0240d028030484d201e07500000701045040b0404d84e0103580a510000051050042a000341d106040140030304101007032520600030018000684200304c03031500c60f505110b0324800c00d900c0022a0068014480c0d0f10103500090f803112510104071545c00703004284590a4590b0049a088101c83d80d51041c2c0054480d00030822090010003042e403002e250355000c001d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 927841591 1250 927840341 927840371
    0x702072909090c0406110102130e040510050115090803040e150105040b1204030f050306030a1502070503030c0a020106061404051512040b100f030c1a1c09060609021219 74
    0x180544103006401e0741d0b072820110020905106c210001c00710781c0c010440b4413400040202c0300f108580d0307a00314038816511113180c8142000215580320900508000c004541e2200c010103980048034640c54034215142c0d500301054407070140c1d215007640142e40760005520707000303140c4181245100502d40b0a00d0649c5443c2c0c001801e0300020f611b90071040901d01007004240e0000c0303801100030000d050903030071480c0070301c002070f9640380c507190003005008114a404007a4002d601510301403644001a6901c1c2c0c90200d00603e015040701010100540c2071200000d810f0b80941d24003059181078450350341ca400e041c5020700226881c00c480e0000110306c2000485800c030603c0c0e041502071485004418000d0070301891151480c001d54100040300b0352401020030020300030b440800c0407103910040103240b010f04000c0d040d000d4094070356a100c4030b404001100048007407562005204c2445610300704180c2d52a400148124013401004440c1002510003160220074460021101c005401c00d0105001041c107620b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 927842841 1250 927841591 927841609
    0x5061f050f03090c19051507241805010e1908030f0606090406060c020118050f0d05070302030a050708060109050f1909051b09130201080606221d0702072909 69
    0x840400c1e1417203040c0f100e4a42500c10b141d0f0030120b9130b004d50805000b5103aa181e00c41852000c005807214030703c000140406d6503005420103480260a81d40c0c40149420114064a0351080185281c011845103182c0c00090510785141d45c1c0d0080c0805046a81c1d0b180783c00b400c503001502c0d2591061043c8069405591580a4031000d080c841d90303101c059481500c0098030b80d400041021600302c3c001c1c0024815515107024800c1e8801c811200010040c8450510303608120b06078001a4044c040c440b151014001e0018110f8101c44048049408907aa250546400c4900c240c607220b00c511450f034003148084a81e40e45035260b01c0c102d402d0004210100d540d40510300310b410806020010310540011100d85004182c480c1c1c40b06040407468a0000700c4c0e40002e0805000800306032003806c0200b118003060b00659003a401c50745e210781c0c002900c652a2802491507040d004002030b0b080300e00c900000c000e9403001c00c0344402c40e480009002500d56448441d80c183c0352030807c0e46011550240f080780c01c166921010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 927844091 1250 927842841 927842869
    0xc1f0206060d0f0609080909090a08031501140a02030702122803052b0b030309060a081306051e01050d030c0201141c02071a010605030c0d0204030f0605061f050f03090c 74
    0x1001d55180c01d41f0040c8540c00b00e008028880c650030104800d0081102d0700d04a0380d000c0400e102106400500b0710069850701002c207895442c1d0000425804601a0000001c2070030b04d0007200d0701240c0504121503180d4400450000c0d900484888144080114582050300c944920034100301c0c4c00c0c500b2001c1e060049085903488030440c2084490603c5811f00f0600c078140c0d07400e0080d00035514008085000c01c04900c5080d401c0ca081101681c0007ca03840c07028800842682c0c0d00460511207030810b40d8240ca081550043e031140f908601c2e80000841c0d15150b000071800c168981c40300b4820544640040d6141c0078031f00c50014446030100240e000036010101c00d203213125080d41c0300589500490402240e40d082c00b136020580c41a8078030051000075040300a80303510040502c60b80c0d0783c50f00c0001c43e9802900031076100a0104000c48101010000580c00c110300c070b590300b901c50120481190803400111810000800c000c160104000888400483c3c01164000c1981d0101d0381845006c0e0041030112004801c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 927845341 1250 927844091 927844103
    0x60e040c21030f0c051522030815150309150a0515010e0105040906080709051b0d0902040209090f06040c1e080a06051807020606090402010f1206050604080c1f0206060d0f0609 77
    0x1040103000c07100c0c078015406000c0c114103802c7d141c0816542c06028104058102c54003a01543c003011140e50343e100c04900d01e0342c00c0024180d10703410315041c0307a561901403403a1305410343b54410000f40311040c030b4032405101e1444140a440790302110310054441280d8140d03640d040002c1080701280944180c01001c0042a460f00203010035454010356104541d0064003d041c4520f82280b040d1030320a07409d003030b03442c50b501e090030002e0060350901c0003600900c5100344098101d0385100420090492700410548941030684061020703071000c00c0216070035038540003042c0c19542c0720034074815920310440005a026103040c1c00001c14540b2a00081d8110f11600c02400395030f1714200c00c100741a541803040c00c2c0c11202c240c41c42016130030680e0010308049007501da004100104d25042186c6d02c041034110790700a0501411107640c83d034607680000d0b1108803c600050140458158070500024002c2000825910360341c040d0405468050402c184400101c030259a0109402e2003c80801d10768426110841e109076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 927846591 1250 927845341 927845383
    0x5030c0d09061d0c190e0c0d050c030a1a03280f050c011e080c07031206031401110414060c030c0d05040e090a030c030503070c06060e040c21030f0c05 66
    0x1819078607004c50002c0d454050304110202080e06280aa10398003610350407203040c2000e0b03540d891030303003980e01a949680c1030b503600744000e00c07200d00c5c1031500842c015141144184143c8000d000e0452850b0039004005406502039030600005034040c2c0810064035801c3ea40000c1403035407a843d8050300200d070b074209403915005400c50008a6801039508001d5114928610b0ac01e080500c8025125820080ca800340138040060b80c6002c06114000310807580e03030f0445042064581300c1c107007050640340c9241104070661a2030782d00030740c040c0c040c0d06031011182c42000341d01d1104410380c18408c0d030340c000e0400320010b0303c001c1c403181c81850024400014034004640e2900d440300c2c80d101a111115102515907032407038100020100210764411040d2001e80c1d0035040c074540c0c98503507244c00c03030300b03041c05840203441c985c980741010526007450342000707028502807a2000105604c4410000400d02d4080a2140607141c000350040068019068591800d00314101075100009a448980c20410382e13000b0301c4a40c50301e00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 927847841 1250 927846591 927846641
    0x3060103060e0108070905130209040b1009021c02070507030c06080f16021005150d0c1409091906090602070609050d0e030307060b06040b04060906080a0c05030c0d0906 74
    0x621401d001480c0c41540b0070201d500d001490303603c4202d2030298080c0700351107200042450001045803030004d81c1c0a081a203c070f1170942824100c1c44c50a0b40c490a0307182d5403280010342c070326030780c02035420b0740703d040401000e01141400c903030b0001d502602c42141c01d401200e9000012801e40c1100000801a5407504a407624080a04140c40c40004080d85a5038650f505902000b40e400204441c8580c200d1800090715200c8040951100e00302542c4a907100100c84d410504001403e0340c02c1c4100d034400c0d200c42e10542006000c1100511040307a0105288c2d12401d034003056a603194017542601d50090400145070320345a01c034034081e68011182510840e4683e9142020040d003000720a121584620f0f200c2e8108280f0b4001945911440e41c01800160b15010040e0295a4100450700184241d4402c19502d07aa03501d0080c10074102485410013081c7c0c2e903000500510001e00405080c482c0d550381312840c6035214040c04d0907d421540035039407000d9030b4480703042c0040c116100d6020450440341c0c14a07440c04013 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 927849091 1250 927847841 927847847
    0xb0a0f3f060f26030313020d060b030118060f0c0206071412040c14300102040905041412030f0103200a030507050f011803020603090f071202010806011e030e0111040b030601 76
    0x2007180c84083d64401c104100c9029643c0d04c0015203503904442200d250421030034a0350140c8100030140754113500e021544580c54442030345506c1e809205000c180510745c1c01017503200c00c441042000b6401341c1c00c02c0b40005c2d002c42c4128075012070000710249250034050f51200d04100f0010032a01184c030005480c4040c05004900148030000e070b40100c0b41c04114070b20a0040d01600c82e005485816160003c1020108218080d0162030107088042c1c0200320a00d003604003011003902c0d2078200d44080c01202c907490148065007044900c2161a1f40038614140d10f56503425801000420718003100c0200d400d4005013994800316581c0003980034000400c0058145400c2200b134160b032846041c14840104010411040c505c6241d83c116501102e14948a41e2598100b03800c10051403d00b0840b4024048081402102c0e5802d004031107000303030780d100c03855079a8200544040010400403803005048620300304220b40b1079040f145180c110b203000420381100d00d24070000c3c10f800903040b40102c1800402003240300d5034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 927850341 1250 927849091 927849149
    0xc090c090807060c0c081603110a090203041a01050604080c090604060e070f02120a090506030a0b06070813150e10090801060b0415020c280b0a0f3f060f 67
    0xc000005447d0380d8000d000760410640441c80001e2010340d92162080c190b0707a030008034800030244d845043d546d900d0189441c9030a12141e00a408241160070000704060078000300b43c03804c0d2102240202101d450b800708014503010020b0410354840d4642002003040ca2402040d507001d4000354480000c2c038204150080d0130075100050314401c0740c400780a002e4050394080f6403001140c90507200580d4a49039110441f000c0e11400c2c11450708030780001013040400901e40000c00c010b8030710014a01001d612a0780500402c0440c1e24000c1c0003c8110360100c074039161030030342001000964208000e5450b50740005c50709460300c950009480c0c001c0070401f0404003411080e401d035440750380d1014040b138001050009213140100c000d0048c1d4840901c3c410000d89454181203400b07880581861070711442480c000800300100b0341d61100005584802d00700c00403d83d40703020902c0b00c0850074031240398101c0d541020080f50006103014109900d0301000030306030036118a03600140c03030507211a00303100840d001c003046070b9030b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 927851591 1250 927850341 927850349
    0x2030d1521061a060d0203040c09020307090e011508340207061b08030f0a15090f1514040b030c1003060305061b040e04150f06060e0604030c090c090807060c0c 70
    0x4500480010a80c1e4420301202c6085d001c030b0000507240d48030782c00d10000c480070740d030021140c00e4070000034040400c1e00181458112490484050354581c0ca81440c00c8010101c11405030118002c0b80224071944203401d401d0030687c03183d089038444411140c0c2c031418103409404007030b405a0010a014003c5640c4000307407418000e11000340b400d032800c6d030b59540262480001c108003500107000c0e002c50140300c025004010329070b00002c000229151542040401004001c0c5001205460540d0307203984542c2400c1c00c85c04480800d0039505204c4000014070004d003001c82000e60f49400713004500103540c1e841013000382c0d15014a075400210304c0d00b549842d0b807a041003e0310360075071040310b0442e24100e41020411101580e05c2c201d0804440d845603c0c2041d050b02681c5d0f090a406424074901d8404070100f5440039040700c0b0559241c00080900328180480c0344200c0c000501400021241401901c6c1980c01109100a05240510111380d41c0c02d0203c1c01e081454011200081e48400910b0611452030800e9001e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 927852841 1250 927851591 927851621
    0x3071b1713080606130e16090c09080a02150c0705120102030f0721110f030702011a06070c0306020711060f0c060f0f0f0615160c120302030d152106 65
    0x20300704140061104050808070081043c0c4a83c3c0921071200c05002103000d81010256441c5010723183c1c065040070385902060b8100040c00c94a0008801b04001900003a06801801003800310f102440300115036800054001c0d55442a4000025a030311244486240e444040c1c00042c0c03a03081074401d2010305480a40200100718042820100070b181c1c5250500231130b801790b200003840b1000d00c0704401307607402a031001205084012040106158064108035840c80401600080807a01001005424058508044e05a015042082c07000034015030042c0f8241d030180341c9a06862141d0400100e49912803141040412404101d80d034010404200c4150065900c203c00034907403418205466901100600100d8005002000b2079220340715146402e850704029805540e5550707000b030010051910301e000031110340c003c9805c001081c0a185d101801c2441e8140c0c0910300e03006040f1008005400840000000031b04060000203a102e801d81c40034901c2e021041d0b41203204619030400c0400c64141484100c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 927854091 1250 927852841 927852853
    0x7150203220b030c0313060c0e010207051c1106090a170706090e04020f04110d0b01170c0417120406030504030305100305070b181503010f14010503071b171308 70
    0x202e4010100341d81d408208001881d44070303034070b02507985a4120f41a1004d81107900e000700c00506140d0216106070464402c0e000c940b40701c2c0d582e02c1840744843d42001030205183c0d250400d4000540d01550710601840020901802d05404a0000d00f070420154846691201100c840114070042800300200905507410040199407504400703503450700e00180000d00c141c2c44480e20144580ea01d90014020b03c46c400038031916a4020301a400060204800050200f140c1c00c510320000604a44c030350b407180300854401da007071629020b1180b91542005900b5806400b521944010f922000c8003d80b004188a41c0c01180303c4c202410007030110740300035110320812610290b090010800001d0000102c41301d03100780f1595241260ba1690700c1507681c210a503409201741c0c4401050600380b0b00558140c464502602449a64680003c40e40300404600c040c0030070014800904518021034002c0460100300c0d41c5640d915010780e41d5103030f00003982e40000b140c0540100b621012126944083c40241c80c0b4a001008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 927855341 1250 927854091 927854099
    0x180109080d020309010f1109150711010f0210020c01021e0702031c051209070302030f0d0807080415020a1107051203040b0310050a0e0402041b0516050715020322 71
    0x42841481e4a01c018503030008007141e4084403d40c0582c3e031824440310200f01034030768108400141e40c40040a0340c4a44944103603e5000d1841c0e50840340b07801d81c040001000e042c01d000040d2820f0064140c400107500030068004400c1c03a280c0010307c080c01c112000166100004401d9041c5040000e440414241c010320080d03006031000605602c0c1e03500c0308025803902c0214002d00311098468410411401450081440740460740000c098054034421010f480d02d448403410f42c9580c480855102c1d8002800d51004500c04a000340c031800d40141c01000180303450f8261900700d100380d034045000c01d0002103495a0240320817a084c40f00308041d000403a604c16131008200c56481d520300680c010000780751000004508a007030445040b00060101412100709a695500c1c1c20b0041c200480c0c042c3c0c040c40c00d206202c0a120742c402a40b00c1c0d100c2007515a40e00b800406a8aa483d483d07800808680501c0b9000004c80c08814005081c0040c000c268000c43d900c0413030800000c00000c7c544144408821259810300c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 927856591 1250 927855341 927855353
    0x120a02060712061505070c060e061803100207110a091505040e0106030b010803040303090e0402010504090513061a190b030606180a090f0507090b19090f080105180109 73
    0x540c201c0071a140c2985080c009501c10350050040c0d074001207010444541c40141c0a8103c009454801d010f40c0540360040e945074800d0707506181d038444055000b1010404840755921071500c07000c0ca01e00c06001c41d04115001c88580c000c03684400c405581c5900003c1c83c441e16807170103412000c00b500300c501040c000e40f131802d102c2e80740d595114001c0510590b100e100200002e9800d5004600640c1c014500340469603440c0c03940780e1642c1c81400b050300041e5501c080801c0300101046818043ea5040e59030300c0c036041c0380000403001000094102d1000484005110010507200e0280700b540b0442c484032000800c1c21041000109400380e90049524544900108680407805050701d502003000e9420903a10004048200006c482c2d804030785505c41c240600c0842c400352079610405041070803000801442d15600415203042035a44100d4032055404c00c23280c18444600b1504515845150410400054035903000d602a04099000001d560b9918400c001d1000b03d01100941401c25840082180580a45400f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 927857841 1250 927856591 927856603
    0x1206030f2102101107080708130632070609060b010e09091b030a05060703091502090a030201050c10020c010c0f080c0901050319020307020c1323040305040515040602120a02 76
    0x407403d810783d120700c6030306081941800c440e4882c4e4401041c036a40d151030710781004c8130b42141c4440d1586220f5541d000c103045009441ca0080c0211070f804440b058078460310300c0c400c00d103c07601e05c41c1d2503c201403221714001603490080a059034405e140100d00b0040c103078001000f000780345405030721401c6241c0a010000c01c3c08a08072424488003000362307800780030060119103000c0329200010014444d09041240f0240d140d4004401584540302e00715102e007418803c04164050111483d50010800008200642c002c00050402054071429a0040380d091303008001203030070110800d485070b51942000011241d20010380005190b03e820143c41c4ca0030131600d144a24094030001e40e05201d03000001c211810500140c41100d50502a0255920305d48813000035219000c0804140c020140d0f0443c076404540035000d4400d81070325400745d00340070721a4801c902900c504041c2c01034007442000c100109454844110b0501d2200139920728541d110328000c07009241c1280300360110110503003408050b0840ba030118034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 927859091 1250 927857841 927857863
    0xa1e06150921060b09010f0509010b1c2004031a091c080c1303030c03080702030a0c061a030601120c0e0f180c1906020c090103031b031206030f2102 65
    0x1140e9101145484001040c041013203640c010300c5d2000025030f140703000c0300340826940f0960707510340d0599031228a45001c0c010020f507044224400301141d44079a1a507071182c01203400483c00380c110008941b1110402e90301c04d800a0b2004942107003111034002c0b40e04405d54000001000401c0102c81c00d032643d8980a46900005080007070b001c010030600d030005010359105481c01c08421242c0d0b6583d00e4003410391108240d040307000c244c0703840000700036600100030749030184030b04d071240b8038110341d5555880300900c2c0492032051607400f51708980b04036850402401e8081c200024070140428041d0600d200f20085592015415420040403c00424810030106401c20040e24288402038050b101d000d041c8800145515000f003210b40d000900350f0300f092280c1707007106c9041d026145491803880c00d2210003482408043c4c041000000d911000f8980101d91241642c041d28110100e0050000c040302a28a264020b59007540c1c8400b20006111a507a144003000307140b010503c459200030300e0060b45819104030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 927860341 1250 927859091 927859139
    0xa14031908120c0409060603050411040b01081306060b0a051309060302060a0806121f0b01030e120a140409020703300c0c0204021215010206040f08030a1e061509 71
    0x1003c01d401d1800c41040c0c3e006400d20900c10b1003c03a40301c80c0010014001110166004015201c1d09201030526102c0d0800131001039403003205d180c0e0795900c0c240245440040c02c44429965000003e65040841c0c080c100500196950655032410403909284c440159008068070710716000c41040123a0303403a4106e80102ca03150038510541e94800300014070034041040b18210f1401b80c0c1c03a078403940e814541400d40030001c40d0341080040c103007510011005c440341e840404601d0352010310032114400003a005000c603001d0500d06404a402c81899402e0207400c2940208203142c0c020604a00705600884210368240e032268003210540c1d01074011a040c0c2d088900c8902c0401e03560a00208480d00c2040744030707c5150060820341d43d81200790204025440200c0350580540c2c015500480d1032761021607010b024a80120018115005a0b181d00e812a03101410080c812540d54109618007a900700071075000c81685000020042d2400701603000303408050100310100725100300240b101e4044256100f070050040c103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 927861591 1250 927860341 927860377
    0xd26070504030f0c031506030503030f06030c0a082a01081603060b070818010c121803021809010f0203061c0221030309010f1b08040309050a14031908 66
    0x1060300c9500c680e81014210b070480c0b4180c5003d1100d40040d210480c1d21808401d0f40e1000c180f6404000c848083c0401011900104003181d00c2506080c06107410100c0101a12940e100040008481030041c0d8032025058020022900d0344c01d202c0c2001c00e41400d9540c4050b054400e100c00001c041400c010111180100480000c0280c28440d80c070510103444216900b41d0b0720302c164101070040342c001c2c588410001182010080181d40f240c0314200c01c145d444459010000c4901c032040d10200c800c1a0940380305d01090358000b0159480c3d4144000022800300141c4140c182100c549095031340c0e009503810700900400a120040d11104600f0181d91144002c82e52203000d2440007400d4103260302d050b8807015480c0e0313000341d00700308000c00194000c80101008000110304640800155450160f569800c0310005d4a032440c19801030420075446071192400351016030700c034000106501c0180e0032240500e00c5a0b034910026080c20400032484010310220440035081c40c2d52034074124030684a1140c0035041903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 927862841 1250 927861591 927861601
    0x402031b1b01020406032f030c160816051506030309060a020708250906120b0a0e0d0806040b09010e07050f07080a021f02070b0402120a230d26 63
    0x10040074100401d14400a564507030b601d020040140140c69880c42020400f42000c200d003c1c1c09041c8064107440c2e10540704e0650340c505070140c1107078200d440040ca210f14070354014000621500018a8100820340e0250780030307078190410610701400c4982030302c95035030900c040c44015900002903d03040f1208868050ba613415505007203003414419030101c0000c0c810f5034840102c29001a40041000a0032850303681e400c0d0361014208252009441480b8546001176501400700b10844503a5500441020010840c0742741c2108c4640307441c44034a91f140008041e0018042c20b03180130700038001110f004588000c20b80d4100401c14080c1c442c043d001300284540000c62080820640c01510381302c90b003201c410394482103400c01c040d4495555031401d400042c0c003003d09000c00c00551081c0d480300c540200c00001d103aa9203600380803060942000b00f030801d100e40310500e00001c6103114110344203600b8208031000301301885601e9250070345000b10203051080504071015a041420484100310310008540215038583c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 927864091 1250 927862841 927862867
    0xf050d050a08161d03151306050c0a05030a0b180a0b0f0f0f090405010902090702031207091202040b031e030405100305060d0f0812160206180304030b0c040b03190b0402031b 76
    0x400407206c0f100040c0d441000503018074010712461980c0110021700155903044106802403140d5888000400c00500208115400c03070b074042381b00300b200600490300340c0d120200c0c0e04202507402c8078400c0c0c40d2500c80000115034203211030a0940e40c4000d443c0303048201d00320700c0041ea0001d80038103c2e902580e22280043c0c1802000d41004801d41d40140201c00c1600302050000d403250b001300c400e41c100d031442501007142c00f407007060403104035182604e005009202c01e0b42013002516200c2c01c2070b0390610a000750595142d000043c1952030310040d40c01195038500c2c040034132074988910490081450301c0e000401c5419160346102d0f0750142d40c410b510440a111601c0c03d000716016215460000b0343e090340400c6600d2203414103104c1e04501c0e5070212005030340c500c8a1404a010460300041d5250000d20040000500400c0030540010201401c1414143c4a080078035a681080741c2241740500c041c80c0c03d2583c0c004034450407039508001d944c15032541c44c10f40c0d40040d056500b188000585000000c1c114042e0f00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 927865341 1250 927864091 927864103
    0x90c030715050c03091008070e1504050d03021612020112090f020d1502030c03090105090d0504090216080706050f070c020a120302010b041d0c090f060d0f050d050a08161d03 76
    0x400141b0300003c4083e1100700030f01c2d1000072203400b030206103100301c00b4690b8a802e000a494408200811a11f803a0410091203c0034000840490641c421940609180719092201001070b00c0940410398640f502800014201d030364040c10350b803099240c0f88000000c26000950f107064280c054503200d55000700791401c56584410f11041c00541c070b00c080248400c07606410002c0d406819844020300640c0c64404100c0d44400180741d800c004608204410020b0402a801400c43c84500030800e00c40c400e1741f80c58034207559104100895803a42d51340704001d600640c640080d50804410300e08078008040b01e0340803514079000c600406040c00c00c042502c108241c400d41040c0c40e900c80280007401a640255941d0140c3c40e900300800072107005041c08031100d402c2914a051007a582a075034480141c036041c0c10700034102a45c11094484100c0400c6420101d03400300700040f8980303078950350542c2d03540700500010503240c0c0241c0041c1ca80e500508411459541c001e14404500220a20241e4180341210006e40741817 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 927866591 1250 927865341 927865357
    0x92a190b160b180a030f090b030a0f0608190303020d06050d0c05040c03090f060b030304030f14010606030902011215170c1009080d0c03020a0b0a05090c030715050c03 73
    0x254000400328010700700280d005a03034034814103503480c1c41e488003441c0103404251802c5100165114100160100344158401c0f548864982000441542c036030304040a50b5008a82c0c807002103031030785c650700c2100280e845410020910301c000b40c680810010175100d40040c1ca05006410146c001c110001c221045510070350040000401c5d51400100c0c83c50009140351980c85042d01c03d6180009192000e0701900400905c07540c003a0900200c03201c29a100b800505200406a4141c4424000400060551000349071254010078110b506480d09000c000e09440d9950001400c25080860000c0186d801404038021452802004240d840741920340800b45400395100780c82100b03c000482d2040170010512080d100301c166400355100c0421101964441d0386c0b8070403104158042e01e60200d0083c0b05540041d940c0c2c2c844c1c816030761001d055449401e06d00200759241010385640b00244201d5400401040100000980140c150f06181944000071031811904050034004c3c0021070600c508800c0c07080303440390 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 927867841 1250 927866591 927866609
    0x907080609040f061506030b0a080c011b06060b0a020303090f19260a050a1206030b160302120f090c031b010e04020c0303010e0417041413021b06092a19 67
    0x9641b2140103018112092905000d11009072001c0348510000c604075400b5001a19501c00040401443c030340c00e14100309080d01c0302590350101180030148603008103a60700e5158000c42c0c4904040d203180d404d0000d00060951540d0000d01010061040c6903002c04205030442c1004c03001941000060101074074040c50f01c2051003002078601031964210700608140001d9980d500800600c0ca031840048400c1c80c00041c000c003510310001880121001d202076012811441c015040000404405420107420f4078002c266002020070001c10001c10010103400d4003088006103050320028100302d5004103136080c201e04001039800d0401003a11242c040b10400f04070501207d58943e074803460003010b110181e03001c41e10071003039500300288158440c01340c4043d1200980f58240e00301c5540e04110780306000e102015110740c1c0920900410301e8120003002d41e100c0343c0f20003403c15032900d00d600d681041a040096061070351a110110045601018201c012400a858190300304e201c034081e02c903a0220f00e40c000911 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 927869091 1250 927867841 927867881
    0xa08180307062a17030c0f0403060605010f0c030801051912120e150306011d040e0604152901020109080307030c02100912030504080f04140907080609040f06 69
    0x40264004081d0009051100f00c00c03200c1001c2c00400900c9194442c0d015040220f503a040301d00d003042c0382009542040854448628126000e024507029402035881a2002d503a00c440c10001541c0004488014007450b04d0005d0f0016003030380e0058406441802060700a0340d40c0f0010502c45c910020080014141000b4946424155403601c0d08040325400c4600e4000350740c044a070303d039509182e0114014003003c44401d508565402004407841e0000c3d09180c4422100d03900d20406980365841040080070f00038018081c0c619050074100c0c100209840710b07449862a007800b02c1d16001c178a8034510380213440190520820050323480101e000d041010006056194000103001aa607059030110701082241d4085d02d64043c0d5044d43c1808441c5000d0014000300200c50107011024803a6200c0e07030b8098410a5100d0a003a01986981c40310b421940250070103040001c0300300814942441c0d802c1d4008840d1404c00380901d0300402090b200400504014041000b003d1218204419074000d4981400490b890718a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 927870341 1250 927869091 927869099
    0x204050303270609031b04180605040b100807090e01270b01082e0603120e010305131a040305071205030610091a09150d020403051b030a08180307 64
    0x20b280310b240c40c1c40034a0549188400701d4941805400d0720034195001300075140f03070b20b05164040300da840e1620f020341d031041d95008400c1e1110001880800410701603080011245018500000150000b918034880014014020032406000140002c2035a03401c002c04a8112000c1d0a000d0160250142010300c941c141d111041d440d0004a83c4a40700c0d5014111810380d90b640ca030306254a54005012a2101c0052880c0c103019401c882040c1010031014281c001800a03600e480760341c00c0701410031841d40000d090044808a40d80c1c03501440340c22640c3d0f140c1d0043c0078462559032150b40324408503d2310071541e1650019081c03500803015900d000d90044080240c9905240009056904c1180c8841c403540a240003042d5a51150351003005513080400040483e003c01009240c041d00011000d90b80a040c610301c00754041890800340c20500d401c440c001da01e035421131600c1ca0900c3d4400801e03c1942c501400c2d44031309564009030070441150050042962500c0a03002d16070940c132600c01e169010710a0f004005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 927871591 1250 927870341 927870367
    0x24060a0201150306050f0a05090c040504030e04110a090602010b0913020d080a0305220b01031b170609070501020607020d1b0206030f04111e060d0204080f030403030e091909060204050303 82
    0x786c401c5c1481095282e140e61103458120444600b03a85c00c044652040c05c40000d0360810360300c04c070f402c98040d051240300d00710854005820b4842c0300d19030481143d004207044070182d40100103003002d80a01d0000784803100040e004100102001410120b01c000c0c2d20540d4019503d03404225090706400440850361a0103017000580a8401a40d43c10305c021041c130742188200c0040300d51f1450040e07014480603042d0746503448048494022405940390746040c40000200c0340c03010086642c4c1c1486110107001c181c03400f4080281030003640e40c000d03070540d04031004001c005076000c5031500d00644103007070440c0c030821151401160615a600000d40200c000001d2220034002a048107128901c1961200300700c01e40310007440000003001b4030a400180c000003102003a031420300c1c06000e5121510400508055a030240a1725104250741003041d16000000c0c01d00601d640800083c1d002001a100303481c1c035040443c8001a60480c08401c5182e41d982c1d0750442c000c2100c190101c4e00200002011661a00d800c0b00b00300c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 927872841 1250 927871591 927871601
    0x1005040609140931050c1201330302131a040612030309140d0519030507050304031803021905122b0314040b0f24060a0201150306 57
    0x10584007007000800e200c20140b600000c0070050a000d102d03848503403042e44481c9070300c2607403506203e0500c0c0d0056850b4440e620700340b496004a008001c900100810301c038028280e241200c0d020f034185080d100007001c10314030031aa400104085407620b01d0300140300a02140316908001e500a030709284061405195801c950300c244541d4003002c5006041320104003c641c0b4520490196281500085010a00070780c80b10306010301454031040c450f498480514101440e507415000400e802041d0007601c404000c50031004a072890408001500f4107c8010b0310382e0000510080402c82c0d258222512003c44c030b1480e6005550140c0016180200007041080c00901402128060002d03d092a031200100082d035284100d030b43e50340100018070514848a404802c1c00740a4285a204c000741560002200e1142d8400c9000d4200d03583e240c14800f0081314000c102500c64541d21410451110408804c0702c00d82200410480340341ea982c8a411800b6030251078800c140c064480c03401240001400216000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 927874091 1250 927872841 927872849
    0x509060906210a1101032a320c0d0201050114150c100507020c03010204051e0d0f030509090114090a0c020f0609010b03070806040305041505090303070f0b0c0703051c0605100504 78
    0x107000c00f1600c0745c440c07a8401c040840ea424000600d647d18007805009025006000c80222004050140302800b100380408000d48100d0404c04000f8070a01e222406020b416000f58132480240659403418031071040711289041c00e180310b8218203c0c00507400c1d4084040b21318a403045400d40d42045032070a1008000c25007100e0180143c000d10b0071209262038188220380a8130402458501000d882039803a07030071030401d844040d4000090848080124030b0403585504100e1007503039441da581d40782e5000d201104034103a03c10f0301581400c8605000b80d40e15a103034a5405080d900c00080c6400c42698101c2c50b00c590200b4a0046000d1035040c481e41c07860642006400340004c0e411581e810f1358070340c981513035241c040710041d0028009000500542880c0350311000e00d42d03200e20b005400d207607000001034255401030b58202c0b14240319224000030440a00d080b82c1c2d03c210300929460500310300d0380300500a840341c2500400040b0000c3d1510b418800ba66009001409010b440107850300041d07400a03000ea170007809 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 927875341 1250 927874091 927874097
    0x40905061015030c05030c0a03381206070c060f0c05040509070203030112150f1415030c01020a0b040f0b0c04170a08040902030a09021f090509060906210a1101 70
    0x101d01d81c440f406030041e9148503800b551030034a590354610302d905503500040e0902d41003580740c1d0031510588103520b46252620340107043d0b12040d03a0320510059402500f900c2a14011031520704901170090010890b0795101e062814151421240b9240440c018192640c10701a124a0302e8081c00070958420054000d551041c0c0305c0c401242c4034031505a80e6030000748106441804448142c00c0019a1000303810f0403d0b8a4020100e10000040380f190306070f400e149501c0000000703540812110005502c030301ca01e40c0c0026005000c0c80e400110000351610748090b0041c00045a08010604002c100c100c2c0301c4404da0480b541c0d010344c3c181500307000c601e68018400c50b2201380e5010020810b00a002c144000920340c0412071900d810f24080040c0c029420086c400000c8542d1601c4260140c1c640300c07207074182c4410352580a040c8503a0014040c0078002240c00850086200324100f00301c5807900608540c12070400c03104032200e01c4420b480510006840b200d031040307600070303ea004000c1082e81c10103010900401d072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 927876591 1250 927875341 927875369
    0x1806180b1507020f1005040e0123010e0f2106010b030717010605040e0a180c05010207320319030206150105070b01061211040806010312050f0f090409050610 69
    0x100c008807460140d988069401154194a44054541183c2c0d008000ea0f036801c101d800c15980d07140782c100461003640502d02c0d6405a840c1d1040380d00b40c0441801c100c0009082043d03000d4854000321f050340002e0010180200e802861a90000c0c4030800c0c540d800c116001e0440e000b41d1307194060134400e0741054440e00c0104000380e031880040104542400d058a6680e034449050900d0408507408020024254038103c40e40c6800d440c40c04d0f150040844062400782021a8036a403401d00020301d4201c590340080a10040300c0c00b04211040075010f000703008442d40c030b544054a1704070070010b03040244040781840100e08000b1020700301500804c1c070b40d1140928407807101b4014515030054584e445009c00003018a0240001400042c0c007520454150b0604c410b03002600034690f040317803500d9a2280c2c0040c074640d48220010400c01490702000d0010744038510b842820400401c841012a0042c020705a000100c00b083c0b501640c1c4581c3c0c0304242e0550014215211030910b061840110007550181c0c4030f4005d156 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 927877697 1106 927876591 927876619
    0xd0e0d0206071b170f0703110a081501031112030d0510080d081506092101180f120809030a03090804050901060f090603151806180b 58
    0x4502500a035081a1130401c100e500780001e00807940c004540e46080c810f0204070341040782e52240000e848164100c00180131444960842c076010700c2081e00c4c80740424122200d040c105d9000e00311281c80c00f06a2401c1c4a10078000c6140c004d8a944204003000209881da4000ca0384080780c0b41d1070343c0c04140c036040b0b0242480c00b0111100001140305090241950108038843c07035001044511a2034105010046002c00c00703846c0c0c0320111a4400c2d0250001c008083d00415078145400500207104502480c1c40b03140c2620084e004e8805074428840030700c03200c3c060480d1034080c4014000441c14407c8260085010f00304d5440d0807100003109110004140e200c602406010302869100c0700c811030341001c8014000111607003e542010706018441707031500d072040d8064065603501e41003800d000b0381031003102002d010140c0c000c8032000005600b40c0d41c851180e40c00201c41c0c0804803243c01d030310049 = true := by decide +kernel

theorem cover : BRFrame.Cov 927697841 927877697 := by
  have h0 := BRFrame.cov_init 927697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 927697841 ≤ n) (h2 : n < 927877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
