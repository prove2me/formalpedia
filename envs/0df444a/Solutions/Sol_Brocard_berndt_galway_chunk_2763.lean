-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2763
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:20.709156+00:00
-- url     : https://prove2.me/submissions/98a8cafd-d0b2-4135-ab70-5f131de623d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 496762589 ≤ n < 496942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 496763839 1250 496762589 496762603
    0xd03030536070906051c0f0c1d0c07030f0c0c03020301050703050a0b040e0d20010c0f0815031506010309050d031d0a0209070503130611071a070e01052a 67
    0x4a854442c4281c002082c14681c001c1800711080102800c0c030f104801c040204c0001e0040e10103c9200700c2c024581c40c001a400c3c03000d10068450074164403000142a00110381800c000303000006d85040a100e80400268081d1030701900d0103072450525040e64003854020010511608029070550a08041003042541030380030320700c0b414000740140301380013881050004541d146521080d00341c010040b040d030500e0050460300e4250024000383d030308100d4028080741c09c407040700300343c200081e49107084001180d174040042a000075815a1b596050a4020002030341c8152900220780716070084400a80d1581c001d070b002e81441c0b078118081c2c3d03d11b440e20810060080c1040c00640d000410555014105542d00240d1007001d80d5002d0065106a115400c0a0311680c0000704195034a078103840e095000101eaa001e80380c0e946040701c403c1511024503107031031421006604005811403000e001000f510a501003100c0d90f00071402e080c00340d6650221a084000f01a000c4507a00d5003c44c28444c030700c1a500c000642d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 496765089 1250 496763839 496763941
    0x9010c030501060e0108010e070507150c090501170703090f140a02090c0406020c0409080c03070f150912031a04240b09030d030e03160b0a05010e060d030305 69
    0x2003140b680c07124401d035030340c0c0c0301c1d02c0340c1e140010740410041c0011046441d2840d080002c13410b2950402044c0c3d540c2013010007001c166424010340baa11240da840b07400032080400b0b01000d00300b520900b0040c041192070101e00810b4181010b80324032030701d82031000f8150201d1f40076820041940110064024265944c601c51200324028002c240000b800c8411180c19503066524907409060781c2c0303a6120030007000c0c151203c4c00f513030f1640c1c042210b41c0d4010000c000400d54507204000242007007045003099031050001c2540b5203000e50034400600d00140c2c1c1d07907100d64400c036650708000420745840958881c040300390b501081d4010b4504445081c0c0110f01000000c0e4051a424a00d895541c849200c1d00035030040c0064503800d940049425007200d8041d8100d14603000d21841224200420350400c000c0c2c02003074480a43c0c0c904888014490700d00c80381d00965000d042102442046420100045418403140140290405d943d80d00496201441c020402460f0384d0703c00d140440008822421141c041010703020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 496766339 1250 496765089 496765091
    0x1e0216050d021b120f070f1509050f040f0b06160b0a0b100f1103040603020403020319200f0306010e06130c091511010e0f010c030917130305030309010c03 68
    0x401010036100003191400c41e49550760b40700c5112103083c1448075640516002c0015400750001d8042c00c00010002d20340203048500740740075142e2030f04e000e2950803203001914a00300502d607482031200e03445e54003130120350030b40940380000e480300e0041415006064041226038071000018040c03010034416040003010034000c030049000381d11106110b404448074800300075002a0855031f40e19516001b8141d18005214500340b070110b20240510742c1d07045a0150300541e0200b54041001d10550604000703a82c2c0d074a2100000c0299203d05444202103145100312039048921140c1d20240240c90704405540c41c004040d0032603106503144d41822900c10741c01c40701b80e4040c20400000243e0078800340900e1400002d5070f11a0844d59051203209000307440d03904892018844142480d001c168403d05c00e011200c44040c0240401089040341c1500303441501c00071030b00f054140080c150109801843c01c1e0a00400101c0d85591a99030507820303c20380c0ca50346d03c0600f003800040200859200190400c04002c070300303554 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 496767589 1250 496766339 496766353
    0x9040e010203101d010b0703021002042402240903040806010320090c09010f05040e040b0907080c13020c070e07030f0b010801180c03110705030c0c040c0c061e021605 73
    0xc000c500c00c4148545404d5021074034001005544c112800400500d4005c0c8140d51071020003400b44c805a91007548041c104950070145801c88140544002a0a03407452001d403130010481108403118034a80c002d402500803000c00866000c41003082200c00a04240c002d4814541c3c2d68207109546450308150002060b030b20051241d050302d0728407801440b60f89154020703420480c9001c01111a03100c00d005090500404100116001c024079a40d0303813250f445402d107201c1c640f44c1180000d04111151b403100280f540448840c80c0181c3d9810b0a051140c2c1460301c00503110b030000508245800d01d20707408a003103800c0500a104840d03501d0341111410041488040c02000414001147c9500c000d00c04c040b404107201c00640f10300c6034103800c000c03001e0856240102c3e032902101810100c50340303c0320045030715901c000340c551a884414401844403000868040080300c01d4154050306541800304001e09042e40c43c3c1602084070100c03120201d00407141e43c002c42d129402c0c400c01074451010f8600a48651003000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 496768839 1250 496767589 496767599
    0x2103210a060605040303050f130509040503180603060102300f0d1415041a04050c090406050f01020c010c2a0e060a03080414031005070804120c0b0403110309040e01020310 75
    0x1001310740440e1b50669481e45841c45000314980140c01c1510b503c83c0c0c0c8400383c100028240d036511596030007540100040d5564140112201c2c2d01110140d401900402050040214580c1c01054040b40c088064030b040c0184182c00d2080790900352803400c2070b0219540031a1115a6500d688040c000c0d80901100401076601600b60030002244111000d55408891420581f09814550041c3e22100c03100e50094642c4022100003d050f41c5080310840c2260b44003241d01d01203440c1c64000c00000f04400d8510040119891000070346a658141d2554140300719a069402000080d280001c03e0710550f2030403000d42254041000fa08241510415400c0d050280c00f0035500d1920401d01421030381d21179485450541b03040e261040b2490740088250340342c000d01c81d4103284400300b0300416115074042e40e60300000d4949482e00031041141a85503104001c5400810350014030000d0702281c0180d0076081c010b85407040482d40324038510030244200d4119040c00207002810b07005401941c01501d0207003e0108c07013500c41d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 496770089 1250 496768839 496768847
    0x11d06010515040e160e030a06201e03181501050117070806220f020409110a020c190b1b0d0f140304170c0703020405060402092103210a0606 62
    0x1500a50303c0c244a05800705200810800d00489109064203001b000d0300c10504c006801c1558201083e0707920382d183c1c00b1000080c0e200c420002030240030030031082d00300614082d03102c40c003124520304802c042d4030000c0864606000c400d045102c08200408490f210001c0d000040d425010030b200d051f001c6aa03040384030010454002c0102c0c03040000341d490100c01d6480342e00300803426101d119881c644005200800c410304006004041041300c500801507a100c1c43c00c010001200c01120159009840503c00807081513800302d003c01c1c080e44200c400180c403402000310b801c0030b1040d40d40101091040007801c8200318038220003c0c43c0785c044540070360303255400d0b03c1800c0d10810401801d6400007000400c00074244000b1a000e543c0241c0106051411101c05400c118003035841200c107000507620081c03041003145014002c90768846815101541070489400204440c0e44800c082008404c5a0000c800754510b07003001503810080d25180510a640d04e43d04000409440650b07500e0401414540080307400c0d409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 496771339 1250 496770089 496770097
    0x6030b0c12070507030c0312020c16031505040b0429131a01050d0f11060408070311041e090312050703020a090b0403030917160f0603050f01050a1205011d06010515 72
    0x15201c1d0f42002d02595400c548c40b021a068500300f0301d0b82803117038240d0a0801c100714a80666006c0d6040585425070410f407298180c01640f00f20003d0400c020000011031036490250080d500a007201c070209859005800f50b18030700110310602803000310420406140704041c550809001d00401c01143c4800451f425008009014041c0c100801722803000c0051843e0090129003801000807146907007245000421640c001c2e48180c1c0d9070380c040c0906005001c0e10070844520440122010441d100e040c8241d0550441c0d2000340c0008941d44d9403001c02171501584000c1041c40811100300b00d6843c04280c050001d40000c600c110004240c1c80740865451201c03021031342030b2905511401d00c1140b0705203200c004ad02e120264282240121a04120386440d21227810001d0250b12a5014119040400040c1104c1d00100104d03e034005041c010045c0d521804101c00983d00030321505010805903040103400340010404190001002c5100506001400321354581a45d104991f0f581c0c1c2200c110506003c2405 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 496772589 1250 496771339 496771343
    0x41e0309051509030a03091805070207230d0303051605030c09040203040c17010203011d0423071a0a08130302060a0b010c02040e07090b030d02061302010306030b0c12070507 76
    0x3200c90500c0725182c40360140d52001031200080703180400e200d0229003040c03601341c41100403501c0c0e80d50034040e0780000f10b0f01c19182c03041c1142c100310600d0003e40095482c000c1d031040041c45910f8850044000401e400c0c1d03050700c810007410354084007a407880c0040040c0030449111444c1a0300309041125680300d04202d078060200d0310201403c1001c007000b0040254030103001181c0022500400144403180f405850700107140c0c0784001a01e0390326141c4024405d0001c0205040c09103450703020480054004029000000c6c44803001c0210001180c1c845880c10900d9000b40350108082c801291075031507510002d1010030990307a40c15006803580c04101b44220010400280560020400074221445691200c02c90110500d000c055281c0d198011a0403603135039048c111006d0300f00c4070080c86040f8403405903030002e500c117500802c2183d48c0c88d440251920b2001c3e014451501280e40c850b01968840e410007805550820100c1d40360341000c0c02d420403650b03c034129582c4480390701c0d0000f4807094010010744100075 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 496773839 1250 496772589 496772597
    0xc2d0609030c09020f070c0b0a0e0a030b16020c0d2105120a0c0e040504050c090f0c0406030e0325170f0f0c011509090311061e0406090503030a05041e03 67
    0x83e00f8400060003940119040400e91241403001801145450b40090000d00d1000c40c0e099a035051110014642d00501c42068003c203035004d820800120324050140d1300c40c40b81640c1c48015820607004904051002420503880300c080100d210a1080c1000b007048403682109203440e15410102d000c1c0e13030501580d030802d5a55021400000c001030b1850700821501406484d00e004d44800c0c20700014121442503d00340d850f175100c415030f038449040081170300d9042014061007000038a4210450001489107000390300070192185a811050350041050303a8071002c8c80e248a440c49804581c0c4080014005482500d2840090300040c4445200b103003242c10081645034001e240058060748128103900400c6465011343d41d03a81301c1e03a08501540d00e5100070300385a0002159548041c00d005183c008080311a42c0f0710f400040600c9100c64151301e0007858403602d41d2000f5401c0d47e4504000000305480d1070050406d0000000b0040d01d0b980302d40c4031920461285081c4102074801d500c0c1e00d88140300354031004000c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 496775089 1250 496773839 496773863
    0x15080705041b0207150509100305040506060901050f01121103041b0e0603031602030c04110901031a060a0f14121014090109050a020903071403010c021908070c2d060903 74
    0x10300c0c200072a000d40c13040c0c0746c00e0071803408100c580891443c040c00400b030700020ba5500140710070090140038443d0444421143e12100d5414400020b00103450f01483e94103000c000c0c142c001c1d40c00d00b240c01040f200c01c0703488904d036168605401c207509030051107403010501d0001c0f5680888c80d946113014850103940090015414842d140e560001c0245082000b80d07814410303442455220765560250b155201006100180c03514003800015050b81c0040c8035529048082031104001d5444803000e40f101090b051500010b128140e410989207008140b024892480001403400d01000111001c14003850100d110658426650000070001c0d1f281c803620b40c0d50105629004001a0f0001d03080716811801c031420042c41c08022400007490b0040c42e9024450440d51284090000c0c5000c0c0b2805c2c840c03034074074005070416003030004601c400c41c041d0382c0000382030b13400100d0604c0a03c621000d0200203000480d1428061502c440b0481c5110501e011002d1403602c03403a0404541d15202d4031500d070450b13500c840c1840328 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 496776339 1250 496775089 496775099
    0x23101715042a181203121e06031104090f0206070f08071a0c0403050607201b101103120703111206130608120f0c03041d0a0902060706050a15080705041b0207 69
    0x19400b0306d20341810000b0340700c184044443e50340441107201c140d08040c1c001800341c50341c9801c0d032140604154842c8202c1c90400036801040c900c42040d5000381d81190b00c0341d90341110745400154035400399000b80c10303000086410010011030f104942c581481e0000b08400a94030040c0b01021403099010040c0150031800110f04503032f00078a242c42404034095100a80007040d100f402349000c542a0000b05001080500300549040c00d1041029007843d070300d020740c2001c9089010942c1d80c41100d078101034000c0a500001e007024400e500184070007416203103459849210300303034143c040c42041d84c8151262150f003424070f00c5580700384550000c4585c00d601914171000b0700b46001000350044801a06407100410a10b000c034a0103000400244c2646140d00a001e000d08605895440000709006c655500d0f1074940c40142c0c0c1c4503800d4400311540a48042125030350440003401501075130015659101c05120082400031001c6030200a4031020785013005962010500861804c4021314a040545c10461081c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 496777589 1250 496776339 496776347
    0x10f140409020406080321130f0f110a03080409051f0501030e120d060e0c070305180105090310050702100203040b0103021923101715042a181203 64
    0x1142c002403000078555903401d1010706590100952601c5a0b561840d918600c1d80c00e20041c0350480c8184403607020016880d030f0340f16121501843d001e004005880c1c411802c20160787c00e00c4400c6000038103060040742c0d4900c0c11501e1900640182c035000343c200700000d024100070101e14a016031a0302c0d1740303041807443c000041d0024180903055032180d0054401c0e0b4120360034820020071446541c4540024031a00d0044c109100401c003a016084000e010801030020903801002e4030082000800c00000c9000e010005070f40c0c0340b140100340c07a0140101540040204425400180b1030b21a82c1c007035811189c00000d250040340b2044a000744064ec00304014800b50501c1c021140240c100f20b640bc2d6846a01c4000780140b00240e01d81c031100700c5201951803042810103000130202e00c1c0c018100700700085040301d41884101801028203581048003c81d00751955540e41048116010a00100403180d10a086014121032030f0300202010030006010309801404005515040b210b42e080501303552480c95500f12 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 496778839 1250 496777589 496777601
    0x108060609030304050409050c010f051e0904060302100201060807140603010312030e1501050a0f031505150a060203040905060f011b05070f1401020105010b0c19020d08030f0906010f1404 82
    0x1030b010b1000780004156500c551040800050182d001002e81d21440400102240924103240003040002d101c101900491449041e5001c100c046d5007546541c01d10b0040f80003081e580c0d001030b5001d080d20700040300c41e42e0107510000903181c150050350780058a8082d1315019198441545030494800c000400c04030303480c5140d800d200041c0c1c0c6030201c1c05580c6617941d40c5c50303c2e5100006560b000c1c0c1820041205290000a081c000c20300020b03070550307131860350305d0b400d01c170142021300116100d446000251104246031300742244401b006040c0e40086844803c0203540e500a8001d001c0c40074074190104da8075107013141540d032900405035601c101907240111004d0592140c85000c560502c02c40801055600403144810080c043d2010131008030005400020300f51070060b80500d00084040001c2d2000880c04122650482a1060000e003102d410b4400f0401ea02c00d0300e0740c00350100c1400b1003800380d121b04611105010b9007412003100c29503621400385e200710b0449441884c05005013103144001509258000e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 496780089 1250 496778839 496778857
    0x16120b060a0b220b0721080c070201180506040f0519080604020d06020f04090b13060e06011b120816020f072c0421080603190c080102070c0e1501080606 67
    0x10f42100360740d07060044210b40210a081700c1c407003882d0222404030308030826020110512803030245054108004605907a20403400d001c0d0401c814041c6000341d02c0310305442c1900600d40540701c15602e40d6154038040c05a1420301545214003540f40d200740c5940b00e03043c451016130700c0440162842e610340741e0030401c2c0342d05000d0701240c0340c0b50240070441000c1c011101410007402c1041c030106081005508210315046001c1ca0240e4141c40c12070309002e042484010039a0000082c02c01c061005526081840c142000000090032107a03040c1c966000c4d10740c802c1c5c02c43d00441c189a003840c985840710b0000d036264000d401c503200c11680019000c209916043c40310751a054050603800140c42080065104000000c8030b0644448000c1c102d0300f90b5240100e600140340a03161b01c0c0c552843c0c213003080000c0e1503200b0685111000c50240028005200b01694000010030303007200210b640750721a241104035101c8030301c01c0b0a604000d071400203444980d854240c915400b016901e50407240da030002000f41307640004440c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 496781339 1250 496780089 496780147
    0x60c122a0a08071e03020a030b0409050708060105100f0318050f0115090c1d1f0206070210020a02031e09130b120106030b041416120b060a0b 62
    0x40109004400c400102000203840c0055a11000d102000d0072118029014000304510500036001c107640a4100007564146881c0140e6140c80f100000c5014008030f1400b1039100c0d00d864040f40410500190610450341c541c2e080c4c5000340ea0360320400800444207500c1c0801b10380f51203e10061544070781e01030744580050000b003a04406a5840d170b03a10301224007040641030382d035458000d01c8480384801d041d00142244001031040c03510341e9a000b060030100d10f48291421a4405183d0440d6403a0000d404d051b084810204161810100c0001d5650600351884005401140c1c419040c2c200140201c038022190303074008500d00840b1800c144038152803d01950000003040c000c4800d184d0701d54403400e644170117556001c20404c5032501040301050002100169581c0741004c00c1001545c585074840c1d000fa001040d005503494040d0040c0d05207071034900781c0e901c8000184004112001594841038919006407680600d40d80c1d0b64041c8190f448003400742d2005804184601100300c11446580c0341410000350b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 496782589 1250 496781339 496781371
    0x12180e04051509030909010906050609060d0e03030f070e0303030103022220040f0503032104210f021608120a05091c0203060a14011418070201051602060c12 69
    0x55207040d45201983c1805540d000010b4440c500c0c5006410540944007849040108920f0100006d12900c03d50710598010400441c50900c4a820f80e030020280c4203103101920798034540648488030b0130404a1b160400b0030316030805030665040c0007058905a96000d885080b08008084d0f841d8402454004031081c0d80d074582e00d0309141e1255030301041e904000c00030003040d141c038104400c42d80c01c40703225040700740a68070610008020304910070001920031814650001252a40d0810204400c0d903000c00c41900c1d03400841d60242e041c1d0115184041c4402a420f0390383c0441034800c020028041481915100d911540c07c1000088002005041d180d505c0e00b8000c0c60402a0300100d08248110a4501c40d024134410560f815402c0620140313600900003007040001f200340d103081004411041c05801e00383d2400d08203980540d00c990204503000106085440d400c0e181040d0700074081c01c021102110001228007400c10402d00008100e801a01650405400e1800c040c0005901f0440148510911880c0702 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 496783839 1250 496782589 496782613
    0x9020301150816120510230108030424090b0309031204050303160503070903080a09380a020a020f01021e100506060408030702280e0412180e0405 64
    0x1c0004402821040040c1c411207040c3c015020101d126640480c003001140210390000079004036074401c89210f0f49000103041c9030504c0d042e50b0443d01c401c082c0c1021610348000840c903890000060000c54200500320119034088100c100c02155110b80401c012135a01141800f042c03654002560780b01b082030041781d0400102414030b802d004026242920590400418448141c14051031500100b0040c1803407480d40c104080003c3c008811703844040c1000b400444c040c20301c14850381c0343c7c0005007611310860207401c2c12141c00314052134a81801e1100080b030104070034088222074090390300300020394016003d0704000d5000e024040d100302a1290443c01000c1114500810001811110245040c0100301050342d854100b012a04085c10840c49201d00344010000c46100204582d10075038165031807880c2d50143d00c1070820714140394048010f02040103a020038010740d10248981704038010907180354040003800050304c000010b9103269442c01030359081803004000b0300b080c8a40145c41641110903214140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 496785089 1250 496783839 496783871
    0xf021b121009200307060c0303061503020307110106060f050c0115081b01020c0f01051b1f1503020a0314030c0a110906030d081b090a0308030f0f10050409020301 71
    0x5912018803a682c0e91085009010001040c14903020100c410420b280d60780c1000a9039030112817241500300031030910001c0c10503109030402001000d000c901640c0c0507108100c040c000e500100d906000049100070858606101405000116451900d032403040000852045403a0740c04a05a007980f03640f200310035182c13045601c8164000f000c2c1e900c0070303004c0801c1d1800000700042c54070312030a0455104c80121000b59681c2c540d5000f01e02001d00703000d82d41c1c1e0360308103d1a00300d03100030444200c180038035069406012100200e00000d008001000c002c07000070710304002e103800410b000c041d401c0204050140b000882011540005080b14803c4904003030305040d80b80d00d4060008030881d0b4103491500c170312201c1d0501c011400d8000600705d0191480d100d0303008005041400040859004800002440c1c504010b40340884022400c0a032423102c000c2e4403401d01640b80d610640e0503401d10042d0a00061440780c0c505a182d008010301c48505c01c1a41c9084200300c0604083c0c80140e03459580c85426081308804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 496786339 1250 496785089 496785103
    0x8240612070810080105010b03180c12060a06090509100915051003110f0904121812030806100507030c03031418070501020109020a0e04080f13150f021b12 68
    0x1156503040081e1070700d6240c400342140e40f1390040009038101401807004400840940303500c0402e4000462041084406c82403038150348106982c3c00c215403120f008803180c00440c44c90f00c82c0a8001d402c4c1711031507584410b10304440c8211000702703030740c0c20080711024100c0c0d01d600540c03000b6000300348030f00304020088449030490f04d003a9404840040819800c00402c4840c1e0303683c007800c00041b5581806030701300380c001c101440390040c40149040508160391064a0007603000d2240c0035052004030010302e480301c1e410a802200d141040d00890a1000007034000e242220307102c0301803200daa40e1281003210558044d00c0001d8550012401d05407600d0f0a0607842040740856403080403902c100c1c80029455448041c1010b0098000038116410000102e000d80c441a500100700c0c0e1103410028001d9440c0c0c10709030b005008824048524100014140505590a000039806d030b4074881134040c1900400701c0e00391001e0780c48030402130150b00583c0b0482c1c5102c2200b108103404000c05898012180b5203480701c2424446 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 496787589 1250 496786339 496786351
    0xd0c03020c0f010c14070302040f020a021b030115080307020306090f0a030f09150c1a010506041215020f03040b0606090a030b07140d020a02012304021201090506240108240612 77
    0x1b010036410019841c160280030302411101c5011880c001440400a4803a0460548003c10040c420a0b241040d1400d60101d188580c0340594182d43c00c4d1a50011074481d88440410380c421301c40c1d03001060b07112201103104081606081c00a102e4a586036900380c03102500300c41c00c40c0c24840309402c00140290b81012200c5034800da56074100602c401071905640103d03c848442007040340c2032006019540300c4104480990300c0b42c2844210003681840c0a5080302d41e0b58981803005030002c25022408404500514002c27846800c0254031952040b09002c8a4050b9140b010341c02a00c00800b000401d00e070210240e001103031072a01a00701c1810207406042540f000c114005d44584c0040c184020650a2080ca80c00341d00d0200e0310040d40240e0900c0e500c070400040c02c080c0c4119410070b103a00c0031080c00d42c056a207160340b1000b0b6440d50310302880c82d4070819909081403030103038440e258510b40c2036100d001400d102c6c440d442448070904030800030002c2407500c110360050f045142000034074290801d000e0910b01c158 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 496788839 1250 496787589 496787593
    0xa0512010f06031101021c14070c030206040e06120604020d031d030a120e010201060807090b130e030304020108010b0910200a050313081b01050304062c0d0c03020c0f010c14 76
    0x199130000a180c4202099610801004803040c80080d6911800c840c21260300240d6654032100c02e030800181d130a0450b81300a50000d0005400180c480342e004e10548603810495410055080d040c03501501c0e0b480807103000b0341c85992034280400107402000c1c001107001d507030001080030b04400b0021034034004d28407030152a8610a06040c400942e8800340d5030307070903120a100a001c0c4a150030a266942d82e06400345d040c186c3d4440b09040781d581c840d000e0303c10840c1140c4a090001e031400540b0305460303900680c0c040c0e000803008030010422002c20740c2111103495000e060302003074500010f070407030b0710241800080c001821840b01500c1c800c0402c100585480b80070308082d6039185030907011807124403081c0e0300010441d086074040042080a0259408461000b800c0c01940c070395a5140c1800100003608245110410811400441071150280c80c080c041c1140105c0d404452401400d40b454058200f004006a00901d07504580303060003800f4100608041c140180e44804a41d550b80d00403142081400302c039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 496790089 1250 496788839 496788863
    0x7060e0d032903060406020a140316020114061305070e0411030621060c0d0624080703110702040f09050102041502060a0219030b0a03020411090108060f0a0512010f0603 74
    0x61100c00480a01d6031091040da10b4248a0100804d8840000a00c00b60090754003095401c0c6850180d0381d01c500903501108415035a1402050101c0c051020a469900540c6043c11609003003d50a402601610b0001c05003200b1281c030501c41e1029160083c480ba007001180000442c484d1614005c0122400c0342086842e240d150200900c40b05a550030302c0044242038141c291041940049856600300062440c0b65a03516451210100500b0555101c400d81d4038281140c03400360325507180c1000d000c4580d030340c840400da101c0c0c04044017952251030210000510820a2034014a46644940c0002203a000c0214130850251141400c81e0040e6000250344004010340191550341031110301d5120451420840c02c00351184001110001c0c0c5600c2c00c800d2541d121310340351203a80c503210a0801954020001e02c44020700e0480c0c2c071a142c003c9c000082c08034101402080c030a03c1c1c404044005c1000c090200c0d406280f51108000300804111195180f9550b00d601180b0441c1e0180910006140129204850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 496791339 1250 496790089 496790111
    0xd05031b0c040c1403130c03140c0f0102030d02090409060e0105041e1101030e150106030209030d0207050609010c0f0803040308040b2d0a020d050f0a060f061407060e0d03 75
    0x14501107a1100b480303140381010341540d5580000110070f0300c00701012069140e40e030f0041e4400344401102005410596016070006c1005900c070810390314028040151000c0c0404c601c14443c80c1d200040c0c1c140d016800620440c024040241e0140058450082010501c0c460544895084800f280740d0310f1100d9440b00204010300040c0d580c1a880c01d0030100f069800d4006540781c886002011107032590415443d51001ca0501000300605a0006070710700b84400349507914035011f4020f621507820f8502a01805042d00030300d1380041181822210050708891500700c1107001180c042c4007000c4211a600e00a076200d601180221010b54410752098807000194209400c08003c15000201300103c00d4203180105007480d40440b0920103102c0c41c0894000c0662910010340b0080d00880e82480001840c01c001c10a41000c004146401012641c000b001007070744801a0b000700e5488c9c0c0c040c02010801d81c110424200580748020308075540a914000761154031800c16a040a05440001e40006d0715640303a401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 496792589 1250 496791339 496791343
    0x60316020c0901030c030206090d080307020c0a0f120b06041118040501090207020d020112020f070c21080a080a0b09070810080d020a02040e011803050309060109110313020d05031b 79
    0x8a0020308445510b0305615658480c0454501130000030f000d04408184070300551107030100254181d030300500300da80340d24001a00030354900e80710118911900081c2c0c000180b0a2440c00c6140581e00c40940304804004c281d10383c842d560380301600c2c003904190391b4080c403100d8403820005014a595030010412707105240c070003080152041a000b0b100c940d0b10401c85000165034503900c241256a081c2450140310702000c04090090103420004100407000203015400c00160403510b100b585c50400020b20815034400c20140d500c5940d2000603ca0381c1c04101c0014554011302072203901941c8600c0202c0c807a480c035008504003120580d10f6801050f1244184002407141c600e0100160185100424101c0c0004200943d80e125400c0040d004d659203c2c80301184203400c0d0414810608070b05040071a4107110f180003007143d031044500481070701a0000200701c641050041044000f040b625050441d10790080411011011480490740032150020800005070300380003400302980c00c80709098007401e41800c624 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 496793839 1250 496792589 496792603
    0x80a060602032a0a06021801030e06062d03010c030f20030123090411120c09041118010e06040f020708031302240307090503010c0e010305090c06031602 67
    0x815900140f1900a03181e032225428962110080030f144480d04030520702504000391150081e01c040c0c00001c2d82e8001c0f040c0e02410256001c401e0b607041102c10b0213120010785803e42a20a03130f41c0a250210300310300d50b29044403141c58081400d2414010042c00c0c0000034212b03120000500003094981c0d802c690504d0761485950049800c01d103450b01185081404a810341c07205000722403001c14245080000c000e1410a0f0501e03020018080c201c0318102810301c64040d580c410980c81c410500020346810f10940410b40a03064000640320072a5a11b490341c07203c1040140c0701d0621b8100c001c1000c0250441d01040b0507500815600c036521280d81081418002a291683c00e1181c03001d004000c87c0d03000070b40003403c036a40000803543d50b0325800000c0c4000b60101d4030024001c5142c030124402d0000004064004500407501912003501050b911000d0601ba5402c50300b0102c045100e0800760b180b03e50098106551200b88001500c030301c01100c0d40051503a80041d102c204101202d8a01409a03940400084e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 496795089 1250 496793839 496793849
    0x3180a140f1f02070303080903120403080c090301151401140f0702060909151002030c1203090712080d1d0d030c05040906060903051509061f03061103090105070806030a020603090c060703080a06 85
    0x9e14038203a03124017036400503100a40010b080004480000340c00c41005c2003540c91440e4000c0003885a22041401000d0b00d030110b0240c012140c88240c600c000c40d6004030101d40d030300c202c0c83c000941005d070451035940b00c40c2c00c03c1c40c0980e00003804025210260741e400c0d04582c0300740e00d0000705903807104009042c004012154400705003958010000c0c85020240090b21200d200c010010441d034a540e10107506080550a520140c00d5051200b1440100100c0760050141000c0c03100c020052003000c0410340340c0501d41e41844c8400350300040210f82940348250050145e000280c2405840c00b0f644107058011140c00e41c1c4420001001d2441c00e104204062010303e010344004008100176050603169180c90307a0006e4086801c1c413014044409500301182c0d10040115040081002204803100b260907481e4412039110109501e007000084c1d0203070040501c6409104042c0007040c5007009503003800b01503800507100401511880c2c1c03c00b02c150b40c1d100000c280280c407e0783c0300303078203800c0c0007403145e003510360310381003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 496796339 1250 496795089 496795093
    0x10f0509030c1506150a0530010603150806010602010905010506040b090c0a0306150924021002090a0f151b03050a0f050d06030503180a140f1f020703030809 69
    0x400c401180001420789070080401031000f5440c2c44440010b00640980c80c0903803228134010409403400c94104d406440502e200c100b040000001d200d15400340159441051011210914010f1004901c00c0e8030011988410252105010380c440696501e0800c01340c0c42280180c0d101e041d05002c00c882030188a170040d034151024041441080d00203000c0c0701c0000d000d002900e6010459144a0307100e60410002441d110410002e0b241a68030700900c11003e034040c42400050a2408031440070b4203900c10707400c1510315800703000c2d03051071003104002a50080d0041507000f00c6040001c211840d05030000030003400a041180b40b001c500c00e00c00380082410107030812a01c2116408100840c0d0440100c034003958092402019821031003105403414000e1400c05485689030420120030004004010164502101e29400d0042c2d001000c0019064607030098130003e82c581491116903060420540c40c0118004289101d01c905041c47ca040c5102881200700040e8408003080084c0341e00058082e8203c1e0000e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 496797589 1250 496796339 496796347
    0xa0515130e24151906180806090c0609041103130b1807090203070306120b040212030c07151713020405130807030c060b03070902190203031b0d060e0108010f050903 72
    0x2101e2041e0400500f00400301000d00140300030759440d1204003150310b064103400d940d150345400c00181050702c070403100d1080d41c0000b040880e0f01a000544c5c06e01c10101c11004107400c154003014018a41c02c076800c8650819121205c203c10010801c0140d44a00d4102c0302c0024581c4403400c04000c00d02c00030f090001d5a42c0603003002803581801240450696070b12107c0540d40c5e840b4000e04400818090307122180d003012a141083c1080265169280514000c0701c0800165040241043e1a84101d8150032015440010100050800705640040f041072504240e40c2140c100110712240900444181c81c002c149081d40d4000c524052140039040300200e280084403400c036645880b0b0034480c2280150900008a050108001054100c2c000c0c1c03002c05025194402d0355042c1c1c240103508040c12001c40d2940d54012420304a200200303481c814010316040c0300c0040e9920f84801c0c01680301c140001240f80c0caa08011810742502200329008183c1d4800016204001c0002241242c002900d0085a900100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 496798839 1250 496797589 496797643
    0x4060215060f030d0309240c02120a0905222d05010e04020609131803080619290f040905060f01090b0d1803080601080702070501080a0515130e 63
    0x41e40481c0c0c64250800040900c06c070700340001c00c6042c1c8064000101040c110000240749590004a04070307005800b2205d01c2629100380100c1b038007070011039500040aa81e400c03c150719015042012800c200c00d40d40744080c0720940c80c0400c0e100d00c0b0819290b02e06070108001c15050441c0102c00300c1c2c146140041155506120310a0201c140240c800781c4501c801041d8046160313100c920806600700c10240c20041c5081940102d12143c03d03182c010360110340d441000030351a0a24a100780c84400a208000240034102040030340d11304150f40601d031110001e2013240311110000401400c030008802c01c1c45890b1498640c8100c1a0b4800604184c0280000c0707003410f4680c2d81084051042d40d00c040d00c46911040d4a0300000700600c102d24034040343e01c1c021b42540702410380204590b4018030003aa5104d1b101d540351201641c0d117a130584120380c0020901c000081c00114198401904050910400d41503000100e0000710100c85001001240c299903c15600281d20108850103049000d1a00c00f0340225841c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 496800089 1250 496798839 496798843
    0x210c0906050f0f1812061005031612030c0b090307061a0d060c05070213020417030309030313030c0f030305090706210b28030203060c0702030a030c0503090604060215060f03 76
    0x1003042030850102d460013041444035000c56100d82e001c1c00410385d00c5031081c440c503512002a01e00d2009034031194000706850070042002c1a4421903900c08080b82480d04910160f450007580c42601040442c031070f844000b800c0c12030f0450044004d40003c5484809500b00041118210741d8003c041c102342e0b41c0c2c80c4441d520341c2c00c007000000341c01000004001c1000c00d01504d951081c030000940c00b10030842d100500402c140d02400550b041c6071030b44100c0382d00d11400030303580344429038a0280300ea00c02d00008403019186481052841c1c801e1611000c40c000c81d60380c0c6c0000d02260201180801e4842d0708010030040108040402800c0d10f181c441c14445100c070501411103094011241740700e880c0c10131003c8548541240960b8414244204048070000c640c01e2000301140703000403071081c000d803004245130300007460999000c03d40040107400e40150300c3d503080d0744910840404031500e000506c01c5a20599501d406003005103036540103800d4240100d0149211a107005150758032451940a06010a07100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 496801339 1250 496800089 496800097
    0x319090b060f010306080706030e010606090303120b030c090406020c2a12010b2112030124110d0201020403020307050603091e0708011118011716210c0906050f 70
    0x59940903100d20b1054012800740405400060a511840200042d842e23032603800801d1010600c0020000070380c41340012241010603110240002d5426840b2000252241d0f200f0b11200350010210340a13501148041148443c0c12581650060b0f0b000c10030b080640401d000c042c1d19080d00319904001d000107004da0600746165104c1d118003503d001180d814120109600241041c00300a141c00c1c403900c552901c4484035500880c01035014003540007840c5030304d0b2201d015207042c2c41034100c02c0c0d5180f618099080d0a01a11034403180300300007010440c4490020306102d010b06a05a581c00580e03a0380c25401810300c0c6c103000b9400b032070140c00100200007022130f0114000144948048941842d09075000d5150b180a04903040901c95501e080d0042003621080c40040c010040c0344144401003458402c015940f050b4450f00041e80c040480700080c515003032944400109a1303040c2400c00100f4031103201407070040c1c552560000010780d640441000ba64100c24a0401000342c0d01d81249050b185064564180c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 496802589 1250 496801339 496801351
    0x60102070b0702040f0e0f12030105010206060d02041b0504091a09060d05071802040f080118020603070203220e0f0408070323071505010803040e061009120303020319090b 75
    0x72010490340110754842e000a9941e5020440c203104114009206031b40b107034031100202c1124440e00340d05100b500c0b1140182ca040b500143c0240803581c4d6200180000c030800300001705c2e8019900e02d005088000c001c04522079a04903903031b40c0e54039181804040c00417078021a6607000b0300a04500b6004840e5a414081a4800801d480c51140100c41c0d103441c0d4070b4140e0581041460702518820104045616800352040396a00310607106460b030b403019413070f08a6041c214615110350042d101da50150401c0c070011900201c0c5441268503086800c00c02c00980b4000814440421414140c100038020040700040d410421000c2001e01c14100765643e0021071150038401018844084a0111400040c405401803000340c145d0181d95a910707403528030b1090200054810100f0714000000c03444800000564041d5080c59001d8202e54880f081049101d003000741c0050200065001e01007162031210b074400b15014440d0f1000740c0c507414500c081c00b098408440ba4030001700c0c82c201780d241c0407541040025070005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 496803839 1250 496802589 496802609
    0x1f030b1b0c06010905060a06140307030911060a0903060b010201051012020d06020705060402030f1603110f03010204080f061f06050a030e070609060801231504030b010905180606010207 81
    0x20388822140c9089000d5142008442d000e1140000345542098020b248a8034007150f10521003615400c0136165500f603007010400c038000070b0000520050181d0b1160524138050206640e86600081c005800c59011051560005044900810420486000d0b000004038240001d002501d000e50711341e5018100c078807860400700350003c03c017015900d80800516403a60003020541d615030150621950741c0b601130354124004d124080000d05a0301011807058a1400b12500d51484181765844542d000282c61419036070200c2201001100c6580034401803008040c04400b600310010491007450400c40e00522128890561401c405031007400c1c80b05030300a80307420b4104192501c0000400300c0c0101103180c9189002e200d02c9074003250641e00032248504583c02c55407440d1850307880704803241304803884d070490701d80100c408081d1002e20302d0300146041002034245522130071715640b9281e240b1800c40a0748002343c0e00c3d69400500402c09000e545c2d07420410703204002001e00b41800790000b56501403510409583d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 496805089 1250 496803839 496803871
    0xb060a050d0609020706023c090a0510030e0709020703120203040f060f06081011120417041e06030e0a06051306020408010605010f180e0709080d02061f030b 69
    0x1200d90b0300000c00b916a0003011911400940362540007544070020f04c08421302400c0402d4840c1204103e441c0d43d044044401e802403180d05291110a0b400040ca03080d402546803802041c0c50300c0d504030428510703010356004181000c0d074001c0c01c0d00b02002d58002040e900d0040208201294018401ca0140c0c5608400141d0303d58071400d00c9141820700c040010031090038112100300e030031201d40181050340d01e0841681e0030142001010411207104c80c1c0c2c100341070001440030305644007491441e1544280200440d20b2003003501040c150140c2d104d40c0204004040894003e810b25074034000c0f180c007038441030604003c01c42c402540b00ea55080d00c110014811500d81000030110f4050051100b90540d0004007907403525100c80c042c9000e084e1901501d80043c0c501840e46205500c1190000100d5501204502c8401e0401c5107404031007500404410074425000e800141c1c8450401c08000e00c181240d001c1e28550a007542c06118070301e1011a154000c9144107000d0001c10032003d54980c000e40c4e85035400c0c3c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 496806339 1250 496805089 496805107
    0x305011a0f03190510060f090f0e0a0b0d050f120412060c02030d11030406050609060603071b0804030f03080c190e031903080403141819050a1502100b060a05 69
    0x540c0c0d000c20340f00c00c0b950a18017480b800040d00250034090703030310350745490400f001200f06c12100c440e02446480c1c031a582000080041c40c032120b4449410203908040880c500100d031011468010501c003040f0303925406418a03207808003050100c040d00711a0041424030b03292811070b1200040000075400342003036503190608070007180200304691440b144440e0a000b110b541452030030103504111400e80380d1710308000000c0c0d040e2418020041c400c0030010452800c40e1941c4d0001c4030107204416828501044d48a4004041072650003d03000071440b624034105000c4071890010701010340906942980fa409000d007000d00303501c0c2100d9a01c024002d1904901c0d10f01034134006440c10355008603940740b4204e80c000c24401d044e403006403244070341d0190712010661109402010b0f190700c143c0300c801c2004e400c90a2002c0d00c629056004807904440d580d0039001998480d00002d5000d89607038085101c503044007149880107501408940c00005180d0410080b035020540428194401d1101001c10802d000900d010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 496807589 1250 496806339 496806361
    0xc110c011409120a0b1006030f0603120f02120f09101103091c02090f0718050108010332011b05031b03040302030d0509010209120102130315060b070b06010305011a0f03 74
    0x280f13550f00044141e1040c02c01500000c554282c07401402d0009082661900c5200341c0c07801100110f030b41c007500500742c0d08000842101c11480d40b40348513003140a8140c010428030f41c6040604100a040080380ea5200c10b0321040003440c805050030b01060290404c41c190510030080203031030a4600990380c0034450285128400400010200000e40c0071708050140040c54800720145842201d0580b41c0c81c1c26602c482c281f12820880a2191b180010400b40040c40025580a0040c90061a8510012008841c44120b00413400c945d00c00054980d0749409080c1802034007006901212041e042c880d1450500350240412800e100c1090844e0600000210303040510070422039409000c1140c040181c3d051422195010354840d00300c1a1140c69402520716036208103208580d82c0c180150950440280b40d940c2d60760b504904074210711000e65560b032000a203015504000c00c05188145002c0c91a80303403481c005000c848040e040b09442c0e82400c42c043c5890400003007101c4445005001d8161a60340703840e0882c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 496808839 1250 496807589 496807603
    0x2090f0606210601080903040b040303050d02270307050406080c0d081312150c1d0105090d150e03070b040803040501150605030a0f15090209060d0c110c01140912 71
    0x600580b0203019a550a0000c452000d0041c203091740d031074503252101b864441d500e004601400d1341d031450411003007001030700a10081c8510000c1050141c01d0101c4610141910541c071296070b400c8440b81c600f010158941400140058002110308000c5103080403281c65540d0360006d01203010707002c805000d00511040c501901d850000e818041643c2a40301d02c410740c424250031034110b0320000f04074111280e08840c4c1c001c0c0d40c08111583c1e10b21a08541d208600c17030745912004e050302d05121003040410f01a4507941c1c4880b4600f030069007041c211114504003d002c86903c0b500098198100b8025200083d642d00d0000340c01c241c21400303294603911903040c440d004140003200b04118006450000449940260156104440c40c103010050010340e026544252a9503181c21561700c01c400b0360902c14009254040e0a00c0100a040641811006d2180310115100c0515a00115036641e0724005030000400c8550640d803020301e495425801c9441440c011801055149032003032080000c0480c420000700690 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 496810089 1250 496808839 496808857
    0x211c0902040230070c02010c030305100803030106030b0f030a050a0b0712051006080612060622050a0506030715050906030604020c0a081b0105010f03020d0c0801050a062102090f0606 80
    0x901000c003010f0030030507404040075503102681400041c280c070b405541c0e14a0060340684071aa11150a560100c0c0241030042c051008841e4010700819030351001c01c080c5001e001107480020701b29200104100c0100030100c8100c0c4a80d0103c81a20f00084d00414604c0e982d07030303124502901c2c0c0d40b18102e055427000600d030540b00c0d109107051f04110034048030742507201c11640141c03219025919101c041c451180120304a0613002e600290120f82d5500304403c00c80c00301c41841c030707a071845d550130701941c8010345400f5224107a4081d140c0d024000c0c0340c641840720f81d005041524464021100703070340024046000c2e41c4425032040c0c0c0040005682d6032129012580740031400c00a541c440c80d1503190110300c50300f007050f940712029159003440281c0c00052249505961502408403420b6156500700302e1541c2070b2030402c40348030b000c000c1c000800040900030300d8000c0c08014004030f011030500c0c10b204150b2a403c00f1220303c0e40401c204504c0540c0342c100810380c00c0903028040500c80c0d5600404581c030341c8260001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 496811339 1250 496810089 496810117
    0x30b07091a07110951010806060304030e010f0c02120a170c060103020d020301150f08010f14161b030c0203060a020405101209080705211c09020402 65
    0x2102160001100146007861060852141c001841414800140f1003200c4220f03050780c1c5c0b4151000c0225841c2070596241074404034450b40c410701460514a11900b400f20601c1c11424040c0d600d10961b003100242e0351000b01a035580d8110310f826200180701411116560f41031082e80000d4003d040c1c8180d12525406802030240c00000741000400ca03a114241142a500c00804203079000501d444d1004840c811400200102070300d074250340070048407159070142280c0c11342d681d00241c0b01081c0b0062800c03009010603058580314500e041455400d40700b03a41e4080300f80e640380161099814501d1901c5642103180c0700c1d5040c0142c010a60b040d0381c4442c03550704240004000006110405611084590029109500f0384007240c40c0c00c0404801c0e4021805425409080740c880b2041d05440b07101454200310f9495000b04944501c2c0d204c920591341302c5102907480750058201903010381c581c5103c000c14162800f8244d1716000d607541c410403184030714840003005941c42d41c0580d000c0d59110780540d0380100c00450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 496812589 1250 496811339 496811369
    0x8040b1003120e210a03030b0d060e0304080f0309100e03010e01050108010603020f090721110a05030f0f0408040605220906060206010e010e1302131407090b03010f030b0709 76
    0x3034101d00701c3c80101d0344203c41d041606484924108907600c4d41d100d02c3e070000c160300d80700f650b0240d0240410801480c1c10014600454021400307034020720160000c80307030241d5502d5050040301d600b001c1c0946042e210580c810008005140c403003807903440d0601568a40b88441040c2600000d01405105104581c0b640c200300000c14089011350210042f60310842d68098030031001030601950400854502e0003081c140080080c1c012411a861080003d80d82e80002d01030501d0042da8825410036140180041d20202c04c0010280345d13a80e00c1e58005007804801c205070329007a5602c656a204602801040000c00701d10070f240311844441d1506200851300e0b1500c803850301c502032100100720904c1941d00612421000281041401c141181601c16030485d01d02c05a840300c0a459802c50308160803a007000c690900902c007804144207250392000005240003d5062240000b400d058a582000d4405c1384100010009001c0d8036803480300312540680c400b000760761103143c2680c4500213540809169503c1030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 496813839 1250 496812589 496812623
    0x3010317160c1e1d0109020307020f060907030c050607150209011214040b0106080c09041109090a1508070501170a0b031002030106030f0606051e09040908030603150708040b1003 78
    0x10440b43c001101e000380140c0c10942d01d00780780640141c0721101e0141d1502c0e01d0014030441c0c0301030b002194041c601d80101e901c04888442c040303282c03400403588003c00ba0001a03040c002c1204442e41d010040101b00c603210304021580c1c03543d001909c0900140e60365a40e001500007200c0c1d000c2c1c000d04800401c200d20410040038203181221000008507012203201056000124a80340640d006600485c10141664281044981400300400e1050a4140801020701804241755128100c0314810383c030080e0003065500d9007030961080018680c0148020fa08018418081668800c0da04000c0c040010f14080d059268040c0180003000c03501c5005805029407250070000c2d80d070070780041d41290b01540c1c0820800d8000714130a411110706004000c0010410404540b6403100711401800c406014540c851501c500c060001e001c031091545c0403100c410021003005078514003488000e541c050110840017142c0307040c0c8070090248000a1004240900903004201c002d04e2860440d03019542c8001001024103001e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 496815089 1250 496813839 496813859
    0x408100c080405060c370e010203190311090901060c150b011e020106051c021512010b0703020f0d0503010819030915050c0a0c06120203010317160c 65
    0x18112046080e0800664484451254510500c280c2e00700d000342c441501c40240c018207680c4138110703c000c610740e01184442e111000a0341405442000c1040c860b5a40003110041c00b06003030700d20100c0c1075410078005102c0303515154000c0c1d4801c0d0018580010300c40c41d43d90800c00c503401100009908541c403c0d002290154028000e5540700c0d00460080c1400c6074686000c0096924a4250500080c000880841d021f85844800000c19030240000f0801c15202c40c04204001d4203801025200c1000c2c41c0300d002981407007111903307500700c040c02161503e800d45c2c2b9a1300d11142c040c89542500200001d0050a06200b0f02ca0540d40d08509020f403003400c05003000082c0103030828059030125000301101c014910140c18904120305605882c0d420741031b441e050030b00540415041e40481406070400c070381c521a480522070700d608588030340c04000d400c60520000906414620b4040d401c075610400040c0041480094a21204218444910b03030350203107001503100c47c0000040040091041c1c070000b10320410a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 496816339 1250 496815089 496815103
    0x1e0a150b07081b070312030b01111506040e070e1b0f030403030b121b060c0f060a05010303090608070203070204050a11130312051303110604080a060e1b010e1e060408 73
    0x503c000110b0314501d2040c485840d02004c2c40010b10014101000c6a4520701a4100b182c40702c0d41414940c200c140440070440c140590300500300e01003a0034804100d500d02c0c085c841c1841d960310340f07402003906a0410380004842c01000d4180f0100c2c068454481042048a89c00c6a265008800b4290b449051915010300600b0a41c41e03102d2046155519140d90007000007481484008a208c1803502181c1680a116680c2d11070600c400c0c1c98000d2051030520b002e801c0010900443d2088000104d07503256040003004a241703508110100044081404043e9600000780c402103501214000f4494440001040080c01c4040f460000c8201c0031400396250f03e0b103080464112402894441401ca24088085500388203001d55180c40c000050b009001040980c3c1e12048401d05c060072030380c40d00b51100051440e14101d988202c84494a98480c40c175450307030a0041d03004800a94190200d955100000a06201003040e0410b02030031441045103040d1f070b0401209070714000042d0102d5030742c580f150f15940c1c0b1100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 496817589 1250 496816339 496816357
    0xf16120212100b03120c0303060f040b0409080c010e010b0108010303050a200f06090d1d13110301030c050a03080f09010228020405150a030308040f080406171e0a150b0708 75
    0x605248200d17140340388000c44480d40c0c0b01d5400b0f1855541c0c0c0d1001c10101c168884191600942d55884010140d00e41e03200c5c0a50060182c046c00b9299807041078047e09590105c0c4881d227582c5d0500b9810782c540d03600270984034103407903240c100f043d04c82d5000d820854004212600d1041c41d900d5449000b809100003085c200d540818602c25541140c2c0d440091560740c00328042c51170000b801d81903810301480086081c1440b01540140000c402e081e0003c100300680e00071201742c0c0d0b51110000700401c00c009190308070a00401094810007011072540d1506056401280c1e00030103030040000d64105960302c00d0000d046610342e284202c3c03c01c4051111034282c0200d0f0344000324052486d1401082c5440704586220b030348600014054200349081d50741c129002d81c0c010340100d9002a000040c0c00005500c0c2c030150021340b880796605400144020284203141601816200c40d01191035003c80c080d0528031460b40e0300800200011444203d080c5421109040d0347d8032034018100041a01010000450010b050130070b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 496818839 1250 496817589 496817593
    0x60a1d10050a18060806060702030106030510020903070906050312070f0f290108072d080a020a090507082712040f15120b04020d05180f16120212100b03 67
    0x1a01005000b40c3d80410b07402004c0105d440c1130005505071600c000207144c078a1029001190550b40c030f45d2106c0c6072881c007401020750507802286119480c1070400c1a513008261002c1c00784152450400032a845046000d8100078009001804105210040742604400d070743c0724010207000040c505100103820400c00300300c02548242201d04103004030450701d00341a9070001016058040c41c10000003a8402c00740864040d0745422084c803c19038850442c0d00c401420480c000d840e412920f4410407440090980240014926040034400210b134082416030b8803c102d20720015183c40d803d82103d04807113402c900d99116108120140208104c190b020b00708403602d0f110382c4640d245e01d51000d0040c8609100e800300000305041c3e107141ea2655550015034180e00c0103040185400030045840003918001c56001104040d000041c04280300c080020005000705100074101100c5090040d69003040d4610489081c00c01d0820300d107040d942c6400c0780340c00324024002140c1c01e00d002100e1440c058074618180900c28 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 496820089 1250 496818839 496818857
    0x141506040b01050921030a050c0d05040311040c020c03120405091008100f0603060c020319090b0405010e030319180801050408040b132102040f020405060a1d10050a 72
    0x3400c1501a01c80e211030161500340c10008560700307000350381c21902c1d014128402803912049141c0001d1005011003242a40d550b55030380c0890205516165000d40c001c41001340420040003c11405888201e00a03021100840c2c0c188124000703d180c45c094456440e4940103071400c0440311440c2c0c9004000b181c000360741031281075951100c40d988800ca244220b02064101c145c001c81c4ca03d0007540040e00ca0401004002080c030784946a410481303840014500c0541d00c00039240241e000e1811800580d02000d00c1e080c407403141403400710749183c0074510030380c0d051080102c081c1d18035660030700903034202c000140180100d08600c08001850b1032003e140000007161411004114000306009683c03240d900310f542e40c3e00d420b01e0305004201660005240941e11101c1c1c00001c50100364030001d070514038111f000110807060380c500420048520720101814490b104100400c8a038541e00181c94a071b1485003451b00131088c4044000d03041d03215581a455201c4460903103154120781100c041c040c2d480590391a8221 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 496821339 1250 496820089 496820101
    0x12050126120a1211070b043e03070e09030417010e15041a0a0b010207120c12020604080106030305030103030e010c020d0809130501260307030c020d08071415 69
    0x1980c07907440000e000c51404202892289024002c000540001c1d41c400060740303140d40c02c113100e55401118049800300c4000c0180702c1841084003240d5a00c800075000c040d00510315840c500041d8140341d40c1c4600c0081c0100454071030340d4050210500425031300103268a0361400c1c11015849500500403903c0c203041140c100403040405110304024001c0e02e034000c00442c0c0001040c0c1500b030704010300480303180303410703035408415902c44081c0396010740d6482e1004603036862031000280c20255130390005e180c02070007000407202052048045030101c400d503200c0341344000114000f15000340708075000080b0560a10500108242d484001181280d00030340e45d4001c01501100110b400554180c4c000e90f01802080d11200402c00600042814035001490030206044414104050345d100340e0104442c1000c88030050001c034201c8004200409850020310301d03024030341d80c003d0044804c44802a000302070042d0007404010041d022607482a400441141102010b100d455569048072619144150032000100c0e003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 496822589 1250 496821339 496821343
    0x140315030d090b0306060d0902030a050601060207060c0803041e0c0305030a03050a23061f030b0a050315070507080f1602041d1002030c070f15060803030c0304060c12050126 76
    0x340d403414020f00f4a107458000401c040c0c0e4006222500c41c0c141da5101ca8001a40c00304400500180324070003400c01c9601d401c401070f0501e20240d00240c00e00455105407800604a681100e6001e640152030300707000048007412003d128007082005020000302c0601105001001000c0c00586221345d9050220340d035165540803d44481c1e100c60b81d1200c0c49807484401c0801d0340034003260700c510090810314060700c0c80865801c43c504800c0000d40401e59480004029040035180c00c005005c0175001005690052440d450003c4001001d9404011000c1150400c00054004070340d01d142c40c15203a10b494003804d45079071111000c4208124030403840c08002191400399100c594440d80e102c0c1000d08a103120000c520780103903100420f07810684208100700400200f02900702c09032a8000d14400341c0801840c51000100c0c1d5913900440780f00e034814010420720351441d4040382c3e0b001e42d00c403c01041141ca401e505803004200144012511403c0c0b900105d44085032160030078021001c40d051200010040883c19 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 496823839 1250 496822589 496822607
    0x10b0105090a05130f1b08130803040b04030504180605010e0406081c09090507021c0305060a03030516230c010c02060d0e190506070e0907020d0807140315030d 70
    0x3582010041030100700f0351502c901114551403289401140500050341103000721070f00da450400001110301005890241d01102403544041c1d801d9074403c52010540f0791030034501004100400352901200003600f01442403040d1401028080c28076a0b20030a01e15941015126038003407140056142c0c4c03101001403806004000c210740b0b1030030241c0202099040312000c0300c10300090800a10107402e8000943e500d19104141c4102d0345503020b010a018491a401040d2401c0b100c050101030414050004541d11071000504803a07046c02c003503680b43d800103071a408003140082c0141060b208001c4140800720004504261050000196441c5003588001035909400c2004040d412440c18081e43c40743c80030380ea1064811582030000c50396540900015445601c07050582207406400c0782042c405802c0d00888003805820044401401c149000c5500940d1040d40100200400c0007010204034181d0040d10404002240129841c1d80c80c504400415800351030408103c1c00317482001c0c018030019201d55a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 496825089 1250 496823839 496823857
    0xa0507080d051803120403050a0e060d2f0a0806041d0d081b0315030f0307060603021503070512060406170a0203060106020d02300d05040209160c140c090106050c010b0105 75
    0x1e04058841d074504441d80e4105c107920a00b40441088280705a5030385001418000311002d4011403200420b04c0305001c40c01d800c00381c11101c0c2101c2868070301c4c13603705541500c000504616200d501d5682d490002006414101c80a13109040441000180381d4004144800316520580344c150050b00d509503c08281c0150484d00d04401d002031020a903030b400d84088881e580280101220784100b0304903412811503014450403a00d0b15580d410402c21401d151a40843d03c060402503282985420280035090784124103c11070a08440030011300240d1b200d40c400000b034000f80101c440c111400c03c0510f42d480c0d6074004164440d2285500004406200040c0d100c0c172110742c0c1c0c1c040d1000e541c04220610700560300240b02c90580c1d0a40d032000124034501c034040c3c1410b01d0b4500c0080740508042c01070009010000e042c0d111181000401602e0041d0031200c08852a60310091004850302d60800103030134a030040d002d00e91300c410034400003e0483d60050143c003800001c5002000b550148a005480c40d105071040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 496826339 1250 496825089 496825117
    0x90711100b060d060f0e01060e0109090915150603050f04021503130b07080a0b010905092a030f09070e090d1d0406320f060a0507080d051803 62
    0x10000c80d400d9002a005007402402d40b60030310003403401e03100603692603420074014100040402c10034041a907030801d005040d1414143c142d5956000000c1420090340a5048800d031602c43e07001c100300d01ea000c1980841c1c0741031010002e0b200c1e410105401840c46203c1c44000030f0400002c643e041c00e83c4a441401075600600c92001c04061407004840c0350801044c2e10b0303020b0a0500c0150108040c5003072244910741981d1564034520f0400056000c4846205003181041020401809141c55142d02c15410403c11000c0a40b44030121301400204030090310b6001c041c83d004400d00c074034800c045600034000c00c2e0860580388079540fa4625103aa010007200c03520155030024851b1210f041c0140b100c9048106c1038224002c0c3c41c14040080340903078405a2007800091003280320310b425150300085c00001d1041c2d54041d0f1000c1200c1000040d54041d80301511480303001c00144603040d040c09902180d00c0d4542c0201c017030762560340c0c4403405002008201d4107071441d640c0c2c81096982070200842207a0940b07442c510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 496827589 1250 496826339 496826353
    0x7020c0406050d02091f060306061b030212030c070215120603120a08101707150207080a02060f07020306010329010b0d1517010207060606050a092702030c0702090711 73
    0x20400c28140140052040c02ca0006c106510030701c02000b61406484c183d1400f09500c0d203400c0e40180303500800741c3c42c8910050044152000694040f81d444041c01c40c10700515100c1d150302e940d0701164852031100a512400409000c5080d585880c003803d02200d1000301d030010381d52488181074442c030417100c004071207500030001c00a001e030160440e0368200504441c4000e4103920b40d404c801400791503090300500b44c0c0c4021810043d1541e0b202441000582074800344c02c0342d0749083c05950356020b2221000784225400311764190402180000d440e8010f4004044400d00d51b52030420051444081e1108030b41035913203034036032506040c0d00035105040700c0d8200302d8145454000030020000b07000c140d502002d00030040d4000034020300c0030350381100305121a000041ea22030481c54040e003122003030b6001c01c05003d03050024240158100d004501104c0c08000019502d030b0983d40b503032821003e41600100100d10100c28008031b60f078018091304809100380c4412a660300d0b19a8280c0d0303210304003405034400d584040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 496828839 1250 496827589 496827593
    0xf17010b031903030605040603080304063e0f0301060c1415070309060f0c02030d0b030703050703030f020c040515090703050105062502090a0c081302090f0601230307020c0406050d 79
    0xd00b8210194000c3c5400501c0e2070700c0318001001e59a40c1d030710580e02800040140002e011080c13003030f01c044405182903a04041001c3c60b0101660541d00c022802c00413036005600c60f110305010460341d002d400206810750309d40e10341c0c01c05010544441000c0d60b0036075000c0845d40d0000800201e809030001e90f49a85060b950b136052044001d8803411504540b0941c6910b140604619280905982c115a036005191101303110a400c00444d5607490141d8440e510118040002c9800495043c0070340b601864003000605d103803d070a070320f0031000c0f150081d007203858070381004181c0c4030480d514412100104c0e0b000c0429102d2000440a544007070042c40c0e445441007180e05000c8401d1480e2440300994501000601020341d00005c01840302244d0b070800b60b51310360a80c070031056440445d5582c010075018810300101016004105141d1004110301d902442031008290907078000c241c0000080c1d0b100f840000c0c001e401000d070100d01d800585d00b0b40c0143c0b0411030030802c10715060090400780c603030240c11054440c4c00f40d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 496830089 1250 496828839 496828873
    0x3b0601091509180c0807060e1806102705130c08070315050a0e090105180d1805060715110c0a0f1106030f1006030207020102030d0509160f17010b03 65
    0x21802ca480d07802c40e900f4400041114008070003e2014401030041d4070301c5c003240500398a518061051082c04d650a08160410743c40c441160040c20070348000c04000441d000694078400e490081b4801e011080303100d03994084c2034040b03400507910140c44c64908003401c1900d80003038410860015001c40c00c8a000220b1642c4254030052080c01c0c1217103403415590f9500f001c1011060389410005901841108120740d0b0002405195040001c4000107501250a54400c42d00c5034003403100c0d001040340f951401f841c058140ba1004c40a000014400c1d9074401e520b01e44001c949980f100303c00300d840d00701040d0031603c00b8803600b03884d60070042c203011f054003d09542d00c0500e002c42c0c502046a045000b4403030b000c000e440c2c040140d807091840d04410240c0d4108000c0a0b11894015408801018010802900142d90101c2580c481d00204036022502c1c1d114801c0190411044c18501185000600380020b4a41070b40140c0c00d04030b4180003800d1141031001c0e503207030307080c0c0d02c04240320b581560041c90801400b28407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 496831339 1250 496830089 496830101
    0x220f0f02032109030f0a0807260d05090d0e030712140304031401141b0714010f062607170f010c090503010b0406030c093b0601091509 59
    0x300800307030b8401c0302601849401c40c03107001c10700c120000d0300400c0744201801c040101e0307420046900020848a119961000d05610a0b00300050421146058401c5000750500e26070304c400844a2810f42c488020555801c0204070803120703190141310701c0b11754110f050b00406008822000240140615504001000400c00e0040c0c070111041c24040d041a021040c0500150002d18414840120f41c00003a003411400d440c1001d110311100a0582d051000d400d080c0042968101c59002c0320a071a4850360922800843c2c003451000259400e240b605202001c20fa413041090744d00e040d841c045030029a03100c0381c50700c12240c1180e2400f581310a1041c44445220300074141d0411840086440032184114202e080d00c00700e00c1d0300e0011803001d200500252800303000b42e440080c01654100442c51071601c80c00e513030072a544500c0d03114560b20b8030150454151104903c110742c0d03a0003480c1c608403507242d02d01c030b9890100a4030011540500400441c6280c2d6030f00850424009000c2c00000b0142024100001800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 496832589 1250 496831339 496831343
    0x3060f04111b031308060103120203160f080c070b0d060f1203030b0d12080411040912121404050a060b03060c070209070e030d0201060608060414041104060f0e220f0f 73
    0x1c4140400002c0c1c4984220740c00182c20014040d01b031651440c60101001c40300c0b01915801d43d0814041420780300307804041e4032105070708125508041019400c08000c144103008948006014404012a03800c0c12440100b0a4002203142000311540e00c4a0511512800e400707101c0c484814814080086486504228858040103008444550095803038602d00b110303400901300401c210000708010300510088542c0301c1c50040c0c50600815103159542c151500c01c01c101d03601408620100321002a44590041c1c440f80c810b401d0580300d9041c2402c00302e40d60440b0040440d03100b81420340650003070401243c410f01466031500d5590602803580e00b00681c040000b82842c040050004d150241c2c4d81d005c00c551200401c058000140c02420503a00420f64600117002074000c1d4103140c01e441c40000c0610700142d006401014034424841c00d06d0002d800b612003035220460a1013000f901284200c0c003161070303d01070904410740380995a440303001c4854000c00b0308400341010b034100b007000d03010540d2103201c060054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 496833839 1250 496832589 496832593
    0x7151a0f030c28180f0606120e070906060203180a03020604090c020102250c21170412150f140103111908011a031b0d03031b0503060f04111b 62
    0x107110400a0241106160300140d040d4000840c134030402900e9219880340701d00300040511000d820800080c00950805a804c11002d83e9818901c3c7c882005003e0341015114940051100a40e6288029502d40102c0c0118001ea20003820401c414601007090004980c0d01820503400c00d49461000c5e0010303d610314440b815075408202d031300c68500d040d014400c4d1010207143c00304501d00c020708181c011007001e80c210000003200100580075500f05d0420390f03914540d1004006841b080c50143c1d401960041e41d01000c4602443c1d104241000b000c0313460542900c0e29440c0411441202c0d008c24800c5d591031039080000286c0c1c540c01400454003e0000d940020800b40c0750b21031103204020305514130501032b481207006940d900c1111041c03100f00c1c441021109022401006909544000610911849500e4500c1a40c1c0d0708402c80416000f070f00b25500c25a99400078450483c511040508140d10494002d0700c00c0e61024845841da2401d481010301100196a900f82400711040c8520b805441c20060000c5038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 496835089 1250 496833839 496833889
    0x1b0e2e050a0512010e04140109110f01020106030c0b040e101d04110d05100c02030c15040f15140115090303050d02040b04080c040509030a1409010507151a0f030c 71
    0x1400b00f90b000900134200009030184504d414104441100050051076205905040403040440c0e2240c003110740341c0354105ca42080800078080141c0c01420385501c01020502892800200005c80f54050700440b0745500d030200160345d40c00340a440f10703035590045c04041103c40f102c0102c6910003403803181d4058404d4180504020002000541a140b403180c02c0b606175002013509000c00303800c3e000300803503000170340002c5041511188100d600c40c4030780140c101c0c44481036030000d818496956003803044140c02104600c580e03c40d181000700908181c1d65894650000080006200750308101000c001d02030b40d82e560030540d41555000c982942c418000150300c0d039000d00c00030078500b041000900013800500c00030000d44031140c0074441581d400900058140d0000c3c0007828419401002e8030030340e10706800c2e034207550344034030f42c010785081c02020009482d42e841c01902d2842d03101598015102c10340c0d40039001c0514481e100400004152442c85140c054201002035580750030912013401c85421001411502 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 496836339 1250 496835089 496835107
    0x30807061103090f011a090105040908090d08040f05090609071409120c040b040b0d120c06020a020d1701061709100203070203121b0405090a1b0e2e050a05 68
    0x21030b4009079440f01e4542c202900301d00100070300340f00d1400524904082407030346010f9000040c00c500b805109141c0110b03100c110000030020800c04441715500000c2000d0302280e000d04041166420a01451109421001010559262149509104900042001c482640c4103031044030070006007070410301c501d0070600910807150340310351112600c0700c001c5004142250001c01000150303082801d103680594030305100103403140c548505624056410010308a05010b070719808841504081001501951011485101c0c2e0b6a020806611003001945c07505800f003031007442e92601c06420b1051a000c00c0d1140800c4002c1078000c90421350001a0000b51170240039606d0524060b81e004484410050700001141010080c520604582002d500681012900c0e01821030300e44520490141c148500c3c0e0407170008814000c20380090740b160524a108050300a54030402902c00e851800016101d40c0c0030040f070074103400d403611520810b81c44c0c1b5412000300001041041c0c81992011514508110f0100040701c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 496837589 1250 496836339 496836371
    0xb010c050d0201090308060603101208130308120a0c0503151207080d0815030c06030c09040f0b040f0e060114030a050d0e0a0806040f03051303050703111f080103080706 74
    0x910381e490340c0010810302443d00e0f004000e510000c0045105417424004d10203060109a9181e09070745400300b445841601c503050100141c0031b20200a40780c810505400300c1000302c224040c1500c030801008a20f030f280c580e402083d0540e00c5201c02c4900181e000d000051480742c61162743c02c9010030203007030424107010f14606581481125045000713250300641c9000705c00e56002021a5101c0c04d000c15071400442c11000180d110b0b54404007003813080c01c0220101d4503505241045481008004004000814441c00400045d06c86031441500c100d213003c8d0441c071584045d00502101c200404090f1800fa030900c800c05880b100110803494052240041842c0000c40401c69080f019205444906012001c0c0c010040710031a10f420044080e040801800005020031700801c5225602d410000d40311441180340b42c101400c2039102604a100303040e00041800200202c003500c800382a120b44101c0301291a04111192031000510f0000c0c0c0c03900010800700d00d50001629405106100100b4070381030444c0110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 496838839 1250 496837589 496837603
    0x8030d2304111908122109030423060c0a2009161106040b04021f021504050118030518030c0108040b070203090406080f0f0105011809060b0d03091401080103080d0b010c05 75
    0x220060300061b100300194808484d540f01e01592070035200503450401c0c10540c403401280715103000d04407208003000181e0a0325805500d40b40014150a0b00d40f286004d030159140d183d0350041da26103c0d060518a02c000310b403244038044036000340827182d0940b59240620701d102a0102ca0030100108000c21180c2c05205121381801503005042c00e00032805d090041008120400e810502c0391410750801c1e0490396000308601c41c00c40400c207400c0c411640d035414000e0150906e111300c2e181c0001c80d2080e400805801002902c1d03041d140820300e02c2200c1800d01031503980c14030002e000f80400e50120018000840085000b98040258419030f0704000c84140460180c500c150020006070308102180d03540c5020400895407520808402407045501d4500401aa48104901c820342c185d01c43c02141c05001d02500a1900114080c188080d0040d45060040560499004a041017602d0f4116240e207503108840f414140d0340c2104510b0b2a08090303e030f00c5001000c0f0a6202410300420b60301d50710124000307010013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 496840089 1250 496838839 496838863
    0xd110a24050604020315100903050d050a090807050603010b0f04091e0b030a1101050d150e041208090706050c010b10051902161e08030d2304111908 65
    0xc261915084032180140c900080c5081d014030300c144204076082c2542d0740504200b04041c0d40e0311115418410003294249500d0b003000e0118420784110411040d8040000e110bc02280d40d1031412503522030b89606e4445c00148550359000304184014801c1100720307c021b00040341e86000403450590b450301034106450400d004981d00510012145036250158002e010030300d0021400f41064400943e502d10943e001001c081d81000004610f000c0c114580d039110440422031060000e511a54540e4940385440086400b280e034215185c0088001030700668810380260481e0005e03009290804070119990741081030383d05415900c503e800f105580710700c403110301203821300d41e00c40c0e41c0e0f041600b40c5682c02e008001c13000e504652111b11f001c440d00d01607000c60815035001085000d81c01840740c104036600b19440c0c004224500002642d82400740440d80881d180c15680148400107403100d0003038104041c070444028100035041c040c113000c245040c1030f0032805c89400c400410006c42e00c0c5e038400c40c40c0044001c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 496841339 1250 496840089 496840133
    0x1091119140c1203060f0613030809010e130617030703050313060f020304050d0e03030408100509010204030506071e080f07030f020c0102070317061002030a0806030a12030f05180d110a 81
    0x1e00c0918200950040d1b02204142d0301c5030300c0c0c84c0f0301048540288802e444003074540306011a69266aa1086a5480500400810840c0c0c050302c0200a48001d00e014445d6407410ba24030140641d1b0307820040151096541c068030b482c0d0075640c520039038190740d211f0184129115030303a401c0d0381151440140302450041c0c1c01040103010742e01071090042d00d05401103040700d10a51040c4803c20044000141c0000301c65086980072034a612103418076800382c025a0001880750081c5420001010f60201030210301d03035a40815032210032400076040d5200d0b042500c4140446859400203110ee6000c1d800104414080210040c94950030700000b03422a04400c004400081c0054801145056007201f07150300120111b854034a014542f2101030340c0c034465840c401c0207100c0c40c140041d207103980030710aa80c259508507081032081c4519610003030003010307008094000343e0f1801d13020800780c14203402125032007036201000f041a41c540c0ca005882c4000401184203042c4a40c42e401c01c00181c802d001d895001601601d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 496842589 1250 496841339 496841341
    0x30a0308070507171b03040807030312060b0307020f302101060c150506030c090a0209031b040f0b0a1206020d06141206040b010b070201020307050105040b01091119140c1203 76
    0x714000582d0a072001c803040c06e91061100340300c0e000c008549201185da1600b0283c4560864059080140900c2e91041c41000d40c007008008e51140c0129861030244e40c0f1000f542d15540700700e0211500703000441c040359009016800c400300c0c3c080011000f410304004c2c00601e04030b00e4854904c0d001312450243c01200016014030620400c1042c8040003246522001c01e041c0094500780c40032950721420140f00ca8402c420001c041800c40d5010340c121b603034a04015060f9890805d0300c0b8011140210324a007520302407413030000d48152040c498030039400001001001080c8013894552000317914601c5c0b440680d000350342082030f0705040b0000e22500005003c0b0005100c03180304000c0801c22200d07011a0044d580d038002c0000c000019102ca07401ca41524041c1c0003007030701c5040c1800101d141d40501a4010217642c6884140418004071180041c12038140170010f100c080710541445a4a005101c000880c2e243c07802201c443c49400780050651003043c1c200914200700060019903c0d01c80b001d0560703241118004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 496843839 1250 496842589 496842607
    0xf0615010906091518030c080c0a050405041a06011b1101030e03120105061b031b0d0e031002090102010b0a1d06010924020111040902030a0e0c030a030807050717 71
    0x6504a000b00030701d0811900c1103162680d080e1803030b03036801d010750700300480018145040c1000301c40580c00f858118819454060302d4914450b5980c04d03130b492807441100003480001d0b40b450030340181c610450b4482c1c1040c0d003a802413108680c2c0c0c01c1e400f8013168180084c42500074104100382078255066070143d074403402812250350024084401e19140840c07035030020800c841c0001d0046158030b04407070041c2c540c195588140721102500e0041c0c0712416290340030004a0645401d4180380c8000350f04401d0302513402c040060541036407034900c00b076002601078202d06183c403000b0203190701604c030440042c00045900c520f510000bc41002c510340050345070405015001c41000300c00036003681d1140007030a2082089007004920480f0302500c140c40c2820a01d0a030340321807084c0c400e40220708000641c1040d07a854645501000c000782d00200c17a50340c01285001156074002400040e103800240000d000b4011002c1b40b03440440307460000410502c240041041000e00103022901d58840c8600d035181c00d6a2250140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 496845089 1250 496843839 496843847
    0x90b123007081b1515041e1b030225020a05150d0b090105010c0204021c05070215060d0305030f0915040606082515030b0411120c040b0307030e0f061501 67
    0x803416000484d80712a6141c04244815801c0c1030304002e081200d081074100d1040024041c1c840d0b4042e1040220400c10095102000c582110010001c12a10528610314241c401c9040740141d8150b01629000c1c0780080350441011140740205900241c1640d80c1c0c070351680d01103114800d1804082490013400100340e50071801074421000310010880350800103514101c0000c20100301090040c2c404ea03800a00710700c08002000d0800050030080e0030034081482e10450107501c943c00c2c10010910100584009041840d041184030036032603150301d9403403c546401c01801c12001c0000d0411001f48035142d81600314041d0b405c1500d201d0340c400c41c00800c1060805a4446c105100c00d000b1102c030382100181406401d108401500603500e108814440c0485d40d40800c5000e8407481040c00d0b00203182a81e402501038006004088c007192044540646403100c010068251060380b00324480d100050002c1401c540c40780d041094219480b10444d07100b1818850304601f0210143d40c01e5141c0116210103452035600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 496846339 1250 496845089 496845127
    0x16260306040c2a1a0603030a03111204210801080303010306150b0711100302160303020d060506030f09060c0703090603020a1202030a0603140109020f10050f0c030301090b12300708 79
    0x1301c0c001c50350b94140600800da483c05202c4e010300a042d00c804104040040503025180407200304110042241440e0610120030300140400c000e0666195000490a40c0507040490403100444025807460f840c6d501d5000c02040c0c00010310340c4030111500c00040c0c00d07a1034800f40c0511030003400100c034030031203007020455030200321004081172500510424400030680d00103145515003500700503a0f54150700c229040104159004190300c00301c04800e1064001070035400900c20011902119020384803446011002d0040040c000c000540c1060203012240c801d80180110711440e040500c1020f0202c1030443c140d800882d00c9105980d900c40e401c00503c0801d510440358500c00c2002000003442071f40101d411428000b1100307000e02c04000c52602098411401c41c1d1840040c10100c9071907207000c050654907540700381b003802c003410306281803640c00e031030403a0110340440f04860080143c000c51401000000b40000b5660145907003268482d2021048000100001b502c5070204030307640c041654a140310700c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 496847589 1250 496846339 496846373
    0x80c03041703091009060e09100b0d05100f0b0301030f06140109200324210a03020d05040f26030f040801110c03120406090816260306040c2a 62
    0x1c42000070082c1a0704540d04000c807031002c1ea12823080f603903000b8070120b20700c00030741c400c03113188400065403038090101c1c2e80154043d1113503c01000708150f60303600d2201c20411a0050410b88503082004000141c000132140d1480c0d4402e07000841c41082c51040d51255810983c031900d440c0703484100300000c0e503aa00c4e0f28030402841c2c1842c1c06055082c808810041041a0f100741035428a9000403600d02e55200c80500e0600c1c00c0040503080e100007140700007034540303400300c1c0308601600c01c02019001060080090360140c5150001548040d0701d401034a6200038203d8098044138440c20a00d421070600a1000300010150003c1507582c81d072400b45190300f10340849075440341404051207050301d4840040200c81c81e030035003002c0c803215a0b1228103180d0014480c40b0390040000400049210020203501031030001e090003890030700b6044100c0c005115543d50b112400c442c0003402000080d285141551080c0c0783c0100c0c0d454030900d03100c4c082c2050030302c802c11004104001c11005414a0400204241188c1c0000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 496848839 1250 496847589 496847597
    0x180e1302010f2307031b0809090f150402030a090c0f0611030c0703060203091e1b04020307020c04051f03050c1002070f05090711100606200a080c030417030910 70
    0x100148a030f0052a40288400501c440310011300306060512a480400b9100c21940440d9584400c030b00d01842075038810344600d0b001c0c0107240002340b801054840890711844422415401d440050b6007000300a604c001e040310700d51680c2d0840b20010a03040303030313692002d40004141c03008600c0c28241c010748035181c0313410b120b0745030760082240e1810940302003004000c0303d40c0010b0141c1c50b0b44500034407a0800c2424400c0400c0301c070a108001038210380009506201068110034262410407010505c801d91200302c40050160b804034510503e40c1c1003130750240741e0120300034070b0302c0985100715001485003403184c0d40155115030103050110041e00e00008070441b0000d09000904142e07282061040c0b00f444144211446044550002071402d402020146603062403d000e60700001500000e410041c8064059000083e18100309075035100c0842c1d078003d10140b03603000284050a4140d46021540d480001c4402c0703640030038480000e4644c0c190078a50b440f00141409141c0717604426050000e08280c03207070514100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 496850089 1250 496848839 496848857
    0x30f09020303091005040b0a030c0905090105010c300e090f040b0a0b0607060204090c02071a16050f06010608090c01031407031a06040b12090303011401180e1302010f 73
    0x5940000c21140c20f240309481c003104c2c0a85124042d101801643d003c1d607101d02c0002180c820084e450340c0103100d500c103135496803150a9150801d1001020090080501060404c50a41c001c2504c00305448640c550b124400c0c9401105000c56450041041c0021800700741d01c600d0070026803405641003984164000f1035208c052900e52224581030070098107001840380c2c2c0b0142041c2c0c507102d41040b00d0391203070403140941d940c0d0340c0ca181e00c400030221030300440c0041c0946000810b0300c400341318882e4034042c1c0c030807915814840e581d04a8080003001c43c504450398130680d02c51070340041c0240241d40c020701282d155488941b51030102681000c0641e2030140c101803510340114000002c1403083e0b03420041e94030780060070500074100004000c15141c4910750091012400007504d41d810070040c204502c0c1100100c007251660307148140d07a80428000c440108240901e000f8955205021391042083c08260031004640c0e01c03c000d01195609481c0c800d002c0751b10b42e81001c15542c0040f02e540e00c441d020b24014901d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 496851339 1250 496850089 496850093
    0x504030209060907021510080703290c0415030b0409061d0309030a030f023a05040302090411010c0f05070311060a020d12112205090103030203030411060403050a0b0601030f09 77
    0x261b481c1d070301051041840040c003281e101d81c0760013a40005080c10a0807074420a881e403d058890801008290100700003081882200c1d41c0c1c401901030041d03012880c001d00306401c11940c03860b060244130a1604040d900d640c10701032607480d4020b111b0f099001d4940001e0312800d04105070800071100c18445426441045503d80c83c0c0c800040c84d0702c61541502d4950000603046908034240602d1403010b5100d0315101020000d074456882090b01e05950404031440e40801c1208103540500841c80080d44c0039125400003400300d41d47d130123a0300e140f040504d000e1074000d940340e444900d00c1451120903103059210000c00d00400516100c00c1d03030080c8080307038101d0510a40c0c5500075681d060b83d0180c28104041d03240742d1a0280c0309a0400c56048200031b60702511425416041c12801610f42c1d552001e4031200c1800003428102505910306890b09680590b01c0c5507100e4403405496000d20b000140c110008010004c0410024000103416600c0f030005114035052000005055560707188182c0350152400340c1c1000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 496852589 1250 496851339 496851343
    0x2714030c0a0b1602010302040806090105060906010c03120203060d12050a0e041e090516120c06030204061202070305090901030b06090a0501050d0605090106031406192c010912050403020906090702 86
    0xc1c400c43d0041000261000a00c0101c010740244d5100d800203101c3c1c1c4060001c002c60642005114907029146001d02d0341c2c1d010700448204802c02d5014010a044013405040e80b0707120380080d68044000b82428040325801d07511101c00b0381000d40b40760006900071601d640113540c0800800120341c42202c0900040d000c0c218540310350300000b0848032440d6a83c1c030b1000200003050010503002d01542c4008400107654020f0182e108444041c1160004250b860200c0e0480c024030a40b015540b8070365540a050702c03c0c0030740000a41c00443c069091080920000f42c143c1da85c0750056002c1c1d4400d07402c095140c20004244008060090000b041060600005000d1501d07040d1800b2080340c3c2048001c0b07050b0300e41041311401800300d0342024001408110001004001c0068803034098401680005c200c95a00c48840088504845c141c3d64000350801c0501c00b011016858070500440c5e200c0000340e00780841d5038072401510aa070b0b81c0d40c00300300b0204007002541361801e102944240140c03021940c030702d41843c0082d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 496853839 1250 496852589 496852597
    0xc0d0207060e0a080318072103091a0a030e0a210243030b0601030b0103020d05041a0708091902062206030e0c10050c03070c0905060f0d0507062714030c0a0b 69
    0x40b402c23201c944010420705103d02525070040c501144601e0305103101554550140d4408501900464282480003800000000340094880e410281006404107416031003042454690a5401140300b845000300e146031811010704000b0101080008403074800e1203503400048540020181c940d4103c11080000c1480000510f51004003403034009440b50700f41c00107030001d004101001e2031321440c0030100801c22850034071700006569188800412566500001c41d1000c2c01260b007811690042400e8240e058814402044c07101e2004101034108540400d14681600010160b00f1240c2c082c85020084190903200e0300160100102c080c01e003400300304000c0359000b0060382c840d03c1004000619200700e0b45052090707820040e0b100000c0b008a6584070b03600340181c1410780c0c51905c540740611241600b03140c0300852030b00f5a58030034081d24003a1314058007a9030101c0f9840ca0303a05016019003801018884680c0420041c00c0480c400c4580820b002c4c05051800a48508103802041c0c031100c244185458035083d9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 496855089 1250 496853839 496853879
    0x61107090b031014060315010f05040c140a03091205070b01180e060109061d060f0f031c0519091a070201052106040b03060c0d0207060e0a08031807 65
    0x841e0305046000440d10300f58980b29000c014902e0100207145103001114100d0080404a04a403000303003243c035200d00089030a202e284040070f04d82404008a080c80d03000403050800750b0a00c9002038491080c481a107500209801001940d50000207042007090910001001d03e02c3c98018180306043c0d85001e0690418000c0c44189640c0e2111042800550380050449103030541c103854203135940302c2510000e803006004010503803030200e4a1904080d451000710744910030007012500c00c0307000c1c42c042c04500c0814407407a03034040c0a07101c0000429000440e0b401c034100d80b19a50141c1e1141040390301c140d20602d1461f00e50822110080811000c1c1b0f2038100001c0040c1d6444070a0b43c0c9240b580b0060703421740300310b680510360404031541030552180b80040c030354441c0360700740d8090050303c00500406444401c219114000040f040c0182c07034058100b0b50107860518844c2d00001483e0b07140c030907a00d00e04991003e0441c0d00800002c03c010000380c0085c0705030141440c03a4000c00101d070400c001c1a01d02442d100300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 496856339 1250 496855089 496855091
    0x4121202061915030c0314010b030c0f1e0a080304050103140601080711010e1504050c0301090b15060d06080d0f0f020a0204090302031c0b0301111303170d0c020304030b0106110709 79
    0x42c0f40300d100c03440c280e40011a03101d5103e5a02c941e0b2854161421034040040e172403d54680000c006446c10080303030765881410001c11400050006d4010880005102d4072401101e0b610f800803c910b545558410001804041300110b843d40d190100040070760f2001180c40650210303050601c1180d981041603a50010818101562840f40560a140c0140440d0700c0681c0d0f00d02c01d65442e0703000354000e81e5009001d07a006805881c9416403840925013030720b9005000a00600c2d032140021410301c0c000450641280c4000c060919006010503a007040e60482d400403403080d00080807801c00c590f0405184030224100e800c2c01f000920034070b007019440701e0360828080d0242d500c450a800c2014800d008588081e00340d004030140540d00c0d0200c00c0f0080030760110081c020742c038001d00e008079040d01c01d0680300c080b03c443d911244d18500f156a100c40205428001c00303600c54003800810f581c28000d004642c204c0034964015130b00d60745141003024400f0410303800034050083c0c1444d0305412040c0810f80105a41c45460 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 496857589 1250 496856339 496856351
    0xb0f0a060c03020316030801050f100206150406090e060106091502070603020901030e0d0c1205090901090e01020405090408120106110d0c1407060c120f051207050f041212020619 78
    0x2c0c01da00318441c15242143c418042d03001c3c64105900316202e103042c0d41c0c0540d00c1400884580341072111a00c528440c080c0580d010200050088a0440e202481079202800c04130701a682d036208001560341d00e00c0b076945540c10410041c0301c1c041c1d0100580004003c08811400c002801075000fa480d070000b4050b043c10140c00040c0d004584e4080d4110320200c5a80b0021581d42170203121004042c1c1c085007008541501c000c801ca45a4203210b101540c90f51180104078041076460310a441d401003000e114554082d540074132000401e80c0d2800e4609100c3c0d400f452095a9962500301500f06000c1b05800040a0100c410700114100702c00150117514804d41e41000841c089850030701411554143c0b80001d10380c420100e02050031940490140d2507284100402c03130307a03c4154181503804140b0045d180002900c28008100088a18001150440c00303906240b80b4014a6410303001c216405600b061840001280300c040401c51801c44e0340e0b002d0580c40c40909843e003003404000b210390a140107a40401502c0742 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 496858839 1250 496857589 496857593
    0x219050f010e030f040b0915040803030403030509072d030b0106082505030103030503040c0e0a090b01140303031b0c030a090501021b0f130f09050f0d05090307150309150f0b0f0a060c 80
    0xd2544900c2204817030b800d27407100d903100c40c602e603290b008590840020341420042440c5400002c0c1440a0710b040180181d481d01c001814041001c54980f5514164140c0c1000000442c00c03540b4000e010f0012139407060498500041d041c1444106044800340031800c903a40b840c05280e100050343c2c107490303041c50629503d07161070405030003044254015690818500090001c20340440e4001d94503a8481c0c2001c40d0705030381e80c086003090502180e441b1500354204100141000400424640080c100e00d0507041c20300c072031500d180e481c5400c4040541c003c1095000300340683c0d80c0411000e90420b0001e5080c1e00800b0702040844c00a4503411032050013251140407541840080d50400350421440e0300e80ec00403245581401c0340d60708034030048482d10303018000b040001706100744211910035802900800c8546d01d4140001450540710951004040d6124045070004020301e0301034889164000004c5480500d1110507c102c42c071008003144502071078031255100d80c44104408007141e0450805201c0b8400c0d82c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 496860089 1250 496858839 496858849
    0xd0513060804210206011404020702030d081e01030b180c1513180222150c02011403070306080106080a0f140102041d100608090a120219050f010e030f040b09 69
    0x403e4001111001c060004050541c000b440c18100c0d0407810142541020080c244004c038820140e010b50180c001503400c0c140940a9425141c2001641c0a40744102c3d1031300300158a10789003038100321082540802800090000a002c85011804c4400a41580d4070018001080c001400c0741e8142d0003903001c00e41007540c40d08608042c0041940c000b011181821145400000b50700c042040a0644111030f64006180243d1202c0002e0b83d40010701c0c200c0380c803441c00040c0d035040805c1c01c040741000750203a01e640014140c0380141d0301840301e039140450520706101200d400c0d989560042030980c2c1c00303c0005d0010400f1042d0107150107811040d0a01d420b185244072502a204030340040c0218100745444c0402e00f52251003a501c03540941d0b0221010a464170011510003c060301c036042c0c0395001c00b00050100d1828414400d0340c18050040303a944114121001b003c01881c65025152a0001f00c0c440880c61028003641c290031000314051854401e480b4600e940303d008500034010381c00c2c00406c0e803942c6600d030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 496861339 1250 496860089 496860113
    0x4050d170c010c02072103050a030f0603140a1a06100503040c0b0403081209030a080109020c0c091e0c030c070b15041802130506030d0311120a06080d0513060804 71
    0x100070000d100c1e210840101941d155960321a00700a5854101e245050307900c201440da001c550301d40d44651030580e240c0c40840141040081107440150b0314800080040d01d8110031000040e0703544013420380700803603041244551000385c00c228541102c2d2400c0041c41d60b03610024042840d0181800c0e0b884e91624201001507651300c2c0c05c03808050030002400700900031410003401c052411900301d0340c070b1542c8840c090340d1603004100b0480007150f0007000611400e88550003401c00d550326401180c9a0911020000b0001c050944d000b00b10000c444c2801c032003180300000c0f00d41e8400814168940345081000d02489c0502c03071840081d1501c0c0c08480890f040850a0b00e0342c0b01c40d200014000d1128900550a4100c0c00c40d400300100c0c800d034810007803000c07101d00ca8050309110b448004d016140c00c100700642a0044c00c19600514480082080307805032580d10441c0b240d000f40200c200009140d17080c010f0952030000000700d401d090100c14440c3e291440146041c07282076a580f468428440d48851030000a0408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 496862589 1250 496861339 496861357
    0x1207120804150c1b0e07030e011b080a0c050403020618010c0512120609060109090b1311041a071e11040906050603010f060308041e0b0f03091204050d17 67
    0x3010351202410302da4042281c0401a000385200c603040d0300d01100c02d041e06800343c440c0302515a0010001a600b601a40c44012002107903000440d00f29a82c09540d00e84540005041c80800c070400c0c113014400e4842d2060510b100d900d400e14624180c19500082c1c1c142c0103100c071603000d4015808420722141d20409000380c2c00c0d640502140c030800b107100301424107038004507841c500b0348000350009182460b1003c01140600010707100c00741c0c85c600349030396180030b4028900c1ea035402c86002d0880c400c8054407481034000901c00800400d8440f1b0520b01e10100310711507420406500705003480510b0208100c50b810b0300910401c810b040b55615031f42d01d0300318120700c600c44506034403620b4242030400b0300509801c15449584114000c010701004035608508882c1c0074080980126024007051040d4103100b07400310605407003494884452a030b64000b01c40542d00000858844600100500500007420030540d484004c0303c00a880c1010304100218070303810034810b0054000c45501804110b00c80c00d2204840b1052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 496863839 1250 496862589 496862609
    0x10623040e15120c3a03210b090105040c0818070b0307050a03060f0f0b0d0f0603080d11180105161203091106031506030a02040906120605061207120804 67
    0x103c1040c0740c291070b02e0003000100e01070301020142a0001082451910313008001c402d8048000703c869030242d5000c00906070031000d100c00054919896113010310b001e154110007100200c2e0301e04c1200c05029240d01c040e40854041c07070400c9070040c8000d812103142c5a10148181c1068141d00c9940080340c500f00e40e50b4007900203d0750010901030400e90000080182020985050140039918074003040011443d2027410540700e8009014014010014000c0041500d01e03003012540d00e071405640c0c0110740d5954803c888482c0001038640c0650468014040030000f240341e00c905240c0a504014813248070080158108840041c0b50422041c551904240f41031300007240b000000c40e0702c94041c000f010301c844151805682585401a070385007201c01c880c41031841c000e0308541049001c007400610340000d0840003440f41c00340804100030801d8071441008010003515075001203400c4c1030020807100045d04c0280a028a90312055002c0e000103134250480344800d82c4440362810905001c0114002e0f40c121380189 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 496865089 1250 496863839 496863859
    0x60f120c120e0601050906040b12070b03040507060c0c0e070512042915090408120c0a0e01020114040809121606030b0901120b2706010623040e15 64
    0x40e03449a841d0201c441244020400001904074031951040244a51580200c000340054403600b004d07002000d14040c081c00c0014000c1034071000a051410742d4001e0441e000c2c0100811041c004100207101c0201603e080840714500c43c2d4884200c0c0350740c00e00a07140c030000c5600104280d54461030407280c294414200c041c2490074240b900680105041c507140d10000b80d032a039010340b06c80784101c206000b007030300c901c1c4444c0d8031010809001200c3c3c4001c00c01d48110405000e0a4160509994114400c0800c10304a5075503401803100981450718004030103045a14001e00218a03111241e038154015406c400d04035146c101031000600b41840c050412841030040c1500c0700c2008082148590640f8405d40b42807001031513100c180004041d0900c2440a4160a4900000490480d6203006e03080503401c0511200007409078400d003882540380300100700320341c0100010002990302044840c4400303140b086048000e05035032701c258113901980c003c1040d1102184085154000078684845440303002030f10b11604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 496866339 1250 496865089 496865111
    0x1512230109050705190e221a0108150402090a1e021b0c06070506010e09032107020c010f0522152102070b01032004060b0d2004060f12 59
    0x44911620405004070700c60422070005014050085c4155030100d207842c215036440d00d6140501520511600321903000c0c2600c0080400c0d41d00380419007401c8c145850400365413408480500c1d009541560b20b0b001075824040c40b0050751002031441d002100030a001c5a0322901d00d405544000e040090b1030b840d00e00c00240a40d0b80142c80d01c164155461240584940007040014805907100c1d030f40e001030031500301c080140420400520140d4000d10f100301120306100320804151225100c00543e44290041c0070b0810040135410480348110301000e00c0d101a110a44075000b4205010b4454824107810000541105110600703c138400100000600d140303076601c000c48041c103820400c40c4032200740702d000740700c200a000260003242c041039440304680110f6803958460410240c904500201038100000c98003074070366602c1c0103480140100c08011541c40c01d0407407107076085078138100314880d0070846400d1540b195128042a5421240c00741000d00084460364400c46640c2c00b1201d01c0302e0310b0f40c542104102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 496867589 1250 496866339 496866343
    0x80621010911030703050a02190506070f0b0702120a0c11030303100f14010203070803130501090b060f1c0f2103020d0e061603020d1518151223010905 66
    0x508070b4010690250307603180c41c0b4141070b120303416404064166404021114010300f44551a8201010090703061480b0f00e0301c031030006450341d014040603911500200e040c0c038140b00c01100c5054009800d4001080302d5110341980c140035020300110308051102c0041080144803c40c42092240400102565560710305106420a85801806086441ca492000200309070311508404c0640e005e050b0019410044a1b90f100d0102c2d074802445410f1000c410307840500015070902902c0c0c81c0030b1090050420510f0308005100c0550303042002c1c24402c800c0300303814a50540b01300080350a103d8000c5400c3c50034070b81c54140a0200d115080440031901400e03040c541d019a4554003604030060f10702001e0081c0d00f0008081030343e900301580c681030764841d44a07188001e41e010380e000300040310f81c111000c034080e078002400da80c2c00c100c140d1006d80013403880300c2c42c203006c400c81c0c3c414035181c840178004401c0c10500700794200c8010310f890030004000d000c04486281c1d40600c500e541e5005400e0040c004e004010062510395 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 496868839 1250 496867589 496867601
    0x70602131e0602071e0504090b042915010311070c030314030c09210102070302070306051612050c07020a03052a1c0804080303010f0f0b160308062101 66
    0x1150464414030207000054200410710031509154010711007203042012035025440c8000858201c60003006001403203072510700074102507074051052500c1c2c9240c642814201c0005900240121640c040c0e042d070081d80000c4c00d0b098000036031180c54840c0c009084016801030041c40b40d401c04500010420f42c040010550081094a10a80e600b2a0b5005400d8000e00c0c980401e685111247c0f4042c8120903040c00c003e040c01034940c2d212012800c414030200da00f2400ca0f80700070740640050b0820242803061090a01545802c0048210414211024060001d00c20540302d40f51041441d04e82010807400000c5800783d071040c0303800900c103044541d6a80740c0196100c6210802c03d500d07001903005042c03c4002401c1c11100741d04040c09020700540160748245495400b40800c44080c0c900707000100e12804200007542c042e12003604400783c45400c0c98040000840181c0c0b052080f041c1c208600d030800440ca05580483d40d5150400c4021a00c88000150644c4011144082034030442c2c1c11045600105400030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 496870089 1250 496868839 496868849
    0x120c060106120c0e0907021c030606030501120c051908070e0103020f04060501022119030204050a0b0a0203040b2d130909080405010c081603030204030c0e0403090306020306010507060213 82
    0xc54034201103100304415505403000b00004103030345804400d034a05004030711641c006c49a2055404203510501a0740b0407001c440c00c0d60b030000ba542c001c10712000760144078003800b6141200600e81d603100707160f6829800c01400d00490740200d400c00300c41001a24084501800317020f90409035a04940c0700c003102c140402003440264420f00c005001410340d420540300e084283c581c1a809480750108581c0f034202001c10208440b9003423002041316400c0080032800d86c015800842e40c1c0941d03101d250108010b82d08550303403c112003020303081000b00c02c02900001180d04a5420218064941c4100c074810f509910f03a078690501c0710045011a03202d0715505100805013000140d2040c007555455030842000c640c02d41038000c2103560700b04000c0c016903014800482816209107191840c210038541c07682903005066900b10046900854140104100081040080e000a541045943c078003510020915882d40c4000b03400654000041a040c0c1d00c0340040300e0703045400000565403419100c881e030326010035510403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 496871339 1250 496870089 496870097
    0xb0d0b1f0e010e07053a14150114070503120915090309100905060a020c0112020a090308070206040503300a0c020118091a0a060302041d0a180305030a050f07021e120c060106 76
    0x20711080078841602c903030042381130300b0507880310403220070041d0b038039100d032000407199403900744641c8001610800c001e120b80c61149a505000c1d0400c4110607141c80300106105070310304145010061200d000005490940000320f600444130041d0903000d68020140340c010075040180011a001130640025a1141000080e83c0e14440142851144c0d0f04074000c288000d4001403070303003c0401c08240780790042c0802030700003004070303191a0340c0d04006450f1079610700c140707150810794072205c2c40c540740b94420352041104417603080ca2030241261002020202d40c124000d042c45140320014407081c1001030741002404005004001016007500d0905d42076003190b5959224601444000c5400e03817190080e074085500c1d01e0154101031400405183d560500200641d59842e80d075850400e4400440c3d4024802d03902a88a00b50340703040c50350b4401c040c0c44009094402e88480981800342d103581c0040c41510072480d04401d819408815070440d03090507403a500c82040c466010846198076400450307428102e51542c0c80d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 496872589 1250 496871339 496871351
    0x901030305120109021312060f0c230310030f15050a0e07050f2d0307061e020c090109020a03060e07020d0f0804080d0b0d0b1f0e010e07053a 62
    0xe4005d038030810621010040200c8410804840c0d0340480c4007805201ea40d010901c900080004401c41d024a404180041ea00401034074440c8000300241e8400840b054155180d8502030010301d0302e80f15103110050511007064684e60074801c40804010f2444d100180c2409142001d510581c060b0441021122643c05404000101031508031901460f039440030340342e940011944201c0340e5594100981010008040c41c0311504255024420078014194030b0f1214800ca41208041800c030302e100d00002020740d07100c5c01c420720366607452081035070441d5840039001d0b03a1802504030440282859510440c1048824414848869004a80c1c81101381566551a0080400842c1296050780c02d48019111031420000b21511040542020f80b0062015003056404101c5030b60742c80b4108000c035100c4038001040580400d810664036102c600504c9034040302c40055042000c400c030b15010140141c4203014000522203101e41320b045c4042c0014010020424070f80c0da0000c14081185908401d100b44146400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 496873839 1250 496872589 496872599
    0x1110f0705010f0c0c0e06030f01150905010b16170c01090503040602150c22050907030b090c090906060315090703050a0501060318030e211b0d020603150f09010303051201 75
    0x4020300000c1c0e00701c0617044446260010000c001c0ca0064001c0c0d8041c011110100794404090007039508407140e0542041e0264503080c5040304540301178002c40080369007003008c00400d0040d4040c1b8803a090700b1102004142074841c001d6542841440343c0c9000550030542d030402401400300c0504103e818030307021340d56401c80d5540304c0c1c542d0140458520301c003184203015803401d001e21440c032914560034050030f0700d001645071800503ca074001120403000007030322000e0810f40e6081c4441c1c9103400030008110541071003005000151062801000b460082401100098002940040015801001400c6028a810f090754024040c00044400c4200c02e070030304000045c00d5101c3c2c0f044000c00b2161f0070703414840030303801e03581110700c0540b0782c4209601a00280440d554596a0400b50300c10b49260750042c070f15000c103c0040c1d009040c00c4c07140076100c1c1111180400150f21004103c9501c0880500a40d4400c0903680000b001845c9004a641c0c10150180001c0304264100005250840300101c80524580eaa1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 496875089 1250 496873839 496873847
    0x1202060106230d05091c0e012a06020c030307180302180907050a0605040306060e130f03020a0f0609110d0201020d030b030307050a0b060112181101110f0705010f 71
    0x80c425040001c018002ca01c2602208459a0046880200da85071808840c190710030180c0f103050340c8200170307a0826490807a00c0440c01c9140038420a0508104249942d284006049816140385d01a603400d80281003262803080050700d10381943d80b018003192201c9450b00170300d03500d0700704480c01d00208019071030800c100810918141c040345d03801004685450b041d001c1e1030b440b000029111900c28410780d42c0c0031405070348440540c80503000c40d82e103580d04c0b14510304203203090300c100ea07104080c03101d484428002e82000760601712001d07036003241c0d0b042d501840c2840c01728500301071508040c09a806c1403548208008054118491041c051013200400c0c00340c800c03c0183e181c1c1300c164024090303403101c1c0140c1101c900a402541294800030705690400d8000d031036840c14040c2c880002c4071650800c00070084690b8010600781c2007020444000c010810411210380d410280c04140905280050009061140c1c0319060009020503800181d6100f16243d10310142e40d0b400710b001e1680031820303000343d119000e481 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 496876339 1250 496875089 496875091
    0x1080108060108030a03020903011b11150c16030c0b04111f021e070503070909032012090a05040212010302011e170705070f0b01081002180f0a0f12120206 68
    0x41d503c0650f203880381890040d0000c0d402040380941654a484002d610800c20400c104035000064407541008200304602c03130f0500e00c0d84c400010311150a0f00603c035910050409440080c2091020340c200781e22142001c0d42d003240000b2000308101c01c41020001041200c5855060040381501c0303180500c22220080c0c03803030000811aa1005070f12205604545007034505042041c611a001618200d54031040424102000c0b80c03c1020086d444250800816520241c80c0c00703100160761145001d05100c4807403544400300c04140014141002c5115002c50703641d10030400040c0001807046645580340749030003950340d109100680c0405c00160b2405074080803028444da000034079a03100c1100c1c1c6450003100c00c0090b0041c11900410006210202c002170b00c940c0d1580819020725081e640e1076141080051405500320700c0803001c41d005019060f200c0318408041400060100c4407403200d0001d04c400b08481000d00c0d0f02260200c3c1903000c000403c0c0c40c00b10140c1450078010a030044607458104c5050fa55808 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 496877589 1250 496876339 496876349
    0x20c0313091107050a030e0a0504020c06060f0316060c080f07030c02040605090c070b0a0f09050609250e070c0c0f0e180c01050c3d2f0c070e06010801080601 69
    0x4403105c0c0000901c01c13441030780f442d035000304040e00c51601e03003022070100d0300081c11018480e40103a00f8881c052815000a02d00100102d0041a4880820160f443c02e920f16106d44010311001c1d2341c0c0082000401d1043c1c0301c428601e00b140c1c80e110001d600b002080710f807098a083e80614600440441c2030306101c0c034600e1041940503801e40c030301445503075203007a526801803504588640d5100c1070b81c94031030680a01e284150150000b40403c2c10b0088565040001c0c20a411141e42e4420b400c010004010604d1082212100d065440c0d00380c2d15040c003940e000b040d00c44010000402003070082110f1a10711490310954540e411805596a103d403a0702c01d400c2e5280702489100c0d482500d6400c05907128500808984446100307607038003c2d0890403242c001c960a1104d1000c0361100b40c00e081041c044030341c2c001c00060400c510034060b034220750400640c8060350303401804200b10341400710012070001c401180d16a019801c03c035410b040d5039500403080520b060300e4413800100158000a14020f00080c50f86c10f0312 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 496878839 1250 496877589 496877593
    0xc011407050d0903120f020c15130b1b0a0f020d06090b0a0203090c060408100504020a09050a050103060b0910261b040b0102030f341202190b04080c01020c031309110705 74
    0x121408010845c40d076005c0c1b420390858100003001040219070304643c01044841e100c69140d080100484c83359010b01c800904d4968000110040801c201020448032560141c640000040050074142c0c00b801a101001d00071505100034002000110b9008601c42e0ba118070503608085d61010410920344214800c201c4558042230681e1903131507181e804a034002e440203180750b4900d40c2c1da11516003515021918a48541d668000400c00c1c04040d0244846001c012180098645020440c81e100181075001d850310040310700450a021031018910039003102007000c1224884510300b00100b0341e01d00141001030042d420300c010110a0f5000206485100c20103800c000e00b000d172400360a280c0e10b81d8280c2041c0850b0740303030895404d070000b950351808440340c02031400e40911400c0f404082d240484464901c810042b14840880c08100c204101c3c6d0740080e0310850490b0b480c500000d180f406400f40c051400d80b9800002000c0c0304000b101d441d080d080342c4580409104200345810030030402e000b6400b02070815 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 496880089 1250 496878839 496878853
    0x8030711060108070e192a08070f05071202030c0a0f060c0804050703030f03020d020f0d0501062c041401060f080609040305030606090a180f1d0c011407050d0903120f02 74
    0x4610180419130365804c82c080004030000d80b160010346060440800c03440e070158047c100920280e2006003164412514180815041c86100009205204000014119140400a107512284240122040c02d440c90b81141c08600031801d200c80080c0081008031f41c5d076450300d0b201c0c89889001d03e44580c841c0c0c0d04440902071051550f201901c04070800e03901d1800309903003009a04400320052000d814054107103107002d9221820900807030110703401078018009021402c0c59040b06841c110b0405040c01e540048040070300256000410040e0140e40e20209a80c0065000424115440501c14500c201281d841c0f91071500c41c4818091241c1c0150380190005008000240a50400c0d4000340b000300310240c00314285641e14100503950701d190602501c40c003921206040141d02207170091a01352003603075514203400c038065600c3c1c659803d1a10012414403245440d001100c4101c1d2090354030f8240c201c000e48600d16240c0400500641e203500040342c07013600c140d1201c0e03162481a4101c6420341e550360010404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 496881339 1250 496880089 496880101
    0x506010c0213150303050d0b010315090209060d05010e07090b07020922350f030115050c010c0f0f051218030c070f0510050304030e041808030711060108070e 69
    0x6111011070b0911032500c60100c00b21106540ca4910b0042d40240d0301ea030344481b0711242e82c6050740e0074034000301c0c10541400404030360342e80c42c00262401c0312011000140c0e01c80c8c8500104602d409010a0050320a10f0f103000040d4229403404c80c6881005240e44031003500d17468803110046802074031406900007048800013200742c070103803130301410405001500090034291542c03000d03c0e5458000141c10500202081c00c1620400c0c040504080000c0f50440c6040055210708041c1c0350105204000311030300400d00d081006402541142c26041740301000b40b04803101c2c02d501604440c1e840309150002110003401030705445c45002035800411200092020039261082c85d4000310030031106803401404104070264400342d0400186008106003468481003628084c200112032440c0035441c014458204100000640e001c10b168513000800c450006400d403140b512100d18120054004202c41000014001740540224115009042d080c04440f0340b42c3e00d801005840b0710061149002c2404040d0200e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 496882589 1250 496881339 496881349
    0x30117070e101509090e1b0312030c0315031006050f04090f02130213080f060702010507020709050406021912061403070b03150301180b070306050a1202280512010506010c02 76
    0xe2038152138114042d40e01e070492035044581724850404d09621100049040c3e4102400146802604801034880a840a00300c0c503014400248104015800040042c26024912401c0324480030082d0850742c1d040407a201c12001007250b405014443c0c005055070011030301e01030280003941c690284900301444029402d103c0c1c1205060490011150280181c0c1c901c400702c02c1000f002031480b14000d20702900c0035030489081c0080039086004690521080001d41e64000039400c0440b404414001016a21b90500030700a00400782c04c100c0c550206c01940d5101036104140300707810b00c3d000da000c001c00c644e0b9101100c1d0766162201d40c1034058101030b03c204040324000011b10344c446641384041d02503030b080c40006400c6039503c8540c440e16020f00d82c11103040c0031314606242d40c0040c0c141010010ba508002c0000e102c69110300c1819402e4a15006800440d150b0f18100401c0c000300c0102072286110003009080014802d01402c0d016480784904003c0303901c01409942c0c007598040c0c490701001445602445 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 496883839 1250 496882589 496882619
    0xf07171207060e0a021c1112070501080912040b0417011e0f18050718020313020d020619050c010c02030f12061507031709060f0c130b030117070e10 65
    0x411900904c14040c01507100d00001100313140c0d1070310340f8185009603454001c8031403c5107884280143c000082d8007640c064006032840580e00c0900300302d490340d41c40044981c6000010b000c002c1a0070404500099610310b44000741c025640c0c00540340e0340d8680500d920070300303d810341214401101c5002003100a20302a80d40404d00c20715944e1800304100030108800c00e1710041e42203044899a011103000c2240c6500544841c2603401800701c00d52a40c2085450402110540709001c1d22800c21980c034082150340345000c5810614500c2c425040944211101600c1031f08840c1d0705401c15400c28000070203542c80402103440c50510010b003141400e080c500514004070000740804d4009211007140c40946022038040c000300c40c40f82d81c800440f0500d0949400350140080c1844c59a9413010741400b42c00380e003007041264005c0c4d40956180d21500107910503000010035500260642d440040086040c0a40d44c0c918200503c0040803509800d03526000744101107021505883c2d102c1a05506010440c0c4c0403c00e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 496885089 1250 496883839 496883861
    0x60703020d150e0906010b0c0d051803060a1e020f180a08060f07090510080f060f040905241306090204200c010e06090a030804140f0717120706 63
    0xb000301c0c058084030351691181e080749034440c04102c200043c10204101e814003400c20040494142494030070059a0b844406e0500428040081100881703040141080790901100400321038007802c00440f400010041c0800c146c0c01d4000c9071034890070440c464006c035100c0e03801c2e0803e03091034201040400404450300140305540300c4888070700000c180c60100700382406044408800300c00c90411ba4000360890b000303944030b18025001811040d940c5500810030660000d40080340300c0399545d60308001501b030b2184d0003c136548140f9081c0100b06001300040c2a107201038090462001644003084155040041103800400a41d0705100c001d0015070f40303402c40302c051803001d40089184140c0d09100442c0004c41d88050201d02030129480110b078009001d5a19407109041c050146410094030090722001180c0c006002e00112102040812070380c03090b6035641c0003125050342c40d0801004225900e50305184640e5200d02d8901c085248408000715040540e1540341c0b003000c1c5803541c9540d6400c0544840602 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 496886339 1250 496885089 496885091
    0x50126030a052a0609060712140a05130c18110405030606060a090b041818050d0c05070f0902032703030429040804051905153a0c0809060703020d 64
    0x3441c8070b040010403404d8003a00a04029042034a40740c3d00040a48030000440048141803d2003003296a280200d02500101d00000108190381e035941090341c0302c0710b600001000e0216020000400f41c105400b140b500d4000804180405000d51460720518000e41c0a600c1e0f160300000040754030752600f90010030070002541880321000344c3d11901c140d5a40c020390700214600100c00610b070081c0c44944510150350040110340b81c4006416103906540b50a18003000c824014519105018003100300003000c02807103403410948031a40c071386000c4400307504107030b6200211080c89aa4900740c0003d01c08030781003082020b8001c5003183d44540340d072901e1105000e038803044017114810205100030425029171044c1e000b0a01c8540e142d19102c00d000d05050b2400f006980390840041c02e00c00c40d900d0310102c40b5041c102141d025143e958800c45405418161100d007881321441002038941c10720384200e01c002a1404e20401c11000c1c0f0094030554640710100e0340d410303694101800140b155800390307024141c0120740d900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 496887589 1250 496886339 496886407
    0x1b05090a05010c1110020f24070831062301050d030f050306040e0a0b061311090f010504080316050c040e0303062b030305010f060c120c030210050126030a05 69
    0xb8038903081140c0d501000309824818008c03160302c0c07030707205e0307219034114000d4a405200f9141c01d0f10352403400602c0c8803921144080300c140308209090f8401944d04400d0300721804109400800b518001c410080003680031019003d0000012070346806150040035035050b448090940c12080422100f90380024092a07210390390b01c62003202d00c00300b0841c480c403952044409103280c0c1084403c00107001142800090403078145006448040d40c1c810544599100c15100d506180d00454016141070040c0e07000050b00c2d20011822140c000b02c450314598480c0e008800381c43c0e42091000c18001900c482e0305462030190310030004101e00c0d041c010038544482340c034400c45840b0044018035018078007509041c1680060344a000601c0142905100070000b4881400c040700a504a6602c0e95110955120b8140c14400140f01c400140350081c0198020703c0000c29041100307603141c00c40000d90248680b244c82c1000c5164010760401e490010031544002c031ba03616001c1c1000c0708031200b01d0000d04140140c0c8283e8803460 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 496888839 1250 496887589 496887613
    0x60c050f030c0a0e040e190602390606010905060c0f0613050f07140d060204080106061d0d031b020609060c0307020114040302061c1b05090a05010c111002 68
    0x18018602600502c0c5503290b903000300c83e030020540b0144c40e443c035210306e00d0141075a40c2d0540004003803107a0001805002020560380c00d040d4024068142e00214220b40c5e0070701d150000700c0158016040041d1a144540074207035054400340e640e0400c8407801c3c040f41c8110020f02032480e020b0083d01400e0090401c5510403442e64045500342401a12003240307001c941c2d4255001c0100c00d2120b2403168a4402c004c203141440c00302803642c1030424044040c022900241c0301c02c180070094044034041c0490764000e0003515500c0400400f4002c82540c3c500c90113580404c03140b524604039201e490402d07055503030340340b42c10102d075417071042d130b0060f02c1040740d00034400c000c05da21301d07111200038007031081c0d8240185841d2441e134000540301c10030751404e0b890300b050200f0082c40180d540700300741d030301e400c1e40300000c3c40302e400c001c1005000030084800000280c000d80e204e0600c000c0e84c00002019900d1003910310f840302ea5901c02c01540c0011a0b0040180655040680b40c56a13080204021100341d440e48111a42c4038501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 496890089 1250 496888839 496888867
    0xe0603100903051e0f092e0905010f0206070e101b08070c0f03080313110909070f0f1206090804260d0e0906091504141006050408060103060c05 63
    0x41d20308401003840401c40c04060803580c265139400d026400d07038452811045d043d00c07202c2c038414a000700b445503280390440007800031600d6030078030150009030850030740780103041c5d014010b0301051103002e0004110203c00241e80b440801c00f18041e00a60316a41d00410000c0d08019108142500c5d1104001858184100b030451404c0b840c14440d005442146e80c410144c245002c20920a0300101c41c24456030a08000080b01c03003003180c0d07004000700e0075030114140038501446401030a5040030342c011483d1080c801000c0e4041607100c112400b280d1020390f00d598a03082589503071517502c245000851203502500215042c1d4000314407851003501f8161a007a26011250030f1612080b043c256402810004108510f10410045030300c0b00b103c0c20014002c1d24800006541c60200800c2203025041140c003041030f1240b0340440031007005008000303000c3c03402d400c20403c03c1e002c03040710010040002c035034000510902407400c88060310003103006000980e0840e2141c5000d42940000d10040000801080c0820654 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 496891339 1250 496890089 496890101
    0x20f1e09041b090905010b060a021b0f1201050609060301060510030e0c04020c070602010e0a080d020903011b03020a021603020d0b07050f04030c03021e0306071d030102030702010b0102071508010e060310 89
    0x400d00d0028101c1c0d010309211b400c44411200f01c0740031b140c017040711100031070b0001140c1c0300b0900c18104000480294034042041c41b580341035460380181540c40d102d0344004041d00500d01c1524159040ca000780e40303550805090791890b100b5a030304015046c1090007001d2094120b411105080d5017150360042c071100104003203902010402280b03811a05c410f001f6181c1c280180000707000100000d00c0b0035896078648604c44d2095194114641c0d83c006103164098400b074101083c40a4079401c0c0081a102044000d406076110306400360050080c501009510110101e92509507500502200c00c000c0040c2d0ba40d850b4071360094644014403005206140060f0303540700017440914420308400000d28034500c1449060036400d103900c40b000010450020641d21300265140d41b01030f46141c0112118240c41c01c0d800c10883c080e82490b0954000800c20940b550150403082021200f0303405c99542c01d90725030a09400c02059020380340069849001005103008a04000b500008000c042c1c88a42800394824012103a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 496892589 1250 496891339 496891349
    0x61d01091a0a112b0309021003020405030c061903180b0a2315040b060d060312110a0c09050c0c25080712021e0a12020f1e09041b 57
    0x1800a0300c03800d00781e0f1104000600148030700041038404d00b0391210a6101c43c000601109400c850501d070028603110341c1181308810f401400d0040080d00684008001c0d40c002d0052a000b40704013038020000e81052012100d070079458503000c1103100c11204080300544a1080200060002480d501022030b22941c2100e001d6201401c00048414044403610100002807140c4140a6168000c10017160320f4520105035110048800049250074040025011300403100b90300110b901d8000084100001d004a42c100c00c0e11540310051100d2280c2e075100d0390741c184c04d400100801500e1130300304035428281d08100d07040201060007608084101c00941d140080e003051480f00e0140506103001429000b0f9000806400f040300900305480c104070441303500032240e5000070701410441d41d0f81c0c4060035420010514844004140e50040e60b5222100403502200704411b91061041c01843d4801c2d1400c03986446001d042e07035200400d2841164100032620100410540350300c82c00212004050076080d2128020340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 496893839 1250 496892589 496892639
    0x12020a0f0b0d180b16031512020a09020703050d2f07210906120204080a0b010602060c090904200306090d1106040302121605030d0504030810061d0109 66
    0x56044940c0310b00340c2e450000624030303070309401100d840411581803d8607444102c9981c0140714002c442c2d000c800400d0955503000c401112544082591040c06080355581d6000300e1720048442d03140d101c09000ca108240c40200804e600b0000c844100200340c009514403156810410031803685e0080d8241400c45140b1040400740d0002650010021045416043d4000c0034800038040c1c524804003401c40d034080d010f20028010010701450300e44844d03030101d6028000c00c2d07080d664001458600260000000c0c002c0e0340c09409400001010001c2e240140c614010004116003080c0e2525101e500000711140703520100c040342d071800884640c504202090040203100000d1034007140c0910000c2011003880a0241c45030000340602001c40d50014580850036012087e03240c0e16110541c05014013004900003c000303000100e009040f00190303500c014844ca00070b8554070303101d0340e034591a00c1a1910310b0240b000032800c20340c511100001490140f800445040c18400003040d1107880b030b20710300042085405500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 496895089 1250 496893839 496893847
    0xc2515030b0a03060221161b0c0603140f040305090402030618010e01061d06030103030e06040e0103030221090d0303181406060f0d030e01080c120702161703030112020a0f0b 76
    0x16240c6c003040401c4c4400065841c1c05400c20b0424030340e085d00fa04261804100e064850b80e03801e0700f840b18800d508140d2040d642421203949000140240c04a03078280c201240900c000614019240e0380300e24803541e41036a81d40d00d4100300300200310007500080d108035081413500a02415003860f81c5c42c064003034805004c1048540d0724000000305200c5421225454822000030031f000c0036144e80050302d0542c0d6040c1040808020f68101240980c020341d8401094a02c00c6000001819004917480f440e1400a150300d4170f24a64403c018191446962110394101a10b03d407201d001c80e1099202880c17508007140050141c20140d1552036800c0010004012960030481c1402105d2405c8000c00361090b406648030500035200741c030b0180944e011203840d02d060054100000307420303c41941c1254440e000c00d098a0b901401c01c408002d54460507003071852550032252078082224580390b0803444480300410700440c5941c1c00c104803118101c541c010100d0f0041e03040e19010503044445103a110240403046201516 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 496896339 1250 496895089 496895107
    0x71109070216060302040b1e28020123072d0e040506090903120919060506030c120304060c060e01111201050f0f040209130509030c2515030b0a030602 66
    0x56540040c0134107204001c1000000c00081c191b0b4100e914000082e090014101c820305130b54030036000003c07030300c04045a841100103c0c8000f00e0040800560003007100b203001014496031901c241d11112242d481d40e40c001154103100e55240346091000300810180148544013220b00c2d104050308683c042500e6080a007101d090612079140e103c0781c200c96480e01d6040c045003c58483c8034036861080c0105803d00040d0700340b0801c0145400110314141410044221030402000410f01034a480d8468000c0284250035031608914800c0c44101800155140c50300d011019100841c101c041142d20035110141c4c0c042c000c20130721641200342c0c20122420340d03030410502c0045a480050300113600c01c42144170052140e48407002074140c039010580e00140d03a94060030010b070001849102c003400083c1014100149000044003802c0c80800b041d0880320108941301d0074601e240c2da0540c4d502c0140a504908101345a0791004100d2009540d040028180c2c40401c00702d00040e0140c0c1007618090303000500404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 496897589 1250 496896339 496896373
    0x603011701180218220b0a051608370510060201090809040c0e0907020f0f03120718030b010803090a05040c2709050103060b1906140711090702 63
    0xd80901c8a002c00c00064207964005015022040b140c0f003407000c00c910010302c068201000400070400e00000e010f19544c4c50b0b1030000d88088007140e0040c40c0b28140800700b0802d04444c41e015040a005031140042030740c1d000d104102c0300030820070490480d0700800e10b0b00e10703021582d84104181208031801007550300d00307000715100c2041035900c03101c11a07142200c49400304031840c0c1034070000701e4220b41c0803400f040109800ca030300c56490440c15902a07040c0d0244441c00d5000200750780f222440100360303a40480e000c2c10281d02c138000c01c00039041c810486800583d805105080a5004281c000c1120305415100e4640e80b032104400d130003030380003940f000803401014548080600f00071314040350140194440030f1001402c00c0c8004220280116583c0500d881c0c054240c03090b48040c06182c401000f596a40703040200c0a0485182c200c0c1c00340282c03000000700c40c1c40c50b12148003991644c0d2212040240c082103072407800c0d4007460303003551001145290210169180c45016014052940c000c104810036881004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 496898839 1250 496897589 496897601
    0xb13031403041805070507081c180812060d0c17150c0d0b030c0d0b2a18310c030c020a06020c070902040b27010c060c0e0603011701 58
    0x446207500921042168a407801a28644514401c0c0081816140c0c03103001e0307807207002d000d00c0200258000700f81d008200807421410720300f43d40d032010140940fa5081d001176a01032080140904604020000303101095454005c09810810281800c89070900c66222400320a010340c20681140c0207608000da82074908002540700050b070b600c1041010b0a20f2042c2d403842d0303c9803056141c5c1d42d645409003411569030a00640000303d00290000e50900034514008590503411100d840e01180c903103050541c5d06e404043c1c92007144001c030000340c0c5000c4d002d1a5230704c0c483c1e00f40d41d0516845422001819900c40c09516120100403516408801d400c280c0b1580400703450803414040e00305890031080c0c11003581d000807643c19241d000b800040e0390f200200c100350704060058010090f2a80000b40000303188011400506514244802000600c200158050620329500000500040030142007a01084103076100c0303004640c01e800c00714110040c40c408520181c1090303000c501d010561024014100000303010303078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 496900089 1250 496898839 496898873
    0x8010e070c060905100e01060603110c030a0c0606080a03030e06090609061602011d1c080f070e030a0b040b06010f180605130b0f070606060c0c150203040b1303 70
    0x1110152420100c0144144003810015181540341e424640a219091080d074451000341c000505c01d8111400c0701a020300040c0c1304140c0000c0c0303401c01034460500b40c107003520382400308040074620f068480c850807124440c00076800c0e01d50035680c110000f010300301000040c400c1c5219403800f250032500101c10a05018006003074016680020007008001c120114140340d000003207440c507000d4a40c4441c0200c0c010880c089201c0c13000600300322000003040c00082d00c103400c0b10840c100d0071507000c0c1001049848581c140c409250320b80003400480c074864099010010109000f6044848013441da0f200c0c1880c240c0283c80980d00b03030080500380b22403540c0c007101c0704010b080d2504021008442150011000141510880d800c0120124006100320305004040727005050031825141c58a1014504a0796907000002c1110654070344040064003900480e85990442e0704074046156140c500000300c0c2102c0c0301c0031040411400200004100c0c0d5900c5800740401206949440340c002c2d040d40340241a002030100b003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 496901339 1250 496900089 496900109
    0x1807030b040c093b0a1109070f05030f04080706140a060801020403050307080901020a0c031a070e010509040c03060801090f02040c02062503060f0602030a17010815060d0b0103120801 80
    0x49409040160006545441d03810660390510801d0030010302042d0b1040c6400c030130314000d440100c001e1169000c110300200e01c0c111902003807034603009002c2e01d402c8544400080808c100303000040c40f03080610592648580540301c018030344501d941e42c043c00c81e0700b0714990031000e038424001d10a92545070300c034101c05408500000c515150554807429030f43c1c040e5407070007800e030580050b9050142c2d00c02c1c840c454a450307200c0d418214141e22031a002c803140c9a041580e90060200300c0010701003d00c0340c6d40401000006865003481e00314500140300160810898550601d40c45030360000e18840c00740301e800708160003892803005000c46071040109580101c0d410b541154016014840b4801d840b000120403120b81026408006103006403d030082c0c45103038051080c54400d140e00154484e000b10081c00c45030441da48500c01d40340051003400c0d4110b03007030217003040541c4006000c0074104c4240008503000785005020210b40881b42e5201c0180040907001214094010240c070111300341c0100d030707a5024142200c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 496902589 1250 496901339 496901351
    0x3050c04050303040b0304060b0904030503090114161b080c10060e04020f06030a06080304170c030106030809060c0c0a09320a051e040305220509040b1807030b040c09 73
    0x9070f0742d001d9401680090b00380003000c40c007006400da124100b0450054414901841c003820090402c0c0c00c112604032955003050301243e40403040301c4100d8031402620028502d070031402c1100b01d90007040d50b40f46410050400e94000e021544600107400c0300d2100000400244101b40200029180c055111000b0400b0403002c2c440145e85586000700071705c1043d04c0d0f1030b48940c0c8101e80c5001901860f0f01815141c00009400b02d860940032000c04050054002168400b601103070078075080b50700912002d00709201c20701280d40c2501d4500000c002d03001d020800c4407601c0501c0400580d040b08290b02829420303580e04840441d020038600030340c140301d0f00403c0c42d541c040d01d804c540c101100b90007042e42020540d5000010880c070403228201104000d52140170038107142500e0040e1682d440810142c1003032480c40c40c0b80003102203041294058070700103440d00e070564483e079403101541200503008c981840c101c940e940c03002c0c032402c1065100a5000302c68060240c2030905005028801c42d8000c50b401d075013010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 496903839 1250 496902589 496902599
    0xc010905010201050c030f10031a060a0509091b01020a0b010e100e07050d09030504090c080402130e0a0f0201170403020304180204050607030e0a050d060e0628110702040903050a03050c04 82
    0x140a4070b42c4030040320300106c031f5a555681061100350464000411048620002c0c0d10f0480c0c664014903c0b0741404c0d100035440703603120b0040002c096002c5a040903194020100000d5420401c84144130024040c0120340343c10185a0b152150050260800010b03001d1503030030404054180c0c0c0c4604014802051600c999003803c4c3c2c0010701d180305500c2c2420006803240c030380f0401c161151044a004102c162010001c0e41c96034100103000501c152400d038411148405920150340c201e00c20080c21651280040002e510280d03a1085807028042c0c0c2a410300090000f800210b0000740c203000d2060b44250302440d50b617401d10041341da400341021002e1642610501090001e0b4442604948110b5010300381b00150032644400280c058010b40c02603500070110b00b03006020062a50418161960200e003603c0f080d40d103c510f01004045a180e94000c90241b010100c0344d5200240e00880035a40c1e889034103482c0c46519000309050b62804203044000502c00100d00140b0f55241c804c441c1c00110000700145014901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 496905089 1250 496903839 496903861
    0x906180b0708100b03070503100602071409310c15080106120b030708031c020306010504030807030e0402190225140604090603032105061c03020a0f050c01090501020105 74
    0x10181d405111003140031a01d2686444441c0c00104040310105907a4940301c40c0040040e0026030b92034110804c0204003082c41d074008a042015181800880c1c03c944c0c50340010822031000140c0349401e0400303101100741c030003554440c6150295001031001c3d203c0c0c1c0071a1070700c80164a17159100c0003501e15035a403280c00171070b4490f0030300c5d0458007145002d40c0c40c9894400d2040c01880f082c820941c0c18400d83d080020b03a5900800601442d400c4540008400205003d10005a2008990190001c0d50400051002503500340c041e00c651402490b1481241c1c4580e00403030100c0c0d00c408030049444102002900381158104286080030890041d0b00e0070380d00c80301c0241c203065401805103601031411a1420314440e1a0700e02941c005205100e070030302c080c03660f07410060000c0c3c04500380140c607105140d1000202c0d412a010f044c9c0100c0000d007005401c41c1524035109202413103a07a00714118000c461410000ca0440b407081d0308014007a10250600c04149400501840b0561744040c2c15a4180742c00c00a0110031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 496906339 1250 496905089 496905091
    0x10506060409051510122007030302220b0304020405090d080612010b03070f0e0c0a09061d0d11091315090206160503040801051b0913060504020403060906180b 70
    0xc000003141d2a2103a5a136480e400229000b4690460500d1420b0140349600a400034070b080ca00007001c11072120920540e4400744401d41c007182d00300404200b81c0000910a60041c140d200d840e1020380100c03421003903840b800301b4030f551004413104804011f01080d4900f40c4142900074040100404010b00c4c0320764007034030501009041c00c2c403800031880b46140300745080d0064143d0010080c1642c0906c2d444500c40315185007140100d11403030324080c0c00034003401d00312411142066035540391000c1e60341c544141120112908031030a100c9610800c00d0707803015158140f808a40920646054080d0302200c000e02c00c91301c50043c01d03403510a011407501004500a00384084030a05a603c0100306003840d0300204000344100044015401e00325807401d004d01c07201102400554401100a1025440c1c140d00c0c015581140000765409540c108142e40691604a03009a00c1001405001c00c01554540002d41207070000d43c0195041334443e1001c070100074003440f4031541c9110244040d0900039445c2c40310440254 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 496907589 1250 496906339 496906349
    0x40c09270605101814060f0c1207150f1514030c0303031812270d240f050906060904080f0409060303080f190207020109051206180105060604 62
    0x11803030a0111903a8125001031018010140100d01000c1c00072800420900c0007464840c180c85402502103000495801901740703102000b0440c0d4242002031500c41d049600601c0521080d04c52400c0501c00459194040d140b41806511411403601e01030300b4500507034942e040601100b910b414005418042014907010a8a048440704012451110007007840e00181140c0190f25100210801840322086a22961011000c1054031030003543ca040c2d44025003c1c0b26106c0003440d400205c4a203140c0c0d101f003007082242000902e88580306800343c8400c0040d20819031010320b840d840480151452000f4080c2c0c9000c595001c0081129140c00f0200640321940640040d04c104071110100341404506001d031009005601c0316560359030764402c0084001d00e054401200072a0308940000c5a01182c2281d06205d4150000e0074040c80c400358016100960001c04100c2c14400310000200385a05c444003860607902401c2c00030102c90030855541201000541d030034551580c141000c03c4255200c04090350210350f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 496908839 1250 496907589 496907639
    0xf030b040906180c09020703081501170405010203070f140f03101707150302070c14030a0501020705010608011104060c0f1a0403080f0c04080c06160b070509040c09 72
    0x401208009005031059040c007401542c140007181d2103e41c0d00980d40c040140c0710320310001d0440d564184207000e0b4040c1c0d04014010402c0ba20000301d006140e2204d0220300b03241458120401542524190035050054405594903136001c410490720701c1d048642460389503103506115401c0c1d00c0502d84949036108042001c0d403154008004584401b003051511009022110b18285001204d402c030309540d4611481100700c605203150460500303d000b4421180c84640200c80b484100c3d003080044002c02d559922260382601c104104400400c030f00f07101505000b07108038008941079140189090a44441d0003015900101c02c1004215040d0072046400701964030042c01d0348a8800d904012802c500c005541e1001001640200410142d000d568188285030310140a00c01d43c8030006e540b07200703000b60700988c04c0702c2d84620300500030341c600203015010540c202c40004045203c0b0b07548041c01741d8002e4405101280b4040352290302841c10303000e0301410f01106e1504000040c03514100e5140d0110310f50360200e0709 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 496910089 1250 496908839 496908851
    0xb030124090e061906081c0e060a1d130c0e030105010f150305090705040c0e090c03010f260f07030506010b07120507060b041802090c07050307030f050408160501030f06060f03 77
    0x1011040d006900180310b84d005071020903541d002030034400c0d1f070032070b641c100080d841d90681e4070703d0706e0702405540004400750303aa46050888000c6040c880514588010790014040b56100203142003401055550388242d6111041d0903401401d01d4250ba1043e080f400103260420424004222107420012004446140104491311a000f403070382400030030381110f5000f90030100881c15498004055000001c010765100110741c6d00d00011644c6400280560303030007400340178400c01c00500910803607030859010009460205101000701171401d03076014031790460340e0440f0704208107114040c8502c2d4018140260354601d0b20070250b843c020340c443c001d4201d07420300601040c10b4090004583c8100b2030120068020410054184404006000056012841000901c0c0041c2e03c05001609682400703501c04001c1d42007140c42d641c02d40300707a020180c1d5601046001d0100052043c020007a14554040e4500c0c4207446900704400101074a01c0320b1540300c14103080c07200400609a10014003c40700c0c0441ca000113303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 496911339 1250 496910089 496910131
    0x18020306040b070e0904060204060f020703030f0f020c0603010311090f060f12030c010e010b10030e030a140d0f021e1204020913060e03030a1d1209040b030124090e06 73
    0xc00d160802990440540c1702000100304041d40204182c0b20142c0b581c2c1440d50141e181281d541940f408010000340b0510303442d14215004038828010748078180140c415210222010400c1d5402c243d006503051781d4507040b40d107505d0501000c02c030740046552003202c29610303140010444500b4482c0007540500080140c240400e041482546c82225000b4000d1184120a0450a018042583e0101d204404003003548201134040c0c440c500a801c00300c00518107042045401f95514044032101c40100d000130005200f00803000d101e40010781b030340464010b031551003000895041510010214040903820040400c60180490ba1541d201d54110b660300010b581c0c881040b0220340220400030b00540c100071a050b543c82000c805544554a12401080b040da5000e0380d042c640d42203014104202c1e00704142c05441c0c0c00440004108040001e00046505d400c5040030030308646a00c00c51301001d102c0384113102c0702c40074601c0782c017401000c000100f070241904030181152120805801c200c2030395240840c40d04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 496912589 1250 496911339 496911347
    0x7052d090c0403150507080601020c0a03060e0a023a0b0f0a020f0406020109110a060504090e03120f0411041b031d0f060f0702010219051b0d0507020418020306040b07 73
    0x2015542c00451300102d03c0003411494054481581d0120100b40110b00041007944001503100307100100902d480c60301891605c0707080003000c982c5a00c81e002e004284206001d030311402c480d00304880e40140040198038417039814070080303440c20180c000c0e030365400c0c00c00300080350420800c42e4004800c5450039400b034880402d540028480d41e405407507024004240010b0650b0194005040103000d1484040e1000381c85c0e04111100107203024004c0440d03414001400941080c1d4000300061621004480c0707040b521540901c0600030450713090001000f03060400c4200120048648813081c3c040d2410700162082000140c2400c41d280b8058040590350703603410015041160101c02e208a22006403221b01e11904245a01d8034022104621002d000d01e0104401901c14404c43c1c9440c0c8450341c010803c000030800c2129298070a624030321401c2068020f00e4850f03002400041e002030303c6903c806550301c0b0760344140801d8440c00542810911840000303400540c078045201d1390300c0b585c0400c0c2d4000c16510b80f40191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 496913839 1250 496912589 496912597
    0x40f0b0f0403023102210709030311070b19030c0c03050301090209060f18180601090303210f0c03140603070504110c010609050406053409090e07052d090c 68
    0xc0300800c001540007070b01311a00d900610500310a030100c0c00c0580b090f20004100e9000030b60740c01001078049a01000407a10070240035941001c00c405a9042c956a014038000d160890040c00e03c50180e083d52112915801d0b1049210f20600c60174107c403898090348026065000502c5007203c800d400080103150341d83e40c03500f1642c01c0e00602d0131854440c03040102c1c1c5005000c0403000b190007051614404d03141a07100c0b21405215417416074400d501241165000c50709650488400c1c4141500b01c4404401d5030801e010310307284100311400004901c010306400500350381d0040703841c6c1240e0301c0040501c2910345000c10ba003800e4a40c195030120f089816880107080d64402c0c035002c10111b504e00200403900c03040c1740e00418000e42c011082403000d42c50310003d6207000800d400410403258000d0800c0300362081c40b00c030842c081c814030381000b00f01d2a5540000f4420fa54603400944450381100070144a503180c810719028050007006070868041e10704036964620030f04808541ca116503131030000a4142840d030340c100e0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 496915089 1250 496913839 496913899
    0x10e040b180c0d0503070c0f030f15090f11010e190e040c030804030b070306050a050d06050a1d030301090e01020405011b020f06121509090c0d0f08030408040f0b0f040302 75
    0x40d05103194241021a120740200306d04039485c214030700001902c0001d002020050b070340c01c20710b05403440416544448400c00031440340c1714000c2d100d26040c400300f040f4410940c402401745060041c1034003201c000400000b503440d00c0503c5069419028030113554003107844000d4552010140400b503d89041c03c40b482c0c001644009d0180c007000a01000704076280032190b0081c007680c1c80501032180c9a104100700b00d61240666508803281c40024004940c07203800940e0802e40c0305000280401118016017051700110400682c241e10020040100400c1403040f0b5418032403a1000f14145800c1000003042c2c802e2441e1400407100e156590f22043d5640d054021718035942c0140a159074000c0c081d141e1081100460b407000035041d01104494040c1051842c403441149000c0c0507000a40d00c7c8030030040701800b903510907038406c001a130341d4000040b003a600031802503000d240c8142e00c492500541e007103401e107550000466018184800e50700703a141441031703e00f40c070741c11503122801969018a0b10141d1210720a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 496916339 1250 496915089 496915099
    0x1090209091b24042d0605030f19110a1101060f1710020301090b120a03020d2a060902030d020f1005090114010b041503090b04170d0f060905010e040b180c 68
    0x140998000141700e401c200c0445645c849109a014584440020703480b03400040b9604000281001c0392000301c541d8000003011540c0e4484095001c1c40c0c08850f1101c04480b18000005440c0c4c02698002046c4a40c500c011802400003a0410103451502440d038460b8003c2c0d054045003c0d0307055902804801e4008c000316608540300e6941c1c01a0a028100c940b400f45d0291110003183e035403003103010640340c201c19090b070003e00001c04031010490380c080625200004070308000b0102d041501e10f0321406080079004201c003040444840c0100750800d03090a4a102c150f46c8884405004180302140306000b400030700380d002440b580d86484503030260410484007030a80a0301e50011401c4c180ba0000b920907070380544480e40b140008480c041e811203180d80f001401c1c025482d00020002049401e41884026401484d1f80c00c100294043c03a069407415520100c62030b03207814040c40003081c0d0b48101401480d500700c1e07880d03007401c1c83d0700d802200308000b402e401241d81014600842d1400700701305c40c0d091030030003500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 496917589 1250 496916339 496916347
    0x120f06020313151415030c042405060a02060106180503060f100602010216200a09140a062301110f031e0405010f050705010b040e01090209091b24 64
    0x25185801c1e1000403011514102a950082c00c80b550501c03030200d052481a20190141e105c1d980e43c01111403115408541c1031141c02c010350300940b12401150142c0c01030041c402c81440e8941d0201c400c149907600118007504050050307403943ca038005052811291542440703040819489030308a280342580d0031041c1c06201d1201808808408850359500c2500100c58400c600c5449000407800d074404e4050075010045e83c0c00003403000c038101800404480175042008003028020101003008441c0b07990000e212190707034a03100703003130113020035044c2d0307480b04c10600308105903030130329011018400e01d8607001080742401d000d984903142d0040303907116031000d803244c21618140e0f02d44221030381e60f9204142c03010f07040f030244403220061555a01510b0075100d0503113400540307060038081201c0a40200341e00b95007640d2140039140080d1210311070b2501d80244e010001c5400b802c60b0043c08100c0c0700c05400540164448440e81c000303500c20b14400000c000c012101001584e44083c48000c0c100554040e9141d4010006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 496918839 1250 496917589 496917601
    0xe06010e06061309112701080a0c14030901060905090a050c0a03020603011806050604182009013f05060114030a0c0203040e2d04020102030301140103090507060302031504020c07120f060203 83
    0x1001b15111349000343c0c2e803511030395100b600130b10582c0c4003202d101003c910f1101917100c07541e41000c06180c0c015201800001c400381c0d07944844090301d206554a81c0c190300314a0400d400c1c09018404a14015000d43c4c10204907441c41c0c0c0411030503c8144034400301c03441c104c20746900c1c221241c0c00c0b1f407004120050456846680b240c072241481006066260601e0f0710b030845a0302e2140c80450403841000c2e4040e061030401603068015a40351000e001c20f10555640742d10f2441c0b1082c0030b0b080030140005084c2642074004c0e01121130341c0858002030038013414000101b41040c0c18280709000c0307a5200c0301400c40844c1040c80503000703078518003e80d00024002c4103440100030803c01a03054050540301c031960481c1000211050200415405036000780c0141c02c100010303c82d00c43d0180342c460a4480c185000078a0303c0e603545a417410441c0a811601c0001c1c2c002090007801010310603c0202c100302201c0c11454803090000140e503d059511454111481d405006402c0c08480b083e100354594101409561f00d107005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 496920089 1250 496918839 496918897
    0xb030f0f090118080d320c0c0d170a0e060402101b0b060f180a150b0a020106060206060406050d110102031c15120302210408010e06010e0606130911 65
    0x70b4034950185850320b0305501d0801d4186c8803100605840b070b041c030941c4148140c1030803660304000f06082040324040260030503c00080040c1c01c1990342540c2c4d02e400040d11440010100f440207080400300a0a06100100d0660003107a0300e90440d0341111065000502c0c4081600c0701060200c40c4514903584614960500c42c143c080b0a00c984c0c41121029100080c1390208480c0054020710400350b46903a0380025000d980c660301c00300a000c030002c907002407039a81c1d96404415078050022100184d4480e02b0800c00740d60100400740c0c20500c100e80611486090202185082841e210080c0c15085a91031000c020390080c402c40e10210300e41303072503012a2440c0040e4007000e001d00315210341e008400400001740088010f0035800c881c41e4183e0281000701e0403343c0300d1b1024039109400300c403142410030000560410034841c440300c0102c400058410341d89440440030054200034460b5000300c804110305003c100c882c1c452170303040c0c0d800b40100080c5644003c00f921070502880b2501d825030038251080300d03800d05407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 496921339 1250 496920089 496920097
    0x50f070f11120c070504050903040909051f0903020c041a0607080c0102040b130806010b0d020d380d020303120a020913020306030d1e030b010201150e0108070b030f0f09011808 77
    0x208903013074160f80c3e40500c01210b0080307c0009040e00180000c0c0050328468200c2540c45003c0c100f00c54200e21505203000c5010f07074170700641410315540e40c2020b042580521080b400c4c450b0455013004450784000c482c3c003090345203201043c416000019440d04000f003a8040e5100d48000a000b10740b100d40702c4039148402d43c0407000b5071960904100300002e20450009440d8144c4804181c500d04011911048070041d4000811105041e503d80010100e01c28030400c1d488441c100c0c0d0070300762211100d00003e0350a0405514280c2d4001d019112044000d80c5000040300c00382000c2c2c13101c802295541050740c000034042c1c20820756100d251708080308100f4030300d80c016601500013202528001d0207294400d03161103031480032140b800d0b400302e038101941600aa000030070300d1006000108508403025036458401d61150840a04900d00000511061178100418005400d95960031850f508000351551141c601c010404640858040b0000d2000382080d040983c900c0c1c06812119600840760be8540100d400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 496922589 1250 496921339 496921357
    0xa150e010314060f011401050c010f090b100608162307030203030709090207110603101703070606062105041103030c0705100c261c140604050f070f1112 67
    0x1207a0f50100d03c006030f030035600f0350403203420700745a0020304a0900107541c1a0007034840b60049558905404140141034014003038040c2c85031251030010f262925009030070300c0c0036400c05000c1041400c204003511750340401d508032101250410060100ea060400303414890403040c5011861000709001041540000c0594043d802c5620340782e202c0c6880d440c45400300e0191003005402041002c081070304a0600f01c000310f80056200c5001101d168032204172084031445041c150805a000207100342c140406840394402802c0c1c1d900c4c180c5048504103040320917081c829144dc100b0a83c0d210041410804248040e01a9042c0641074a468001845410341c94a51a104d154000e280c11540f884000e4402c902c200c20701a0b004601003201c54400990f850000910f11090b88a088100030080304030410b10000d5880d50040c002c0442c036403490121b540342d41c0c040605480d0140b418101400b90b06c541c656090b40e40b082c0c451902e00644c3c6001001114240602c0c4501800c0c0e0051001c4034400414110007048410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 496923839 1250 496922589 496922593
    0x201080105120a030324060207090506150d0b06091003051510050a03050903040306290d240b0a0603151a04180609020a030501060809060c030a150e010314 68
    0x680c1c0c54062240c80c591200b840c5a041d00241e0501001a0203913004c1d00f40c000b104040b6018034042202c0d00c418848841d003099000d44d0154004205401080c05020b07427085059407040c003140c59454511219000e60069003420329118031103803125845140550345040710081080444010003580a002004242c0e0514800d5041e5003903024181088904440000d90990382c0501c4c116a540d0200c0007000c0190a072100c5000812001010a0480c011440900c0d040c05504480703d81c1c64201441010b50224854014610b0396001c4000ca070744551142544051420341040c0c070584040b00030010306000c600b42e03601642010b80859900d615900000c869081d41c071400030035a031140d6200c0c0e141d4040b10601c40c41c40341c04003c1031001b440c0d400c0c06800c101c41240004907119456032504401ea070484c01104c0300003942c4030010452603a00480311500a10700700043c0c101c900704007100f6480ca12000302280403042d11103201800c400030070040c203001007401401c3d01202d941c484c07070030040c01c00d40f0842d2601c032b034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 496925089 1250 496923839 496923841
    0x21010f02040509280b040b060f04080d0906090e042402040f060c02090a0b010c0506041a0c1207030b0604050306040c03030206070807090612020408190507080a02131d03040603020304020108 83
    0x20344100032040500c0d50040d21312000400d200600a40504041050a03401580300c4122400648440025082c0d00d42d41c51030307103a1a5418078620a1800780c0d4035000204000700040c00300504c9800032010f4003520410900e1304105e13603450070080d800c1c070364200e072302e20b2984040740401c10703420104d81c09001a18043c50b01c0c0a541a40c5035000c54041010b078001a41c00301ca48404100d04403071550042e080c40c030301814680102005d03610b45074100b150850f8251640b0000100080480264815040c1d03c541008215404c0104001c440c40341410000c0c03000d010b05982e445110101d50fa44d4060340e0041c4001030440d611803500749000320f64114948000c0780503100d50400f042000f405070005c144101c0c1a0707034a000c14185400c03002c9608482c400298020250300300400701c0c001c10306000807000b00001654081e030901e42864a0b6242c8041c0d070b40000415000700d00d08100503600d20b00600c0c1c10380031154002c160744600760b0004c03003814070f940e80c08049440001000030309032350160083c0d0301c603c8c000d886100032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 496926339 1250 496925089 496925101
    0xf050301060b09091e070206010f0b040b0a08090712030909050a0203010b12060409080c1609151206060504090b0406060b03040209130f021c050708010c0e21010f02040509 75
    0xd840003402651603200c0c0c2440f0341c41142c1070920225030700226218200d0305580003c06010ba40c0002640d4003001038008a0041c403008a120f0f040c40010700c1014690381c6031a1030242024040c0c01000020301c100030142e000700300c0c2140204210300180a0140d41140d00107120715002c1c10805141c1f0811a01c2d50402c1c0008038080c8440c42035078100c0b03918018840c9440101d2100840280005007505c4d48076a80d83d4500c40458447e1006d01700714a0040010400740c010b05c111401d40e01003a60040d001c05040c065000783c400c0605000c0011591071031016040c1103410b00e8940c0c060125170300f20b160003074500140782d01800011403001d4051401800c0402400790bd40744d085250348012200a90810103040c04100c030380340081440b10046009254512140c50140d0000324050110400041c0132420b030403480043c071000348245401005000000c0002c000301c0000580b040c4c0050460034483c50104c000c1410b00801380050103140c0c46684020400d5240501c0390750000c1d01700b80210350250b4403140000311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 496927589 1250 496926339 496926341
    0x80102030402030a0206030901021312021e100e060712050306151809190e030309010f0917030619260607120e120f07141906050c0c10060f050301 64
    0x80640c2e00507014003054030603a002d000b007aa2001d04205450343d420403140c040803011400150182c1407100e60072050311081c0c01008040001d103502c1004401a0321022030f2940e55403c40c5904200042c14442c040030440740014005024506003c0d052024030940401e40c10b6004004501c10242220b0b040824070050f0340080d000c0c05551160b108034040c5001450311443c081c0800b80d81b121012444c4050020356504450941e004131a00c0c1c0020b0380080f060100b5001c0a0240c022991021581008000169102c0c40100300072003a20340125034000011035402c0c4c50352a001c10b155108041c030066a030341c1d503002040c00030255200344032540582c07080100440e040415000c2c000c0d80395688061480740a003c40720010550605415000d216104100b08902d08040c042e1165041c2c24506a03104d82007800e24071548040101003400a4003c4071a0700d001c1100c981125150383c0e004030f00060242e66144090341103100b8803846041c9803140c4a502038160045422110990302070764000c058080d81c52007418 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 496928839 1250 496927589 496927591
    0x11070515070507060f020c031201030624051036051818011e0605090a0b030a0b040c031e12050a0c060f1103040c03110108070c0b07230a0908010203 65
    0x6800502c2c02c02c8514040b0700540c001c2c2607440b00c45540145086130101c05180355a00142c40a40c120304c0c46c10041041c03001506c1151900310401080d8000800104225841500c4500416104001414201c154980305224540d208910060494841500019041d41c50301070031070070035240d0700301e81c00218007401d140721280c180d410095602d6207503480b005518102d01c80300c1181d5004540d81d681c460724110140c0ba01c401030007040b46000140745424202400021240100525005030030010f0301316680d1000035180314039a0700005803400948440c60804284006a8000361501c41c61980e00f40b0720382100b210742039019120303100a01c0d070154014030580341030085020103004960f64100403408910b060b00941d0081c026010002843e00111720900d40542041c0c0d402d40300e003000d0240c213100b000f203205500048280b090034000c840740740c0b40b41c00400c0710548000c0203003c0f06001c004140ca403405400c1600300900210310800205d0f4104041d9900d039048201040c0002c0c0134042d0004000340e040c8201d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 496930089 1250 496928839 496928851
    0xf120305030411030f0319080108010603050a020d0311070b1c06060815030a061d160806070521040302010209010909050103050309150d060603020a09141f09080111070515 75
    0x80d4150703a103a0f1200701040088a0005406000360590848030310000d100603c03808201100c00410ba03008014010581ca9058003c401c40b685403e20620202d2000201e60084a0741261104543d44243c541107079000f48550184840c2d00c510b900100d000020308021b81700a00540c0840c00c405441c5c1ca00d100709403903080c482d0310045845800803601035802c2445010200c0d0014048031203400c010b82d280000ca03111100035003544694203511000012083c0064030498407410700410300d19052400701501d5040160861042c064000b80410300c07445000350301030140c2c4010407005894070742400c010307010f1b5104460290000c0c0001501241c004014400c1c00c2c1a260004000c5040203600c1040c4070040010340950712002000b8000c1d440c000f1564001c42c40030740507940d009a01e4141d5402c0150840c1c0168100411080c01c0c0302501045440d03140a04d003101c1c00c400c940603031048002500342c802c400160030900965027000144107414143e04020301c00c3c10b2180049901071b1103003031411084c020040c0d0703603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 496931339 1250 496930089 496930097
    0x8030406260f0a0b06070816050606060408030405010e01030f1415061c110702030a12080a0b10030b060927010807030512090316060f030c03061802071e0c0f1203 71
    0x441c409812079030000c0003080c4c025240504e400110b0311042e1044c1c1203c5110000e81d0042030407482084002e1020540080c000c0e01d02c3c03030803e4101401d5a46900580c01364604128000c442c000503170b03110b0b410002d59024944010001c1c1407201c2d10031201508101c0c1d45103001021204900c0c6107050050484004410000e042c5031064041861000541150343d040340c11650b0611900000da6018402140418441e182c56a02c40c03002d008040c100d4003000b0440c1d01040c0c50070f100d199540c2c07030380703100720b02034543e6407500086585200c40051010f0140c0b038402a00240b9841414840401c040d00080c09100712a904090726a03031001402d40d1601c45010081c0310303800c00c3d03030b12840b0052100007402102e140202078030207442001c0014024810598071200006100528107c40590103104000d810612403506201c0a0f00f808604a18920f0150310099881c0d40002e07484244081004446025030320607402116001080c01d00e4041e4000c28011030600c04c506650014810740100030324030f0283c0d49a21 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 496932589 1250 496931339 496931341
    0xb0601180524040906060c050c0604050d0201080402031609021803060907030f060207023106050303041505091512011d04080a1704050f0705061303060209010908030406260f 76
    0x503118042d082d40c098074942c00180070109610440d401400060007150355081007103021030502d91b141c2203402c01403d0061000704000d21441d25842c12441d11300382c0a08205220303032107600c0401d2504040a14980c0c0a01c81c0d06008102407803540c0003403803452500c0ba15112070b81d95090030591030380802c6ea403a048270b1f4402030003000040d03035008804031503501a0000605148041d00818500303400c00e512154139000344440000d8840070700302d0b00d07140310f02141e0303042010904140209640c0c1c4114002c1c56510f808404002d0300b0740c2d104a044800c0403401030f003884403c0d050308402a003690050007401c03000c030300200000b003403803100544814202070f85c044e0007140c6130301c03503807a005c68980c4a0002f00e0100f1902c1032a4103000407001000c0c3e402948580300030a80410905025800d1402940000d8030071a42082000d454000072505402546c0e004800141d440c0c0d04480180c482003142d1f0b01c243c0350f90002090000714260080825126041100580c0c040c414520a0800d1341c0c05003201c1e14402044a81c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 496933839 1250 496932589 496932619
    0x81f020421080417070501081302011d0303070c030804050117090d0c02120105040309091811040c0306120b071209050312060a09020f0904140c0d0507050f070b06011805 74
    0x1c94400940100e25840c82c0545039000d0003114001c0500707400e40c0b5800340c03500300101d5920030b141c5a44000141d800581a000d1680001e1840c07010b00d900304688108801d8048a941e4188102c0d140c00f503000505040c01b0756a46001ca5180d0858442c41c2c0c003160603800352880010090180c144141809405400d01440426003618982d6400a0580c1c0041203d50310554409092041c10b0086000ba10780c2640e1602e000c800d001a00d0588010700d50391510380303040780d0001d10861007840c1014003c03503010074142e1840804600030030303266200d440a529410800700038450b205440354040d81039079403a03c0c280203030010392106a50003800024420381c03042040c1d01c02c1c0307010301980342d070007100003040c0540e082e81e5031900c10160b801100380e104480d000022501c2807450244140024184e10400750708403483e0a100030411401a040d1618046480d9030000d00154414822070b02414200310080c0d4030f07040641014480b9420407101c1c0c42c00710b483e4580307200c01141c4500440341154001040d00ea40c60b20b0503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 496935089 1250 496933839 496933889
    0x303201303030c1712100b0a0504090203090a05060115020d1d0108070e22050603150f25030c021b090703020a0903150c020601061106130318081f0204 66
    0xa01040e0b54141c1002c50201c5442c50341d90092816000701d07800c0c02079504000c9070115500703501f45d000d440026010050b42c0300c460707080000e4130b041b40c0c407241c030041e01c0f0754596503068100008501e00512500440f400812643d03841031545903003800e66404c4820011004e0000c0da820a030041291111003400464807003550f100302e5505a0040d010725000b500407a591000c2115601c06225481c1c41c043e800c003005564480d248501c1c3e07030102c0110000c0c9414554041d088156400241107071000c0307960303180000d41090101800c1c002e90030940420320040d80501000900804002d07541d10018001d041c40500405030004066241000040405043d0780f10400d00394025400300c40e2350400e0041244000002c51400d05080a00010401d004902c126080100900380201608a54144000c48006c40211a0001503403030703215404141055078920141026240b11401e2000d4600e09081d5500100ba0020b01140d00c2594022400c0071224bc960502e900c134050380124095842442d480c0400c0384c03104181 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 496936339 1250 496935089 496935107
    0x907031e050415020f090301091212050c0a2303100e01060314180c0603010f0e0c030411010518060310060e15220e0901052205030307030b1c030320130303 68
    0x141c1ca101078035101041b0b000c02c0c25100d0002c01501d00c01450005050803d410004651011210007400c00030b510b481441d5441d0303809094984002c001004818030701e8030b00c90320203800840c0466203031940c503440c0100d84c160800c03420340660801128413200026030076000f4022000b06c11000d4000d00c0d2507580e030a0595604c03007070004100c01c052041c0102182a601c076000118081c0c298203d6241c5200d007010484044001c1c040c1c8500c0c03190504104003c0414150070022550040034038000340d68400d0181c0c0c9421500020030300540c0b1460000911402d1100f11011108036000f589030782c20139040d100208032a4040021800038074110800c242c10001c6e50396138071080680d01052003000541d4588480203080c40044481e0900c1c1d039507400c10700c4007041c0402c0a40704200c1103100005007040440d9607503516808041c4c400f0080c10380310081710301c4130303640d50354070307441001c50880300041040716810000c000d0201e803800480190b402d80a00942901070f00704845990741d6808912841e145503540845030541c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 496937589 1250 496936339 496936357
    0x1a0d0c09060311100f0207030b0405031306050a03050903040501091e0e040b0708061009030b07120f02071a010b120c090901031a100e0c0702030c0907031e05041502 72
    0x8000000030a51042a208100185000307080d541000301c120001c1c0035000c000d41c020a41130020092129118544c0001c501040c0c03070b4803000c056869112441c109145010700b41150828050b49580800c031140d016015140422066800307020b19202e19400940340d1150b03000b45800030f901e02d1402d210450842d00d100e03440e41080c28400d881d41d5918180c00740000002d0b00d0895120102c81c0502003a04c0c1d0011075260400c00880712143c007080100d40241c440c1d450b03880010000f10007a80011541c82c09010020f4880e1043c40040c000704500c0071854000354442d010448180c60440313689150040c0e9070b0106c505807101e40085616080c4c07441d0320b04500441c0108100c803411010020910316803280da000c18002d51084580c1c00d0340c000e038000c000c1c0b50818000c22440d4048440b1000300600c000504030107811004ea007000300e54582250003c6800e00c03c81c00085a045107042092100141d03059102115a240d40c80062074142c0c0c41c0a0010107a40090f10301070a2000420500c441803070040d4003c03c0c8001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 496938839 1250 496937589 496937603
    0x211107050f0d060207032001060602100c111f110c43090c020309030d03051816050a05100212090402070f0f2015090102010603051c0e041a0d 62
    0xa40b040d0740d000140d82c0010011800601e00c0101c420618529021b1000c1c0100100c0003070000c5410310000950390004800c00c0301307406481d2050502840c1c0140c15442c6848021000e03110380e4814502c404400703001035403d030598035140042e0b41201745401b0702030350400552030001d1324500740d580d800078003c40300d5507a034000042404a400080d1700000c102045040340c5851041114515001c9800704850340000c3e58000e5400401003440903580c0421550700c038020780c0c18000f8054a41c2c1350075000c5c00381130384001d10791881080e040d6101c1e20300d18003c840031610308680e4180707011340713032070600c080c84441d03154100240e07014003440c5042d034500c2c0001c4c1008542c09000181064600d8640070304412a4901c241c80203107102c619403081c0140c0301d209001c4102d0350600c1d841000d8000011440300c0710f5000c404030300f921010070092030681c800e41040c0006c607007010480c3c2494010a041c009203500c204c4010010840c0080ca00c100e500b40b501030f41c0201c55500313460f001450b42d00420300c0003448030108100c03450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 496940089 1250 496938839 496938859
    0x200d0503010302130b0604060e03100908120a0b120a0c060c0201020706050c0a020616020907080c07150e060f0f0604110f1602130c0306050d08030103030c05070909211107050f 77
    0x158580d10047c000600c138641e1802d0003048003105050401c0c4181c0e01d00402c2e142401804804502440c2c00c43d1090705074030b01210050783d0b074000c403134005001b41c00450764850807002c0c0401c0f030180006400c00300345000b000d2200d000341d0b9816042d0b038200542c00001303001d41c000040070021140a0000b512001da03008094a1484405034009081a4000d21803140740c084155040800e600300b2121450f440103180c1030401d014181945580128092044010900c090011030040054215005118045c0d0700f0700c01c0342c2c440d0500040e441d201e83c8046480c00c000204480000c0d05a281ca400340f60030f0000d8080c103803890f080000c4614002980890704105043c110882400c0042e203a0300c4506030ba0000d44040041d405800003401419070b805c2d640b04a21a5032403c1d148804203407401c0450f41120352608105d44084c01030321f0b106050100c16407054207000d10305040c072420f0054003c420081007091480f02560072842400989800040c0c0249000b103601008080c801810440c2640408040061011140e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 496941339 1250 496940089 496940111
    0xa080c070c050a0f061e0504120302030921101404030c0206070f150e030c060105300703111906050c01020403060e0c042304030e040b060307200d050301030213 70
    0x40100c85a01040700040f14180c20044541d0149080101d060384801e45806c590400030024560301440c041e15010b0700c1c51800040c01c040c0200225007000c000030b802200003a0684100c0c0c0308074851030302c00dc211805004024003560b04544030b18040f466074103a04000710348480e1011242c21035884012a0010310070000c050204144412403a40383c1e20500c0088005c030140c40c140c1c8142e507256a081130003035200b0300c09142040710104880707040d1441a2a00740d441000608001c0095020715400c1e007507001d4242800b41d4101c5c0c00304200003540c0c0241802d0f201035501d0428040742d03250758071070842880c480c0241448502e12441c000c029000d48980090704040d12034075a102154003941020b40d0030b40c010a03078080942441e00500c10000c0d00c408230f0401e4900028038011140e90010310007401c00918000c0f00c42d040e03807140e000304012139001d003031142c0342c2c42d0204015012154041c1c42c8542c0003041880e51a042c20001150300c0c4100d0b051380c0740c0382941d20f103038280546802ca0588a54035680c075400c038410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 496942446 1107 496941339 496941349
    0xa0603240e070e0f15060403031107170a0f17221710020a0311040612060506090a12080409091a250e120706050417030a080c070c05 58
    0xc1c0103039602010050705e806a210385641c4807901260200905074401450149150000112103581c1e441d44a03801c0000d6080315440d02c164003080048000848503102d85060501c00c0069a0000302890218000c54020084c040e10000c0c0b20103001321a0014140c8890040c60032010160303800300c0040b1410340740d0590220402020b6000550142d00342d1290780314aa43d0400a02d02c0c42d1901d0701e03604001d1450780c0400000c10281d0800d0b5000c1a03501e0b01504030f50481c0c400520000c00d41d85041d004000808107d5000d461941060000183c0c80398180103030380c02c01e40705001d89440c12117a060742980782130025066291903000014615103014841d0303400c0001d96100d0402001464408000a0895035001c1545640d07005a510004625403c1005070045d1100e404110f108036211218850380c0380140e0762140001201d517800725642c0451400245001d500139081441c1043c1c0f203002207030f = true := by decide +kernel

theorem cover : BRFrame.Cov 496762589 496942446 := by
  have h0 := BRFrame.cov_init 496762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 496762589 ≤ n) (h2 : n < 496942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
