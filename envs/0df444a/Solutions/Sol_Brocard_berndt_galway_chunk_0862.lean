-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0862
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:14:05.650296+00:00
-- url     : https://prove2.me/submissions/a0d6462a-9e56-49e7-a241-5903d051bc42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 154856115 ≤ n < 155035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 154857365 1250 154856115 154856123
    0xd06030201030b030321091f051f080706050a1e170a0212160c0c080601031a010e070e13110d05060a06020a0b04050a1e05010e01110403060b06040e040b04 68
    0x200d801c20381c0c0d0515031a48140003500f4484440b6040c0000c19240d035403880d0750000c10920850f0940001c4450300c41023400541c3e55111515250300c140907a480f00344007105d2038807a040d81c52641d1603251144050b681e130018418803090201c08100b145550f8010f6800c41c84014509240b60002c038000a001001d4900405445c400c1d03031b021201042034203a0601c03c0c1c034070344800c1c0e5030b81d15400c2e103e419030107080c81241300484042000d00c00187c400280101c01e04401420b005000b0300c2d4950451078892600e00c9207504285030490351310b00401c071505a81103415044481410700d890280c1c03004011030704100c050329a0107081824211500301c81d0807010001d0800040841040101340c49480c10004816880d1080000692004807080c1c003040040c494140c01c00c0c490360072118440415550003c0b0201c0107000164004900c0c2da01e041400070a0041c220b001d14076000800c2420b1800d10b40070118041c9003c0544229500c80c501410f58032618210340103400320401c4a0300c185807034a040010104100d804035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 154858615 1250 154857365 154857371
    0xa03030c060608060910020d060504060e04030905010509010915200708160b040e1003020d06020705010c1806050f070510021b0309060a2f010c0e0102120703080408040b0d0603020103 80
    0x3407a0b010100f07110340650962409401100f1b40048540003030340003100c100c581c195941d900021155112f03c6040010304180e24051030514090070701400e031440ca0361100703044c05810032400c22a60f0388284064151001d5203400c55a0b00580311040b40c0e1004c0f50300c8070444044840f1703440b06c000a80000d260049500399411511341034015018442c080c2d40300e00c80c600010714244001d10801c82420090380d0700070001c03100c06540654a4000480400b01c5440c1610525800034002040c018207003d01602005c0906100080d20b88180c030701c10204c0c1041c45048200500440e8410004080c031080b03448440c4c11508950110310b2925a481c000e62040083d15240c1d60750752001c641e41880030003038490480300103050605240780c201080c0d82c52140070b103c0140c4800080f85525400440c0301c0c18103004800c46c00009180c20318404060032000e5000c61060555002d000d01444624a110031207680940c5480e00c9032841d210752508a42030700a0743c0181a0424010130a00a400394590003001100e000740e03401c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 154859865 1250 154858615 154858619
    0x8010605150406030e03070503040b04330e130203090c0307060809060114010504120c0f0801020c0c0d020301150303020309090c090d0f1704030308160906080a15050a03030c0606 78
    0x410510054600181c000405200c00c10006000c3d41c00b0140d10800481903034901841070b45c0e86411540302d90085041c524011900784000c101800002080e850318440599401401c11042c1a0300300c0081a01d408105401d016a44140ca4800c107120a5500d40c00341135442e802c01c0d1010355200d80c410785c9070314002c0c0720320000001c4130307442806d000740a09080d0026040720390a040c0810311205070520200d050040c2000b00040c400e1001d4030150099028616070700c07e02e4107010301e00007490a070364031281550380148100740010f40003003800c10030740104494541c80505a0b1000c40e014001d9010301143c070140710040001490340100c02400710210131140410b4503502c60505d070880e4024800300980060b6841010f1001480055860507558043c0302c0d074118120b01012140807940c4140c000710000349024081c01281d0500902e50941c402ca1800e00100c0d05060140c0284444801884904081c0d121418a01205d1150443c04094180907180303000d0151039080190010403031200880700c02e4601500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 154861115 1250 154859865 154859869
    0x1f0b04082a12010b180c040e04050c06070602090a060203091005070212031201170a03170a0f0507050403020109050405010311010c06060503030f03091c0f050f040f03060903080f06010503040206031306050a0608010605 95
    0x401071042c0502410141003a040a552084023280107000725402e22680d000075030729549210141241500c1451301603941c00d03002c014012080c0c016405602958401d0005c01400d1f680c840e46001c0100d82ca00c3c04640f181021300000e580e045281362640350900000036035034074000003440b22605a4905491050f000d4010741c108540c3da114100340038000070700203020a070a508200e40c440f9088407a0340004100c0004210300c04044074800e80d200b2000c100c0c002010000c55811043d10001040212004c10140d895601c408048003408132001c3c0c1004900000c0108018040e80f00002034031010b0116034480210402900c45944103803403d252500ca10340d0300c4039001030402100c040c5c94065a5035004107503440304007078405410142c080c1072981028800418402d0f1a0b01500740258022400812240c0c02410080c0030302801401c0c0a011810b0400ac00c5120b0360480c0403240c0059058410992301e07960f5849001c58480f1244005140c01d040400788070051425070404019180c00d00001c100103550340e81 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 154862365 1250 154861115 154861159
    0x10207031407020a060503070e1e030d0302311707031130010f050c070317070c020d0305090924240904090b1f0b04082a12010b 56
    0x30000390f00c0428a81d01788805845480a550045454104600041066400a4500a00e880210b003c02d500805246190300d0100040599565181011072070007000c401f081c5034140300703100c1800321603105e03014450340002c0c20b0382c03494010400d0001e09002c480800b11050b0301d07220148026160100300d04408036032460080d148403042200c0701e0104003840c40c18804940c080f10b00344400310195586200d1076404d0800d5000e49032041081001044da00c0000b4a0080c281600012602e03e080207500100403031560801071403111035404949080c1c4040e0245001c8030644144210690045000b0061060282c3e0b40c00b4403400c103000741c0800240b00b4160806101e0310781000d060703150460382ca2102003203010b42d002c0028058244060008a0b0004050300e4071809000300b0b89000c200100c8070350041c0b0498110b500d10318054815104200d05d0140780c80315040c1d4038403214010f07c1550310000060400140303030b5026080d070307644094074411003684411403131402080c3c4d0304405030044480c08541c0704043e183c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 154863615 1250 154862365 154862377
    0xa14100e01120902040618050118020703080c0309010225030f14040302090606160318060c0c180b040507030c0210060302012a020303030f06011d060d15170102070314 73
    0x39448040700110741e00d808020b00003c40302a03810a940303900c04904400444082c124071024000c0115507545001030000e03015400342c000c41e0080e4810312001c40000da01403201604403040c003d2036a107c0e1603040c0340b00c1c02442008210300441045444052446403a0108000c0c06800780d21051007001d01c6410940fa00f40b1201d440900c1351500704402c1c4018500300d1540c07034024401030005410400300c2d0440d680400300b83d40c010381c0403e0100300b20745074140164607804d014040c00d02e41200d06000313543c0d81c8490709290f80580501e003801d03100a2051205c00e0f078000d40c040c030802030080c03003941052600540101612070345071006000c0e200c0801350188160003a4021254103945901440b02660070301035070440d0084a45100c1c030103601400016036802c00c069030041000034048200d034149030340051700c40c4500b82004445003030410505650b03070b03943c4401d55400c071a0420003c070301e11502c4c00300e00129550303640001704a24008544010300001c15406010f5040c8251903030004030011200039034481c0180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 154864865 1250 154863615 154863617
    0x90e090f1c03020408060702070509130b1602030d06060809010f060b07111906030b1e130c0c1401050708060303030114060d090f050a0303050612071505090a14100e01 73
    0xc11148180c0705400e906403804422145001400d00d074454441e00d0400c41c040e02d00e00c006038007802c414091031408014150300040b14400000000f2030940d511105400000c0c03010219010380c1c1f0040b00803c1c021f00c2120303202c644c07142003080915210b42002e01103001c141d882010641c64118007110860107407060340e0940f03420342c1c503d41c10458503075118a18404150300440c1c010b00c0101c8414038102400c4429400761299071804a00b240c040d50900121003040102503d01c103006a8244c2c00c161030341403100c16060480440450024a152800d0303c2c654030340c0b1402402e14030942d0600d1861101903101c41e0155080707949040264440008050b0f60f404203008514807400c0c0a0503e826138503088004090a244106000c54481c80b0364031001c2e031161f50070f03c054406400c0950300004041d45407050740e038080d004984003411440c500404035600c81d000e00854505a802e614002103a50150050702c10360709000b00545000f640f40c5400000c0442d4544105025042543d07118402c14000c4550303903071610b41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 154866115 1250 154864865 154864873
    0x70e0906060d0e1603021c02010503130c1706090c0d0312050403021e03070b07020102031909060b0402030c040303030c0f050d0c0c02100302120f0402030a0b040501140106090e090f 79
    0x141010014103901c42c80626851560350703902d0050114062104200d820200140c4081c040c5c03540c0103001c6401281c1d0800301950301c03144000300040c0c1c2c101c070135207401030b0045050130720099851520001d29891b64011611170301c011110100969000110244902c2c540400e844030741c20381070709120390303242461030040128000e000c10380d0084603141d00065025020344100c407040500300901031904401e0003840c011907000040c407030050101c008100c40d003040b41072000314654039068015810341c6800304100d5040b0390b103c0590106120b12030f08041c0348820000c008540e00d0070602d2408040e0703130042c40b045020a0034421101d040d68003c80e15445210040d8952601d407406162041004000444000050003c0380304200301507103408041d0b451002081d100165140c04071900302282171002458980c83c10203001c1000011384001c82c00e01c0b002a4400c003500c030b15441c1c0d464130794003404056034564004a030080c00011683c5d07000c44600211287d98608003104c0c2c840104840c0c482e40d21406070f05850340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 154867365 1250 154866115 154866121
    0x3031514060705070321030515060306040228081b0c0a0305090301090b010603020a020709090203121c020c0303240901050f13090c0e0c070c060e011b060504030305070e09 75
    0x2400320050914910070410344e54015160741d14454078680180b25030302c10f480c0c2c402d01c11204076010301c00c241c0c10403c0c03881c0103030030044241c1c0000c0c014403004201030b00898020800808100380c031041400c8030044225014903411403200020840e007021240b61948252030100070f00c2d000b03c40802c440460144c2c6000d0031503071110340c4050b00c0307580c450441103400d903581b80e204202064482c000d13107001e8003643da000359441120003030003441c2030f0454015280d0306181544071001a9070002e00304000f150b0320691075448070504c0c038003122450b40400084031124000100300c51281e5000c03006611070540c0101900003007a0a0320601051710b252804290448405001813009150105036282c0380c00004190002e640390300415a41594040300d012103108600800c103018200816041c00e84c411701c2c01c08010f040410070348070b107224050741d0f200d03060902c07601103021029640300310010386c2040c0e03266424002050141c600301c001040102c0e012f5001030b02d0100072a038581d10424002403241002000401c41e51 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 154868615 1250 154867365 154867369
    0x2214011404030609050d02010f0e03190504080610080d050a0e13290f0907050a0503190603030c110f0d02060d14011707082a01230703031514 62
    0x456a100c10354240c5009000c00000544680116031200e4442d070054441c1c0c40c5e00b000c019082d1200420748038601c504021800300c1440000041d1440009004c090b48080c1580c1e041c2030728541b040d03821140c0e503030140808002980d440307100b0722421110100100c0b1501508030b501141c05014070000003001130319040070700300c1b1442e009200b4140c14140c2c030f10009900220952002424010901c40a0039410f00d243d2030800d86400388103901d46900661320400c4514104034010000d2059495035003d01c10044082100d41c1d1304040c0d03219200907844000c00034030340c90b818040c00384090036000321000807900c040c2405500700000e00700d103d414084c1161101724455801c104c80c9400068840c560700340d6503000303205d40c98004000d02d402054034508000a00c03015400c85414000140c00441c240c2d48204a00c506582030901382010250307250304201080c0c0c40c000c0048279401c60051100d0b11840070024070700060407002c0002e2510078401c5d01c0410100b4140261200c905e0310070322501e072581400d100c048481d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 154869865 1250 154868615 154868627
    0x2d0b0f0901090503012d02030f040b1302130222030203070512010920130209032a091501030b010c08031303090803121501030b0325031403221401 64
    0x144050519580c490b8030381d00840c0c04c460071180d81041c0d10940000310f0f40c0701b03400651240c2a406115105520f5490400d44051003440c024000074050307042480011070035056800d101c06165401031078000345541c58003414010b0b4110010784002a003007030300c0b1000f00020b44050303001181d40c054090900c03d8a0b10f0108505244400600a41c1d95261161440050040b1805c05100c03210107503501c08004145050005400e02d000c03580c50410710400c04110243d400007400c03015154128580d40550740043c5258080b0442049165084164401400548107004480400e521401e0303a08003c03208500004407001c0740e01c03220103400783c04d0820214074004000c0c0950a0b034280a0300b024100c09070b59800341807541e4030400e038628000d8120401e001c14809841000c0c05001030910381800000034200010ba2600342084210b84613041c4910741e02502490305155000450700991440b6240002454503a280d500031052051051648080c4580030300b0b4102010080e11111881595880034100041d100b03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 154871115 1250 154869865 154869877
    0x71e0908010e0f0c010c0309030b06120105040605010503060c0703090e100b0c031314030309040c02010e1009050c030a0302070e041a0901090c0b0a1b0609020a2d0b0f 73
    0x42001800011a80580900480c2d048010100080604020b01000181030003070080300c0c0c9040000360207250000ca0740c041b400d4010b9076040404043c0580715000000e81002211040d03c2142d401c0108100c1031140590206048440a600744c0348141d4800c06c41080030b2059800c010f01244245409011510074400d0f40348d4031846044d10f00100d192204108140c507000440c882c2c181d0b03480020201004148108000020120380816414141003900004d80364003401c451180030b0b03030380e620307208803058801d4001940034440b0754181c03001541c1e03e402d8500035000c0004181c881e0b100c1c030014202181000200c51800a4066020b0800e8a061111004105202800a0310240340c0c00c082c2d00d0b01d41030515003d0740100041c400010b00c031400c9140c03503007440006034080042c250081c009204050381100c031354407050b0074240f00403561b8802884d1900c010088180040d400000c8101c01042c07848075401c0d480c03054000f00082108034140c3c1c0c01c1001c84070300d0600882e040c0107800d00c030300d81d1458101009410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 154872365 1250 154871115 154871117
    0x106020d0813141b01050f07110102070906080c031c200c060307090608060d02060405041805030415120b01020703022e0e01030606050702150304021c05100605030105071e 75
    0x9410406440300308406251034920710f0141c0141100100d0080381e12130f80728000600703090041c203000442007201c1490007a810081c001c1400980f40328110381c1709001d10300107040340345409c0000d940c940c00030640d5081c2030120729000c0c0c41030f1080d030a00c000a02084041010032603a45203880410b4998151b41c0b9a5500c808811510600c030070030703880380d6444018503c00c5c0b10075500d2501562500400400c0d0740b1019088034044c034103060304000940c072034404550035540c007500c0106080c18181c0c0c0e42011000c41c114040d0242c08082000b2480d952400160250403006036034801c0640900c82444003120b030742c4c00c1d490740560f100d010208014208100440682d0344074400050303240d040a03c4200003945400c0f80c903070004501d01c407030811070f6070180b1804020b040c10345401401d00d000c0364085441d10320040d00400c00c3c6400403000030210340da41244521340e400c01880b86060040c091408581c0c0b000507a00b6801c00381d060440218013810144a41d0384105210b03038882c0c10f1b01000002d15814401c01184000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 154873615 1250 154872365 154872391
    0x91506160308060120060403051606090f03030507080c090f0f03030c010518010212061302041211010e0402030402030c0409060f14060901060905010c030f21051e0106020d08 76
    0x10440c011018090015000341c550281d40d02d4200001020000c40c00b065203001865103128a500d00c10005030507a01c41d40c50709007596500d1082e8030180926060359070042c085410407006004000000750340ca90b0743c0c1d110352000d000940303544109880280b022a214080c480040c0402e0b4120f2410585102942902a01c00096000140b0109056600403480075016030f4545061040341800004240410060300b0021410103445c1018411000d8014001c540700d2043e421101944418a0303044600500c124a403035801c48065103405411801a9103009000c10362144943d411400d29008403032142e6030003000b41501d190707081d080000824410381c05981c4103a0301c04600050b21858400e0410341410307403112000c82e150a034100503030040160014010130488031406c0040e42d0300141c2008401e039050910a000302c81d0488111850b0145007018600b200111030180e070140510341c403540c02215820a84e0071260b04401c40042c3c0c0290038801d050040e0300c010b045100c098880d1500e11341001d0541013075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 154874865 1250 154873615 154873627
    0x601051f0e060d02070201090b0a050a0804080c031b1621030908010c0306091b02061b070611030115020d02250902030109020a080a0902030d03020a030e0a1b0e06091506 74
    0x2242c00c0d60000d1494203445a800542c08041d503070070075603501c02440611845443c0c000000360080141c00f9008039041442284400700303042140102c243d9041d404044100e0703864550900c1620200303080041100f0785030080210111030800e00b18101001d892542e400c4881443c0058001000b03120854000c0e02044040711000c40c81a00c00c0c040c42a104a4994000c101e081c10285560704076100c0034454088a98111341e881d14440c1c01060459000750207844050071101c3d000041030300b5210750342000301300601e030082c0d44040021700006941070380c2c40d02040c2c4020342c1c080c40c000d9a50308858000c0d0740142e4003a50440140001003400c004c804254141c08402a40d52006034000340e030402e03001941020307004a0113030380807a0b00c4803440750700c01d074a00014445180c1e15004642c0701c0d400044094201038001824014290003038200c891110f0f941070443d4221609428540110f0030f01d51601155003844007000155070104100a600895005040518035190040003103005030014050f20340205080c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 154876115 1250 154874865 154874869
    0x303071101030b101d090402100e1210060f0506120f090703020409200306070503040f02010c0203160501021e1903031503080403051603151a100504080607020601051f0e 74
    0x7404c151214503841e44e103070062188011405a20f4038684190142c81c0c45001c000143e5189006000071a13010b00b045c03d01741c1111070220742603600c40810541d41c0e20500495800e0000e842e440001101d22176040075000796110307400c0180512805400e119041c001c0c0001c039503100003411070540c100d00440b0031101c82c2640c9902050907500008401c1e284042e80e55000d03d0740d0300000d0101402c42c9000c501810440c54024000f81c2540800b07400984541410401385046900556007010101d0b0002d0458520301c01510618070b90410700c3c000c1c1030040c01000f10910109400c00c2c1f541101c0c00e00d0b88041c1c1180d03000480c0502007805141800d03420180c031150141056665408440099809074815559407402c5003802c5180600398513501d4000c094410040002c02e9041500f059172034110b00d001308040415100c05610540c281701c600e648980b42d0250a040c55070400010000c4500c04010345480d41d07548802030362030310000d105058125445480c0c40150b5018005004850300041c10101110041480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 154877365 1250 154876115 154876129
    0x706050c0c0a08090a0f03121d0402030115032f0d06030b0106020a1703010e04020405040606030819030f0e0d11030f041d060d03140c0a17071a060303071101030b 71
    0x1002c0c0c648050000d2401007500782101d40d00050041b15003445031440c99a9170320001c2d1034184600400700404920354400c01c0200f0303c00504546401031081d500d95846180644010b040c0d0044240820301c1c0c0100145104040c2580c04014111155072003807800d1980e10640c03a0394041d45d01d402100350755000100009100c140720a010b88030f19801071503443c9141c54000d080098504c072a08490360140300400810300e405172180d40c0701e40d0503107001c9510380329807034503c1c094a5a900010800d800104003102c4241000304484800046030390b00303000f00d554801c4044122445007094900d20342181050002d520b0141c166a907444100400302c80c544440e0100e001440d4200c1c0c2c1050090403002c0002c0c0c0401d038254245150072000407500841c0c0049c040d9406800c514254110303600b04407001c0b411a000450a00c081001e503904030710070f5650102c0c3c107a00310706640d1100900b03c401c07040c84051603d116034104225441104060021454010585c80d548011815a07003c18101a101c0c0390908603500d8541e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 154878615 1250 154877365 154877383
    0x50c03010e0d080112050c04020a0201020c07090f0609110f0a0507200103060e0906150102070806040812280207110d06050403090b0f0904020f04120f021e0102030706050c0c 76
    0x8800307000c0004500d00000c01e070f014107038808102600c80401c0718002c1003010400c4840310204440040c1e40d007600302c034282d029004a0600114030300520b0f40000e403880c800c3d080061403101c40b060400c000754481e80e10208950300b0101e8210781f81c802340074100d40d6941c1e40e0000d2120840e2810a142012503d03a2031a1030b00c0042e440d0b00001e11410800603c140d601802100c01410101c2c0b034850482c03074403a14031981c8250082c1400306200c907040c0c0a0005900030f000e9000501800b2080d1b074100d14003420080c0841c0d12030054500700f9a00f150000b0700c1c0724540d070100800c003403266188804800e401c150000194000040640e054445101f08408a83d01d02e000113151078481c0740c01203140d10f810f0402420052456101c0b40e000b00041210100e0600d9210407548114421180161905550308a50300240599004015000303c1c55102030284108860307000c155038400c4a030007416401a03440c0715420b00350030b110540580d02c180131980018180ba00101e40c005c01801c807403400c1911541e292441c000c0e0030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 154879865 1250 154878615 154878641
    0x711130e0f0102070b1806070e120d0918060807030b09120c0f0c0f06091302040b03040c0320331c060506031e0705040b0a090801140105060412050c0301 67
    0x503800c0800403070304005d0350300c03699078008021300003268814103488200007042c5c0810040c0364080c841013951419880000d48100d5821100da00311094409421140d4134090301400189044141240840074000e08003a0b50300080a031201da4034564600c03040581c054409100e0780074101400220000803c0600105040d100082038000c0c06641c0803410030000403030383c5029207908001e00000d82c40d22000c075100c8050958090126140d03604041c00240126004005590000414003060101c014001010f0320f0003900314030314800715240c0300c03940c10a943c001c007904003058191007161005003000f100c440c021100030001242d40c40b4101d5901e41e07842000c0c01c482d0010203140303040782c00d01188190001385c0030680320980b0b14140b55018042c54882c9080f42920401d4a10010b408588038409460040c02c0d412200c07a21039104007000b415a100c980031300c01d00c81d0b19069803660025440c42e06503040f541d020307122a180c507042003400b0b00f4410800105951504c161400707011152002d101e425000540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 154881115 1250 154879865 154879867
    0x2070837030204170607090b07140708031c2a03020d0606050c0f0604020d0809010c0f03030f0506010305131203021c0905070812040e100902031005040507050711130e0f0102 76
    0x1000b0303603022400603d40c44d0901551000301000446600803412030150f0b0080b90f42c0c0c603203600d40e40c80c09125200c20000320001c43d004010b4000f0340000000090700e0780102d00e008000c440d9481044442c21249080d42041c00300321241e0070044140245000603010070074031315000d850501f01c0e005408c240c1d0195400380300003c400003203400072220148404100b01c41084080c0070b96080540002d48110203030140505114000a4819034581c0036460200e60302d42d00600c01a640031135420040c0003000b507502c02c100002e042030f00048042d0710034854140310300e0041107400000c180070740f504044140ac8c68081c8050540c20003c0c02c010400e80d04402680174040d48010071002c241c1d20340700341840a940e000a503981c1c000e13810080100d06a400341da040e1003070202c000016a480010310715201c81c1952269404502c0003062240e84401105d00070182e0b82c085d5421300007501c4607002210780f031007006d03000381801407801c00130080e1b407401c407501103200091410013217149120b40c081c450034103408000303605031694 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 154882365 1250 154881115 154881119
    0xc06070c06260f07120b0d170c12030402041505220e030d0f06050d08040e04080712020c01021c09031103030910020a0308130209060105160c090b0f030102070837030204 74
    0x740c444c1c01750280d256008428000d420009001c502038048101d8000d0400e000300040307100c141905d20079201c40394000400c68510480751704003400254401d440903070140f400d004020484611640c00001250800740c2050030400070807e030050280301c034140503180691140e20b081051401040508980341c2d00c1a0001030004240c400442100c1c050fa00041c060341c8004a07500c089940202542c040b100b400c1c072003950a176503a00d0494810701c40c03003c00403d0100580c0c8003811050740040c080c01a880280c08072380c0c2080680c1c092003490800580d01c0c0002440c050410b1001500c000c00071610484060226410b0281200c005401244920698401a409024080241039010310043d8000e0742101660407858226004039980c020024141814008001040324a520140000d4210990803441200c043c2e506c1e00200c101505944d0703a214400e0700c01032b84441c8185410310032182d400d58842c035024609048070500703103210001d64480120800d001d04d500103100c20800040b1040450340c2e43e005980e14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 154883615 1250 154882365 154882367
    0x120509030a02013605010b0618040c030b090705090a2408100305211e0408010b031b0904030c080a030212010603150605030c090a120201020c06070c06260f07 69
    0x50510115030408a914640c54030326840d4000d00c51542845800b41004030744d00d141020b9001d40b00c0d001e4400d810200008020f0f2041d16503480205c2c100790211340074001030284443c1241515613590949511148050200c0c00c0103004100806000c0b4001d0000111241e8130400c050f01840044000e0240e07030400d5015a04550f84000319940c08410121092815800e50326010f40d150070808002007121401c68034403454601d1320003a108009800401c405034244240301d0480f03190010f1148950540c02c140140c501c528005c24170500c02c1c1c041d40e040f500841d03002c00c2084003c140c050800e600340518440c0450104600310002e003290680360b02c01580d202819002400720a2059100504040c9400c0644044140e40621201102d441e8a0042d40342c0c0c0340c031440c0001521581038000e620040d900d07000242c0842580d02001454000d0302a0b0324103007046400e0000e40d10901e00001e0011120103020301c0054080c40280e4081ca000d5400010030031600c0070307a60390340e490684610500312005010842c0c41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 154884865 1250 154883615 154883621
    0x209091c0c0b0103021011010c0f121a06030606040515030402090105010807050a08060406170601050301060e160f02120a0809060c040b0d0902240d200901050703120509030a0201 78
    0x401200d107803544119880e51119482c2c401c0600009120303002150000d000c80c1d00c1042895090398041c0c0003000b02d2102000090400103c925180300030401010b50b2032001039680c814a9410031101c3e4103d04100007100c200605540000d041c2e943c040390030300c00400c0381d80311540c0036440a0500d00e03c40350349040ca0700400102310300580c0014100901102040318156001061700c007064114100078840d6144c1c540080c01802240e045800c130800c0e4070000491081300012103138100c40083c0c00030000f090322040b10f940e2000c03044894444442c2d03070301001181c0c0c62203902e070402c9000700b61042e210041000304080300d1540c400c210710000a401002884a443e0701400b650341c01004c0a5191440d10340390201d00c20740c90040059a070b00250ba1052180155100c404017580c440d05070300001e40084c2100c56009503e9002586000d0109103481440c4546540c5103131443d60a000f02c42e480d9080c80940c0d401141c080d440400d04a003008022160840d110200c2d0191902546126000e55100c0300c04203002030071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 154886115 1250 154884865 154884913
    0x70608010305012f03060f03190c05120d0809030405150702091320120304261609020d0b1203091008040b0103110612070206041205190305090a020909 66
    0x81007480701c52109103880300c40340718502d044007103481d12560740c60300060300a20342490781e23a0103004040601c0c0f080c0c040d030090840301078451120840e2880c2c8413400d1102c000d180301c500141310303404000c08080450290643c9940540c01d01d017207030b1809445001040f9000310a00c1c4142c002980400c10700e08526255079050340c0000e81c9011000700b000746480d580180d18000345c11070600081003280c10030a0f1255001d9101c0d0428200c00c03281e03a1995010401d03161000303c040c1d40d04548100b202d001e4020f0010030f41405010425025070140c50901c0a05c0000b544401580c40400e81d1b620069220307510344c107094003e60045203015545403070b203c109209980849000140030011744008000014042c00461381c1076a13049074845100100c0303080890f140d03104040301d08032425040020040d50f1a0300150461045200e600f18010341c5d21240d00a0742c0074000c1c1e210078050150741081d40317154a40701307034041c0741c8c0124200300f121141c0d1502d070040f4680b1241038440400d540c0002044180158445c0106c000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 154887365 1250 154886115 154886141
    0x190905100f0207020a0b030c070f05060105010806060c120901030617011b110618010902060316180605030a0b030c181e010b030a09080d050c0904060b03070c0f1407060801030501 78
    0x11400741d8070350000b22181c400b8021b42c4440da001002140c0c6405000096a20f03455110101c80411001410195541d01c02481158001502c4c400014481d09017101512000441140107003400216034101000940001807010304141d40c400d000961020040302c0c011034520040e00000b01c4a00c42261090b656081c0100002030200030070001400c100e0020399190b01180f480d0f090035038000da018200f4054032002602035402000407003440b007491510030b0b034030303a04181d15283c0b0980c0d240c03401c0c404440d0451038031685000c40e1040c000120001c04d80e81001d4800ca2000f401d4907151500100000d980a58104403481000d20410410140e284181c081c0d040e01601045ca684a0f50f25080e0304540d54800107002c00c66080d2150f4403202000f01d80d0040e58494010200c0c2800a131900d241c041c55150000103070644220308241b03000400c01c042e0b2040308d0041d48159208154038000361210341268a0320201200c071000710005c0c2c062201020300020024040da0b690380203055146080c09030944040c0b04a1003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 154888615 1250 154887365 154887367
    0x2090c0c010e06090c3313050301090f030807090801050106030b0f0a05060f0a1101020304030305420a030b0f071106070813050a060c0f0207170304030803190905100f02 74
    0x8010240d0010320055210412501d816038090114500301140c0144480b00300c1e140384085002e900c0701800d1000c3c01d00a0200c1c90703a504030348d0ba100304041c284e506006000d000003203400c51010120307100c3d9100d40d50004a5081c171080341c60b03441015500b111000d91010380001e9588280760064504607817442140c1c0c20444040e800036040a0001d12a84070703940c3e0010b18060005041c90149001d03640750303000d41c5c1c4110f00854481ca4a4100900503001c100c4d4a032085050021300c00b416100150349000e2869143c00d1807503441d200080c3c2c1e040b1800404003080f60f1145000c8000000030300003960b4503101d4a032055104100d400c00940c041d20100320950701120303e03045401000165a800410154081f0403a01d4000b10510340e400c1140c140b100012000d00080c0c18201d510010b141c000b440120281041c1d8222900c081e55400001c420a0030358002482d01e400801c81040458041006941c00810031807581d980840d40409280031079601d520103c8840d0041b0703010504040391482881a18003408d034040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 154889865 1250 154888615 154888621
    0x60803040e180f0a03020c090109090f0201030b030f010204030c050a121703060f13150f0305060a0c02010e0a03090e010e130201110f12121e040303020c0a02090c0c010e06 75
    0x262044401c001c1c600c1c56011140250144004410406051900941c905941c211040303030a00039100c040c2c884800d409501604000110320802e80700300010140c01c00760f0044280c8540d4011030281c4030304520300d46e1500c540180b001640d40300384001c10095100c0c00b1000701e06443c143c03e00c0749100c1d10303901403161002041a0580450701c2c044600500080c0303100740640d40c3d82c03030200285114066040c0b80c0e4025511000440d0140c010b80d0041e503040e030301d071120a090030341d039000100c18030b0440f804010801d0f00442c02260342044035070814814030a15000103d00b0096003416a442e0041324101900040d4120350100035190043c00c8160141c80302003248211441c0035001d1146a1b4070412000781081888c00d21078600000c00d008456040b100302040e11944002420312102075081402d11600c418000b00214201140d0320100c03403034107034505441c030160390b4440d02c00341c0082d08802c10001c40345c0030380308000005a0742c1c4407400b4420903907d005030340c440fa040754902d400c6407100703040b52402d40e20110078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 154891115 1250 154889865 154889879
    0x207020109150903200406050613061404030501050f01090f060e070f020709020c030a11060115210f0c110604020102060105190816030213050c040302100e030a0c0906080304 76
    0x82060b100c80d034400c0e10700c0001c0000102c40700001c83d400a80307401c92803440c003d49040041e0703071801c214504583c02d200c12034071901040301d1407040031218001c030b00340980100501d6001c1e40340c0b0420441c05c0c41b052801c09a90341c42c0c85080d1802101c1101003400c1840c0107100d009014496510000d0b5110010000345040100160403100060020400d210154407465441882001079401501da40c0c58195141c4200451441d07580c0c00140605000c40c0e40154403a240a1000408034125026144418120f040b40034003901e00700d0011080c0702000800c2c2ca00321550004600482201d806040000200b21300f400e41c00502401c0d0244481440341c011a00740400f5030303070002d0668155482128000741e8141e004011914611050740285020f01980c18411900d1206419402c1140e0090301c01d41d0001101400c0c034002c90350b00300e030820400c603028482400982069198030304404845c0c1405903e2891341c0000a2810041a40842d000040001c0c00d000c0e034652806440010081c2c07800441c181030034070301c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 154892365 1250 154891115 154891127
    0x3080c0a02091e01030818040614030c090c040e090a06020c0a0b0a0b030c010e0a0f030f120f02061b070204140a0c11101a090f0702011116030e15040b0309060a02070201 74
    0x200240c41c01102159030003016100ca00f47c449811001801003203a695608559401c1c0d071040040b4503c00d0199008071212418600c040c94442c03a00e198004e032030182442c40d40d01a01e8009080784c2240e1007607180c6100010780030310082042000d62402028655542d2401c6505280c00611910705942000494802900e00048001080c41c3c02d01b002210b5207101d00105404d4040d59010403000340c940e100c00010b01c044a412210042c0c060880d001c2011000a0140c40c038218184185006a102800103844002c85050004407405403001440c0740040540000e4140c0c0c00401040700340c42444814000005c80e14420000050040d080940005016050980d141c18103c4d86004000c0c0e00c95000c0130000045501d80381c0c10450043c00b8514030f060a4411900780c0400f11002d40c055032905202070b03011080b000c10380390b90200401100070807003421742d8102d0750710003a22107803504020a1500840320a0482d005003014100201000351245010001c85140213001303045070000e03501c1000b0384c50150768009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 154893615 1250 154892365 154892369
    0x506040e1302151308101404031115150109060e0f040911150a030b01090b0706091b060c0507050603040f0f030203070203030a0305010623030a0c050403080c0a02091e01 74
    0x84020700300795640e0000c10840403007984002482100091603140c3c4d030000f036203400141d0306590222040c032860481a0803c907021841d801d6481d2461500040009218542c4103000c1d4400034103603114000441012801c181c015602842100741002100820356403102801c07008001500d08500461407910106550288840070180640d07162595003050005194402c545a01b01610300d149008681c0e11307406940d0495002c40740042d00704480c8000943c803a48590007a202c110700301c0c41c500012a9240700003410780781c0c0111080c5100c50307001d040e0072090040f400c0040c0415103a0050b5034100c0d15045080550a81025100300b9050050201041280c03441c2c00716154000d030b80c00380d004c0b01810140e1841c002c0110095147c4000141080c0981c3e060300b082d41222081d80766030302114a080000001e402041d0000124484240001100003030140c220040203081303070900704c0c0342c0b60b2240c4071201c0603809502d4041c0c0755031141c82e90208604100f000640d001007a040d1890300c1680c81c0100030300320301e018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 154894865 1250 154893615 154893631
    0x2010c0f0f0c02090a0914010209090f13020301090b06042a03020a05040f030309031103010b010c0b0601030e030f030f0f15130605041806180b1f030f03180506040e 72
    0x1da1003140518000d124080040350014000e0784c2510303103104070340045c214100c412101007517440c0c44640c15003014004c0c0c9066800003017960280360740704903224100d03450042240034440382d0710301d5800250700c00703205400407140560100c0c1400d10b400010712042d1024600b14800c00341084042c6103452000c240d030010045138610740542d541852080407a00342c007540d00001c080001710310b40001010703000304089003100d104131340c400c141035008001c0608881c9a0100075000c1240f920030325000581e43d145c025800401418005800d00071214034600d5a006103884a00c180000410301a0180051800302c1e40b140c15042e05a10500d032403c5502007004003031030854020240707246891591629500400d007c3c010183c000c003d50b040b01c1d03d0000d01c01c0c241410540d807042c5400c400d4804003014001414055402c06100c3e80180c5032500b0000311a245206540341c4e141a111011001800100e40702c1d03009070080d60b0707100190081d03044440045503240e00207840b07003408110401103460618150382d030107450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 154896115 1250 154894865 154894877
    0x6141903080d1e05070215010303020607031e0f1d120a110709090f12020304230a0306110c07051f0f0c06060605120c0f04031203020c03040611060702010c0f 69
    0xa80d9100c00908400310f01c50040441c4444001e22a1402e6485584510003650032103001c0d001090042600d80801e01001c1c006820903000581424029001a80d42c03802401001c404a403049840302c1c01c56112094400710662560200b24000040f00b0381c10503c2e542003009496024404291f01cac1c01840358140a07014030070000b003c1c81407440107100300001403080801c180300c80d2100f49050350780e845c00c1c614200c5034907418501d2400d07218800019203094031040b01c03041042c2080034948100204255030720a5005101c48408800980c041c000d02c1042c03010ba0007620b49984030b201c085810109030b40c04c102d002c1c61b00259003008811549503a00040912030500401004001c0411034404000d800003911a03800d003680040d13030b070340d0140c000d01a0044004108026844020042d5068403d02c03001403140003050106001207420349003992400d115504005141103540310032030b400c540003940300e070740410820510b2412182051000e42c2d0700901c14402008010b9803108054240d000070851181040300b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 154897365 1250 154896115 154896127
    0x30103020120010513021905030c040e0c0a061e050c0607050705010b090f0a0e0c060a0f020709050c091804030f030e16080f010e0f071203030f0507030614190308 71
    0x86803040400c2d0b10920301000b0b1019140040a074111035811200890240540322207251049030075510460a0ba08001c1c05047c401c2944170400000d031082d428414628014100f009041c0e964505010f4014034094175030580c00d00e114040142c1c603e2020b8000b0081c842c1c100314810404102260780f40d40040f09040294a032045070034603600405420140f65004008841400003401c41010114032442c1c10582c02d10031029401e0300c0301d8580f0544035200d41c0080040c00401641c5000300d121a50a071800d204840032a0350f203649403425500d003920804d040c184001855901400c002d2600010544130704000c0c0c216081ca41ea0080c59451b01d00c2c82c51041640e19100d0100010061140c880b0005d12500700750503603910f5000442d200e12418804286a6203049801d48031440d000c12810001c0303082001500409203090b00b0341c071010000a1f0101c042640d80c0c45d42745103031071032072141c03e000d114135550000740142080d411245034468111000e1140031006111003410003100040802e0f66403000c0482e031110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 154898615 1250 154897365 154897397
    0x10c05120f0c010f050f090d020a022b110906010f0e040903030209030a0501020c010614210307080c0a06050a0626031605060412050703080105040b0a0306020307030618050702030301030201 83
    0x8080e4402002c0d5035400c0000310b02c8409055000540917070710042080040d9181c00d0040c0b0780d1048803d020340c000d0780001d4035600140c9011100100e00c0790917840c0c510100c1400e4152025180600107044544d5200e140003102e90b4100300d0500c075400b07402800e0404840c1c5502002400714100701c0750326489075455092a20805100340c05071045c0e040043d0458410000c0c0b032501a001c0d40040003003242d00d6190000008038401342194110000b1009000701c580c64051042c01d041800710382544100500c4104102c20004008030004c0201c01d03651005022081070504d000c074251400909443c20480c18513006100003850444200e40c02c0d072418140d5906030788418007850950060843c5500071400d0b16010800b4803402045a40c072440c410002c0c002c4c540e05410064495000d05000500050003103c0140850304090388403242c4c0d80c0c8000d058518040c0d603942c55000782d03030045880b440042e445000030000c0698040f82c3c1d0483e40c4402400303000034500036000075941d0105210103410004520f030804020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 154899865 1250 154898615 154898617
    0x20a0203010f1406060301060c140120030414010e1e150f0f1608060f031e16080304080303040b0601050712090608060316030b0c0409021803010605010c05120f 70
    0x155400350003402101502d0300603400600140901d0800e50f0358040010782503142c48001c4038140d8509403a8854041d0042d240c58480e00d40b031440d101069981c8565071104200b02d81e81c07032103408000d00c188a03500d14040c81c12502c0324022001d002101d0381010280101010f001c50603040f8044400009444a160b540c0e07018a4612b0280d2032a0781c02c0480e50500040941c000c0e40144a8595900040c0054072600e080311003c400d5208007100141031580850f00914240d0030741000410002c007129094140710400380c80e03502d42680011203030742c0300b006001c48003512151020020000314001c1d6041c1803502c90400e44070f10000788001c003060758000010700168011020390303226a40041c9003010a4161071000340510425000722008140c481e00082d080c2d28000403940c07040b5240b403c1c1000464550ba0719403490000180802d200f0b5041440045180608c503c05400f112600b02500004a41400281802c40d4002d801c4181048807505034507010400000b00c010b007072001203540f2603035001c06200300072a17 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 154901115 1250 154899865 154899883
    0x10306020702041835130608070f21110a02010603140304031a060118060306030201080a0501080a110609060d09110d08030f0702010b04020307170108030414010503220b0405160e0a02070302 83
    0x400301020821150141c41c011081c416a841f580f10381500c1d4680d410140c490018240c00e48002803901d81c3c89030614043c3c6054036a69101c2101c0c003040741d240c101d0300003c05030001c0070b5110050b95906001c2052180c4110544400c010b644003540c5030a056898030419409402501001d0306002d43c04901280d104803000704c5ca1514003105044101c1d10f0f84401406441c10707100c01ea0010703964202066281301e01c1d206090480300240300401402c8140e0380c850144a1800c03910f04c1d44060184088010f60715241c008041a0035080b40005150031145441c00380a44054100340c040c0308600704050005035210201c0350810020090240305030780340d4800702d0141c450011883c0e080360001c010b00c4a21504004002c03291840c1c2c241c541d41c80c1c1c0e00c4a44160381d0707020b00d1050b0202601a88003c01965001324000c58000410054142c03984541fa03070030a8203041c200000300d0f0319040020070003080c01014400d0500c8041d00d000174401c2c540c50030802104100c00604a800c40750303800140a0308140c001c00032505 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 154902365 1250 154901115 154901213
    0x904090219060215010501140d1523010201060e2e12060507110d02071401030b0a0e0702190314030a0e0f030c0714030312040206070b0103060207020418 67
    0x5203941d11900004d44851080c030481300d080d0400c2c00089019809203040060111900041c00e080c184d101c529140501000ca07505030891000ea4400306401c03064040e041012240d40e807880d000c200520000a08451030b80c0c2c8500440d43c0c000080c040e41e03002d1700d2040d02c20340060760f1480036800c0b4800e890031999400c90f449160900003070141c0b03504002854100921074049a181d105174141c0700d5a040e6120041a012a0011380148a09100346c0b451303a001a15082018940021003031f4510002c0345880d013154004540702241c0c80c04008031303e5130401c48031500d040e05c2d040d006010300c0c117650040c000302100048207412150110000b4030700e0a255002184818202c0110b0f014448508101ca07105d900007103840800c1d0054044c080b43e8a410b0a00c0c02e001040003800543c07400f1040300401000701c6002d0b00480c0d20240402039100843c2d681c0c007070340f4080e40c081e11005070350790349900c10081280d080503410482e941140130484086a10020540585100b603036014010102054840000342d80c40c00400f9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 154903615 1250 154902365 154902409
    0x1902090a12053a0f1202180306101809080c0a1a1b03011703090310020414040c020c0f03011b0806030607020c030318030709020307080f180309040902 66
    0x2090220005810001c3d43d141c142042c01003894600144800701c828412031030205509808500c1c2d54826400c00ca4845294a401c0380300346041c5001c08140d0b44143c80d050320103d43e414860741c0501e0148042a04079540d00c0a09107164a061401d1314603000d5250551a1640c3d21103119003400641d0086030285111142601c8a0840c46c0ca81006e0603e118034400c4903d2640c0c400245804031401050001c048840c83c020f81980c4ca0400705000c00e040c000c00d101d05501041c0100300c07041d24100803240313802c0020b100c00342c0c945d424944143d496501d0804514801c50811440c40752003600420443c020800648291070115400301c0464003410b00a0348928400d5400d20701c84000503030050590303008110482c00d1f03408a0300e41c104200da5601401030300b03aa040e04200700ca03281c081042001d4601004014060f91000d603a20b11080f403c03600129118030100d240c403400c009241400032082c0f0303400404001d4140000312440e12290340d81c0181507015000719580c051201c195134074038050041e00303c2c030440c04c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 154904865 1250 154903615 154903649
    0x40e01030b0a06091806090c030b0108060708060f0609010c030c1b05090f04051e011104090e0d0306180f02070c090c080f0402010503040201031d060a0e070605031902090a 75
    0x2120101c5011039907a42c40e107142c100d000c01d02031002e000d031095000320109811640380080d11120000c05c104d010440312444200d20001c001410640e0300390090400f01c01038199440e04101c05417414000400c1e00e482a00c00b44c2c902481039603110140c0f08403000a00c0e112007900d5151170242c03142000d003507028091130b07006080c0d51032800b079071982003080c4c81081e1900c07040c07a00c684998484408054600803e0b44d00008003d4208140241c044d1600c100e0960002c07030020082041301520364000c0c0c01c01c0231000c3c1c9401c01460811b008204ac901c181c02607140c1080403078038210400b0920003403030f030b07001028940360b030341c0b10040c07200540646002c56044000101c0051f03842622200500b1107944d500082000b0074006181c0d000c0d00342c2354038030454040c1c44140c5103a4035030b8011070044c4401184c02d0740740e040c0300c50950b0684000b040410f115480c6114001080316035214840c1c0b409110b54469000c0000800801c15610290380c0700304002c52400c040075844000301c00000f055a074003a0024801090024a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 154906115 1250 154904865 154904873
    0x503190908040609090501080606040e03071e020a0506071709010309060f0f05010b1206010507060e0f1509011815021903091209030506180f070803040911030103030f0c08040e0103 79
    0x810454119813980181d0640c0c0f607400c082a100d09118809803504100d0004003142040d40001e007181d06900e09692900d00c0640e2460341041003c03500c403046140c1049017108600701414241d0250400f12406401c040030360b5540e5412001c85160000780000101d50000b45034043d4204ea00030942c06482480394210409a400c02800f800c000949048e00348000041c5210950045641c83e420351341e0b1140041d0781d40801900e040d40039030411101c1c6540ca100c51030307200f8024050710000310014000350820220004400c068404d0241070300c1b00b036902d4840900b418000b411451003031650310500c039000c01e00e0145032040090081000d0452602c0792801031030100c55165110000d01e51058075040c80e5020b034003804403035030303142e5000091060f40b141021494404050005640240b0440c1c1243c0140242045050510006a000511513800444d040c00882603600a10138082c146507110f034199071554900500035200d0030b02c000140090003440b0011301100d00112806410640001d001c81e51f52860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 154907365 1250 154906115 154906117
    0x70810020c101b03020901050409061d06010908070e090f01110d14010e0606090a03061d06010801090309030818030a080702030f060f0c0f040e040305040e01060e030604030503190908 80
    0x10804a15000b00311404407014a14840e02c03514001192100c01c1010034141c003a80290f00200826040c0802400001000d8505005900c00b412202d1400e550142c00c000103c641e900020b40014140007074000f0230f2200010008007142155807440d05031741c81d5150480c21505088106c98809803c0d400d00600000d0f544a85000b80254580c0e08030800c0368038100e901c4480c02e80350138041c01144014070400f103100d0345082c070060244420700526402c10144c0d00d54540b41103c40034006040f0a0340c54002400300f0520a00180b0b004009000003400b400d0202d035002440d40d42c80d804001e040d0440441c0c03901c071250803400014000c40001e0200c5203803013042c6c1007650060b000028128828810224002d480b002c1c0031031424010407030791442d0512502c1c0c0da10f40300d095401409550310000b40034000080c01401900720240518020f496041d03503242400e8115a54800503005103051120903403414541e5200015407a602c550580340003612602c900100888045a0040e40c15265003480c900c0030074810880 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 154908615 1250 154907365 154907377
    0x1020a0f09061106070e01030212040b150607080403021203040807120b09010b0a05010e1302161b0b07030309030c020d051b010e06040b07030c0f0501050a0c14030402010c030207081002 81
    0x40c5500700c6050b03488108a0b06440e0904015038507030092000f0070b01c494040c455048845c01d05040142c07c0068090085600c0d0310100c5040d15000c2040c0248800c0180b02e290390201d449054170460314000c500c0e11160214819444024019000c1a0300700048070001e10070b42e03004c5c2400b001619075090b0f58240c1c8214050f00200142d03420340f508804603c0074001482460104031002d410b06800030310300401510002101800d05400140d40326004180c4102c0d407008000d54180101a206d092905040003c01006504066101c09400300028000301200f00d00780d849080d40740c680412429002d1400301e038104a6031100079000070603040c80b80c08201c4082450744404c1c000b03040c01e1170104602001110446e101c01042608078400300424020001100c0040480a00a003801031040089580b045018002d40905a40a9541d1014001c14002038010340008942500e03055102d00f080d0305c46e28449110141009051000c0000c1510401d40240b0466005125680a50301c88081c100c40300e40c0654440d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 154909865 1250 154908615 154908617
    0x6071a0105010f0309051509100609090519020603150307050604030305030402030c0a0f180608070602030a020106090204051806030c0303030c1e032a09030703030906030b040603050c0103110c01020a0f 88
    0x5402c08a5109204e4419518140e41140c0146400aa02507101d180d1000181c1020414000c4e0440d04009890702e001e8a0f004144132140002c15000ca400d2480c101030140c084000a10142d518003000b680e20501981e070404003907101100405400800a4603241c03e070b40c4456000320020030000f00741500000a1403290307009500b5a2001007040b010400d10285502426003500820070051000b00086004210001004000014241e03105c100c980e1402c01e041d444100160b0000401e101d00603420700548004181c00401582006c1c1401d00058007a0070501c82c10320312040c3c0d0030000345c0350307a0104004000801c01809481d92424105032502142c0e0045141c4024111455112000c40e01c801044910034640d17012414100004000002100841858404503031340d014010b5041aa03402e10850000318800d8903201701c01850074501500352900c1045181c819407803e801040855004144403e155070246000100c009401a94400ca802030307a20181c0700b0740c03000c5400715034950003400c005000802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 154911115 1250 154909865 154909877
    0x100819023006090709140f041401081203010f09020903160b041a0309151b040801060603240603020a1202040807060905030d020d0305060d150507080907050306041106071a010501 78
    0x3440c00340540e40005440c2d000004900c0304d0300b08139024246c120711340c01040c010200040c880000e0002000e642c800c0c0c40134240c1389111401008503d03420425060340c060060840350a41d894081380b1001c8540364410080a02d400181410603650148848048481e543c8c00e840b0410382c40302d210140320340050003440884402e0605110500001c0300507640b20f5140d0701d00074498001060818407081d00054600d0024010081e59220005000406800540014800014040e00d0260700405481c002420f001149000b5a0030124a0301550480000d642203400c2c09a51202c82d40b03c04c403441c0b82c0600301103887c0351001c280800c4c3d030780300400d080e0100d540507510841920380303230410581c89800ba03800b5200564040c24011140900a8000b0366000200030520180c3c00c1c110386601307018007400c0449051030f82c1d680c0c0400c2025600544441d1700030b041503004092090a00700800d0782e920b00039101610f160a40e002d4040540d9440c401c54078042c0e0300000c5800341509084548000030001e019960100e44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 154912365 1250 154911115 154911121
    0x12010f0902070803010b0d0209090c07050705011d21010603050c040509010209010503180a060c0507060e07080304030b100306021b0705090f04060b040b100e030c1008190230 76
    0x2828000e9810711900005011301c0c1d41d10704064440d06921120518030240e80070320200da12035550460702849800c1072080690707528114501181050300903080181400000c3c0107520074441c41d690444a07500007918102500244144c12151006038115200035075070802e60040308009011484450703502d0255000d1019440d9044650f0a038040d83e103026000441c24800200312000081030014403100c4c10040e15124407040e15890103851012080401180c00013902c03000308440c0c0c0c410306043c504610301070f040039420035101030f03180c0c86580301c0542554580c80204824020300304c520780080d503000c8011565035080210100d5292080c0503014094090440c00040c18140181c8030307446150301510b00d45082d9200c3d0f0782c0c10014030f000b10703000d0b070096030311100301050340c0303940c0000d0200912586500c0a2000154101340c41c1401c9004c9a5024120345c2c0480d50025070803403907094110510136810f00340741d160619040c0081c05501810003c41c00d0030403c00e00d07076010402c0c0c01989000c1c543c0021003169 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 154913615 1250 154912365 154912379
    0x309040e0319050711040504060603020f0406030503090111011e1e061805220606090c11030d0c0219030503012606010501081008070b0c060603071d130812010f 70
    0x3010300075242202c4007100c915205054428401031074103510440c4d00c8002c0d100e0704008201190b07011242110319503603840c03052041d86030641020028107801c44042c09460b04543d12076489028030320405042c4500c0240051a540003034200d000000c0d40c11081c421501066030b900405442c4030f00300b00c02090405282010000414022072069420600c3d10314504400c3c4e803101001032100510202a0080202400c41e015006210a0030031500580c2c003c00d83c5d81c200940c1c1c3e42100d00039040781080c4048090440b1491601005071000d80300640c000182010030b104060341403880240d03040d003020520500e00010140c20030040d40c140c03100b60a4104918029046141001c2000c000309046544038000420443d03101300360b030303030f5000d6560808454941d40d6041c12616140054211001c00f030404a01610710035010081c03194031503c100c00030007159107402c082900700c084c1500200c81f14500303034000070080d21665403141015640180c8440c0da500c2e602c590b182c2e40308428000c80041c8224444002854 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 154914865 1250 154913615 154913617
    0x2030a061104032a0501080f0f0a0621050106060e092a0d230c1c0f090503300a020a0e06030f25120f09020406080307170403030f08060109050306090309040e03 70
    0x1507910650740401a03111072704818480070006104041c2161110300224201c05081c551200c07014000710f0201d44142c8624025003034030140e802010802404180541d181d0b40c4140544c1d811080078115911112001440d0f0f00540d41c2c00000560814400511900d803c0351590000083c0daa180b02941c070001e412003814100360714243c80322100c100c42840b02c00207600d440110401018010600061030a41244040c015610004415905038202140d6800b00240034040c00201c4000100e51070707410708041d05600040040a860a405661701103000310b01d9a00820816110140041c50645c072450108521080080115900b800605c8030150041c81030030503550854070300c0341e2901c80c0b990305c1d400d60101c1002024400c02c103c0c00c6580343c5040300e015840301c3c45075402078040c205c0a10350b01d071002d04103482441c1b0b0030400c00c0c002d948104030070001320b644844280b1034104031b03250450442d1124801215200c6076500190352600601e418490240d900200500803000141d40611150218425103616 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 154916115 1250 154914865 154914871
    0x307080d1a2b0519140f0d0f020102040e190c0e0f011d04020705012c100c1106070809100501140f03030c0607080106030e060402030a061104032a050108 67
    0x119079a034403240400038000382d003410b441c00a02d9580d010068403600e02c1d00054008410003960b0180c0c0040c00d1068045095107040180e40080c403044000c107240300d82d80c6140c0810503080001686550404c01d100790100d82c010641076540d400c440c1482c81e14205207140510f109a1064545800c3c200554010b92555901c600e00800e03800c0000c00c454019602400309006146180348440055601642c3c2d51028010305c41c080d0303000140c8009413040d00f070301d49282d030f100c3e480d400c40c01c90a0180c10310500040d8640c82c0f03110081c011030300342c40d401c005640000e81c85c205588140194000c1090495000d035205219a100204031021001e40745198002c940d028000c3e0248179000310050040380c1090000951a041e01508891503c1c4100d00d4860030b201d420f44403840050211001000683c0e414060034240102c40000381096051a9001a81d540b40744400200025116003417645c1d201c01c040c00341d500840c2c01c4229990f44080741030092241c4881451408940020360101240552182001c144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 154917365 1250 154916115 154916119
    0x403122a081303050a14010e0601030b0109110904091109070311030a050903070c03030c0b070329010201020f0a0305010302090a06060c0602090616050d090602010e0703081b0307080d1a 81
    0xe0108058403020305681c484000403200e06502d10300000081d00400c48154020300880d140914420556001800e44030007021142031680103100600124402c0d0458a0444034407010004580710624502d5040b4042c141200e0340c0503281c80728070818031480c0c6148049010044502c4c0c0c0b25643c901c030b011f4085445001429420171002d00c00600008a01e500654000c501c0c04104c90905450350f503000010030300303504210b0004901c0f80942e0100110000303003940041c0700b4103003800466060480380c0f0045044086003a45428250441000c0d40d000b036040b90490b0704001c03169540c507042c81c000a80581002e00c0304078001d082000c0041c90541c0d440c8100b1043d94544d64a0070342203055901c0301c60181d003040d1801d5074041000c204c440d46111005600c3c0a20b20300c21801f80440041203a0b01400c0c0903140d500000035641400609221100045651005d40341c3c001940c54581c551841906958030003030b0b500701001c0c03200045040500050b0006020034108984041c444d4120fa001d10ba040d002030000b08503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 154918615 1250 154917365 154917437
    0x4150303050708070c0b1b06070c030e0a0503100b010908010b09060105070804150327031e050d1a0a080309030c01120221091b0f060c030f040312 64
    0x100000c1d01c18001042c000b409607841d01d0819459807a80700d03072200594002e202c8403000140d0101c1c00e8005011140ca0f445e0418054111807410101c0038181d0740f402030005007000618101e5591980d034550304000a8000541183c8919040d041042c004000701c480003404a04001d0000400000500801081c088058082c80c0b20f82c484000541d490b40040301d04407003102c014800800c840c0404940104100ca00b0703600483c0300c0d0300b40c00c0403100f4107800ca4004000040422004008250000b1016800f07031000b46810602c06500039003103a0714000c40d450303060850f0801081c01c41510714038100b00e40001040307c0260104c0d541e143d00310791b213104e0190b185425400c481c409516660080b03e80121515030f050026140c8410075403101e2019038403848607400d60b8020418003400d95400c12041c01c0d809060b000c030701c0c40706004000180346c140e1203040851141500080c10740140d0802e0041d1810140d030150203d4550781c0f0303480c101140860155405000900e848401e034411600c4051803415151050151 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 154919865 1250 154918615 154918619
    0x3030509011d0a030e01020712050604030f05070b0f190204080a020f03060f06040914030a080106120b01020a080a02150907060f0306060e0f030c1005120705040305060f0406110f0c0601050415 84
    0x352000203080a400f81503008464000504146040c0e5403a0050f104cac1c0003911a03032801c2c1c9000303450801020190010060184100d40000e411000604d40040310300c920669941c0c0c600010400342c1c2001c82c000f180b550700114000034007000c0021054201c900c00c650100d08190181e0501d07079940c20444040601128500100d0305a0810348c2c000681d203402005041c40c400720345050507241d0390199404100103211200100006030b400000d00010722860382013804600d0002000070350b1000c41c003c016142e40c00005100314900d008215001c024450402c0c150300782c2c40c0800005844801e10310816020590358000038207101d00c244030312020b0b90810744550072001742c800144443c001d003103007c0c217815104a61811b420b030794541d103200e000d003007203a42c682e69600c0a50542112004c805421001401014041070002540c00302d00e5580c88940c0628648050741d4908110000d00b00c1c02c07180e8040b02c3c7c0d00040c50302c4030401600c000c1c0b850102000403514166a22010700040342c0c0b4030040071162410307040003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 154921115 1250 154919865 154919867
    0x61407081602160e060a051c0b0c0909130303050a180b130c080718090f03080c12150102150103080a0f09051201090c2304020a0c0f03030509011d0a03 66
    0x1041e800d00034184101c81010760303104100d110303181c81600071014900a06082040d1840d0120049001c2c1c40283c4038505d4411041c500942c00411448005081000640000d4000c900d0036040c4c81d00c407030f4014840342c698100104043c405814210042e4002810070001801d001214020446c005910854103c07a226035510341542d20b54002e0403011390741503a04030380d0001c90802e030b803010040c110440280c0320b09440e10001c4105c05803000394011031981480803c2002c94602c10074504865010308080d807155035030b0f00503200a07100340b02c19507204a0b07140040c401c040e920b00204c01c03064102a000c80d81210782400c0c0307141c2c040c40244001010384d6000c12000650b20301c188805980f001e10f41c20016440e90301c03100050450b1a0011841d4160fa644200800611003414000801042c410040250088000940201c542d40b1300200c0b90040d0340004ea0110f81c10f2007820728030031964000c140e0f11440082840e00030302902e82907034565829800d0190158268107038100340c01e204d40c200002004603404581d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 154922365 1250 154921115 154921141
    0x5060a090201020f1506010f170a09080706020301060207091a03070b0a0306051804030807050f0d020a0908010c0c0507050307270b0306090601061805030d0e060d0f020706140708 78
    0x1001c9046000c0d211090b100c02c40700304910b030010040340b5000c01103072078500001401107115004080800400000b1071010380401d030061074104130301880c045a24003690522104c148600315009101a04c00000080e54541c0820350809035402e03024184041c2c20320302c205d00100044800100e5054015107020802e0212050080808000714203003c41c00564500c0010b0302034150900e01c00d003c008a5040204059011002d6039001c08903081260502784201c4800f80c0c1400ba0400c184142c960000303c202595004400660051081c08000c3c4a503071a1481c0007840c010000b032086a16200e0948040b035a85408a000015100840340d8018484400c0086d15200d00200d400080815659000400d0f0342e201408401c0c851021040103082c0f0354901480100006944201c550320106030150910096034003280f081055401c52601e804805070200008040303101e120b0307115001e54604144801094a5600a089510701808003040b203185a4511008283e20403981c2000081c40440000e0420401034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 154923615 1250 154922365 154922381
    0x50112031b11150318071a070c1701090302121e03100306020703081801060509060405090f251d061003020c120909090a0201020d030b03420405060a 65
    0x8542e1100d141c28410105100e0b00c5981c041c00000e600001c00c01000500407020480861080401800034628100d400401c0c0200211003950310a000180392052007012104034000d082214040c008840701030000600901244400700c0140c0a140510b81740d001c1c3c2c031401c0c0d903000380304200b8030040e000121196492503403004001c2140b8154185010001c10340b188040c0070304a100740c903500f4680c00c0c18803003000c0034140018443d940743c2c10b10200b4407203600c900c10959046801650007044580b00e02d500181041e07031407072070082a446001840881200c0c03121070789100101282000c00065101c801d10015010107150381c440d110460307000714210307081180c401e00e0412aa4a0014102070807036445508042000e03681d200c0701400031944107103a1030014441908110346400610158140d90300207034940181c4d0304d9102c00c0c540d50340c00308911134405003c4142c001c805c071075072024080341803220b061034545c905038514542000d83e0744840b03510070a00010390241d82c00000501d029903e080503100505844 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 154924865 1250 154923615 154923623
    0x610051507050a0803010302120102030c04060f2006100e0c0a050f070b0c1b01181e0f0b04050d0f020a17070f0b010501020c0d020f0411070804090f050112031b 70
    0x100710300360201d079043c08420752092150303e000707940794954010004049054050140182d02c1042441662001c0608036000c8800c1c5061000789105012800d0b10b0b40b240e1100314000008502500c9991010081400307489801440903211030355884001c240030b01c0c0c03400c44420440c008100110386029000b4405401c4004000d10b0403840c02c0c40c65914030f0100b02c426075090850000c04244584016090501d1880d206203040007007110101c0d040d480460310008010250400c4482c58513804461050206c0c241c503d44c00001022207245140350901d800c000844042e82d1074001c1510840d102441052030521310719842d8010280a4a140c640c400ea44048042c1645c0081e000c11411000942400c2d400c00454055030310009107624010000e0f0a0000a011541c8101171a250280050341d882c03001d0100c42c102510300103030303242442d02c803140944102100a011101c02050000304094260030440303403800114010701c8584d81e214030000c0c41005642c001008105406200345018401080398a4680c1c02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 154926115 1250 154924865 154924867
    0xa0207120f080d060f060806011b1403121501090503100225050a0c0f06170405030f03090a030f0503130b0a0f06090608070b030c09010c212006100515 66
    0x6a42d41d400c1030788180d110300d2103540c54660030014280ba48014400401e9182002803081c94000c0c00245042001b0000c000d115690380042e400348006035940b900c0d2410140e080301c0e03546102d00c1420085d54801c413809000c0c1c0b103c181d012422540702e840c1d90011500d000e0700800b400c001a46501000c0d4001c046d050743350041c1d04c0c0141106c03032100e001000586000e40050000582c5508000a4440c42c0d43c00c0000210208a81080040d9110540c44401412002184900d440d0f5250050039031242002081510724040244442c815002c02c0c809107140c880d40341c0220380044140e041d5200e00089811204043c420050180890702c1045203541c0442190000540c400407454807800720340b1960407007502e1f20754418052049a0f0b00300700a00140a145140c28258a4040712514003442903580041c10042400c020320200001c0811346c240c04841d00105904012519400811900c1110039aa1440042c401051090340b00410594020741305940700040b104d0511040c850b09840c1301c4132144480324 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 154927365 1250 154926115 154926143
    0x301030803190504080403050d08070807030c110d170703060302060306060d0902030703050f070602010515190b0d09020f0105030f01090e03070204060f06030501080712020409170304050106060f050a020712 90
    0x103948070303c40c8218401d10300b860b1600e08500707000340703820401c054500c00e210060043c0002c1c107810041c240d0340b1002525001c145c9140c095000c6841215011640c100b6120398104d1280c40c13078010f0a45075045091b840e0410090361409005c805450302d070300c0060340120040011444905015004180c1d40a41e507c0124140082c5e0340420301c4d18081d94020f17141e03604020b40758040c0c1603040c046407008105510003030089040035115024412802c40311103205561074241c65840301c0d0700d015050700a00007a10100e4407040001442c801800100343c040744540400900b00c2e00c40c1d80a40180ca01916401100c004035078208103d130001818501d41982440c4018081c3c440142c0e5540100000340103410b50700e034043c9140003005000e80701c040e017001c0b45a800840c0280003d5241c018800c26041d0100c4000c02c80111600704500c1810f058603081440c40300c004100020300c2015000b4004444a03980c5507408000440b100311814001c1c9800000160441c040400500c08006e4072501614010443d24140503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 154928615 1250 154927365 154927411
    0x50d140901030209121e06090708191b03050d03052d090705031207050d02030403120302130f09090201080c0309030703030207020301141e070207030c090c0909180c05040b060301030803 81
    0x46c40540c46c0c0740503026014034100d03c00040c03180d00d80044245000f845168103220103c2e4030f90b00c10590107441c11001002d40000d018106040b03910501c26a82441c1145c2c0d00d9081c1107440e82c000c40c80c000003184c149400720300c9011403030b5600f000007030065491080c89401d000c1c0150040201070407400e024410608003040b0359800f4800b4414400c1d41e80e06003540c0b4241458143d06007186403051360203640003880f081003c118040d90040948001e03250060381c5c0c1d0240c1c0041080c03e511a0080d0301c08011028000c10385200c1079010100b000d0003626802005ea0b120700001e001c51000316200c00d00d54109012800c0024002c0c0c01900921344010700206000060320f0304c0090006003250000780d0140c000c81c0b05c01c46402c0c0c85240c84d410400714070261080c1800c5481d0200249a940320304801196902e4040f01124031074000e200240001c480b003031084101c120694060212440d070283e030f4400d411880040c0c40d152520500e031190401a1080e415a86181c0700d07803805810040a1141a8010986a40043e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 154929865 1250 154928615 154928623
    0x6040e01110d090c09020702060a050c07083703120903030204120809090c0310050d080d1104140406050d0b04081c060603050c090a0302090a11040909050d14090103020912 75
    0x1102c220100086122040c01c2501ea0705880358010400d00b84100903080250f224581280e0b00f100e203134100940e5480070000b0046c80c3c0800c5522280e86170103114440800148005a4403440f0303944d001c00b803000c010f880c00000c400104001e1005004c100914115240b100c21074100d010724900a08005040a68a2420014410380c4200468000100160640301d51034035102168211645001c80d50540c07408401c62456410746004061080c4c01d98221003082161400494000340100c64051040820f600d1028045070014002d400d04115240b010303403c142018414402202c07802006051001e4150b1503284150102030b10551742c10400700440001c0c40c40002c081c10031084803c038000780c40e902d0001e0081c00c03254050983e1542030b00030006001e203070342c40813100c10542c1d80440b4566010788a030103100004104882c0401e60308030b00446c0c0010400145ea0041344494010815141c0414540b9422980701c0c40580e517151440c1418402e012507540b1a83c007511595601401c140f60104200902900d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 154931115 1250 154929865 154929877
    0x5090703020d18020307060206070c0f02061603020c0a0b070c0326070c080115080319120c03090213050702100209061c09020a08160e0a02040f15030c02060f06040e0111 74
    0x3c40a00d5981080c110b0904100e408020002440074007a10304205d200201908014580030300000650650401590f603280111503000c403161440d24043c00b070a10b00a51504101b42000d40704601c3e110000403103000390300071901080c0d40410030145807400e50b03840100541503042d00300c43c50145481251148121080180354041c0074004032802d0a241c04106404e56040c0350901c00e0346d2294a030700700000400001544e481e005850404216140b45540450f5010f520308500c2c40300d1030406403400101c81d007540c4142143e0f03000751000c0051086404800040c0c52050f035800005a001d40d0420300a050680e01034007080c10000c0c00c0506c0c100e880c80c00884089090700d007134580309a032050500d04620b02142d00c40010602e3b00040c081c0c042c07200b10582400c420700e00ca2001c900000c0c200249008020340c1c1254041d05441011911240d1124011007000311410244000310b45004008071509000040c028030421014082c08507503582d031800c1c40064501c1004480c0259258032513084c010104901901d9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 154932365 1250 154931115 154931141
    0x190602072a081c09030b0601021f1a03030a0905091305010204030b0603010b0d0b01140105070804060306031209080601030201110a0b010803180906060304020d051005360705090703020d 81
    0x51142400407050400341400c2034010312054000c0c3d22000582c00c000c100b42220307004000711810790b4135400144d0403c1d125520403241740744110446006100d19034004c0550200446100ca00c0700443d41c14150b40f4460385400c1d801154003440704025500e844102990700074510fa00160301041c056807000c0c01d907003090704106d400b0a00841005258202440380c0540290308a41c019140b0070030791100c6810304c8041c0207031a80d0181d19190303011141d0254040b501c4140c0e202c11030b203580e81e598040041c02801d6900040f1500814984000100380c8241680e50035903890300003501c09a480c60f80152040c2c1d100182003034603401040100b40c082074a001940d4001c00c2c880c3d02960361028410360484419000481e032900c14040c02e001c0c07050a40340c0c01d0a83e980180d040d00e51000c009801c1c20542d2030000d4081c19940300c582000e003000548240e024629410a8250200c030a0b0b10700f818071340089684030402d01a4003544440420805440c1c200c4c0285d400c401207040051403d41402c1c800000e80e03c401e1840c2d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 154933615 1250 154932365 154932443
    0x190b0f09010918050609061e06210a05031204030e12030f1e0a020703050705010f020c0d0303090203030a030606080f010e040b07090510051309150627090b09070219060207 75
    0x403456410000400300c12301e240e0030481000e8031707200c2e00007455005a1441b0920304006411007860700e443c100508882e0907000710880341c90303000d001c29140420720100c0302100010b800e1000e01c486400c2c0364404400158a5002a40c10304200440300c0c8450307040121a100c184400380d440c003040c106d1000c01001818030396800b400c4801d086061461a00c02c29a0100d4108520b0b28040c1c44480d90109072503034094000c03100c0c8089117a2906040300079201081010350316000018800d51042c0d0181c0c0302d1411203110ba11107266550310a41100044182480313010325203441a40003900280380700100680c4280a400c100d0310544c1c4a0010459400ca1040740d0008140002459100318a0410f035a0303009008424081c0400050000d118404114611070141404100b00d0101030400309150072401c80390390042007851640d0381c0c61192014050380102e9a002c2c1894401050942d840822480a05840a9402526407010b96240d4009500002c4141d40c12811054141c1c0300b5400c080c040301c40005040120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 154934865 1250 154933615 154933621
    0x90506070e010516020f0303040f0b0406110a02090406051e010602030d051006020703020607170a03020a1b0804060e04060f0608040203150405060408071109190b0f0901091805060906 80
    0x40e1004a00040c80c80c1401001c0c004e003032100c03003c2ca02895100da4180d808101d803071400c0700440d180d8003643d04102240c0458101c00301c0c0001c01200900111241641e94440c0d00400441064541a6404c07000e03401c04aa400054040785454028940040544444c0c0700020440009001088020f801900041e00002001079004c4901d0140b69041010002080401071514502a643c0d48440c800213000d0b0001069140a0001190003001d4200b200345903541d4950170040010001e601c80e24038a008251104d003012000c0b194005940d131925403015443d843c1c282040b20503034500c100ca8020700e82c400c0d150030b00800c00c410f240c0c202d00000d000a40740d01800c1d00b4a88101400c03c4403c101110003010008100400300d0000641a50040c1d00a4003403a510714071401d201d203540c40030303402d01604607041009009a403441420800c03120100c5176810020082c2d42010070004a40703015a40e40d102101c4c1c401800300b01696444181054225404290746002e82c0d65107504010b0115003c8825400200030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 154936115 1250 154934865 154934867
    0x313090515010e0a0302040518030d1b020303040512030c0412050d1b11090c0702030a03090302040609140c090f0316090b01050c0a14160b0c010e0105010605042709050607 75
    0x54619001c01d08142e400d1010210105070790088504c03000e4402d075103502c04502c0d0030400707100351030080504205130395803000801c9040d009001c8030034030110b4400300322082d1041c0e10700c00f0094a0203154024003401c52071080f092100307003a0b0000385c03461420160401c400a660005824002c000a124801422003280d00903400f0f031002c120241c5020707035984d07400b020500042140380720003000401141c81c5140780c5c903041203c040038060f845000350103104000c200000d25800c07100105c22240f0840d818003145446807551400d499805009000c4c0314454000305401e00030704809015000d0028050600e40c031602400a4900800c001d01c03140380d0781da084000e1007003204501070004090b5007820014905405141c20036a9207010100c058010907032200c0c0c0150080041c4200c05d00501c0e03078840b00c0c507802c0c0c8444440c821030380b10307501c00c400c0c42d803801049014402043c020301e4102c1b130322070711840c1c181460052401000400701e00c01c004240d08580e6203003074099607481101951801400207040c0b038171380154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 154937365 1250 154936115 154936141
    0x406091a04060906140d060605071407060f080415020f0d06050603040f03050c07151121040e04060609020a0f0e010215180a020603180d050a08010605090303130905 72
    0x80c4140c40c1810410050005076000248002111503600c1d08030412034174040c00c2c40e500c1c012020301811845c101200058000d601101a28a8601503441d00034881c6e0041303201a5206000c0c804d40c804100e01000140c0b046002d1144c26502034050302452125490006004040b40d210804c0000c1c00c98010917a00720303d4107107124100c0a00000e80300c26241d810240c5941904107444880101040400228071422644c140302d00d6008041205030f03404441c0243d1000781c6010314282c4007815a00c2104200c1d8440c0e8006629040d030318407488101c074a89414112141da001400400c250f40743d68441c6c400051203040c41c03000308268184c0303566001c4007903400d290050513060003004180c11944041e13000406214140740e0360760440341c0d02c3c00c0f42140170011a0b69a08020100d68084e610810100c02c0101444c402c1e0141a40b00651005440c800d00002d20706030380314040c3c8941980024240310040c40014082c030010700040034014200e13801c000c2e00640480e05003807141c002101e02a00c0b1010301042881040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 154938615 1250 154937365 154937399
    0x2001090f1a0c1206210304050418021005090102160602060f0a0c0f0513051302090a0b03071704020f13140903071e03182304050c1806090303040609 65
    0x31190700d25810601070340c100a0044800398803504451201207070f540c0d44e50384103403181007041701c8078040c0240c40c0d0418540c69400901c40c1078003880c140140b00351080f05801c042500c00e0350003068030007683c204450071103464100d41c0006055214a8440d40f441680c511f00803001810b4903030040491b450028984400c032032002d00a8101d4608003c0300d68a400c0e0083c03440f81703403454945092030320b468050300031010644840e445160011400c900d41e00410119400429a1500907502a18195503032440e0000c544801c642c003800140b0545040c1620b404034200c501d401c0341c0000d00b0401081035003800200d40b00da032104000092551488a0908440244180e90717024200102660038603901e80c0315840380c1c0500d003103194500703036010010f0810540583c10007401d1184920031504610340703400c103021010a40c100c0864000c100f05005115a02d80340c01000d100b0b442d940100d5082c0305184a26411000d100b00549602170f10074060020a0340302000548010204d59840c1c021035403900d00e29500c12201d00e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 154939865 1250 154938615 154938653
    0x70c08010c1e020a120306151e0503130308060a03120c05010b030606060702012102031e1003031b051c090314030307050403120e030a030e18162001090f 67
    0xb5840360020030b40101301000c0154001d5a00c0181848034001140101110b420401c0207907103080e80c12a0741a031003a4034807184050780340264030340d1008410664140c00b08542c84070303a07078030303500903100000e48500c000540100018049085881d1a550346143c104241100e5000080c1d070348164409000c02406440300310b103008d502034050343c00c000c00440c5480c80f034001e029051114120910400046424981c0e4144ca00c01c1000c54803130904002d0f241601c8404042240004422000f0031000c0380108078100440c3c0d415143c042042c80203105041890200b854250741074028203a192900c4a03440f0f07502c094000c0b40ea035880703a640342180b0b0040a504010190301240354800d00c100702d0303290303048021242035a030000f2a00707000c0e42039a142100e0340031812011a816024111303181e400c054001d18140690101121501045400d5180c0000243c0c2d0846456000300f41d42c000a07800d83d4000d00841e01101150031100121100e400701903400d40e04102e100721a100d080c104810240000f50240c0c3c0102258 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 154941115 1250 154939865 154939907
    0xf0102042c0130020907020604140106050109090e0a021809070e01120609020a0314060f0a0b030a060213030c0b0a08090607230d1e0509011509020a05070c08010c 71
    0x1007820f8285003002d8011042895080400603503540c07181c1401607908190300034140841d038680303464025140c00c4c080e60f04950301c0905404904400006001e02402c0d654182e50b000d45503494880790700080e09001c070b451841c84c0a80030444000d42c4987c0c4812446420811920090b805c26504561804140e640314146401040c0e00600c145890a00c0d140c2e00248c0080003c103d0004c140000744200f40540d00040541c00a0206407100a00116407548a00303c13180c01c000c510380d03c0c0c260090a0381c0c00541070796419003102c01d00000140007580070303181d80d12030074503219485616541d40d0004a6090b4200a0b070480010030701d1021160f002c1003242d802440007024240504000c803010f0711803400a940244425054403035680b01d155280296039121014071401e20030491024001050743c04108507000c0481c1c2408000b800c02d04c030500508010550307801c41048418030349201c240c020f41090600d4000c1000170414440804d0080303400320003500c4080000214440c483c0000f07080703468641510344030084 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 154942365 1250 154941115 154941119
    0xc030f07051203090901030506040210080f060405100b07060605041116080f0d050406090309080705030d0318060c080a06051f080403020c131d0a08090d050f0102042c01 74
    0x500490031100319041950902000d0303281c9071189003140110445076130030420410002080c40400201603000c0c9000366144501c46010000c2203c4c00c91040b20050304001a41002c41c503641080c1d40100c2c3d114080b280c1d010182d0340c84804c032400c3d680c00b801003610401c0d1562401d200914207403290701c80b5940504066032038000500001100749038401c0024001c3d4030049602000c903121442115092811140100070760f03c0d01d03142940040035603079030907000a0110500410a501c0c001400710599800900501041e40000c10881c0030b004c5c41e0325035160000c10081c0c3d24000890b94015000705400303d4540b60554584292004200c1c0c029900c29407141164114101c0d2803914120540c0d180c8240d49082400f13035990f801c2c2030b854108890340a41d0408480224814495001d500c15111081704000d003c80050000d5011980c9081c0900301a01040040208003d140303419801e09440714410400e8503020340381000c000342241c004c1e90210070341c0f03a45a0b816414205401065810781c0c4103048014580794 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 154943615 1250 154942365 154942393
    0x70c0b03130807050f0303010b0c24150307031505040b0a11040306090206130e0106030e011e05090709020a02060601030b010516060c030902030318031903170705041d090c03 76
    0x240308080c029000603800030b0344005101091122005c4075102c00200e95603941d440e4184442580807078080c040b5070040e03507086641b1a103003c60781c10007030341560707002c550325217540751024801801070050581c544900e0703c2c0000068030480d00c038039426009080001e0b0924107410000e1003e4401010460303541d241001e4250981e140c0410f4130203407034110344000368803061807011a43ca8400d1601c90035807540301e4640024501150400a4140c6c4d0250341c2c02e000e00941d82c000c09090340c0c41d103844038600c2e092882081411110380d6124139031000c4200c04485460f661102003c00300e2340042000c000682040c41040b44550300f6010b440b03003028080ca4128948526996587e0040c030542200500e225140d04201c469184640c20000312140c0081c00c1e29615448051110744001c074078001d440c002e0042e8404c851013242a803000001294254860707420145e5650300c04841060000d2003c4207002c028040418035103140160f00145002e01c1ca8046a00c3c1401400b02d03142c541225034a40c802d9000410802c040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 154944865 1250 154943615 154943641
    0xa12080316030b062b06030b15060f0a0504060e010e03060a05100b0a020304030c1a0703050702030a06020403111207060504050f040209030102120103060506031902010e120f03070c0b03 81
    0x800314500c41484941c032180340480151540959a95120501003080c008a81c00755a80385002e80074690100c5001c1c2c008105201510200c1c4406421410500c000505e402242841c0e070290043c000d15961516004010b1081241c1180d2403440014001060501000f074200e84c0300b0071181001d081c440384a600c501c0000303584510052010390103a07100c0d400315100d07804414100b4003801d0300040c202d850701e0160380002c1d0f90340c115101c10389140c80c10080000f5844c02d0300c6c0751070350222a110700c018500b4010380c40640300e43d403002d03c007207805209110a050208620344058030113140300e01005107000312003000b0001151203c1d0124a1650031409003044540d0b000011103040b40c40955404d030016521100250082c0104180d19401d9400058040c2c0031081c1d00300054160ba1103840104801d880c3c0d48103050b0b0b104414130551160300c0c10b00c1e041601540c0175107012a42c6a034000e000c02d82c01c4040f0341140d42403040140c064005a070010802c0000c0140c42400030300601a8514401e05500d0030702620701031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 154946115 1250 154944865 154944871
    0xc0c1209060703030b010e030f010207050709060609030209070c0c17060612030301142707020709020f041412010c0e030d080f04020105070503190207031703090601030b13060905010b0a120803 84
    0x303142e550505d0307020f264003603032004481d4440102950300110991007164042c0d4800a0226680d010b116030102e00080944205815100a9a664082c1508690900954250203000c41e801d2040c984030f0381000a03980311080d0003034940003202d1400b550400d50154030f02000644a6403040d5551560b0100d5040c1c008292811900310028010f07810720128045201a1200003842003203040101a0100c000c3c0280155070040005508860f000c1c4e5a40c0044800c0740a480081202d8500402c400c001c140101c5259086062000300b8020403518840840f0380ac444040c043c410100d020302c505108076103400e03c602c01444a02d0304129400d4034058401c05200c2c82c00420017814004003241c0780040c450104141c8848014240407100218003000340650703144c0301c0b480100c540f2400340c00c5c503180c1800054252800ba00000b00107111076403d55844a01c4000004d15040d4060700004090021a099010302e00007180104000a1301015140034015031400715004051169498201c11001030308100403264 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 154947365 1250 154946115 154946117
    0x2b091502090d0620030405010504050c09010e01030b0c1b070602160b040e04050a020d0b06031c1b032a020405010909080706090c050405010308031014100c15050c0c1209060703 77
    0x42c503000007041404d090b20030445018600c54022040100300b01d0154409070140b4019022188495895000c018101f4001d0003400070036010000100005144000360a81000d0800403080c204081c442e40302c02001c02c0500000466800040200701054041c00b8102c808000e090f0890300d8181440040341d064800c9100d5180843c5840c0f000400f8410240030341200e06500405881080e1500d0400052041c8203940540c424081d075092144060306030203000b10042d51a4490364403140c094102e0290703148503680c05406000c0201c240140651030f002c414442c81c0b981ba41c500745941024014003084a00580040010524107403071000480c000c0c90550f01010384c80780d0301103200c0b400c520745230750703800340d56400290040d05190010040100003805148a15940e08400020a0342c41a042049001142c9080d41103140c00601320084ca214100b20b151403801044001d2140c0c02d4140070b00120340f8100d410070303070207000891010340b02130090010800312400e40c00e1b802c3c01c21800c00000b44840c451248001c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 154948615 1250 154947365 154947371
    0x6060909090a08030f010918030804120e040e1b0a08060c031005060301030c030210021b0105160c0e041b0e07080a090204050c1b12090103022b091502090d06 69
    0xd001c44904010004000d50300c103946a4680c1081c3c515180000c0b0300703020380e045031400c10624914496803040000f00303854055032161042c5d103c0351109510035644070b075882d04000fa61310400d44241c59500842800c405040014014100303a21003103007040c0303884205540320340c19181c410800b00d000003504581000e12250010380d40d4842c0c28031403c210f00154032484c0c000c680480004148425540b099085a0003a2400c40c21000400327401c0340c440441c201c5910710f40f4500e40c00c09034203500c501e000e0304519080c001410498001a200c84140d0701c04c40d8054080180c94030200300030081c1e50741c56007840450048410a400c2e092041ca00300d580c000800000812254900143d02c42c80181c0082c03481c1d5802800811490401c884d03074141c10741c0201400002d5241030204e2861000b80000e02c1c44145220203056410070482d440118040d5200c030788402ca0b010040b007002588440400c52007030507540500c3c4005200700c1607182c00b0606006010032030744003074414040b03800386444106c0550030281d4448800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 154949865 1250 154948615 154948621
    0x2040b041401081603050d081306060b03010630020306040f06090b0f09040b010b0f0405040903080403081005030304030f0615121727040e03040e0609010801050103050a0b0a110d0510060806060909 86
    0x2049d04030351070640681030604113540080c49001040043d81a500165240c00c02c1306043d410300b92076400304001c804003800020a000c1281c241c0d581c0510303003221000304007050102c5006908029100d031a00407500f050703920010300c000c81c6818007288016071400d0b00c02089610302030726042c0088105210300180880c002074104011a00242198060680100100302e1030015090003803400c80d00301e80440c08224144003040d01c03210803a04071800c881c4018020f6103850304603a03800c01405207400080315a181c58220329804c07420800c6a000281c002c000b10001403a8150802ca92a2810389180c8151384000b0441c0152072040d4600a101840140780355401c0c4403d280c000c100108420204c44c0c1e202d0102080101c2c40050410a4900400d0704482c500c0d039a1362288050340c03c80e4820300c802003c1d0390001142c0d000086150b058113074410180200050103076559407200c00c41c0d900c1041003544440d690030410000021020624000d0041c81c58610300d58035140010410b540700702d00d0890700c612620400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 154951115 1250 154949865 154949881
    0x9160c030c0b0916050105180d0809031c02150402181008010c0c150b0d1b12030f110604030e01110106051306030b01060c030905040902040b041401081603050d08 71
    0x207651074480e4000c0ca03aa01514285007103940300c41c05400840100b4000183c001843c0d84036406441c20543d10314020290070f400d807010810040c1d180c1d4011107980406005a4245550a10400320750002008100020b2000c041c4001d0811500b0540d071040c65040303c06200150705d0790340d4051589152400c1c50340d002c0c0c880c580340d09080b402e6907214801c950b0038002d0a054441c0c1c010001420688207403241004c9400740e8903900c054030620204140c00c110f03810031000204050781c00840c0d1514010490ba00714540f200e0301c001c2101044101a40803c160401600c3c0c003aa20401c0c5500000c402c5010700118105a075000301040e81303500405040040340300140301808000e600c1400102030003010350070a6450303140c02e0b03406025130b844152850444100001400390150b4100b0307511903490fa8039140b10030b0030402080002c203007440c1d0590700140e642d6181152900c540c03048000c40c18032000c0c0f2000d00c0d0f2500321030380d15100d1190040b83d6000180041000010400500d090f17016115003081546135588504d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 154952365 1250 154951115 154951127
    0x232404090605040c050f06030c180a030602030705040e0a0c09030213060806180d0807020a0f0c090504030809070503150604050a0e070b130603050105010f080403090506070803060f09160c03 83
    0x100c0603241e6454081840100081941403108031031058844240d83d81c41070007000694001200c08420100003000341342181c001d00c003900e144040b001040403d03160340780d0315000100c0e00111000c40209900040c1844041e01080b00d00da441102500e0600480e401031400410504140c40000d0007405103803036034161324240f030b00068003500524040f04c1440c9040590a060106d07003070540d02c0503000700344024044034810311101e44610640c1e0000d0000c1c8940750384040881c0b0111109441c82904030101050004e858040c01d802203000e81c0e18010281002c0c4d44403410040c5036807000d4070907030081d10b1145900000513141e03680008202e030300040556600d41e4800c0901440250340304d141c05070300c8000c035044000c80060280300c61880b00c0c41111903110b46050b0201d41080c0100744c04640f00b44bc41d825558130038101d0039841880303482c10f00303180b80c3c0d2000807880503005080304641101000c0f0403c01c0d6410076040c0381300c80c441f00f21050400750030800d132039000b14110303e0b8418040052050086041c140601 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 154953615 1250 154952365 154952381
    0x5040c1503020909161b030507060609091703060109030201050313080a050a0e010201090804030609030e120d031401030206220b0d020a03150e011403071701232404 72
    0x284048820300c0d01140000c00030341c820440c0f64841c080200101d44040e4401004a1000350180c07552000041007585207000082e844204504001d81001228009a540d0281000500050001080440c02850444180803643e440300d9410403041c020000d0603039004680c0e0040701d80a0a02568985940ca0518900b0014000203814504005004036044d0b5107e0020410241c00359241511070100600490980345025030281140d00180000d001158656009442180c030a090a100a035105004a090110300403605215508858000c03484140c240c0590810f50002240c01200e5605690000b034850081011950000002e440c020400016200c7c42501811003400d03482e07129600c401e194000381d0310140a4000180c1041c0810707510848291404003990102c0074484020703820b0030860100f05030481c0e52207a15218180c400580d42c501c0718582c001c0c104511001054607400c880760208500719480803841c4078112281082070f0001c000e410040320390142c1c003000440f0b40d9102c000a024110700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 154954865 1250 154953615 154953629
    0x2301090614010f080102070213020c0a060c09180b060a18030f060207110607020906011d090c0d050f10150c2003071205070302040902010c0f08090307050609060d05040c 74
    0x551041d102a030300d516541c0c102d0341c01c40d504030750003034550014a0030b0340141d8070025003101c070324950f40703550f881c403078028010b01c04400040380c22811458403910245c500300022200490307400d860078407211003074042c0d8100380c000c9810b060180003442400320711603100d124008010031640c11418a24002340c4107015009503005000001c404e1541e08018009500c5000211514461641c1b101118140801603400c900e070020b00e201e8450740c5441c0151103d4403c0002c0601c03903010070000c10309582c0c440100500511520685680395150001c45408135040900000c2800a03003000301f11801e442d0562400a4464a0042007610000c0301d20940f041e0b04440390080c48000e00b012020036030403000780740008410003203088841c60341d45c408010613040340c0008080c280350440c8070140050705054010003495481031404d0b003465403050719100d01d42900b0b60f030b00f03da0700c000008020301c0d189010080480074040c00c41d140f40c070301040017001401301c0c881d401062a100c0d07210380004040c0140c0b000340030018501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 154956115 1250 154954865 154954871
    0x11010302070b072106140f0303041d04061d030703050c0c040905011b08010609030b0402030c040c020f15250903061802010207120209010b1e04060816020a23010906 72
    0x401c000240c056500348482544a101e440f040c0410009180601070882c6c955804401c14100c03140140034200708144032094140c40204000562043d071002d005074880080c0031080741034189442c001041d03034059200440003081c84104d9541108001c070440f140c0a80c90309206681c0d2410f41415420120440c0e66503501510b0300d2240030a1080640200c4440400c00c048072071007104044098600704000c2c041d402c002041f41505000041d440c0c00c005401c44e00050031104e0041140c000501540c462207000700c01600318a0944c054030700c040140c01403507000c00054404500d401107049000c550144150800410303100d42d0441c20501402c81c1901660304088280410303525242c5424100308072031000c034010702c595540022618403074542c62040c190f004168600591030301581003c1034105403075500400d04070f14100503620380084000c2c8000c2441d6200c640c200e2030098569200b01c5c00c030340d2203c410341d0000c6403c000082c200d0b45001002604c0304c41c040050084004000d4010000c0c41401803e10b85 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 154957365 1250 154956115 154956121
    0x1401090b09060a05010b1804020408100603050f030a080403030506120f0303011a180108070216080604020414160f020f010609050a0c02070b0304060f180303050603240411010302070b 80
    0x804002030340e21581d00c003000c851458407100a1981190803d01c0f955085450038000135580008200304032558031801000035040c141c40d0170081f42003c0c401e1900d681c3e09da030b031400c0c20000c1250600c15820342d14201e5014606250880d90082c180c040014401800c1507a603000103801075840309e1040c210382440b41c2c02c0320f1507860103450316692a40280a100b150011201e101c4007004025012580240d0b07001140811814407040150b0754520083c1c415010f500801c50080640c2c500e2030286c1005200c03c01c0104070908060060008503104441e10030700340f41060003000511001c00c800160216124600b051407020000c608a04220b11594104030342c0d400c10740002031030205608600d00514102004200710040c075001660389103c0c1d803050301c02080f001d000003030120302158851080350262510100b8a0703404292400c0358200722003011004030380d540060200600302041004019107481640c08404440451103148bc4d1100510042158a11602e02540359100c0d405940416900031009000c43c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 154958615 1250 154957365 154957373
    0xf09050627010c12020a02030912012007030507123011070c0303030f021e0a090e0606091201020f210603030a121802030715120506010e0d140109 64
    0x90020100301d1504000146100201c42040c480c101080e01251520700d1042c0114012070f000c3d4020301c4074101580014005034459403074448240020076400c1000043e55143e52004c1d00d460380188449810418007172241d4400039130400f0440b035003141c000d104403024800344841211340070074a040140000303000d0705c3c000e42d54880f51041c4150b6504108414000200f025800e158980a10700c40a8015202c1c0c84003040402c4c000d6014010380d01c1481005480d11604108180340c900e07401c00102166070f40001c0030a00306501c5040e50010740304005081000342012800141c0c1401071500c081d1081000810703181051000358101d5109000350700f881d6444441a8580e070004481c004414580c0072095400101545000300c00c95811280e6520ba8010100420221030001c18964a00e400705608002644c03000d0b80d82000400024080c40c590341c071808014101c000d0041c00020070058009050800b444450b03030f04091a40b80000081c1e8421101d424075040c10040740320142c2c4400c41a52070141c16500b40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 154959865 1250 154958615 154958641
    0x50406090b0f04020a08040308101a12090a0507090b1809070f06080621100504080301090f02041406071703010803030a05060f09010b0306060f180109080f060601030f090506 76
    0x3000003219100b04140d0410b0a010a0788600d800e401d0015020034005170000f4041c40c1056048080580800d40083d2203003040c0784204403007280313080d40301c20108a4400090008545030740c042e0811024020b1030707282c0e65419584584070b00499041c25181c240d800b805880320102e5040308140e00707210036218205148519260f98603801400b0940c5016440880d4083c002c1d88054094031000d000406101e140d180302503010440003246100c0b40c004d82d1000381e03030f0303107068050603006038010f9116595a52500c1c1d00301003200c2518501c400000c0c01400204040e00541c0ae5212000409441496440c2017919002c11384200070740b502030040714044008070b4031410002c00b5620a001d0220104455182c3c4001c0051300803007904483c2e444204800103021642d440e01c06142c0243c400f90030540ad1002c1000004850780008030544100c40841c4c1c55107816603807104124008054800150440c100168007243d00c80d400203202c0c50516466150525030245a64850b185064000c42035030341905040000942c0c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 154961115 1250 154959865 154959881
    0x10e0a0606081908040e0c190f030b010e032505030a0c150507020916020102090a060305090c091b030705091c060b03010501060504120c050a061716050403140705040609 74
    0xb603101c0c01d00703480e00600903054214203c5030883e400e2424240340903201d00302210300912007010354105005500e000340c0c44500c180c0d4559095265808503050b1800000c0072500da04140904100c00d400250910ba00d0114404841080c050a400c010314885482003e00301d41c1030b440a50188101c0410105024000e0303600310640c2c0b024031951024880102c401c48142c01003032000380d80000c0301070104181040035411464100d54900025041c031410100082080c5080d81c442c0d404640c0364000c103d840142070000322a417040481d8200c20908000384400e22000f00c05030032803107040340000803454281c003032030603101c071a01c00800040c010b4074004041c000820804000f1120542011030484a074981130260368182e404079030f00d06041620308040c0840300e424103001038400c80d8503440003040e540c4846030b2800140540e900c40920b1201820baa40c42300c0340004246040d4039034100711100c14141c1c020700300c2e411a07400c0148020f200c02000b07401ca00701401036004d154044e2419000041c0d41d5241e03000703240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 154962365 1250 154961115 154961129
    0xb0f090a030803131a060a050d1502160203060a050c120408090303130e07091818050102030c0c1002071208060303190e01030e0c0f091902160b15150c010e0a0606 71
    0x1220455000c3c00c00301ca17160035075007554803641c2d00d07130180582e0411a62140f12140a45040102d14125140c0541281d02079603000f503040c03a03070340704107015800d040000c95040000e0a500700160b00d044040035480d400b0f1001c0940c601c5035141c001c9018407013801e09440780d8440c0202603e6455a4820072056185024421249074003d81d81c000360f585802581040b044960b04201c0c1c1c440c0d185014035031b000030f261845049001181140800c404644244050751007910341e40592031352020742020040ca0450940c214040c0a03004000e01c00015114902c00301e075220907820418503940f81c44001909500036100044500780400c0029022594080500d0000004c20780301003050803800861640c40341095980e00380c10064000103550142400011a540b0010102c01c004080500300d198100b44da20240c84a5585485004d02c0028041e04600c07094004d80409941d845030614400464a4540c00030b0741c0d80c0c0c0b000f0010860313049146081d00002c1d41c1c107400c041030342c4a504051400c170000782150f0043e00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 154963615 1250 154962365 154962383
    0x206010e0f0402090a05061309050f0106051f0f030905030315011803031704050f0303190f140a0e1603030203041502030301230109051e09100b0f090a03080313 70
    0x1900203101c0000a900507074001d0710841e4980d60794129403004d0540a403c2c190001100c01410483c05000e10800c40400c1c81400600034100b4030b280720f90309683c52078001a11800700007103040c4441c0704180a0305d0610b07650741880744030000943d000381d000b8203140b800a005804000100111040c496131810f030048000d8a902004480d9400c90600c501860f00004000c1703903401801c003004200d02c03500c1e0b41d0701c24400c03400c4985007800c00c0705450070b58109403002d00ca000c5d10940d0030300c441c3c402c5010300f5218016100003000202c3c0c43c150180e540340805170104520f203551f09082c3c1511303101805400d070b080c0c0040004100c126521b2038025941e0b84103124004004001180d443e003010710101c100c2c1d0403034080c21080502ca0401c00e6504050341200c013a003906210b1688000a541e8a91403840c44212078046501c0071600201400c0c041c1b404802000d0355104800b080c42804006d41d1501514130f4400070329070060310b4440c100003080045100b6000078128020100401440c680310101c0584080d02ca1500c40c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 154964865 1250 154963615 154963621
    0x130f0501060f1205090c06120114011d042307050418050402030a17130b0304021c03080c0714120c0709150b0d0b100917070b0301030204050c190206010e 67
    0xc4640b9019080c4400010340c030011644030500150f04a290460b40000c2940c5445081a002400a0340090340318280b40d01940c0042041030b849841c0e0300c095450a0130410f5001c5000c411442950b0030300d0314a148115620800080c0040010024201041900704000c215042450014195400c14440e9001d1030a00380001401840c1c28001c01780265070140041140c03041c00d54514000d055001c0c40003200c4e074001c0c4818400340f441d82d08644001c004100c00c0583c0d9040500500400d40c543c18600041d2418400c0403d000036480b20314254800c2c4450078182e2201e0300343c5028462402d000907005003134030808010b6155142034400a1014480c0f003412110159900c19a640030b5070b0b4203041c0007a42c0b20300f61408104040d00d80c4000d06181103510000211041c1c624001500c0484d0190000c0025050b404103108001c1e125180807000d82e0031100525415140800c502e246200500009004a8a0704007255055154005907280100c1003807249280082c00074000307544000912840a2103d509404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 154966115 1250 154964865 154964867
    0x606031a010c05030d051b030a1506030203070206072001060b18030d0203030f1e0415111e070321020c060c090337030302070605060901050a060c020d02130f050106 72
    0x81e01042e6900901650422a01000000c001c02d0000c00101102100100005401c03d000b00218400c4007403800c0020100710a507044251124075800c00d005062040007406031041d000100b139607002d130321845c100381004024410610340382090040a401582404404140300e504a0043c0582070320711800c040100c015503007016078880000d84802e000d40c00c02c001240d41c0701e40c40c48100d40d015500309000c448a81c28000349c02484042280c003510b1000010001210b4080c4900501e0301150141c0d00d52810400b0309109000c0411503041c41c844000b500017058010140a5100c2c060500315801102118411010340e101c041d42c8116040400e50040c030000401c0c81c000c8006507281108050014809048444a19103000303400c860602d141d1101c4018002403040e8148a5082861080d07501584600c031528110301912000351205204443c110f00500040e00c904d2103210480d90f0310310b4600c620b21554000300b41074101d1113002030742100c030f114540301091b0b803590403018400b0484001000395a03a07900c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 154967365 1250 154966115 154966127
    0x1021c1401120c030f060b0102010b09070f050c151009060602070b040e0603120406030c020709060311010503070e1c11010801030803160504120b090601081207080a120606031a01 78
    0x544195644158005106503041460080850b600c500c080780706158407a102c80f0070070200303900b04540c051f841d620840402e503820301803221040c10586850078903090880020b00342004500d041c2d410404042901007282500704000100c040802c64900c4490a01c48004604820305000b0a0141b609203100090314070720003d01001260700c0d203040c140c00c02c0d0410020050507071000e8142981442081355051001004a004100510441d100041c880484500190400c0007503400040c10078a014002c101198191740b028a600100340b810541d41c1d514044240c84444d40b08018a801c40c00c0e416820034611080107840c070b03c042c021041458214070420044614410900000744a02014808118103501d007030391410440c20344e41881401d2949405040c40d1000708481d0a030340c40c41c6140d0a100d2099410701c801d901500700d09000d0000d031500a0107114451003078100c000c00c01040010403004240c4909403880030403071882001d00c0300303560303031080140507145c1500c1580074210035425400c00f40d80210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 154968615 1250 154967365 154967381
    0x140a051203040803060405070e0306161107081002030705070f231606050a0e03190b0601020316200603040f0302060610020c06030901090b0408030a060b070b0f060f06040801021c 78
    0x1181c4a14661740c0d40144406402e01a02031014444100d0002d84680c4d41449200e114648140c03101400c0d042030100244460505400ca101940200740207020300200810001c03180e204801015a81c1e40302c0350001c503201d02c6030742e0b000761104030b00d042d000c010400c481078600c40e44001c0707000c10426440100001a2180d44003110324114141294003007040500030405811008440d09140c2c1ca03000440c0082030070071160412210307000245c0c01624041000404501e80c108100f0306c01542851820700400360188088040076141200d0035005104c0134002100340015901c000d01210707240c2c01d1074548544000d0b8104401c80260054000003002030401c041c800c0c81030100c590090001d00c03540400c0c80101d07480641842020354850625402040541d109140107a102d011650794a1800d05009d20803034841c1d400120f00040704006410104480d03d011031b810150090341403d113a2622000562008540054180c110744080780006e0304500650207006584c400d40e650422100000440c0c90495000f0b0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 154969865 1250 154968615 154968623
    0x50f031903230a060b16120203070503120c1903090302010e0d090611070801060f08070b0301030b22060513020a1505030103140f15190908030601110a140a05120304 72
    0x41c25402c1c09104015060b0054103211002850035155012108540d018800c41503582c2a1003514204101000c801084510f24500c0618100403066850750b44078480d50b1140d40e058050745000c600c4003c0c50000301c480003240b400b04880d07090140c41001e0080c00d000d110590240d442c104100e285001c000c04c1040f100055640c1d8a0384d07a5050110035504c840e038401040d02c052003004004108807800744500d001512549000307458003031414480ca071030540c50b42c01c1403220810500c010400501c01100164210008051800703480c00d980a0782c00000e6a6181c000d42414185014403444c44002038084100900030366201c00c50030349451401c15500c1c500703602c041c0010030410041011079141c1070507190f041c052209803064400c200126500d00480d6001280c544e04000c1c040c001601303141d5840b00c29014141009000c285002e480c0c85040d400014112410311030454442070302e421040c080d44602c1540926030307104175008040b0007a40c48090540889003440f612003401800700c10002940d1140f540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 154971115 1250 154969865 154969901
    0x11e05040603240602070e010b0f090f12012a0302030103051203060d12030c09121214130b030f01120507090b0a08030304050c1e0a0e040807050f031903 67
    0xe0458224010110403078031a05100030a035400e0b400011800c1c3d0503004100c580e00038403925042c0500c8469800341030348007034900c11040040602101c6141d09036020102d084800c50103001225001c200c0c602098030340b012081d403030402c0303508604040455110303181c0c00c10346102454541d0200c0076422407100b80000f0b4015444515404082c0010030000c43d03111201600c110042e4040d5502c0001c054002c503c6000460703103800302e9440345a44100b252004211098841c0c0c500b404546a1400b64010b41210318200000d055206003a048000125095490314060660b041640c41051800b80d420940d0800c1c84690500000503003032101c0c0d0803841c8041d07002406810030a1a100002005010700e4040c6908a030302000c00062220090000d5803043e40660054400c13400d4420801c034040181103001074542e0640c0e1000c10494441600300411344070803621380310b002c0c0c4440c240640175005d840001440380c8902c0d403610141d03041c0031000d884011b8480e8138240502c2c241410580c19903000c0e003070407010004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 154972365 1250 154971115 154971119
    0x2010b01020d0e040f02040510050909100b0a0f0203130602012f040e220f0b18030403080310240f081302041e02130311030f0c060a0e030307030e011e0504 68
    0x6071030340c08440801c05c1910018900355030755010451007045446040d003c20408164a000c90501000c595440380598000340d20035800c0101075900c6e0f01884064600f0440c5404190000c5802001201c0c030880400c41951501507031100000c0c00b03002070181701507a844014651050f1414490b0841c80300d503022084050500d03080007240c001c0d042d001840f100b02080c00069100054002c3d10000c131405009644019500f086424078521105018282c0038403040d00304844c0310749400100035034043da40d03c280d80540e03946810403d8001040c0c41e801c4030040003c0c03203a070820400940c80300490666001d0f115000c5000c003c00c01a43c0c9824200c468070281c2c0c0e40286070b0801890035a01c014900404120740a1010300562030380d6080b40c02011180652188207a0244103001d241c580701e00851340100e008208100c00041c0381e5407600c8289d03d150f40194408210a03280500503607042d600304402800300c80e107440c070b1820010316015002c54071901240760b00404404004c16005205001901d94640380d00e428 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 154973615 1250 154972365 154972369
    0x60503060d030504050405010902091e10050a1701062601031e150f020408010f0902030d080714120a0501060c020904020105160c090b1002150c070326010602010b01020d0e 75
    0x24024207030442c20480304001c0403601b81e81c1da00c109030290521100060702c80c10780f04144040e8003139400b20f81c080031449444140c0c042e960049880100c101c6032500c07a883c1ca510300e00030746000140c0c0d03440140c00d940510000c5015a030080740c2400e401420310b2842441800c41c0041505200c080c08090300040ca510425078480c49103004580e4214490044032000201d0094810b0450740f46407214005250005003c00803058240610714008401c600b08214103030582d800030fa0380d4030b01d038903840d03043c4441180001c0170b441c0200c00b070354464002100304981d102c4080b24007003030031041101d030300c00070038544400031500301e1043c0e81060403554007a22001142c0c035035400648580e0040c0181c0c50040d0800103030400000c03118a88a4001d11102c7c0340410026074071810172640b414448440d00855220404940b11000b2444075107401440403007800d07a55540c0c80c10126003103210340c0342e0112080d50012004800303840032581541210f0140e070003044003403843c4d001203031258250b1009000182c0d80005040040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 154974865 1250 154973615 154973629
    0x903010b090405061b0903030d0608010b1008040f0212030f040302090c03040506180304080d02010203220b070c0825020a080d0f031119020a031b1a0403030b0306181606050306 77
    0x480315070345e01900b4041032400003441d50344007400c54089181c84003002c0045000074080d15403000c0301240c103d6403411007800020f0104c140180041c0140404400c440251b48410413150321504401e0141c80d500c42c090200350405a02c240b05c2240207802c0075001480c491a0182079074080c0c2d03409005003d168851003003501c3c644042104084050008100c000750881d2300700000c031504c483c1c84d000942c403464129201403128030150600c40300a0621401c940026007000681984454103050644002c0f00c00c0c2807050b00743c09400a443c80135120b070992124004030b040c008620451003110384454458803034034041d454200040441010550b031038003c00d49180250403c040d0b500100c1032049c10b200c1500140d600354034803d00c000002d6080700780040103041c0e00041c2c0e05000c000d422000300c1032040664900f00d49015070000c031884a0329000c0480c0c04c00d44650030600c040d40c0d0050403600b0714244480b042c8052101145d00410038800c02648411403200c01c682e0798121241e580321982169140401d000e40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 154976115 1250 154974865 154974901
    0xd05010e1e04120e040b030601120606080307120809030904021803010c020c0f120c090709060906050405030706080a0e07090b030f011811030708030f21100302130e0a05030903010b09040506 83
    0x1005d501e1b40204c003802e4500308030882c001e1607036000c10360134803845003070a404666403038100d2041d0750010007031030f40842c1c2221203868601d01c0503d051403071980e03103078407250030750007100b4156030b2142c000544040c81c01c11424072201c903000200e00810035280580401ea964001c0c0003110342d0410650208100039140c140768801c2c000101c0015940034103610000905c24907004c80b0080e021401001003172000d1580905c81101801160809625003070a10340000d999040c0361103a10100841c020024802610725080703a030342d80305000e00712407916490340030003400707441201c0c05d85010703118100d120380708550140120001605544180050030741c16494000c2c0c3c5083ea510100c0d0148a0b03541c0c0010440c0e0200018601c985a0401e090b440320340011110001c0e800b03046014021144100c14405c11007044101d48046035811202041400b40c2520310030043d01c551480b0043d81e0191589403070034010084002e0442000c1200200401201e08003005050802588c029142da807282c00041d9180f5150f00220030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 154977365 1250 154976115 154976119
    0x40636140106080f011a090106050f0d0209030d030b0411130e0603010905030a0305040309150516031107030f15020705190f020a060507060e06090c010c06020d05010e1e04120e 77
    0x20b5480e44a0300d9103458aa03c040b09603a01d0f03990384040c045c22150110040342d030381b60126904280795140a40085c40d500903400c441c40300100001d030810211403581d040301e5145a000d070681c0d038501d0010802038000c01504070140c2c011350402c091000c1600414003101c01c2810026030040c150303410040001048440108420b03015941c5a42c2e01020136010000340081c0d107038560300030819103400e24005000801d25402010204426041c7d2041e0310b0300501503818229401020b460100c1850404860701c6503540c2c0004024010324002105100641d184407605d14000c119454803c503015031400d04920800d0740103001c03500031596142e03407813480f0a0425440c40c010003204584505540018000006903400761001c64000500b01d07040207828060080209201400740510340703007400c2640c1c0c0302c0d589030b0510390400c00d82c19000c0d030030071216505481c10082c881000700810368540007681501d00d4203641c1c01030110701c4201d510700a0088802118440d40c0d00014040040c00081e000340c40080300b0300c2c0519 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 154978615 1250 154977365 154977371
    0x130803040804050901030b04031710090b0310050a02220303050712090b0d06030b0702011a010f1e050405011b0c2705040b15120606270406361401 64
    0x43c660384180c0754034060341c0a640a9126400c003450050501c0b25080d24400c111000e00c81042060b0000711100d20449611071800f1441520078070000382840d041a00006500c3d280005000c52802a580038041c002c0000740020300807140035203400701042c00c80c03000400152040040800184100350f940c0c2c080186801c050215035100c500c40f200e03a402c2843c60380e508580d201020010f00c101f12903569044801c07400200910980c00d907030446100501109070741407004180380004424881c40c4598440410104814400c800300c510003402a4064820b0a000425564183e005a001c1d00c00b100040d6610000c90803d50b85072801400c0845104c4420341d142d00c0e40100c40c0324000c030712405080e01c11449035801d1460f0303283c55001c0749520000c11001d1401001c8141900901102c0000c9240d0440d40403100045800c0d828000700c099440b00708810583d07205941c061008000c8150410041040410726008002c1e903045107054072005421204d542800c00c42503907a0200708104c00004003032171844004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 154979865 1250 154978615 154978619
    0xc03040306060909020f04051b0a050903010203100620060f06011103030702060604150b0904020c07120c051318110619080907090b0904110301092102060906130803040804 75
    0xc412605580c3c403a03485152102c41d01811880e003003505003084c001c1214100114245040c0382a00032401c08d000c2c1e81c07025000188140914050800d685a40500900030341d03892401c4001c011022900e8810400030826400e040c08844d2141c400b61681e142d8100010680c1d9505d14a0742e138240034010f03040c07a060015403002c0840b214010f00082d80729000a8000300a1412b00005100c00c44021081a503814581d41c4414400000800121a8000021640540c44410801c4410b0806c03609601100c0361012002c0140104120302c1540d50841c0c0d021120f5001d105540e9441c8029120301440c0d0791000040c0e0580c01c0002112ba9414544a15000d8051400d1a40c1001003400c1d1008800010000c0b921942c00c0101d80d00080000801801e1401c0302407102c43c404001040c1e814001170f00050494a8444d0002c0b02c1d600c0952054101c1c41c1c018103161180201011202042c01c0044102c000502507000041c40e580d5000400c01d00640d1425501d24034de5169869000c4280c001920440c1e01d40303020400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 154981115 1250 154979865 154979873
    0x308100e04030302120702010c230c010603052107020906060c01151e080708031b010908030a0f0506010201110d0f11040603020a020f0d0813031101090804090605010915050c030403 79
    0xe81d115601ca500e006950f4604403c4162695000030b02e80c3c4116130401c1c410b02d030000d03405110410589920904881c600c040254001c0c000c0c060382400407010740c03800301b001050020000d030011040c0b900180035004041c200c013500d10030b0f02c104032019421003140344c049581c46c10124000e001040f49034000003002a119980e00344014001c0d80401071500e10b00c01d00048103058101c0c400b0007011039800404c2558071b0421071035100d024044145038541c41c514441e500300e01080d00143c3c00954041d9841c0d0b544c0c0383c0b40039410020a800f25500c4042c51030140000e00d00d5005204403401c8448901d541c9042900780903c030f2015204103010071446a0b126031802214130403100203040034019030b48001d40c03104c2045100a103000030700c2c40400450391028074070f0088203400205041d00090591010a80140700d41000d44070601b0000030b030f82c01580391000980510030808050f209540d50325400303000785580d03000116600440c0c1e0080746101d159864000c150f507030282c0000c0060303603400c10540342442d54a450b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 154982365 1250 154981115 154981139
    0x10f080610200706093807170a200604020d151401030f0b100e06060d06180603050115080c09040507030f1412071e0501110705010e100b0904030810 65
    0x4882008074031920005d021a180000800d4038510b180381e502185072840e5252036014907002074501b05c103540700203038010034082150f400c403040b007065040d5555600d001e42001444041d6070707642013416030618024040200e10100e003050003150024022234901c45a5100d4524100a0301d4249603066500d024444d984d14407203640d603009500403007228002c80c91904141c89907441c020041c7c9200d16403220203200281030b511040f0b0f0098000d40766588c88160280c2064000c01c070750b420840f8449000ca80001c0000f0258010704c0540e48143d00a020408070090070303580c081d010340511061500074050258a82c10142c0400f540180108101d4240c0ca40d00d4442e000b4440d09054207556200a4071400075054404010700b190703525402c107401d0310700090b42d29a0020314104000703c0c819222141080014403500f50400c01078482c810002da40d440c0e400d890181c1c020001d243c03c244036030041d602c800304208802c0c850146100005080c4000b15a92a50100d4650344020540081c546440c0710111342051054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 154983615 1250 154982365 154982369
    0x6091503111c0213230306071e03020d050c1306030605030a061808221a0d0f1407020a020102060a11160302010608100e010b0f13020a05090d030905010f0806102007 72
    0x2214017001c0300400701740c0d20811400c1070302d02c0d0295004509024845500041158880e0b006481014134901d044008030043e1240e9055454000d040100b0701904002d02d000600342c110120302d14000e002d5903084180d056a10500c44c0075855049640f804020400640009100c1004c0c0394080e60010190b564200054000d070380508010b141d810303058105601149000400b030141110445040075254900f823006204100e80f44180e146c450f0801078850109402c4120180f02102e0b5010b140d00c4c01c088000d40e00e2821840c164014403481c404076403004250b108600001030940a20780c82d00500300310311030103144001d600700d00b19940c914002542a13402d110480403d80080c001259059407000c0503401d403000500b81d5071007196401000c80e02039440e00801300603640100805a29500009020703982d40c01134124240e00300d025860144201a400b011010645a090304c0e8902001140d520403190503408079661134118026099070403100e4028440c0c0c005065803441e020343c1c150340c9900460b00b082103c1d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 154984865 1250 154983615 154983629
    0x20c0f0613060207032d08220b03071805030703020402090607060c0e04050a18020f01020114040602040e0f0c040b090a031a09010b040b01020715140406091503111c0213 74
    0x140d13000388108125416414a1701c2e2a034144001c250048082d0480c1d10b9103050b00082030380c800081d20703110300c00e803030303c608110030360000e05103941541d4a180b44100f9510031078032400000c08205181402d0441d81000707105444005c0d00034010641180c0c244002075104032402503100c00b007804070320700044050051402d0f8030311558940409181e50b03018070080c1c41c40600760205441c103081940e140100a000450111a01100d0101d10043c419005074010702a40780c0e00d041d02801301c0100300a0218a4000308100c803c2e50540b001d403a6960140d6188041c1c01b40c42e11036041000300070170130035601c03502c02804401d00000c0019a019035a030717840c48080210800240c1050b188101001141c0500f0b1162010983c0c00381c90901c090340300900000d4946201d4000d111004a031100c030b10132a103102e031105018800f003a00c1415980c43e01e421010742a08641d2040d10045454200110700d1203121703026140e10090204440e07810301c281100c501c0e4038040264080421a80e003408405175400c80703925603400030030720 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 154986115 1250 154984865 154984873
    0x227150c0f07050607020102030a03050402040f14040209100b0f031504022116120519090b09010b0a030210030209010c0228051906081f03030f120507020c0f06130602 73
    0xc80c0360505101ca01d5015074130940d4280400030240c0d8012088859816031454005040d55852001a000b0722103003c440d49102c1c40c103a6600032001200f850940214003c4840a1980e500c01e00b100100b402540078203520f448060010405464914000d56003003221070101e040c0c000c0c0d0103000b041c00c90b0480d44800616101c03008442d4109a05107040c640c00c2074000d0340e290851301280c04081c0c9014540d440c011003041d51900003403203d501c5807682941c421801281400b90114508181c80d00d004151841c5200d0f504c1e1810120381441e060030028201c03540035020034000006e10605800039000341d000541071001c0211200c0042e070b90310712003034000c2040e00045028420546171a107030b020055000b03580034004410107807000c4c07034000c9100c0c4c088130410700e0040000d5544805a5130030001104440401c0d0200441c04400c00d90402d01403480c9001e26505d4012480480341c1110960354244e416501681024800000900300301c0b51038075101e138000d00f003245825a00a0351200341b19041d44200e005801c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 154987365 1250 154986115 154986133
    0x31703010611073203030703080412080601080609071803050d030b010302040503032515050a0b0f0a05101106040b0f070504030c0b090a03020603070c0303050a0227150c 74
    0x1400890645402101e10010440c1d00c1c10b10076010602c139442c1c61500500e40d0401c1e04400b040c4139010804210750741c00340a0313944842c828a40031b00080020746080b910000d82270075900401d485580030300c0c4600f005a543d84999140d180500c029540301800d01d004000c14401040403000355401c01e040110b01c0740c4010047d81d02e002c0e40060864010910440c100742c01000100060b50700003081c2c8841851555500150071079001000e070340c84c501210010011041d40b89805020300e80c41d40058800e0795075120a01040315070500708003080a00c030051640c440301600d400c0c00241840a4821101c600b103082440180c4540c1a00e645000e0007260301301e13258517050082000040340c01c81c5490300151a820098105400c65550b1903142007980180c1c84002c0d40851406076540e00c1c8003080009580240030300e5074a003000103000740803203c00321007580881d0a20300400d501c00c600b44212241ea00e4019140d442c2e4000c0c8000c0091000c03401c00305190b10104c401071342509a8207800c02030100c05d6040c0c00401c2c0500c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 154988615 1250 154987365 154987367
    0x20711030a0f1b12060f020909070908010501050406060804060f0609020d1a0319110102070902070501020c0c0a0503030909090f07080601060f050a08060d06060b0307020336090408040317030106 85
    0x1d0003099090300703d40d0b8242048500554042d000c600d6038008404904034440306003640c024041d8202107540040f40c0014082e01980000c0f4140c241d5190800900240e0380301d0302840107446284c860301001410b22070000f00803544c960b11a04509100003c08220f95a07a013000c14166002070440000c410340e540510b0f020800d036124018810310055001c0d18603100080c149002000c0801806003260002403240710b9160310030b200c0407010b014608070854460a050600314000d400100c0405014454040308100e9850403640050442e000240114038050301c410070701145a10185c4040021721a0705026041c0303d01c2440b140c0d0250480a0042c44a5854400028071110034144400700313028082003041c11031907202c1202940300b40f0a8502c640b4004c1c05180c220300501031503101182c40d050200601c444168040000c143c0b011074000e0941c140380d510074403118403421411020300c8140d04a4a201207030b08002c1c3c10b00d40d12030b0081c0e00082c1860b03501e80b1141403c83c4520320901541c003000005211007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 154989865 1250 154988615 154988633
    0xb1605010c0509032404080703090b130905130507050d0c0e010b070b0f070c3305061504120b18010207030c0215090a05011407140304060f11030904020711030a0f 71
    0x700701050900040c200503c841710b002c00e8000740001d4003811000440c042854011030104c0700070455001c0c082d5450242404288111000d0300078920900c0c10300c0701144c200f840c01000f01124a8002001d00700440c60503040100c001407400044072200031200c0700043d480480003100b0300801d03003840c41d613980b58940e150070240f4103002043c540d1391141e64024030121560041000c40600d40c406d81450301181070300014806003c403800d602d8065000c02c1c141e0924451030750404d40c09000c081c0c400b410321142007800e0340014040c1d03004422010440000c2c510200c1d01c000386e00e80d003101042c15601c8101c0d2109400da801c0e6031042c582a80441c43c02c2c0034020031810003101032442c555000c1c0c001c50602d1500000507041185034440d41e81040018103040e54100003800848026550001d007030680c240c08050ba0980382d80191140a0128204075882407605010342001480b00c10024082e514002480c801c03c0000c2d00945800c1d51424080800c4031b038185c80822100318880e0040c41e00a6440e001e41c50914a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 154991115 1250 154989865 154989883
    0x50c030606010f05030103020616060c09030201020d0c0206030c030c0f0a0908280b04060e0102040905041b0806010b0a14030901050406060f0b0901031a031c020f060606040b1605010c050903 83
    0x100303d10002141c0340b540e4000305480c1526411140300381e541c1410365121034071201c0c104001c0c060a107444090030300c0070b81214031182280c0c800e800f41d4000701c0c41104156400310b000e070b5020f90052408c100040454988000031580610009502810441d40d00003c0e500d6402800041010400100003484054010002c03a4450f190410100815000c1d11700071100c6e00450311001084002858040b40410901d900001c0d29861228021911999074a000402520060318240d40e04046140341c0181091000c1c0c22005a404000003400e1991801f501010558000e110410400010110030550480a1030045004140a8002180328209418503038100c2e46140d005905030411541c041214445000580d1580f07442402c00140107004075005094642000500c541d05000c3c5070300407404091219000d442d8007103281d01704c54550310394411140e500c003070950708207501002c180001c010449140000b000791041440391194100700603902c072425500d41d03003601000305002003480445804c0400680c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 154992365 1250 154991115 154991117
    0x3010602010b150f03040302150a06090506190e040c03120306051002010e0d0e01031508061f0e010b1c0c050c190c140612070305060a06020d02060105060a02010e0109050c03060601 79
    0x1214554509a0703c040d11070103007014062240400000c0a050090010b524040261000c2d8000c92070002d8844004041b24000c41c03401c1840d00000c9209401c0200460034610b860b440005a081e0a04030b07000b518500007001111175002d092000300020b050b900c96680407001c2c43e10086201e178101030420034005000b030050b804580c90701003441081840020f000f10104460700b007040300c0781000d400403006080303400c0c0c500e481c103120003c001403280d00004125126040c0d8002e01c44414000c50680c4070710040c40d05c2442c10b01290100140001e0030f2900051a0311310f8030038103c0386009050310720001519074441c000f00100300c0105408101c03280c2409400700300001241022041026507944100c40407441c0144901d0441d120094144c0740c990703000310388010490340504012450300600003000341400b207842d86e0092528007000103100b07000080981c00b051007a009000968203143c1030188542028101904540d01d400001700d240d40c1c2840b0f1204490300607001340c14004451001e2500e031640107440070b8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 154993615 1250 154992365 154992379
    0x31e0901261906030203010e03070b0106091d0a0221070e01050705060a05090f250e010308070b0601180b0d1d0a03050f09150c0105010504020301150e030a05070b03010602010b 77
    0x41500c2011404035881010002001410040b80340240014640c03a04001d41640c640301c3d111346a00e00010103840f2643c82510089150380c1ca4840c100c1c1c0003421441280884281d00083d05810f104030482517a020700310b00740060821b0860082070914104580130300c042c0500203014480c15580c006c50070840c202080c24891320b00741d515518107588920003041c22410a5072740012a901c048148000b640301d42043c41100c045c1012a054059009841e1010f03903903000c803280001901d0903c80e4041c3e81200c0d0425482400c0c8a16078442d036981c680300605850401404611424440a0419525001d8180c0300c021a0310750244900c0c1d682180c103840d0541d40112800c079030701c1c901504000b500010700da91610300a81c070784081c184100202e00803940d0030f40e4024410b181d600001c00980000d881542d040313400a102d140d9941003070208a11082c0140c8600307030a440d500319036150169060700101d60000e42141c01c0750713885881d09070400314a074002140c8060008010005594240a220840704041f5191 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 154994865 1250 154993615 154993667
    0x60d020a031401140a060305072007050301092102010b1e0d080f0d11070b07231209010b1012020f040506160b070e010f1409040c0201020d1116020d0203031e0901 71
    0x282c508083c03e88002c00c02400742d488006008418040702c40133010140003441103c0e09490210420201400085003c0003c1a224007415205008071050715801400d1003a010500d003160b07139511242560702035006040e4420b5080043c1c4080700034204c4141c80100c140d1a0802c0110010642e6003c008003007240b081401008040342a45c4803ca8010708642408200606c517041445100400c0c05000c5648080214a504100c0200328a00b44120b403088020001e503410f40d010040c2c251052030000000035007481c0016003440c40e560084c01c500c480c12076854107240d6100001000381c1c0c010201c01d203800ca8041d0200d820071500e40f08047c0c105610f824811000309481c40002c00d170000c150000c0d01004004108140c68821600440301ca943c3c010b00280301e40c0c1010b84d4068041d61204c510584114070b400400f070303401c91900c0c0c26a0044600d00700f441078081040d4081240f100350b10042664140004c0061103501802c41d948c6001c03800c0d00a00b2503450340c03801c2d000034206e801e4406089040602800300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 154996115 1250 154994865 154994867
    0x608060f0a03080f09010c0c030f02090a290303090406181401030807020103020304061409070e092a19060903120f020309040f0e0a03120614060d020a031401140a06030507 75
    0x181e4800701404111305484800d80c0d0700480d070201260401400c240601003011090000360241280b1003030017646d007240940c41c1d046414085803091a0b24060400003580e986008503a122001029041c004046034140192803001608841203030703102c10124034610165a83c044614020050030914141a10f809585961030709900c80c0306004000341015400030002c1d0401480ba4005450040d0792601d0502500d400840c1c15601c7e4001c0c01307900c02e02e1103001c0005215242c00244d40c4002d0308a280280001c4d1100035480024988200e00c46601085844852546401a0349100b00824650f0703205407299185040c00100c80c0701805400c4200314400ca46001419000400c4038039004c0c1c19a4009401a1203108400052015050315042e60003002200707014168004598151204034643c1040717803a40c1c403483c01d40c404803140045500800140442510f085c902e9019020b40003290401041500800201c952682000d0700105030401d5242000f040604181c00f108014000c1c0b414100020304001070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 154997365 1250 154996115 154996117
    0xc0c0804030303050a0615020a140105280f0e0d031a09040311010b0901060c0c080c100c030219080705010e1f110408010c030506180105090408030c070c0608060f0a0308 74
    0x406001d054888005c66102c0d2000d91080008010318110400485004a4029101c12810030140d81403448a000d180352260181700c0c0a0181403450886009502d83c550b0703003450701e03c00304080904d05036104203005c500704c0c040c01803034030004000015050b10100780501a040b01c20f003000800014070507010b0030200c1d407100e4564a800c540c15090070480c011580e580c4d5405803606a100fa60494001400040c02d145c00440c1e03050640d1103010517504594031441c0c2d2507a600d005130075041c0d00802003030302c04501a0040b00c0b4030400360301901c1070f41d150b800817036000c521321150303d541282d4285000403d8000d116082c46180c11100c4041d018100c060b0742c6030074880310390800c21628034102e0340d00d160305444000c0a4084400802c2400f0090021841005000d0001c00c0115005130140040c0c5508600c441c181c0c16140d816594028400101d588544e2161211030300014000005070204004500210340c119803a98001c00ca2640c40541501e402000c0c03010041d0000611801179031b2080060001401c910 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 154998615 1250 154997365 154997369
    0x1120c05040908071704061101091a06120a03020c040e0303280f0510080c06030c0a12060e040f050f010b060711030703021f08010501050a0e010f121e0c0c0804 70
    0x7600421845203d0420850a202d41440200054094880070303135121101d00152041781c2c10f5403101c006049101003400d090b0358105000a1a5444645014100e050408a030940084001e0400601013080041c0149842d4007101c0540c0581e11209460f1000e26040c022a01a603100c040a18194141071890b103140c0048104802c80c0c03c0a81400854402d4007a40301e440440d06080c014412410f109004801015a074001c1c65054001c52107400c4a9060107421280214401d00700700c1e10300502c0e000c1c00c0317440845e200c0c1170340016034440c02c0010710243c80b4070526011707900581035003502100b10b20300b0b1460031140380c0c040000c0783d0414402d945143c0e80c1300140c0b0031450f00090302440802c21480028107003445500003d41c0041507120143c07090401d4a81202242e00d103171664141640c0700c10042d0340074010008104002100c00f201c40e0407a5100c1c403110904200340c1d05060310301040f4000e03418140e46020803007402a100d00000d990b50080d580c00340300b4041d2000d05101d1f41c110740340d0711640141c0c03060f8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 154999865 1250 154998615 154998619
    0x81504062712050c030406030e0c0307050901031403040f09020c010606090617041109092410050d150c030c030b060a05070b0907090912020d0e061801020a0c0906050901120c05 77
    0x1d0540324042c68021012074040307042d2001039a40e140d841d00d00c00ba0041c40103405000461003800180c49140c14001032000c29520010105062603103103544180e03040c40c0000301e10240e800240070010780c2640c0782601780041c144c040000750700c40001c80400c03421a0301c00d0740040100030134000104000341e04001001040d84009180d41c4656850b42010031884000308c2c403841d048a37070941000006040030881403070440380040384100f0392640d045610070b9088161040b10210000c440c003080704d4540758100c94030071442030500804982d1314005031403c58030140321b42d0010a4440b0303c51302d001545445648440b0404030b0f12281803200800d0018864090050000c3c0214000000b243d0341c10300400c0710100130035a2840600420b0300c1d5280c0444407030001c0c0304c0d0001601c100510710f51818020741442d0701054003d00ba05040c6103480c5640d8041140d1000c4d07940c154095401100301003801c041d0001d01a201c81a0f000c03440e00d2030007040c01622001607000c03902c08140d070441b9034009400b100c8164100c13501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 155001115 1250 154999865 154999883
    0x6041a0618150c100e06070f0c2a06110a0308040c0305070609030b0c0c15130b0a050906060d030c02010e010e04020d06060806060f160305040815040627 67
    0x206542a010310466028459072212141c207580c040103a000703004100003054502980c2844d9038444282040d24140403542003581c10880c001852144109283c3c60400514070f001e8444034810f440e00720314409a661030f0344400040b44610200700b011000384400408091800c540c00d01c07908203d050b1181c4007440000c00b00016400414140200b0f5181c52002d1350300710095445031a950080507140c00c42070311040380d904503a540010042c098020a941d110114900a4182d406410309641e42400005141000880701c40d45a8404222061292486002e980b040014203082803103a03c2e140c400018512032084000650501c0040c0e840b0b004400141c2d42070810001018030f807030040e00c100da02d420240d80c200d8404509000960b07060b0b0844001c591041d15603034141d864401c00e0203d640b062911845a1101c00c01c250791181e191500360301c0c3c1e014068a80542001e840c1d080c0c59040c45d400c00a0280b400005405110034070034135124005045c004141680030340c40d00d80b240700034140d28241d0b02a1505030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 155002365 1250 155001115 155001127
    0xc01020c0a091503020303030c1c052205030f04090e07090b06040311040908070501020d0c08010f031104021608191d0d03020c0a1e121a040f0818010806041a06 70
    0xc81c07140043c0145078000e080da522460071200c50102d0f50007503440301c1440407540b5100009011181b081034010305c1403c05100303090039138003a4002021482103048803148810042c00c0d48508403a00076101400c3c003c84040f417400c1501000918143d09900300904061500640e103010380d69402c01c48044a03030280920440c5103580001030000e0a1641c00540741500000f8610100541940105189040c1c00800c214007100a181103a0240b82402a49030b2286101e0042c80400e19018049010080090000d8034050031145494444003840d101180c1d05c45001c03807480c400130301c500e802c2002d5071304d07603d4074100d4003488058401441844000e224007401089a4001c1414428824050441c2010b44102202603984600c0082d1030201e444011a1100e007000c08241d88500380d501c040c104e40c0102502d4210502d01c8101400c003d009001112a000154441e90018482d000985043e500c0b2040008413803645400142262a00504032482645004c0215600707124111001501c11025036000c0e0f1144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 155003615 1250 155002365 155002391
    0x14010f180e03070f06140906070c1b0305010606140a0e010c0f140313060534060c020c1e180c0f0f180a030b0403050a030f14090c01020c0a09 62
    0x720034014840290300000076110140300c40003902e1461684100c004200f00c1d9115140c5a03881e91082d0303101f183c03c1e0019000300d16001e101e80c41c940081801807001042e003d02405025007030310b020750710490702c59440d450100217283d045802644002d041540c224517040745100d000f04401d85400c4110305014050354104140710004c5040002241d106010016450900805550301d82048030101c1c0306200300c00300803c58511542c2510000880340c02581c3c40c0a407071f040c9646214070703089143c1030080d0301d0701c2120020035480d000c1c6100d2102944c01904021002d242408240c11009a110b43e04082c00d0682c0c4107681c48642c0c080d90940d0280d40100c120f81c5a6100340d124500c6403015828400c000807924081540e0030340002c125602c21015002d0b01000b0213401d004494a50388005001c04102d41b00040101c0d0142004200d0b59003079190011f078409075100b0200031176505150300400110300b0010444824810050032014900900003020aa02e503080018610880c6001e410740041e29812128048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 155004865 1250 155003615 155003621
    0x81b0d03050a0c15050910050106030c05091c0b07030e1905150c09060a21060302060a08040201031503060b0f0312160c030b09060a061e0e070207080106140414010f18 73
    0x10360f000c02814841741c180018000d983e04048801000b44a180c20000a11940a4810740800301480d444050404180300c040044031000b0001d101b44200500e1400d10020300b5209200344242144e0728002449036002030250b00d41040650b90034a4504810444004504001030348110030b03000c0c7c88800600d0b80ca5540b42800b03401600605a00b161000c41c80f916006e80001a00001c010080c16401e10020054822420703242a4030029410500820241d0000b510031509540d1090040c1004242c1d045200c6080d0040c000740c1c1e100359025962420303d18120314005030304d8526035500701c000b0090666000c0e000b0365644900c4d8134581c0c01e1100b0700b0405042141d54a00a0011a0442400701d0940380c0303580526155032045803482d140c43d00d408804103035a08410042001617040c5c00054175100d041c1040701615440240c01c900552041020008009509001e1740016008041400e403500000b6418001591136402007002210350880060140f148241c401a0440c1c048001c1480000c110a10f01e07401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 155006115 1250 155004865 155004893
    0x705010b150316110d0f0e03010515090a0b0603040f020306070804030806010c030e0a1716080d08041109040303020901020c010302030f04110a0b0412030f020a11040203090115081b0d03050a0c 84
    0x183c010480c407445c2c02e98204c0004581d50310a0b07162845d00c2c000345420142243c204551401c175100c2003170010b82c000d003492070711641d01a1181a0010b0101500d000141980d0400c82d0201c40010300600c0000440c2800e02416401070803c0c00d01070814141355501418142c00204030f24104620800c0303001c103041c850005800c0041c00900241280f0340c85404025a14000000700741d0070780305440005100140e0728241800700c82c10400a4000c80c10300440443c1d00900151041c0e60340c2080da02120500c0d0740300e00c00c20b40035504c03907100140d440340712030006030400f1011511507040c1841441000200340302940510b034010761090301c215178003100c00300181050b95150016031041c0d4001c14081414034003880c410004070b0007902c848400389250641242d880d4002d04d001000408003800319841c0341059006507400c00e0410002060740101109050398190311a40015401c1c1d00001c01c40c08012001000c8040018040c1c5007282c1b41c140d5a2809092489110704010400603014000428411100d44c0300710 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 155007365 1250 155006115 155006147
    0x10509130b040b0702010605122505060a08060a050f090c070f050a0b01030312090317040c0512150604020304031b0507090618052a090303070b0c0705010b150316 71
    0x3420142000104140c0854513680590310303280011a03140303824000c20001c034403050010070000c140782020b043c01c1c842c0300003189141d00105001080655506000d01083c0c007195441e1503491400c0e00030405c0448090b0302c901d0040c048c0c00000c49064441c3e031038003507008500c0485966030382a180750500c5007802030740003d000d60207242135507802c00c46c1c040e04550480780242d9a032070814a1120220381202d40b480d2004001ca4074201d40c4d6108041f90800456000c3d006681d007a09a41c0c1d5507022403084c2d00d02c840b03240482e8002c001511042c036200504181c109005072411402c51030107503400b501510880c11340b19140c3c41da41e40d0400c00c01c60100188006004801c0f002d200e415034805440d8002c01480594200c000c0c200400146501d4060034404881451003042c803800e1a201c02400205500c82c081c0503805020412035140458601300314180203104141c0b815640d0000c6007031050071a001d0030145403050740081040c011203d80070007680d802803100f100b10381c4506c42c11101511143e040c0f0190f18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 155008615 1250 155007365 155007383
    0x4050a0807050601030627060513080409020406081b0f0d06031203020307120c0801050d0c0b0c07031403030c09120a020406090c030b010e090412090b031009060501051201050913 78
    0x8000c0080c08030701c0300e041781e10420003404440c8a121601c00c00c0c1501c485800b50350340095010310041500c54004582000025480900c940d2140c2ca400746d05a100f908843d0710705400090811501d43e0107030110354401c2c0080b8051040c0e0341c00340c01d880054414030208154080010520307014256584d070100000395403001941c01d03041004032015000e500100d44800101d058124007a268a2007070089440301c800c41e81d2048801c0c2c1c242400c018401c00000401c0c0c650f40404c01e004603050365088000c100286201c0c0003030244034910718080b102d01000c0340001485800c280f040c04003d440e864140c8036404000c440d28940c0044480e111460038200c0d4402039030040c244600002c5034000c60384101041003c50307074140041540c0c04c00540300c801d0741880c13280c0c211020200003404155405200c0000703003030782d140c0300800315901d98454045820644040b034003408650340070002c122451244800403c800e08045081c04000c0d2140e010341281481964060800040011a407504036140c098005501003114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 155009865 1250 155008615 155008627
    0xe0d17251101080a1505060a0c1401060302030d020a1203050a020c25090204050612060a030c0e060a06080f061e030a03180501020606030303040f030c0210050712090f0e04050a08 78
    0x486050340001c802400300354104042803c9002d54000c00d200d103014014004111440c00d8240070103075110802070700c1000180746a00300023030120304900668002000010410509500405050040d00f42a483c1994030507a01e6400042c2e07521110504d41096040c0000e5550b038418a40019114108140005000340002a400d10b1409202c800040c1c0480d084034000ba511000076608910503402100d90091051143c001c80c42c0894a00c03580c4040c01518003002c49641e6600c0c43d01c40c84894100c040c000c004182005000c0c1016203508000b00800e04c0c00d101070303003080401c03005092009017606029041c095200c0e0a002d41e14400f400c452000030b13040300e80300e080034280100380070f0090b217205080303007841640001d0a610000d00749000c0c88000700658919201e5546400b541643c9181c21410320150027104c02c00350b070329418603440a1089403201561003c3c2031800c0340d44c00c0c102140712010310005500501540380064207406c10740790301410380d03e43c0b5216400c001d0318007501c24070020031a810000348 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155011115 1250 155009865 155009873
    0x92503120807080c1809130c060507140304061b0201020708030d020c010e060402010e01110a0210030b0906100f140d0905010903090f0b030a11190905010e0d1725 71
    0x107118403580d05540d8225841e2038890301ca10103440b40034502e0203031202d0815080c0b45442c1c03403a00035400180303083d8000401030301640c541442c000e20340c1c81200032510200d840340c01e010206010b00451500b070006075140908210000e000c007245d00c0761203544600303080140411640200030583c090441d9078116a118000220008065400480540c2c095400d25107401d07000040010120700640c0c1c16141e500072041880011203c46034118201d48041c4140c41a003400b5881c2c031007452500c07400c143d5020480034400000d205400c0c8010b0890390203165030180d80c1122690104100d01043d0152400e24040c0e41c813102e006200303018001008102c1881c000a00b410024158005036500c2e210762505820340c4e40d14141c881c54119607110b070585080d000c00000e0840701c0198496034400c064404032a0400f101c4071400700d810740c59410f544020940c0608140040e6810040050343d031003081312400e42882c0e4513038460008105c5060007818489011841c8420319400406814035072400f01410f40300c1b4811428 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 155012365 1250 155011115 155011127
    0x80c0309060a0203060607020a150f0201140a0207050a120207050108090a03021b030309040e06010e0c0406050702010e010918091b12200306090109060b0a081902010201021b01020403050c0909250312 87
    0x3150b4000c41c242f03e400c40134141c018010340f0f0310002c29915044251741e800c00c03c600694402c02003110180204003c1100151403800c50a44276005907000306481824000003502020014100b0b5a1030f030700460050340001e170f00040344d10240355103035a00c140d5500c401011034a140101204c40740d100b81018805040c0150000d80d0354102c44020410b0401c54640d01e100e10701c04d1103039001c0d0600140d02040041d015501828495041f10418500010b8440d42c50701809143c01440030b1000001c0e84408901b000e004201100c108121000c1c1810030b031851400149003200210710700010014000300320502c0300d500740c141da40c4440c00f030084e0a480340707880c0481c1028000d10b4507900440d6440e2410103040d140d07007401d2103d48141c55100000f4820070880c0482c00000c00010b0f10308070b04540d000c00c40e4200250341507803e000c0c0c40011100140e110f60942c0f50481c10800e100d004035004001070b03010441c010301c000a00ca0300d4a0310b4901c00d48c04070413200981065201c0540c10140c100c2998106e0030a100e64041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 155013615 1250 155012365 155012399
    0xe0d0c081b010b04110406020d050304051507020102030703060906050a0e060d050a050d0f1d040f2d050606160210030207170a170106051909050d05010c080c0309060a0203060607020a 80
    0x15410000170141d0700001d5001d01640c094400180e0180c00c030541c00d00c0c0a0001503802c54010000c945480380e002c3c40a0080400c00c86410006035004400c1c0080280c041c0134400c06000b2908040c0103050404001c1014500a07109003081d03882d40002154485c2c6540c40c03007000c402e4005c1c3c2500d11050090825995030000c50851030002201d41c4030343c0501d2849420b42880809800d5010b9110400590070040075001400366141900e40d6080f040250800c84a80b80ca5a1302070381280785900e286541c00354044603401080c1501580c003c01003040b1841c81d07198402c0c0e0040c0d0440d054181c60010100460081c0250326000301038515154082d401c44028034060701c01c21351650754050103500c119000c010101428860007010550038091403c03d40e04044203100310441300d2034241200365079400050040d6500200c00d030b6299550b01c103042441a44140a554011680c151040c5036041c210322056071480020034601c002a4040045801d80d0f9501c07084844081c1c004103080081ba850311552801801c0710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 155014865 1250 155013615 155013619
    0x905030301080c1e01020303011202282c011203020a0b01060815010c03120b151204110604060e01030207240b0405060d0309090c090512060603100e0d0c081b010b 71
    0x4000810418040700c04e991042c3e441a4003950842c0d00c2d01d130008c64441c01406080380c0c490403184c41c0c0c004850940c5040070a81e000d280040860a2500b41511040c040003210784010510402050300603504082411381100c07084034401030100e01500b0124142141c504005204410704800001c0055201c03a8207405442081070444000038890019104c08407000d070014045600c3c003c0120b0810416071040d220340b6800b400900100800c0d64000d602a4003002240d032808800c2002c0c481030040d26601074050b800196103070361070241001006042d0784e40c442105410103400042c860100034900c10f0070f00c0041c0d40c120412800e0740880071504080c0024905040c0201c0c40c10380003e600b4501443c00080c60b44c6c041e111400b4803401c0407080750140151003280310910400b0103000400c0e0700c41141355104c4504c0a0003034111418420105407c02840c0c0c4029503c060918007040c1c07064030007003840c015603105d50038604180c400924020055020300c103e8404840e1808280020306401908088044142 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 155016115 1250 155014865 155014879
    0x230a050d03081b0d09080c0c0108010303090b0a1704030c05160b1e090315010e0112020901140f0604060c05010b04050108030a0c05150a23010e07030c030905030301080c 74
    0x250018414900400c800280014901c01c020961012508011004692002d010203103418210408031040d03603110013044a506c03100003041d00d0b01c0c4000740b2650200407000d20f06105594035603100141034102130701620b000720304001030b08803141d40505807035030088884c1c2d0ba1100c503e1900e8100605940e15005042e81c050046509034809410300030400310503166400c425034107040345a00700025424a64034520200801042020241d640402005040e1514008000c1e915810300c042d6186010040c0d02203001ca409038522100141c0d1030050280c1911030032070035414030f040a0b0b8005042000100c00355030300130701d0009000c10201d0303014246020142c003d40c024810000c82c0003c3c0022101d003441400e200390418000700d03c21511454608102c58002d0f006c031000020f24500800203100e068a45002c0b40d9514400001d00200b0346040c011003030900d04000c1003c2d85402089105a50010007a4040554442002900038040e41c006144143c20104903a01ca43e1101d20080d514400c07403001903c0746503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 155017365 1250 155016115 155016119
    0x50a0b030402030f011b0c050703060504080306030d020607050a032d06090606020a05150915010b03160c03020601030b1e012d0f0b0906070204050a0b04051005010c02090a06230a 78
    0x505018024822240e660301c001449000e00081f10004442c02c0c0441300b40c00342220000100d140360180c5401640070340c030103030b5072420000100742c03600c540c419411066420680070002815081420f40d100303260b05040100c0c00c50402c40101100e400142245000d6040b004080540507482c1e60008090b18441035041100546420f000da0b56500c441900404e541d1008201c040c01107582c42c501a0841012021100c1a021805212200380c00907000918000c501000b0001c50001b01865510300500d9401d14640301095518001d444460501000c0c0c00031007641c022401d0300500c409003808200321460300201650b10b91148020218610700d01880c0400310a090081050400c010380003112030007500c0e082c8003458420b421096030440b1280c2a80280700340311550150f1994081e00c0d21a0542020001d650030540c0c042004460028262b00e0101c0d01c68401070100c1e980041501c5000b030f070102c4010b034181c1c0d54404080c02501031900a044030750031031500480400800220400540307411903982034825 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 155018615 1250 155017365 155017393
    0x503061c21020f0a0507090e011415010210141305030c0316020a082a040609020d051006030506100507110301060312080108030307080f07020c09010b0a030e0109020a05060a09050a0b03040203 84
    0x1042044040c1042d006001b0030401c400c02da40c84403060300070550021401d60350000140b038108a0440302420a0f10503019101c0d180d69052208800d0900344110800070880e6600f12100d0306d8070024410000074802e15502e1013407001c10001c0e5080351441e2800c4035524101c9540420309a800301c08120b00844d1240750114001c038001c109505442880645012807034214080840649a244445a0003968924010507020140d000501050101b00300216440c28015120014201396074050400c06d8684003e00000b942c5604414500c00d815141c034035128042401c010482c000e68062099156180c08800010040b2585440f2403805080d1527101349680da42c0051a10b900c400c0710381e81d001511050010704149000510359401015500c103d07880005110041a14802c00781c00843c0e000001041d4400142c0e8540a00d1219000c030800900880c0b600b84c0c0811812502801441d1013908041500203490f441400444010b040051040030040da44040c100c402d0b0380203940c00c0c2d00900900c2e03a0340500b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 155019865 1250 155018615 155018623
    0x50a060303020a02060a030b0607030c11040603020303090d060b0a0305010501030c0617010e0408160c0801111e1b1005010306050612060c0f04090e03031608070503061c21020f 77
    0xc9070960042c00030f0350800e40c03c008607a40240b01d44405d0540d12080c0c40c62548659000d001c03035500c20b40711148500440e0801c2410f480000d0140c2d403046091020a100585011050300d038108020384a0103c0401c0514210001c0e104182019400803008807000007400415040207040f01c4c06403585c0c107040f03511064200e07000c1d1002108424944910801003080001107492181d1107070140d01c110703040c140b0442c210291000008015128004d4146052090300c00038803a0004140401c00b03810b2800f01c0024119490003180300354480800780116a14034a60b403080c2c0b83e9084450503400f9100f0b50500404444007c180038001a60b400c1c0c9064000f0340b01e8100902d16100d01d1600c500140540d42c0e07219415680c82d0f024000845600d0001e110000381680707940500407050007080003443e1285841201c0c40c1c0388604141c0142d040220000a00041c45d030418104c0360020415100740519010700d1000c3c1c02d514200c40c20090080f01040e190044a202c4891130310340a8146500740c92140e10192015070703803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 155021115 1250 155019865 155019869
    0x608011a09090a090203010216020102060105010c0f110f0d050303040b060103020405032109180115090f0b0a032306130b010509060309010b0a060816090f0501180302190801050a06 79
    0x1240d0810040d0484501e450034900d40c0c46a0031210214510807164080703401e9801c00c00d4424520000f10000e5411580c0500c012400b40400b0310b0318080400243d01c5c0c042c00c04003115009401180303c400c001c0591b8030748010103440c0380c8024160090310101e80c0751180d52540200d400750303045103511012904941c803900071102210b60090090154403100c1403c440d0342a5034140000c1c0d910401c01800030715489508406003c1002c3e0484120207602d1701d0090340003030381101510010014002d0040c01404a000da100c0e0503120a40c0b06030303458040b01c2c0000d500070001d56100a9103218560040180a500790911601c500c030250782603088003410348400002e80759007411450215100b070040c0d088070b003000303c040c6a0010600d00082041c15009020944107407141d0440000101400100411030010702020407024849141c41c403030141c600b450001c01480103010310f5040100f064080e0545921401112014540043c00304407007001c04c9040c0c85a07858140701d01c10041d400d09002818405491103082c007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 155022365 1250 155021115 155021159
    0x402070206180109032003010617072702030103080901030f0e03180a050d05060601020d020d0c030c0503071a0114041a0f03070e010e0a272603040c060801 68
    0x410a42600c2c034503100c8800c030154440c108007140100001196100c000d005003000d844410b240000c50a005040c00d40342140c0000c6280900b25081110104000034800d040714805841040c4001084480c1520400c0301540402218004400407007400382c540c00408070150700762403c01901211100d810305030f540a0031948156001488901807410241007424800a0020701c01401c03140c51300700007014569806010340f015801902000000d580410034196003107094002883c5222142c44010890201c400d0002d08128011500c0e104022041081e00c900d01d50200c04c0307020701c09514034507400c810700900c25203000e40c20b180d103291041d00706071140c200303c483d01c04c401407a01060f40080c000740011900000d6054800c481e40014030310300251503240a000d042d2504141400c00c034030740009807403013000c0c0c00d90a1403020b1882c1d158a80460700625207581e0240350f0381e410030480e0982007100100080d0043d28030000000f00320800610851040a88031070307440e2030b4041e9803074852020614844801e414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 155023615 1250 155022365 155022367
    0x41a010903080a030905031b12030c092218030207060f0504091508030a0903231f061502150108010c02030f0d09020a03150605120d0509040b0a060903030207050402070206 75
    0x4008501e1600041100243c80e043c0815070755420342e070307807860b590000c0300400f403c059014004610800501408608400e0142901e05500b040340c1091141c0c8210382c0302c18032904000c1250102102180309032000c5a40c45402049982c0f00c4914845c0b0712560a2000c03801400382e0140072640e14010000c0380e60441070b5955035402e1a0901c100f071801800ca5142c4132490900c00400040c2e2400f0070402442a0b40c2aa51250302c41c1c0c0c918640340149210182d000c128100000f0f0700710040020004440c140103013052400f0f8400d0007550f205200909854110801c6502ca00126503a940c1d0006851007040d000c40c003060461340e90356170446088514a2041d1001030b0800c02466500b45c03544d4000d0081b1080c0390038006141240c590000340c22113465401140c44403104010070601680c1403181000400b42a920040120b09110103241c4032400e846440050146c08203001e145030b03e8590101c00c036004003901c88a0585c0d2640e2000e4030f140440e100440041c0f007100c0011603d41410700a449803158090440c1e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 155024865 1250 155023615 155023619
    0x9010f0e0d2a03030b030c0307060906180303080403030c0320040303120e061308120a0507020c03010501060f03090809090405030c060a18020603221407060201050c0f28080105041a0109 81
    0x46005e01100f10101e5071501c906481c0940b2503030b06010300070062409840b40d400d03042c41c00c01c02400c1c24100101a11500302da07000304002098114107032541c020b82c903280000c1c1c0300510400a030001e00c485001813a1002e030807041421564414001001507178080d460f00740307540d12a0052802540c20110103004582c2000c8081281c0700c81041041e1482d07071007082924180102e0307801040f5102000c0320f10002043d101c400340300000780c041c8014032111000761b0081c8559818107001070803141400e044c0070b0815a54829078001c1c42170080558040b03440050010490b03040a0512990300c3c0c0100313038210340b580603030b00100300090010b01c0352092400600101850809454003000141e800040c064107004d42102900340c008250340e001400c0382c6100b40f212000200e050103400c0d203002082c4d0001020343e85000140664076000005a407002a408a00140d503038000c0c6c020034a102d156905590583c480c440c0d0808242604094101c0c1625029a4104801c9034091020140c150304280c0741d501184000c201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 155026115 1250 155024865 155024867
    0x20306030c01051e0a0201062111190b03040f021207031502090a05041b0f0905012c031b09060904020d02040902010e2701050306100b0309010f0e0d2a03 67
    0x103019182c92004403494130707005181c60103409600524034000141d66800003446603072000102ca0b00d0b4008003403c00034842d001540c0f0014031901c018400d500c50107001000e0401c040340824000b000d800381903402a1a4201031525400080d103449007203106200002020f00009400690301003240c0d000605070058800d40040c000080d848150002e400020b00b10000c211603c542c0030785c1445c0b1043c260817404002c080c0c00c000305115810a003540c00c00a4250b410821070b0b80c03000e04154109044d0342c14812200750f6440c035605100c2d07042d800079010b000300300a500c45643e000d8400f01c2207003001c0c1c460038880c2d641e241c02c100341480220350080d445180310a14801605140c0e1041110500c107042c84107121940000055802c4a000480307a02e0201c65100f0070b071380f05005030880e4010302d400e0b001011541031040d0054405400307030141a42c24503000c8002240294250030114400048843c00c0100c10410344244e511250004a8100030415100c1d041c01d0b601400e03004661040c00d110891440c0c460190382c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 155027365 1250 155026115 155026117
    0xd06080601270f06031a1b1306050912062a090d080c0f072d030206090d17070c14010f1e0203040305030307050405010f05040501050706110d0603081c020306030c0105 73
    0x43d01400c907034905005c400100003800026000c05610301c0c519032480e001d50003110508081b03044100306902031080400e0340102c08400c50982c0c01c103061058031498150081952190241400c0486201c0c01090060b030382c42c8021000902c2500e06901e080e0f0300c09038414081c50307114916646070803170040e0703e0794008100c1020181000e811800b0954941d015008045440d14203250080210b0040941c20200b90041c1c80b12041000c3d40701c04c400101c81451500098480c0c0168020175000b904c44800040400c031050b4074a2507103c50701076041c2c1d102e07401030620f0a21008180580400e455551882c25040c0d8014680d0702c14003001a6101c0c164100305400b6400c0785007210032244150300c8140800f100040b03080c006984160f08a940d201e85942c03508000415035582c69050409001041100788080d0768800c0c211114940c01c800c1c045111001c4410300e000c0b900c81c24000e03030f680c185814030100401840034010078000948201034202901984801001c83c0f1060f07030003d6040d070210300d100c5c9240d40218 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 155028615 1250 155027365 155027381
    0x31f060807021f2003010617060a0501270602030301030212010b15090d0602071a011217031005030a060501080d020c132003010306050604050a0209061209120d0608060127 75
    0x50004983c0c001d1080b204c6640204940c0074040b000c50202c0184903065005200d00030780c5103c10341d0203189003452000319010415a0051604100e00001900030754006c0000c40f0210400841400302e115646120080d12a002030004074800c18121000030011481400340c10f1100340c0090500204c040e400d100742d60f06610000c40280c004110191500101c1d00c01d20181401074004c1c1c2da8021140d407111000700002005810024010110305210360109100c0f03071000c5000c0901c0c041496a0352280301a00d42d080c985c4e54030175627251049164003000c028094010318100d07000842100d0651b03a501c4010b0f603d0b81d8086c1e900a1b01f00300700c800c4941c48070340d040e00000f02d071081118166a5112030002c11917030542c07090700251400c0d41c0b1042400820309081c45041d41c000d40100d001c41c1001510000071710540700305000711071880c03030b0000401e00c9007200740300100d001c050200400d0754800c80e55041c000038001c94030404406000300c400006040705e050140050241841800c000002110910040203000c15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 155029865 1250 155028615 155028673
    0xc0c0d02040609182a0b070206040315021216020c090a062c010b1e0306010e04020d09050c060a0203040b0309010608100b03100905210d02031f06080702 67
    0x2e40000441004501c035000080c104d2203c1d201e900300303450420049115a110105510300503803045051058040d2490800b56281c501c001d5a8480850000490034000c80e0009000c240641400e9844044603500501d048041c00200280c95a1108941c08440d40811200b001582103280f581c051440d02c0a9059445030202c5d8001a840c0c1c2c5a008401000128075551036003520386215019048154810b410700501c0358011803860203c1540c1e2962518030092509541c00d000400400e03017aa0103894190304d814005001151200d4400c801c203005400840300c159094003680c444d4640e107050560895501210320380042d860b16241c0000140168002003042070295a40c060124040c681400b848003000340f044070108018644908150074142040d038a181d40d585007550550000340080742e42d01c8401a1518194081d8080002c0f00d202ca1240040a1099501c000100000f22104111002d01c0000240e013100720a52104c0090791030120566450700944d02420b01e0585078000850001c062041d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 155031115 1250 155029865 155029871
    0x180b030d020706050a09030512070302070e071407030320041a090d0809030f070e0109110a0c02010807020123040c06021609181a19020a08010b0a050405060712080703020c0c0d0204 79
    0x1f4030b444490500c00b402d000440b030a01d00054000c02e059042000350064444104610298202880c000d0040580c441e00030f00e04c44c0001c030714807061602aa0101161590f10721645a80800c9032440004076881402246c80c122010b0750000d100c0000305095428024001d4032032085140961580c0c112500401c02980e89482055400c80540b1814410744008002e0308082c105035504204031902590070360858044055818030907070741c4c2d840e072260b2900000c540a00f46840b85480300c94040340500a910b2903a20482c03007801e40c0c159412048448107104034065910401d40c00e0312001d04a0322030f0050842e956038010100414803032040f05512100c2a0140d180084106144030360b0f403400f00501120039150070710140300c1081841c00b020200114007006580c4110b181400100000d082c011043c0148000d01502090780b030b545a0141c03084130003610000707003040d488200c580b0380191248406011400094415008100500c3c080d00070398120340c60702c0c009400320a1441d8184050041c105400780c0c2d100e61 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 155032365 1250 155031115 155031119
    0x70606030c0b03090615010e19050a03030c0204180b0408160b09011d03090105040603020f07230c0a15050919060201060e162c0406180b030d020706050a09 68
    0x1111420a8000300754500c0803d03200c1c039000c107449041940050603a010015a035403068450380e0b12a584800501007200c10290403855800804d02000054018070b4100441c00d070f01006040d00284401d000b85e208031002c4c000342c021840b40301005865100700804407881c013070200d00001d131420050007880600d02d2214080300360688400c80196015244580665900c51003a0210310050341d04480655582c002146072915180008010748070303038803580341015130120304107806c03400060480e00c54941145a0301221200070340c40881c0002c660081d5440d501c18204280d4090900102400840e50307411a141030380c0f44010010348040d4080c4100c540e0000d2010500c03009590789825081c00390155500000c2c07490309220505101c4c1d4800740c844000d0710805880c030302e021507114102c02083d4445045996241c580100709203082294030704d00541c411b0802c0c6006c074200c0301b400c00b070b84114501c1880a00c080009842415107440113012010010f8006410034810b2038000c200415440300c4502d401001d45d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 155033615 1250 155032365 155032373
    0x50303042702031503061b16110d05010c090806040c03033002190201020c0d0309050708030a1706013902030703060906050601020304080616210507020d0219020607060603 75
    0x1a00c2107078400c00c44904c2c2d05092941e0304080000a612a1041262601c611420720092400e401000100c0400007010b00940301081810701c0503852285000e001e404140701d4071b1920501900b001c21780400002e140383c60014031503400052041c02139800c07101d601076503815074808031101d50b1000880c0900546034a100f8a4021560b404841c1c200ca8259005845070b4910100880c8078a038600c0c40c130216801806a2200c006001c1000c114503052402c0000d0302074411710f00142028010b500c000c60f2400003295800310b56811258401204a0b0f081b00d04070180d442c00015101a049120a26184003034400c04a28136048040b19076140c55a003540380e40c2e60305640e400285440800d0700206c5205482c0c680756000c014035402a03542000f02400070350b082904040056a0301d1000822660a80d12017081c1440300380e02034154461250301c40c0b078000c1c2000000b8064803025100941e141c0b0018411001d111205030300c041881444400104007005c8160069020404d08d90401f0318240e4135166a0741c000070000b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 155034865 1250 155033615 155033617
    0x10e150409090827011101060617091c03021206010f0807030b130f0f061406070618020d110a15021207050f01020307020a061b080402100c0606062007050303042702 72
    0x48109501d2a84d0314094036400146207004c0311440d9102d5a04100040c4003030b54200c0ca010140700f10001898240c0d0742c0b03084585141000300303950f9408400003400016202a810303002418040c0b01d4100d0014142c5408004480c501080341030100020146c0000c5449948240c00001d03c460f0001c11100304c07186801c80c541d0440b80b2041854043e29a01d030050040c0708a0350242800a09100340452500005800400c410b0302c28040c008041e41d42d0b80781d504800380721a160b5580c0d0b664000d0318501c0c4800141c80c00716070308104000c03018810300e20480006040d0303030b0300100b42c2d02914540d4090310500444031080541500080012580c5001d034400040c0c041d00d0910241d8401c82c140d80c000e094140c43c40c2401002c0390103041c507140c0b00d03400d80401000072680040c0031a402c65030644103200829000c490072604d00f280e04c10000e04482c2040c02c001540d81c1c1c032000300d900135640015038041381200740c040d00f684d0300704e144200e64050f08217010030031064240c59041c3c442c0c6c044103034a114404035100c19200403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 155035971 1106 155034865 155034907
    0x150303050307030f02040905090f0c0a1502030c030a090614090904020d1a0103081b0303060a03080307050403080406030515030318062d09010e1504090908 68
    0xd151007031388214019803800c1c1c0115101d17074503040790402400058a44c85850710034080b00c0c4440031340203d41e01e04070890080800d02034600d07100200c1c0f00284010000010340c007042c820740d94000c1050009081d00c0d4400d56601c0401400c2030400b502e021010308014642041c00e001074001a25100009a0407540469000000156601d0f050b1445010112881c0320300c115074000000308000400a0301d000e006c8105500c1c0841c891050b215500d0004881c15580000044010030200b0009802140c000c030a03071130814174082e126162124154095803000000954075010410704c100c9001e045000180210003551a004180341c000b00400440038540d0710450000648007018081e0408216a800110440e40e04110742074101100641090010601055580050880f24984410004001821900e0b02c0d0309103800d05c07017000b006102c82c0100701d51100301000005a03ca02c0910f031500 = true := by decide +kernel

theorem cover : BRFrame.Cov 154856115 155035971 := by
  have h0 := BRFrame.cov_init 154856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 154856115 ≤ n) (h2 : n < 155035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
