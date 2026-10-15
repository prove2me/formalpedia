-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5208
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:06:16.068446+00:00
-- url     : https://prove2.me/submissions/eb8215d2-2296-4800-8905-eaaf629bad37

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 936510791 ≤ n < 936690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 936512041 1250 936510791 936510797
    0xb0d0503091503041203090203070b0f0c01110a02030a031104050a0806180601060804080c0115151202120f18120309150f0a0c0512100317071a0612010c 67
    0x901d000c01d0038401000c003440454025410180300b80800201401e514581c500f24916002c42c03a8107e030b00001e802c000c8198400300442e8400103801c1101165000900710420040008005000e50001d500f0510322500070003078016001040300ba0405030196215070610020b00c062181866120f03c003040744043c49400c1041c0c030b507010008000701c0f6074407001c0085503440341c1c2011300303003139494100e0240450002420040c07a03548081081d240c0c20740c00354400d0b0105929100b101005950703413400300d2a0b44564603189400201c801c0c9451110305040e000700c542c0d0702100c1494615036907901c15001d085031400b40040918108014561214803002c003d14a01480140481640c0b800d15043c030f0351402044c03500141071207030058100071460031050031b1243c0c41094034001151160000600315140c0c443c0c120f2600303418042805011070401d6506d9814250380c1301d080c00504208002107500c213180a0002d00904924400a2803518101c0002c03003d41c200380041c3c00c5504c80c1da0031009541c01d5500e020300d98800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 936513291 1250 936512041 936512047
    0x7110a0c090915061401080c1c06051207080c27070504090518120309070518061002160504150518160c02030a0f020109150c06050106051c0e010b0d0503 67
    0x3e2000400b144020380142d1102000f01514000b081e00902c0100c225041c14801011700040c030030003d08084601d4642800d1001d05a000c01511800c0200718501400340103400c007030030312880184c00141c0b20007030f1101d000040c01d00e514001e04110138800d00a070300780c102d032011061007807034500d040f50305d94010f000c5a12559152420100b0314411220000c100c41070034010814203c2c203003080410114243c030700403030115943e595415000d80ca8402d00d58411500041c030704c3c11120702200401c44850041e0404c0b1612400d04004900032a48d83d07101e500108070400c402d00c8200300f02d2407d5403101c05442d00039a41c88800035039a07c001400c000b000c1e40010403840e44041049075000032211442c035481c0d407034103003406c003844d50790007081d519100800c004191800c0b1001035000d5a0152542c40000c00f2640c00750030804d07183c400c00800c02d03140b940089400e18108000415841d00645c00e03100c144400703040d589049080390203100058848110b0128a5540ea50780c01c3d82c4a0310707a83d102051142c09540190b80d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 936514541 1250 936513291 936513293
    0x9050d110d0c0e100b030402130e0706050d0516080114180c070c170a0204020d0e030a020f0c01140a081f150809010c0e090a18060f050f090607110a0c0909 68
    0x2c003d450090490110f0200e044052044042e00010342c0e0f0040d80546181d5030100c04181044004e164072044004113205c1d0090024410754010000c0252503640c2206002541710a146e0003881c48080a00a0104880c400103004001148092101008000700101032024400412455511703007651600d5a009000680e0414002c90b02241c0e0000d150102401444100300c0041c035490f9220444000e200780d40006601c085124940c0102038040154419681d4030140140041d5582200c1614009180a442031005023907004a2010503036840034554186132000002c0112040c0c2802800840c0a2000c6600005d040d81801c0c02d00e070142114131210919103211800c00340c900b0074020100c0855a0511007100c214560107920140103d40656004ca180c0e107a00c400d010203450026a007410118262681c502448240e800c00c28440005031001c201e04c2d164644080c0502104581040382c40d440a00032803109442801c1e0921051024029603d030107000da602c8001141c91940103541d0551501c0d030440c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 936515791 1250 936514541 936514559
    0x20c060a09061e0828060b0a0813030e040b040f1d0106090513030e01120c080610020c033309061b18151b0a0b1609050d110d0c 56
    0x104200d60716010000030380c0003c0010000781c030042540034540545100700f42030354880d000c0e010880100e10010b05c1800d03107541361040326070484421280011080380201700548116801481840e0301503031101d2219041d50305000150901290b0300380c001e03a41e250914203d44007449032510410382c01c02c0742520a00490442401e54503990480c640c0701e03251a09114581e00d00d00100d41120740d144c00c00040c41c0e546200141c0b42a8030304004143d2140c286016265040c4e80326013601d108450459403202c0341d64802e04204e0740c88092200c080e40691000b148500288005456007400401700c108140d00500b011000050071541a91030110981c0f0201c2031004009131660780f51108500c289090742018451082012401c4500c08400c2c003402d00302000e09000040001110003095000b4000102d02c00d49580055694900d688260750390003038000420080040407030340c034083d405c0c5c41c1d96000e001d608040c20001c1641030640e08842c90a02c88150a01c180c48032030110000034055521f5030340540c5007651031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 936517041 1250 936515791 936515807
    0x1803050307052a0d120302040b161a040228051002060a200301090905100e0309030115050604031b0e2a03070903150b040617070b04150f020c060a0906 66
    0x14000e980030f2a902c003001d496081c840d01000d504564407460501c26032070b050b0001e10841e085000e41c140001035500c2500306804d41c1d03040b01803007032105180b18038801d0400d054150087e28020750008480040745003a4018a00c1050308041030f25072507e078a5034440001e040710a00030340305405a0410b40401103e9011031242da060480c0030000d012440c050070141d0003081c481405101d04455640b080070043c0441000070000001c0f0308201045044041c1400c280c5c0c98000110701407080d0b0071b0800c0d01c0f6460140350820303800c54202800c49401c01c1d0070340d0358203014040146102c160328201c6401c00255141008480c030f002d0b5503880e2072074110303802d03081c0201b002c03068031500340301c000400f00140882d00307030b00900d008212078200795446003507065200700c03401804407a21400d80c000d00304440491041f58400300030301c1c08000350381141d120755a508102c0c64140070f5841080d4110080c0d03480c1074480e5010306640c1c00d0940c007e105403428400048002002c5801040b43c007000100b03c4034040c445681c2240035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 936518291 1250 936517041 936517093
    0xf1207060f08010e01081507020102190e1009080601170307050a0305120a0908190c0b0106120c020708030d0507140403051c020109050c1c081206030d09060f180305030705 75
    0xc5620075811b054030345568075800e90035224181201400103031441d100b07506440030240e10500441c5886c924000081c020600540c1c41440742e842e1140072542c050240c00031808070b5614501904d002e03864004000c3c056204030400a4150004001c05c1d80007a03010b10038801c4543c842d0300c409898040541c085641000000c01f580c4281b46850300c0232002c60404070582e0720f840716024000c081c520720241c04640e8a69140c00c003c00000e03e13840041101c0381c000100c1c505090310001c007005800700d802c030120b075030300428030403018941c0040004021606a50300001c0e8082d59900b02502420030000510016038020390099465400210402c0c0c0d88906d404142d1001806602c000d01c4103c00c65111581c89060f186140ca1090320944030311a0381d52000030380348802d03d8002244544440c0319401e13001040c8401c4400301e100340101d030418201c56001c1c0500500740c0f003803a661040c90603402402565001d5040407400b4030040803841c0000098420030060042c1d900c154007811940d00d55540c146039580131000303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 936519541 1250 936518291 936518309
    0x170c06040623090907030b1018051011030310081605010e09060a171b030312010605280c0302060c1908130c0320041a0f1207060f0801 59
    0x2082000503844406100c0c420010100b482c250000c28039a041140f00e41000703d03400c00f604004106106406511003030711100d003515040d0f0391f4054410103d5501314811402010590350702424480e60130070040780000e2815504200c14508001143c151842c0c008a610190501f90344905102141c1c052181d4140c5a02010741d03041c87d070381000000b0340110b516a0b82180118040000100b0545d01c000d41c0000a048440b0360341d050428500c0c015448003c010290388000c00008002d0741c2c1814000100c45105c011690704d80c80507428400221034a0b804140c40350b060b1a4040740c00f00a006030808030314441e91650b103407803481c01c02526029051800c01030660f01c811406010085504440d51440003a4044626202c14281d41d0b02016103000805c1c180003502c1c0301d00e03052001c402c0240c030321440e000240c101c0e29200c44100743d0000700019034000c51826160a00140c1c4000c3e6079003400711b5926145030000344191020782c410f07981350745031080c1d503031001000402020744003120a40081078107000d044060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 936520791 1250 936519541 936519547
    0x507030302070807122004020301142d06070302070302220c0f0e1003060b07110111120d05090f1002040f142b05061006080f0906041407030b01170c06 66
    0x283d00c00f0400c0704007105c01380421b003608010744a5250108030318039906000400c00c544a58541100c0701420116000c080e01a9580580c0800b80401070001d000115110704032007001c0c041c18205000540e0040c9204070309500c01c1000110041c5d540d1000c2c3c2d20440b4a106050349200c08080b5a6000d4407200382d82c8a06208184d04e46030089948054400d40420050390b081d0840b5004840887c0140702580c405030a00c1c0000c20342c48100805041e54483c420001da0f03c1d92455100c01c004103031103117481c0c0d00103654601d08014621200400303401c010f5101c2c89000a6480c0880e0b50b115060a00c07003e6440a88090360000b02071180981c1c500300708001d80030344d00740030400d407141d0008a194a10204421a4040c0f1090070340b5a0300c5147c5800002465448402d40b6040c0c03d107915458040c01031409400041000c00b40000d403404884030100d44100b911800511a03500d450302c519007044410740e5421260b01031a10044003082744981132034006c1403186030040744058401c0e44d5504040c00a00d800707100b02010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 936522041 1250 936520791 936520799
    0x302220614101806270305010e0d08011d0c07060507090f120308040b0a200a080a020309060f0613020406020c1002010c020714010e100e040b0a2702070c030507030302070807 76
    0x70b01c03420403c4d5501424601110440052401803074120b00a11200c0900c4a810100c10414123400034140350116400312228402c40c00f009681c1001f090155010005071030030185412201a000941c1040ba6001c480f460b1082d581c031140107a500803255800400e200c418100454074801c003c42d0002c120400f00c00c400341d241d42d44c0050a40304090400b80003003030104040f449003076082e80b110301c1d00e003640e440c200c0c141402400205ca2580014003050007058050b0009a036542c41c1e4000c132840340303203007001819842e556680c10038640c400181030070303800c028200c508581d441030910040000d003900350003e0026000910800c021410365a20708011641040b28085429400044081c2680d030724120f0403111480f814012140341465201c40c55101c5080c0d100507800030f400010f10702c501130055078180560454401403104030603c9102d6007001007228440714400700440140e02c0317141811a14050701e009440d4480c47d410b60465002680c068210010800415404000d03040c010700d5144050440903241c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 936523291 1250 936522041 936522077
    0xf0414031e03150307031b080703081c0f0509010207020f060a1b05100f0e0c0d03080a15170106060f0912020f1809010f180c030222061410 61
    0x2941c514100d80e031004000700c1d14404010b01000901c61004d0102c45400d0f42e6418400251250042030042c0da007500301e0b000c074000202042002c19a0f8001752180e280c01c00707014295804440d40c0c0d2845550030358030901ea440e2401940501402003013620009a280c00e2a40100003125002c459020f128840800c041c240c02c03504000b0034003402c0d070030b0020001c481c00207082450400801c100c022001c41d1804035008841c10b640c1d8807141468509004039820683e4040a0089600389102c2c0540800eaa40780000e80ca005070f9000340c443c0701c0d0b040d4004248241d032908401480c3c482034050319180d9440f05014441d55131301c002c02a180c03c4480c581114090302c0d180d03050b12850104c65010340508400742e6105101e03100d08948260381c503a250911581440c0c014821802040c1e210400c000c0b45040c001012a0a400d10703400144082d00300c03801842181c0385900308841071920900307850144142031421a5084075030320400e0700911840624420310701051041040710484d60750310724240b2400580c19466421 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 936524541 1250 936523291 936523327
    0x40f14090a020a020709021201060806180c1c06241407020d030c0228081f0b0a03020303070305210903220503010c02030c0106080f190204140f041403 66
    0x1c8089001640c404001d18224140340454002105660002520020f03149044410074100e550540c1d83c034a1603242c40007000042c0400b010000720418407800415040c0703080744010148800e00881c4201c03590034181c0301c07900761050307680200da64442c4450440d051140c04030040070568401d2400f2003a000c01d6101c20002030142e51380c06801100098141010903008032141021260020400007420108c1040700c00e50143d002c03100059480104070000d5411030004524007070107101510028055143c4030300c00c00610504000d513502c07491050002000d0780741400105407140c021740d111035440d4100d0075400c02461800a10640c2109030b0b404020251340044143c4052100320301c05100c110300320515095a049203500190303071551034a010481e034150000001c0c52a000400c0090044950300e08106881784c1d8402c01459040d0409031003408040c4002100b001c0192004000154460488d40f5004510030b0407210389030f10658030002c1c00103010b1546890307907405505c2c1c8001c501d0710100d1112004500c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 936525791 1250 936524541 936524551
    0x40608070b030a110409020a1e051b070308120f250c03030b060301140f0a050f090c2124010e0d0203070515030403110601030206120c12070203040f1409 67
    0x9000400850f1203001c41d900005920610040460b0b10707940c98880c1074000b1340c00608003001240000a0b178041401c116102c2042c02040c545400341040c840c1401c103c5038110340b124211960080ca080071002400c0200640014403031007010030064a05035200e0b02000c80d000d8291202c1582180c660b51090840d550b040300000315902c1c00108500c0c403072409501401e000540c00343c2c40314000c000464134002c5000e401b10351600407100548456030307680c1030107903410141c010950000980c544109041c20808036840d040780c0e00c0326500303203072003a81c0c1d44503d0050b150761361502c01a02c1d00b41c00e00140c4441001c3d00444a580000c405401020b14000a0202071030045000e0040c000c640640c0c0a56034280500d100a00003d0301c5680c10b1010101d8081d61030340212002c41c0420400c0812280c05800042c400707060340e0303014190600c1e2185c88100441640002441581610403c12210a0070b01e0014415409416a900195101c1c1d05102c4c407500240300f15081409030000071482c0b07070015914050510b4001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 936527041 1250 936525791 936525809
    0x5030c0403120e030f0c1512010605030606070609030c030e01030218040f020f0705150c0304151d0a050c0111150a09060209030d0c060605040501030f060522031d04060807 75
    0x9030b403540c0d00b95165503100c54480e0313050044640c5019588000b054080c45000200c6c0e40c014500440401410f15008540d4034807032402000c4c005108040c05a4021508a100240b940381407106a0350358100b96040c80508400140a40c40c100c810141c000510700b282c19001d08080d8142800042400d9544a062000c280700b161070f480d0342904107284e0382c12036550000c074500d00750741c03540141002983d81079045046001240340d80c0010b0035000d00325094074000c50384428107403480f4054040e101c0103048200e075207251500340050003425201c4d0420015030000c3c0310300f000d400c03130b010110f0000d0001e80641881c05403a4000c2035001d485412540b00241e4400d2003407000203411450ba0400724002c0c05068002c507018850f40707a410071110b4102c2e10b0034000e144a50300c10b100c502d854a0a01040c0da03400e200082800103000c85410000741c0e181c001703e500210000c10103e2440180c0d188003445068042d081d404600301030503400c043c0480994510501d00c007603a0901117030b443c2480840d61020948142144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 936528291 1250 936527041 936527063
    0x40b04050c0d0c231b0f070b1c020c0c01020c01050315280b071103010b01052a0607050a02010b090403020304060f030f1a03010e011104091508010903021c05030c0403 73
    0x52402030703e000348148105100410f0f043c0e948803811380503a128441e01c24095003450b107071342c0007000f0001d042615882003002800c481e40c80c2c1011050b16820985004001407904441424080d18520240000c030395000d00414201184100180c04c00406000340c90400a081041209401d51156040c0e980d141c10f55000c0d640804021556049140c030020b80480300007600400140000c030b0b070f006400c403140110504c0307442104240406080310141c0da480f501181c814032220202c610001307180c080301d9102c4040300450035028004142044030454290020460104045401c03503424410114045400c0d00d00c6221810140c902075a03c0c0281d1090104014103008800b80302c030312940120030407082c00c4006000710040462044011118503030118040e40c606040603060b040305008926004555010403403401d401c040c0c514001d06042032810016107800000020301030b03401d202d4500d060b40250f016080544003000080500e4a03444080010400144148115000180111011a54407182d0b0400d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 936529541 1250 936528291 936528311
    0x31104091e08160f0b0f011d09031c05010906170304050402031e0103050a02011229040207080d05090c18060120030d1529030901090818040b04050c0d 66
    0x1d0b078400d00d4001000341e10078086078000c101680301031034003241c41281d62101c00d0f692012241d0840c00709224116500c810400301e00c44c2d20f5104290f45400c075103008240c0e46070030001041000054034440303403100b1095842c00104028045440f0304000713440c2d914a48010044140302d500d5807400740380191845103900001180404143c01001c00c04030010615a515941e928107109481e10101401640410000000101182250310a008118020600d0301640e215903c40401c044034140101c1c03030704a0790800c028804030715803901516500b00030000206072442c01942d01418290380e112414011280c1c0341090081d502c074540c0c195400f10b020b02e00403884000d0822804078801d002660050240000034051000b0016608480c10034058040401040b59458000385900c0001d0000b04044200111950380e071444000e004507003200300b41d0000b00b41380c509601c424002c1d0b8000544184c4101803450700b9141802c1900580f4134655003100d04014514003e007036030a0720f100d689800d0a2040d502e000341e01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 936530791 1250 936529541 936529553
    0x40b0901170408191b03271202030d0503040218100905011203020c012a060b1504031b060c080a03110a050912030f07030531031104091e 60
    0x51102819103104803400c2c242030010381640000401354026075100d1000c480b41c3e000d589601c003181020803105030f032181030384c070100c5540303158400108144030b10500c100991158401032802801126981c071828199a204061901c050000344034180001402008090b0392507000030240b046100351512041e5581624182d200100d542241c80176034904130001c00d282009803c07640c2558465000c5440e14243c0c00b005642403604500c200007010307050f181d03e80d50021071108144e80180b05074404039100081d4000079040300e00801045050101c00702e420018450040110f00c3d421407203c085c10700041c1400e10003040340c007209402034410013000464140c400c3c803942c010350b45da180307c001c069241e44032804000c0c005e9020a43e45481000c48508030002c48101000316022130381c0d140c0e920b0b850a007031903905075200e400c040e9a28074000000840714184100b48068214407030022202016800d00710715005441c00c1c0700c030642c28051480e0564002c0041c004a2081e1030b220202c10004510320a5450b00c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 936532041 1250 936530791 936530807
    0x6010f21020409060c110a2004151401090b0903030d0e0c090411040e0f030714150a0c030501080c031f09080408150106020307030c0b060d0b041412040b040b0901 71
    0x2e400a01c1e007045081405415480040b52104955403c00c280f1501c100090f0b65600d50711010f401104401f0044840c030a0a015107101070a01030808250b0886402038002810749690117484d40000c42d20303803a0090340c2d00041d035601410b00152454180150017000c40da032405000e1070314500681e100ea08038603040c0c0411244980300e000412101441c90186040014451152000c50145062030701003071405001003010045540d07100700442c200600c90b03c51450640d460b03488075655009250407203c00b401d10b43c110502c02c91030076402094003074a0b514001d0071658168800381c881c0d00145c1d503070646da64010030050882030300c100101c40c00150a540080040001e140020880c074000a03000480d58030104091200f4403d540340b04000707070b0b0382d0320003a40c60307128245004002603091801c1c04009400007280c1e6070007110250044210342c140e566110003400c41504c003a6130640f001c0d10080c2d14110200805c076013060440300c846080524086d490419401079009144400c00c01242e0104103910171110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 936533291 1250 936532041 936532043
    0xf040801020c1b01050a0c02040b0609030d02011a010801030f17090a030f06060b0913020d090f08070c21030305061522060504030818031002042606010f21 68
    0x21580c401d050b07403405507218072a5510000c00601040280080d600581c140d5184040549600651040941c00c100003044c61041c40c42d4400014002e800140c0c40800103200c11540320303000001c01e1035620700745484109000f5400343c10464020018000220303c119404141c641c0202080780d0701e444a1b0241603d4000d013040d80b80c00040b10000001408041003920f40c000d070040d0020000d160315145c100600e486034890300c3d60041900101c4100311303140307039000f4001480d11070030003d480c504a981d007002800110a00303582c032050109076441444068620b2100510706050b0052031820115001c460300c0380c0000b4040c0601d580c40c0000307505611400980404d01300d501099503607404036550b00c0240c50526410764070220f0300003100400e00e14011011502a00d41090f000381c04d1075541e8800b03166801d120202c00b600344c01543c02c44d0a01d01440e00140026064000c1c4070400000f0902400b126110310308201241c9500c80c1004120040e0f034480740c42d044d16401001460854400310004040e50a0080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 936534541 1250 936533291 936533293
    0x11070809042c15011a16050a08030c07051b031f0e0703050109030915050d02210124020a020a140117090c041a090705030a090f0b0a0b03031305060f0408 67
    0x3180d0030030b0781c00101da03101c1d140360300c02e0300341e085031740c80300c840c4405141e0220200312072107010004002102c8a0395240ea2155100c0c0c8100c2d00d044109554201103600140c5030301d506840301081603c1004070170b004221401c030215644108c091132445c0040e5a420260300884001d6516980300000310075590041650252800c0c1282e040d039a980c94502e0081c00700600c1503000a880d03543c0401c00543c480d03500ba40241c101e60712141016800b1007240c00030340c40425642c018400002c9003945c1e40c00141e03440c80c000c05103a103402c4440402899104010194904544210341202c04040300503600c244640c4165280f04506807000718030980141c17204500643ca80c00305882c41020040040340000780c0421280d410b031414810300c1c1e469031003280480c0107030207055400341400d00020301d01c512850107140c1c400d001441c041000041074880c294910000c0c2810380f04507028030b040041c03821141c005c98010307101c02c1d4010b5140c501c01e152100395060250040758440c4500090144030414090300b920060324081c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 936535791 1250 936534541 936534611
    0x20c070b12070809032712330412051b060a1109010f030c180f030b0f09030708031914151e12010e0106181107080904 52
    0x3030058540c1000810700380e072120060000349441e00c030300034a50042140f40d0041d414110101e001c03914084040050307890f9803241c00d02102e45956a0464840d01d074038810081c00c2600e412201200c1c0304000c0c0138001d022441c449108000145119000e10b074015000001e11142040c0e55608480300e2050035220f0042803102078041004100205209014428850003000240f68082c0781190360702414190901094050300a004424025004080450b24916094032141d0301d4100304100c102c540c2d04901c81c205000c0707005201300041d0940140e048207118412402c94905900c000c0c1e664416400020300360080030010420044400340507072101880141c060220150f04540c0c41034540d8101e0b0007020354020b07901c0340038090600c2c0e08a040d05a08080d05200c5030340e01501800400070b405c0208051944d40c500c40740d03095400a100c0c040c090b140c4076101541544071405640c0c140c9400100da812850810802c101c0000d509030104c900040c0251270110700b00120703038030300c014985007051808100389051b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 936537041 1250 936535791 936535799
    0xa02041e0914010e060105100809120c010c0809060c0f07150603142a010c020d020613081209010503040204051f0608190504050a02150d0e100b0d1a0a020c07 69
    0x1400b500d506080c404000c0010405a100c100d0380c4140038880c503a00291001c1462a0b05031042c190030358000303511400c07104040c004400741015503000c03084049450f5543ea080725982a0b11080980d001030282000300355600340f20a802520348210341810405080004101040040c03106070500000039140e001c001555580c14031130440d03000040084154003500113045012804990520040b02e040c40c403a05005140030300643e00005007580507617208042e40300300001070f510f9400030010750101c1843e40c0c01451030b080c0302914262031000c221807500d0052003070111a0340e2140c20b0341d502c1501181d0201d002e4440700d4409040d4402003021890044a43e000886c80b5504496481c6c003682e0b8411103400c182c0384c840ca4400403100290380c001c0060f00a04c1094015160828582c1c03401c1030035100d161301e00742c0c2099040044440d07114440955410030000346100e04017612031505808420b892000040c603080c3d586a510302080c10b10701580c0f03110f840100305100c4103a4103655030580b500c8102c402c2e003911 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 936538291 1250 936537041 936537053
    0x50c070806100914040f060c050c060c0d06050306041502033c06010e0901180209091e0a051e040501021603030f05013219030f12020d020a02041e09 65
    0x2c3c00307154501420091104182100c40005500c599009440c0740028105690b0f03d07070103008402d5044041210034004080405001d01030b060150450f40301b40e43d40d40c2d1703c003000c59040e10602d070300407031103034100c0020400030885464480c0042100f500006030740c0c0d80c810500000c0c000f8880c03100d1601d02c200c2d0410505c1c0d01100c40303174440c42c110888060034559458a0045489542c0b600100750041240c0004010b620780110b00b400404559020150400032060003280500c081103d490818681c0c000c4001d46000d8000c51294001e88092024004c5241451400f800120700c00500c080d203540600024050060079419221102c640b1542c2202e092010f00b0014064590f9030143d8001600d46030000445804004001c0400c0440c5904550110380701651840c4001c0500c503a203030041c25100c0c01c0803000b0003189000740a0b51060728804001440f42c20700c110030503d000609025940500c11040c03005400203103611420f941164003280803c01145011901042c08944401d0b1a0806c103042040000e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 936539541 1250 936538291 936538321
    0x1b01050a0315030c03142b0c080405220e03030708070c21020d0212070209060d0317010b07030e040b03121606050f1f030206091c0b0c03180f030901050c070806 70
    0x14207012100047e10164104a2900e844400040402c6005d10121182c0b405220361180d05401059031604155036400462080b400b030710402c4052280f804042c481030350291044003071a40501c0011802c511302503030094000c000240100302800f001c8031100c0c0801c2200c050861000c804041410410000c034003003c2e68400303451810b8009401030008007205803907403034144d419894004241c4503441c0c5400c414840387d411003210a80c2005450b06800b0035800a503140c2178004c01c1c0d244103141d643c091605004009400c400300c202e21450500c03200c3c00440d40d001034031131208240d4401841d0340d20088120013041d001c02a80003421107090504000d02c141e4520200380c0700e03d07040c1d030102040040ca1400b20000752184c1c04001c2d03019209100c500c44605003800c00360407051075141c6284d0202403584400000d001d0440744142501000800c11011500c00c001a0b45a5504040248074140e0b030340e0340f410b071240241910141001408141040360003001c000d075000500c8001d00350703038035410841501c81c2480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 936540791 1250 936539541 936539573
    0x140d023106050102030306031507050c01020a0513090212221406010806010608040510021c0e07140402090a1427060405070f0f030f0f02040609081b01050a0315030c03 73
    0x1031800070005115400401124414000103006c3c001a240b00342d020030764240c1c05445001004002e2002540e803d600340300900406e4035a88846840c1c13000034000c9010b50060741c00c025017890041c05141301e00060040095000507001d0000d105408011480443c10394129a004c0e001201344000c0905403440451024103a9418009450044ea00d40005842024040d50010841e50104003d070040420a80c05070044401d4612000c0c10700c000c0f520103000b07a07003542e2a11030b601c4d0452001044041050f80540c00d08040035503041d420300b010031000815200b00c9121303c10000400c2005564143d079001a00f120b88224940b00712148152a04000020f1b042122031a01031850140807922443c00b420840d07104040c142e981c4004200324000c110041c007010208010b5850300e85d40700101004241c00544003510741941c0e890003061030304003a28a440e05440e10b040840840d00c201c0701c0166400001c50b1030303c60942c100850b81d0004081d04070510240c6038000b504515840001004100d00300020141d10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 936542041 1250 936540791 936540889
    0x30c0d0b040605070e0913030c0c0b0307080a11040608040f020603100e071b14101805160821040f17060f071e050f1911030301140d02 59
    0x1990704d0900580d40740e80b1a00040390301403c942d002030a1602c0002c00c1988071442441c01d1013482c402551460b07441106500116440d134008000c02804a9110941a41c000c0b81440c05005003201540710010901c1103008680810040b00c0016050064051030440d1700e582c0544035540d01e1402400560f0901144e014000301781c0c000310082540e151207640802c822141504d2007003070750302e10340d070b621096001d842d030250f000c50282c60210040d00446104c1c044001d0045520100045c540d407070118184400b80d01860701d11020840180611074001412099290300c2108100b00c0c9100105250424007540c0d0000ca0542c41d80718011455182d401c0b9003c05a08000c0100c400a4a4081c260340f0741100031100b5500080c85c540050440f4020301c04158002e8a40e802c210303242c080703501c41540440d403203203442003441040f4082098411745d00c001c0340102645807601071821541407440e04500c580e804506544280c4810b803c2a095641d61609526400340200b10b1307a8034180e07410160a144081d200c2a0701c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 936543291 1250 936542041 936542051
    0x80103030801170d030f0e010906051902040806070c0c0314070609080a02030c1909090f030801081f020703030e06180d030605031e070509040813090c0507030e030c0d0b0406 76
    0x129629000d040400706402d4004e400e44031040c1004400030030056404469071900e8a0001c2c0c1040d40a03c50026982e0003400042420b1600310b983e143c80c0d03285001d10300a014030400c4108901800030814035000003280c90b100d0110305984c204468180d80a4001a2030a0700200c4018100c10001604404607216900c0366445142e66003815a00ca071240b11010750160001e04203c4ca6070300d0706080c90100a0a030030092380846445510380421240c8118040b113180c00b10240c070030145904900d95500411004d03005000035040481c2c40c2c428051900304405860360042100b41c20980650045003421140d54102c42c0305150000c03400d4804100f26000c00c203140a445a4120410310134080d5400341c0d0400fa0007410780501d4440f18825654804010768080d01aa6502040a5441500c0c072800703240602000d40d03c1e40002000c106100d40658042185240b50920b02d10081d038018050750110703509414100b88017641000070a003404481402d950780b20018004140070095518803140c05580180c00800c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 936544541 1250 936543291 936543299
    0x905090c031c020d0521180f031e04081b0d0602180a0911070b060a270c170f1015120e060615070c05150703110d050f0d110406080103030801 62
    0x9803e1091906400740320300b00b050f00e140d200c0c1b040002035170020304001c02283c13501c000d404585d081022039450703c116a04001501e000104441d0304200c520303482a000c02d46014a016070b05952030118840c0000c0c1d5031903141c01e6803003603a0f0b5154035481142d0080c00641d0744050300c5002100d0b5000303c42c2c130203100b00c1c11141e011410b040103100d940607200640307408624003059500e50b01d52100c0002c0519500c05201c04021420f40004048052808c0817011040139070385180b284a000c1e109071128a404001114030000c00070101c1d2841590400018513454141d0340740c0c0d034820020728415800c201e469280000c07004c040668000414070754018550380812240030b640c542c031625401e007510655800a80305400c031440c484810010200307184074000c90510540d485020401d40340c0b42800a00c000320300461080e0a15400118a2100c03102d81006041031626902000d0058090078402d01d010500c0490b401c4186210b5030310941d840c0d20b9490344a5101c5503109401000868240000c500003400580005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 936545791 1250 936544541 936544547
    0x1091d062b0c181e02161403120f07080a09060906110406020706110a140304030516050a060c02150a0309080d06080d02030301080a0605070314040b0106020706050a08010905090c031c020d 82
    0x1030494901c1c5920620b200815140a8081d4020320a02100b51b464000000001100b2102480092680fa405035444010319120002c0000000f400e4208411854082181ca940e10521301d40d0301c00983c00d0001107030950790070700000030b045c1510300500b850718010172512020701050142c0212055542140c20b03458907500110340103010400c11011b180c2c440807042d00020b42000402c000c4100c444212410729032380391501440d214904410300003901c0f03030341002d01c550300b04001080050013a5041c041020f0101354080384103e5984c40c54004070030408141b0b288018400c0c1c00a20400307070001d030819152004010020010007851080c00c040e481042f0301d00c6c20305400031003a24100c648143c0a41048078241c2c8036400540b40c01030204040680d544959410105d000e00b001c0e001f00d0140c8106c00156040c040064540f0702c1a40084017400340c2440501c40d165030140250303040d12032124000c90580c4038405007507e07184280110ba07525020312901c00ca010307901c040d00f000007000c955084134484070b140e007819 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 936547041 1250 936545791 936545801
    0xe0903040501080f091612020a1d0a0509030d11031e0c0304080307050418150b09060f0d09022e0503012312010e01060501091d062b0c18 60
    0x11808921000c1c00148860f4004550661080e1500c003a280030604071410f00f010b1601b0398000c00c642c0201e41d90400e065041419240024010311090401390903a003290f01c6924040041c240211380f42c0340d8001400d008414026038203c4049000140540e5030f895401d51400d800840c1c00691404038643c0002601c3c80da2074a003030203448542c48407851074680380c0b5007103000d5000a20120501c1000c1000058030700f0035000c940c0c0740c8281300c2400a02c1a4540103011854603103680000d09820301840701070f0040d618602129503d40d40c050134580d861000030b440320301602513030b04003039070009100d02c8075034007012400c1031560042d01412800314600502c60703055034640400e0045420b09001d0102c00302145185c44c20b0b80c500014018241e00162030444c0d602c1e400d603501c00c2c0ca00da040d40d4650404201d5560403e00080107003401030170780e01c9103062100c0603140719000104500c1c803450440400d518001005421580034490002025900ca207080c20090100c185034401d91f60040380c440400d0035a050350f40b01d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936548291 1250 936547041 936547049
    0xa121416030225240e090702210403060f0b03031c180809030607020601120b0603150a1a06040302130b13090c061b150e03121918030903060504080702060a090e090304 73
    0x242c210303409841401d00000c03610042c141c0066104525207161203c50962440c0724034401c0c9c4460742da4450542c42c1403001c0e0b65588483c0024171b810000810000d41d404400c2c2ea00b14000104810810009002e040c4060b015881d24105e40c81007801810f418420404018803c1c1c802c01e6040702c0041d243d151080341d8034032007445200e0042d03c10300c100d00b0028811105c05900920002c040722610f2282440400089100340c0d0f40900003951040003180c1c04c0951b1009140405003110258281803540d00031441e20000741628041096455a02031026550140e80a01c40708820038108480340c00c03854140f0b12810030340a048081840d0583e07002c45c0c0b40ba114112401030f680409180d8021805142c0d07080680313600d10a600e01800305000240d481420280e0311841071400080c18080e11181c0d4941000700c031034921001c0455034440400754040390300003070401c0403a039200c00001081c1d0743d9802c1ca80928099007100a6028400243c0031201c42d9200c174105d01620544035080046889091a89689201d1841 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 936549541 1250 936548291 936548297
    0x3230615040b03070c0c08010608031605120301080a110a0501053703090b0f0606072015070c0509130204050405010e0307050a12141603022524 63
    0x154003814580c100c029a00c91120030203003040c0e2101c905072600d40007218508001400f1481583c140500300c100c03a4014101c11008000242c01c020030552680300d030035503021910b00c2e0300300d20104010041143e2010919601c3e421b0b5100c0d40c5034500349448000c1d400058908261012a106261600d0000e04003151016100d4501e400510b05900404d10309141c10401c0102e1481c01000d41c070080240c1039074040840d650005050350300b44c45c1074050306001400e6100009000c0042001301d0300c600b070440d003401da040a41e0010000311001850b003c40410101c0d107400181c0094083c5d645100140a00510352142e1480c910183d102c0013484201d0300c0c101c513072072070b610a034904000250905a00a6401500407000440d0303142030b152985103590701c103440481e216841002e551060007079406011a40c00b0f032501e495800c024000c040101c0074090011120b445000401121041600801c804008200390700c28002c0f00141d0311080d000261103d10403490144071121600a001110b600014000380d40c9803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 936550791 1250 936549541 936549611
    0x609011107050a12150c0507150e0a03110c010f050405010e0a0f0f080d140d18062a03020f03040b072c0103240302130f020f040603 58
    0x400116088000d524003034040d405074103000b251544981110002a000050030550041c0341c602d0040345420a02ca404040e1501d07041d2456440da83c070408849095411000455600c000003040e24014540760185049a10891001c4020140c1048403000342440003010303a80c40d1043e00005440041c00c822440380051000c110a020341d6004070b140817200140640403076030b40b90300c695910302051456040740c50381050210301081050020450610080c0c8949888140c21140c82e152101034045e080401c180c0c90340f07410150203400056030880f00c00e07981100041c0405002400c2d80d900c031600710b841c50802046210b144803851070184c001c480031482280ea0203407859440351140c06040354050700403410402d5403100030075200d95607403110300d100300001a0004e4118101002400f116059050200800d0b80710010010f440721b1f04400e5821a60180e590001001c0c02040c1d04d4018804208a2702c88544041030201c0200d0b003041c098801d40d91503407410040078100724100e42d540500c43c840b401c07400d403c02c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 936552041 1250 936550791 936550807
    0x5010e151e07060f1112040f0f060203040303060e0c21061c0b09070f03050607030f0b100305040c0b032806050d0b0604050c040b120c04080f0604060e01060506 70
    0x900001d250385015003688545201e045203215180d07074401c070000c1d2111900c81c20003020040f042c0c0702e12141d002428022034074141e041128000281c20040c00540310241102c901002c0c1b050b6010b4800f0841d60002c021275403841e261030702800401003030080d041045021000103407003003a240d0448102654032144481e900240503000e191680780104019002413500d2441d030558059158240c600703512032040710200745440c0300384038070f40a0280d1003403640d400c111104101050300490140c2c5c01109500e070100c0e0109900ca0000c01500340e01081c1a00030354500c10a40c06560305901040c0114422120703030701415602c0503074202601041e508c403594140074030b843c1c601190884070306c07a040301e141a20200344250340b24000350b10500b01c014103480b6000950708009551405201e80c640c4880c90724042c0341040e04000d203000e203900468002280d40d0305139a010036103103030390306055800501c81d0508842c00540b0031002a80c0310142a01c00320f032001e0501d8203031030f0851018042d440c1920006080c4a04204070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 936553291 1250 936552041 936552079
    0x27060c1c0603020303040b07060c0f0509040e01090206043011090912070c1e03030e0f06040302030f03041d15010804060f0509070510080402060f0c150115030605010e 73
    0x841500d0015030768540010058400307002030002495400c0c030b060703110421400d11000340c54454514030100001944c80c016555000700656083c0703a400e44002503202c0c01200403a0042031074000180d44038030042400206c03c090700d11800c510612030340248609007412410080000402c00c80207011895150a00d441424181e02c0c90743e004a0780c108030b4042840d9980b11040a5000c203000b0345868102b0b4105101d890740301c02005448000600c081ca24941c1342d5103004001c00c4600e000a441030b502814a140a55107083c260741c040c41d0000d0945e010030091012040c2d03294082d00c00c2070b03c5070303980c202401c2c55100c203000c3c201c1c41900007850385407140b80e10500454280d48018001c8610541d5041805104001886520b1181001c140103012490900c0c04001144880c05031450070810f01c0010000141c0342c0700250b5410700c9018064546aaa2803103070303941000c0500c01c507802e04100030000001c00c0440410480c2d5a000306450822205880d90011281000181c03c625040b0340701c96104200919 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 936554541 1250 936553291 936553327
    0x3050c0f102904151205071505090928062d030b0f070c0803040507030c050a0305100f0e06091605040203041208180f06060307090e1e011427060c 64
    0x800142103100d42a1a51444117090880400640d550b620503030092092016000140000151500b0454206120f0200040484000030542243c0e0382c055980c2841c0c0180003200c000f11020917035414400319413280f10700040c11035030b034103940050309550040203080c1a10301098400d40f80c000e055203145544482d60000c0c20b240c060149030801100750740b0000440d01420141d8000c921a8015103409031444c20440403440c41500f24611410306c800341000015000210380409000d2090045001100810024020181d43c0101100ac1c0920402c1140309400490006030411401500c1c400c0c4948840031f00007240001c450047c0265040301030000100d0117404001c1c3d1141842c4901d4000d400041507580c1480184000d104083c2c1c45513007032001604e400d201d0f10b4040e010803501000030070104c800c52139031803002c0003170006901c841c0c12a2070701c124429080300244055000c032048680c1440c4500441845503400c0f2101d08221405882c0da02100c0440d40c28011005005002e0500045d01d00d4509020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 936555791 1250 936554541 936554561
    0x2011410151b020402030a0b0906040c120914061e012301031d010612140303070f2303010b0301081e070605090301090b04050a030206131a0403050c0f102904 69
    0x502d40c0c01c030001a5518001144140c009850210721a0328503c00d0000310040607002d02d128a0804035141c05403548800c441100c415a0100481c03141480d0030007682c420f08546100541c1c0c041e410411600b4103000c0f995001d9800d04000d09030a070380c0e039440c2c4081151079411103589194a441c000018035882900812641a2488512a21081d0a1003000d00310348107a031060000f4030b91601c803c7d00340000d00381210344180f01100950f2544c5003144004102c403031007854032030500000d5400820000749410344107045040951005075656155020891039030402d208004840c455600e4001c00d82050440b2034400400c00b000500d806400e01c90141d51036000034103500e8240d0750320a050f04c0480d0045041a00480c0160084c280305c21060a00a0501c0c000500b504884c10524003400d00040c040d817880c07803039922010b42040c441d4880b03207001c80341440342e0340c2d0303203070300352058048003682c05102150724031110b42c50f9031040000040d04101d21034804070400d1210200d15a10045451074100340c2c21031030240c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 936557041 1250 936555791 936555827
    0x501150c050a200a03110321040e040816050a210801150e09010e041112060402010503060111011e0f151202030f0d080a05180a14120a0201141015 64
    0x4a0840340400c0001d184d0358000d441c0c1989028200580e400c00740201d44140460304c03151a18043c032030440020314842c91044903081080100003900744400f10307003070712540e4100e058010341a00d5103051a5940e92400d41c1c0035519100250030004118200c040070300e540d100c0980358681c1c01d07860b2400c24600703522907041010030f10a00d00312031900c555421011602800b007814000702a810b050610a47d15900102d5241c0141c2864100c0e001c0d60900143e0160300a5091030300c0f540e41d84d034810048841505075002e01c801503082901c501a10410440540300520100c2010049201240f04460654440036035601c090103c081c1c0900170140b0340604900c0d4140050100d03a00d0140024a9910307044828000ca00028110001c1c0109004d0354095541c000c088890103007407202030244055254400e81e140104003001c88980d0000b0300c1c3d4240034850744104c4240017075448200c0040040e0180000f50f00020903032004500285d8030fa54200700076001c3d9400070f940d40c0c004000504060300c0c0c189101c05000d0354 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 936558291 1250 936557041 936557093
    0x90d02011d10020714040908041418070201021b070f06080c0f0301061d01180b0306031c02030a0e09090a02060307050906041206050604050c030c0d110a030501150c050a 74
    0x14548541200b00c48068159006051403450002503000030901008a503100c2d508110070840801e4913402a20203988098201c1c03600032125100017442641d18405c0c003a0783c00b510004000781d0a03019800f40c108142507106450500e01c5918031640c80c1c0a0a004a505024240e0028804244540758003a80010000c228a1400d00f4510044000342c200b688090001340c0b520a54010440b00c43c82703810701daa0020308003440d11420810003210102d4403402881140d80000c000203155541c104031008200c01307900311401c00c500000310003e40f26844944aa400b0446a40e022009818861409842548100040d1034820303515420400241d0020f8030314070030010f0501c0158100d0303031050020001032060000c0d44102c5d4201d490107906031500140f080c1d02c164070300303001c01459001c01800c0702d80c40350346514840e640301d1141013101c0045c00149800500440c2c0445c0303081da2282c140d03220505940c803070340401c150501c048004444200981d80c00401c940c01c0056032800142032007081000521103142c0c2145 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 936559541 1250 936558291 936558347
    0xf060e030f2d06010b0901050c0316110f030c130c090f08060610020606010206070f0203070b0a05040c080d02150a06240311040303140901030b060c0c0306010b090d0201 74
    0x46410380d01d100d0080d502c0c0e680c01c64032045540c0107814168150304007000d0300c0030f5803408441759110700420000d14140600010345140f90b0380b041c421a0400703400040c00c10002c0280b0b091103000c040c4941d440da40100c0401003841042c2c5400100d201c14201300420003144800c03103081c80401b1b40390311480001031159082d00852103805a194076800382040a006000c2031405e84104542d180300700601c034055400000a20a60b81d9000c182594424006d0402c41052502030808a2842c0320b884030142881d80040b040c007007982c200d5004140200e01845946003125200c1d00f0031620303001d00840c1c21015a106182c0700c00a0b03412020000c0e480030600d800002c01b160b445040c2104400f4418840082c2c036070303c18035082c1c1c00303400d8032980c0021182040d01904040c15990060581902c8243c400c1d1040004030304005581e00c617030451920044054901505c07214001d01303442d6581c642a44440c42805050300201da201300c05d00645201f850000c0c08080c05085540040d030f10802c0646a00d05580e0408610354 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 936560791 1250 936559541 936559543
    0xa0f0908070311010507050306090601080711070e0a060b040501050706050615070b0601090e1e04051c09150c0305092103130e13030915050c01140106030c090f060e030f 74
    0xa5168000d48860000f014064182400c4810040002c0140002070040c0701103601c414503002c2c0d0051007800c1140e0152901d00090300c46011b5040c10010510827610041081505c510625001308446002480541c1d1070b16400b0805006034020b0310b0024006011440204000381c02003034025078040c100c60240706248480b00101d40c0100c40a079000b11107070f01407020951340300c00300e0b43c000e285503a808401410401c0001411805c0381c1c0c0c00c0b5203503d24a20200d010b001040c4030026036188812007442c6042d102400c06055400c40348101140340f000c8071141405e2a00031207100c203049a1643d25989081c00300c0d4100108856891031000c0d4807070004820b4030f21400100000c0c800d0b0845110f0b02c98006240000066240800900550403e8404c0c1050307400070f50004003040941340480c2882c3c4926000c81421980350040205600e000e60034404010710b00c001c108c0301c507416500d00355024444a4818042036410007058071880c9210130b4034640800c1018443c40a4591800000b015502a400c2402d216 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 936562041 1250 936560791 936560797
    0x806010c150f050402011205010312141303050a0c090e12070812070909153c060807090b2a07030b010305010209030705030d0e010f0c0506180d11060a0f0908 69
    0x11980b0740e22070601085d5030300000341040c408a54082809150304542e0b0352003c4101808099040c40f1b6030b100c003d07104442403410707500c0e1030098607804d030225035807070901ca941e03103084a1003503a448005a2001c2565051070283e00c40880e000001040703c0720298184c04a50ba0001300182d0303c2010500404041001581c0c016005601580e1400785190030000c003e41181d08840c260b03a0400c01442c01001010b03c650400d0350001c50b00c41c1802c500310300280b00d5540c0880300c3d0400340207540c0c13405004910380f40c0141d2170601900c1655101240305444050608841c4258002e0a4200e0680070000701d070521aa0320030010701c014001070301d0b08107550303a440304c0c4d03080c0080c1c10884a5035000f180b100b040d81400c10015001340811002040c814101c070780c0c0902082e0143e18028100004100d0a03541540100460320400f6409002c03102a03141440f85005280440707010001a8024068580304881c441e020031116640200c024242a032140100c0d1801014413603c0004601e8454004a01254004010f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 936563291 1250 936562041 936562061
    0xb01030201050901050d05160e0301091a1e04030224060607020d1b03081209032503020304030b0702060618070504090e0a060c050307020c06040b0d0527070602060c0301060806010c15 80
    0x30120623409028042d0801d079030891001e0080c6c1c0340444010118404840b0300034070281070000303144c0c152a108280c40b0440c0e443e8010b07450780b00000c0240420542c0c0019800c41d01d01c89150044420030520280307440c04082694002e0340000144150409031a00691042401c3d22602034182c0c1c2200d051080e02c64100a07500a030b0300c00c480400d9104405400b0107000d90320852a00103036241400400030205403a54003114196240c0e85400044105402002210042c0d500000414803034901960001e550710811206940680260940d0601d118000c1000502840d15034807000d003040c0c14284650002d04445049021501c6222a010041041841a0600e000840e0380d440e58a140904002c0e1400a0032880940200001c1104000041c030314803e03124849143d40d40410181c40c0c4030351440140a060941210003881580340280e0f13880001810301c121041c90b000e442c10340c0c1d104a480c4c601c038002480381e50301007000800040d51661050050084c030a10440c90079240ca0794181c0c00104803040412 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 936564541 1250 936563291 936563311
    0xf0f010b0906090f191818031101060e1015091a0d0603140303091608071203033b0303040528050102030705030709170d0e0d0614040215070b01030201050901050d05 72
    0x1080c842c502d030f5624010380e0346c403210505001004a401c1c440c0c04035025844007408010441d0152380b032603035080d000315004020f15051150b460800c680e048220580c2440b4004400241d5000206528000d0340a2001c44000c1c9013521f144417144c0d00c00070042d03807280c41c02e240c056503141f401000080024007104880712a000040d5202e00c4e01446851a0500c203160741d0f02800b44c0d02c001000081c0f8002000f500b40c9400310000f140a41c941c0c50b0590140c140b05403800d58036250007441c0350303036940e034007021007866045c00f5070442c44900b01c44105d40d201e2009841c0684150010360702c85e150958014100d040b50b805281040e920425076031110b6007280c106441040014200100303010383d90b588040d03210060722644010001d044125540169111a12401034041c00500301014070341d95600082c04500075000134080c40044124601c14501b000d007210103c1c0710341100041943c440740d09070141e6502d664005001e09040e400c0d40c005440c82d07006140f0150400104110b01d40740106580503030750052416103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 936565791 1250 936564541 936564589
    0x50a1e020c0f070e07051b010c2106030312020f04121103160b180f031207020415290d1a030c060f0a1101060306020a080f0f010b0906090f 61
    0x4030740c55062800c440d19046159104282c10300440000241c0076070080042c2c01e0007586ca000c0310810b89002c0d65010100303030300e035441d011404050740e4200c004054a54171302044100d50124450039101190454013000e40058540c507028500f01c180e9034020189903061541c0141825076540380100100403889046640100301480c10042c1d060400c400401030344d005901c100b80f03d00f420380d101c0d0380b402800202110707800ba204c010700d8551a200d50108403c80c001d4280c2c0c00350500b4042c0c00882d94006003040740601d01c0c00840100b02c405031038854064070074840824010385140300019007900300b4619825031091301004948901105486120f02c1c881c150183c00507400e12000805003480742012916010310b1081000681b0150868201c0d03049030114100010f4100400411600504858000403c050301c00a01501040e41244070780c0e100f04214400c490940ea96155810f0001e6020b100300c1c0c0341d0300010301c1000e1040c80c110014010804010b003a05408102c41c2c1c0000d680801c0184402d00e2602206c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 936567041 1250 936565791 936565807
    0x20402070f120201020313060f0605060c03120c0712120b0d0605040302011a24120c09130c050315060c07031101030e0604020f010f05070515070f020105060112050a1e02 74
    0x1030b000a001009540003c40c1180b800301c0303c0d03d50035480381c0c0340108480c3e610894146090256403202020306005000d00f40c03545064000c6c07542c7c2c0d9010806039000c01c0b103c540000d1411403000111400e40381d228018070111030070504152030220004042c07249040e00c130201103282e03844000ba8442c04900901d8007103624145414040e007102c0c1540e01840c4614619003146c001c5803030302c0c0c0d5241038a0444107403984040904000d904000c0c060080030480c60044c1d04d0a000e00c50300031a000c0d02005804580800601c8985071410781103036040d40700f240114000f0b00004100184c140b02c05000d031100a8591454204134603a6a810252030341c104840c041040700303900d19a942d0520a1203a2809100000d04a46c10641c000441d404001c1c0501410000820040b486261003002aa02440c0e8044100c071246011100070380c6201108840407000103000300f80f0813400e1032050141c28050380040c1c690340d9010400308021400351070001e00406c2e07210385954500c040782c1c6200c0d50900295102120050320ba02c25 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 936568291 1250 936567041 936567053
    0x20304050312063f010e030d110406090b0d110c011b0c0b01030803090a02030604061e2f0405030f010225050d030f0f0c02060603060c0a0c020402070c03020402070f 72
    0x2010381803c4c01910300c0044030402c010b240000494421030f007100071405541d070050320303401c42c00c03640c009034803550030401c091249180000107040c40d2004004144807402c901c6000b0006800ba921460000900121007013000624030402054100d0001c44042030b0b40c0d010384000091680302642007140faa644401440304a06c540342291207464451500e90260101600c80c460b03980010302010f4800380000010600704036082140484080e8050241c80d1207180600340800200024400e001c407555103003843c1c1599207102d10401e03414502c410409031580d684c2500c44808207410b80210110054100401708282d6010407030050601d03003401c00541d69003440c01c00d4441701c0400c011001c0540003500e00c11400580045070b240d203000041c0c82c2c0000c10f03c040c40d0184000d440e40041c860020740c60f1a003a44945d543c0841c400d4411402502100c0c0d090b1121900f40c2440d00c0344003842c1c40010600d1b40b00718010310300340d0010407000d801003903c1505e0a880c0e400240481e40030760303030440782242020004010040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 936569541 1250 936568291 936568327
    0x308090f0a02090406020702012a120201051e091905030a2607081807090204080715090315020f042411060606160c0905160e030c22050a0b0f0a12060c0207090203040503 74
    0x41c01e031008ec406c500f800060040090980c40303410840340c1d07810700003817030a180400101c44420341d03c62000d0683c042c107040c030580f66400b400702e0600040141d590040304100089400c00106541da021070101c2d81ea400d401ca4600d600a8500e2925a0400703010b10315a0000f0811040605079150005030b99502e031400580c502035195202c030401c0304031544260000394201201008482d0810850b180c0c1031348245100c1c000748150050700030030000206010400d0130910540420140184002d0303241004a18400d944032102511551542e50102d80060036134113105020702988850162001801419981c1b407004800c415000700b5140b41d9210108402d08010501c110712703128040c20800842900c48000c00d4440068100584c003810020307040401d24101590313105084486040c0402190401404190103088014200ea215000d8404503140c2850240003440444d8100c040f054922103095541c4d6003d007074404100001e5000c0d6800014031078015000552080744100081c0d6030310102c0d8500b21120752 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 936570791 1250 936569541 936569573
    0xc0405100e060a0e0d0f120f08061e041e14060d03050306040911030d0909060b0903060412020a0b01030804090c03061815120308090f0a02090406020702012a 69
    0x88036042580d242c03201255055035492801a25091401011410012040400400280105c0c0300c140c1484007407400e20104100301c1d91441c1c07000d48509403c90b071030788081c0c440d6648000c140d84c100c015060358504c44040c1200143c000304807882e5580c060030b1503043c5100110001901c80c4180c5032a40c0416843d19403041c1c040300c1d62810041d031520020207038040103041c140115500d9038002c0034048094003604401100070115200b280300c0400007449a2200d00c036503c420f03810a00082460840300c0103079446a000a002040c95555641b5003140745070b0303500c04c0602980100d00241d0042107402105601860007444125611403a150318070040756400c498100401d440d00740d0074480c030000c1442c051760314008485c001c2041d039100300f00705559174800d5001d19482c00669000c0340030181c020043c544201c176401c0039114840510380005860300c0324030344000e611039106400103000aa099028001c0c0c0390042c500403414800b401420001030004000700a425144465003404101170840880c6c140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 936572041 1250 936570791 936570797
    0xc090901291002030708121906080d020706023f070b04050d09060c0f050708010204080d0207090605090c2d121303020303010b180a03060204031502040b090603041103060c040510 78
    0x110426032038440143c01f40f64111180784180c2008100080c4504100101c010108030040065958528040390b880100d107403100054043e440f0002460350001c1481751900b86401d801600803881e10940080d03064209504090b0701c1e01040e2a0300741141c0c50704c0030300400c62060719000380761705290400e90300c1c280044800c00c0801400400900406130300c50aa81c1446a00c81c00d681c5041c002c40c5030042c1004d149400009140d840802c0001d13240c00001030b82c4188003002d409548001d03855000c5401656024005d203600903115101240c40719148200502c83c00300403841c0d00c50401e04000074046c0100142c0360100f40a02d020401124000a4000140e04040c00b0503a181503540f160743d01940f01d0005114161400a0120310030100b41d00d000c00360800a03200030916410a0748900c1d010b0002d4115020503200c1c00502c21880c80b21500340e100300d6059402c01d624442c02c102c05902007042c40c1c1d200410032101070303020080d50240d54804202d030601441c000340c42e50ba240d501701000e010024841595142c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 936573291 1250 936572041 936572047
    0x60908152a0d0c030515010c0c05061b030a02060126070302040f0f0608060f0c0f0304150b030d09141012050403020c100206040b0601050307020c09090129100203 71
    0x2540036107a0401e031000c0e4041140c0c00508144541054203005028000c07607880d0801d2001c100300f550540c0b00e0b5200ba0b144450340c81400001100440d060280754100800310407201409002505c1c1c0b0001070004d80317861003404009515503030141c41c00c68100313002d0f6001592214005202144000c04000110b08091282c0b128100064210903075076803152101030b0180c1d940380302c0c89583e111107401c80e08071800d180c8030070712640355605495031f900e28080305e400c1c3c401561a00800d880c002004100c40e01c402094240c54219201d0b52a000e040a8203c61286043d42d034551810031a5207040c0140030360f02820340c4840e16a1460151140844001008021b00c100c26100d43c003102c8503009911000b4100d9100c1e000201a5550301d02030b894842c12403041a03003d441d1151114032aa400269a482113116128010031925100c005441c40d000540d10701c2c016030002c10036903e01c0d044c0203010950000d01207002103010703610400d00e6400413074261701600400503440c240070020f0805014400200c04184000c41c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 936574541 1250 936573291 936573301
    0x220b0a0b0d031b21020c120d080f0c07150f110306060a120207061404030e0301110d050403090b030a0207020405010b1602090a0608030307120b2d0607080406090815 72
    0x1d9480c01d01143c04011884000c40900810318090016991290302203588103205581c00b035901d0384205070b1244240c01ea0f06004407440303404109110310454075160f0070080c4c1c032042100a16540010032000514000707000704c0d808601c0141d0349441c40641d10000140142d122240d1000382c0307600c07501a0240e42420400e00c00640c56050403200c120419250001941c44d0044400c0042d1040320340c050160382c100208541510700d8a000240181d1003a2195404c6228250a050076908008480071140d0400c3c0092102030359140c2003030364818440c1c40d00c0a911070311201c20180d1030f00283d601420003a8042201e10450815100301c50140c690942001d0600c1c0000c2255001c54100140003409402500003140304036516411050107807905c3c8094984078500840018002003001c05461192806c0c6152040e05040100449008455070f4080d107180c0801d0801894450300c400e10b4507a00840100701a00108107002c000d4405001c0300da0314600e1952802612615120403031036000351084110017400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 936575791 1250 936574541 936574547
    0x3050601021e0d0e030102120106080601080a0608060c2203030f021005010b03010506130801020307030f0c030911010e0d050f033402091909060507031b080609220b0a0b0d03 76
    0x650060b0452030420f1071301290101003030190041d411a40f00c000c1d26400003080440c1c00c108a24482c000030390ba41840d681d502542c20054074a030744500c1400e500001c0104114648441c01000f4031a00c850340103040b209608114101c2582e0781d401980020646001003180c80d074140096000f44840e01014002da5040c1081c1f02018401072240c0f80c031813100080c180c1c51070100c1c22800340080088200840d280d140080028014120f1110380d106518a48681c51440c14024840c02c2d4070b00e81c01c00041b204002186005403103940350540003543c04200d003805040064420840008050000c03c051600c031103480e041c542e80d049005c0d046040c515054842072002c0c1e42026a00243d5540448000e606038551006502c061403030000d00310001803c2c817800800f03003c100d800050140b8000c1d6010052403045028501c40390464202040000760f0700d00c00300301e00d450f04c051000c0c0c1050100079499186011004000c074942d10040d4200d80c00407206080000b5a404d03807140700201c800560f41ca00285820307640007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 936577041 1250 936575791 936575803
    0x904061203110d180e09160e07020c01030219031a0325060e03120f04051c020a06020d0c0803041e050f0714061210030c061206091a22090303050601021e 67
    0xc09070817140000984030642046056000d40d550288403a0781d545038200d038070a0400480d0f40c80090710921481d06030f00c5d4400c0c400c980e0483d12122501e020092100c0c012000341a41e400c0c0b051040c83d612a2848a6a4060180b15440514000a0386400c14001d4040c0c01000c1a0ba02003010302000350814222902d010070400b082e100d00100c01b540e01c842da03001140e854080c540125400ca103d850340d400e0030b41c1d44030841c2400c080c000c0f5032181c1344903130b039610480c0d0303410200c2d10010004900c0c58400c400510780002840d0050311494003807000c2d042c1c00200c0465801c45240c2959658403a80001c0c810001c10712140c0050100c00110482c02c0c3c0101c80410860712130305620307904081902002800d02d11040c541600a103500101c0e40704030aa8880000340b005103803c00c01d4800520700b14001680f41002d2041c0380b0394242041e043c040d0715007800c041128810140100c180008907110300d01d0445901c0c0d11070b0b00300c082d103e6100020b183c1401c00c00249049110801c0101c0f03500d0030710b030302c56604c0c500142d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 936578291 1250 936577041 936577049
    0x12050609040b0a090c0605040518071b05010e01020f030412020714010809011d0d090b0702101b0c08010903030605030109051b010c1a16090b0f0904061203110d18 71
    0x30641c0c01e5241c0c25044801005200b20140403801e6200010a400c1c7d03012001300100c07441210902081087c4800820800c5c8082d00d001d00454240000c070030707212050915003e503890243c4000507010000f8000795099078012700740c0440c22a40041080b040140311140b00c12800b0b10b501c0100155400c1140d9080300c880308500d0181171000c154002804d00109401203a8080c07403030449280c1641410760314541c1c40c900560040081074451038040b90a00c055825a404280c00800281d0a0760070941e0984070841c035800d21390b2204580212820110324000c40080040c49444c000107484030060400400700c0c1e0382900440c1c42641030400c41c2e0040b03000065a000144071400e1000c07450062000107075481c0d0f19039140200004c0c80011f014070032903a1000060300c114060440c1100200301e09908848028090007040c4000f40301b2302056024051000181c1000030001d80000340c001c1d100c0403911030040c00d26030210300040c04c1841a04800f54103000825003070400b41000340703140e1000d0701508006511402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 936579541 1250 936578291 936578303
    0x31f0b1005031b090d060c0c020111010902090a0207110d0f0b070e011d011209051c091508090a02040612060f020405133b0f0604110d0303060f080d1205060904 70
    0x3641c6611585c1d400440e00c802544800e0801040c6199280940201c00c0c0b0001680850380c6007200303051110060041c10304882d0300909102041d900c201000000b500040f0056540da0100c10040e0640c2e00c030315407242652402062804000c451703e1800b4016100010004400c01480b4501005140d802c01c20662305480c4451018600b0218000100d135205603c944000e0507500702071750034051010100c0d82c00007860b01100c900303e525400140a69040309144078021424035182c0540d03032828840c4450b1038126010070141e890f04911900040c09851168001101449103951b0480400c0074074450704c2541065810305500303051030203001610912a20b940c213030140b520303200303c2014580c0c250004503a4503d004110300340c4150411590348800194410a061881200b0100e00200710001d011031195902c0100440a211900d0600c4810240c4ca28100e040c9621124040742002c030100605001d410104003c0c4140005001700030080d00c5000741c03490006103003c0500405484401d80c0c1030380190040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 936580791 1250 936579541 936579547
    0x1109100e0f150c07170a0b072609010c020607090504020c070e130215030903040603111b0f010b011d040b06071406010512031611031f0b1005031b 64
    0x80071403071965008003103a501c000600d64611070361803068054401c1072019030455841e243ca030300c0d41004040c80d880602442d9401441c1c0c0e03100092034450700c135a01000a00d040c0c07410408001c000e05c0d420030b130480130b801400300240c10051078220900c90058001c0301031000b407403541852580503001d41d1840c080c0703e008680005070031004410400440c00100305074445070000b45041c3c08031031001a68548120721603200c02c40c00000d80e8550700e054a01907074a035009103203020303d0020107a004190b4140d0111400b0004e105c0c040c029a02c41900161000d03144014141540301882054211194696054148059009540e10b000419402e21644540942d00082c440610341c3c0010814081e100000740321407440786004004040105140e81240c000f86d6100001c03a1507511155120b00851450000040300c180340b0601107001e440d111a04064041c080d640340d00c80e0b244071100c90004415246c175603503441d41c600040d0b50518a0000d00c0820720780c0307015421403c0c80c1109808030344801c0031807044201c1c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 936582041 1250 936580791 936580817
    0x11d0a060f0311030a0b010e01020303150d030c0218090d020f0723120c0f0103110706270c17010603051209031c17060a050a0302151b060109110910 65
    0x940c8050030b0002400246030f10317898144220000340008000090008007000103001044d40000b040d240280350400b02d490300040314509000c42100090419010002a0082c82000d07031030301403050101001e0b654182865107014a40686842c0841c0c500d24110b60201c540044860804038090050310032104509405085081884000b5101200d4581e88000a8a00398804110004440c5081803091ba089085c1084650064044455034400b00c0b813112410090b4200044641c1e003d51a50885503201d200c50010014984550303d080d10402c45001380c4040742402507511a401000c0c01d50342800091089070301f150354075a01c420203568140408080480d0b0a00345650030b004c07401120041e0724400c800d170f80304560014940000040c03100d201804020100f01241480324607601510b1020b000d8540061466091000711180d501c00b0050140c0184403107142204e80001c0300040c0340d000401040f040d41000011821250440c001d500e025404004030286510f4581c0110065055824031107420300310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 936583291 1250 936582041 936582047
    0xe1501050f0d1103030c03041503150603050402010903170901230a0c170f040e07020a0321020409050106030506011d0f010f180b040807170717030c0a11011d0a060f 72
    0x54015144e07458003011030038a600ca100040540b049584a200b525a4980100c0069003140d60080240711950b10000741808014020b402c002d40151040c034001100c83d0352a1100000520ba44c450700171078000001e06102e82c2d40c6d01404c41c2c4034600c10300101c1007e0701d03415035a4800900c07070601d008062189a20001c5d042c42200c41d03030340c85038050100010303039280110000701c61142e01c80d0003861500741020303000c203280324800181009030b258907403500303000c2642c0c11124146180c20a081d10314020b07020030010032403412a00603d03000706070a407400b252509000380054030310046042e40c0c10401070305020740040395948001413140d0608c01c1c20502900400c4400455003038280c82804403814000010000d420400b8100900c111000c030419180c045841d481340800c0400640500c615952084405014689103103072030301510390100d42201e26110300c01c80601e0905241c00e005903100c00f264480c0e000d5558001c40e0040b007800003016200004100fa0001400035403150041104014060026003207282c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 936584541 1250 936583291 936583313
    0x20f19110d08070804151b061509110a08061831050a050f0a11040b01030b18071701180c090f0e04022106070f0e0d03030e1501050f0d 59
    0x1400600095a034101804c0111550b071003403050304148a401c000160100784111000f022038000115807101034010b5807281c001802e030042482c9450b1003440b10005d186189440380004006107080410f0304d643c11614042c003080001819580940300860040f41d20282d40180180e02887c0c0d10702c540c5403140c0700d404804907001800c007800d00045141e407010f001c0c8a800203490602511600c01c8408820b1429845070300d442e00781c1002007462004240c075180da0f10b0709820203180440189800110309000300c00044105c504840212006507845051044003070b8001c95044000840c40c1001e9640e500d8078840c1d020000015442c22044ea650341e02042449101c0e40a0394014003c0c6655000966100c2050451100080e10224402ca440d44260303000740d8440e20000c510301c00a64050613065554000544d50015000a11010840d9442c01051583c1d9203500309000207000340c0e400149541c0003013400d45804101034002ea400701652004101c4c0740d44100d0b00c100203213016690316010324128501046126 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 936585791 1250 936584541 936584543
    0x513150302060d14093c0105071121090415050618040b0a0e01050607080f2b2c0f01420302100e0a0602010c020f19110d 53
    0x208000a9003d488002c42d040b0b14800d1404a03201341c201d440310a90595141503001c180b60340e01003001c0640b01d03145013000d5504030300d00c1c02c010b540010302d10b840b88071401c41c2c40407540f08010a404500c0c00000b088208038003d05ea80d252042040618403c400200341409601b80301c41c403554035850010304499400c0070100003004058000343d10342c00c08468587d107005a14980300e01071807400000540600e000c03042c500c11240040c03042c502c5a420001801645e40c4070078001d842c9032408002e01000c41759003000624040e24061102004100d0b0344240000440403514074890031070920300c050300301c42e45501000d41d442c400310110920b8038058141040c02d103602004006100e510701a8220700c1f1342c2c10031004440051403d8003412f1415190f62400d44a8012020508002c8081181c00e00060901400006a210b29424829000130b0008000340c0c0c050280d8000307030010307510f0310103e501140d01000901d80c0b4440c6a00541600d02da00c404e40c1001504011000d4201c0198020071035154a1b5005c0c051142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 936587041 1250 936585791 936585799
    0x180e0c0913020c0114150402220306050f0601111b0a170c0108060303040f0614090d230712061d0d1116080604030e030f07060215010902040513150302 66
    0x80c82011401000f500a0100ca00c02942484a034091555450310702074400c100d00106c01482071300c01c4062200a4001c0e602124040b2543e0311a40803080f410821803004500c42c01d8081558581a08081c00b0480060300190503c50814418040214082442c2020103201031407541e804584100285500d5913542c02690409144110054003090201d8248100c445c00e8031060b04039250f020606070389109521500b2481906a0814010503200700c20003604000040c0351503041030031100000b021512486d0084a603428408640400501401c1e42c220200141501074500b5a140607495150210016001000c859032078807402c000910180c08001180b480f6002c0750944120750030083d081840308000784506208600b403d0207200c50140d403840a4a400b5005003400c2d4680e50350540e800c02d03003610010b0b4036005690b00811201020007000005092560040010350b4a00684294621040e00060311070f03401004140040c2d1204030a100c503501c0c000100098403500880390200113111030700000e40c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 936588291 1250 936587041 936587059
    0x15120613210215010f0605041e030602030708160905031207061506020f070801020a2a080a0e0901050f03120c0c060301090f0e010603020120010f09050a03020d180e0c09 74
    0x10310b0360010f042c1c03209105019002a140e6200e40100b144d5aa6034400e50000400401c003e20141425401440224541140a140300e03903ca41c0d901040ea0002c9469000040850003003045914001e2441600116681010045d0350b0070400400c0d21080192404114403000050344010001554400360240d071b8582814091507807214802516444d1040c802c0c18030344034802001c100c905044c803c44240352400c0d01d9200030700304002d49622681008000b0501000383c2084808045602d210081948018540d0f41259200e0f201c010003941e02d030306030413160081d107854080583c5520001880070400b00790032035442c4c031888910b018926011800180c04d40041d004000000c50625603000403a464400c0d54090181c10348000402f0300325486440040d001400483c544080c440c400c2403000518549000049004580062414280d80c0344aa0403901c66009107452004e1590520140400c420149040780b807861200403000801c81c0240074a607003514265000c00c004035603423012642c1118000e0a80c2c0d00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 936589541 1250 936588291 936588353
    0x30f0c1014010e0106170a2c010f150806060904020307090e0c10110c1509030118170a120c090509160201050903071709011803060515120613 62
    0x20310388200b80b048190100c07030303c070010407514011128a58800441c80300e0000c10b42d19840c2803c0504050309141c0c0101010007429441140c0c201c3d8055018034170400042500124100d54504075403146814450b66030141c1028801d640c4d02040300782d00040212408130050b220347c00028107214043c4c0c02408901c0c40c001c4081c800701d502244a00c40c0442c02c50b06c40d00a9284a142a201c0d18a1608003115030342204940c41c03490320b40b03040c010014841b01000c80d400c284880e400b080c2141c02064a03500c1d85c2c5070700d0104804004400c00b00c00b840021071210141008518070001e800b5446213241c1b08d500c96102d10144100030312405131580101002410003426007809084441202c00b5460710400550800307002904500c000800c4818046d44481040064a0382c0000c8104c0c50b08030b00b201c03a0410a111081340b00100908811901940c0205400103842c10402001d8081c0324a161541d40920851000c1c21580c000201e0140d52041c584148011004958504903800f08109002d00408000e03200c0c0c244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 936590791 1250 936589541 936589571
    0xe03030f06040c091d0405010e0d0315050307030b0103150b0a03080306100f0c020423162c093c06030703020d0314190503090c0d05030f0c10 62
    0x5000701c0c0c0c1030364100100800f040302290301d04a140141010050b48850b0744280c07000458009500501440c00004c0005080d0140e80c14052980000c00c0043d840c0c1c4051000074650012840082c40120018400d01c3e2a551396420302001c144005441d9501d500c0410b600004035800500099100800d60810140c881c41e00000503002601c5190040c1c050803141c0521500522003415100400c0d01d179210459141e500b040003525072200380d00003007001361054607403106640304250f000c0c1319225a10050f0407202c86008050a4240030741801078030383c071080301c1e86064568022244015080d0f4100015903110404030002c0311040d41044001d0b110b0341401c680309058283c003000c0c044200004004541c07074200415549980c0d038000603500c09140764214000a001c2c290642c01c2e14501c0320120304142218901c0c0705000b281508140104100000b0400d900d1014800d803e40c200d0304445620100c000398945135a2070040b0420960802c00000720007103a44010045003520241c54001800f10b40d082c101ca035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 936592041 1250 936590791 936590821
    0x33008130813060305060f01080604020c03040329070e101b0b0c0301170105190c090b0408100f020309120a090b13140618010c0305040e0711060c09010504180e0303 72
    0x1040005c3c81d01c0e000c40c4c494540031880c40c1c8010710594402c02c854072034404101c003c0d03001041c0041284010080000044d95241c20349a00d292450305500c01d007540c070003c2e02d0006800410305001c0268490346141c00350b60b1460345189400d85890002d000107880c2c00c1c5410170001c803850240401070310344100240b03002e466000b036068618600251610011100c00c2c1400e8034000d640300101071030350b040b41800c903250301d6010b099920107500d03060380c90035941e5024504540c4260091002504400d1403040420801d00440b00790800000007140b940c40d000212079160712100c082024004000109079085521502c800c0c0c0282a0071000d00d0780c3e86c504d811903841c0980c1180b04494618901d00104041c502c0c05100b17844c03000803458130500084120400441d0324182c000c07803c07402d0000034000440c02c1d90740521103070b2003030085480d42e07210440c0112100340b5049004050100000c2e003042000080e903884429101103c44481401390920032280242c40503060240c40207070648400b01c10010f81e01004204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 936593291 1250 936592041 936592049
    0x12180510060e130f0b090604021801080d230a03140f073c0503040b012108090a0504140103120e060909090a05030c07033008130813 58
    0x112806040014610425145140b01e80281900c41e10001510501d100400d03d035580e00c60400081c0c0c2e0030450b603c0e103403c03100585140000e170340709400300411424501c5040559808c011480c1303010b580b40503061580c8001c2d42d2021403c1140300c2c903100b080f0400c240b01644105001a525984a8090a80041c020082a400e10103c4075110000c5060702d003092032230700d0261541c1c1c0d941c3c0c1411864100810307800603040c4840050340003106030480301c0c0743c501608007040070b61036601d16580c0d080c9428807044510041c0c100306010f820004442d00302ca8074401d9000001130340700185e20348610504c0001a445520b96101640080c20001c115460030650160b05059a02c10150216202010720b800c0f11240714044c0501c2d04100200070900c050314110b00100e900203100003c0350800d00313036507880c2c6045400c00c2188036100d6102d02414410400524502c3c599140b545502a0f00783c50301c210003956140c0d443e05100c081c0005080851000e12500c00c42106003a00241515520310b100804c8036040c180501ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 936594541 1250 936593291 936593293
    0xc120c0618033e0607081308031b0606092404140709180605011709030702040e010b01030c05030c0a0c082811030903060f1009050c04060f02210a121805 67
    0xc201c40340c83d800001614011901803c468102030340c940d14181c0c1948040203010000c1c1c101000004c03001c00c200014400356100c10554800d88010340e144a14014000d41414820220b42007045115031408042e1207040400c007510035004450800400c0c0180b40c4075919808602030107080286181d0480310900807100412103070901080700c00c25135011180c060203140c1c0080c04030140300030002907510286801850301003d0b02d180500c0d95000a00310b0791900c41800b0b15944496280441c1d6815110b40c2804030407074182245145854601910b191103120080824400d0b0300c0c8a001c14040d140044d1b0303160301d1500c0b915500d944502c2d004441784c1c058140d89480018425206080030440c0030055405104c4054000c0043d40c55164060800c00d03402006c008500c036140f00e000426283d9030203000d000c0c140c00701b0034036969820644020003aa802100007029540300080d113150322100001c100b0500c00c3c050381c205880e28a0b00ba0100d500c81e40c42c50701d8240c50303800c080e1002030301c9000310701e0800071502c150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 936595791 1250 936594541 936594623
    0x824150d05060709240804030e0d060b041107021507030c150f0605120a032d05032a18060d020705011b080c04060302072d0c120c061803 60
    0x94035003000e200d000f0080740b400051703807441c4582800358036803940051081c1044030134150400081001c1e078948c0301080c4c405503203800f26800c80b424180b10754500003035032240c002d240c070910f60042402100c50703c240c04454000001c1e200c06040c46401c240803031320350212002c0e81c0d680007854103130007901400304800303203240c0307041c10020381d510308007158a4840d20000003801408038961001e031102d84207001e406120040340c0d2118150101071000000c80c0200588070145c5074100380c00c090414002200e02e002030701300d640904802d0b5041c20815a00c6561303c7d5140e0300d107240c0c0940c0100c1c403d800b03288283d1011500200f041800c005043d0009200326210050750340034201d41d2082181e4503101621582068070b410041800880c0c401e8004182440c05440380c44100038080c040003001c01a00c1c0800660040300c68642c008001d501c00204004245000707603035404500700c1e100c5802e401400d124100a00004140c42c0f403840c80b992480c1d400030354104000c43c44032491041c0c100103251180d140203030850307415 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 936597041 1250 936595791 936595799
    0x150201020717030a15090e06090606150a030204030b01030c0329130309030b07080601120c050f0d0914010b0118030b1303110102031303090824150d05060709 69
    0x148251040250024400380b0309902440810200d640301801c8960b190303465a4007884000f00c4807040e0310090a04010005603a0784880c4c0041c00c010300580000d001e0740210060045a65600807981c0c1120007070303d03c1650f9800c2525080d40244120391000303040c04001c8000005205400c0d000c0e07022a8020441c24000c0021000308210962019203113000e80004140885c00d002c0c4041c6020144a01ca414045e440030785035103482500d084100c4000b400610901e04028095920542a00740c02c0d2007600240b008800401000d4103138020740328000d80903240820030900a19054004000d42c0e50030000c1504162004540c4502070201a4103041c0400c44009a00c223074100b44114000841e5042001129140c4440c551000c00c0030040340c050b4108139120300e01500f524070030b2004502584180b0351008400b8614500907012880c1c0d6031040e040c1d0b03042100702031100321111840980c0d54101c05040c5885999a90010f404002c040d00402d4100600329409d40030401d000a00a00440803a02e80c40f505582d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 936598291 1250 936597041 936597043
    0x3061502190602030901060b1c060e01030507030605190e07030c0b12130f1b18051603090201110d030204050a210303111b0d0f031b120f0203040c1502 66
    0x500142030031103101d482454408256a0340c095900700301c0d04400891000c7d03496040c140d00e5003084003a21400c0781d40c00c560307603580c5190f442000024030184814840540c03540d19020745502d11880040c00c12502c41002903c064031580300d20358940035844042288040b05420300e40d0720700413800300b01d03040e0a039480c0110760040303030308240c2e00480d0b4041d0003946943e0ba006c03805c600d0404200c0d02140d0350021076203000300007192041c40542c510414607546402a00e4948954a07137a440d03841851081e140c141070003020101c2c015403c04e003402e00d050110380a050761004840480d2044503442c042c0c001c181492000c0c2c1d07819002402200e800311400d00347c041e180c0700c541c42c110700725102d90040d41c484ca00380f020010340640c000d942003201d0345d400da9003000d440070080a080001e00b071440300250030020a56501d44c6d080140e240b241d00345481c08000d09158135400140790407800d4a81c60521a08000300101001540c00107032000500c0d00c004d6482e070406142151045081c1c2c0510241001440c01000c0d207548 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 936599541 1250 936598291 936598303
    0x2061b0d030b0a06032019030501050607020105091e130218030c0306072106060c031803020102060112170c03070c0b1201060e03010e060106020f0c1c06021b0d03061502 74
    0x44020f20412a851400c0016001403510900c048520b00c081d5000c0b81c11400030f107010308034110443c0e1015803807034030411008084490503041988104018405040940d030b00c0300591b02a541c054414050f102d10301d410740c0305242076503000b05a00184510074000340da44a9005406c01c208816540c0001d10003d1041588901c40ca40c5219010303401140041d001030322420f000c40390304d503980d05102441c01810203001c2c20f031102a04940041411910080c00309940020b05800070000101c0100c02070341145e0000303481d01c906124941f00b03602e140e0841d506101100300700035050880d00c146250b40b40004441591280c0010109481c44010000000380c032140042c1187c080c040d000e81101c103140e09080d41030780e040760b000b10000d8166503500340b4a90f0701e0004220683c003804854008000080f80000640d00d0180b120b034015000e6803d421107050148241440307101055801800980c8a85a00108550690301c04400311198807603000c011201c0d5070154004003c0c1c2d5441c064505c3e40d1264030b18241c1e6224 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 936600791 1250 936599541 936599561
    0x30301030f03051309020a030614190608060303131e0608090709230901060311040e060c070f0c14031204050607022b0b06040f0905060c0703030902061b0d03 69
    0x7440d0500380100107449040285400182d15040d583c5242e2a040d2203c102c3c1c20451000020942c0c41c042440741c00740030b0030740700d405100440b076503440303420000c004020320f05c514403804041c01131030804500181e0701841a244600da41000440b1401c2d0340780d1180072003e5100e208032540b412007040100c1c006116040044c81000703100000c011440c07070020444001e103081c000c54078600401440c8503204001303d1100f14011940705002040041c20750030314820b000c0b90240050f22542c81d00c040c10414010201d5096440360065004646900080c1009280d0810b201001010318504250200308090560054544c484080d070848000c0c0c0600744403008a4070480c020190b0240060001c10b0062502e0320b1280800700d000d910102c5240d015801c00324940500c49400c90302031641404001003400c0c240b24804d416000080d0a00c00850580c456507241c1c078002e4a1040c2c6600c0008030401850b0081c0c01c041c8031503902401e025513a000664031500010b801d4462014140a01000c410300340d031007402000520 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 936602041 1250 936600791 936600803
    0x9050109140102161103120a020d080108010c02070501180e07050304050c091e10170a0218070c0f210c03020114070f050c011d07080708010203042f090a1a010203030103 74
    0x201d101e13505d0b03a105203092034044590521441003e4071310300740d8800140c02c40c0c003080e0300140b40d882c4550102418001050b001451268506090035004942c0010610f045800a003001c00449560300c40b01507010499420020008a4031024026120307400001144128010000d903131002510340b0400c5001c000560756414a803070726140d841e600c10400d40b155900072000c034041c58040d40d60f8800c0500b01c070308485901041e581040010310254113120008000031002500c1005c4145802c06010703200e12120500079050070070000c40481081a05510b60000c58001c842c18041500c0c4600c00820a0450303100c110015424015003030b81c8001d101c0c0e03001340191001d8403012030001c409002103400d904440c01030080c540d01d0358152016441c220f158a684410504041e09449081c142072a01d4080941c0c03007500607070700c10020040401c1c0c0d0030402948030f0301c6102441c05408101040c01282c5508148401e41c424502018000c0708801ca50003020305000c204980313800c0d544820010798690009200103800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 936603291 1250 936602041 936602077
    0x5032e030809011e2a1a0c0c01020f0706060b03040b1902090a0807030b090f21190815030d1709070815010303080109110702040b1309050109140102 65
    0x203550401400441c02c040c90808a03d00300f04041802e0820701e130600201042146907424207200b20f00c401c070540309a1440c0361035041c40e2140e503071044112500040c40f1400201e900454a0314030003000300d07100d070442e030002036444070201c5080400701d600c4904110381851502c140025444405400c0e01e2045400907500300260b500c1d0600e82100c00700380c1007085410340e0708018490003541c03480c9500000d81003000080c610b26056240050542c0000382003490613a1040c04000e6060100140c1001000301c10001e55031a00f95010044100c0d0258000c03645020301084500302503140d00c0951a48070380d4021001c0039030814448145910340304032030349c130f400018902c803c0142d0032102c002400e50005291001c9804840d81d4605450410b080024030050b2240300000402c181030780182c4481c00342c80060740810071100c6920700e44000d44502c0100a000b40e45586a1500c555610b0304903600782002d0100c1400301c541b0f2440e100c0d00070400c00070102c41200c0c100c084c0c00c00c140d405100390389100140542d1101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 936604541 1250 936603291 936603293
    0x3031201360507110a0809030d17010b0d140906040219080a11130e0610050f0a0e040c050a1403060109141f180c08091606110a0c030305032e03 63
    0x101030040149240240900310b100b2807801c200c1005284c5c03a15004030380c015142e800382020541040e0240766050104030001e9000e1a002c00040e040300d04607090000242d41d500301404500016040b00c500c0d120740d04800c43d04014140c40080b032000c0c89984201d400300380b07000034440390b44100760860180500a5000c180c0490024100074100d03040840b000308400a9104070700c0610090b40e105030074042054001c2c000340903003850500103203000b400d800c0b0b803040381014411021454040b01841507500000c12a40403800740004041081c010380405000f0b180100c2d21000029480301c25621128060300c01c08000003610042c51042121845504e030020546484514010018185008500070143c0c05a040040c810000400b50411896100b01c08101c41c58440005040d11400801412154028180000400f0340e584002c400382c0317a0702d0511480681e10611400d107403459101c002404c9005502001c0149504900a5845040564904201e0009400505048000c00d030600000050707140e60504c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 936605791 1250 936604541 936604649
    0x111e01080a15050d0809031902090f16050a0c051b1002150c1c05070c02090c03251803060501080106080a170d090609061d0c0603060907020c03031201 66
    0x21308140a80c6015040020300ca000904281c00208000c80030328000c0200c3c0c0850520569803076010100021a042d2450400700900c10015518075040401c00f000400c004514082c040c0c103950b01e500442102c6035a0004088001640440d001c07881c031034521409011545480007900c182010640c03060803115445a01840720160010700c602038418001c1510511420964810148034800981c0c40c0500a582401405000d10014140c190051001c108109003100b079a016030a19020340b51240304100903107542101c413640808955078a02e0400c50380001888055040700d41038035802d0008005666a40c183c15503a1125820014400201140a480990300581c00b403d002d4202c0440420000e40715941c1004039543e511040792640e580f02c0300210024100a035a0341194112402041c1d04a281c03400101c4a01004110a10400b00c20000407817851081c000c00b400301c0b00250440340c99459031122274030244024081c501c00710041d1162491608045d209030318021242c1e4440d0300065194041034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 936607041 1250 936605791 936605809
    0x10c0206090a180504120504080c090a060503030711040e010c0206010b130f2304050105060f07080c06090a110319061a03030a091e030507050d111e01080a1505 70
    0x2039644290032641c00a00b500e0312590f12281d8a40101c03000070546060f1074002c00b600782c21000002041000c1c0018012400001600e98146004030348051300e95440840c00400b408440e0403139038150001040c0c2074204203043c5d59a0a00090440c1c040c0404544140c00074200c0b10307100d50070801070380000e0040040041502c01411803102c10030840f102c40f40c036892040804025030744404554524448215400320681c02d43e0758070030f40c0480c0c090045525040000d0024066903c1781d40cdd54110004290081010a10403900760b5003210055500e1807401500c80b9441c1c20090205443c9420b58640c103c0151030085030f40c0803500440d02c0545000315503500d41e540200030282d510709403240e016100c46041c3d60304002070300c0700120391b962f041841410190714100081e0702c0441d075400402021030a10014201003a98000d840b400d0b642d031501c0c00894102958582810022180c00501c0742191808441d9003801c1c50214900c20b8807001c00d1910386000200c00c840a0001007000e40d03540403c1440700d4a0407640b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 936608291 1250 936607041 936607057
    0x12060614150c0f1c080a0c080c0906070606031a0705030702060a180f2001020313090e030d09080304020a080a0506010e1008010203010b04050a050d0f2d05010f1a010c0206 75
    0x1207407800f0740380e0b010b22464012100400800d00e41c0d8016002c04881e440380300c03a6444049544140034500010764041e08d1240c014180c8401190040349d204071035207c20081d5050a40c0107441884555980c2c03c000d000740380422425030306038420b6400100e41500134812203000300151b40c01032142d07a80f41c400c0040101035040b217040f00e981c074031070582001c41c02c15078203c00700314010700d19801c601c1100034604102c40c0c00b1440f403905542007440003486440030120903070201c4051510110784481142212401c0d482007402108806240500c0c400070701c007510010711310440c8291182ea07207454480507200c0e640c0324401c50050541c2c3c05480140300140c011012140c200071011501000b0369110350103103007681c20903009003c14600205003003045107449a8140018041640c002484441540703c603100009000c0d00500325800c4008000040000c10883c05034510745130b052042d800c881450100d010b04603080c3c0d001c0318682010400e404e014803d24000d101c40405031110600d0b05980da007440b4094200e131702c1e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 936609541 1250 936608291 936608293
    0x80115031a040f0203031b060106032c0c0604060c06050105062701090503030a020c090105060906070803070203040b070b0603010c1e030515042a050307120506030a0c12060614150c 79
    0x10b0f1580141c4081000d030510b0642c1003405078580300120142031a24005900c21003c00d8100100c2e88051070141607403090140d1505201d68413401145015032821480b1929603802060000d80002d506500140e820a00c52040c0000e1000366030b01c4003000310901031007840e000504001c2c80d9209075142c003010751140b0410103040654105903100300090458108285c15400343c0c0269813501c605140c2034405a02500c02120054140011000401c83c10f00070715000038034903034001000c144600e0007041903070b0040603603200041c0e0b15501403a125961820646103180250f0810300000c8010b070180d0b071407001c0b4a01e003924002800c03400d480308901070b01001d448641d58006400055409803214040d0044202020131400d442140400c5038500311800760031103908101e020b10500858503070041038084407802140020032180c689000203414084815001801100c20040000ea03006182c1d01e510318103402900c08002c1180d552141118140c81c940c400d0390310020241901013412b0090000e010301142c000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 936610791 1250 936609541 936609563
    0xd020a0506040b281e02070302090103030c03180b19090b030f1923090c0a060216050f0f013506040c020c0121020c060c04080115031a04 60
    0x12031070340d0348582c019060342c042c0042c160701009aa20003219003c80c0455295440e03040600d0000c20380002e40700c1807004000c251070401c61103842005404090b40e001000340d841540d40e45405055103885040841c0171880310344030b0030b134104518101181110b0202090034641038820b49802820074910700a030702070180701a00032a079165160040d612805180040b070b078550030640c41100081680300d041040440c14a035003642c00c80c0c0c9400705c03045088450001c100c2282c4400c0c031168100503044140d2900300b41030460010360158001096403200d541503154016254803401840680054504a65000304007405640801d51250030786400050b074103840b02603080708020301c0e003406403032136122a81c1c1c81184800380200c1d843d040c450380d4942c407980e000402c441101800040e01c4403e40b03134110032041c01c1d040414420901e15404441d494408c001c10307030304546080d0204000c4ca810074007440348190710300b640c1404007001400501054a4102c3c0c9850b0682c4201e584060600303000900490b500038600d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 936612041 1250 936610791 936610799
    0x21f0c03210504050703030212030411060d060518180d0206010b03060a031a0402010305060105120403030b030c0a0303020106180608100c350a18020603130b190f0b0f0d020a 76
    0x94402c4500452040e406040040e00d0360034008e00d40300b5510b20020b208081007051000082070742c2d1000e03c400c2c2c17081c0c44d0785448400c0c00090500a2505600c40e980005070303030311081041e5a589003028481c00d144443c00c682c045031018007503503c1c1c40302482900907a2240c00140302950b08600559881200103060b4802d458a0b540c174070380c4c0c20400041c030740342c07928507039013404119a05401080d034402d001386009400c000100b1110100d801c0050009001c2c1903a4850240c940e840a00429100346405049c450856541e40fa0090003440e0318400c2c2940704044c042d901c604446c85009440031100d680f0000c0a49481d40e02c1040300402010700a5014040c0e5a05540000c3c45c501c5105c3ca40c1ca034481802820201d08650005150310008150202261426500103000d043c0110b0440100d60143c030b80da03460341e459100c2c01841c1644800090f000c3d50b880010010041b0074003c840b04640007007801800010300b00b801e030300c056540e01303155140d00121000c3c80d25880e003008048004850b000038031114030142d072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 936613291 1250 936612041 936612107
    0x1b050a020a12050d0f2a140714090405070303270f0806100503060a1508160819050c0108090a12031505030309131d01020d0504021f0c03 60
    0x115407168081c2c0786100050030a00c8020701414407581407030309240240e00e054900040090640c840e200000b078403d20034090148244500c00c07003001d0360140d00301c0c580c03200e01c4403215030315001803040f0345050066041121480c10814030031030065078800d004281090a65809440c201090b213100302c0c0c2050109207000c041001c03802c0d844000c040c207484104181c1d040c6000107040c4a0300074800490b40303019050400c41d60f0ac0000308581c1c0000380540008443e6521041c05010703920b641d00c100201d00c036901c603c0f450101681d10210031204100d0441d13a49200082200e0350035000040b0103085a001b20915880035402008a2a403083c040c0302500d40d074000e16038900144640b03001d40a00040d070744a035903031103204184a201014000440080d41400101c0300000e515000700401e001c0119102c07e082d8803800c0c05070480c1280319070540004d41d02c480c52417240340000e090403181a8400c01d0410000c040c12aa80248582c0e401c505559815018855032030645890f4008881d000c900c800c982c00000707035010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 936614541 1250 936613291 936613309
    0xb0a0909030c1a0f0c070f03050306030106050d080901021905030304081b0f0109050d020109051009020f06030108010222212d05152710020d140a0b011b050a02 70
    0x207000c0c0a103103c1814500188191900300030b03c0301c2800d2404115290101d142d105140491550600d8900c0c1d07280d0301c01d000300c2c1c003500103075200d03581003641e007040a030810034020060080c0c40d4080c0d084a1201ea214416801c0f0180c0b01280904550400c00c00705d03004c81d1030031006280a800d800000811001d01443c036902d000318104105040d655514501d90810800344010604000c00744000d101d0407070f00c1d450b180c1e154520010705440c40c584d141005011912450b90060940c0c10040c481d0b0789a40e0742d200024040c2d844000d0940075152040124450100b640050138142c44111080c402c510505a4040029000c1854140d400407000000d40340c9804680034a41303155105100400c9038080d16160440c80c01e44880020000320043e04100700424188210b8000c0394408180480c000140c00000c2504100e160031000200d10f00000d841000d21345584c10400840e161103640780c00e00c0c1da030480490101d400d290700260001d000f840f0203d1080802c00415a4401d0241e001d48146e0034030365002550040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 936615791 1250 936614541 936614573
    0xa0e210a09170f06010806221a0403080702070b04030804060f1e0507050f0607081b1c1d0c0603060103020f04090c0309120306141002160b13090b0a0909030c 69
    0xc3d0001c0b15860200320b080c000035005140c036500030022414011022600c4209495a0384003820510240806101e1000c0e403030544d1081c8452207180c2402d090030020001d141c111030060143c424904009820320004086604503508007035128102410504122210a8042440d404001441032404480007a000c400c0c0800c055949449503103400c40c1c035045042c031000d4046c0f40b449401c040d04118246402c5146140e00c43c61201e0300c2103200b107010894141c0350040482d00e00c541c2c007004880100201d030a61040140031891102c0e03a0380f580302e03d1002c0f48e983c0840c02d10310750001010f101183c030550181d005440f910302101c501a0034961210030140840364921100f2000075281d61507042404001d10355404041624a024030055003001107400c40d140d00911031901604180c43c04990079031083c08110098617501c3d00c0380c07014070381d101d0030341f03000c1c0d0000300c09400a03060410000410b44040c2c03064400004000d08690304c0645807400980061640c00701c254203201002211800158050302482145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 936617041 1250 936615791 936615793
    0x53d05010513060b0405040b060c03190e040213060e030106030812070e030a050a08070303060302030d0c030f1812050a0b040b010315090b061908030406080a0e210a0917 74
    0x958900360400c140a00044081d1145500d007880a000941c15541110251502a500841e0a10010010450b544035021031100b05000c0440c1d22440985070343c55070410f94442da0750308034140594004000403881041c03504c10b402d03040e022080214a014600111a140340180006071803590b175240e4054541c008010061841000d030b0410030515040902040448002d0300141800c5981381e03145075840001103000f80900d117001c909081007500c241c0000b0301070340d80030701a6039170401d20003030203080003081c9a000c8011803500101c4c0c8103010311a501945460110444000d02c4c140b0b42100b41074130345070b1260305a03518081c528840700418001606c00b8002e031300c04e048141e002e61443c20142600008032039032108d5241043d04060200d44d01119042d0807040480d006100703090340025a4408000b0b6500c610042c0c00041000a207140d0002001d03885940000c0d014001d0107010030344240c441440121034007204401801d41c1c040140190087c1450401328100240000e841d040140516120b850480d501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 936618291 1250 936617041 936617051
    0x151d010210060815330f0d0303090218060d02090901020c010c05030718050d0201052208010c030506040603021c080904050a0603060c0320070305040509070905011407053d 75
    0xb1007107103800c8962240c005c04031781061180b0003d02644018805103611418111001c01c0109a56400f040785580381c802020710041c6071040c600074024180740c40c0103910442407924a8802c45404106540c840d041c02469121198a1582085030b03134640a40003003520740d800d101d01c25201000348606085403005444244d101d1400702170040c4401d1342d40000802600b54504100702503140d030300308059a0703942400d003e5100e007000482e12144d00f48440c2c94000384c00380f02c1000122290b065120340c1030a80030781e4042c0900c1c0d8552092100303a404502c4002c5d00100c8018082c580b9030302c5442c4c034140c428400d03240d0510340100c840000303042c0c600a84403080669a00c85040081040714468111001036600382031042e002e2050178001e10000050508103150400260f034000c1511410882c0c000d407000070f04410040c14460710040c03100d1400d008040c0864821582d10405503c0d03c400d85180c654000014032540d0314a00c44035420701240228196500140d15880c0303051600354012003815100c0c01c100240c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 936619541 1250 936618291 936618313
    0x30106090b0910081203071701030c170a020a0303050901050c07180f141b0403050123010e04050307081b060a2007021302030c121302010207151d0102100608 69
    0x21082c0203061403180c000c101008001d00500451103030055412416041d4803607881d210700b65031852080011400303402a480022040150404c004803c0c0c1d141c42c050b06400281c10340d202981c45e100c089010350f1140d11184200002480380000300f070350b100c041c50510b05007001d0300d01142c60500e03140c000800c080320300c00022031006110300c25003600d014030a40c1401056004000342c4103003003014080128030051a46000d80c00522441194015540140204800080c0c00409032500c29400000d035950410000005841c9030f010445901945d00a40514a0300c0400e17501c0c0e08851740041840d1607040c2001100786040502401181c3c0310304c0329220003107a00c25071640c046400c007040030b6001800010500c084000b5840f210107401580c2d504010040c1c2d079880d514000d0100d4003510480d041d440680031700b0031443d80420303414054101e200381c00b1900d00c15111414003541c2c0c1103004c0007a000031210704d034510301e81c9011105001c4102044c0107440241b4606aa00020350b56203801c0440180c0c020307841c8903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 936620791 1250 936619541 936619549
    0x2a210b0d0507210b19020f0d020d110309061305070b03070305090d080c09010c1e0804060807031103040f06060e07020a02030c0906010203070b1005130605030d031e0911030106090b 79
    0x246400000d0715490084041c60313960340000d800301504048021155041040c0c1c401102c1e4119003030314109140d500d07211840f00d0392481c00f035404100c0945041b4203101d107140e00c182e490020b89000d00310103400381001303a685119803403034044201c2060b221407041402c001a60000400158059a00c955001c140e0713240002035649400c42d1603401000f0085280d0400072001c00c03480648032803c0003480c00382c0780c5030890700300b0358021a0103651414440c40050f112408109030803005004032009502c0705086a40c80c1c40080e0200e80c0c030003201c08100142080020002009420024242c503c9803400058064440e1081000c01104071507420140e400720b001c1c0c50035450100032040c4c03034500480b01e107142c601d03140c1d000039202c0c001c0c0307030b00109001b101d200400c0ca0721000c42c85060240801a1100c81d00c00150140340c1e000e080305100d198002d018903c0850f118520900408020b12240e01d208a10384690a03c42c1000340780c070380350688604002000100d9541d400703014550040c88a0100402e550760090100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 936622041 1250 936620791 936620819
    0x418020f03131e11012001150e1f0302040e01150e010503071a0a08040c0b1c1407020d2a060e151e06010c02132a210b0d0507 55
    0x804094224019141c00080801903044030405080c07821020841510f0001b4084540c0c42c403c0baa1254200000f6170070501c1010802812141701e0f00c0809a140c50325101c400c03280805003808907445207034180c14405420560081e809140d180400083c1c4459001c400b0705204c1c0c1903400c50040d0000c0342004015a00d410002c1c10068010b0050192000b900103190020900ca01c040707400600003c07600103000d110307100040c00c00420078180c807299100040342061540e01d003020315110308a40b0b00700392060341440e2003443c41c0c40f8402c1ca80080c501a601d1036800e4601030039442d5a01030b00c10301e120400451000d00d09001e0081707441094081a8804000307076070f81c102102403c0c56960380e41c0000820826400c4201c2078030b440d141c0c400b2180155240d40d8012110401450006034002006068000604049a110210000c1079446042d80200306c80d030450300c48011030a44070009159030402d4940b941d01d215061815200401002800081e20004039041520854080c1c41035001100c0030008410130804c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 936623291 1250 936622041 936622073
    0x90512030c07140a0f03061e0506060901210f0207050d02031309050601230304140d21020405270703051909020d0c090c0e090c0418020f0313 62
    0x1941c181900c1d1003a440d40c500d09440b440c00d601c1c4181424200b5500c8a04119029118482074420203640364101500030f800c170400382c0e4807210503980481d01c80c6503580c03040c41d006400c0100001d150944110044459804e2118480740341044048800080c401902c14045d132003d100b6405601c0d0a0b00341400c0d41042c0b5940c0920056410401c03400442c00c0c884544c10f8292042e00b04000303501d8a654004036140349001c6034603000300c00309202c2010007410300c034051441284100051055500e03c50007513902c50154040702d4020441c0704810031100a81014503244c01042c2240c0181040e680340b0002d03015025003180c041da901c0b50f6a00b926651802c8801c42e9901c084103040c00d02c60303401d20251940058011405504400d0380d120481d50456a81c1c6403500207860300801e9004c44075484485d03410007088544072074008100191010741090030310030b080500c540340c6410000c3c2800c1c50950107188c100c01c1c1000140445500b0885440000007002c0558002c80b0440b94110341d100722450030340301700756880d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 936624541 1250 936623291 936623293
    0x702210a05031f030c060905040b0109150f03200a090b07080d020c0a0c17150609040f0807080c030a0801050102150a0c170420100c080703110607090512 67
    0x1903a110340c00100312504840000e0603d01e5901c4108a503090452083d040100315450400c00010029488005c40007620300c115001c1048040c1d260044d03d0701c0105200310311300344176580c00b00c0e40e15602400f0500394402403424046040021050800c00c01d1429071000020507501096601c00c0c66805030f01803000d800c1c524192441e01340182c982403424050003103a8446150001455450450705000b164951036021203080c01e02520741402100030301d80c600c0703a400184548507400d80641412003806005010150100d03d040d02c0326100c0342d640d0702114a00341da8400040181d0f500080350b00001305041100c410103184c886c070745004014a10752040c0d0120381150312038003980c4005100108260313003213845c2c10000140750300c900c001a581e0710000d40000007455001d50810050003045c0e074202c4007900c0b00340c003034207071600c0284200900501c1e00c45100c0c0c009405480c441c3c00042382140100314040c040c1c01d2080701203c4020300c481ca8240f0850300200010742641d010001414040f03400c804181c4500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 936625791 1250 936624541 936624547
    0x1505090a03020309060d1b020c01030e010b0619020f190302192301200c0d03090507180216061d0609030f180612070e06180f18070221 59
    0x78030029524020036a00920584000030342c18542c100960104041c95040c8000e9140140d0108020391a5001005690b000c05c1c10181141c1104030180f04020b224a0014140d50800c0101c10804002d01003c94188055206041105215010400c0011802c00048920748180041e80c0b038020704200002c02c003c0340281a01800000003181e1000b9114140d02100229080d101c0b1000414090803482590100e60108800120000c009880c010305034407040341c04849601c2070f122406c404a6000c1328025000b030300003082c188034040c0701d0f5103c5040725a09410240c146414201205d00d0615000740484e60070340c0d0f403195440c0302140344d1001d0f150322001c84082c0007280341142d1400c2e16032003141c01462000c4070029101c0c400288508512400690103058140c94403c01104404109801d441c0c0c100440c40c4004203248138945201150500c04898800e4009035111034280044680c0280c0c001c1e500c01c4100006004203030102103a14070035182a03006142141000e030500790072001c034040c04000d1010030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 936627041 1250 936625791 936625793
    0x10e2107080c120403110301020906070f061e0608061f06050d020706060b07051903020c0114131d09030a0e040902041b051c050f0103020609120d03020a03061d041103030d091505090a 80
    0x180040e233000c1600700c941c40c0e01c43c050610740b800091002c1403103071000c08000084e126048505074809000d5584400481e041601c42d5004000000e82c4d000541030300c030104181c00c0c061203104401411aa10700c1403000f40c141821030340d800e425620380d40c0140c100c500012030001e080c48820807010b41548101b4419403055903041c2c4000f510748441d80b5000e07042c40f0a107400060000d4101045900b400c11032481200400e03258101d90110030b001c0018200c800c441680490149100842114540015500c0f00d81456010300d0030300001e8216020140c2c1e1203540c9600c0392152914031840e5520441f0240c0d10140c3c7c8000907030942d4018421880c80303424603803030a420402c072142c002e1381883c1901c0d012180c1c1900c4c6c241001c0001c82120ba12a00b1411500401882403100c0341c25401070b007101c042e162801c2c400203032030304400d42030b500b46280c1080c2180036010100d4081000651101c0b0780c3e40001d01a2850080540e050209441118104541010062003442d017010032a200312900b10321954090a140d10b01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 936628291 1250 936627041 936627049
    0x4080a11190e100306020d020c070506030c25050a150c030605031216020303120726071d04141b0a02060403030b011e08040203010e2107080c1204031103010209 70
    0x401d02440985200302d801251100d054001040c000350b90062066640380e84281380c40c0f0103504a142d544044d8410004003080c06d151003020b030703807044410b120b800d81800b41419500189582000007880012440c90a050105400784444041b203030088854040001c03040b0181002c07599201011410035250510500071594085001030000271101082c07030300d6400589005103580d8800000075410711001801540e28100c02c0e034114422085511080c61a10f400000a01da5008420040c401d00720711344001003880d4082e2902c008400f005804401104410b1400708084650030a454081c2a46100402142022190020170003000c01c0d0102d6090403144800a0b6540c0e0700500010141900c1c0c1070300100a0740300340080c0d010b0303c10050a0420b21115410042d04207401501e0580c041d5003010880341301a100090b695080b050114108800c4250008113506150030200040361920b000300110028040e0800c540106410500902551580355203854200c076500c08601d240640d00500c54201c0700e40d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 936629541 1250 936628291 936628339
    0xa080702011e0b2b03080f040f290c04080c0a0e0601050a1803030c140106053f0609150105010c030e120f0102210c070f0c0b04080a11 59
    0x600780030945100b07000001c0c1007120608540c00c1e44680400c0301054034100f80c200051064000d0325080341b0350300d55041d4040d2140048901820b0100c0c82c10300900011500150101c0c040f4480d0110840b502c000d0074074107003d08042d285844081030110b02032020800511500b0b601107411900407001501d0321040e030310786c1e940080442e41400408606503e80e140580408203036142e503500108031494881c0b0300a09040d140c41019110000c1d4041c0306401c4001c140b00300c00c1030306c0000700341c0c407a0781d0100d10600c03201501101e0401c440d1203135242c000d20122900e040051240a440024000a10382401d120f4900900001e00c4550b41c0411001040783c0e9030040b000404403601841c20260010a40000c5801580c0c007880305030f840c4c0310b11300c130b07411000c0b0041d8041c2c22a00300ba100403e140301c500144000203414141c1c2c040004c2002081580300044640348003490a41c49807080846c21030352034a81d00c1554000c1c1d80010741580100d501c520401135101410f199100048514640407001b00e800d03061403007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 936630791 1250 936629541 936629591
    0xd020a0b07031d01020f27240714010c1103070b07080c041508040c0b070c05041d070f06140a0206131401020403030e0901150f050d200a08070201 64
    0x1541c0e408126854955442c9800d0b54149128000c5d561000349900061060340081d5402140403030f00829407480d0048020800768921004010a42101c038030324804003c3d50b1241c5558208000800c00b00d0001100d402004e0030490703010000150f40303601680c010704455021741904400e07400401c8010001010350782550342040580c03804054075a902408078070284280e400246d03140b08424001c40c03030745078800c0c40307144038a10800d22100c0c0c145d07032041c48541034080c0700b0004201c1c0c038909006101c0750a0560000411100442111000e20501c25110b82000780f40d030402950192280000c0c05000d070002c1003680082c5e18900401d15044041c54000e481e0000a045d880076034038601d984c40203002d00b0b079100c160081d94020003195940d40d02d15024002d5085291035038013031800800000b03040760640c02d0320108a41146c4070940034406003002221030351f01c800c2060086540d198112a0780c0c508090555503112400c002c0180d84030340103080a007101000516030b504582c10013103a01c80d0b4510107512840a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 936632041 1250 936630791 936630797
    0x5030402030712150504050c0a051507020402030402040b04020c0304210c0b0a02011103011502100b062505120901080603070501020304061d0402030a140c09091302010e0d030806030d020a0b07 84
    0x1180040c504580b604104c241e469041c1d5040c603003031101b4014040742080800c0c0c0120f0314556040d0b502e0081c400d03082e2880741c0c4000a0309082c44170801608240e00250303840b0b44010000203a0802c20400a81203800003450002c00d5440400e051240901991070207041e807001814a642c00700d4030346c0d82d501281c1703c42d0160744000c2c94081407520031103000350030101c2901c0d5210415a00e82d0703110200d500f1a40720210760b00005106294400381200300610031140c0e002c401030405c81c9007415505e01c01114122071002e400f000e1201c0304100c40890024008060785560030030b03515071755803a44800108803503405440700340300f07030020072080210303a800104403000c44649081807503011101d0350700c161514100140c5a5017280c0000100104801943e001038100c4107050100c00981c2c0340d030301400025000e07518840740c1180d281c00c04695002c0041c8081001c882c414580884035021050100d84126100c410440119103000c090242c0e03858140140c0718906042e1008186a50701925601541c1760003030545014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 936633291 1250 936632041 936632069
    0x60a0f15030e0c040617070f0e062106010b07020f0402091305090a14070806091501091d01090f0506010512100b01020a0c08061b181306051801080d050304020307 71
    0x1011106000119448200400800c0640e64440500c0c0d46e00903000340c40d00d224020400082200b0010340b6880040e244006011000c0b03a4905d0144102001e40128a0800e25200400040603440c100142800382441800058890a640c8184903280c120500c05a11031801405401042d4a400f4201e03060a10f81c00360224094665520803410b207030f17a880001e00304400584401000d600001151012030340c41c141240c64075900c0d51062a11048840601c09010080c0801004644004d801c0540038800d071500c590380942200c070700a402c5410210341182e4000c80f4050a000b400003d02c40c02c0d0040c8002c2c1c8070070800d4403100301030684034034440224910f0181c0d00c10f400440d070b9200f0800c10b05002d038041040007005884d41c1d0a213070349003c2211104c040c1402100c00d0048001680107032100000c00080c001d0212407040100404d010025451090b443e5990740d00251503913a94034900010362018500031403e5040407410341c1050000e003c108280708040085c4001604c0010f2444102d488142034080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 936634541 1250 936633291 936633311
    0x2d09050f0906130b1e030606030102040f0605030a0f06080d0905060f0d0e070e070c1415190e010516031401030305090d2406210c06111e06060a0f1503 66
    0x81613024241078110071400d804e0a0f1007031514084c080c4080040341203c0070b940d40c076001c040c242c0c407890040c0307001095041020400c1c54041c1d0003654000721300c0316004c5264508615242d0854005078081c0300307941e0040010710344058210724858040c0005581c1c16140103c0708000c05c171544501d10441182c0c640d90044250311358020310100c8040c03c0548003c0b4403034208001d000f4018080c0e04410b03515244400030740920114002446c9041000590f4019400e586a4010801010907500440c01c20ba807110b0030800d05490a114035032090150055000c284404101c0c0101220001a6058114010703100180f020a40180640307944a01c200c450594003299032a1441903c50701140e110034940c1c0d500c184c809001d07020b03007150301501da50307130040050300c00c24065040d642e0010410140041400c1c1d00140032007032041082c900c2c01c0c0015412a400c2031205c0c1041491042040d0072000301d50007000078403402e403901d5203407030004040c2e54190307404090504c2c030059180c2c1030b404100014135542d178060803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 936635791 1250 936634541 936634579
    0x1609030b16180e060909060106080105010c1109010308190201150308070f1a06040e03032503110c03040e340c0206190323060f012d09050f0906 63
    0x100040b80c8410444112543e00c50300410701e080c0c1900c0951203920b10500042d908400058403604a43d119036500507264a00401928200940207041c1c81031b01c0d405400c0744e0740d03031508040c1a000b0744c802e0340c1e450b58580804d240d00507420344140c440e10859041190607252110041000c0040e030350011a03059540c3c1c0705251158005055101c0108900741c50890340343d1307034840620315510981d02554180300c42c03054171f91282d071a44000c880f17690f105041c2c18034003648000004125010740708030f42000900481b40600045054100c3d140750120b0360b1000601307000f01c0e0f00d000704850300240100c0320203540c01c3c0e0b40700c55600200034240700d0000c040a104242e5412034030171103070320040d1070f0054511942d520341c0ba8003101e0201801418070000c24200b01c0c9000780380c00c60001f6490488c41000d4003403010348561003004044840c007007405042000c03a08500382992091000c40554066203c0300165558a80e88050404205503000300d1080301048000481034644070080396021604507200c014a280305c046403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 936637041 1250 936635791 936635807
    0x4231801020714100b040b010f11030f1b0d020609060109050903040e040f05011b090b130b0309060403020705180c0a02010917070c090e0a1203140f1609030b16 70
    0x2420f4280200380000340100d01080000e03c0302004182032010460760820300003910381b280e00a5000032412a0344c449036a1280940864000282081d01c2c075100ca803401141c0c1c142c22854442000c07260301000744a04040c01c10103441505054005030901d403900d055495110b500501c9010110760b19000020038640d0240100c034081e14003a010300c81241454100080c0b643c0688408a4641d0f00e406030081180401509241c0b41480356541c0c1c6543c07505013001d40d06250402290303683c80400301c000c08545881a08046c6204152900091a41d07140600b4003e02c0c20026600c01c81c0241c052070150900581112021075001101e584a6035403204231034004c900500c01c01d94090501d415801100300c0c59004940100a41d0b40200d00804c080c03519141c4034811182c01048021180d800301c1981c000107075080080301c90404003814000380380c00c500c1090020103041150601141041301b010000c0103219825210015a40ca10744920301e181141d8031081110000741c007810f20148211030044030f1034850120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 936638291 1250 936637041 936637043
    0x110d0609271b0609170606090105010e03070b070f0b01090905060a1d0609010219090b1b120d0603060c080405060604181a161e0311190e042318010207 66
    0x5000b0b0402c0d07540307000504082c1240140c0300c9100c0c0195186026480025905000b080010701180469117001e0040d1128021121415054040d00b03c00181403908007000d040d0141c01403070f00f0512017031185854861000c058020b64000741ca4400080080340317000840c0d981c0302c1814400012011a1034540803030100d661488850715100301804c1140300385040d0058446250b101d602c0c1401520310904c00d8540a149001e000e082400074891a400090449940080c08a0010a69550403860200b03001107600c404803002200e600e4020400070041e15105219a5038030501d480e0f911400c041c1d0f2803e0f100c0c03101a01943c45691111420041001c0310320700d221001e0742c0036030484642000c5035120b84801340c0c200c0c0d8040e5103010041c102c0315071600541000015204428002c000000c0d020310a50060116011010503031605100c86040380400d441880c00c05241a03c0d00c4800195180030801036644001c25240d11500582049040090541c102500034a01005101d403000d01069428020302401c0c0c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 936639541 1250 936638291 936638333
    0x9040e010c110105100b07080307051306030213150804020d020a0815090708030304020a03080f071a09011d070501120b041b020f03180409060b0301110d060927 70
    0x2003000303401c82e01c0d100c40782c40c1c004001d0107150381d13103242058600e0452081401c2c0701d408000c0e400008880100950b0b01252500b046418810101d0030210b40e03c202d504441d01081d40000d500c4010f1582448090040c00318503190802a1401721009044260150001303006201d442c248000715560902d41d4000b42c2070315011034603050312a20f06007003016015943c2c3c035810301409502289014010044030311681c7c010344509800c03895130383c2c0e9042c20362081c5040c1f80044028050180041c5989d5a8510115400902c00020f41032408009003145c0c42d43c2040b031450381011050b0400b4840110f040340413104242804066507410207043c0000e40b80304c403601c0e903000c0e191000311101c850001c02c88142e1094564215440c0c158154582552840342e1030409184610702d910700d440e10b1501d900b180106c144201c1e0082104501c1101003800d4401e4440078030200303100410404071148803403003030000074210950b0a00c44c40c00c142a0644c0c500006440312201904004464402c3c4019400c5c0846003942d210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 936640791 1250 936639541 936639551
    0x5090f0f1309142404110d0602210613020a0221030403120509060103110d060c08010515130b0708040e010e0105152704060b040b0c0c090103050a02010509040e01 71
    0x80100c005111540080f0b0b44016043c0d400d01040314002040f99103070304a00d0341d81900d489904c410f400d101400820860340d140c05640643c506898600c50700d243c0364480c0c407016846481e080c000c0315641c079047d0b1558044440c02e2040000c241c0c0e5012240c00030003140e09006955000c0f0900481c2485070008108484141020381a9101d035000802540309501030369802c860300c81c040d012607098030000d5900300015401000140042111005065861b90000703003a00c0c01d9084980c0c4190640fa0012050340106800740300402617402c0408040144115903007005240c050b0800318218400c08a025183e0401ca000c20108100a01c001c2201c02415410551102c40e42c2d5610b103640d0034240900034540038580300310003142c02c540003070305417800f013000c0d4925044920a0f4420052380101c4401035641c3c410748504001442c090408002d0010b00b40d071200541d518502e15082515040c3e03000481e5020b540e40000410204c2c5000c52400192542480d104d0b6540b00c4060006014201c00f00d000710140d4a41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 936642041 1250 936640791 936640819
    0x50c0c030a0812011a18130c0c03030c020313031403090607061b0804020f090702031b0a0b0105090115030e01020403080406030507030b04020c0c0d0206160b0f090d05090f0f 76
    0xb40090802c20084019100c000da8944004100d403800c0040c00820440d000e000040c880e680142d80000103200183c821885c2080c00c8070105c0c2956001c81006001c0307000700c0002001d15600d03001e4030760300c1195030004500d000d568400c100c00c0503c1610014100b008141400004420140111400420010728803500c42c2e080c0d0420743d0060022091800a80c502180084092402444000e210b240c0007800305c11013400d0041031201c0703100000c25050071408104000c1072100d80b180380c14040c56000100800384543c80e880c08038034810b41078000520402401c001004640d050340442464113030545030125021417550303082c0d03019001ba034100030304140c000314002c40c00a6050380b05500c00d21041d5010b02080035007106010480c0329084074041c10703810040d82c05407207082038640c051281d8806400545003100300708881540300f500d180304659070004103040c482030a6480c4905500000c401d4040d00e10003582d844d029100d03101d13482040340200310300c0b1207403842c0c1e40c0c8101003248109030192117500c2044030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 936643291 1250 936642041 936642053
    0x6180f12081003020a0605090a09021b12070c120c151242050402030414160f14060706060e060a0b030129190518030105090a03050c0c030a 61
    0x81410400001c0e1451000079003181e00441030008a90b00500558010b9042420403150b81c0c2c0314506058200320404d07000160501288000c200c0000b8803140c18100944003104603080c41040b0107800941c510910001d408901100590030448040181845410305039141c040314401031035221100401200426051081d04030402440315038201c07001f00803d0340e240c0d1044034600b0381d82e0007064003043c40000406500c0c001418a401445140040c80700c082c2d80c4000080999000721411036592105101d8280044000c00c14200304007d0010700e06200b07410a141000410030510440410b04a6181007a88544070304003114851500f142d4140030f00f175107070600112505425246140202e09280c0c000a061100030140c0b416030701c1c0300c070b9108009484101d5002c001210364000d054914010860920f2042d07660483c00c040101a071a00c40e11400040d40c0c032100c1e070341041005802a414101048440743c07002ca01c034040c2e107900d400c0107030300c0d006200310b0145031800507103d0540501c1844001414405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 936644541 1250 936643291 936643313
    0x21010f02030709060503040f1101090f03060207020406050a12080702041103130203060c040b04051306174b0f0a050705030d0e0306071215090b0a080d0c06180f 70
    0x500c6845028105130b441208950301d1004031009001da800110910b800212592013070300844205142400c4144e0304c1e084000e5000070320358003c41c1c1c10750b0300082c80c1c011810240a40e0b40206811510042d80524004421540e140303a003400405162000038204115034460b84003013090401050313129101d18061a01308014034541c04280e100f0b11034000001c1500c820300b804c4409846035007291034281850301c020700901550307100000316000d0306d580d00822444031450240398883c031200002d100b044541b5040d400d4400c2d0b4061042e420044041100144035040c0f10141d5450160f204041d0021041c45a010305000a250511320365000300e0725218240300000401070150380701201511303984c24003400f0944c1c03008a03490006805070880d10005050700d020700d0070710149184a0901251f0b2194070189803103540100d0f088840025610380442e0014140700d21004041c0c0a5100140201098100081c10190111703100421103a02c40e42401c4219a04541d15403199611001d016081d51003482c0c07034000c6403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 936645791 1250 936644541 936644551
    0xe0406023009010209181806040804090b06040b0304080a09180e100c020a0b130b070804050c031b0d05120c030c10052503180c060e04051521010f0203 66
    0x7021000124100240601c210303100d803c80102460000751020013019128040113041001010143c410080080e07401d100c103e110750700c5035007400d907140c0c10301c012941180c12800e842801100305100510180b29041c04403604181c001d81043d071030383c2d603002c1c0c112944102500b0202a13201451400c0c0300340e4000c0c3e0400c004100d000c5080d1b07030a021009a10804481200e83c0010059018070049030201d180d505420f500300b003841c0419041040261120140d042e07007a6110303070000315450100400d203c0240144102e503c0220040e0102404c103512010840035410341c120711500044440340c00300310042100703e80801041c102d00e82c540e051100c5103500ca41001403a00950b00400d031803903880f14418071505d803080305039003103107410341507800808107510440781d035110f0501d6075036403d0007840e4044034020010684140c0184e0005400c149008043c43c20f1064054012410a002d1003820324483e8084c03440c00c03034142e42000c1c5800001c401e41e1442903000c0c10b0840c85501c2c04001c0740101c111600194416 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 936647041 1250 936645791 936645877
    0xf0e031603030e0f12120306180907051f0e06090f030f010212100e010902030613050f09010c030c080c0702040b092d0103020d0b060f10050711060406090e040602 71
    0x20403080e40612800079186131605c003050300b01441080b903030040c0402442d0001405485016554541e1f51510089082501c20011960016408010328506025121295028411082d0521507462400b90205400360411845090041000324580d1180342e10a204610001c00702c039040c0d000300369094001d50144860400705540c03000041c0d60600107542d00000c641c540b2212802903031070810240e00030742010b8102580480004c100d0203026045018481c05040100c44c4000d581c141050200e08448440481d0022b0508269001c072056401001e03055000740401d000c90307620040d500c001801020041100790784080c0c200d0500490002d840c2c21031188441d80e000c0c00150103401442c3c00d05006c1c00740710003944032550f800410000707152060300c80d41210000d81035041d2080d0100000c0c584d090b11102420010303002146400502c8011048424110000e6800728a040d00f4542d00514042c1140540c00050030706402003000c0001d264121090010030a441042a02c0401c8491111141e0030002c0180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 936648291 1250 936647041 936647059
    0x80c0724140d0504060902041112060f0f09060a0e07021006060c0f08070f021e04271212060617310f02040c020c09090c010f0e031603030e 61
    0x849801a240c644141500e0581c0c10b041a001c80b404501a01c0024002c5079011303100d52144006807202d018000500300030f14145501c40b40c2031107103220f0780030300100301511a4640740310314405521072303110750301c4400c20a480303105180e078403000070503030300a625070002ca00040c102040020265003c00c060034142d41d50b0b00c1c01c0c06a03554078201140c00c03c00051019203104003060044000606030307002001c2c0a44a6040800f00721050340010340324000481c000038108444a10088440ca450f00c2007aa0a44001640d042c00c081000c00c1c24103855041100108030703083c1213000e0035040e030144001107448004030b0020300c250f6803941c40c002d12080d030b44c0b0700601c442030b54070010804000440040d04600000c05102d0700702c169132140101c80c4034240501c240c2c0c200660240d80300158a40b4001ca010741c441503001000c850030702e10103110302c0c1d400050021186030081d51014000d07a03441014400c44c2c01c55403818038458401480024148050402c400d500f50100745000030030990031409401502d82d044482b017039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 936649541 1250 936648291 936648359
    0x6091211060105060d0e060f18010509100e100912260402010e010509060d020c12030c07030806210a050607020304050607080a02030f0c1005010506190804080c07 71
    0x510800e240310356000300d42200c40140180c0c240300c40030f4141404c1c85980421400610311407641801b809075005c0204400010401515200041c03400b410100c070403008010501e82039a140b034841180c000119074040d2201d0010040f884200031032040c0c007040d904200410a072515110031084120100e820104d59007031500103032502100420001c6101d00c2140c02d8084c1d03100d0780115400d00b850701019050100a000d00241070301c420010302140c07440b05c500165143d010106503445e0070f100b40846002014200200b144c096420002c1c0e4041981c941058602503c1d44c00010320802d80c80200c50440a40c4001da0b04c464160010f4840110b9002e0000d0712031903120241c4c12070b124403a600407190004410461130000481410081a440c1c3c2c662040da8284035190400e40103641c02050018803d078060303000c18141112a2194500415084810383c0c130b000310002c0307042d210100700b01c010403e021503a0005814014244100d88a42074071600707543d00c56031120030303010400070054010540c0c071050700c244034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 936650791 1250 936649541 936649547
    0x3011503020a0f08060301020d0f091b03020325090f050f090c060406210504051506101709010609151e1214010b130b040b0d1511090904060912 63
    0x802d060802d81d21032940f00d4190303400380d81c1900040c08664041d0340c2042502d200809903c100c130b441c1d0380e00750400300380758449040c81e44103c548206c0035131120305110403c000603038000407050b069a0034103102c00c03103a10003110703485004051548640c0c040741c200301d40c90b840c401c61980201e00c55051800907030426160024400e0b03070340b207104800b241c1225040009000d102d0042d100d40340300e4005040711035241c00c7c203050900140c1d00143c80441e95035000300b400380c0c0d1b900980d80e01075070701960a0f58409911040544010140d2195242c10744c1401803520100351041000c0d0000b0024240100061007081e42010760644061418441d1100d0fa50300c040062600703000c1003800104039440048001c03524400f0351a14111403203209410351103503580701c002d9811502d8001070030030a00b0340701d500061460700003020b00c0142c9900081c1c8501c600c003041e4190001030f808c02d0201070300d0100c12000046581c01540405554030403160302c11ba20580e0071042004100c00c46c4c1000d03107440c0c0300e85201c070301d5018600015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 936652041 1250 936650791 936650797
    0x1200606190305390109061101180506010f080c0603040204021b071e06020303040f2901030c06030b031f0e0a0206040905010602150c07021918060f080d0507061a1003020301150302 79
    0x50b0000d01c15000801280f442120000b05462340003000040c642c41040d8013026149160b40112015004a03004200a58030b00c0c3c0400d00800140029220444c0c87c0c000003a081e20009000a02c100d5001c1255850614420300303000b0088405803c48000e41d03140e603210702402003031b03248442200305580808146a0302c0482641d02031680f0020841d00140c1d5581c038041c03814600d42020b40003404e1107020320840c460f110480f500860290808c0b40c0c1071030420100405071001d03207031058066885021150502d038a00704d9600c0303a4607400100020780c842d0215049090814441c03000e07502820108000c2240100c0b68405030490b1456021a00c905504001207101400203e80c07001600000340b10314009410b05844120304008400e258080c04d40d21020b0f00d600190b00148044c09803a40e41ca000d00521813400f5205020f0305612008201040d524000200300384a0b0080042001d030f16031200768000d200201c20240000c00080100700035400100c070080080d002403092040741c0f0203120400300c03818060320032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 936653291 1250 936652041 936652153
    0x20a02010b040b010e030307110d02130f06051e090a182003012f04030b16030b09010f06050d02070204020c03120c030421020f030c0c01200606190305 66
    0x91410840c00f601d50740b20a0000c1c0c9d0303800d5000a450703410342c00181e5900c1c80054900c15207000004400340504014070844000707070442c40c01041c80781c400d072140c3c2080305011408041c0840c0c0c1d0f0a0540e460f003500d41e0151030302010070700d1303e000b80c0c402c2c1c2d508000c41450350325101540d81c4901c05101020108242c2600c0000183c2c1501040c200c1c14541c0c4c26040001d20709016a41002d07051034150399585615004c40105c441504207903148403542182507243c0100c0d0b90b2103400301d0f810410341d4103005c52411a021584140c4040c4900014480c444030b125805485c501c0b50010b0045403a0441c00c022141c8a5000c2003410110b00e403100006580c503d034560540b0301664206900306507a0304c1450719a404110700340191015440351118207a07440400300002d01881c03000802801140e40d0010000d071a030555110200407141104a0362a0786e001c00050ba5944940100d0300f0300c030420b10055101808038941c0c2c2020344180034a241804580302d83c4d0300c0369081142d80001c0c80d030722140c03032802d60701403450380c024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 936654541 1250 936653291 936653293
    0x20a1403011118100504120605060907020c01120b04060e010b070c08010c02031b0109060f06051002010e06060f0111071d010b0a080604050718080d080c0c0616090801020a02010b040b010e03 83
    0x901d404a030404804013200500d203801d1003071505c1d032504840350401d500324208451041c0c441c010001241441101075400135254002401b1000c0100c0002c0c0c1140c122285804180e075582c0d450204aa4503600b242c4020300c0810815001541c54011290040d803010006481d031030000c00001815000c148208814104c0d03550186003030500d9070381035103140d51041551500340d42d01c50050801282036485480c040781141c000006240e0f1901040c010601100c2e103030401075901d000f4480100110101c1c25542c441070841e000540b410751100141c54400c0400344082d0316100312400820780032444144900074107103155141003103a903191400c08a502c1145400800598400003084190605800454000ea0241460020090181820003a00340c00341e00044680d80142c121410703454000800c0798004005424a61504031481c00d600d58411f80944044d2000340d8405030480c400384035690030006800317444000d65484c41c81c0c1030001c5c0603000f1505424070491405405560542c0100110242004064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 936655791 1250 936654541 936654577
    0x80604050303061e030f010e25150c08120403090e07050d1109031f0b060403081b1c0806030f030a020c0405060d0516030308090307080f0304060603020a14030111 71
    0x14024070074542030780074003030f11640c05000800d5a030502151b524983c0407000050060303a42c0240703e190002c043e02c2180d69054075108801d08010002080c070070f4400ca107905c2c80c1c2032158014100d405880b4108041d04441c03000c51042d40c2a01c02201450150b4000d58480d07111945a070500048400180c07000d4002c60400c001112800c007154200040c800495403195040c582c002012a04000c1c12418210b00d04580b822601a01c404511615015400640c0c0480c1003070309554441e20284240840710030b48024100701380c4d0140d50104040018000541884000c00414290140100106407021072090050480700c11048000105854074024180e004003040424503044c04000c0030f0203401190407420020340c01d00410b0003000b01030300c0511689951001e140c69400e00500b102c40c05410842590420040c600208004d802600c080340c09400e0050b68030748591910303100402d0603501c000e400031003200001414251001c800700d10400160020301c480c0048401070062072140c0c1207640070141542c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 936657041 1250 936655791 936655801
    0x40b04030c0e1b07031d03030a0215090a0323070606171515040c090b2110030f030e0f090907090f0626100510180e1b03010f18020307080604050303 65
    0x646c0d61409200c15401001d030094a1400200c0d085038045151040542c1c019190a0300040c0303040c5d1459400b090542c003a00512030150b900074020014524035140c1e4001c10032411124070203040455401c25403020080204991301c00c2c81d8110484000c500720103d029005001d038a902d207490362a071107a403100059149401000c01000000d101140c100c0e0204a4a00004151141c180b030060140454010301c090798020703e03648642045100034403e0006841902040000030030082d01c000c1021f80c5410001c3d08004004003050548014845260f407100c180f0046c06006400444e180007502c50ba070710144a80f2819207080805d030707030b000d1003020110303040751210303000150250190201c0f03040301e0400c1d551505001c0000300259102910070404003900c5690401c00e507503290380c45101410130110305200110b04034004c01c0d142e0300b4085032001d1034404200c00350711a607829841510300c00361007501003100154000300c0541000c0c1202c8103c1c080d125600c0080b4400c0000661544140c0d4040300035451a580c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 936658291 1250 936657041 936657047
    0x30c080307031d06040507151713020d03170c090f0906040b120606100c030e01082a040f12080304110d17071a0606070602090303040b04030c0e1b0703 66
    0x100802910402d42c0c1c0700c4034401000c00ca40c0c1c4010b1808070050041ca51418241030507801c15007164820303805100e000315520f44850700301c290f0710510003032000042c03800d40c0d4000291f0048500c0d900004e62246020111034109034001c10981807102050344010f007555036044d001c817a14402c0a400a900c40910040410b19150041896030710050103400418840012800b0510035220225420b03415000682001207905180001960054080c40c0c4504070601c2a18042c0030406084130702810804440009610f940d18403000c5840c695201400040703030400140c3e90301c0650030074096041c0300c0010502c005100f80e007845600130780315000351110745180c55580d612807132041d0781d216060700413171100e0000003c21180301e098466805203a424541e5074209251105041c0311101c401028201008140b0525884104c00e641c0e103da8400d00040c0d0314800c05002070f00d98052548402000c600c001800b00410944001440480d00e1079000614540c41d4090075802c18400d0204107c40480f0912490003c0b0744 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 936659541 1250 936658291 936658297
    0x40807030f080409050c04090b090408070605040f0203061009052a0706110301060e040509010e0c06070f060f0204170a030e1e18150d0203060a02071b060327030c08 72
    0x4420980710f0700c0e1680d00d158000035510100c45a42e618440440c2c10401e4081a0107040981c440c03c0310782c0c458500d403e51f11580c03c3d0140c400c018082c25582e900007800c0011050342c82602d140c00400300c032001e140c1400701440103000c6000b0481d00741e0404020881c0c0d80070340710006034840441000307a41b03c5e0b0032040d5801e181d40c0112406075003491f04c035828007118050041c021406003400c1d0307881d440d403011904144000d5075000707068103115a14040501f03845220204096020581c02c07502d20395180c2d4903060000c14007440100c0600f03014070701120303400200e480354020421591a0034000031031050600282c0c1d158815a18041c0114100b240c04013514a01061040b01c0b100030031300101b011400300030202c0d0100b0001c4119581c0c0092f2802440580603440340c5c00006550700716642091050f580d4042a12107401904008000343c000c2040420030090940194660110052410b80700d0342c0e6440050280200040600080c0d8040d0f64005000b50602c14801086400d9210341200381200e40c0d80403a698 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 936660791 1250 936659541 936659543
    0x70608060a0b0711100e09040311010e03210108070b1608070506040302010b0a0503011e0c030b090f040c0b030609041202161214030c0a0609020a03240e0102040807030f 74
    0x5895810007203600b5418001604105000e0204c0d890504007070810300005c88a0701d0790769028820365110320303e07456031103403200c80d805941407520180305c43c81510b8030790150641121122280c0404144c40305c003101d110081e100c400b0446450340c9183c3c0d9961054580701c048034042c0000900c020400e811070f9030080340081c83d00c00c0c403645856152105540750141000026901100142d4442c079440101e8681004800f014100c01c80c001c000c2000f81c08400452100000341e0320120380e855424110a540c001d51010903c1007020b0080c3d40185080900c000501c0780441e0100c61441c4a6207020803074541d040b00b5a841128003070800030203500d0759141d028880000100040842c42030301c40c1c1840046501940e00c0c001c2ca9052040d400c003080320300c0e000590440c42682402980d0041c040c9880c0c41d4000201d5020741d0380c004074002007101150010a41044203500701911026840c0c031040c2146081d2108084051203c1d41c0810402c2480c503d881e007030f48500d00c0b86103103039840305206101051507800340040103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 936662041 1250 936660791 936660799
    0x5060103030c0503090405070e01090533070c0b190512040305130f08031b0a080f1305090c030601120605060f0c011b0201020702010207211e050f0c0f0d020307060806 73
    0x5c04000001c00740c0f03000f150003400041c1e10210144007035810070110720103030000701c5403420001208c030040c52290911086550140902c234444100000382d0b881100c070607582040f4411780d510384075000c000d516880364507500610f0100c840c4007178500d4407660554100e14511180c0072200c2c1c43c0d544088421b40c02001c400c00c1440c00044e4002008040c2c1180c030310007001402c020b9600e03000050190b4000c0350922103240865004018010001204801100e000b0b14540c0c0b5610f441e22a07441410f0700c0c144a641003245c00514840a20800c105180701651103101e0983c1c810741c0104d001c02951081c1e4000d403180300d800040610940d841040d8500c00340c0f01e0410384000000704c040c3e02000d181802240b0000b1100075035800030b06c140c103550f81800590050a420050000d04110445426021f03003103888024006680c81403483e8808081030b60070800c0150404111642080e08850650f2240f480d16400b0740304103202260803090b810409000210150020b01401d106840c00c2c5040c0c031200d80c02020719900c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 936663291 1250 936662041 936662047
    0x20405091b0909100f0e0c2d03090618010207150f0e0703080d0c0512010618081f05070c152d0e06010504091110021002122205060103030c0503 63
    0x2d984614555610941030180046035813480d200001031540801d07080481ea48415900f04042c846400b400c42c0e1580031220a1428410220721003003404940c0c88804004040f000001d20800000c002505400344e1488120703c4402c8049690403401c03031040c420000d00c3c3c4d0640700410f400e11121940004244840c092010400d104d42684150800c0c03907540088a00540119800c0b0400e9001d01c030300120048141400d03407400e81461014813015034144a03000400141024013404500b680301041c1c0144411070440d070702e90004000031a8440386c03042e10842c0301450f04000038081403185500780c400c950070030310359400c103403004040c40b02500e2568106021300c103c0034048440882d0031039404048007030044000071201e1100340c51a0500006a0010344214102111000805c216004040002c0c07400c0b2400c200d8411607590036801d00b8003111000c00c03c2e40c40400c0e0741b142d03040c004001a104000011a0003c00c500d040084a0340d003103000c401401c1f56000d0001440040e009485162003c5d01400490b41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 936664541 1250 936663291 936663307
    0xf0a0506070803090c0901030231021c14130209060d0209070c030f0306030819030609020f0403060b0301051b07051207031d0307082505130209010f03020405091b 71
    0x4100d51046074212910a00002008091882889048400e51048800913460751654001400c0e5001c00c03002941c10300712052600f502c1e1504030600c802c4a1800200c290348a440001400f5003241029020749405414140610244282114514030682042446890f00700b055000e00ca0078a03001441e60f904100b00c0003554001d81e039641c1c0c2c1980304501541d9850007825882c5001040c90f0025405c100c14103050420501c0080c401d0415a4400980000b0302148208904002c802801e02c81e0f014446480c4001614000320f01030500410690b4090001440070301d55090502d82240ca0840f600e400030350301002e0004100c0d034114000c20000780100c04481e40b07001030000f107003401d0b408000120085004545061250111310240309a004d5080b005001c00170b00c0c0204968492401807000c00d169040821020130348a903071540000608000b5100c5603107038a090030804001d40c081a26180030030805600f00000d10701c28004c540c152072000e0302000840d04d403030140d4003100c0c208030300d200803210041c41480 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 936665791 1250 936664541 936664549
    0x80f0702071716120201090f060f0f030b090108030a14041a090a031203020909131106031e04050318090c0403080706020706020c0a020418030e09070516051513110f0a05 74
    0xd0042c09204e4413071290184c640c1300243c04001c01e68410301680c94601d00401400d034012004240107206403c1044c464003048038128020900460010b41c4694003d00214842000001600b6201c480ba180d20a0144a0201d013100c180502c0c802d20402011400c5047c0c00c2c00b90b51405858401c20280036241047d80703c0c0d46820b00703026181e1041c0000b0398085101c1c82d01e450b2100d01a0b4100301445044460078030b003510307445003070400c1401c01409014000f001c00c02c0401d441c0c0003d820501499005081d9040030300e0116280c3d8401060410190740c3c200c92143c0d42c3c5420140e207400350030803114203441d041c0b460b40ca50081c0d0304030f280c0540326242c0c00d01241f40403800c14002072600160101c083c1601115920401048030301e80050104a8070499082074000380e001026030300168400c40d0f266403280d441c900221418456076520311103a000356000d9004121002410082c80c8071401d640030a1540c0da46100005003074140340140401c206140c00c00c00e10308003495101c0220201500042107a52030390046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 936667041 1250 936665791 936665833
    0x51b0f0f1003060f140a0603020c0c01350906090601080d08090309130c0206070525530a050d090212070302012a0201051b070f06080f07020717 63
    0x104800c1786202c0704001e180e02d080482e94002d00000d00b001c50402e1500900160317200e9542003106d050200003668074820442c5d18130480c0615904034640d110340c6410368104103061000340c2d10300030f0900c45d80000c1440e0b0007001c41c6403030689182d58010300310010401001c0380d060070040c20a2203640010051a0980e8881114070003850540e80f50210302c1c4510204004c1c9030150080c0694108042400304804405500d18000c041020301074483c0000041c9007003180c940c044590107020f12540030581d28040c041030310030200d4468421440701503030b42d40410014404070f01c00801400d410900b0030180800f1030145000c0c01e00c110782c0307000014100200380d020419842c461283c1c41c180340e0080c602001150b0340014036a490031240d02c180b1003400c074810b0030500903105004001741402008686c80d01001044040000c202c0208411684010750300c3d000c941d041c411764011480001c44000019281c110144501d5010340c0b5160b0042040c01c4c6401c00042d85000d010100c0b204a00807010401051392280a038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 936668291 1250 936667041 936667049
    0x80a060812041706070906030e011e1b0504050906060c1c08011a0f180d0c090506040b0d0b150111060a0219110d0c080405030a051b0f0f1003060f 64
    0xc255952818200d00f0310030f210a80d0707040340c1c2c55489141009029540144200e007104c02c5402c0103d42c3c00007a04001e400340440d5848200701d141c040c080e0040400050700442c016040d54000300f2200c2c290480c4c01c5882d4450740c020780b900400300e0004078601741010001010250503044c06e44448081d030504000c1103080d0003c0e4400003515001c014080180039103042d01140c00310081326403800c2c15103003640c1d4881c0582c21020904c907030142d07003020140e100d20464851550303000e001300801ea9181d23001f0000820041e90650300881ca0040307500c0007400c040f1011241c032600901070700b45582c3e03080c81c0000b09400b4622404d0402540d40e180c45502d40c2d04000c0303103000d600c48540141e240d800c031150142c13201100d50000000c10070248525101c0210108181100316028035101071006424127207a00c541c07055603c82505031103003510900600c407000c91914410300050b4440343c8400307032007030403c1000303039003000c030180d00c0001400d508820303141c0780d25160b150042505002c9412550344603180344c01c050683c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 936669541 1250 936668291 936668323
    0x80c12150112060521010222150801030f06050408090418061b171521061807050609120a0b1e04080d0203040c030b271507080a0608 58
    0x1100903a20342c0c102e060007800c80041d03001008510b29040c0061820f50f500d0003110703e450907011a0741d03414031003901100c1d08158804080140b80451802c0540310120b1031040f0703e210700e07003003040e01c2d00c00d841041d41034102c9402181d0300040c920303a40c55010003054054011601c6001c208043c1c60030342c40e1801250111900c000410101c02d101c0d04040c829222400d0a1070350540300218016000e5800188031600b4410000d00b103500e62f41e401070000640d2030003800d15035200d41d0719020585500000c003102d60b10040d652041c0d407c1515401b4102d640001151484405900000400d208a080c80c0024008082005041031b40c1400380c8510517091440418094408281250400110003083c40d0a000320228020b40107013249000c1d20f440549000d02041c82e04a96000008a010320a00319000b60203542c120144c00401e0600000a008602d80d00301d4800d0090900128480c56200119021400343d4070320b03803030980d00d0307940c00404c03555254000c040401e060740d1900c2c0442c401d0010440030140300c0d0a40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 936670791 1250 936669541 936669571
    0x1050a0f1e051e03090d1d060d0204090c0306030c0b0a03060f0e070801060c0f02040b030a050f06150d02030a020f0d080c030d0e03091806010309081909060f020303010501080c12 78
    0x40c20034a40f1088165640f282c003810024800c1c80440010448071600442c9040d00e1440400f0003000c2c5c121100900c2994401ea0100d008042e0039007541c014400c80c0d0803480c4c100710310701441809400f0380e5070610024000040c021300410080784141300a04a860051400043c4140c8407441844e1915064000c01518142d00081000711900940e815002d030040c0e0811594041542c4d8a900c0450780c84080240505d40321501c0d80e51540303003003203000310b110341c0300d010b41d192002c00c145440d036214022240d072100d101803000b580a031810041c04500032660050040c1c01c4401c807a40a00c69075408400720140c00c6040100b082c1e0104001c10041c0c00145520800340d5500d101c00320b444419660301c07004565042e04104141090703540c0d4011180402d03a0390100c54800f9030394460042c0e00600e0760f01006004200d0000345100803201c000d000302c480c11070a840c0c800340152144c0c812603100c4200c0c164a0003590082006100c01e6000380000c5034006c0e00c80b030075140313001e1048951815008090350550f1800c8104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 936672041 1250 936670791 936670807
    0x1b050d08090103150e060609010c0f0f030f0f0c060510031709040b0603130b0c0f04030303050f07020d09290c06040201030b04020901090504091401050c04061d01050a0f1e05 76
    0x15001e083da004400e4204d20101c0d5003090456144200b0241001d4810703000011101030603401282041202900700303402d06c020345041c4c02c22180c1d4190130b01c0210001101090410600da01401c50182811115603d01c442e10303407560b0b503a500502010b4884c61010642c0900040010b000c140c40f8204100058001ca0725200326909000a440d2100181c512500d41030042110710410740755243d00440e045990492503403201d40742404140315008811448040004002c8189a09504094001d480b0400c5802070f0703035603032081240c65402d62103461000403180e4034100903404080300c01d64060101602c229090f034140003005207c0c2c2d840700000714181e0f004103080001303543c1c241c0300d030313401d402c44c01d0f1001d51070111078000003003901c0568065a44500e13502c03403140c030030b10140d07128030140c3c0800440208054100326182d01069041031003020006070070400005030603407090900c040f5182c0c0c10303142c0314249481c3c00010b54200c6014129801000094003102c03101c1a207172a900480c1021030b850310b542e600c5c45 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 936673291 1250 936672041 936672047
    0x30209071d03060c0d0b130f091103010c17040c0521010c020c0a05040f0b03030304050f190b070e03100606200a05060c0f1201030818040b0d1b050d080901 68
    0x1c1001d005209820003810461000c41d480300b15030b005800c21030005440d4503610000b4122801c0c04094084551604402d13107801070a41d0b20200302305015401d03001c0c450800008050980c0d43c0401441c0c0058070000c4070054440e4681e15282d041403045038040d8075992910049035038448108400b0035a104529840c40c15030b00300788078000c034801561010b070145034880c00201701c0e035501c40d1181c079010b0b80d40d4010010740040260b015001020004041c0e03562828a0b0416641da910310312010a280e0150405c02c4401082c600d80500350303560302c8201c2994540d0356440c103980d80101c0400b060b4241c01a24203034405c01d0054411400900302c4c0ea201c1c49084540c035064044019441c0c55071030115408040c6540205200107000740c0e000218000e8541c0e81c00c2051501c00650003111051014031303075014000310410010701c2c00341a200200700c03031810000d000201080281d60140d00c842d03400c480c01145010100368403051000050422240385248195a00c002c15440c45100e1001d950307081010480c1c582642e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 936674541 1250 936673291 936673337
    0x50408130803070302060106050f130b07030e09011206050a0209040203040f1403040605030a09080405030d05041404060b191e090f0e09060703020a02070f06030b0301060b1903050a0603020907 84
    0x800005504040440d136001e50f48180600400060003004501c0302040450181100d922018008038154181e5442001d01e05940003440300310301040c0c1c491007080045c01c151000034106c611840d11074228a01944440e801010b002d0113486070745408010700c21603915640015030190b0700c103c0004526200a040400395410b80d4900c03003a50390030411080054940c880140c0303402000e803100014112800e40b415103014800d0f0340c8080e4240c0144440c2a16003a0400050411512004d0300c59609100395010041204d07118003600e0407a1100340242e910407045030761080f2003101c950412603001400c0c2007182a0039040b95040000140103420706000301310a0502a900900c60511400c0460a04615181c0c5681c4020306040c10035a020070481c007080e2003000303040c1c02817054400b1540c1c52074580b500100540200b0207420700030340c03c3c41400550b5074600c200b1101c086c030900e040d00582030100001103018100203400c0d08d070410381b03c0b0f1000c00965070b88414203008032095210310007110f0700c40403040c0c5645 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 936675791 1250 936674541 936674549
    0x6060108070806030c150d110c0609030412060c09030b28140115050d0203070822020a0504091103030f25031b150509010f0e07140d021305040813 64
    0x214107082030002e19240020800041c00c0102c030034580c6d61a00d0352103485207005480b400072809080020303241107a50401c00074001400d5800136140d856481e1009075540e442680b084000404100e140750300480c0d83c6610207002c41c42b0a1a081e050300b40d07a51a8500d00c50800e580c031005030000181041401000110203507034000c1d000b0810710002e240700c2c406401013901407117105081c000c110440c2a03060310400c00c5964f0507403140c1c0d00319200e040c0200300815814044400040b40024aa440d080113049104000707921a0700512002240b410102880041c0c0300401e0101ca0000500a150403942d5042c0064800b5150350984c1d1600c1c2c030900b1b07004800454408030042030102107112000040390b400019958000c13816080c440c0140e165241204c0c400341c216018250361032406092200f02c0c2c0040d0411209040c112100740041c040104d075154840c03255106207600c4001c0c07500b0446050902500050003240000e00e40e40803000c442d441c020549400b00c0d0304403030700b0000040e44504043c014540030064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 936677041 1250 936675791 936675797
    0xe010c03060f0b1603050c03040e010314030310051c060f050a1401030507120305090d0c08010507050405010903020d020d0506070908010f06050105090108091207150c08040314160c080606010807 85
    0x215183c0b1042c1c0d41544140800303050b400e0000b0f41d000b420b1600480403034590011a10403030350384030780d40e1158401040c020700048481c000f8080914042503000401c1c1e0f030040d410405010701441c41d020401121740030245c03800c006414001c085070f0104d03940b0710924909145c180000308640c0b50004041c000c50b0740c00c0d150104a04940c00c0103102141c1c001803510159158407002d400c034030103035050503070300c50042a8140707a201c50001040820000541c20303103821208000000c1c0300c0f98890040c1614180282c0c020a40000d00c0140100094a0810951030383c560000d494161031514988956092000460300c440c0402e80c1c0030000c01915100b441400c4090b040000104040360911000a1091141114007810404480c0c0800c2184805204100302d2080c1d40b400035907100d08910b0209088101c90742140421454001c14106031806a0b41a41c4a40c0c0c3c16075418034090355040384110290000d0f40002d41c024120b500d04000120454440700c09081d0079801424030b0300e07140d400188820001440c83d010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 936678291 1250 936677041 936677069
    0x10020705100e0a06022109130207060c11240a141312030209010c0201080a0e1b010e090c07020d2406090e1b041a060316180503100e0c040e010c0306 65
    0x30004000300c510711004103c202a900e10307601c0005520010300c4103100c88d2261000038032508200303482e0300c07498a800c0c0640b00d88000340c2050041d10b0304c0350920401d010302d202040a8031841c191618501c80ea0000e149040002c5111111180c1c0c01c1120080b1200203103445400860000c2c82140354203117100640c28a07041d0f140c030b003401000a00b0f4094069009041c08221004103d0502041d000340600101c03400495800c85a80c0166038001c1807540c102a0210f03104041c1014582000c203042031141c802108441c1c0303412a25400e00c18159510034080e1151140702d040044400300d81d440000c085423204401003090f509080c0340d101119260703440c01609a12444040c4001c40b081407060b0004841210000351000550280c200c0c3e084c01c0c42c902580c411000000c00c140c50700040200d040300c034140c0d9035195003d4000c4d40300c5880d14020b401013a905a00000da42d01e00c98030690019540d18581074140c401c0b28028202180656048500b6038400365116090441d8156051041c080105418481012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 936679541 1250 936678291 936678313
    0x70e04050c0402090d1502041806080a0f050709090f061a010f0e01030237020a0f02041808030f010326090607020a050a090f2910020705100e0a0602 65
    0x294400c080881c0c10300803500840c071501071340c0d241c0e6100651243c220003c407140e8030203544000000c2d4040d014880584c280c1c0031200b180340d0100e115400548800300c000f0b10310240725403107401c01c00341445d00031100c5200701c510200e4803041d1402041c9126100d03281e90316940c5140c3c5032080a4a10203004061851030780c03c507042c0540c1c0c1c00081450b0301d9100381440420441c1520040707000c0e00c501004425824030900d91010b0081c2c00d204515980c2c1d9000c85c16009500740c0f18003ca031251414807000e08258030303840e210000740c90140c2c08030340c0c409810002c1c451004210385c2c4540c4240c100710307101c1000b222100d0040003440328911840e0700281d81110940140d042030103080285009005600e40a6003002c11500119112081640302420004107854811941c0f00340d80006010710319201e40515050604503c44080030300b00d00e20020303201c04900c1422040007000c2c45494041c0c016a042144281440020580c480010411134040c41342d0746d50b10029050001d000c0000c18551190301154400c0440f49 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 936680791 1250 936679541 936679543
    0x15040e0606161101090b04380301030602090303070c081c020c01051204050c06030c0703171905060a0537050306040803070c080a2a1e06150611070e0405 67
    0x102c15030150090b09540e8084004840401054000094400c0e0015000c20b40202140c0803200c6041d2003041ca20f10512249115441c007482880d0b01130001074144010f00000392580c01500d05244040c080f0381c00e1030050303280c003600422140d01c030b0400c40e00701c0210010300448100109601d10140e0005004da80c582000003840d0380b188045c68a450100d2300c01050401c8014000c0c1031414400508031a01c90030303c010765a05903848280214042443e412081000e4500d40c1079141c8210a190300700300068102c54400790160600408003030b4400b024610214299494401188078440d40c60781c03c12036040382e802c1d0b0a41c02a07070b41c600102811031200c000c00c00e40d41d0004000e03a01c6135021180546a46682d0400c4c1c0d503416844074010401c0001003102c4000c42e600011201c0303500350700e00440e00c040c142000800326424602102070203060302440d07001303055001c80303c5002446110307000010308144000c2d40b040380d0882d20b0300300f030f00040d64003070004540c40c40811443c00546000307803865007941080e035030701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 936682041 1250 936680791 936680827
    0x32c030d0e030a20010f030e07050409082118010504230a0503120406181203150f0f0e0708160c03050403060f0f110403051f06030215040e0606 63
    0x1010400015040384400c1d91000d000404031690f00440000110a40198240d1a030082456041c0003401c0b000310a020386129024030701052141d100a000d4880c1450240405403a01c4501a20159030800143c00804109043d40715104141c0380e0f403050303504200c000480e48202c10103c0183c281c0c10241408085123201c00f0032204d240e01003400100d040a49086035041030701e03844002d0500e00000c40c03010301d0183d807184000e20840c42039001b00401910701d050f201d502c4c0310f54140500190351341002e1000440c0a41d00451052040070a8000c4103a6104180b03100c4d03a6041e04001e483c540244010001d08403000506074100004e0304010300149080a8103080b5060350304e084000300306e040720015040c0750080c0221400f45070846001d21503034401c2c08002c000303804030080c20b042d02c81c03401c00e01d80302141d000c006480940358040050520740502c81904100d07203101414001d074403540e5a5001006a540d0782d04419040d20030352507140c54030300e403016200054034010045405088200502403042c05160742c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 936683291 1250 936682041 936682063
    0x90515040e04051603030c0c050904030206360c030d020105041707020409061103240d170c0703050714012105070e0a06030e2406060307020a02030a032c03 68
    0x14200407a81c1e40d05116207814040c0c0304c2a440301d0034480001c01819400742c0b098640d50f01030b01400c1103c0345d0b92418450281c1080b600a80180c00200200300c0b040340c8803a440220302455140140b02600890020082d160400b410391030075444181c000c016414240004c5100b10701c035000030000c0c5d01d09512900c494200760841900f00d290002124411036980e40c0c403107904113410000c1085591012000d8117101c4e8411f0301c00d0304005c02520b030300c100000450b40202c68000c602820118803203007580e4400d04501c0c011220010f40d01011f020025079950104a030000071400b50b8000c010040ca803a80f0603134000411980541001020b0364816002610241025580c4102c0000000c7c1075440c0001140e080310100201a40241d04900004045034903030841240030080e0015100c240c2001040880140002072000900300c0b040d00020300589800d0000d140d1129050045e40c8030124541d0000c1d0030660f62500880220b0f03901c54040b01c68201030108024803411130601400422400c00000755503135a0088 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 936684541 1250 936683291 936683309
    0x11120a052203080a030204080118020f011d280e06010512131505061018060e12060403210c12020f042301021606091202010302120f010609051504 64
    0x248603880401c0001c00d080c0216084000c032600c5120501009020398400c0c483d5031841e42c2400903803c0607880c45000080c03401d40c002e24068052141500544100455403808007105110701140d00c125210b500428002204040320f0081c24800c161140d598000705400c1400b481d40b4840401110ba40c007e000c0707807464059640103041aa46d2100b4001d14108110b400512a8803c2816040703039445030382140740103a00484143e605100c656000b1100d2004120100c004640102c0d4100301c03003805807209a10802001e800c980300441c0103000e040c0340800649003240000c5d05c4512080c502c0c01903102c040f0b80c261001d003050040790801a402440d0407a6018001385095000602c034601c000c08030100c8004050710403040402c08229010502204c112018103400b60181603a029590450b035200d501c1503440e240c40740100c050415240e81b64828000300120306140c0d0810460420602c0d00d1b034003c1c461140c0081c000b26039810820f00804000c6543c4c8494092608607880f200c0a41d5510241c0303042d280301d11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 936685791 1250 936684541 936684577
    0x2030610081f1e0c0f05070b190608030f07021008130b0a0b03011401080c01390b011e0f0b1b07050613030c080a0c051c020301050711120a05 62
    0x4905a0010f011402c241454503003410601050440c0681100a036000151500c007928030001405464520404c0001480c0314900300000701c3c0c41c2c40c40e101d07856040c1500360000508948614500c0d10b9130340240b1607120310030408600801146001d08020307200c940d030740c40c2002007030400100080c20341c10140001840002884005814001603500221858400030024070a0302c40200850a0780304080c003594103203015541201881c1d5005a40c400d601c0e4940418620101500c1c811030400381089911000125900c0f8004401198500e96840c0c082c00400b10b015041d00080028207845c0c000551003080c0711217120400300709803581e480030396480e0841c0520300f50307250070007403d0382d801c090450308039562088000c14a065885064075007032007920b102f421070504444d00e903440b04d03a40700e6207588014080c00115800340014200440d08015845003032880d002c078040d81e940002d0a41d41d040340c0e1040080c5000c034510000c44001c10401011800c155113003484c4c20348942005040b80b0807071314001100005a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 936687041 1250 936685791 936685843
    0x1b14150c0c060a030e01140c0403021e151b0109120c0c0801050c091005090906040f020d09050d021603021e0102070e09030315030115030b06120102070f0203061008 72
    0x81c00794801d086802006240e0320b8440040c058014622200740115542c80c00448841c02107840a07900d02400d0350000c0e40342171925541c02c0124540c2e8004081c5140002e0158842c055114150036408588045580726111029650720344658001c180321031100b40e06110189000c1610704814041040091400300b107218503034100782280ea040359200c0d849070f41ca07100800840d00740d0800070b0308135484100d178407140c10300307080320111980d002d01404180e1000100b808030b2a40c0c031309a03000d40d8113003407644005801d1041c1404503104445a10f5020384040e040400441040c0b54140000e105949543e82c031150b00a04580110f45002d044140c0120750311118404030300380d60f008112990083c804d070020482c1600e40000c90315100d4006031240e41880201d0880c0380a545418007921040d1514450f80041d03d41c0ba43c2c45940303240c0409405250048995540044107220070b000a08401c2d001c0c0d14521a48501841858a401c100030140c030b6240720201014050b0507408101505407105204d0013050b08410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 936688291 1250 936687041 936687043
    0x17032a040503060f010914010803030708060a1805040c06090b09091e0106020718060e0f06010e060408150108031213060b0a060c0201090609060203070f1e1b14150c 72
    0x51070300000d40c18403902042010b444042880641610012201482801026200703460324130000c0c000c82e03039079070001d200084000740305010456100800400700c1d0550b943d40d03645885c071201041242100300340c41d2070401060041c1025003200074204c41ca403100d80da42c42c040c03202d143da010340300001e80f11744690300224070a80c200406c141700380c52810000c080c16503952107000e580e8980c20301c2841403944e04c4040755000855203204850894201100311340f07160340e6000c95401d0700c101c0105940c1c14002c05004014103501d804000d0030140205200505214065000103000940140c0c030081d45980308001e03c1142a50404c0402c2d0014074503600c20b10b000f43c062521074041c0c072503458010b030444c7c940980002c01943c8a0103030356002e4001c9e21110316290301c0e40380480e02c20009021b6207000d64420011140010b01c0200d00103501806080900b0303030860840700006e103880122038181c600845844402007803c7c4052010f0000306421110160580380400202d0809000e00a500100342c1c408282030360002c05c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 936689541 1250 936688291 936688297
    0x1a030f070302123d020f1602191401020f0a0203030a0c030c02040516030506240d06080f06061c02030c090a09020904210e13020f040909050a17032a 65
    0x5205000340005000303214001c031490515080710444100500c49581300c1c0740e03207101b16103802c0d0518151703034946014600922a1a07400d000101c0e0061044010400b0060082d0544800f031f1540141091300c07505c1e2100024906030102d4400358068201c10481c5006075030000841300c0090f540d00f44914504035909050300c0c4607010b01e401075007043c03d22040001c1480c90040c03014041c141038908110b2074480741d05001c4007051141c2c0c8210501406294011101120700c01340070090f0341c5c0c080c08241d04e6158001e1a050090440e4100d0455100005103c110701d084045102132402c000c400c000000c84540001c0e5560851589d980d00442c1810003051038090b46811540015070041c0403003050f030078103182c24010001011380c401c0e600109450400d00c028810311140c940080c000340421840d40d06195100029032044030f204e4020001003000003405440d50040440d014050000b400300c9614030306041002034800c850590664400b00100050000585452800102c03000410160000440c4150000e44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 936690647 1106 936689541 936689563
    0x8041709090a1805030408070e09030a090b161e030e0d03080f0907030f2f091305070906030f0212011e0b0301110a031a030f07030212 59
    0x102c51a00400049810040102c40e503030b60300e580380e919640c4241d00c4018141c00504023045150020080158401c1c210000b82d0300d4080d50010041450200d40a901290040420786e20100c5130301001d080085a0b1060898045040c10303110890812065101200002c85420001d0390500305003c40440b4a0341c11340b12507255403901c03080d00703080e40001802481c1a00c01e0904c00400300f0031098400c85d91600640e500d41c0c0c00900c0010040d84650070352000301d005c45c80e140d075032801c649504514036400240740020f0a50800549042c50405a10750310000f0a1824441c011091007000840c2c030038514401c641c1039800645020b071040c20384928114003004c840d100300c0b1003080481d847d0004015200000d000040c0380460703003540c142030b810907511400002d6550300c445180100c140b5620451a1040300100b01d141c91903a0307202c1e517500003400028021a42e5000402c103001d81044100382c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 936510791 936690647 := by
  have h0 := BRFrame.cov_init 936510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 936510791 ≤ n) (h2 : n < 936690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
