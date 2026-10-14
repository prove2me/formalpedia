-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2830
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:27.607991+00:00
-- url     : https://prove2.me/submissions/088b5cf7-283a-441c-be3c-3b388d8257f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 508812949 ≤ n < 508992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 508814199 1250 508812949 508812977
    0x50a0e01060f050d140f03071a010801020712080717150a1a090d0c09020d0506010e0a0305190c0f0e04060507030608061302060d060f030212030f07062d05090d 70
    0x103400240c501da0001510341005c0041858140342079080f03070380d10440e0b010128140e03041029401c89118a183c1c0d10503142c03040e988a04180d030803072003013a1008011b80c1c220a04280c58901078220715610a007176040c008030508554000d140c8011040350329160245103a8440b108600d080d40ba444040c051421a0304100c00103900061428071070625424468070ba5100c6003000c01137aa080d0038040c12810b00103644401e10034081c00c0213007509a8000d402b140581c0380c030a41c9030504d0030329201201d0f00040200f200d010140614110840074940c2074030481001c2c2d10110300d448100800300014680c4480c001490325007824080c00b1294041d1030300d800c060034100c0401418000081d83e6801140d02500078410b0041840010501e02c14001c1185020703003800f40c0001c1c00d074000c1c400303803080b28029140c2040c640d400000043c0c90744148844405445030900407e000b01700168424180184800c070203850131203950448034001c116040c0c01000e40b0382c0380c80822010342800d005409072016035052060383c5007001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 508815449 1250 508814199 508814209
    0x105100e0c2d090301050f074e0c0314061c14070509160203041206020d050c07111f030b040f05010b040e070e09061210050a0e01060f05 60
    0x1c1c000481102001c55650304186100070040c144075254070308038000c00d200b480d0030200d5800c030540030b40c40f175460003000920745060003000c684200c07041ea99174160321900d01400404e1403141c0c001640400303401140902918444002c3c129441c0030406c030003040c0f21150380700e0310903201229070130801c00d4144529000d04003001c0c090583c1101c002c4500030402c2c00b010081501ea46200c02d00600507809903d40c807108640d010515100361401922542050f80c0d07000b40207015608281050380050780100400c1201c4407005d00b00701c1461b481110090705d4048400c140d2801e40340c09490310041810006402c07810403041c1c1451492080c070540340044c1c071702c40041c8a034001d40c2a2a0a442c1411303100c040e450841d56890380026880080e039039040016503164010001030360000c1c020201d0f8402e4680c0031440442c000c041c10003a40c2c000901c0450142da4010074842d418001444c42d1714148594101448280c200340511442001c0800300010f00c0ca503c9000c80f0b0030b541855002c0c40071464200c00a0140f5220703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 508816699 1250 508815449 508815451
    0x1a16020705040c02010f0516020f011e0c0219060c09090b100806011103041701050723070f0515060f04140a0914151015020a1407050d03030207050105100e 68
    0x8440001c0c007076016074004da0140a80c4120341c003c151070700303081044544000c0c020510b10a0541c0c2124002c80200001c54201c1d150500b480859181015003c1c3e855103080e00924015001841681c448a8075003540c6018072291010417102d26440d84201e100c610707401000300c401848070315014020642c402e00400c0100341a81307104c0c802c10220500295403640110000c0300442c000d0303011240c0c2e46989012180c50310300f000c40345071103e508240108014130b101e003d401c0645540b0f40022030719052b01d185c000d0242d9110001c2100c065040d4400f0402291091000d18095100d0703114031461440d03d1010414821641c0c0d6a25201e203192044200c000407020b83d94950003040d07050300140c02d00681c02c01d41040244140700880328440c03441c1e000000c40c01c0c030990b230f0300032540c1c11340b0002040d40712007118002c00300e140e060000690050310384002140c4d0b582124020003a4040c01d5801464841c404513150b00e041d4a1305801090300040c000c1c04003c401d00c50168058031306103401480303e08141f0820344543c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 508817949 1250 508816699 508816709
    0xa080f0106051902011107080c070b070206030a0e0a060606110601062a02040605040507180f12080a0c0507080f0f010b01090b0a050c070f15080103080f0c0c030a1a160207 75
    0x281c6520f0030050603000358825109105485645034030354407030703181c0a41c1652112418203540e00903a00000b03801c5580005480b141a802404c4a08542d50b01d10900300078100501403015920401d1075103004142c0c5407281d60054031840da034080511803c414100d1422070107902c40c00030848a02d07550b20301a00740c01c0d41c0e82d000d0009940000d28081150001602402e04c0d60040c80d4003070f240c0400d0121413a0840d06600f410071900100700070082c0d0300e90000f0b00c412041d102d803003094943c98605100107032514005003c4035646040c001e5480c035541c0c80c0c132440c0802d03075040340300603034802d007605188100c08000500300428010000e119000c0c2d80700000345210480e00c43c90312408804203151000501072000d645901da4508101c4a200e580e6880d084e4221106d48500c0920030300704028464003e100d40030050599401c6003080d40f51501c03007034000d03120b64041c0c084d03840326010f000724220b01d543d400d02c250b024241c000c0343c00004694040c0c2d4181c4034450094400980211565400f1b50843e4000ca042c03411a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 508819199 1250 508817949 508817977
    0x311120a03020c0f0604050a15020609070807150c0c08060106020c19050108090a120c02011413140d02041b020607020f070303030504060204052e0905010e040f140a020a080f010605 79
    0x3103440403452601594100641c0701028000109e122103070404203240c040c20a50031290740e51075002025031240e25902403201c1036000260203221542070700304031560365030b040e00e04001c865189441d40c02d0440343c0d5810180880d00048010803c9990410000c5045803049640103030340e6541c00840418000d03944074860601125100042c40010240210300b28950480c82900d0700c24034407040145400346040e012404034403010100080350303910350241c440b1132650f0064150300c941050f807815000c022054000c0c0d4045200075124005072100d000c2c0341c12000c4895078941c1c04402e1440040d082070030080040b0215030000e00350414040700061560116601743c10005031a45650821002038403c2e030308003541100300424401e81c441c90701d8540340a641403111400c41c420300782081c121101401e0f803007241e00140f001a04c40d8018a0240e101c03011003a40b00000043c082d10031403144921040803a102c100d0709602107a01c4c0b00351604080d643d503106484442d80d0f21998140b084c043c02901415032410410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 508820449 1250 508819199 508819219
    0x1060906050d151103100302011b0308061203042115020c07030f030203072003160503070603020d02071205070506060306070c0305030432012403030f02070b040311120a03020c 77
    0x100e80c0592004400d9041c80d45045d45e245091600c411001c0e040344012800039195040411092a400300700e01c401d947d2503595020b481d01e54900304180781212a0b0038081b2800b08100000d07191100080c03000c030000207002102c0400f003150410302c1c0000f16074030b12a4281c6004001c0011b590b0404904001500c1d40701d4036400d850240313402c0423490f602580c80009d1032141d00703407605aa20240740c2c10002e5201c00071412611107aa2458503020032041c0762143d550150310079142400310502a4004c0c080d21244c1410050800d5030341c1c1c0b1800910110f40c1007002c04a00002240002e03c00d0038020700e0b500c280c09500a000c54180701d00010080218003c003e0208800880803908215054010741c0d940c03004040d0304d03008210000d05040501504028800c2150304c0d103078544c2020144100f80c110044040b15200d002185540c406440a09440c034002003103001d04400840c40107d510081d201070f500915506010060040034000e1145034180410307070310b61106100c41d0001794001071040c1742500684814a007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 508821699 1250 508820449 508820483
    0x7050322080304140909011b0c020103091a04120f0203040303055a040308033301080a05040f11010c06021c112115041d01060906050d 59
    0x8244019041880349000006002613144510100d05000c070008071814a05906c1e80b110b401d00300c030010540c4118031440036501c40000c6020718481d200a50060402050b265204c5c0d0b6664051454105101c02c110000b506000510801c5482d0200f521f416080c2500c0c48031115001175500d02407484010300f00100001ca10b454000104000790b9510a041c21410503107103003014100e0054058010070b03071b400e500a48400d0301e0411691010117125141032056103054210340f03c104084d440108641c040a000b85048205648501490240d41030010760221840c07980e08001000d00c94042c00d40c0c2081070a10041c0004119020146e9114960003212030b41c00c03406180050310301551000c00680590310100310031551f801303403100f5a40e0000209808006408015000c42d081d40500d40d61800d1a4007081c03050441001001c403601d4004808580d0001140c285500240948080a070010520342c8803540314144003109000302c001408100c130307040c00319508180115007207040003000503001c80d80000b941c0310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 508822949 1250 508821699 508821757
    0x80313020f1c0308150105090d0c170a0b010e061c060b06070804050a0902120a0b0f10110105010e15150d06080a0b361608010e010e03070503 62
    0x40044006007000c42ca02d81d007044501e600a44444007a03012600010010b04002d4001316041c2c5c070180140c64807401e00ca00d800900c83d184190380f004541c41660140b0101b40c1304e00000f62040b16003211001000369038010710340000d174002c1c13b0344280840d03020581406460b64034000c0041d0f1340c840502000040303e40c2130428002405401c80b255411200001d100401e02400030010f00981d001903800901e02030340d40380d4000481c803884801c81c06091200d0302290820f41e0541000062103401800407907540650030014030401180c020440110721101c01c01c8408bc002806651b00500d0054140d100501d41007410003017440114210511400540381c145242c0d000d08016602c0c00070740c106d030822405482d007010580d10024008151040110702c00000e0100b68400d03102150802145000030440e0741c039018072190940c460640349124003492650000d45140801c00381c00500c00c0320004207482c0d4000301c0300760031520f107074506541d5500204150387c0482e00020442d00800080c084440106565012004d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 508824199 1250 508822949 508822969
    0x6091a1b1213170a09030203010b060909180c13050a0e0a0b06010f0210020a05130801181101050910080a110412140f010603050102041d090709050606250512030408031302 75
    0xc600d5080030904d040c1059101541c0c20959200707800030019000303600108440e07030040004c61540103440c800000c03a00c1c106c0d0011120b00481d60380403a41000300c0040040c2003124405000202e00d65941c0410403416980c0c0249a00070100788080c1041e2055500c03282c01d91100141001d0500c150349110550280c806c02510039030200c5448215110f007540d010081c03003030340807440000c0d90600541022031b03d1041880345200a140303010b40810103060301d80ea5003001c03040b14100b450521030240010605926401c1d00d000001d106990340c145c0034544080108100c401c00225258000c20602003440500c4205610300c0b11503410501d106003840100c5045481c0c8003a8402030b5041e542860b40000400c40b054002e00b003900c1075200b041c50075115406a904031040102d415540980c03280c0c104001e60160765200c81d42005028212524142c00b56008403c044100b41201c810100011051b000b03001c020320a05a00d685050340c00f91450415440d180308500014045150a19044407403c0456464088203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 508825449 1250 508824199 508824233
    0xc0c03070c03120306060203040f151b0c0f060c05030906030a06080a0b1b09030307060509071a030a0c050316111c05030a0f0c05040b0706091a1b1213 66
    0x602850364480c0780001d040a00807081001103814144c01082d02c0d4004401c0d14260ac5104c40c42001d014642190140782100d031a11a00078003224100c2603100060480f801a507042c061030701c60720402e03e003413100040381009034821070030002e00680348000a07030f020084a00200c412920710340c40b5200c0d844210000c004d00d0748126001c0c440d408041080000741814948180e141c80c148031407110b1003070345441451140988030350f89600104520b100148030340c0d0016400030320800454900310349030b01c00c0708140481c41482c2c0408503804010010002010f00422030600081d143c00d0f4151f0401100308616940456121401d0050001002400d4101088030801e60240c00303c004042490042000c1c003158001d6840c198a1401e00391080c84560b02406085012020340e0703140c0385007500d440c800c1251030b00312480c21580c0c5a1200245004102c8890704900b51400b15503140b0100c2c1000c1c0e035120102220743e103641c0050041404007007080c0c505802150392140035240450f01c0d00000345052004032101c0020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 508826699 1250 508825449 508825463
    0x14041a090a2c01090b0f060d0b030105131103030f040b0c030904091109180601060e0118030501060612110d090311070f060905060f03060609030a0b070e270c0c0307 72
    0x4402c000c29076a0300c810000c4804001c265040e622200c481d016104c62101080d0400e49941359621a810150001c140c541988840003908400300d0380000d09460041d2070071803440d280c030f034006410300c010a01c049015480c00c4000358500308144e00c400740c1e1070240344549401c1c80c10120340904818070078001c80312800c900030000c2080217481c0c42c11108444080064a0007400488001021444945504500c046074000103080382e80c80d100701100d91003181c3c14041e04200e40412041e152010411900d00a50300c600008521903051000084c01400c2d120306180e201030070710101220790743c1800e0481e13940d0040c0100104a07003415050654917803100c00d0b0f00c0200ca21481c4800913020b002c0850b5841500c180d5500c2c414003580c3e43c0e0401c41e00b8050840030040ea04810404908180780c040000d040040d0058255071041c4110f4941c0c1259080407034030b000c041407407211414801e2400700c0c1d061840c0916250080004145001000b5007030b08001c001c0e0991280009003400b98400030001c0d180d01e5540256 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 508827949 1250 508826699 508826729
    0x109091104090c0f020606040e160e04060b060304080a0302180910030b060f0a0510140307050d0b0d030c0201080712090c0509090f06070e01170c0a14041a090a 70
    0x1401129038070500c40c02e5000d61914a03c6070300c10340304200f82d101400103540100000c5c1c581d4010000140072402442c1c40b0b40c0b05000c10880c0702c412120411004010105403041c441c6420705203402503a141200152003004c0400400c40000c83c0b98082d50140d0b1514500107032111206881d80074420080700000ea44103a01008101e00d04c40c1c860000c2050724070445284115481782001d0081500c68010001d030b000c41582d9051086003000d0741940b07200580c1e460700a0008840e01c0f180085d547c000e84500c0002a000600041c1201c0c40d4012242000d0095442940a1070552001803807044030210080c10003100c100825582403254582ca50b80d074000c40e00c01c1084e90360764500b030400200343c0d10070b140c0100d95100010352003032000f01d80c80f0400c01902024016965410100300c4800728440c40b041e05001c0625100038101d482844024896007a40b07024950b07450098801610800500010504108080209011040d0028502048800300d40705090301c8001000000c0c101c803810350080d09c24448441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 508829199 1250 508827949 508827971
    0x70311070e0114040b0402090f040b0d120815010c0804290c071d3105060406061d090d05070323090a0902070201140304061517070b130311010909 64
    0xb40046002003c110780c200504e528040074801603000300250194010189411081d4504080c0c000c0702d4121001042c40090b0f648070398901c00825581c1d503002c00054504010411000715410440724070341c109082280010000da40c8011561046000d1680510346500100400000300407441a48180c54409075454203507031500e00b69921264403801240d121203128400820304107a42c203900400220020001490502c483c102c48460081e42401c601001c40140001064060082d00d0003584521008142d0b10301d0050800407001c1000382126040c000c21050042d0094002412a02802241484c41d240d910a0400f0750303040c00c0716580d0350089145410a0006204040300412220004555614002d0f2300c3e90044e5049008041000340814220005440401020409141c0c41803003900702145002031064400c04440300c603400721038480d503034031030070341c0995024484880a0715103241680c0c02e005d503517058003564001500c405041c6201c9584480020791080000c440a8031440800340f000341203003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 508830449 1250 508829199 508829219
    0xa030c0e0307230613030f1b0906050a0e0601090e061503010306060501030c053603030a0c110f03150601050705060f0415050424021b1b0a0803070311070e01 69
    0x991900c100c051410b000e011503141c01d02c10385e030001c02050079030080b16081d541d0b45825914042800d4940781082080700c01007070021410705024200c420000f0840301d15000c1071100880c440e8010140b01085042000007a9920888810480e8202000c00c0e8041d01c0304004507940b0300c28441d21008481f4000008414094503030000012604280e81c20003510751101021155801803400c00036124010442c6820b4401c4000e00903042030300148a441d403000e41c00b00010f451a40a18103100108201e100c20400784140c0d202e4048100c4000d0740c10300d0301500c004000903143d869503110960340003007000104005034458000d4411584d400703030407268941408803481c1d000c8841120121200b00c1e001002c1d00c00d1400b035019031402250300c0043d844402d0821481c050b450031984060302c0c180d42d800c0c001d203901c0028001500085102000141c41d03e01e10111141001c0580b0900c11340c0103002d140d904114241000080303503550b82c0c062400c0c070b04240d950000542088059030000581c0300344640085209214 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 508831699 1250 508830449 508830479
    0x3030f18110102070305060c0307090b040e0403030f151208250b06011715010c05070914010b040e0103080a052a102d020403060f0b100201060b0a030c0e0307 69
    0x1c010340e40061110000480c1c2c1ca00080c0801002c640101c40492804a0004003543d005002401c25201c1c132501c1e10510b000d02c0d00030303900600e4610248002e01c42415014032541603001c500b000b051000d84007140711a03030070541c50300c105503075030600c208000148101c42c0252401091200441030706028009214041040300c0e820682d40301c802c1c1801b08a0300e40c025402842006d0f12620760940c240e0741d14407075014a41c411102075040c000e0b050030b02c600003501400407038064a03240c0700000b40700c2c10105122820010581204011050400007403200b250f14241490440e0b030f120b84002d6440000e080101c82c1c50003007480d0482a1406000701051003012844000382070b19030501101e0138101c04203d6102a5107407441d00900030940d003245c0d0036560303004070041c4900c254020340c007514003642d9030399141c22107000c000c1d1566042d0b590112103002c0d280956843c0c5a01e082032000740010b5003428503500a1b48100d04441c804c0c1603803903c03075402950044140003428200181038500f810385d00c0c0000041003030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 508832949 1250 508831699 508831703
    0x501020f010c081b070f200d08070b040f0f050105160509330d06050f0a03030905060918040b0906060d0f120207230a0b041d0403030f18 60
    0x40500a0300328480511600d812000990f80703e0009489441d1200502071120344010712404003040104c020a1140c003150b00c40b0386c0300d0300840d0344003011102c980c65030f4070340004120700c200003460030080490921001e43d0b00c078030340000310f400c2107403182d181c03100c6d419285200090406880b42c030900240401036001a01c04d541d180800d03210722038103240132a4180710349100d07560700c2080382e4521800d403641c2c801102000c0340081d9420000d0354165100d580c5a400007200001e039203458190174851030a1010a08a10203401e1b5000140c00e030465038080e100c0c10342c41c013440d40294004a12240e4039524035610303500350641c0348040c004034103282c10120089c881c00c131a240e08502c641c002003080c030f00382801031800c8260045240c5054245560303504e002d03a9a64402001180709445001c0b40884403200030904400d2090300900130081200d040c4844869198881260000103200030006042c403450302c0c2c0541d00c40c0703401001e130b29511890164000c1c9280314080c00d080d483c220361450098130203811020518 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 508834199 1250 508832949 508832953
    0x90204050106050c03190e06160c0f06020d0807020a08030106020606040605090910020702060712050a03060e011203050d0f0606030902120604050a0b040620041d01050f06090d0804080106050102 85
    0x1030780b105801d46240c40386000c01d00f550b9000700300344099140303010003030903c1c2005403402807204c025190009100d500405001b081400d440c60f642401c00c44111a52802442c0c3c100c0034031865442c181020752143c2001d4460700034401c5540001300741c50b04c00d001010950394090300c00307a09c07561103107002981c40070115242030042d0301c0c1407404030305843c10240c40d61151654000400b030010315803030f01d0400f039008048200c0c4c00c600144601000500c148800410746109990b4a81e19504181c0d001416103882d41e1140c552060801d0044c0b00b10051840e40070031103901402c0c45075030f401c4482500b400920100c0300c1030260914006000c43d4440c1d1681144000a00840e542e0008648070000f0a031185800da400501a41c490101b440004600c11206680103001d90300004102c2e1040400016041d07081d107000e02818000981440700c0306490620000c140c0841508801c0c56040c400401c1c60080002c0400b4410b41000c60082d61940d280042c11007810742c0622180d40740d50b500c0300100d018000c5402028094 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 508835449 1250 508834199 508834201
    0x40605180a050c101101050f0708070c0b060d150509240108072c040f150b010e09190f1d12030c0d0204170f0c031207231009020405 58
    0x8940c00034907425039a0304500981803640520040103440303241d08010310144040070141420a000078030a8a202d403901c0d100304185450441e034000d1805030010805010b001d0489282d20100744007035078917a4860401d44085040014034180070b540351420301540c0110310700b004e080002c840b1000c1403485628001740a203136241c058140d00e00d020000c0034041c1c2a03480c1d222000030041d691500b000c22501039035040202250390411440d000c00088122401d0392b0015480d8402da0412680308000640074110380020004810541d000815801c0b00316040b502c5042c0480c041803419075520002da02d001c1c0d5010040207184e03151219503015114140c407054161500d84000211150003045600300c030142407511614640d03a2103415451b64221044010803154280b1011401400b1502001e00349003000c0000c001040442001c03074980302181d44014029004070b0511210f40b0201000d4a07546648040d268100c11008903100c1c0c5045a040412952481422010810320034141d101c1980c0c14000da07400d100e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 508836699 1250 508835449 508835491
    0x8060108070b0306150f040806010f0f0e04030804050f010c0206040605070e1c050102040905070c021f12020c2401080c040501050a14030c0613051f050a14040509040605 74
    0xa80303809102c0d1001c003140420014403246040b040c3d0b80d00c1d010b40e00240c2400c0141410b1264110b80054002e202542d0105006110100d48e4502003001400f044141061460500840707151401c0301030401000c0c001d4500215040010074407603440c24007030f608000c110002c02c400000350346900540301030301c1c0d592034800032a11083c4182d0350741d0915140a00210600e09170720700b040d107180000800640e0955070a00000c03440011501a10380a61242d95800f01c00350264010020360144060559005186641031501025001020441408400c4600684800c2d00300c08960800503030b50843c3c0823003e000310b005102c1014030480d0606884c40e0104407991030442209100c00ca80b1300b0300405a201d000603a082015100e0481203c561503401760584422940e201c01203403071034000e03205421031301c2c03409501030046080c20442240361000300d0200c0c2c1c1c01d03244803110240a030b00c2000c150000b005204c400c550429100c2400b10b5008202c050f05040c080c0c40c0038201240200010b50b4041800104a504192 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 508837949 1250 508836699 508836703
    0x31c03050609130f050715200703020a12020a05030607030e0d0311341214120c0702030307080a0504050909060601021f0e1605011b11010c11130608060108 68
    0x101c80c516a9201c1c1c4149440c1d61101303240d548a0040441d41c0b8030850202064547c2c441042c4514080c071519144c0780c0984102074940c400c0a400c0c29000c140e4000d080400160352402c200000301c40e4841c00d03c0001c50b0250004c41c3c02c45102c3c0d08820f4051140c4030a001109a142d804410180080402e0b01d41c030baa407002c0f084041d0360b124142c810468030284858100d07126600c403541290f42480c01030034000d4004081d42000401121001d0350f0103484014881d030020b4120810f011800130421180b0300c0c00b05c0e442807400182c4006812014440f40101d003460031510104126660641c00000c4503480360054140107140da031140c0a43c5001701c9039000492602c144c0064182c1c007400058024150308100c002007541c400804e442580315041c1c85604829035440300b401014000034040c2031801601341460005040507004005c00c40955156810301008038200c44800c582058003407a2010b00352910342031000d550504585a26402801074416002c00301d9a41c2c4030608803410081500c10680e6070b107016035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 508839199 1250 508837949 508837951
    0xd110304030806130b0405150a080c0904122105060a0603060602060f060418030804060b0604050a060c0302100e0c01090603020a0c02090606040b0f04092009010309030e031c03050609 80
    0x5020800c000007103989440c001c10039040d5102040000607048600b07100140a40380d00b9100d149000301f1944003a422809d20000d214050022174006120203c15027000c14249500100040d006403000e82d0940c044510958141040c080100f0030050b81000c05541d1030f004160070380d2820f02c282100080020614003170700490701141d910f6000b03401c46a480500801c44100c0042481e03a2040d9601c404a038286d10448000d501c96010744c0d202000ca1030185400c0c02200c5940160512440c1d0901c000c004c41d81c0e60b94088019100c031883c1111a64a4a180907072030241c440c03044c17075503407800c03c03640140c2207000080c2580b0f24102644d807288002d555400980403031141032003200c000381c1090151005070804025864005401030007032840d055858810708081c0d0440400c20ba08124005410004c0c40150f00500f800c64408452942d203036003010040302c415102d201385140c1810f446411100c245401001d0f000303d004000340035140b00311651680808041320350b0044a001c245007070045034a90418000703007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 508840449 1250 508839199 508839203
    0x90c0c011e1a100c0f1e02040b090c1902010e0a0f0203010b010c03140a09050d0620121b0d1406100302071505060607050d020c0a090c0206010b1804110d110304 70
    0x150940d40f4441d804480342d05151000792400700c140d101010024403450512144021860302c2e400c180000b92040000703513410500484e00c108419803d10507403036001c20880d481c0d6641e1151b80344070100d0346141139002d0145156107002c1800744c4a01d07a000c1c030042e108014078692013180200200c5200c0e20040d02c4440131044042e00140321030740341c00061207141000b84a144882c0c20b004101030b546000240d40b01030700c40402c40d0303110b448404520345051000003c0e034070000060100c5003050990146c04481c604014803100c111201d62015000004a000072200f420f0801e0006001161040343c603001141c00503190036001d200c40443c602c580754801d10a07225074a82c440e210381c0320b25182c1e0003083d0140c14058005503100780100080d50018104003c01d001181c52a0060030000c1c24840c2085003045850344100d05950901c1c0e218000c2039030200c0c426064a0311481440d03150a1840c00c6a4040d07803400b407126400c14a015040508850440c0207441c680d8205903050081c05604400340886010035240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 508841699 1250 508840449 508840459
    0x1009141009020c030403061805070f031113140f0f0601020a0f020d0302150411150309100509072313020a0909020304170424020f0c090c0c011e1a 64
    0x30500816029400600761582d034002124206a1661145011942e100f0039041e0b2881c07440a80008004040c00f06900901000503080d00d45451607c42c040044c04079240e1601c0f230b496501010f002002903070f210013141c1c1c1c00758050114034904048820002c8109981c15007103001d401c00040c4a6610004103990040e41c090132650301c140f895402d000310780c3e245502c11010f60142613032a080f503040d80140f0910490040b0aa411381c1d0200d8010710803503050107000078000b07940400401107002c0d000100701d801d6030140c4000081e1076039061200703800c2100e03a13002050b04221288503561400200c60008115075000c8a400d10410781050380481248100680d04010501c4214200062901070380035680c00390241e024030032110740400030404640d00681100b84000408505d80106005003240480703041c00500080c0b64404501d165203075a058960230051013114088000b40c02c00213204c050300c000822040003401207114440c3c2104494003010003060b8803e01e80b20050100a4401e1680002c0301c1300549 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 508842949 1250 508841699 508841731
    0x20705150c0f1b0a1a1b0301150c0b0a0c080c0412080c0a020402161a1b0913020a03091703160c0302030c0d0906090902030f060111070e100914 63
    0x242d14001e034010258005814402a60b20f114501c024825404403e1007501032981110802d071504808900c0909101c205406d0080c600c10340e14040002c41c0d0654601c0c1840061020f001c9030111440000d0400043c50215800c0a00c44c0c032150a4001e0303040000d29884032002c950740e40b0540385550096215039601401e450141c036001c1250700000f000d0803032107442521510141600410f090740e00150f080c0140c1a20002204140810556160014486403d20208a080c001d080c20300822110300e10f070102020004046d0210758500505100108815000b9920754400c80c81c054003d0000c80f00c03e554803038080403a203503209480340807240b00e1540400e900c0020380d56403501300c0b003e00c103400c0c04600f540300070072223250b1014040040c0c881442c02a940c1114807420000d00400d4000707258041d102050050007400010140c0c41c10550b8000e80c2071900019407080421141d18242096007c000c3d036000c0d540900c0905032400c11a0400e444000070244018120482039405a84046903e402c010945c85 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 508844199 1250 508842949 508842967
    0xc1a070f03030c02070e0106020303041103060702070b03060f040905100e150a110702060d0b0a060f09150c02100503040506060d030c1b0f090b040e1c050f040f0801020705150c 77
    0x1a0140003082090301c100c1c0c4401d900c1d1b0300c0c0c4802400080e0006005684084100030400c1011083c910302c5034001c0c0d0241c03040d07003002d42000c1d54403484c0b4011001111008000510180c0b1070409140704100010700c140502c083d075044c820b898901002c03620700e903142440c81e031904041d40000c20402c1e0085100c0f0b441d04580d9a11100c00081071101d4124244900402c41c070000b59840802420100c0460200007501070049070402070340b0070f07443d400175042c0409050300322000d5400c0360003081102c01c1c0e08542074010300d000c202100d04203002c50707000b5070240011442c00c40003036010015610441c414802c42c3d28540302c0c0e078100100741100c054010000780e061600e500010b224100e010321042000480c4082c2c05d80c0300c41c0b0044020100741c02c80081341c1d640310075206051800340114031807251254007520710300d85903a95045d103a040945400062200008440046244040071900184845441038203c992541e450501039803240b80b0540b1244a600d400c0800905141a15400394903029a1249400400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 508845449 1250 508844199 508844201
    0x50d0602030702010b04111206030f030a0509040b0a06020304091401180b01031d0d0e191a091009090b0f01050406030e03090904051606020c0a0b250c1a070f0303 71
    0x41c50b000440d502d0703031150390450b00d407030145c0740401c0e4846e4410b5031198800000818110b1004100741d2013640f120f50011031081010049411884880c94203940d29909400824068282507a805d5007052444d000091021750200180c0140c40d61000300740081c4100010301041d00b403003801100100c001c1000340b07500c1c2c4074082d03211400034801810301007080011014404000308144100c031586800411002d49481c3c0e000f201c165020004a03604001c0490500c1815050b00650207a040e03149482c00079036200352100415111854401801b80b80c44002c9058006c0603c6010312030f1210b030138140718540d550f62a00600030414148103946450815180c04c0c011406420603980d05d26041c0010031514400b606d9060b141031285024000400620860700501d5510640e10707407040f030440d044402080d20f19035420f500082128980c0c001c0584900c08070051001002c1c06031541e20001d0080b40110040224003140e010031a110b942002ca21b48400c0d0000c40e0300c92003a11001000b400390282075800080c02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 508846699 1250 508845449 508845451
    0x219020102330c092d0108090f03041d15011418030a0501020406080c0a0c020f150a030906060b0a2a0503040e16030b181801111201050a050d060203 65
    0x20584540c030384a4550301d01c03029481400c3d9400149100005001d19240c1408420714001c0462500d12201407030b100340d0074000c180e207440381c1c8030304000000c1c001c540007500422403006510200c005403a6515503818445030300ca000300e2a81d03241d040b103000000e03000300403801d1003041c0e826060b1a10394449001441d030302140e500003008040500401800146a500c04100341000d031031145000680d46c0e8149900030749080d20007402030950803020403907010039035444003111206550544801040c2082c810014000c030b40344a03101e0800f880041a00d400781a4907410038800180618070400000d80c4642c03019000c1d104001c19803020540c4a079405218280850465000500302d1689a02091840c1d803200e046601c5035120f044428031040c20f0009440e0b8407100d4040c50036050400300200c0400138085074502c030600d4005c2c482d00700520005169003804070441c021285448c0d000300f20798040c54018002c243c101e0643e001a6005c21000031485040440700fa00c189e610080c0a0346140c003941d5950b40c040d40c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 508847949 1250 508846699 508846753
    0x8091b0d1103030c1b0f09010f090b03030d0c1805060c07141c050601090608060708070f02070f06020f010608010212042301050403090315141306060e040b070219020102 74
    0x40100a40700e2404c4c07060154414074542955900f2402c51400d0030400301c0b00ca078800c1c0600c14100c40004005807282803850304211845504081041c02d02d840002c0c0c114024841c150724481d06080c41c40b032020b0b9008501006900400c50344094442e04c440901009000d6003c0980b40b991011805229000141c4051070000d44002c00c5890070b40802d011112110b464448101c47c1c6500c2580140058040b500500307024012510040c03049180143c0000d081c8900907240d002480700020200124034424081580a44a510300640507242ea83c10000e40c0c030010700022241c00d510380340e0003182c03942040c000c4984501c2c8500741504503031110707250a41505490308008004410501c0030340e000d0714007801040e11a80c0680c5440000c40c2c51800e0001c007611021100342c10461400d00c0101c0006103030000a42c0100310074101e010400403a14003400145510780001c440c19010b041000204800020007501c1a8025800d40342011590741c1020a0800c2d0100002e002d60400384c144002d0480d08888104002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 508849199 1250 508847949 508847953
    0x120e07061b08070302150a0c0210020d0b0901030c140102011a060c0a0c090f0c0f0c060e03070816030905030727062102010e10050d151508091b0d1103 66
    0x101d19a9900d540f036105142c1240540c0100e000ca903003a80030440040d41c0014081c809100701c1c51807080094541140c100c42c4081c05a01140c116501079940e03001d140a0035015010039603a5842c0d040c03c40c00c01019200d440714a65100720420305d075500c1030080070180c103003c00c22200c8125214003000745c55000900c00300224410151070b08003040602008a0062019031000200811050310705800e4800c9108950f0900c401003060600c05a072140c800310000c2e4201c1e40000c4e074a903202c0c01150661054a50141c1440800710b050007034607051801e52490756100707450b50302100e5510014141c4034034903841031b080064032104000d44148000c1c82c00301102c5214110008541e9201c51980c8001085101f03400780c2030001c007901c1411543c02104594514500701c5410315484001c0f10010400d106858034140e0158650801c620040b0b03009030180f0241101000d001140e02081c5001010708034101ea5100142c452a000a540410700b00304580030881c0213449000c02c580d80d6200e1302d0400ea001c2c104580c041c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 508850449 1250 508849199 508849247
    0x4020f0f1602090f07080709030503221502030414030106030804060804111005120c040b070206210414100603020f1c050d0f09080c06090904030504090f0b01120e0706 73
    0x180d507050f14951146103500c901004604044000820003000140440c05100d25510140041203001041c6c1d0404035050085940d820868004010310110680c88024080324610702480c2840d000b00c09082030300c0c16400c0d1301c4410305100d81018280d580d0341c480641900f00070001840341e14032403840b16034400d0040203c00144581c4a01040607078540510210008002140905001c851312070717400c0d049418580f11070705050601c0240c42c12846481c0c4003d00c102c40c0040c9100c82500c0000c404034428210407604441890582402031004825480d41280b50241d0005410028854401c031070640303070060640d09130001440144082c0d07103820401403001103d90030358030002076070410490303800c0455540c0e9540a91045035025218990360303000781c00c04c3c0d040107501590741e4440308240d401009040f2a10400c5884504056440303105079041049031908101380310074101429000000380c5902aa50016601c2c0c480910004690701324228a4031600592070400c81603224507080d81c040c040710020a1a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 508851699 1250 508850449 508850453
    0xc030f030e0709060e1302091501170a0c20030a0c1a070e010e030c0907050f0c01022b05040b0c0f0d02070606050a1203050d020310031208060f04020f0f16 68
    0x18041d2290f12520800c0e8585409018080f04501015005001e480310205c481c03010f0b43c001040c05c00018031070801c0c1c100c03510181d03d01d03030701c0b0741c50354807040b003207070b06c0421050801c113007120058220000034001142410080703c1022103d00ca14610b00d458020181d070801d440598201c4130f4a81503d0140d41c1c1d50000354440394840c034030156550148140d03031201000910b1b9803002500920a00000034882d07080710208019540f5403020082d44048589040c0da55801e1840c048980e6001d48000d6003095803001c140100ca0f202121520820700c10140c0b031502c1d8a004000900c400e45a0840d00140000710800220304030b442d10f04041d04520f81e074010b0003410100509002c0c0107e0b0003c603025500c00791250300400c201d04119040e4030142081041f040071450050300d020b0010f114690b41d00b0b0400b503001002903c400c400d080c001003c2d5134442c2d01c4500701980180c0c001d0031888240c440e03070b114400f1510f400782c0b40d1400d171084506c2c0100e28101d55003456081c20f441401c54108200102e10104442d1440c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 508852949 1250 508851699 508851703
    0x3010f1802220501030f020403020a0e04290106200a02010e0102010b060d05040c0e2404091e030f050a0f03050a02070b0c04090c08040b041e0204020c07050915010c030f030e 76
    0x56215a03988402a0900d4100014140d8a1b449a0742d500c4620410052025840d0300302240251800c4c00009200ea0f2100c0c605210706c1d507848007060341e0110030f00c9805905041500d45490407142c0035907541800f1550070366604041d070128108a5481c2e8040c0c400a801940565088025040140000161400480e01040165220381e03079100503256075400b004100181c42c80c41d8030283c064a443e010321031030b003c03484103400c000c5e80400c0c6484d040c40080288980e40c0303a41143e4a03850f03101e0080c40c081c085400c05070070404003892044012030107600c0c80d000300030310071800e551403000c4540c2d07104510041031600f42c0040c00003512442103141c0800c20540820400181c140c055001d400100390b807180341c01d0b420000c0351500414401007061034000e00c00495240b81d043c0380c000c1d4000000900c030b1094041c0c00d441e00c07100d095000350068000b0940c0440e4000101c4c81c4022140305a1710504280d0b1202845c0c2203269000b08a140461704440d5081c000c00c0c070800044041628a0400052040c118041c0078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 508854199 1250 508852949 508852987
    0x7080720060108070611030306010c0f050a0618110409030801061115040c0807060207030b0604050c070614010906060e090f09030d0e07090609020c0717010b1c051203010f1802 77
    0x100b0903030190504102172170340400d12045c6440440003443c214181880001c003440160031001c1c1100e08407810907803e02c4020f01590910940c001d45c01c0103ca00c5c2300e21070035116880790a054411440074414640b10b42407500800c5150b90b4155a070140b5603007080020b80d00407851b40403c2c5114420040d491048802c14071350705004d14040d41021603141d14200e0324615002c0f50350001c80464118003010400214400300d00c54111100712400301d09a6180f410b914610b008805000e01083d040504400c410004142d1942c10707207645100c18421540c0341c54050b14220b00a04015401903540303c000340c50034a2090203039411000d400c06403440c0224031181441038440d003950801d4aa0807400c4204007903807240c4910801429a45000d505041c1007c0c009900c40d480d40c45208400001d40606040c00c0c00d0a621606400d00000d00c042940001c100225662107444c0404032079611500310740840015102064034103d844103900c60004900f40200b589090101302c84400c801c54003807181200c070003e020122 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 508855449 1250 508854199 508854209
    0x71e091503021207080703060f110304060b040509030a12091410050a0f180b06060919090b2b02060706060311040f0b06180a1203080f0f070807200601 66
    0x3000085040d0b00400c03001401d88070543d811544120000c1100b000041012800c80380c000200147c001c86620310f8030003415640d680401c020200200300010000c16500161880000751800c003c1c45d07403140b030840d80c0d9109201500020400801b10146240002d40084103203501c18034441c000000f03d80d820358506500340019014143d11001007220580e0030b44590700110441c0102400b85030309a50641c2c03400d400c440406032499420000040d241c2d1121811078010410281c800d200e88001c0d40181c000f24a858016808918140340b00d0503040c1c03801e8010601550090403000303042003801a6408406454164201d801c0041444480007080b040d125040042d030254800034420200d2908000844000341092401c040c0792400c40c44a80e110b80007610170002c0184d102a8107401107a0005840e00703203a51054090017211a1010109640008000d00a052580c0031400e540c031541950f5131010004c4510740001054840085e50a0f03106c0c0d082103115058580034004041d07850a0101e04000e000d03049 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 508856699 1250 508855449 508855481
    0xf18140c060a081e06010903081e1318140c180d20090f070e0604080109110109060c110f121006080d1806030b120a0309030308090a0203071e09 63
    0xf004504401081c61301d00b0800070360321840c014988000040c0c5900e0740e07030201410046021030810b2a101c2c500d2207800c03ca03502200c8080e222a905c05100404400600481541d00f658800c000800011400391418403030700380f14900d00340e80e100751040f03034240c02075006600c2c0d0b1603081c600d8203801e0311001e4000d100c86003c0c04606102c281407441240801c1200200e45004011035010004090242c0c20142d030440c400e4505440d40751000c0c000200c29000c0da0300300a21551078800c2000c10411010300c248020403081e2600c9250503501c40050303c15683d82c0d0b602900070300307007039110324030519181182e1198010010120558400010706180c604260080780d0b0001d90755803502488030380310800c07040300705030680d14045400040c14842c4180c01e00e0380b44506014980c40d90a041040c0d5500902c0101c120b0010049a2a0038410305005003070902510054000c1903405012460030000845c00903109034001e00140312551800124603c4407000744205505000d0f44140480c3c42c0c241801598004003903061 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 508857949 1250 508856699 508856701
    0xd02070605070f0e1021020d1410050d080417100501120503180d0b041a0105101d011e03020301080c0603060a1502100c120f18140c060a08 61
    0x50003408403440604040c041c40304542160b0301140c0c0c00000720500400075146448050700303241c4259950711050590903032080c0354810528028034154060308060304120070038040412810030b5a40410300c251070301d40000650307441c10b1181c1c0c14425240150148680429031800e540c403241190540c003817904900c51504481e40c81e80301c0d0121400754501400f691000d441050f0115a54207950f840381c00300805d86080f01100d4101c00b542c5612041040b5904461010120319061500c00c00001d60740c811034010010b40070001c103143c200581d83c601034201c90380b929407159014202c000c4d14a113645000c0d42c10424184400108032126072441010414651405a101d50602c0c891904298100c04124003810081c010069a80e035140980d1007210400c842d04250003095090881c10074141504c822080e41c103001480409079808243e2442c1c2c602500d10821120161032010419140b2030401a80c0c00f9000311002400b140c0b0040700a200c0300c00c0c0340308a4680700300e0100403646a40190130b141e40880c06c040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 508859199 1250 508857949 508857953
    0xe1203130309080303190b0d14070e07080105060f13051c0201081b030106050711100e13050c0405010302130513060e0c0a0c03050c010b19180203010f1502120d0207 72
    0x1e6880c0b010b4480340001d5820f6103081c6000078242c2284d40180c00146844000ca8482515055000e154413600460030204181c0b1165201b95600307414442c0c110004175500002e1143e600c40c600c031605a0f4070003003241786810300340d403a24019034205a02d50004403c10039800101542d441a0440180d0080084201740022900000d0107941008100310001520210b0a420041d9170404403415a507071420290f45900b2070f8100f050800b51402e0400e600030740d140a0340441e0704e8100014000fa11011501040c2c40d042d10b5050383c007501c0091354940ba0501c8244001d20066019801031300c031820b0f8240c041c500599035803000a207030941406d4107050349903441e10244807846c4520a007560045141c28524035004c08030307200a01e0000341c010007034100321300072a416001032020340000070f91010060100900118006001b1213110051082700b03410010b40c2c84c0d80c41001294000c0c4c0c0c0c102c41806042210b00740c41c107503052084040e1955082c08500a4040540041c01d02030003510030150f007640010388581c014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 508860449 1250 508859199 508859207
    0x31407031b0615090e0c101b0501090b13030e0f0d05011d0c0109030503090d1e03020f0610141c051501050a090e060403030b03030f34050601090e12031303 68
    0x19045051311034180500c036494010001100f424000c3c05035182404001480c8049482c2c0f40708842c4d01124045040c445410300c0015000404200e000e1060300c0000c1c0c640b1044a1301c0e00b9090300000300480c090484001d490324000803011000c1c80050045000b00340c1656070a42103a203004519078002440b40e240c4a600d075400c1060aa40110a0a02030740f502d0a60312056507038041c41c50030600c2000310482c1e04040015030010041c48079100e001800e0240e10924010752521858070840a2074804e4100040e000c1c0c1041c81120100e440351032821030025150802c0c85045440d03c4607505101d40c900a50500140d0104100c52011040d1200e050082d41020b00b0804d4543d2241d0113a02c2c028100900c0f00206400425200d0b00103a050500180c000c00020100381580250000301080d03110105080d8070052164440d55907411b1603c0b50b00d1490322000034035000e07040d0074200103041540a0801406044190ba00c04980b60720681c00f00e80481520254003c160750007224042002e0550810400806400c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 508861699 1250 508860449 508860491
    0xf200d0f0b0c2704060b0d0507080f1e1f03030c1101030213060c0c03140102070b2a0a02150412080a0c02060705070204060b030408130b07031407031b06 67
    0x8030300b1680d01c0d00081081074040e038018a00140c580050a4000010035035139030b400040103280c1c0901403911950002819070041130116002c8001c00c1d0042d0010301d030000250705a500c104c0c06039002013240380c150a042c80149500070314450240b4400c400c003a40d805140c0540c1c0008610a03952705c82404040c5c40c0044c461900e804410381814018070600c00d010b910b070b03908101034604a15015000300040e00300321481082541c00a00801003000c110340b1000019002889400d005426090850b21421036804da4240c240101c000d90700c04110703071884941521802400006501d2040303c1c00c91181c55100780d00c1a109840441d0440741100c00210056000f00c0d00541c00072817814100559030041d400a0748940e07004003083d0821000094500456071079500c0034026155010005407645068a005039080d03112203001096002c0d00e00001175405092000c4030b40481c1d150b40c82c220500c903100d5491155420001003101481108000048148640700c82c07265141d005600208401810301081e1100300c0c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 508862949 1250 508861699 508861711
    0x21f020f060c040608150909010c0f0c08090105480114071202040305030301080a0203070503030f07021302040905270a050705121204120c0b0301030f200d0f0b 70
    0x80c0e00b00940d403286141510b04541140c00e00702d10a0741e03804400003040407030030000c95210f84020244000324005500c00750700c0402036282c00f40d105060307900c01d031211038003400000c141300c9003000460401c0d4403d2016109017070501e0300000c94000208601c00d00c60700d0088602c80244003010141c440203003000302c0404007001e01002007041c650704002c071540d800b000a001109010304109441800b00c00c0da4111801550000240d90312541c681e003c07241c403a2607842090340b080c8200d40340801c96150100850b8241782d030040b4070b02d00c1c0c80c1440c0d017800412890705452607071840d424040020110220300645109040a0b45401e503401c4036503428801045106100070300c030b9805003a104001400014000b0103980c021034056114420569040386804080b50303640c18200030118000a001c1000e0102084c80e070f20461200105336215001800c045c0000d200180c40700c4a81803181c00407480f5012401001d00c040e0100f240940e0b442000314841c1d100d44441150765180085070401132160b40d65240b60800c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 508864199 1250 508862949 508862953
    0x6070503131a0a0309051002280305010e010e151e090f01060912080915070311031e180603190608010204030f1b0f2606070207090207030903021f020f 66
    0x1442e6840705404030b00070000480300341507855080400784035042200441500744a42c0a44d070380c048440b118403c540e481e14007a000c40544001200d400e50003070103030a043e9444ca0015a07200d070320b8071806124107200a0080d031850120f0041d41400e030744485040354088414600d00038400c0c580b043c2400035041d0000c180101c1c448111005104d1139600c0030504003102d085161340c6031418401d040a100c01d1084078402c6920426411006050485400140952601a4076801903030082c81c0c249644905ca0f208000e5032442244d015014407400000251030001406040e07540c0354075901c800310307003c0e82c0152410a000610700d001c041d602c07029405420003500c140402941460300c0c0d80d071401855428600000d004048195815200c1800741d81040c0082c0400c158420109070b03240350101103100200d0440303980481e0409500e0098500180050040384590300a04285107041e640c60000d401c001c404508000420400001590306c0d010000e0000c400c0c0000f0322a0b0100c1841c000e0325101c0d010840b891a6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 508865449 1250 508864199 508864229
    0x50906061206060d110409030201090311070e04020108041b180f02040f03021203120423240901021e0d0c0215040b060409050307050105010303110705060708090109050607050313 78
    0x1c84010803071982200c03040c0d501d000442100d14080020b1030358211210b4200349401c00366414164150441e1034590f0198507400c8407542152840c0d900c0c1d9545002d806100d007603010100b80103500c9181910f42c403d0042c40001c44145c0c41e4105141c0390740a0f507000c0b03003040001b80c0d40d038540d41481b803241c4640c43c41c10580442c6003d151802005005845100c0617128004102c0030a810707070000d01c100d54002030780240484c01403510780b030f020407082d0400d2003170380d070071a5a6103840603c6103000070480c0c2e803c000c4000c0c0c452080c40603e110003409e01d000340001e030155000c1c46800e100e403850101303110702110f000070301c1d82d01c0320009800e48040758208404002151b120311400926411020b4280340c0243c3c04c1a000e1496a482c0400324010f4420650005c0c00f40c440090745205110044d4411816648a6500c1c80c1d241031612403029501d030351038010035a02607420000c030400180303903800130420058103050403420b041e5203000003440c540200500303407002c0e0000120130301450781c11203015010300485006170500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 508866699 1250 508865449 508865479
    0x3090606120d08060d02010e03120a03140601200f010903050910020304050a090b0d08030c120115170604090b01080a14010203040804051002070b19030b040b030a0b071103040905090606 81
    0x4507901c0a4012170040248004d10400d5902c55442408121070180890b100e0b49160300401e2030f550320107040d940c00245417200b13100612003a22070840c01450165500c00c0c6036103007042d03075403101d044001c51040b0038461540030f540e0f140d400380030305032266000c2d03140c00352504a003400780400e81c3c03141f801e07200440d0420003083c0055501c140c00f160541d61510b9000400382140d20219000071a0390001130685c50001c02008a00e0b100f080042114a00d034888080043e666010740c1200c2030705000c0d1403c00304043c851521650000544000d9025400400c0814400b41c2602c80e000c0407102a00000e40c15000300c031084d01445111100c2c0343d0304040c2c00000f1441d618054507152454011400f88a204070324110b42c48084610812418010346034042e0040e03070b203c0410240b200d01d81c054650540119080002c401b603a46090700c200d00405030041d02a111a03401d543c0c43d10414100240201c05204052440f5410041d00700043d03c007030b100106001070a8185100780c2860703e0001424a40310300819445400303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 508867949 1250 508866699 508866707
    0x3100905120309030c03040e01050f121905070b03010e0702061e070825020309011803020a03170408030c070f12020102100c09030206120403090b03040f0f080c0303090606120d 77
    0x42000d4001c110030340720307101d8200c42825403240b015429520300c40894041220300030440c86a040b1041164094617448240081c08000740c00400c400718160491617140c002d68400c40c0041c500c50340b00d030040e541142d8544000d41d0490300f0a0700f1030b54200c090242000001034040002c641c000840755002010988001c00008803d6401419081002903580104600f03130a1040340703400c0e00580300d12050300074201c910000e680e0b80000c0c1d51680001c0b144030240704070a80c2c1c24030320003e80350041c21107031005003540c403404920a51040c40031080e85082000042e404000d1002d0031139448400050b0440a00c1d0980c92902400160081580111140f5003400113030b0b00054582880301074150080f0300e090b0300c9901034540c400e85a001035000b64001980c0307140d040d18004e42901c903900c01d89a0b008016100c440460a034003084800814011101d10b4200101c0d1440c0441d814480c400d071800707413811100c40d04403070a40d04160303800b0095a020300144503080ca01101c1c0c800140174060024940d201103104024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 508869199 1250 508867949 508867963
    0x31404050c010c020105040819020411090d0809011b060b03010b04050c0306011112040f08070803030121111c110316210611030703050c040303140913110903100905 72
    0x707418032194000c510116405102030340c000f008014180c0c1c82ca400b1b0381c0841003192142600c220311a07450450800c1d080300428050319210780014009100f42401766481001c240d1101c81c056060108100603400840340c1c0080110b1741d541702d0540821845014010301d1b081d643c000b80d074603210780d050404116621080d8815a0317031006003440c02030341c0b56001a2180381014004403442c803600d580003030040341040c03010f40400d0498521208030340c0f8550342d950f00f940e22800207001d038000014040c4506440141c5c01014070100e603000340c407c2c001c015400e0b00081c00c00c015400c68054443c002102c42d800b808151403682c00c0110055002e40141c401151800e00e289010340682c921a483d61100040540e41240380d03010110b13403040d010490041004681001030700201c400800280c2004001000c0c56101c0c0280c03811a503045d12002d0b09a01d00480010503508004060b0b03801800c141820600002180a0420112011080560390304103d10900d030504681c0b00c6000d040d0b500342888100014000034040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 508870449 1250 508869199 508869223
    0x5150d02090a030204061e0509040f02010c06020408010518060a090809240a020c12030909010b030a2004080c0604081903050c07080d080f2e0909080301050103140405 73
    0x69030303a03481c4400034800030060340010b0341161811102180400c1c10100710000c41441c0c1d45d410f12819512010880b6080086070010140041c03089610015401100688040b03403292001504054581148a00b128011100d19a030743c0d07048401c4c0e01c64400d0034884070380c011100d480d00f8070041105460310981449180c2c0c50740d025488180700c240350018007150b401884109001b1750366440d124404020364401140d181c07244603800300020b001d200d00c2c00004036228120b0190110015a1804c400000030703030002002102c1036610751204401601c00c100440070080303c5003508544582c24030110500c0c140e00d401585008100400c402e2080620005859416555007450b00060000c070385400c486a0040d40751041e040c4c850400040f03841240442c882804d0780c2c00c0d0740d42042541e91500d00e034402c0e5600b80d0380701f60303941c40c0c0e000c034107442150402c01110f1050141c00210700886d9507034841400c5958001e001e96003900b000c070040c402d80da03050040c01004c038621342c0c020304281840c1d21143c0c1c8600c48202c0c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 508871699 1250 508870449 508870451
    0x21f0b090402060d1e061e030302060703091113240506040b070201021501090e0d031b180506040305060a0c02212b0504031827060807120c05150d 64
    0x140c1015001300340c1000300303910b24118101ca80d551158a840d405820340b400744002c400c0041c030520780e452100c0341c1380d80b0441e90594010000c580319458181c0003041001001c1c1c4080240646000725070700d0f0118030f410f00000c0d859001804004092244428200c0d05020b824030141241041119a542c0020352f0300392100d411002d0380e102060310040c0c0c903020504e594024001c110600000e403045503070303202040c0d00104031f09440c01e805103400202c003200c0c0402d02140707000454585180f00035104081c0491042d503013180210781551110000b600310341081d40119660342c04202082104c007940d01804450400c01c1c0010607480c2c510b080142c004c003501c00303c3c002c0381000208520074150568002c084040010860100075008140c1c01c0314041c2604032030540100304001000d800ca00f441725001011120b907400411382d04110f0810300c01608242c05c50618140d0345882010910701c00a001d0440240141d008036120350900343340c000348210203179000502c40c0314000c2004000441c0403040300c07200701e62640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 508872949 1250 508871699 508871707
    0xa0329100501030e1606170a0b1309020111010f0207030306081617010b040254030f1b1f0203030c0c0307050109032610050609130c021f0b09040206 65
    0x40d0795480c040d40d80d0010040c14505c68400034403da04211001281181810120403507900c806a1078180c60280780501d0b008150800940306403000c65008000841c814507200224504d020710150a41d42c1440c010b001943c2d000400404040c0c26100d9200180b106c400900001060404044007070f02c0a482514100c60040c60380041d00c4070298041d03042c011004008541301c05e00000700441d20004041108282140d50072001f8a9041d00201c0d0661801c83c410b444401d0310499500030541c0145a800e01e0b054410821101480b15050081c004500781116a4030701000b4034100700868102225284c40560007002212002c0c50b5001c000c80e6400403680b91031380c0e6901ca618040e2440c520038034a018080e540303026900401c05501043e850041c03400c00b080d00c900201c400547d2040c5d080140e900c046c054a00120420180c10188040d01810350300604602107103c084a149094854141c940c1c001a004032305240c548210121a08800302ea451404002d849414400704440c11800781000c1e220b0a0081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 508874199 1250 508872949 508872971
    0x2f0712050d1b051614010305160e030a06060e0f07050a0806041508060a0606020d031104090f1b020303010819020d030c05100c0e04241e050a032910050103 68
    0x1c2a0010741503010045942c1960b45000d544075540d01c5014000314400307605c6401510f0342c800c0c0240b6001d00c2400c0c0807032810040101381a50011074501005406004a40c8000c0100e12184905001480070400c5140c541c509203500940c1114010000c109001050044845032a40645601c1d4820303000d07980080c1c09a070820140c0c07034064480d440a0350b144181420050b03d5102a0040300841c7e4242d001c0b02d2000300e4020080c1c090301c2000c801c6000c001818001000850056004000c07400300d00280090100d050b4461610380d44081c07104400542e10000041040400c104803005c0c00c00f04200c54104c0002950780021104050641c2c040d04014105170120184101070003068a4002d64050400107160f00304405800f0341c0c40c00007a80d10540c50980b1a103020710010f43c2c0d2411503a5100c060301c5086040c64605408401e2400c69006011040382d800324060701d898220324040d600480c0003902104503032105000e0001c03150034801000c0f0040042c40742009a800406080d40c20034200800d0b000035030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 508875449 1250 508874199 508874237
    0x1214030403060f0f0b060a0507080912010c02060411040b0a060c021306420c06090209010f0905101412010906090305090a090c0c02060702012f0712050d 67
    0x29401c00307070030a450407801c2a080c0300d40713501807030400e01c00740400c0c0000c1140004000e514024201400b02043c01040444c00044800008180405005011114404035890300c5800c4400203000800076a110b131080c0014850740014580b51031100311401d0282d0b004000114074400e40718400c007824403244510440c2150f95544880c6420b406a0108000c00c5070384030140400000c107410030124400c000c40d481030745103502030440c4d45c64940c462510110161394070300880b200429248103803241c3c0c0c3e954004600507174490000c00d0081c1405101005600d00740b01d0004201d54024040c11015242034001b0420301001c074000c0c1d6075051044818070b0340940c000481a000d0b1800042c0145003e02c0e08284c1001c041d0450041c2010300030581d0300039005502c48009104854010060502040c42004420010b03d03100004040e41c0b481071401c19011140550a00305103203440030302211021015400140182c1c0400108004007158071144510780c000d6112a911607104103036807401c00042d601500d81c00240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 508876699 1250 508875449 508875457
    0x20306030a2f010203070f0b0403021504080310050418060203060a0e0f04030f170c0313051903030f020703050f0c0a120807020c0a03150510120303020403060f06121403 74
    0x800410514035008401c003001d030511030761024252520080b0181c01d520000c20360f03d420b0f600030001e08500c0c1c07030364071508244600204200c2c114420482e08103d000c52484103240035070303c030f10541612414400d407180780c802c40503000703180180e14260010404047d00184c500c0c43e2034120100580e686c803540c01144410070507420800700800703500184403e8480502c100c911890281d62016042e01d1042800c440101a040e8030120303004440000c5080300241034011350308030034000305041001590790350f003070702b0210300710841400c900c010500c000605415001d00c00b49040c603000114039025403603801030282d0160b8207609103058400325507000c601c0d604001c18141d42c0d4208140c820071800b00b1100070550201114414010b01891101002d68180f039410002525407120401d00c11344403002c4090020a4010082c14500a020f400040c2c1c1000302c00e100b0230032074000e903005a0b07640d045003801c0080c4e42111800d2184540781c420100411860020100b445a5100144000e0310800c0d40d85c82c0d1860003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 508877949 1250 508876699 508876703
    0x9060304121803050307150605060a0f0302160311070602030423030106030b0c070c231c02150c120a0219060605030102030f010306050714090609030118031106160c06020306030a 78
    0x60b04a00481402030010242800502c0754543d261010901c02c0e03120150350291240c1d641104060001d803007050300448a00600071054a801402e02e07807910500e40d440c01501c4400d4010441e00455500e051005100500240119000440c41e0626203902103c40c005890030220781180103c0c0810307400c1da020b4002c1c400464220071000341e24202007090410650140340100c0c0c1d8002075010020703400c0048100400c040e008c628152007040e00c7d640500540018803441440340043d01200f1000503070312079040310700303054450b5031441c0c40d80c808003045480c1114184c0940500780c03082c0085800d80740d00040345144000d00d5a80300c501c10240346400005400c035900f000e54154004800c016404140600c840d040324080d03c024809a01c4003541902c4480e100720400051350b00c100080314440c00d2030402030522080103000001d9050804800c0011030700c145004800281c0e5087c1b0580b0f409000300701c80c98105000441e50842102c444001803d61042454020511030700880040d50a40c0c0034089041352503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 508879199 1250 508877949 508877987
    0x161a0903060702011d01090c090f0b0a180e01021e1b0312060a060f0207060509030c04051503010b01090e060d2f01020610060903140705060a0f080105060906030412 72
    0x2082c44000640600410000350200b1005940d181e000e5001c1405181d9845070810f61440c0c90a05111400d070280034154040380c40326031100f09072012502c0d1800400300130545084a0814500705580c18400e441c45161140c000b13a0040c4501d2034408148880303000300c000f03000d607500c0c0c1c0e4401c40d4644c0900c00c409250000c0351400007040e02e2002e8401068154401e44040300d03080921901c1e40c4060300c091428101c0714005920408043c810540114000d0262590040460300d80524420020302074030003ca404c3c036910202d1480c18400e60800f4000c1501615003402d19210840c00c2c4101d0440c1d031107009000b00d10031301035038440c075040c0007100c1c0100b4580c190321241c407070030200380c186c105272510b9204101030300500c00e550000f84c6503c0d10103602c20a4400f181c0e0383c0450103207580c60b654000c441d4080c440d01140142c001c00102c959401d8010420700b800394481a68280c0c0c1d980d000351070b03800305a201f1809003800308000429603490038100c070b03030003a489081541c1803640c410084600c240729802e452148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 508880449 1250 508879199 508879201
    0x118050f150d1505100512070219061e020903121c0c0e01021c050414060d020a08160207060e01030203070e0303040b0c0115050a030321060e0109050603161a090306 72
    0x301110760026043c140ba1450041d640950310004e015400c50f8000180e00040c90a0001d40d5424029a440e00d410404030320455040c90a1203003c0d07504c84415000841e60150b03190388420300100013000c1c900004410513011400e0042540101b500c4220000507000c00d54400140c0151000c0c03512402a9002c40f00b001c1045030900022010b409550080d80c001d0245c031a90300b0914103496075000d054550031495940d24102840d0614007c484010b040080d61711000c1448442001c03d020701c0605040d0106035100b5186040c0b80c1d5266082d40031a030058000c5401c621301c14070050b038010200701d181c07407821b18006980755900d42c404c83e11032440303040e03c1d54503000c000740020340e0a500794050320313046042030000c200318044a072080f980b0302e01d41c2c810981c210340448001c00129000710b0440401c0303400f40110130414010314070340e00c0442c0c2403074021404031082040140700d103030031611030f255024009030024401401c0ca41d404000c5d28085105404246145540b40b149000545040d59003402c0060110703405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 508881699 1250 508880449 508880467
    0x170106030b010e0a230d0803090c19030b060112090b04030e010e030a0b061909020706060e0a0c2111120901150308040306110702030d0207080c0118050f15 68
    0x19000d112400750000f90714002098082c036107401008115100300306201ca2046a00554241e035402e01989035a01000c12160800482e082c5802588160b040e44003034403220340088200003101036000201141503c00700424000142403058180e0420400d0030009890740306921a000900a42803004200032130510902007016001046005003610903211a8242a02c1001345551100c01c4103002d0728140d01840401d2031800c054252200e0000d001c90b0700c81c801a1105001c0059030700c045c6048641d6680e46104001207071082e41c0c0c0f50741180c0b418000b480301c0b0101d000c00070451402b0b29031814084100700c030321980309007076940081600078240740c8042c0c659580040c0d00c1190041196011740c29400c00211400080700c1c01c1803038042e6907101da80d6038101821920351100070106801e00384010201080104003680d02002521548540b40d401030406900302090b05091004103191641031010001201d0406000d0b036140001b55042a5401e02c6c11001030400902503003103200c9103803440c1c0d03070000701291 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 508882949 1250 508881699 508881701
    0x4090903021011070b0f0405071a04080d0e031b030c0a03030e03071203170717090d021b030d03090204021b0a06110f0703030c0c0209070215090115050603040317010603 74
    0x74a014610081040403000686030a00e0702c2884801849010038400048150022482c0c15030083d0103282143c500a0f25030041c0720a01c8200a0040ad81d05c10104007040701a03000c000e607501d25440d51500740d10764050800425602c9030130032031442280000e20228110b6403401c0083c56030100c8001c2281d652513a40342030207001c1c403640248142c0203026110010a000345808000d0410310761582d50b06002e018800c0ca03800c00e440780640600e0130042990604050b1081c0011f07a00e00604514002d814a07032484000a450164240b07603050709020072444040c003a0780d02159500080f040c90402140d00309071740c40045d000b4800d00300401c0e00b040c0344081c0e084140a0018020420521800d1308100c0e500c104450754039207001e610401541c2d200200640c17000288242c01610180700c2a05005031508c41a5000400380442201c5002c0140e120300c00315001032562071201900a0242002003242480e100c00c0d20b4207050b558021503004e040000041020944140c0c049601c904402850200658480e14010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 508884199 1250 508882949 508882963
    0x10e0d0c03030f0501080a03050f070b0c090f0102070b031807050d140d0203121305030d09030f02070f050604090b0114070f0303111c0f1410032109050f060409090302 73
    0x340000f840c24101c11071a4455100f0b49058884082c02000428400c3e84e007100c090340030170f00308040d0110902040c8000703560344980d68000c041503210305860724185814080c9d03403030103850118115440684c2c1000b01802d0a0112504103540001145441000440b40c2d8900606940000e82000c1009460804e00604d00c0702c043d00e0010f4072056600f03081000740126964012050120055400d460103c0c0c0040c410501c9001554800d130240c03820101e50642110403030744420400d4010451080080420355810301a40000d40894010706503003e0401700030414074040ca0182c035201c266500d803080c1c260303070144250710940b03c02070108940d6909540360850f644400c1c0c1368100c0120742400401032801128038165001504044a10707500280e00c140c1d2640540a613440f240306865842e50000c80d40c0b510000160f100709207000300d81801520310700d0114425200f0301100c000c81ea03004120136417056071200e0003e0846004448031002d00b070326503000406034481e943c042565285008042010550041808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 508885449 1250 508884199 508884203
    0xf05040302091f0806071b020d0b040b0f01050409110d14070f091a03031912140609070206040803070c080d020403150b12190c050a080304090c051317010e0d0c 70
    0x12000a41e070313403072800d41d2088155181004554204940c0c02841c00e402d26145010340020030304c944061950300c809241020954090380d15000d0607080110b44125002040c1c018001500c1c200310f1020356444003002d015900c0380692040c4026080303c001d1211602d804401c10038040c05451113240e5a0804026214103840382c844d0541c102204400c6020343c0300f80840407a000034028614001c111810019000718420a50f418044080500b01c4514154030a00c01442c2a0044105c0c05003080c1c02004155107000305140308550200c3d003000b00080800041ea0742021040c180076a2060151800b862940249041400c010b403000c10000203001c844002c0e03c001420069007049240f0748078043c45000b20805d1100c0d480da90107581d01c0600085260000e00e50b0901500d5051544c035110000200940b20b80d50020005a102103800d200400c1d0fa40304400c0006c0c940d007402444e241c0740980c0d900c40c54403c0c1c17042c00742075000008124100a0290041c072180f584242c192108181c60041c0540041069102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 508886699 1250 508885449 508885501
    0x3120105150d020a09080d05090306090a0f080304080c150103260a1404150c03020d0302130302040b040e0105010807061106011d040f0803010e040b0f13030f0504030209 74
    0x2405041c0001e401c0c40070031003201c04501d00341d40355040d10007035841200140e04011025500041e58a828814042c0411240c3d40c0c0964420010080525000e0090541006500113503508030001d002c00300086c50740f592203502c0a840c0e550b10b08295034103010380c040c06080c5010b440140c01049862080c0303541602d1145421104201d551030503610426000c884400c0000340030080e4060a501441c0100998402d1b045e40034940340c3c8800080003d1003000790005d0106401281a4007010b030140014844412640303400c500f0021022401e801402142c0b1000e4080e130740d12400d00e03403107460719003044804a031460002e0000d541c0d1904d0311a40c80c40148a281e00040301840340b544880f00200c5c6542c100d6000f8640c960360070f4540d440c0040c034203401500845410342100c500070700040003100514028141c00348a81020b1500b4100b04000390310040c480340104800000b0041c03891010f0b500107480b540c15280c036410610001100352014440d40e00080c0d44407e82d5010401c444920400120b6000d4070000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 508887949 1250 508886699 508886701
    0x150306050c030f010e04050a0204200d0501060201060b031003200d0c0810020a1227060509013e04120b061519050703091d1803040f0e15030f0312 64
    0x40700715103c01560010001e0308101c50400c00740c92b1540040c1070701d0101d20b030801e03c01e9510118248541d40856800341510307841c1c00042200b6902845803800510540c0a0316181d440e105040c46542d541c9070000600c02648142c01c071220000035800c4000412028149022404480c10410b600703200030310461049201d0303000000ba0706101030003034510045603600c8040001810b10b00c01c2c405400c2c0d05d48d00148401a08207080c03ca61503442680b541c00d4000c0c80f002559080c0500f16a00751190f20400c1a042d00302c00d801d075074269000c6c4000c940f03220b00204982001086003005043d07548140e60020a101082400140902107030342d40f090b000b804115441c044500140e83c040706140921611101a000354010b100c0340300b80200028540184240742c00c542e1a600d03207500140c1046292003002a164040c410410518800340305510080e0810b4000c40c185483c00000c409552214000c01400b484400d0200c1c42c6036440240c4140011801000d07030708007043c4012503640e650040494480d00c602c041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 508889199 1250 508887949 508887959
    0x41104020d141f0b0906221508010320030703081908130f021c12032f090607030e04020c0a0c0f0b03060607020d061104091d030403020103150306050c030f01 69
    0xf41c8000e01d0750186140340030340391030803141c4207094000c00006030700814108040b40d810710520103d4008640b10901985040d4100410114084100309000060140b0a4014004213607403603220b504170707209100042c0c01014240007103400c0c54015400281440f202280d0b406001040314621000d4400903070711100107581d0341d000b900150500307030030281a000e03c0240000160401c40002c8500c401c507a00d005010352030903501c8800340450f002c086000a540c1c0d1840c0b24081120001208a508504020000451081d09108020b120300440e20f0320880313000480a0415004000d00066008020411900d96030781d0070350365440340c1801900f00c070440c00c07064002c00c414250040316010380d00050507182c256039411051095136886140c082c1d034014400809440004d0180c02820301c2d9000040c1555100c515105004090340c1c3c0503066964841c010307030840004100000152822213409103000310f0b400000c0c03400c0e058002215040a0502400d0504200d8031440d42c40c0118016070030418011083e80c0d0700c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 508890449 1250 508889199 508889221
    0xf0c0607020d0209060d21090b09090a0b151309060503030403050c010e010c02040f0606030507021b131b0f1202040b0a081906090b030601171203041104020d14 70
    0xc04000750701400200d0004091300704240d80c2c1e80d00001c06400481d40074800e84910020b01d6101d52900f0ba00210703100c540d110140d00c48203004c01081c000d0340c9541040d65a00c0081c001c40c00090050308010b640f901c5250302c994400f990051041c0d0880c00c40c5a480040d8024002000c41601800c160182010400507290900004850440f03401c5006048012042d01c01150881303412a0a00d040040105114000d41e17124403a0f10b2004110440000c0d1840c50500c029090720001800d50003550880c8001004809042d408010001d00c11145084203c22010500008004803585410b0030307443f140303e5405240e080301e2403030b82c02d4440b0b88640340d5031000751400400364800da0180f1048104148210714419002e01c034040e130040707200400500e140c0c113100402400c403103450f40729030300b001c2d02d800d0031125a050034040c0c140903100f6151154021051020801c0d40e581c4003068500e00400c0001c00682070280030102d50144c240c0040081d56946480c035095009050300410740c14900340c014002c61011030503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 508891699 1250 508890449 508890457
    0x20d11040221100323070906090c0207050405010f06140f0703090e06150a05070606080d021b06120c0f07050a0b0405010507030c14090402040f0e040b0106020a1a22050f0c06 76
    0x480301076030003820350800307900c0e40c0b44600242c00940c0e40b140040c0402c1f440309600401c03018080001c40002c501d14944070003440c00c0216442203010b68a05801408417580b150390460555090b41402e1140406080807151107108500100000b800089065010550b00400c2c000c1181c202071680300f004d4950354100150892b201030070701d039081020440f41050b180110301404a8902034640041d03640c0e0b035081d05c18204103207400e01c0e0b00107802902090200442018010800aa043d14094104100030340c590440c09809010784409540114101c10203c00180c103d03031640d03510900f03450040d9002c0c6001c0202040699040300c081d4200000914100d21a10503505d919a056a80640042141c64803400c26400441d01c180c00c56001c10020440320042c9000d14003c0401109078052898641004e458220060700f0642c00c5401941d0b01c00003007000308221a1903036040c580310301c2e003d4480c94440100700881d052240720314200310049a0a11001191554021a403442513842c10306a200801c105841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 508892949 1250 508891699 508891703
    0xa0209030708010b06190507050610150302130b07020a08030f0307260103030809010e01110705010e0303070c06051806070c0c0923092d0d031404020d110402211003 72
    0x4000d06c0b20544103021161a907401101904051345003258a8880b43d050034012542c0e4000340c62150420040700740c00180340d880c501501c0c641142000c0d442016645100c14900c1101400c15021905100f550740b0b03004910010142d01040f640e85103901681054103404c21230f0380e1004130313944184510926400d003541c0c8880c11a10310000e00c151b030850758195007181000c1e040783d00941d644c207502803074200d0921881d0703404800d9054040c0c540400e8030349076003900c0c2410001c96440c0c00c03c0c018030007415080143d03981c040e5441200440c2c2035640000ca240180c218402d02c01c60785c450740341807000290300400b02040d50390145200050154460703001c2c0c4262645d60303038040e9100041c12420b0008000d08111150410203400540302504101340030f07031012102031104264030f400c1050001500340420404035891260b10f00701840490141e1415001304100140017900811074407480b03904100441e490701d41c5401d401041151a44d1000b904081c0c44a07080d030142c100145941c0102e9010401210000c084075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 508894199 1250 508892949 508892959
    0x40204080a030c230a0c0609080d08070e0a0603140108030307050406111617061f0302060a090302040527011413061803030e01180503250602030a0209030708010b 71
    0x2680d80480c0d240007090010b951114000c0c5000a081003212074000c400d000d620005c11801c441c50818249040d59580031100f80051440300300b2200c2c1e0007140786801c5440c142031048075a61140403c0c0c9500d540001a2684442d09503008034207507406a00c1000c4c20707010115034098581e2a440d419950740710507070b0700b0f1010941c02d100400149200c0c07940039014891301c3c800d9492026124055a2064100c1d4110001c070307800c40440c0001605003000b00a034400350310b2820302d41c002140c60003e88814102d01000e40542c400068010025008495180045501a01c200070a01c1c11104100328103801030b44501c0c00300820511100301002c14058180301c40204142911585c50366901012003032000700003190040d03210a0342d811110b4016006101c1c040c040c2d00c010807001d90710720409007181e000f80351403020284940342c10360108070008161111070b03c1010080c4e8195911402c0c45000d038514940007012580004100044a15603401504081200342c040f1886141c490f80301f14261003010760030580003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 508895449 1250 508894199 508894213
    0x509010e19270206040902030f041a2a1c06080705040902030607180305010504030c0303051e06150904050103060e010b0a0b0f09010507021e1203071a091204120302060604020408 78
    0xd0349881c100e02c0c1144000c1c056490b15943d28446800d036082102d080358048451800c1209005200031742070f895200d50112002c0c030b850524141589807a071034010801d0582000d9243e01c0b041700501c119810380f404112100d101314070764081c4d180074010501030b0b00110702410800082c9420180140c0100f07a42c010003410195490314411036000203802d482605030716500c540007020401c284980c500460099541140074281420003400b84c3d0310160990441e50840c1c04d5400c0c3c40c1a500034081c0d08248100c4070b80c03217000001c6903041d176240034500540d94803a1a01c0000020459075510100c40032030f18030028820224104c1c100f00c00701d205032080c2c1085603820080804845100380003040c5483c014140030381400d00903004500000103c0000401d007201604114110740303005800c918000400c8001103191428550314407070640211580c0d82107505d0300324007280701c109003446001c028142d010501ca49803540c0315481c2c0780e0108100c000ba00540250400301e8107a0400d40211340c1620a481e00070f101e5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 508896699 1250 508895449 508895501
    0x14010f0206160320040f0e04120309030302130b031b03010621140a0b031c0f08130b190b060a0929040807051206070f0f090509010e19 59
    0x20142001100003c05940d0750101d4035071100c1107080c9810321900074003681c6441c201402d880d042d19454105c5450342c4442070070000056a038100050840d04145008111400e00f850240d0280c02001000f0000c6d42e50f141c0b0200c0c0d8503808030082c6201c0c01241044e00c0d40d080c0904452082131000b801005e001411124504810009103110200d01207500000003d04080580301502003010549042031000d8403a90f414101e49400c1208a07003e600040c6042d080601c14140944142d860340d02110a00801da00044c120416005400c80703026004160b880c280d19004a2101c00c00049003503c1c2e04517443e0110f0b401840c00c00d0020781d50010b00701d481e80020b040c2804800c0e03046c05103401d0341d84205485004400300c051040b00c05400288058001001400d04200402c0019240c03041d0860389603008004201c102c540c000500c009101d02400c0c1010200310584088462440581105820400c824000202c5030381e19101d06100b450680340000c0184540d414040c20796a006140c40110f041c801e00840e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 508897949 1250 508896699 508896721
    0x30a210e0a140f19031701060f030e010608030d020a0908060112020d061e0b0a08010b060909061c0b10060804030906050a050c0111030412053609040c14010f0206 71
    0x62200014003200c20310020a010a858100a150002c100f0054003070703031a0805d50401c00e00148402c21144a003010343c10844020309950029480200700342d212070340301e00d0740c803429400322003e03004c2e110a0703036512201c141c95000658020410b101c0000e00c0d010b03001032504004104203040e40c245c601c864100b19015000c002aa80e507100e07007595542d5843c000300c1081107031100000180e09000d040420b41042100402c02c00c0d51a5501240d240c1c2d06098070400240d0342d900803540309140c1202c9402c0c90303444e11008500c0b81d40c1540e100060b20040e02104000f0b100c0300392170720780c1b00300d40360f440324500280c641c481107980400c150f9004020900074a800d000090040c8068030b4100302078074015051401e00f07211a400c0d240003c17400d0f00c49200010a200c24006400b044034100d0085040480c42c00510080a0301c040c0b02e2856198001c2c1039007584110f190541403504c008610f00106085014181401c200a5071308841c407880141c0740e86150b6620380b42d40103d005208046254010b001c040d550044104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 508899199 1250 508897949 508897973
    0x15050d05071503020409140412110619090203120909010609030302030924041d011a0409050a090609050606030f01051005090402030f030304080430150608030a210e0a 73
    0x50034584c09203c04110f80c01c1510980c54886145100e114950405041500289544000c040b040150600601030707500400285039412200a0030600720b008a03440440d8000c1c103801c0c500940c58001e41c52081c1420329540b003e00300c0d070441150301e00d00c60790ba120f10913039603c4000e04c0000c001da0420701220540c1d15041060391a01005100030a111860310307600c69240358450f4010400702c4040054501522584213006400b506504800002e240c106c18000c60050240d403007281002c2c0d07101c000140801c48150440300d052a07000340c0600400c0101d01c1c201342c850350102d442a003c8c2c803c401d0001c50030380741401050b02400304141d00c0610356003444180641c2e901c0050090341c040c4038181c0e001c48c002004100840c13041c0e0242d0b0848d511641008003145101800122442c1c0d411142061070a100d021850465040c070b6211015030655007a03014018080d01e21a0700031120342c0404180308006942100840b42c45010030300200008905c20301c00031040b201003c404c0101503020007042400120035203040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 508900449 1250 508899199 508899239
    0x314160302040b150406020d020f1212090f010513200906060906070f030e0306010f05090a02030603010e121c0e0a02010807020f1914030703120c090f080115050d0507 73
    0x11040d01c6151913010303007141d015510000040e48070003002c4e806a541449032803400390002014000c41c10342c840e40c481203030040b01d500c00c0201160304041240d541d4100901081480c020000b8486460541c022003c1e01d251a00300b601e24441d4003802c0c084030007c8c1407075507002e6000103185d2104c0f1b8440300e09010054112045c1c25410440030841c406c0400c05200810035480e12030b5403680e84018210092608080040c0e005440c0b502c91200b0030300c0590380d948031543d07121050500c0143c4a03910800040d01505484040c841540550210150a260346c04001c00400307134043d04a50045120008450413207446007000d0000780c10101c1020015846140250b80016031441240d8030040b1806400742007a0408481d019040c030380684020412005103213410a4140e540061418108981c4010700850700d8604039000c02d41d5248190b200303460140b41c404c400303061404155031006480704c2c4468003c1c14461104444228000d0340042c061070a5030b02e410b0660307408809020428030b84490390782c50542052107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 508901699 1250 508900449 508900459
    0x219140a08040e0405010e030c0604030806011e0c030206011a0904050705040f090b01020106120308060f0325050f030a02060a12110c0a06050a020c0d050702180705040314160302040b 80
    0x840030210307075224007900140207940303601256400c2c14540103007101c1460b01c200016400a1142d0701241c0ea02003003150f406601070900c60901d0391180c004885094000490798194420603503000780c8030768030074281196548682c007101d80c00d0b6214044001c4588050500301d003071100c10010607a040c1001d4109a41025960900c0d40c2810f8554110a4184500b50080381401e40d60345609520f646c0d09014042c02040145881c2505840a46006100840082040b07000e041707186c1103d401ca0710100003210441181e40c1030307600401084802002221100c0c41001c3c815031361040c3c00009458085290500198003c191514140740d029058440005040780d0f08400f95440d408407180d401e960300200311b0390700660302030010b000301440d242c0d0854801408154a291050185440034100041d00491034152800c00c117884004a100154000c0e440a00220360a0036440502210036001006841680e01c26101e00d040b480070051104c4c2d80da00400010701880448202c10000340c106507004981140002d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 508902949 1250 508901699 508901713
    0x307020d21121401060e120c040e0c270f070521041a04240e010c080403080901050702030d05060d06090503040609050301020f03011716080a020a06021914 68
    0x604030000e07a1032051940c0225040d5040912001610b00c90305036a421002244041d550410344018045802546164000c801208421080080402c215020010014014003804400d90305131a110b003100c1940e140a0200a888148440141580d03007101003050300383c02d1a9591098100c4424490103404001480001c0200e071030300c0c1b8030004c400200e2070109c1c49890301c20708251410080350100c110720507a4220f001d0041c0000035001c0405c0c000360605803070f43c5900000d561030500000b054081751844040d80ba0110031181c040c1c00ca8281e0b131103580213880e41c54055940e0b025403400d89008071041b9005800400100401405a0348101d13000b282c094000074440301c842e0348107412078800c0c1c0d0003a900e075840464100b24141d4003010b000060b000c250001c3d030030100f40b00c1820312640018050aa5103080c001c011558445007001086c41d00b81c40c485500e01040d5841220070348902600005034041c0003c1d45010405d5800054034440c20019403a04902640464466114100c0d4542414026002d144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 508904199 1250 508902949 508902983
    0xc03030a151d070e0108060f12010f1a31052d060f0a0f030611090a0e06040507030b013f0509010e1614031908070b070305090307020d 59
    0x1c0ea100161a04030486040b0600302120040d02440050480c5410404071404001c250b441e004155a0b115074155010428001e040314954094500030038004003544c0b81a812980550301e15813a8000300b082980c0180c4681c8011039910f00007001200010310b411108004809845210f602299002106540001801d11641101c0300451950703108118415170340003d000c0d40d8a07103910710340c218081c101e81d0301244070714003401104124014403001e00303107030f6803520080c000c500e068003183c0c4003000042506c440786403219045901c00f6002c0d00e510f07010f0380c541400035031043c1c00380c4144004a10f0507111040c0015414501c1903172204080300400c00030801041a175403000544c45c444821600404000c5041d00c2c20480f55403c4804100c02c56034181d2020b0141004d121038549180d050b0b8000240c3c00d401d4180b4000801e15008120301d000003d01030141e80d880500101c1000742c8101c602c203151070101504d8106044099030415644545690000c0001d84014a4645101601c2c1031103480c840101102d61 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 508905449 1250 508904199 508904219
    0xc0312050d020c010b030601172a060406020d030c05031e1f06030b120105070509100e09010e060f030703120c02010c020d050a14190f051f061a0c03030a15 68
    0xc186000f200703a449801e034480c0740c90140501809821040408588020601140341d84c03418000180f80314610651020710011180400030340d15801c0203464160341c0d0703544107002035079590034400e410002440c1002480c04a0b114900b141d0040c2d6120541c40b2580c0e080301503402c404480500350307116104840e00301c3c00c2000c90706155500202403d440004103003500310240f064540c44041104116451711041002040c0c00030140c0315041c50035181902824064142a1030246a100203954084c0401c40001401c500b1016524402d0030300347c4100248100323f030705245c2d03150004d0200910000703440c692612000d2007840c01d03421060051418086040558000c43c5c0034000d0303000180c0300e40d04810310b180c06100b603000e8400b800c110094003c1c440c0103030340001c012945001c0c90008220007055030850043c04030801541d00021800350f161900c0080749840880200964030540d200243c4034084043c20140e00341c195415002010055031656441e815410018041071002c0d000213104404041000080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 508906699 1250 508905449 508905457
    0x20a030509033d0207020303040e060612090d030c0201090c05100903060608070510020a03080403050d2a030f020a05032a0408150a05040f0b04060b0628020102070c0312050d02 77
    0x803000070904081030f01180c079440d002901000a6565004001900044c1c60010844045608840c454041e0380c0b079407000656903203d146038500154002c4401d000b40500c0108070030314910002c2d141089141c41c1490240c1c00d0352907821005e860034048550070000d83c2440c0c03d001c402e0050620b00300700c1c107603265502c1000f12100c507009400e45900c9094140002e09100480142049090000f80240103007990003d046640c0208012304208011991080c1c02c90f0076080903010a055032013240c0ba40740781c400c0c20503c00e1816a560400030341405017410b070803071a0344201c660184482d511185580c0d540c61012a5045c000100102d1b0385043c601e03025507001d50100503001070402000900a01c4282030360201c600c140152026030120b00d41002e120000d61800348041a580d80119110400c0c1d5590818400900001c40e070290810070000d20110310701c4a20181150018002c206401c95a02c5000c00320300703e000700100200a0720a481041c40801c02180e00c9012514661600500e4982c003a042903041c0e0308 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 508907949 1250 508906699 508906753
    0x1060803040e010e0105060f030408160f14060f221e0b0f010503070506070b060d060c27060203091207050402070c0302180f1302041409031e0307020a03050903 70
    0x1242d100510500c040e14029900524040f00d500781429034600c00c22005110180000340380480004800c0c61a580e5029482170303403908100e0316003c5900034241051030001002d14103027a0300610740001e0b1043c080c0380ca181d02407000c01440240066546494010442d01070340c090340d0411074180386100c08114400300b808402c0c8034025541c0503050a0402c43d03804041a04403500c83d41003070a06001c10b488800075100c000c0d03004044a0b00c80c0c3c0700c150120704000a0400007400150a00311368100c49604450020f00388110003080550b900400001154040c4030360007a600103820405c5426000c1c682412400c15528800701a141c81c5592000014120790001c00300301e034507400c40c04041003549001050300012040c0000c05581c20315012103030340582e0100402d100d848182040c484400d5403115400002c0741400011000f00300d00705243c3c0c0c2a526000059840d004883c0c00f141c24400d042d080040d00d02504007900280764194140c0e07000d594940110308a55050b1150482d02c1140c8006211011040c82d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 508909199 1250 508907949 508907969
    0x9050705130e06160509031e0c0303040f060503180f071424032208070b0141040c110d0f0c02040509010b060c0f011406100e01020106080304 62
    0xa480c020912a211100300030704038026241006950000101040c82d903800240025109103d070300d082400d61300b5024040d01160144070307a01d0b403060303580d07400450290488021070488044d480500109681d074030480c041c00010b000b03441ca003080f15500420103503800c07a00060203108243c810300441171802030f00c481c044203d9480303240c0401c54580c02165424441005644202001c11461180d0358401120300824002d01700000029440c0e04103e0800c42c103c1300d070030600d0402c0a44030b060210380390300050801c0e9480ca032601d000080c6600070745507a01110111040c1c1160710b6078188540c103042800200d26004030750b61212000720690707491040342c42c083e01c01d840b588010031040c150325203004895258030090140c10100d107880c0582144075051a00d03411103000c07402c1d60f140c0d5209070140c0300060701960485801308004403010030104a400b001c03807042000b00000d55a5034545007c020050f02d4041d040700c0303151801c100c500e21441411410070b0b0180008906183c1d2102e1085c03441e03020381d1184101d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 508910449 1250 508909199 508909213
    0x90e19120801090504031b0203071802121e01030b0408070212030c1c090513020903030a050301140103141609051f080c0403020a120501090215070b061813050a060905 73
    0x4a03401c024080d015002061040109140079a0040e000d040c0380ca03c451041320582000000310b40d0100304c107801420141c0e050b4040700410088407406508088d020400d102480800a24106140a214910b440380080b00074082c0c0d1840d110044907400c058016146a28100081009600d40c101070000354540e40004594485480358801e080401d21829400360340c0280e01810011540030410381e040c0d810868a41d02c030301e451494034000030302c240c210b05501808041001114031f504000a54100e45182020030021100784004508449070311180c2c0c1d100300d40d4180460380707200b90541c141000302d03241d08211081c1a1980005540003103042c0086a9485a0905500c03c10354011000e41c1c000e41d421886606160456001030b55510050195840c0d203090a00e84006100c0c0c250400c3c0c0d40c0c1ea8001e003441c85100915640d840550380080c0003507828090010200704581403054411500c0d0301c402901200744c4c3c480d403070030120098650300165003034030a158008020400c2ea02c1810f030898070403c020256 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 508911699 1250 508910449 508910483
    0x315181605031507140906040305070e071206120f1a0405060a150e1b0d0609090201030e030a08041e1a0f1b0f0d1d0c28090e19 56
    0x10340040c1a42e089403d4070100c043c400745507001801c00510000b0246080d0301d6100310804140c1038001c650000e00544505200050301000e441d00c813038005e09030341d5542116600d4400143c01a210948508403012100200d42c0022884a210030740308180f05180c80510b001c0741860b02c80c04240265010344040e080f1030203209007811039100700400085c80c02c0d9100001860141216645013004145900240c080d134a104d04078420341c422210740300301070a4208030b8552541022002800380b03040881c0400d00d820925000300d54004141c0c0c0200b0319580d503140440e603d41d40d4030541202138449814034118121019000101502c02c403100c5d4410240034400e05140000280c41e41c00700c0584410310920088603502c2080d100402140d0b610120a0300c0b90356103140f8009000010311382d9001c144000b015001c840a03030202e01181c4e000311800211020000d400c0911030f40400d500a610b400b01030400c40d40380402400341640c0142207031001002c150341040712407800c922084144030804a400003101034003004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 508912949 1250 508911699 508911703
    0x40203070201151502100e072c0703020c0c0d050c04060603090c0b0307080708060d0c0801050915130213060b070804030c140d063308070b0702031518160503 69
    0x13800c408143c10038900ca4a070300651503d16051030f22119907182c01c00510f080d1743c02c0001c0c0f40140941c000c5035415100e4103000e6500011000d102140c002030700000318813640d20900070340799a000c2a0b80a442007507196010400c0c00c001c8444101c88901443c5400d201d16a214480c0d980107086548000c1381d822500e2414841c2040b00c2d41006200c9081401401905075016888640c00903181c00c00002a86400e40060034528130340d10010030036244448085050320040d007009014074004011909502c02c1e4244400f07600300111181854843c8800310807001d031a111403000355480a00e500003d10344e440e14182ca09613408868161910500003c00b0810019005078140040405581581d540b40d450f00001c1c2080034404000b9003003680710740a4500840e8070b9040300758800078401500c56600a4880e034840070011070b00c00c0c070030f1600924100050f800181001c40e140b0300ea00401800700300483c4518032415440c050100d002c844a07004290300921420050705088030f0710f540070f00d0240e900e003104140c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 508914199 1250 508912949 508912991
    0x605090c031e0a0b15040203010617090705220f02040b0a0f050405061e1b0705010e010207030b2a0c0c0906010314070e030c04060905011a0301060801180209040203070201 75
    0x80954012100e0b011200e0011980350802030303100314905090f0310f968280105507400300d0038090f842840000002070f03a0750048580b103003540b10080102c045543d200401520360b803451007102d8000400340003140c5010301c50b06180f02801144400042c844907151220750498005401244002d480000c03840c440540040c0f4075860300c00e0030702d4041d20b001d08060205059005103000d41c08d4140300000034202d502d000b5003d44440814000d40783d500b5990135855240e582105200b214041404101703070712171652000c241c1c02c05482c5c100901c0c51142c5c5401000d42c03003141c461600c6002e41a129882c080c2000c0b00500181802c1640c0b400419400444400b0440070440c00b500b024141807421156180c0c000a410401d0740c001030394100300d5404102030006ca820301d01d00360700050340546800700c089400100c2d40c1c0243c2c1030382c0e8090307103070030309102ca041069445110a009270340110b4150401001080b5905181e440c2c8401c0d4a803016081000e40c0000ca0700b40c3e081a503200d000b61b515001e1280c02000020441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 508915449 1250 508914199 508914223
    0xf0305090709051f080f0d0c14031c06080127050c03070305010903080601031e0504020105041205030301080d08240307030b01030b0a0f021c050c12010312080601020d08070e0d0605090c03 82
    0x3400c06204c1801b400f0b030fa01c0d1541440101804596a0002c007802840021006000d504506403075440940750f1b01010504103042c180d40d0000d06d02980421303614014410454030b484044400c40c00340c14400c05898400c00b1407001100d10348100142821651000d20051008600c6080042186415450302400501300141554101490258608422001c15514401c0c40b1500c01d40000c664a0742e00048982e8480c2d5000304420071182d0360b0701410048000011030484884806403010f140f50303290110780c03c0d2003e8610000400f2503c001d655040303070a540200d026039005048440035540c88e0b4a490746e038802648265000303002d4804010b01104580121500f441c1100d0046103003501c44080c0602071000ca00c204c04905990304001100000c5180403160031a0560ba2a5111036a60303140000030b80c1100303031190317001981007008200c841d4000680b000e442011515449203e9403506000c031042e108200c0c07616404944254940040703141403040501550a800141c00c108034100285441c0005034620 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 508916699 1250 508915449 508915453
    0x50d0f0b0f040201080c0c0f06010b04080c06181201020c010504080d0c0809060c0d061e150e030706080603150709050a081506062b050a06150f0305090709051f08 71
    0x402c001030b03a1042105600140c00c4015035115016640318500d81040024004071078800c070380000c80c80182c110702810444034180125000800000d043c403189014584102002a8580301300102914027460141c2c848a0310350b00050500f01000c84507420b481007683c047c0c90568000881001e010b96038001ca0b905640507007800c06031410416001a174941c4014804404c2c42c03408a00700031024460303004030009042d032420700e034034214034940c0402c07440c1c0b10362158001900319441d40070805c6020b4840d0341400840140540760140c1f42c04802e568000c00144015810701500d0100c0385100d840da0b150500504140d40ca04841e02e0400090080298468103d805154401c480031030003100394840156001c442aa04a61124405607a004501d10400e00030210403160580c0050003802d00c3d4812403080b0385a0324184891507817207144404461541144c0000610940c0001070003d010741c1000e134100074a88202c498050380c0b82100000c40c4c0c0c0640d100d040c05454405540e2034001c0d600d114101800f89030300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 508917949 1250 508916699 508916701
    0x90509070807121a1915080103170703030209090a0b0a510305070e010e0603040b1504110309011d1507020a06020309030903010f0605010c0318050d0f0b0f 68
    0x805403611041107001c0010a8443ca02141083d00685034001400e0005c0c0801c0c4c171122191081c500c44120038022a40300d82e101740c0c103040341d1a1064004a040701d8105005040b011041900441e050340900004c0d014150200303c4031203039413128114030703108600c90000001c001c0c01d07401c2040300001c1079602241440d40083e1310f0f0350212501c60b4042407000c0c4c100c645c5114484810300f817904480880e1044919141030380c4944101c081d016041184941126034803c081140c03e10019146500c0d0810b00740d40148060001a0004080042054000340d11580a40500901c01c00242c140c501c104034840444002006001c48480240a442038520200440841d040050801c560fa107241c0020f01306ca00c0c48021010480ca81d0080c05000d1129401c41425542c034500a261555030340e000160881c003075860b2111440104c02540316031400c1c0d410580d0380d2148910607480403680080942104400401d01a20000d6203550b1500c0d44144a80300764150001048035040c2a10b0f40c21000704010301d8030700d04c1d030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 508919199 1250 508917949 508917961
    0x3230706050f061c0611070302030d1407080c0d0e0d02070f0902072d210206090d09090e0304050a0306051806060d0602030c07020405040c170f07090b130603030905090708 75
    0x40302ca40746444d10f02d41c1e425604503803c0900103424054110206e96600190381002d040d4040f0050404a4200005102c045841e030462166100c1c100c40e02c0c1c0000310308001050b4540b03101002401d240300d0040c2d012980d40c181e030b02c100d401e0142038100b550240c3d22444041012907020242c01c0f000b0161560118240391054982150005c0d0729441c003040b600c0c000201112003012421080301e032a8100200074864403141460388000d13040c0000b004003600c104000101441800200e080f04207100707580703103030165140000090240244901400c1c407030100348404901500c80200040040d0300507407001c2204e00f810061041c401c503405400c04040e8205401f0000e1a480c1d91a0351142c44e40e00210059607a40c405402600600803044025401410602030000780300e0302c48050001c0d01c03ca00c054220b61000c1ca00165524994070b8002c0744560814002000b01c081b04d54042e0300004d5002d4480c8440d1484005090101e03140d64004a010a440e1581070001781020200c0a90041031070a1060f82030400c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 508920449 1250 508919199 508919209
    0x206090307020402131701021c051302123a0f05031303110109050a050111040e04082d0a18120b0a021611030d020d0c0b0403230706050f06 61
    0x91078080c0c010754002800a0240d4a180d03400030081c05601c40c00349010020707040d00c501070b40c0011920310320007200b03a0303c9a50740d04070740c4500c074002d0341e0010101c1c1e4a401c042d4248040800307568031010142c011070541d000103841400c4a80e08035488441880c59510f0344d12010400e00d04d04071507403c01c0280074034510b08003a0700302c011280c2004907441401583c03509480c04a60640756414114929420b00c05440c0070071a000556060292091000340181244a5040070040c00b07144682c094903202080440c0220b4181c6004240d0300748007508004040170000c0d86e811585184180400104000140b80c12040e41d105840034000fa10a40b50600302516090b40706015030390b9034201a0212900c0f00201d0800d034142c3c2c0c125140b450401582846212403401c1c280a08400040e515002e030081144402a480c804191403d0540254461500e8001d0176140d10700b40000c0244118140052100c001d040d07a140300c2c140010701922030031459590001490804c0135198054108941d0003a04018803001d0390ba4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 508921699 1250 508920449 508920457
    0x10e09070e181c0f0e240c0c120714100e10090e0702074203060801050114031006080c1e040c030e19080307050d0b0907050a090602060903 61
    0xd1070002501580070050030303040c41440300740c800c1401e1075083c6101c1c40e26040345a540b10105a0380320704d503100841070f050008000305003a03950b100a413040e01e1244001c40510280c0a4080801d003210311001c92400801c4a200300c1d804403042551090200304484601c18100e10310108056801032200c050202020709492070328880d40344140400307996414158407070000d0380c0040c010b10714203100506000001079102c0900d805070405400c16074840c1490712032825201450047c030b082d9040700510001c0f00c901342c80700e540b40011081546079400003c8114003405034034082c2c040341000c001d109000f40d0400d07203400302102ca446101c40c1082030801c6400c90104030004ca40d80207a6940202500d03d00c0940302d812a40c040d1181d2052610f11118100c0380d06901c89241121901e0072243c0306070b00074a1a819840300b040001341052010030000702c0b2540f10300c0c0038001100e02c0300e0340407503150703031700000510902021100d40d00094004078160100b5071348440381100410300c50000e0120b42c00d0860840b500e902c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 508922949 1250 508921699 508921711
    0x3030902060903010f0b1005040506090d0212030324330d0f151e09020d0207021804020f010c05070504050c040e04060b010f26061f0305010e09070e 65
    0x5a528800825921441c04a4a03256001802000355040e001c1040c0001d100c3d40240500038900340c0c1d071100c45503018200b120203641000b41414244241203003003101c4d0f505081000c0b43c11400e001a8500c0c5c6d070340204069801103064080960b0184611804441400e19801e51640300d120691005802c2284412100ca0100440c4440760410108131140511612400b80be05410703034605002130852003003940c40341001c46e00c44000d014000d9550341d05101c0c82900c080c600d11070004404010840549036078001c2c0301d40c444806002d810070405400041c5411032080101d01003550f24020401107191035007007095174200900b8004403400361629019502d802c14010306020355500c401140c1e101c0d280c9030a407001861800301c036904601e072910b4402c3c050711441c001e003408928602d02550a0600031910008a081400d2489205800944600d02105009040e81d500441780302000c40010101e40501c1640a41c5602c02140e5135150260010801000a0403059582c1080b0021b2090700107000d40f00f50400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 508924199 1250 508922949 508922951
    0x2180105090708070201320105040207050d03021c0912030b06030112020f030307020406080d0f080f0402010c06110f09031e060403050a020705060d0c020c0405100603020c010b120f0601090207020108040303 90
    0x44d07501041a80144105115180300b400100180101200088600c1c840c0074140c01c980b901590b070b20010300060b40201000280103170001400200e0541c4641d02a00b41e00c0c001c0038081d0810f101c04e4100c0001c50304c052009907810709000c1039808616816004003000040d0903140c10f4607640c5000c100e02c4507550b803010020310492200d090007050f07580400c00e6074505500280100405581c03006001e54900300f1101110100b8124125410403a002e000c4080c4100e60755005200250354507801182c42022444c0c048403d165100e400c0701c031040081020780141400b80518680d01c417800010140741015014100a50f01000d151780d402e114004580141c00c141e00d4100740d500c8150740c0005a0420055411568001c4400310f48641000d8030f0343c001e00b024803000c0d003d481c801200c0f00d09000540f001100c110400300b07800e0740e0070884240b1a07401007450b003150340c00026440140381c00140304a410514505010740c8181c0108030b04650501030513004251b2004210b00d03040c9541d001070001c01c00208090181 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 508925449 1250 508924199 508924201
    0x50609070c11010c1a0106020604021906300e0610080105090c010e030307120e0a090b0d150f0e0c010813030c1101090801050403180605070201052505150402180105090708 75
    0x110501c6030b6081d803091681d02c081415070312408000e5542742d00311002d900c121070340c0944000b0380203c0c48500054800c15070f00c214500711082804a801004d011040015104007000040c20003000c0c480d1501d920180740c0030342460304020118150701020364219074043d904d0041440015080003c2c0b03440440e8080c01c04903464486600000c3c110b004023600505040c42503c44003200d250701400c0c040c400d0340100d400d0300e1b03c03544641d00c680885150f08101600304109101001c041042c0d0fa80c6283d4014056601091111007003c41800341c4840403030250080d4050081200c0940c1c0200b07805502c00394200003400300010a440c01040740048071030180c045030501c1d003500301d02d07441120444040c004440007441207003418600140780301d00107001d0b4050040301101c081401e61003401142c400540596070700d410103040003030b4070a00038000d840b0f05160403d1194420b0000d83e081c00105200c1c06c0b0040c110980d0b24060042c0116060303007000c00328030071150200601807643c0344101103800c903d0b40d242c20451 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 508926699 1250 508925449 508925453
    0x405010c12020f03151203122502030d09020406050a03080306460b030c1201050109150e0d050601121401020a09142b020a12261606050609070c11010c 66
    0x82001954981041400002a0004407523007074046203010303648042c0f65141505054a6060a401074041d0039030058008101401c584006034000c00d41c2c090000700300140056a80b800500032141580c41201d01c1803002c8200111403900c40020b55070303103802100321041c450040c0048412460807910320061000b445040a40c01492102c100024103400b44045650f41020384070a601038004440ba042d603e0341500000c1600e51013101c2c40011100400c48010300802018230664800000e001155080b03030044025a0200d14200b003002d0090051542d0345605152a0904184144410792072104a81c010401950f100b0382c048142401c64803010a00c00807003c041001070340f094102d2210840c251000d02c01482d50160002d01c0c14900c42c8211020f1078030301e9540c1d12030580c00707a42c10009010341d41c40d803000c544440800b0030010b045845040c0301600e44a0942404141000880415951180c0e124108012070038502120780c1c1003405400c003604018510741c0e80385149103025a405040282092090013 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 508927949 1250 508926699 508926709
    0x7150c030c0210150e4309030503041701090203070e0717330a0b09180c07080a090e09060703141303030b0310090503211006030207021201050405010c12020f0315 71
    0x5001c03078043e1001070010000a10b1b04800c010345041c8a01c0308101340d030940d0380c580036881a10072039070308c280a142068500a20441d10070351007040e000d019500d403c41400165424000380300940030000c00045641000c030b0f00144107115004038402c401c840b00e002d00c401003078200c000031021096100c5881c44c41d81c85601805180451b022140c0d0002040c600208030041c000020b0030a460341030b241d4540f05444503505644540040d150b08560440030080c1402284041c80180112110360800c1020300703642d0000c0e400f060341d00702c4100256030000e0040c400c0e06503040c010381241180c03800240c1c116040415aa14080c09500c40007000c0c195140071460b0a03440900050010442c0300c00f0801c40480c0b00c5c00c1c440d450764040000f107024588000b40c10171807000c0388081d0502514416505800ba03500b008800d40095100140580c1d0003510a00c01243c003400c24002d96104620407000410001059003025000400c0504080707085c1d070050000e62000c00d86e9900b03a03a402420140600c0303100701c900700421 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 508929199 1250 508927949 508927981
    0x41805060a0b0f0f1204260f041820120105010c050319020f15010311090108030d1e02220b03090d0c020a09060621110f07150c030c0210150e 62
    0x1782202c0c070b00d07020401409044858000b0104001040b004002101a0440450311130200b02d5800494144414048880d03882c8542d01040e41301c0b600040c07918070b000b21410302150700c080035500c1544001500c0000f05501802c0b40e0045c0002e01b002d1a1005840c0d4520303407640140d4046194a02c1c000b0400178505208005605441d0180e01c151808409400ca0903589550240401d90f45080b80c1c3d42100c00508100162a040300c0380b1001450a0500d000881805800b24040940324480b404605010300d40b400d2008051240300b660003604a455504807140c861825a40801e040d20814070402500e09004604101c07070703004510b841401041e107031000580240302d54120050075454110302095481d002807501c054402d00200c3c03502d540c944900702000b6542003552008a0b00420700030b80d1100c031080006846014806d0140d5089507003000f1011048404507016440001d80f01c01d1a03000040d01070080c0c100d04401c1110502c04400c2400d60b46210b61744520441410b061500c0000707090942c954412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 508930449 1250 508929199 508929217
    0x40308030c1317010b0f090609190e030406110d0c080d1509020d1d120406030509010e1b0a0e010819052401030c0b0711040515030102041805060a0b0f0f 67
    0x2020046001c0c07400f26009020146045015a000b120281d10a1811041407441800300510922055442c0304404140002034a4141203458031a00c402405000520152001c1c0100d0341e2803004881da5078091030301e0720b40c0d01d0b90302ea424445007000701004211520100c1c0d103413500b5510b01007200000305000800000d2183d10103480c00d8804640042482d00c541c021448200c25440d0344040580641d00d010340300c1618000c6d41d501031008110800c5903c1c00780d0480c0384c1c845815000000c945900c40061030400c0c1030080c0718000d40d0ba0b0003010380c03424034140b88010040c08504013480d0056042070121955480c0516038420302c0c0310f958801c0b10802c9010070018110349000d04107180d40d0072202522002048080c0412592081405404248003036060b05598075103400c0644030070240303c90f009120081102815202000802c8083c030b10340c0d42c03000d00003030000b170104c3c42320400a00d4201542004507100a010644550802c0744e04004079404641500c0c0c207082000d04071560780c4103d080703680441c8216405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 508931699 1250 508930449 508930469
    0xe100e03011a0a05030f0c040528052202060f0304081e030405011103070509010f1101020f090a0b07020904080d0207020a15030c181403150907090e0102040308030c13 73
    0x74204185a40002d1071855070507140000314585440405854181d00c950444166104168075810341c5071a80026802140c07130b1646900c5441d5503084030236031403100c1011070940f80c1c49205101c1c141c00d6507007400b40203020700003c0c86107104042e8000355040c4104070740421001c0e4003001007014051094200e61034021845401d1842410301303404503400f5001250166080e510349204040d124206500702c038030507111541d8180c0f60030318045c01510300c40d903d22440300402c0340a00001d01e003c4000d1008014058820410035142d107018010070131100c21541010741541c0080c441140141c43e1204c00036041940700901544036400750b28144000e02035442c020b580500140d0000404001c007003201c01c0107403182e6505200074421000c05554440b1448400200141c03070b103804001010382000039032a1101c000301030380c81e040144d40c000c01040005445000250700a48001c000700b2120340b18030044015640000d43c1880d145444001c0c10340001050b15500300c00c009144003040d03c3c0307150240017810542c81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 508932949 1250 508931699 508931711
    0x804051c0c050105130f0b151e1f17090c0a03080c061302030c130905030406030c02151b250521090f0402070c080a030e0a090506010e100e0301 63
    0x100007001e2800240040d40d25500c3d040100344001700702c0c0c25007042c03180c01c800f401084c088960346400180000500400c49810012058100c0f0360302c1441c0d0101e5030f285941480e42102d0801e00b08581070000074079600d159030580c3e502d1603510740c1290b040800702c640c1c40c03400001580c450782214200070355810801e0344006841000310030481c0410140811400e5201118602d55500d2a004810211680041d40c1035000b442c403030409150a0562031440e01c010400419a0f0f0a0743c0d036464950f81160b0000404241c85810184030140d0400407445100127484940c074490400300040500c0e40300341020140315600014031200055001800c0280000d5141034045c000d80050401517100c0030070031007504030300004222408494a001050303074940c0384000c0c0380c40079142c0a601080002c1d400341c1c0c01103940094100d0b00080c5a4001c3c081c0c00d11050081e02d0745125048850200400b5004980040c1e49907484c0c0402e104c4280d0f40508004003041d0242e45440c0d600040c2942a15150b804a44060307156090034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 508934199 1250 508932949 508933003
    0x902131805062d04020d020411120c040617132d05161202150307090b03040809010e04051302010e130204080c180103031b02040212041a0a1803080405 66
    0x507000d0b285255034a00343c140d00d000c01c41110110340603900690f00050741c1d000c04015141c594003007a4040da1a01040c0d14068480b48a400c061008841741994001f01150412145401050402060004407400111440c2101200807013041a210203070038804010b28250406003c000014544080f0341003883d090042c91800300c0c1d039865490a4801000c180c40c40000304c030f81c400c020302c0003034560040000041035000344803000c0d1038100a042c1010403400d007000151000d0403030000c500541c0248183c03691a00c03000c001500c114444442c40b406686440d0800020001002c43c40e03044a60903c0e0030b40324010000005040982114610000e4510008000540c1480000c4054040c24150b605032080c0e10a0f100f030343c4d8014402d02c800750104589007103680d205243c55030281c215a100030801400c0c81d0f06d60307400000c0b034981102c0450700c0d07440080c1c1458203030a035082c501d640842da901e070500c902403510018000c100740741440142030103403101c007107004c000050003001b0010b2070031000f03007070089460 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 508935449 1250 508934199 508934221
    0xe071b060f110a0f08060a051507030305010b04051f0e0406060c050c040c02120313051504020414063f07180b0108060d0f0203010c120b0103090213180506 68
    0x30145828040340391246525403204164190764284003c0c2d1a00c0d44d03510621242601d000c10001e00c096849009944007040c56030b41d411221143d02c1c80201d681e929581580703409002c6a1040c0c1203031b41c0c040360510041105954508480f180d503c0508030001900c02c2d0303181e05440180c600d8002c2d9500c24280000420516072207254100c0290041044900347e0000d0b42c288412200c0f1603c0c0030006801503005004400061070096400904111211081007515103c15042c0329085480ba4038071015001444154640f80c01408901c0400c0d0401c66a18108500004d50342d120998080882801547d0346141100d0001a005400613005850440c0c1400307520006448010341e010304140b5112503440c5070003000c0540b0034000e40c00b1040e1195101c0d52552000c0002110501c10100c8040521407104001a2021300031340d009072003192207283c03074414044203010a0b11781242e14141014030380131501e00569a030070301100884076110b8001668014903248410400c11080000d05103100304c2051200b82c001c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 508936699 1250 508935449 508935461
    0x315010e0f090f070e0607020d060c180801050f06221104050a03120f110703030513090c02160b13090506030304030b070f0210050402011e09050a18050c030f010e071b06 74
    0x345640c0c85085911217810407510b80104140650400e10650b40c550004015030312600c003040490408040e022032200c00b000c040003d0303820403d5180d4441703051010b0000a43c0301d0a411800854150014880101e41d410500404011080f0942e4841e009940c008a500080304e01619002d000c28a0054890409803480d01500004100050070946061622445105070f2144072400c1d10150411503d0360700d0488050f003020307040000881100e01c00041c02c000c03030f1040032005900f5030080d201442842d141c0c840b2044040d4001d8101100c03c0003180710801d070760380310a401e403040218000ba150312590702291450045400090030b480c402428825510f4003d042c40d042081250308841041104000100a07100300b510020b0110301d0001c0003105500120002d1145400c5511303045400a40da08000b6034028803e40c8003580c07203004400314000b83d809034000d581e44521102480352441c00c00c01000311640d801441600440d0744a40003040401b1303c0741e003800344150b041d03850103400300305070341400401044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 508937949 1250 508936699 508936711
    0x40213081b04060803070b07031806090b1807090e0a0b0c04300605060414100905160804150609021201050316061d010311070303021e0315010e0f090f 66
    0xc1280e8519280c40c3c0582410b4541c04800b8600f855181da54201074268050700d00300515454652506104141030304220000307008c1e030b801282188081c06c0240c282000901403000d4086c14400b0315a464100142d0b45080326010800040c1405140300c9031030400c01c42074030092802e02c2420902600c006060701074410303110903503595800b045814414000b99154440700191210a1803100d0012890315481241d01c41d030041d1001c1507140d00e0b03010050000c3c1c8c0803140600c45c40c03600082070000090300d00c502580502a030030740d8400749050780b0300a062910010700c02484805500c4818007605415007005c0001c00b140e840954440080b201081c404820074090030b80684650350750903860030095400c1c2c2088a03641d8130703000c80d001010700c0b01d810a5040300c14506d050544806040314078003040d1009182d0030f800b81c0c1c3c0040c2c68202500310843d880702e0000b0f1070b140302ea4080c000c0c070240350118200c11594032024201036100100100200c1c107101e4407191000da0040300c15042205680308010690301ca01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 508939199 1250 508937949 508937983
    0x9040302070e0c0c07060c03030209030709051605120c0a140c0a031101051e0a06080304030506071e08010e10121109010801020a08130204020f0705030403020108161d04021308 77
    0x342d600b00c11000d5038004c0304000101d0381d01000c4104041400307082c01c040c44074020b290240c900b0001001003841c0661a6201e4000303140d031181000705000825250341c07010f004619100d85001c031802d0081c01e4004000c1d00044520790b0004070701002902074000c1e504a84a01048542c4500c41e0b41030302511601400b03800c0c4e011800510026000c000e041c443e5911484151105400b5030790107403900700c1351110040902c0803141c0d8407034010032014020030103230004521a0000340a5440d1001c0005d09004a505c0800c514000920b104416a078011103514159207160740d412645aa45806119052210340d010b140060600c3c000b82c0140850f0452440c0c0030300c0c040c0c6082500784d9a0300403aa080b0f01c5000c00300f400281d0300300080388010b1a640b0004420900041001d802c06940d1100d00107142d110300421140c075400001d08004658125030303d01da01021041c01e00d04141d00c0024050728014245501c0700042c0c3d500e8411024550342c03a0305943c4030484034144548500d440b18501ea548012880543d9090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 508940449 1250 508939199 508939201
    0x4030806060a0f030f0e01060e0a0e0c01140327060402010906090b0a051308070f08152202150c030a030608030a140a050d050406091509030801121109040302070e 71
    0x582400000c0380c0c510303441d03541c46580e950070341c0c4801c130010141c4540f8082d400d40c4505811401980034002d500103031840b1101c0d00c0903070401140c034030708846446200c000ca039001010101000d80c5c00034140c1d01844a0b80300ca5980e40e0f980c0d0390000300d105640ca42002d01034031100d44500c1419a000642d1480340703100b0b8a038405010384905041da180350340c6201f250701000c802c2280d0318a251040c4040c09a800c1d1a4100041541d00c9845150419aa50b0012044c000c0319240820040c0420441000e003e10b9240001c0780e1070414009a200007103031815100d1440107034a880200711748802c0300301e104e50a84043c80d141c840c4a00b0440b143c44c0d40c0000300e00781c0028100312000c96651300c044122000c220240c0c07500100144502030303515a0340c01601040d030500078148981e80070044540030b078500c04d5100701e500085450035442d103801d0580d004c00030328800c0c91820010300c0000303070031445441c155100f452000441440a1400c0e46003a00110403064000c400c203070902c01050303000038030070042d0b0b0301e50100e00a031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 508941699 1250 508940449 508940461
    0x2030103060c0c0506010501182112090f12050c040c0807230a032f090a0e1b0313151506110334150b1e150c1005040308 53
    0x1140c150100041c02d00e821010042000b50301803800514048409d082090a40c0d507203000100039090348002d903155a0307000d8026070040103014101ca0050081e541401c0d413001d4140380c0d0864180030907000d403a00c10700f0f4a030091010312900300049001d291000700280f062041c44070008020710350568146000c50064094038904007102c03d04002000d0740d0104450070514a404124007074903011440c6601040907840003c29807404032242d584094140401d140e494008405201051429030300240b04c01e0844410302c80c10074040c2080d114081c507042c1c00c2503140d844841401d4907554800500401190310034031004110388541c0c2000ea4440c000464504000d80c1c1c80c1820794100c4501462625203410400540ca0201c504091047d8928a000b031440b01d0702d05034924605c2c03e01a462800e996030f8920014204020010340644000080161244030305080c80d0141a002145040002885984011340b42891175200b002070300c103410004001c40b0844600104d410000f0035041c2c0e070a0b0000360b1039000140d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 508942949 1250 508941699 508941707
    0x50a110a0c29070b070302090d050a0506070302042411161802040803191b050102030a0f020f090f060708070b091b06120411030319031a030307120e040f02030103060c 73
    0x440040e181d070160389003907110380d5003490804c4001d10200c145542440f1125064584401c1c0001c000d1181c4014403521005040880c602030000300030404040c01040280104401039011303108074800c48100411004071014141c620039080c001c1010740d403013405d110300c504000000c0600100c1c0c0c040542c0142c80811241c4a905078440c90041103810b60081201c400f0300280c61740c0c0107001100500e02000110b07440c5000341130340600d0b10002d4466a40100030700510000c0c510074010803854500045203400c98050a0180c103021304c940151103504005035199007a01d0310422289015800340d4190350341c842a00d09025480025540d20b0254415180c1c9921080c100608281440f2001407842e400c02c0c010a85059101030001c0049401c1070003d050001c035610301300301800070003010758031110840c10410002422180710207a50f0740c1074280c1e0100500c89440100c1107902c1560040c0d8030b201d460880d00010b0310522510841183c0040c42c100e50b0300300741c0300350b50301540c107884c4104000c0c0620031003120300b19 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 508944199 1250 508942949 508943009
    0x4030c0f0501090b0c070806040807020306150f0d060f02070c0f0e060a03120c140601060e060301261603060902040c05070b01062102040807080c03030c0607050a110a0c 74
    0x142c046244480203004e40701d540300c05002402225400c448402c0d0710f90f03001c641030441c1960120340700700c40400c00d881145810f00100c3d03030110003040140a020300320b10000d072814a0202030240a690ac101d682400e00c225070f0806410840c041d0b00c01d40d911502d41ca49004481058840c20740e003440c11201c00301c1e107198803207003507402440010010300c126819a140d146503200c900c5101e400344643c000b801c00028001c03089600000e1680d01c00f030085589000005405402007a001501c150010401030020b07000310002d16010b00d040184003560307500c54440c814544600ea5400442160001a000041100542055084a2080d602403161a45540060307415000c1c0060081c400300a55005008242c03040c54410400351fa00307032074400314202c0daa07111812a40b11350000c2d00d494014880a0007050070030859a49454403c0e4000c601c0c0c0354014441907224540640f0000400000049405450b4481d07807100302d43d10760300c00c10b40c0c081029034500700c1ca151001e442511043e190389100500b007003400484803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 508945449 1250 508944199 508944209
    0x1030605010b0c06281a0f180a0207020411030a02041e23030118060b120303040203100b0a0b1902060703291807090314030304030f0509030f011104030c0f 68
    0xe22140d05c440c000062800080008085072580c00c07000070404807030380e00400c0320100902107144080301801d000d000c0800303400102c2c40c1c054811201c0f40c0f04041280844294000c1c1c0c3c040340103842e01c429100203800750a018a103480340300400f005003d031031a9981d0040086451500c840c005c0300b24600240d0100360040e211301d480c1d20035000c5034140c10110351850400c1810002340000340d9403246007050440d0b9080b4180540d4415901c1c2c20803049401e01a0f1244001003160005506502c0c160f070009a54411006c0e401d02c10607242c206641c0140c84121600c00a000014444c1e0740380d000a0000b40038505106c101c800041c4510404192046d00030700c40e620901c40202d45d036480c4000480c100131116608800d01e40c0e08200b1f10f0a01603542010043c0700781c021126a80d031103008034030790700b04130203078200b43c1c15807800303d40081060000090308a614100c0715011810026141c3c4441c000003400c226090030190a15402d065842548091100060054922403000c1904071034a6011180b40c1038005c1c0a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 508946699 1250 508945449 508945453
    0xb0d090c1e1a03010e07090b031003050f0a081603030902182505040b1810020c090c030c040608180109030f0f020304140d0f0611131e0b160f0b01030605010b0c 70
    0x140000d50005c020f5aa001d807160814030201c0e80d440c2c90680c001d500442d2060f0803505071000038410404140300da8040c4a40100c010918003c50752104500c5102c1c0304800700040902c08040e00800d4085c1d008a030090350000c003818518010051801c500b80d000322074221040900b01840740b000070354000050284050780d5a52420203081c00e4002e40203601c4030410104003d03c4548483d420380e140000c02c001c14106a0140a01034007050034805a0540a04070020160b4240100440e2804442c140c40446d01a898050340f5529000400024649200035041403542040880002d2641201903050500250b0b070740c44800c0c1c10303181c01c100d031030b401140296042c40503a030755000c6084c944400e04003011070085800b4044003413035541d44001c4640c002c00004017184081800e40f0001c81b41c240715002806040b10858031b40b079030240fa850584c0010b0103500303a847c0c1c0201e0100381c02004401a03111071a4006801e034200303021030500d00c0810a00b4401110000c0c101000400c40c203105005903440503d5603c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 508947949 1250 508946699 508946701
    0x10b04061112071b0524090a2705100308070b040c050d110906100e04240905060f0d0b0720070e06210a111807051e130b0d090c1e1a03 59
    0xa000301c07d50000803a607500500b40480490007440440c5002d9818000505080703007000c0b0303d000d0300c080e1800141000441003ca00c0100f0108181c44101c0390320340e074000d28803452a6141d140c96903451121741c005c43d4019800c42c0a00080241001c030002880c1000c540c0c2d42a0ba5484c0300c2006440e04000c0f028000080006165034410300f09038008207400480c0014840c84458000b0442405844990084072480e840b0b205000703442c100003e00700e502c40d0301943c0780c1c10010080c0e10b80090300f0030041c02c0001088811002c0c400b2071310100040718408910541520401999020845500c00c0287c07422445414540070300c000015141146444408102000d002d248200c1e07210b481900078900542030300b00030181c42a400500d8a0f00c0c10741d200301156240d26450700300644282001c4181c10080c0080b5510410502015204400c210f00848400513441541d45400e4880c840190031426001094103020450200760100c403190a1500c8808204c0c00d0609240d031580c040140c0f4500506142c5d1401e0204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 508949199 1250 508947949 508948009
    0x50105011713020405102c240301110d140103020f01120902093d1206020705151806011508040204021e090307080303010b04061112071b05 61
    0x1410740e50b030010b0415006900d041c000d40110f01074820803902d0100100400e4410700c80301c03248aa840160280303001901004160001d428850b0784409002180f0f040e41020403000c00071510000d00d4554440680288028604c41d5008081c5400103404514182c0c20300845404074a40c4001e0360b8101c94000b45840385030703452680195034018041d459040c9050301d4a03071180c05a110000300714042c07440413000030030b201d950712501c4071000c43c1c98141c40b0f01c000004064180d0301c00c1d031031a101c0c280c0e200c03000308041c500c02c54036085009110b0712a006106005180c208401400e81070f10740d510451070a04581e00801d1644000c9858813424042c0c4600c034a001041c00150307602c03a00556900c2403026000514003100852014280070051140c031011903000912200c0d00d00703040c0b0a200060405800460031035040408401060040e170090104000e4241c4160300a0501003100c5160000c50382e0f200ba03a12030b16800d2102c62001d4070807404c100c5510f03000380028079081048103800108039928610f0381e85a450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 508950449 1250 508949199 508949237
    0x50706020d0525301b020a05090c2701081602030703050f04080307050c0310090f020f150408010c031406060306090916080115050117041203060b04090e1005010501 72
    0x441d03c00d035614019410b8410501d003c81e40c526540c4003003007409607002c01225400400704002054140416103014140e800140c072a580c501065540c1268a81255a40c1c1521003240c0c0c02905032049400701c04018005041d0742114160f01d40c04400e0b0781c2c0780410b941b40020095944440284480168410010030700800e2155024040300081080903d144c1035650038004d240da0000c030401d940c0c1d504020b88080203894104038038240603611190900800020303880d500f0004803030980c081d01503a001000c0009650310b10400529030b03010345c1c889644880c0c881543c0e500a18a02d40c042000c0782c03a14a181e2558a82121868400d00e00240003c0c55a42c1340000e003c040c440c05011081d16200d00032610110340b007040c84180280c2400400018070740c0c51884940850b6050b94001c070305005402e00e200a03040300c00c984095005801c0641c2d54003007001640300700c0080296038030980417081c0c082804220308a9036002500125415022900000e010303100d900102e80c020320a03903010803c48109060607c00c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 508951699 1250 508950449 508950517
    0x121611030303071d0a051f0801140a05060f070c0618060c0c150e150a030b0609010e010f0210090b010501031406100e1c0305031902122e03050706020d05 67
    0x1010f85422101582c95010071f00c10b820800c45058240f618080e0850308581c06a49a80146010480d2444078500c05003c80d4100c0c400303001d954041d00c0300107010b007041d074198001c407102c81e0780c003043c1500501d030307a920028044048100214042c0000744000210b141c423401000c00100d404c883ca02d41060b01c2c3c91a044064166045080103128100c810b034444e517600d400d20940441420a03560350f540e60344080060450b5030022310948507100c2441054503d991240300794451076000c2c2480e00c03d03404a080140d06d00099030050f00000c40c14110408200095003030028121442a02c0c180045445a581c09516440807106d01d41c005010f50001000648260120400700f1b5010b8000a0308200b84500c005010842501c00e6002c51000410700ca2400510607940c100980101401c43c1020385e41000c0441c1c80b40c010300600c2007103048000600840b074170740c080c26854404c0c0d5410640f51654910740691074030818402c0c00098012070003c42e2107d8043c20803504100007039501d21280f41e21003150f80034101d407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 508952949 1250 508951699 508951757
    0x801081515010c0506010602010204080f0102281106091b040b030d0f050f03010f03030e030708030307030b06090306070c1b052218060e010c030603080d0c0212161103030307 76
    0xa5110034102040713041c4030040c0a00700716030000d40d80703e05050b80d491801c1104003803041c4ca607204200031052100a45002c021600300e1038001c10700301c10fa00c2c80849480c00c0302561403189014100a210800a0001d0515108080c102814082c004c48004020495000b0092260113400c03101415003013074800c95644113912007a09001d8144a112103201ca020381090f0000044000802000d00516070055420300107508210020200d03a410711503056107901010b020103083c10b49601d0200c0007a951141555140480038084401d90315100400038110301200f8030039215212010743d0030010b004212190b4040e0780001d040c050404110610080385034140090301c2c411907030b03143c3c20278580500750304d503080c1030303034003a00c008920300e40141c0d0b1080c02c51351282c90380c206140c500b24003003000404020544500c0c6160080000d0800c510050a0307041203114641e030110040f0000f00040d401030616007a0113503e004a403174400c40c410310300906070b0343d1009075000000318040e030b00c041a20300c920081e442040c0b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 508954199 1250 508952949 508952957
    0x270201020f0706080906060a03030f0c020609060c030702090a1b1101140f04140601141002011b030f110c0606090414150a1802010f110705060301031101080108151501 73
    0xa500a2100c0b8181203158100303100190004040c01000030702002025003150080340c0001140c3d107984d8024001d20104614441800b02001d000c50541d0360f8282a11035441018105a0b510000c031020300b600c0760b01c0084124420707250309c408140044264881c5014421164044825149038807801341c0300080601c10440ea00e640310b20408440c2c1d140700020a000d0340c241c0011800d42d09040c03800c45042005004c252080ba407020300100001c40d807081078078400e50801c5d100d0305410105083c040b8054202c8100c4002c00342d0155070848546540743d80700c000c2009203118100f0001c100c0c01415001d0384540c0c01704002640c440d8000c0b036240d1600d2034a040e00244641c00344405284802c20180c00e203044c403000c030151404d04400700241030100e4020503102e01c805082180301d8890380da0005e00411309082d04e1004120f00d10021500c0e0313400401818000d0680100301c2602c035a980c1c0b43c8820042c619072211350001c0c50381000010a035030001040100e110848005015030703030f2400081c034403d55250079140d0401c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 508955449 1250 508954199 508954213
    0x20d033f02090a0305011505090f0709060503043002010b0d080706020c0709050403050702040b01180303031e090c1a0a0903060906020906071202010e0d120b01050c0d021c0327020102 80
    0x605c01d102e20045030a40d0090284d002d803402041000d01c09000b890390715001d400c0300400c5469070340b207881c41007542c1840c106203880b9101d81c204540380300d141c005112000c03d1566406500900036203055801e440d2294004c0c0946000c50040c491229900390004007810818090500050059000381c1460001380044580003503032810035200340c270802e5030182c010540018000701582003e0168510482080c00c001002c54813065130f5040c4500a40310140801d6a96024294510544001c0340c60715a4507041c207220381c122500b0004a08505071080c03aa0142503d44000201c100c1402514a080440c0e201c00c4c0d441c07851b58031114060032224604036142d50f4204102070241d901d02025024190158020502c139181d0070401030300315855501003445981c816a09142030b55030040c2180c00b00040f4100c007140b041d02034801650a8050b100c00c00c8898011140c641c2e200f50740c005010000782000640180c00032028501c19401c84000f241d41e011284002c3d0b80c20483c00507944103000c03440f44184110707010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 508956699 1250 508955449 508955453
    0x605010e09032b09020d03030902010e0d0807060903120e03030108011b140705010b100806030f0705130e0c06120a0c0801060903121710030b0105030c0d0f080403020d033f02090a03 79
    0x1b494403051000c41c040703503031424208103550740300f00c3c20300d194882130b03401c00161501d40c0c981140c1b5010b40d04000f044c2c50f0f1918030b024201482682230041050600d0f50500240ea6034225081d240c1c0c00034026498290310f0203940080c4055a041411000d841039100e00c000c0c1d20035112201072551025205849075074036505107001948410003d0b000c0007009558190142c28510201801c1155240c941c034910341c40f4071410302550303a840920b070403a20500440040d03004c9030644014202440580e025500c0340001c81c9850045c4114280b8074400c880701c0070104000c0b48241402c5d41d102d5800c0c042c0c1c00001c0c0500c181403000907071030341e4240c1688038941016080b48418104804610100f20b4810f9400803101100704104039400d08121b01501044001d80f81c01203c0f10041082c0324510b0102800c510321548016060180e95400c51b0f01554001d0028a00b83c1c03143e0501410030f42080032088400900020700c0003040101800c008660020050000d010000200b441d901a4000100060f4400046400080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 508957949 1250 508956699 508956709
    0x1306051005070c0f090218031227040c0c1209030309030204110912030405100914040c11030d0c0807020a030206040b09121b010c08040503121902070605010e09032b0902 74
    0x80200345c5290003582d54411035016854040980b0300c1180030b5030080d49510302010715002a20058040c40d2104645058003242003007034452600855500f280c6482610600154061a5002840d0003528032066003c445542103c20640910001e00003074001d200a2005252035002104640c0200c0304c6141042d41c0d42002884449003604210007c0e8400a0108070302d041c1005418040310003424000b981c286840c940f4900c11540c1008107118655980c00d04080d640194540e8404a11140440380c8948a00020400a04c1615295170104902d030001405842c0b0029841c1c409aa055018104507111a40d41c4025034001500300d0340704c1e00810300c0740303d488180b140181100031200f807203440089420740303510350031210000c0c1141d0400415104100108000104440c1401d855015034003444c0c1d940e44d1480c0044c1103901642c68050300005030300c02400085c2d00154169080501c1e020f00d162030b41900c6681d0b0740b081c1c070000c0c3d2040114107000881102c03e42c0c0100080f900030000850905c180d1750000d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 508959199 1250 508957949 508957979
    0x3050715090e10062006061002120a0c0204050c211518042604121502180102010606020c3d0f092304090f020301020307030b1306051005070c 62
    0x3c0350684200308649503109103e0158458001c08034000b114400088a032608802000c3d1402440300e00e945100c8203208004a010941750300c0c92158490901c5040140019030280050707102c0c40c10714012484031000002150150702484030315541d46041d5420344502100e004242c0d4030301c401a10758825054a803203403000b500801504001d0782600d00761500a00203030030007401007031002080080800320907100044500b91400c05402030000807251400119540346d0403c000d88050010601d44203002043c10851421582600240140ca48520f0102c2e920300103034000d29800b4240008240802040c00a200c40601c124595044006445d40c0e0702c02c40144030000c41c40c0000d0001e02880001c0342d010480d4000390400031010301904014074000150880340c401050300c00c9a8510b501010407880e44c0c088500544d0141c025500c80ca40b8400142c02000d01e00c0d01d15007e0b00c1c0c0c450200c00680d00512441060714001091144015812101190650020601207030a030340c0524000c20a038110020030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 508960449 1250 508959199 508959211
    0x50f07080417220e01050f0607050f0a061a09070e0d020103060e360d110a05120c160305100e16030b070e0316090b01030902090a020307080606030103050715090e 71
    0x720340c000c010b444650310f514860b4442c0130903145000041c0195544d488001503061021a4600c3d100d072100d081c030074104412903600100e1441403002200c02c1100641000c1548004840c0b8054141c1e00300c814044091400c85070b100008203011074000e05880c2000780000e11034010f00d4006242522441041958001520766820762085801c030041d440c7e801030b90b0141c42d445000c3c0046442e00c2c41e9551103036240c01c90303000e101c1806002c840300c1444000420488104d190000200c50410380017564421072984032100c507084602403444102900c079030007030446086940c04001048240702000d01e400083c071010107188110b000c0c400f034800c0801d001c1396048001e14050301040d0100d080906015082040040380c003030081e0030000304852191808010314040f5102188003080c81108400100c00400c080c02009500c035002600b03001a07200d00e6405103119520f40d44683c1580e456540402c02103020900c801803041c0d000c0c04080c0a91200782117540320058260805141c031640740c0e030300107440040448072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508961699 1250 508960449 508960477
    0x304030b040c0f0b0306040504210f0201150f0b0f07150b09070f050a03051f03030206060a081c05090a030c0b071110090e0c070c081f050f07080417 65
    0x40c84288003803080c2840082c0f08500d02c402d00c00d4a40040909140001401c03188907968031000a401d004011409030140d404c008800304600c1c0306d10b54003808418444001100640c0707040042d84260319110240030075240348011100c00640b501800c403106611408040c1d605843c14000e036000121341c82540a2903442052010070115030382410301a010b480240b141d420803200c48848034107541c10100b26149140c1c14030700803c040d524020481c800f41c5200701d0402c071441c00e01c003000040c19030204603140184401c8035030b6011941e6811801c2e569151000d100c07600002e0405110021030301406c02060009005001d0350070869403500c903200c200c0790030b90118240d400000f41c2e04c020040c03054200f40b00000b08a03800c504200c24084010b0024201d07000b43c4003212000c41c0460440e485c04800d8900c1d241d07100090703602c80c54540112644a0f00d041c044010424464075140149000c0e60140500c036041c1400704c810303d0350703c0c2c0b6002c40b0001c00c0a44240d0700c0024030880c403680341c52884028403107800d41c21a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 508962949 1250 508961699 508961701
    0x609060807060806030102071a070c0209070e012d080702010905014107050903010e060109090302060a02070b0a0c03020c101a0303161b0801060305070f0e07020d0f020c030304030b 79
    0x3030041c0c0f000c0340081505100307920400c410f40000f052121100200c00c40444400740030754601c031080d9140c130307412040a07500c03e00341020020400e911907000d0100000070380c0d59840141483c4044800400829008407415154030604650140b10b241143d50001d114400400c081c420380c1c032160300711010642100480c480c1d869414042c50841c410502400c20440d5840c50503810301418600000c4000e000d8204011002500c07a0a03503400350094501c40d001d130300580b5403d50b902e4020302c005000000740cc40150240c000002c51510081c801e41d2500c03a00000305547c40d0380d545500c20000d1001c0e07881c0070b05041e03082c4400040f040c010044500e40703000724900002d640c440c00d03d90100000c0c07480d042c4c502c00e038410018030b40c10801f070b2a20240450340c030015442c5101106d80341d034040c40d40300d50040110b039071a000d0004140305001807c8001c840708002c0c1400039079110448200c405000f182c1002c050780c003030300000038801c0c85001c0c1d00c01008407610540704d04006000011f07045030b0003927106540c00000787c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 508964199 1250 508962949 508962959
    0x130b0a0b0a021c180905090705060f04050418050304140d060515010207050d032102160b060114030114100302191d0f03100e03160f110405070e0d05010609060807 71
    0x3d034042c40c40160780c0c28840000c1c081003040e00c00c010b00740c1c092000100c1c1c0300da02040c1000c40c00c2141c04042e00c0300801c01074940410300e501d64120340081c03084c284558101001c0c0e602c981410f101c68110f82e500500910300e0b082c2031242000d0060342d010211a04902d040c04510301042c40792080380d010703404400f502290740b0038a500081c5003482d1508224400c2d403640c11001c0010b50010031110000450070500c0038824040d100450007800b545e18545041d21161102c5000c000000c47d1891080000f6221316442000070810503443c5e01003405481c071200c43c0380a902e419403414818100c241040361030090300e000c1c9004040c5c0c1007071078011044008644d48041c0000414449000c0740c80340a41950a100380c9507060001a035140c00b8015041d61a5986103840080c0c07010900031a0b00a11031021881a03186d26481d03d010146455201030b10100115048403909141601070356019104036600c0504880c194002c00c034030388500b08411201503585250009040a190050b10024102c40001d410964542 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 508965449 1250 508964199 508964233
    0x912082d07060b0a300611121b0313021914030c1503010521190605060904050705041e0c090303020d02010b061911060c03011d0105130b0a0b0a02 64
    0x102030f4180c89410034010070700000c10007a044d4012180b80e144036540d045444010f2480300001c10801402540c03c201c6003004440c42c1c04020302070340d8080c2450740d0150342d43c1e103c0c0000006401003440c100c1d031070400c0454207a400010868860500042c0a082000c441c5130301946012001e41c08803807508005140c2c0070241c6414406514180400d40304200d42e910302c080001c8240c0710500449101d0414604000300e00c514045003074107250b5004040380c0c000c00b004492080d0210207004102d03010b508250004a4070f0401021242c00740b50700c40d00400045052801300005000b140341c025404400c506419908440f0310b0040303001e901155116803001c0b03419410024201740f00e25030583d055a0419450b0101034840c503045507048404511904c4084440d6541195031480400282400348251002c2c098900500c0001f1412a80c40d42c1e5907011102c0c0c0c41092180042c4248500d03070344045600d500d1200110103400c01d01882000a00b40c2e1009a03c1c0c01e160005a04180c0100c1c0040e4410044103d6080d04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 508966699 1250 508965449 508965461
    0x30f031409060a18080a1b17030a06090b091b2a06130b01030305070f15060503070503010b0d0813050a060309020915060304032307080d0506010912082d0706 69
    0x40041404840e2103554030740c45100d5140302003004502c004d120364202d100e1f07140c80095100f1000005550441c1980f00590002d80e510402589000000140c0c5007684c407842616010141250589580d041d00302100100c2e221420441c04904019074140c0f9510501c0d4100c43c000e001d845800b842a104822600e404030043c03400d080300028030700c540003160340705a40300d0440390306190080e82c49805141a058480e8a002c1c01070400402d450002c0710000c60350400320a0355810b0301102c410740d66802c101802e8450303640c0d4680d00301110541d1200418601c44c020095910300b100d000248030f070741c1d6000c180d006075107078480c100180e42c41c026941103261145038590000010224910045104400100d641c480504010705100480c0c031083d2442500c1344442000040f00c0c3d1855032500d80034180780a065004048030183e81e0325200c0011a258081c01984064a0506d01050700070007050f03892000d00d500400d1083d00c80e095429102e0b0b280e45011441010343d011014529850302c50030318000083d00c0f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 508967949 1250 508966699 508966721
    0x30510120f1a010b0313061805060631110c070b030703060b0a08071b0203061801050108060c030408130509011403010f2a09080a08030906090c0d030f031409060a 71
    0x2c807203030040100c411058180c0703030480c06600716615200799a1520b0303402000103151481c1d080400d140c0d203e05104000c16071520400c0140d810306000078040000c0f804840141d28501035441c0b0407503402040d800d06600000040c85510815803a041c803400140d464556541d00c480c0088000004000d100303641406584010700e1384040c668200460b806018101041c02010a420480d1805121160f0300c41e031440b85c00c0c40340d006015a0a076060882034080d141c4106d0000c07600d03e60a03c400020061b4000900382e2154483c140f10508503102c40e035601c1c10951109510106242c50ba200105007580c0b5503810358000d010340441c0d8005042044207060950341e01101c200c02040c03400e802a0300c0604660000d40030001024203060301100c0018041d41e40c0901c07500261264030550080c03a081040d504001c41c0240c9103001207810669a1078031040d0f03903400e28042590400c81c021000b030700203801100040e0700a113480c2008142c9940903a4a41c8400c00300300c4040d6800c0c0d0fc50700c28131004034410320504003100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 508969199 1250 508967949 508967993
    0x9041103091b01020c0d1109010906080c0d0f0201140f0a0507110d2301020c150f160e010f0e030607120b0d02013c030603170910030510120f 62
    0xb107807040040d40761440d2140c5103003d1007103a4030030307420482a683c2020710f9004c014850081e86d41c6414081009004902a440041c41880704100b5186400703071650034150f07404803940070301e40469070045400090310483ca80e01c0060503c2040f4030140c4100107042c140c01030b951906e8440c2d129062001604c012480d106006030005085000414100c1440881800b003c5030041c0803034807907040c0c00e070080c46102c0d4140c032a0b002e00c04001010381c0541c650580218141001d00b61251a64201d418003c081c18600700e01103064041c945071603501500e8828a00281d41c105114020f0301440442c6c281001150040001509910729183c03030241c920580700c3c02002030743c01030800c660316400a04540307000c0f510080c050015480d400c203030b5000301c944802d503981d0181e50301d40a22081c45003d40500160701040781c40d0540d400c0640d8100c00080e0a03280c3c010f0005010710102070607140e0680060501811403141c0401508000c00ca00c2d041c00070198403d40b040281905480950420309020091442030741400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 508970449 1250 508969199 508969243
    0xa0210050c0d080402190306051e07120e0c0a0e16021209120309060f07060f02070f06050901110a0903060609050714030a0b0d0609440904110309 64
    0x50300005081c505480302c0c2c2070003d8192502d000040202442d48100040c0f81a4000c003c010413010f0b40240380264a201c0708041030410f40c000b078000b0000111445000100030075074000c008030068101010740441d0505580c0c0d50044070000c280000da07143c01500e40c041002060100e071400c20040c40b619112284045c1c0350030426825070700c0a92055601141c80f03a088440110b20341c1c203083c030031102160307801000b06544510318014104246c01c02032003911002d107401d1140d0194400760007110720241e80103412001c00c0b03105a0b95013000b080d01a0007a50323159030754403090441d800b102d4001d21040c0303a6034071801410b9207145460340c203860043e0824804581481c00f4003500d283c0100c01602800155070248e501e179602d8050400080c030300e00d480554406003907445101440b16a51041c94020301a02020100003140c6a241480d0ba40c555017600c501d0706241d0700080b03000740640c40c2803d00d201080d1500d241c9011280001c0a4401004c5c100c012502c000080c085956000c01a102111500030340f40810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 508971699 1250 508970449 508970467
    0x307081807050f1306060e100804030206042d03110d031103010e0403110123221b0801020c010506090f0415050a0e011503020406060306141507050f0a021005 69
    0x118041d5100d40c1c0c1c09818070400d000031555903401c01544480c401c02c01040786503540c58000b0040c0ca541c21007680161060300c1c901a080c0e02c01c03190180f00700e415030001c00d0700740c586a0b00d24001045400d05001240603000b04030b040c080128044150007406952101c0c160126400e940742402c0071164114149860185410100c0550340150380c111000202c2d5046980d13651308041e210050942d40d07110350ba5281c00b040940f5010130059003c0115841400b0000680c1c0b01102c4c0200890304203c0c001e2058160255040012031a001c0264081c40740c000300b00704103a40d5001a802d90f00103942030310483c0d45400c1008614101039403c10744c40503a000b816201d40c28951110b11512000f111500143e5889400013650031605404c1001c440381114000c000462100580505450041c00103d00c21409d180b0700240c40d074445d00610082e00e044000000322904c202c004c00004c808036030400e860704172090105d240841d070705121710300228074048050106001c40340304010f442008500d0140502400f8402644 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 508972949 1250 508971699 508971703
    0x302150c150601022d0714032e09140f03030f0c09010c0b0703090303200a050d1d0a030207061d10020705040507090905160203070803220803070818 65
    0x80021000c2810074040e40325440100d00700f40c400b054030340201c16071300e100c040c02d2a011351400221203403100989401c1601d034103181e81c00e02003010702c095160380818140311021001855445030707002c2e041c02401c07071a540c03030009109440d407080051b5200720f4103604808240d4020702c140700740a443c14000e1491854038600006090102a0494400c0040403e841061f41d02905400c1980c6800520011807840d18500c001e024082500040300020300f002c3c034001071610201c1034103000408103001c6608142003c00107c4d100d07003081e83c910000c0758490b0480c020f1101c00e45111503c003010b10300581103500712410043d2804105a2242040000898000c60030000910030031510f90004c84481500442c201070032490a10740703400c1154001e150a051200d455003101040d01190603c200030700041c2c0e905154851002c41d00d03a54400580c00821145c000910118002c41e8805501c0c2c036030401060b40f41150217032965074004101d900c1d050002c1032220380c6412405082d400a40d08503a22a4001050f114503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 508974199 1250 508972949 508972963
    0x20f03010516080405150103080307180302060a050c1203100312020304060c060915110a0f0c020a0e1b0720091512010b190303090f0b22170105010302150c 68
    0x340810000f08041010800300f80003c003181d40e0988100401941c417801c140b05ca0340d00582e94180405e41c84d4585001055048103143c0c01c40e50010502d0382481d040001c2a200c80d80200034490041c0103804804000e00d080d0005140070700d01026003a0402d40c1140341640d50004a50018030035540f050004210481c0e01001030203995902a1000c030f076104491070110550301e00d0001c0d01e11058107291680d440a504003014001c850003a40d00c001c040702200501313486c8548100c42c041d412200d030754828031400e404c0f500c0c032a4105954046852004641c4070310b104068016000c21924400e01d034002c03031030704070b10740d816602050412034564405003850740c01e032040c0d001c1c0c07002494007039980c4d031003400410310007984075100e40701014095104001c1c0c44c40d4070460b100c009000c01c5011503049503003c14428101c240c10001d590301183e40c203280c0600e030f5003450b00b101081d03000e80d560344620401c00b00b000810028031501c203c0d4030f030700017107441d5040d4130401541d4020351104158101e024010070800310800201d10f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 508975449 1250 508974199 508974241
    0x3140f0f150a0b040207082101050a12080313050d0302030f06040e100906110d0b0a0b070309061407080409021207020c060403020d020406050402030c19090302010905090718080a020f030105 83
    0xa003003440f100031501038000e80d207020b4000c440c049007240a02c0d10602c20499240d19000d00740445a807241c0c200300001e82203018100b9500c0503e1200c03800208000d00035600b108004c41c2c030241c01c6929580f107a1500c05100790a2000907004070500c1340c150104440305801c504200c03024002103035a000e6580c0e483c1d400307420b040b5840381c640107401c00303204d0a82c0c482c02e290f6000c1c00089944205480746200074000c0502054040c1205200000d02c03c01e0307600507100141d500d030f80e4040c1003d18003041100e0f0f03070507401c014050b42041000140006405000180000e044512016031a0b081d004526040c803c0010000d0703040d90011511001c203691980111800e5079811640c1581e185060300101e4000c00558000a07000342c400001e0060242c0f804002d0403c4440074403c0c0c549030401184100c482c2000b03480024046241e144003403010b0326020311269031011403403810307000d00b690010200f00504046d0f0300c5410540c1000c0e022106500f01543c6094402c60260000d0105041071910154001480350b21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 508976699 1250 508975449 508975451
    0xc05210f0310080601060c150c17090f010c030606080f040804180b030106090504020a1d0a0903020f010c030e1005040b06040c1404060509011e0212030c0403140f0f150a 74
    0x5030b21a03101d0032074600a008500121101980c5414000e480030249400980d070312030f80e041d248400c0180da800307003500d8609580d40700e8a040d0081c3c04080c84800020344010828042c030140c1484242091007402d000001940d004225036142650241550a001d01400c0d646030032201080003051502040b207048460034480e03289a41081b058020007004000840d56042d401e0002c0012000c80c950407040c02180215886404c0640c0c441c1c5a800d010482a03a646050b00300800164010724940e03c0300340c1c00b5019005550b204441164403038212505606c41e80082507a44000901c240002c00c40c401e0f000403a0380c4200030301d086c6a154041c209500804081c410f545a400c000b440781c0c0302d00014030f20030454860141d142ca8440a0141c5507030070101c0240d0000d0701e900381d0b05c13205015114042074030100a4020b44140000c0c1c0c40c9400c10b07a400180b00d51951901084000700040102c4108610000010060410300300303200320450810b850301444088035840441c60802c1c83c4903a05e802034121100c414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 508977949 1250 508976699 508976701
    0x6030c0f0a0b0730020715050f03190e0c0d020d1b0b03240f0409082514010507080f0603010f0e030702010f030e0325080a0c05210f03 59
    0x3400103016030300448001d45000c03c007201081828803a5241003502a0210040c0030b0f1804c020b82d08a1800006074001640308540401105043c8440000c4007010341c03500c1803810445401340314440c1c1c015900c1072440c90ba50707003110f0380303a12003403003506154103608001d066410000c1000902c0c98890340c101030f100d080150000c2e8100031405001d84504002d21010001c02c0350f5807a0007485c076030421280102350340400c81c812200b12929080c40762442000408120031040c118080c80300500318118102c4203074a0400c00f01207101c04000c544170303078103084002c0fa0aa000c1a413410200c0f4606040316140280e04200c00d104186410203e0300307030f004411141480040d40c40c0c0002030301601e400480c40002034900340c2c0c4a1145c0001000a1140e107000b80c84000c92004101d5045007108c0e0350401d011407980041c0045803400290f0103004025074844003904c0c440201585034280580e20000b41d000c08109000700460420806100307404010b000c1d10501c1ca02c0d0348858603c4c1c681841a510385158a900c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 508979199 1250 508977949 508977979
    0x50d0b0a0909052104030c1e050a1e1e060f0c1b24050409020f0d02030108060105091b091203070f030e04060902031003121103030f060a05010806030c 66
    0x80e00c000c161070300c07041c4800e048508085071039500f0015a01440c5140f00c0c0e04049400d51902100c0c01c07241d200700b40c9401c0034034002900c0c4203000310060f91350641320755800005190791103440c58005024004102e00e6100003035000c078208401503070321101e58003500d40140403d800d85020030b541160014204460b42c0c003a1080308070340d942841c003401001d400c16052405510f491003c01c41090b214a008101d100c0080680328100c2035241150950016008020a00000e44950068003c13001c00c02c41d00c60034991509810030907600309030482a90340d032200c40100301030301c1d09047c465044440008443c00c0009114a407d81912481c41d08e1405a66002c50b41d4001803010422034810036080110700e00890014600184000c240c0300010307100b10300303008001c039100340503208890045401601c034000003072231079845000700b05143c04448117000307003e1203054000e50b041c0700031842440c80c001424103524044041000f40a200c0c1c006134104410242040100e80b00095005400c0f1005c03108100500c3c504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 508980449 1250 508979199 508979209
    0xb0703031806020f040e0619140a080604050606150f04210b040b04061d1b210c0109060f020a060e010e0d031406090601080a050411100f1707050d0b 65
    0x1e8006001c2c900c00200740e2444400c440c0039206980700c61021a889403a01130030400380d2a036048030034a1288016408100725440030782100c03083c1e140644038241e00c0d03503a4280d50342001c50484090340d054010504110051800e0f002494013940e40c1c0c032115050454208403000d480c0070b240500d0540707501120350365042d410403c00e08c00403240c3c40720040141e440c0c94940f440d1181e50a480480b01c460074200c80002e10143d0780c0d0b1030200b82e04160010180040866450701807603446151198102c200c80c50a60244040d03130340c14600504148004000c1c140e0100e000514511550744440200048220a0701226902213040326030300d80c004070081100306500e5051401800b103210307000e10790b101ea0b480141c6099059080140340303060a0182c01076555458043c44010441159254002100500050041d280d1a03100580141c0a650007142401c414008983c4612490f8412400715902c03000542015500807503500e9008251100c2c03240341d007012440940035001d103440300e210b0b054550040312029103030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 508981699 1250 508980449 508980491
    0x60507051506130207050a110f0f060d0b030706110712080f0c010f0c091805160c0c03020406030807021914120c270c030103150f0b10020f010b09010b070303 69
    0xa8018119a6400d17a8502299940c0c045030049921304444c1c0b0100034a0303d0120351010603900301902d41002c0c00006010000031707620004c020501280d42c2c00403a0b025407000c11204002d40b1081d260802d41c03840029541d0720b4490940d10580c95040060388403000281540c00380d4045404284202e07807100080403180b4090b0a41c0905421000d181a844621180c2c0c814280421241c10f01466003000c1a2901108195982141c000007242a0b005005103c5031041c400540128002d9603038220031900c9078000340503558560b00668402c88007240b100c0940c078152420032a22800c650002c0505440c110032000d60035021410300e0704c11844003079038104590052140e4403031004002c0141929424a48924906c10307654040d214041c0020800a13103c2005001264141c8bd0410074960302803811030101005040300348125103e41d83c642200c0030b0982c41c0d031180344814a4003034020381f80c1039885000311800c60b1f8800f00705611600e00742c1c0c0108006c1c40301e0b0701141c3d41c03141c00d8a008252040051000b9403070b155 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 508982949 1250 508981699 508981729
    0x1e0305090d051c0201021801031103040f030c050607120c0c0b01031b0b1308120c060a052508060f0d08030c070303021b010e10020711040b030c030d0216060507051506 73
    0x1042c042c20f0141d00340e0641c0280710000b400c4202d0341c20003001e00f00460454011074040300c0c444a00300041030210b4201d0742628103861184c81c056401c0b007007581e00c090500c40e0542c1c2070720224600740c40d181400301250040b030261161911708100507481580358024032020610018000181c102070001c0c401001e445940007400c8154a566907548014141c80c1080407184920340c03440c001c9074100300f08200c54804895040501c0740080007aa2507484a14000780005404200300d107445008898130003c101c0748445c0c43e1101e0b1b03101c20006240c1007003407120142c420b4982034440d80488100e000010510f0342540e802a07140010b03d5226030701864140e000341b01d0171500d00011451710700c0f83d555003901504100c640524501c1910fa0786406070300e4000503400340c40401032041c0c5600308404101e04043e80442240080201151612061540402d0808694480c0c0c000142c02c40605000058900010b201c0200850714095140400e191030b4243c640000c249030382400510360740491110341e60348454004042c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 508984199 1250 508982949 508982983
    0x2010c150c0e03100e0d05030703090609080702040518150618041b090b0a120c180212010b0901020c061b1c0e0307080d0e010210020301121e0305090d05 67
    0x18464000242003458070900b882c1c400e11801c422104401000c0c0104000e9070700f410003d05030149a414140d41d035400092130301c400c03d562810704034085001c0d030090b1a00503000c0e1006a075190745900501098900081041d1100003143c3d140f404070b0b400004000008006078035032282c0766100d0800041d6881d07800c1c0b154000b0660ba0006010600080442c00d2070401c004000300701405549402082c266605218207a81c400003a810403ca00c17000148102165481800d600a03042d0316000f040c4850700001d0986690194007040542d001c1c0f2401101074050405000c816041100041c0001e41d02c40e0700c2d40200b80a1a03000c81c00d0302107880404089040b41c6900c400ba00c651005840450119070880c003c7e070400614a13b980461508001c103080e803c1c0da06880180601240c131040540b0349440c440c18150440c0300701a07040802c0c812a00c080c6010704170071016503e154000f4206102e2100d44007a003009028028128040041d07000380c100c400300d5000b503074031011211039420f0860a2066050108900b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 508985449 1250 508984199 508984211
    0x203060903040602060a0501080c060d1b02030a0e040b033007060b04061707050108090309030105040503190504060507110d0f0501050103020913020109141504150f0c080702010c15 79
    0xe00c40200c0640300ba680b1a9080318006e0361501c1c10030007030340e02c2032107191003039088100e4100903414101c00038064030065010200e8080002c44441711001843d4069800503000800c42400c642e51041c800c442c241c034201c0c0c0502c1880c1c030407000a07450300c1c04255181e0504e0030170388208040303101a281e444990417113a000e00c2e4503404503042c41c1000e08176402030f081c404c0f41b410b0313008140c000c8100c3d000300541d0b01e100c00a190441c246001510b01030f80152a000c05c078071040c403080030300d60b40c00d01032584a40d2041001c3d60300c8841000104404d0034001d0201420b014051000f03000950b4024280c2d01c601c1c0d08813034082102e0540b0400305500105115018200031816410b0100340703d415048581241d00c255a041c24a613501032103500c04845981c40240012242c41c1b0810003501c00d08034108038800010209202d00c0180c03c44040070b0b03401903020b0705800310848507100030071750070008864800000d42000404144581d451085078840c1c1c1384003c1c1071104484101007800a042180b885500a0003810031407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 508986699 1250 508985449 508985461
    0x100f080a050618070c03230706090201090801091b1505030705090109090903110c030303070c06091109011e06030c0f110109081611030a0b010303080c07080a0e091302060a1209020306 80
    0x5d203013140506602144c8030b9a2035048141c0141d0203490a945900626030a2100c25940c1350050301e4022003d9041000c0c4110200d4a050284203121001d4494135015110518410016031038030480d9015600e80e0080c1e501d81c680940d0410f0803603502c4546460030903a58810000141c52006141e00110300c950b00e4514640101900f20282c0c0c94100030076001c4414980d00301c03041642e02d220172030b008070000d0300c0d00c807019000803010342114010f1442861109980500000441d611400907030080e0a010001040801c880c1c0d110308030364026204901c0e06128242d0400c0000e811410003540c2c3d042002070401d584a03207240294041c100d0240e00094240ea40c410300284180034691401c4240c8aa11032048041240c1c5800204020915803124030102140e103561025100d1500060403050040d20800a100000350320f00010b2005400c40d07141ca9802941440070300c03240407001894510b0b0310006035a08000340ea204001d0781c00e03541880c41d0030358900b44c9403a00b200281410040082d0548a01018007003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 508987949 1250 508986699 508986707
    0x60501140405030d232709061c08160b04030906030515090a020910030f3206061c0c0311070309090e160b0901020610030f1101030e030c0705100f080a05061807 70
    0x440c807640848103942910940e010048044000d503042580b20000f0f50603201540b00500400c0400b2b802201401d09151540242191208642c441181d1031000501040101908400000003070500c916080215180c00c1481195105e0b080070348134072441d4540300141082d5542d8040791020900a004040080d400c028040d01400d000301403090114180040c0d82c100c403004950040c202001106904210f040c0714080c40d0b140750000d000301d600720004029001004000ca160011201c050060014507015035580040444600c0040e00d10440c1041019401103940300141c03a0548030200400201031001072805460014841002400d5280d000400601e50000300c000d024010801e8080c0c41540d81c41d4900102d01300c150b800000c0c101104a43c110011034400c0440e030704190410704000074000c800c41009403658004828502e0030b50304c0302d00103200d2401c01441410000f152400e000b482d040183c0030151403240010410385a0030b40c3d45001881d01c0d52200c0405449800f18032072101c0a041c8018020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 508989199 1250 508987949 508987987
    0x6040e010e0f0120090411040b04180510030339080d0c020105010f090f020f120711010e250f06020f0105070c030e04020a21060501140405030d23 64
    0x1d5103415180c105024980305101340030610072568520b00b105034010040140180664409032590500c0081085602600200701800081c0e0000a01d50a5540351106980c801028040e500715512020000a50015110300d02400c48001640b44803c40200f0b046507032500c900210b18192065001c0018407103c50b00a20308a8600f40051050b8103074601c09900303942081c490b1011242080808101650041e03102c0007400c800c100f00545040d81041550150387c2150542c100c043c2d82030700a00120f142c11504503114505481c00a014a4048c207920702e44a5590007403902860241031100e280c03082000e040c210190220000250409885080c000c1d1f80c0c81c80340c40002072562070302c40442c640500640c0c4900507260302d07507200b565800c00c0303205100c06034005001603024408012413120783c180b1130180202c3c40417000c078400202e01c3d142600040421902c20004080302100304030a0144c0d407800714064107c1402800c0104000308200310002d4a00404a030f1b03e8440780c0003148201e80070010602d50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 508990449 1250 508989199 508989223
    0x10f020d1d0a0c05012106320906120109080705030304030f0207080a081b0a060e120903060601140d06060e010923100903140109030810140906040e010e 67
    0x55040700072400d4460399500e00d24000b07000821404400c12071503205812040c210402c01c024450b5040d03024414000359040c5400980c2c071000030020030b1004100345401d920840316075280740303508880407034041404140040c0045000c0e00c5040015400c8242c250020900280d00110b8269a0100c80c10710b44d80729001514102e0000b08a440c0380c2c40350f0b5100003451411348901c42c01400e12001c07507940742002640102013a000700b5583c00d07480f10010b88140490f04106002e840040340995903c01c00b80c2c10005401d1036040e90320004c0c01813007243d0b100000c4d1039a100b01c003800c001c000c00000140802040c000d00080800f5242044230116000f0f901c0704146581b09004c0e290340030101c0c0c5800c03000c0c0200c002014820b02c02c141c0c0119154807490402c0d0742c000e400385c1c1c500b08081c01988944901015030b100c0245034005030b4641c51080300301907000f40c071203034801102d881116101b8106610143c84494100310988684500408503415503030b2540006055080d6000800c124040044915201c18159002c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 508991699 1250 508990449 508990481
    0x31e09040e070e060d03031b02150c07051504020d23060606070f030804030908010f061a04050a090902040605130e10020313030c060f05010e01080d0201020414010c0203010f020d 78
    0x95440400e000040242c00d0b6005031501101c1075030345100780726420540480640815459841d5100c0e038a5141030b14025076000c0da400341007001c0781c2c0e0b03000d01042c04010b84841401030040001502141001c40c40000501a008041003261200d00000c2c240c00540c00703000d082d41c5503420044072580c01848181c5001c10003032059481950b10346041003220b0048a0024142c1c2c10303000c0007000043c1c41640c04541c030500c6418036961054446134040d08581d1201c01c2c9070400340ea1908140108036411200c88038035456040b00a291500f0b180125001e00e98600c908105103495030352075421955281c010502038000500050000c13490300a110340a4043d44081e0744250107840d82c01c00101d00c40e030003103034440c0c0074001c40380044003120354003110a02d200c0c0e40f09449099484071801c0b4070080e1400382d0ba00a020b031013041e604650508104a0030040d403031068005680c03042004003e49203603240c0c0540010000d003094841091903001007400750640ca60a8102144001000391000c04a44e00c607028407000100703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 508992805 1106 508991699 508991711
    0x307030f05100f050906010215130204020d0f0c0e06030c0d0905070e0405150403022109040606081503150109020309100c02100f02120601050c031e0904 67
    0xd00b11000803821004111006510000300d002d090201c521041508000f40041c1d520ba2615205000c1d09140000246a000d0101c0e01d4615450b0041c00c103541d108840c00305000200300003c08011030601d844d00c101d1005100742075110b40048064190f91850300c0300c3c003684416412001c2c2902c12541c4492068000640030311108000f0910b0840480d040c0c101490624149526172841c0040140501c08100110354001580c44400c2500303410b5604c2118034000440103403007a90030880c0c106040850002d010745d40500510300c200300000840203c2544282010b0f1036042d021500078100b00c0860060040c04550781c02150016111421558040d520304803920a0380c1c40c0c00c240c1400341c1c00c100b070705501c1410140031306d80d814000b4140c1180b6119043c020344c644c412000e403030b4a04100010800058644d0200202d45440d4101c021a01c0b0012001904d108030380d10284d0024003641c1021 = true := by decide +kernel

theorem cover : BRFrame.Cov 508812949 508992805 := by
  have h0 := BRFrame.cov_init 508812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 508812949 ≤ n) (h2 : n < 508992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
