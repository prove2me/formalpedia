-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3771
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:37:35.546015+00:00
-- url     : https://prove2.me/submissions/ec26e027-9809-48c9-8671-6a7fa8ccca95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 678057553 ≤ n < 678237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 678058803 1250 678057553 678057557
    0xa030e0a050a080a0201060b0c0c010e03031605160605070b18011d031b07030b060108131b080607170a0b010e03060a05012408070c1b0b03010f06020c06040303050307 73
    0x39002034031074a040c00c1c0554001c1c0d0754000006521110180e0920a40c1c00600c1045070450429401c0802c05403182c000d03212040c1045031102c4445801c0e5014803c64404d80802103008000380200c4c070b4450b4580b4000300d00002502d00540c0e0000e9a03501a60441d480e50b40e00c80ca5403103503070b9183c04601074804113101907003074603669650b401d074581d08075074041c0e1403070202100c011611180d10060010a40c130795030509c85601d8011800c108001040c0308161780c0c020100b42001425a03486007000b00705054000405400601a4807041d440c444100344018155602042131383d0050f1358031941030b034000900300c81d00b41c0d000d1044030006504080c5948600d2448a05241c031460880300c1d01d0000c1c0c500341055030041182c0c0e40e40c0004110000d10242c1842c00c0302e0075058117420350100003d000e00340b0b0704000c0000c0c09200c0302c150818200b1110707006103900c030181c0348810041c05440701d00d4005260000d0080314862034092501180b035600024810009020060605141c0350039641e08541c40d81007d400b0a003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 678060053 1250 678058803 678058813
    0x9061b051e0d060e01080606060f030408030403051e0d1a0d1104060b2b060501090915050916030522021306050306041101020c040510140109081501080f030f0a030e 72
    0x2d10001c2a0168800070504160002460b50400e9852410310401600726485028104136811410801500b920360094105141319120f58950405031258461040d429009a00480703212840740000806803558001d00581000860301c00c803840d0540e80d944501039940100320920043c00078100310350100280c840035001140382940d403d0945055009080901960301c58602404000150318001c1440d003100b44c001448803500e0100060100305050048001464484201c01c04003949420220010b241c098400c0940d45042c52091401c50040041200080d042c50042003a034841c1c2075403100f000034604500712020bc00740c0e00700300381c80a41011740c0758490344465000a103a07074144000303441240540c1c81080c2c0d043c0108002410310300341282c454840d030300d40014041d08407200f201401c150703109129507284240009005035003150f00c40d40004014441e2001504050b180c440d8540d0480301c001d030896445003402d00103280c40380160340c4a41c20404090002042c440d02ca90040c80d00ca40d042003d0718 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 678061303 1250 678060053 678060067
    0xc0e09060d08071a180304030c150c0f05010b0a05030604020612101508190c020a060b0d0c1d181f060b2701020c1e0a120609061b051e 59
    0x300800b0184021349000c0520302040005101e0400c2d081940c44d005040910700d070a0540c0d450325004910390107801038402040c500711049034010440c030200036401c003503a524010f80502c2c04034043c108110b5003034020b00d44e190700001c9c141400506c180c09154020012030514440d002442000c0200410904500e40341400004440038200d000460560b042d558a1043d407804a105010308640210121b040920306407039515415808122084005d5002c00e0218203405041c0000f02c41903146107000e03145007600031001410048a0440d44046001c1441e502001ea03a00c030340c0001d00381000c5042d030409030040e0844441001d80d0001050707076100007900004903d41c0b140c20004458000d01c044114248541417011a03071820106c0d0880340d01400d00c014465001c142c0c01164420440c1c940200c100c0d04004100600390345e0300700107074028000c06551540c0e041840d0070888047d00c6644c0301503400510b0704140c04a46505041d403911004203031749460f40f42481c0b000300c6001d00d540c2d0703e004482140081c8080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 678062553 1250 678061303 678061313
    0x90b16020f1e010806010c030c2604140f04020405010906030e0102040e04030e0a0e060a0306110c01021c0b0301020a1e030e030f04140604032105070512030106030c0e09060d0807 78
    0x400c03480c221041e50000040c0c0b5081c0058030640c0c0280c4140d05000c02c0c0c4204000003030b0b1040f0f1400c52181e220402070000c0c0c101502141c441600b14108040c448408a408100a5110900c1100700c50703003100d100001020520500040348509e00605002420402041c820a4001d070000d0082c980324500040c6000d6480c8020801c030b54080d038040f00040d0f00300503004881d240008d0004003500070380e180a1524100400040d000540c6032000401c4180c80700c8581d03010100d1001038038004a1b00c42c00a668070b498501c1840300c0000c18220543d1200d240148100c0740b03040510130b072151000d607501d880f1031a00c1070000a041c114241e0151000b05500c0c0d55000d54000c400780b015011200354070b2000d035211400e054a040200542c90140c070700960041c401080402e08051424928a10305485507a00c2048540100c840b4400c01348098054490019820141c0e203c2400441c120350580d50308004007080c1c038000704c4014000c80241540162110080350303c43c83c08074800d122003031140008a207440603d58031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 678063803 1250 678062553 678062569
    0xd050606090c130603021c05010509060d0507091419050c0711060d11090a0b0c0a030e120f07060305010501030218010f170405010b0102010c0507050312040309180b10090b16020f 78
    0x101c0000284c01158007018440b007c0b0040c5500400000140324544c14840410410240101024840c2d0100f2920b0024004140308680c094445280144024044900d80007a6250180c841c004060310000c4101401c03180c40c42000e0150100c1c2040501e010541d44801c04284078a03180ba07644404104a0100005900d100b9003805100c00c070b03402519501180b08100d140343d04d5601a240a41c03040050a1140a02046022840741d050402c01c044900007408200010354101c0101e80e68400c1e041400b02c0c0b04000038000d001c031a1700d0f58042c03120344e8032040114141d005442407800c248807101015051580901410b80f040e801d289007000e0114000e02e040c0910b05d5003540d0903500c69640d11300041540d64203026903550100b95041942c40c2c10070a9841e01e50340c1c426081c6201d00c1c40f200c40042001c1620275220203008040301c21822070140c1491108600078201e06400a2068103481084101c0c24042d620322021a000c4030f18042c180b490303543d10109155108030f070490340040d0002c07a014040e911400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 678065053 1250 678063803 678063809
    0xa0e0f061f0804110d020102030403020616080309061f081f023006090c04090509030f0d0e0d0e010504090b0a0506130e01060314040809010216060e010e0d050606090c13 74
    0x42c2d011203a083c90b0902c885200d140b03030115406001841c0d441030140c0d800008a134202c03541540c0c030980c0c4d00013801d0080c41c203208110004044010000c240070440c2400580c0318010080110b090040131000c1000c0c050402141c0324000e82508080340e0000500c1a0307464070100e122000724007600d0581220021414003031900000f0b03180707070340c0c41ca41c141c4410382c003081c1290b0004082e19101c0b00d909281300c03030380320034004c074460210700c2a00e0350001005001c0031b1065410038505850081e84500304120360300081d00354120500c0b02c0f4480e011540d003842d03100b400c240408110603150706107814146104000940324818429030400d00040b40041d0702c0c0c5540c401829514104007100007601e0030040c3c00011a0810b030b1005040604000788200d0744102214100d8200d81e000c1c2074070703a07203902000041c2e0821810340d05980e20025105d42c0081d07810307008120354064500990f100b40f844800d030310810004c1030710202c001d00a644400000b03580c50810302d20050304041801d0900d8248032214000300240780180d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 678066303 1250 678065053 678065057
    0xb0301060f150c2102100605090c1303080d060302030f01270303090c090c0f1409120c0a0b0a0f0c0c06030926270904030e0607020d0c03020f0a0e0f061f 67
    0x140000d88160b6046c402d0252004030140b00f846224030345000140c0c60000582a6502c1e801c0002c0e100f282c000a00c80c424000750381c008000f94441345505411310040ca540d20050780203000781000030200800621072a0081c82d0341c85030004040303043d0084104822031245c011020306039288000000f00c0c0ba504c110a0041164120120307a40025400040413a03082c92621414000d000070302801c5541558281c0321700711410366598200c0c90f0804481440c00101000c244d0b0045c11019000c01c0030400382c8020502d8103a16214108400c1d030080040741c080821841c05041003007000024080213109400400b1034070702403218203914070980007031b40b100c482c625028286022000917400e60620031520040c0c20711904000205152000384c0d000c07804483d4010f000408110007207002590b999234203c262030301103030041c0a0044c01d00d4180781002d8102d40c0c03070000760711880c1507584018182c81e01311018000d65004111070b44e0240c480f580076128a1202a11140d881140c2c0e6400380c240c00c1c0001e0800015007255 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 678067553 1250 678066303 678066353
    0x504060b0a05010807021c1b050a05120f04050d060b060a08040c0e0f0f070908030c06100b1c020c031c1b03060b0909091905100b0301060f150c 63
    0x145040210705039560380020f05001c0380c1400c0003011500070800d501c01113a4140c1880369144001401c8500750031554841d04232200e103601034401e00c00c1c00194028514440c0b0202c075401981e8901003142401000000340c290340b42000705001030300b00425040788030340c03003000c3c01704038000100300182e210b40014030b402000824140800050042c099858002400060b04005250400400f107480c4c0410003400c041c90450f2b080302003000c140c411140000103003680c0301031320740324046a100142ca034141500c90407440e590741c00000c10342e080e070f032002c5a01c49509181c0307480140110710110406900604102904c0b800280800381c890b180d50010b2503005900c0c140300050000e503c03248070b00ca108001da450341c00c262405c00140840320444048605803603044480585590720013642c01d280100b122800140c010020200c1c100b080340004c1d950700c0789450a00c080c481400c2180916088902c20f108041c0e001d80d54400820060440c0b68903a540c00c82c0920780b0403c45c940302d0700c840e1806600094002e08400003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 678068803 1250 678067553 678067571
    0x409021804061407081302010c02030601062303100e0a110403062f2203050f0303191803140d05040305270a0e0709080f0c0a0909021809010b04050406 66
    0x7162007082c60f80d050b00000010f2a0030a11001040c08400909010103642c281c035042042da8012410b420000b60f004003211619a11844000c1c203560340c4110014020300b950704001108544001a0780c80f41c03984040340c0c507140345814600450b190020b4080d10328a0b03a1180340000082a0318010b1024501a100200700c0780080301034068400c034051814140c07040c0c01c0b68420711843c164411a140280c050100b03942d101480d12070706050741800d0344000c20601ca0050310b030040c010040080c5200e26140c0071241101820543d03004291182d040b0700d41d08400440c01038800107401004100c10b4982c003100c19604000007070301b082040300c9068401f5070118401064071140c488850358101d0241e041500380188244011000c1286a00f960040d90442c0390010000303a01c080c0f24200c000010728908007160035281c40000055150810486494041c4402c43d2011544207080c0c0903850b03545034080d08400e4411540c1d8150150610003802e543d07003a54a070000d0500503581c50041070f00580c0078040004418103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 678070053 1250 678068803 678068813
    0x1020a030b0a0b0909011701021b07060807140301092018040c1d1e100908060106140a080a1805160e01030b07120f060b0909010e130305090409021804 66
    0x609a4801c3e00351070000c1092000d41d46801035141c2c1124021107a142e0b6180b6100c20460180c010140e89074040c0e0700e0140d6001c015480001e40c40100c0c6e0260311552420780b45c960003203d4450380300141c0c50001e10104010401301c40107030300c80d90141320b91705107002d002035030064050f03182d50241e5003a61800c8150f8010810b40c1c035091090709980c00980c2040100c4a480d03040820b41291610406841804a51011580e42d118406004130014000300702500d0746014043c0904444c0c0e850180d04120b21844002040b81401100442681283c01d42450708001407154112003121005010882c0182c4130a28403011296820b41c41c0c000f10f200380098100e19012500d081c06408040d07100d6011130141c000100081008101d4660700700d0b0451074000404c0c005042603401078401c101c41c842ca01850302000107000c4594601900710403070300300d0f59054603990b50b030308000030a842900e0307005102c62201d01c2e003030000c1e00910003000d11240160001ca400210b03034000a6a002d62100d09520780c000650400003000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 678071303 1250 678070053 678070069
    0xc2d070e01060906050c120415030501080115031e02130608100c08160507022205161b050a0c09020703140403031202180301110a020d080618041401020a030b 69
    0x800c90360000c440540c5000710040a504541c840d100602100240c10345078603005004902550b0f10010607250750710b6440603460304102101000704002803401001084030712041c003401c21101040280000c9003420364850b04a0449070100c44200500001014001622002c4c461440c0e9041408001400c900e401846801d20407103142001c410780c9030032002d0000ca5005518947c0002920302c0c4c4d512034110750401035410344984500654441c02003080350304c0401105106190300400301a0511141d00c41c41c01c10250701c00b1031081c00011582450b1241c0c0341000446582c488540a00111051600d0a840e02c17240d560280e04545051034000a0007810b240d0803200c14010302405541162500b03241d03032002081d035140411b00d8a640380c0c0001d20a402880500b1060b08038590080c020007165401c0c40001c0c105a0124103e0380141c06100c0c019100b0361300030031610344240d60180144000c1d900c40c042e0500d4907800140120f40b48540007d40a01c145801d10182400403040e8800040400600040082c00c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 678072553 1250 678071303 678071309
    0x105071703180c490c05041e020a3b090f0a020702040204030819080c04120602090409050a03050301080714030a110301021908040b16050a050c2d07 65
    0xd82c48040d04208036141c90501e60303900c08104c1490f4541c4504c018440c0740405801d03a103521261010f04401061030035003004078510621580d000e01d01c2ca660382050001b50b900034856119000e840340d0f049803c800e00c0e82c0007000c0c5000c56103000f2a500103d81c00d10081074507956405004030342100316503400c9070f048a0036038040034802c5801e2091450041451102000300800c4641940c2d0041615011910303a074055602031948192019290f9901a070303440e03c0989202c19100001e0405c0010811412400d41210b0030385140d00d582000110080d1608000b0b0351140d4003d41c0c02070382c2c50b55041c000c00c0e0103011079040036100365900fa80d20352505041604e060030580201d140c101c2d12058201c80c0e0b5034005007400149030302416681c181d4a945000078020b010303040000c0070201c0c4288d00804115440f56030103101d2485504205601e455850444041070320821489011032400c002030110140611701806199802c1d200300c9001824000e090a155501510401d490041d002138800f07244105001001c00303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 678073803 1250 678072553 678072601
    0x6091d01090503041505040b03150a091a09061201020309071409012105120a020f10020c07061202070629190501030f0209030319180311040b0105071703 67
    0x416901e98603401d480744540c0c07044140134000c454075001c0c000d0040059070018095112001e4903450400d0f0a040708550014455200d0130340c00f100403440d17000078800c030108124418142c0a900860783c0034002010800ba2803e54007006c3c3c6180c0000d000000d000940c07082a9040c058038bc61445d00150042d840c0c00402c41520444120005100c512a070101000710701c8460b00003085455803606003e41007400e04198892003d00c0055031104a940004a000342c0c00b00c00780440e0300800b04400568124040d082da500c40d07642000c0401c206030351107502034007841c0400301c0e001442d00400e42c2d80d5104442c0250300c40d400100c802440d410692001e1400c00819450640c0e591444565200c40038984c16001c1c080c06042c10741d10644080400380560680781c400c60081c040301da0740c9450541004000c003592407a50001004400140e48a00910328a4000c40354000c0241442c00c0107401004054080403510904108090199401041030f05032044c20b1032100ea540f09a0f030742060940d074243d440003810300c800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 678075053 1250 678073803 678073811
    0xb0406090902030706050705030a0806040209100905030d02030c0d051c02120a0b031b060307050d05010b09030d0906050904110c0a0b04020306100812030a0b090c0a090e04020d1101021006091d01 85
    0x8046a00402210791a4074ac5141c00440c50f41c0d0320700000c0013801004000754210708088600e043c02600500405e00743d40b0700310121246011181002c903507911131000001c80c0d41e0801301d20030051038002d40180603a0511000520400c000e0050410101d800070090320109092440a1018404942c820410f24040603401352024900c5242c101c000d01008001c050b003c0c0100000155035540b007041038881089403d078051089507950443c00e422900800d668500c203000309180b0f8820702d805801c1160480f0400d4a45a0400710400e042100500d1420014404070300100b210100202042c44403102040c81074081b1101b900781401131500d04540100468089885058140800000001c810307540450b6900c0f007079542d075500c070300c03210280600000e9a070b0451002020b01c20602c0f05030019200000e220768a40303400070f41e40ea4400d80d90541c1a2006500705804402500224a8400507103144440600450b00c8a01001d51084100d0326940d0041403103c3e0340307031004001c40d103400c2c200ea09254403081c0240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 678076303 1250 678075053 678075067
    0xb030c09151e010804032115081015150302041502060702070f12020402070c1706070f08041731050102070b09060f031308070b040b060916050c010b040609090203070605 74
    0x203003c03140045c04c007900b07124443d40e0a0b641840b0304403464528140f82c030b609009500c2000c0c48164402c9181c0a40040d0b40210024003147d1500c1d403141d0070701c10701703a03007a031000301450100c6c1d540c0c1c049180d400440415400300004114050000d48842c0da01d1125802080c251500502c001c2c101b4981c0c1c0c003c0110002ca5500c204003038001d5144440c4501d8040f24010b0b0386020902c0e04245000141d400003503600600ba5009070300f120041800c3d8410a01500c4082d1b03400310450f000c9a0702c00b41210300901034500020a803c0e28142500070789000c809908400403d0318072108007035a51400100c80701c2c141d1840030814011943e06002c560002d208000c15503003800c03842c0340001e1003400350480041410802000144c01c40c24003810a4505541001110382c1d42d90503420b0542c03a00c04200d6060b40c006038064049805418009040c3c0d2080e1025001a200040c414500b01c803681d015601900c134035900c0e01104140c6603103e200f0f91000f000c00b504000394560740303441410b0901449902503c103202d400c1c4074007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 678077553 1250 678076303 678076307
    0x90b010614070611032d07030e0309090405030417012702011701030c050f030607140d09050f100506011b0605062b17090609040b030c09151e01 63
    0x1090540380103003403200001c41403949498850150300c901a04035401c203c4600f0741400b10100640c01880d00099410f41d040c001c403051922462441c1011b80398017160400659802e00c654004580c20400f1002d907464401064000780400070b0551302640c0b1500b0004081000b1010841d021100c42a041c0c02444a50a0b00b04d450030038606280342101c1b010140061081161f204074004d820404001c210072000703584074203040707102c00200d01413603001d5a162004038450b4900000c042e031040c011581c0703500303001a60000e070300d8482c0c00c002d42c6001c0840c1c540c101c40c070010f54248204185c03003150400615003103206030b6110066900141c9094180014644202c0e80d01c0784080c101e1b08600c0c0c20180c0420745031a40d60106000b44890805078213145000300718034004e441d800356100a5a80641d14808100c00200d1010515100e105030381503011408102c41006424190002441c054008095405900641010891440e0112000c0b0440c503221007264000c1d150001e4000c2c03800c6441d450031a841000b030000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 678078803 1250 678077553 678077573
    0xe010903140a0503040f03020f010314060f12010903030e0d08013602040b1905090a0306050c0d15060f05070c090509010e1903030b0913021e030613021309 68
    0x18100c0c5a115054244203003081080d114200d9000c000c032517489980702540b811003852070004901c54005c0c840d11190540c401c1c080c504040680049011541c0c980b10100180c030700e0489200707a000762444d030100d00790010a1141c0d203c154000d40700440e2108122041c2c0d41480c091050050a201c0c806005104e80901400b408043d0300910761490b210012000608591103102d4030610b002d50300024001c951070310040050900c0c030101520110079011311603026941806601000b580100d803150040000c108590003090b00030305d10705401c900c1c0c20400c1c2008001d03109070141c900c0607a03070005400c01c103a030b0784908000c503c007140389817141c10884166588500d002041c407a0500b000c2d210310106804410a5110024242c0d40b002240d40d440d0300e034200c104000c107000300140d010070700e0080229907505201d0b0295215594003101d03044141e8441c2e0800080795083c0d03030952050b0340400f141d0710460710304000e420b0260410905800e481c0e00b9a2040101250f80017841705686400c05150200082a101c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 678080053 1250 678078803 678078809
    0x70308030915071707020705010e0d0201030b0301110306120601060c02040209041b0818120714160e040b0c0702030705240f090109050315160302040905090d08070e0109 74
    0x481658903240c00c600e00e49000809500568036080540501c020716401240c1890b0780c11440c1150325550780c417000143c0c0c40c3c140c144501e501080c1c01c000b07102d20615014200c60101c078030505002400e084808003181c211480303010402810345000050080750b18200c10612400b044010040020b9810075100070600c400116000b80503940200d4804080e9540703801c0058280c4410482a50000c280c040c0200f16440030f8490000d0103844001090080001040840c00c0034507054441b0f00d400880d503070760030414184c07a028241a000da50010f982c68211034a840000b803070b8941211402e410141820b01c016240038140c8404004100720300001a140414240c0440304100d5002d094100043c11048200b0451a640902d440000880d8410107031404040c1100c0d1100380e85000d2008d4880c000c0c103940311841c3c0c42c0201643c00c0200080c0d0042d0011a01d10300044051502504055885400c2826030b5815504e201c5203801c604162040280c0c000c00c0c0c60350003041446d2a002003c44100040c0079224180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 678081303 1250 678080053 678080063
    0x80703030c030c150509100606020a0f021e060a090807061b02090603010b1003050108060c04080703080306010201020702061914030118020d090f030c050f0d09090b01090b0319050a0e0703 82
    0x402400034000c010800010741e013483c20f828011494144400398a904151050700c0d0410300c0c200c6d000c9401f03440015203c14455001d24944180b42c62a000c01c612000c0300c81203c1e03100002100c0e001040d07290340e405440c0020490300c807040740d02d0030100c084e810410950801020040301d0895010148403c801d0403c8e207a405848810160310b8405c0401d01404961a5241c0c00400200038645000c0d80743e40b2185c100d40d015070640b1426107030a17071461607910807403140c200c15501008050021035092001140c02c03003014000145401e6250380410441c0c2c118280500d84008200d00210300386820441800c10810744600d420f00c1c660610b000c0d0070b141070005101454050b404501e106540301395620610000f0f41100345080c07189902e1030010440455402d04660324010040700620780f070300000f1411048005511041e89450070450244004c0c05030007240c40c1040000c140006100204d880113601802201329011902c098030300d0440143da00140024182524050300205001c10100311713401926404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 678082553 1250 678081303 678081317
    0x7030825030b01020127050f0c0108180c0319120903080a0e0a0f0306020a02100203060f090402180901020a0f050708031f0b04090c1d0315180304081006080703030c03 73
    0x2c100100e00605801c02108241c600741540d00d054a4000d824460003540300f602124080003c10b06402e8880b20060602c0d070214110602051040f042540000e907102601012a2805101180020704d00b00f00c0010000c071901229200340305005020f2215801c0740c0303c6040004c02d003813460b550540c81d03218001680040100d2007038113a10f503548a000200081844022007408642c0b6420404001c1d448480c2a42c098426520240842104c0d4020b82e0300c1140000d200302422649001401080100180300301d07400300305a4002d083c26034001d0499406180c0e50000181c9a01001601034802d80110b40f44c603050201c2800944001051030302240d5203d021501a001c5001002d58280d018420b25008100341190100d80400c03008581c0d032041e0300e40301c45507540c0c1c00c4244085049040542d80e8201180c1c25400040d94003d0300f903500345171103400010035503200d5502d040040e1001d095800c203402114040e00701c50ba06001400243c001d080c0034140e24000307041c2151548e80c0141500030039913002401c0c000c2e1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 678083803 1250 678082553 678082571
    0xf01170313030606150c03090e0a02040b0d050a06050102031c02180a080a0606050f060a0e031f050f1602070639152c01061a0703082503 60
    0x400d00507582540344412503444002d071a03142440140503a800b40b580034003010300c6407641841c4264148620580c00d51501404541086d4544070382c16002805244509d808000024180c038000c0b0040c00b0f01303d18440e0020b19401d280103018203480c0c0300c0e8040c0e811035000340217541820f02117440340160107101c0c0c8001682c0d1111203212451010030701332902d0307000031078034400100e155000ca138041990344170707070070421100c0d86600804c0503c4403407401c65034001805014002c60319000d0800340c040c1400080440b0204104021800da034620361030780c0f001d00c00b9264414415055000342c078454000c00d4502302c440a505030904025900c9800e48a84070820104e44041202d555540c0305d0000c10015085a10780c0d50940341001c010400011001252050706045009114280d83d01c41c4020042114200c08841c81c42c1c40c110303d0049a41b2040f03071507a07550b680710008051800c1590030902c0b00098110a40300c114500f0050005540100b804504024102c0254490f4905501d942407506840c1000911000c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 678085053 1250 678083803 678083849
    0x30a0603021507060b040603081207021015060305090a031b110a0f0806060f0108060409031115061008010e040209181608250b07050f0303070e0405010603050f01 71
    0x10903900103074010403002d4840e811401e0700c00007018014040c100070b10110903c2418813007116800c1c072020701540300500c59154903081209035290030040030700c110b955120000078540b044a61480c04c20805120b030810070401d40d45c150140765848000040078048607541d0343c0340584000c1e40d030800c44d4610f5990201c14010400450380740307140110081d10814001d40c403411149440344090181c42050710400300020034138a40280c10f40390a00d4103070744400b05511018240030241000740300c00ca0074400b400302d0701d1240c1c120070020705c25400c101f10b00300c2427141000c0e03007444a10000c00c0300860070008208010700002d000d0200a03504144e05440d22900d980d41c5a0410b031055228a041540718002d2001103000400b180541c042500c1d110030580d00e00c0c0745010400d2419040c145800303050042d03101410000c1150440c0a8020140581c1c00d070741d41c1c0700c1c441880500f5130344100c07042000300300340c0141c0c1105814035101d00d50260289080800a900b80b90900e031951040501c02d915580440750500700c00b0070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 678086303 1250 678085053 678085061
    0x10b1c02151e0306120d090b09040905030c0d08010e01030b070c030507140109110a0806130507080f101104081506030717060f0702121608071a15090c090105030a 71
    0x100071103418a8401e0035442d01c03915603209840c505d2142101c3c4982c802010340208481820300d4141d180d81e05010318109402c43d09400201c6415480741d918426400032070024402494512905005010100e5450101a00c600c00680100c160a90140011b100003411020060340100c1725051040745003800c2c0c54200c9035481019001401090070858030a0001c00c15000f103081140f00e6011200702a03004000c2c4485c004480c840c1b08450303800303040826024040000d00e0042c4070300640c140c0c0c00f6541c0b2941154a01040805c2c001d00e90340c80310300e041d14048220301c44d0402000400d440185040d280c0035200381e03110648012240e60940010120355a03a4080046600414038050000680c08010f100a501e502080341d035541c1d00c20000c030004200c035102254202d601440340c848a42028890100504d14100c030708021940040100321900100c1e800742e120542c9010f40f0b4082c15540c1c5014514002283e41209960f401034228109200012034440141c407440e081c20320b85503841c2d40c0c8026034200a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 678087553 1250 678086303 678086317
    0x4020f04031101030b010201050c0d090212030703090603200d020d0b0405010b040306050906040302120307030f140103031d0a140d0f0f0308090a0c12240e010b1c0215 73
    0x2848001030010400c03070010103903440c1410980b020050b4207003a20043e03003a103104403199440c003401001141d0f030303240883d4005000741d4000341c0384186002c80031896900d903520400007540896044001041180c0e0b0600807545900400c00000400d00188180c28440b8042c010030052100d40202e04100107080c1d0354400e56280000600c00e02c001c3d6076900841d000da502600068881a080c500012000c0400151807402194950300803d20341d0b8640c21001c01940010740003801301030b01c4803e07400310310225004207202003070b10b9581c00f5104e515618001e4900c001003107002c1c07a00d1109003084000c1c2c1c0d4950052030212480248500c100030203081c00501500d904c0d903c0202807480036075048092111595650000c1d61082e229100180c54960490360348840c0c002008003103001030441400244c500ca401309440c0751041c42001600f00c06840081c40c8d43e803207658060000c581d100b49002b040903007401100c454000655440030068103c0c079014400444000d400b178051005d40300e1410705a80c01404854070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 678088803 1250 678087553 678087577
    0x901030b030a060606020c0607152703081608042105041805042a050f0f10020a0c09020a12180f0c08010c03020301140405100b0703170106050a0c0308060402 69
    0x2c0c1000e00e48900280313540d002c0ea0300140314049031a001414044c086520041d04104008010034a4000c19000382c0b00e241d800d480c04035003821401c0c5070680198044a41e01c5d00c00d0b02c2c0c00c80c003482c00c0307590b905032001a5200c00e42000385030030520020900742680e8480c4034031548c0f20b13425084002c4005448620481d030020740900003040b8218000b07241d652180c1d0149210b91900b141aa03480001365a030040d00c00d00112000505403002c00407407400354070f43e01d0b0071200541945041500c9100181812440c402c041c0c0261704800c1c110802c2000d0306e041c0c0c00140202100c2181404002100107001c5074440e018400c01da0787c0c6e0120400f40004031407944401a610148031000b502851800950b108554402c00020790f092503444102d6a00034001d81341a104080080d59441c0003035410400509406070403911040c5448001007041180d040c010050f05000e81c90700030b401c2000200610682205a10100c01c100f000d028440b82c0d680d100c00314070b40e4141c0611f0640d070251160340008001744642240210 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 678090053 1250 678088803 678088813
    0x30c02091f030606090b0111030a26070e01030b01050c070501080a09050f0d0e040908160606030c0803071a090a030518060301031416140607030c0b040b160f02070b0901030b03 77
    0x4100070581e00f280c425107001c4003084c00306d0820140103441d5a40d1030041c1080c544c00a005000540e481a50a00c44100da83c0c4032206020049401c001d100301400d0b14590000303481004414840c0d60140035070722284800303103445441e10100003403a5071a000e4600449040024450204410315003070f820103d2007c1d000816980d100c0641d80f0200da5488c3c9140111001c1421181c80500e5032401c2c0c42500002e03604005011303e13069502c54296252040030a040740c80e107076610380110200e14031310504d1000d448454019690380c0f6460606901c0b000314070280c0303140241d0303c0b0308211000d0404100c5d6101c4d1075141c100710341c0b01d40d010203180c0500003104240b15001a804000042840a40d046c0b11814002500985000b02c915072000700207108a8000c460b25101c4200117400c0b0750500380000c025481c0a0302d400640c0100c2955111400b0310162002e9a4501c403401c24480ca141b4003001c071040b44401c9007044203908124010203074036088035102d143c0c1c4e203a0b40464030211076406174020400b40305c1c0081c2550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 678091303 1250 678090053 678090059
    0x60108160c03020328140a0909091a090c040e0f03041a040806130201090905060d0201051b100e0f1f2d0903080105041e0b0a03080d0204051804030c02091f 68
    0x408421720020521002070500849000002d52003411114811000da803403d0013541803001002c054004030744100c45039050340c404504d005000e404058000c410540141030501a0b01c0c0c02c02c410ba03051100519030f5904200004d8401420000458085800b01c8240880c1d523001120211303124096070b400f042d428041d01d4200080b840c000c3e41107140c1c41c2d200b40c9a060347c141c1c48035a120100ca00444405e40c00441580080e0055030051026200b2f07410551110302214a18004460801d5460519080000d4886d90900c003074140601c010303070412103810002d1008850041030002d40d01b4001090f4400c0680d030b00030403240b141c4000d0b00003903c4014508420500c0c00720807224002022032040945c0050a16000802c0c0d91030540584c0c210304000c50920000c0081035642040141400f041c45c6600a00d80f680020000d1466000b07408010942c240040c0c440f031401041c41380311212000c5100c0703501c0700401040002500300c12698031090b010b03207101c2819078441650300303110300005001a500030ba01c20000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 678092553 1250 678091303 678091357
    0x100f270e040303140709060e13020c010e0703020f03010507050a080417280f020a02011439010908030c0c010b0301020d06060e030f070e0703020d180b060108160c030203 74
    0x40100f804074004542d00c0eaa500760046440003c540208000034150b4079150089192800340b0109c040701800700107160082d0155100d01315151304210710015001910104258609045103413a64034060f4001d01140c500040014014030904a1150a0060130b0010801380030b0f8403002407000fa01000900c1783d60300c43c0350000c0540307224034044a10008081903091012640b141a00c80400c0c8420380003062402d0056006403550101e03403800d420702850070f11013012000300750704910780000c00000001c40b02d800c00740342d40100280c007958030040c9681403040305000641d503001201e912040c90041c103600e5030b465403249809440d90310b65031a8190300106881103000025031040341140c02944901e04c411808206041d210515103d14000640100508000c120200182d85038440c09600d001481c00032800030b00c00c1180c1d40f0710040311a203183d40248c0001c00c100c41c0c240070307040002401c1111880ca8103170204034920030844c08940410515284010416000300192500320030f102e400340e40000d024210b4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 678093803 1250 678092553 678092561
    0x10c080402040e0a150207050f1507020d02060c1b0114070503180c0607060c1403010816051905060d0204030b130b010b190818010f0b100f270e040303 66
    0x41070740709600d081c0da500c4042e4000515001902d83c03000c450b840311851542050000d4100200585040c0600099001c28a400780880303200408507441c081c0c0c16003049100285009480078902c1c081d580580c0034001252006000d64203c1c14040d5a1800c04c18200c04500380034103e200e0320700c40004070400601130f402e80c025010314424025071400020380d8103001511682c8507000c800e4140c010340200700580103da000d400503120303e9a103040c0606414844a090b20840c1c0c000d07804110307107801c440d000302e50284c4117910300c40003040101ea02098050100300321802c800a240708403446810300080f0810a43c1c0316406550003180c0154130141d1619188100c828a000d990740d0440e40c40d0b00c0c03840041481c24115003601c1e00181380d160f41c084100c602c07481c2565103113006480c45681c03000100b0310041d00d04003401000107840c080c40002c61480e0602c01800700030114a640601030010132104020000e911810505054201186803828031206010444003580d440d002800725900c0785080100b81505500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 678095053 1250 678093803 678093811
    0x40902030f070f03090b01030215040e010902130609062f0a060b03060a0c1409040f090305090901060e0d2301022107080105092a0408070302031c0f11010e010c08 71
    0x1103180c00140e0081c400c0b07040305c4e03002c0c0d0003e04c2c10302180300510250515214070002c15a1040c0c0701d524060b01e031001125800307000d0b8001c0c00b80680004120014003e043c580b01c0007808603060400d0480c3c10030310098600c04504000122005900203050f19040e034600700d190400741400c09507400482e50b81014000b40c400d468100340a4130503c2d001c00d60040b00d074442c4052416950399404001c0c05190000c0320298040d04880c1d42c0151151b8105120249501c0754030b940768825142c6556421030f0030144115107405a001006000c2e84595a80313264451540070203a0030f81c0180da0000c600380100b8028101516a15850203070340c070124001e2038a051008102d64400c1c08030b58108420798032101c00701c032300070402d001d217036004040c4501199000c08404030000b1032800083e14643e03015054202600260019031148815034040d00c030400c19410184205011800d1810a41c024400d48480c05461030080030000c0c1d0030414968001d80d00103500f940404c0600e000d1500030f001105504000a040d003800b030b9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 678096303 1250 678095053 678095057
    0xc0e0405010b0a17010f050d051f0203060915060d0f090b07020604031206180207061d0c011418150d02070b0105010e040b010c12051b100e0f061506040902030f07 71
    0x20140703404e440710022406048464208915800070300706400e0090722041000210ba43c0c2c0704120b0071200707041c640c081c556040c40c1d0024006840c0d207800d00c100020001c014100b802e22120a000841d02c2d03482c2d20f0111103008902c89808103417404905100340052000100140c080c03642c8109000310143e010890500607402585c0b4521000200340c000801c580c0b4504c141201c02c0d090900c1c000c0d002c0c030140c000d8440c25001e00c10005409001d41c081002c0b50901c1054400a0381024060408540e00081a6859008071403000c2d03040126814800742400141902584680c0030811a14130790b0b00302408403071007040141810354a4802a1500c4d401595003030250310701140000002210a00f03280c031441106e01c40595581c4040e008541ba064a07100c05181c00c0740c204182000387e01c4064800c1c64400240e9801d02e07000303056081040e0751200803541d901c1c010228540000e1194203264200040c21a04640c0d40341ca41001c8640c01c0d0001402845580d000086d10750011040240e84405855414440d1001d6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 678097553 1250 678096303 678096317
    0x108130c0e06040b15030f0a020405100f0912080304140a15050402100f0203220504020403030503040213110d02250320060702100905070b04080703170f0a030c0e0405010b0a 76
    0xb00c4104200345c60300041c60b101124040c000111f0b00c1070000903464000c0300c1d030780c00140f409845102180d4100007050200c0c010503044441000c4c03155120100100602082c4d0b0360701d4849016503200081d80c4005000500004618041e160b02988144181041c04c0e5006c050850003204903000300c0d01a01c01120242c1c8129282005e84481c0750040c1c049858003140c6901a45c6002c8440300001c1341e600f0003942c000b0003400301180104184c2c23500e02c022300c0954003944441d604ca14142c4108a4160040c6690310800c03818010301c8500182e41d10280d070400d03944410007584990310441c06d0032030355800c0c07100e0707001c007424420aa00902d500244030340c07002b010b141031980050904849641c1c0d035040c203070b40b4640141d021401500031800198002d9850f14420350550303019640d40c40350383c1c5d100e41241c1c0051945820a40b01082000f40c90707000650390f402d0202c102400d0062000d0035504078011340f4404820715856074050013155215060711002c44100410030000ca5841e5146203659811090104000c2811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 678098803 1250 678097553 678097571
    0x3c10090c05040302061611030f010f0605040218090408120109020a0305062d0a150216081605010302030a0912120c08090703020d020625060605010507050601050108130c0e0604 77
    0x4075004070340540f0703000341c0f9581ca0f10a400500002c1032140b4031013507e00ca4102884542e003643c090060002802038035001152036071104034039404aa0050b44214031a5204014140000c9542080d03020303070ba8011a24032446640e54240f094043c03080c000d034446603101040000c5030346d1010b94042d0160b0b280c1958104429505e9800317000110050350f5041070814454019012404081100621408006020401d03003560712070441d1a68400032801c18050303040001c0b003c1d0690003145250004026003402821082c2c100800144189074900420381059000000548040e120f50000944107a102030b002c030101000d800b0060400120045880701c5900307049541c98601d10410a580c00707840c451002d00b50492460f401c01001ea50341c940c00b241c001c10248900ca40b000c0c2a0428400b030403920703c0f01200d06c2a00c91608108507031168110906100c014010a00445c200281031030540d40d0a00300016140c480c0d46040324040030080c4000c194111002c004102e040c04000c103c0e000700010390f003d10007001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 678100053 1250 678098803 678098807
    0xa05043606050a0203100e1e0f0603010507020d1403061c030f0f111203060f03061303022407030e0304050303040f140901081911280605033c10090c 65
    0x5c0240c5600079001800d02040c080e80c1c7c502407070142c01c00c1d00b500c080480d54013820354200c11504125126070b0059440c0301041181c1c10280034141e4083e0701d0744080c01d8052034481002d0030951482c030403034180c81c1c1c0100001e00a0b864844070b00001c00c007160300d0305644414030302d001008041c8a00710030380080c0341560415650f034043d00100c8044181d02016084071a65002ca00c81b05401c0106001c3d0b20202600d07403a1001c2d101804980e0140303a500002d88480b0310383e130070003070702c4c0100307608641459521420820050740c002c4024250030560503c0c002c02c8002200124601c5e501a503040180e1501000800007541c101e409110411107500c045540a03004890041040310402446010f41c1c2d070300080142c1405000403020400104d00c9020040140303241140400c80054128200100a00c0300340300100412940749144401440d95103440ca00c1c42c40c1c1800007402e0340c6ca001e0b444034404952079110040488500d505551100a00c0322a0748440c940750034100c0c00030900c0d2082c040c1651501c491480040c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 678101303 1250 678100053 678100057
    0x230904140a051e070f0305090c04060b04030512070c030f1104020a050d060b070302071e08010f0b040b030a170d06150818030403020603151f0201050601020f0c0a05043606050a02 78
    0x180e0b00e512031039440710900c82c1c06d5000e004000c200c1403140c003418180c842241e4441c4640005010303070703040003511203045242152034503111501030200f0319028005a00007698480f0fa00068a90100c000c4c0076080300d40c54041000401c003541d66078840c0c00869200c50481c3e011001c0e10503200182003e1084598075800c40e51380384902c142c00b4005070800c1c5014018030312089903144d035000c000003402010581d03030040e8600715003441d80c229100c15280c00401303055152038013a40d801d00000320050031823001180da5201f1003121162080c180e04902058071090390f602640094024000204070403903071030070240003c054990481e81c03a00844040207030480040030000070b581c2540c0d4060720b05d81c6103456864101c0149805658815407021043c5a0010500301c2d54590481002076038001003001e00304000007a0502d070110044440d140e02003c1080320700e90700c80301e2200403100107581c001803010211070700d05c210f4414542003e581c0d0703404003c1303104164001110b6005d05800b528040089840309654003041e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 678102553 1250 678101303 678101311
    0x32031305030c1b1e031c211a1f0e01020a020303070605040c06080912090a0519050a1a1206041407080a1103090d1215030b0610230904140a051e 63
    0xd548061409000ca0321041498907070ba40060034000307545100b482e14481003092904c10703078a285840d080381700c00e0003202c0520480c012000703d44150301c5000d824409030b402d88481278100d0070070140c41c1d80035840340d00920910300140c0c1c0203801e072966142123040980280c00250740443d41c8000810002070303c42c0c0314010300ca0040c1c1d030b1100944060040c040503422545c10000146607c00e181c07100000300c030343d00d036541030300606010800c03000e00b145883d04100ca81542c42d80a002d4180c020210095080c2d1102d04072101d00000a100f4030071500d6410124004280860580070a028000240081d298014a07918403c0e0045002400348154008405046000c1694480c2c226404000800c400d0b0b401116800440d01e2130308400940e40c50440c03c04070036541154401d0707400c1071500c418015070b82080c042d00040d02c8104e00b480c20820082c0007003408240306443c800010503a01084081066a454000f1020400180003209181c100090800000c26060b00e2406140e450004002c48002c8058201845 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 678103803 1250 678102553 678102559
    0x6030b0415090f0b060f040f0506090a020c070e0c070f140607020706081512100f060504060605031b04080303010311041a060901050a1202070332031305030c1b1e 71
    0x2c2000c5a07501c1a01c084c001d00010b5104040c1100484036846034403500c142004c0440b0b000c2143e003851340034841c1428000d0708280046004004003401e4650000e202c03012a0310701c51011440f80d0b59400b0811043c018084020b00030300440c40390000b440b0344c003110300c641c903040103003543c0d9161203c400980e52115a4800c1801041c10040002c08110220041c9028010040c14461100305500600307810207104101c2c001038284d0341e04400400329550710446000e440140d404024243c24524003400f00c1c04010800b1035659015140303a003501c134119082d580240b01c04400c9a031a540c40b407810400e519140c0010501840c40d040d5002d44069800707244110300013020b040c051078085000c0044030650707c01d040c00300511101a0b0742203400103c61000303000290280d03440024441c8e28500c294085010b00921038041008921017a40160008048a802c8034522416106907007140c6405400c41c0603d0140340310a00568140d10b16031011469448118002200d00146901081744440300c840c02074004250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 678105053 1250 678103803 678103823
    0xb1b070e040c03030e120a061a06070c09020a020f0a03020c150304030e101b14011409060c0711032d070608151c030306230105070b0606040906030b041509 68
    0x10220b070089110245c160300c083e06103041012a10040c03807400307000100460f0030780da940c1804070b012011954000d4450508440052a04039541c490342142c0503540200040310384d0000303621094600800202100400c4c007001c1e41e40e03141d4a030402a40790300c003d8010500811f041201e80310000458801c0b06e02c2954551a941c210f0002d8a00788102e440c100d0b41100144091144800307050501c03541c0242c80035106882001600190030031540c2920b204a200203c41d10300346013030180400000c51007a50191606501503102c0d480c5041c03920241d10506000b98040c012000b040d240c4a0f0b9040210741c002401450101c07a80758012420fa81c3c812082c40784000180c545401315060b440b240c00945044600100340701d10307400c0b01300c2c07a0040d01102610202d002c240d40341d40400041c0002a1160482c0b50200664003440003500d0000e809031003240704c0180218030b64000101c503a81c60030181d40140858107010080d054a9203010301509809075400c0d00d1840c0032008840c070b0f680290103540301d0581d100d80d04031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 678106303 1250 678105053 678105059
    0xc100306060813152c03040303020d111c120e1c110f0f06040b060406140d0303060b0f090102070b030c071b05060d050114010c0b15030102040b1b070e040c 68
    0x10300002d040c01c0c2103c0d40c29029401807004c4116000303c2884503400303583d00340030019203180d100b80320309080f42c0317003403160801d0100300003094001c5905018000d960902c496441c400c410001d00f0402003a042600205080140c0540d0550064119200c5011100108122000c03080015031b610314800146411b030f942c403216a014184541a200542c40c1d0401c02c460f44444441e040c50304045000c0d52418a661069080000f8000e510352070700d070444c070151001c00450b814681d4000b00180500780580c001d01907a035030b81007010300c82d0740103000520001801e80d84858518219152660014444600510540301c1c049660072045003124001d0600310300d52480e2000d030740d854030914241c50560840342140c4040000e06511034600030304034034120060000b11903050010b0035400c078400e01e41c07447c1040823141c1454009000c0c074003215040321214400800780314040700003e0192040303802c100c100c2403004c120740803c5401000305810b0100390105481040e17848a401141c410021100500f5800c1121303410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 678107553 1250 678106303 678106321
    0x21b250b0c0304030602120f1503191e030210061a030402041e050c03100902030402010c02010e040b030a0f06052a07080d090b0402011112091005040312020c1003060608 74
    0x10711054603484140d82c182682ea4a80c001240c008000c3e00884e40224810402d001e05d841b0820380e4881005a00c00c000416101e0100c0c2c1d445030200c800014200301c0444103000d01c0b4580055284000448049551042131454003c0d201c48100c10000409d50030700f000480e02c8007508960180212100742c95074215900c940810020304001150070641e00910350001142c0e4450b405024428041c1114895407401c0c41e031909150015154003110006205106001c0140e0b401001528510f8091800054035002080010001d03c802404154107214666011040044ca04104940f10b401541c08220700d5881c4412070720140c1c501c40c4509104003c1207494550155640c000c1c045141c0a10282801d094601001c60201c071141d42068905000000411045607840714030f010070310340381ba0054180106420034403140c07030203088a40c030b20415079000c12449aa00c9201624011600600200e0249150003800703512074281c0b11041d401140c032030640d14451400780c001c0400711240c642e210711445d0b40720102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 678108803 1250 678107553 678107557
    0xf1c050f0f0c060d1b08040302100b0d06110904021b010507020601050a03080c0c130e0c100c080c1c0c1b0e0708060a1a0406020105150312070510021b250b 68
    0x2002c06a0317981c2070440ca14001d01c4581d0203400c001c60b10f80c039410b405c050801910b845d0449000f40301c42414014070f0302051320784842d16484a5440722010450342100301840d00d0701d020700304a950f046880840c1310034100680102c4d606030400c42d400204007523265404107d0719030f802401465000725040345c0401c001010707903004044a0103000c042d2450310f0302c04000a00a180200b03112401341e40ca506019042e64014000724804410443d410208004070f1200603241d104500c501503d041004112401180b40a02145c0200203602011200c203058000c3c001d000c04040c2c10f000c0e940500ea0070009898401051034250564000004036250399072042d10844580e0402041c41c0d17003000306190000365a4400c0d5501000c16109281c001d5152401d090000382119402007040807101c2c000d007508540783d10080f8550b40c904400d42c0c5529a11111343c02d01600d8882e0104a03085034510016618603100b008031603404104502100351003484a103809030140e41c1002e286044054031030f035481048103a1036900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 678110053 1250 678108803 678108817
    0x218090d050c03070b0709030201110c0f0f1302030a1506030911040f140703020406030b03010501210c0b1810020f1510030f05030909061219020f1c050f0f0c06 70
    0x440703282c44d58659400f51134060a03248200451401321040c4115038118241e1303580d2038000b40c010104140b50800040000d00b00c108a1401400f10001044058a17034062440116101800555503403e2240880005009000d00c004020000c45004900c4510030300403a0070883d0058100860784038003108201c010680340c0c1c0200010f955641940c18400846a0802c1c45244261401030b180d903c0e051002c2d003501c10005416120b40d1600f0300503c540c41300d03403820702c4000103c424000305446491410703001000071604040712024003c2419024003240c2c0007407203060394040c1e610b501100a1a081640d450701c0750441030515402800401e0072031840d0b40c445542c8000c41c003820317003e203a40e2501c0d00f000e0405800815240c580000481c0c03402c0d0b04000c10310035040402039030030003018070103c80c00c15291070401000580714a42c284880c4155550300c10061040d02d001044400c1c108841d00810368114840c0e2401c9406005290f05c910910740c0108090303041c4141440501600c03110041000341f1603020a07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 678111303 1250 678110053 678110077
    0x2030d02030a020a24050f070909060b2a030301081c0309020607120909140420030a03053601320913061d090706170403030f020a020106030218090d05 66
    0x380c40b0500c01c02030041d01d011f903440e007a81c1c40490a25550080150340341d0b812191505080410400c800ca0b680400c5a00103000030801c561803440403400d520030300c0c45007401002644404000452040d0012585548510355066078052944003890154184c4420350006540004280060000724800307442419048046140071510700d07440d0103080301142d01c02086000400710540420040001040c91151303049800914a0760040500001075983e5800340401800c04c1008292041d5154901034541d11040d600c4070f47d072505200c45024080c859084c030586900141803955400c2508609115030030002080d203001030390500b0b9040c4044119802198442e4011040c5040c104102200744100e0300a440101800e04040118019000d0720560180120080303400c019800c000440e041107460071100001505c801140e616410250000c0010300c20510400c0d00004400c81490b80c10b43c40781d02920300c201c646000740d200c04600c0340f022440440c1c1c0d40c403d90b4044041401028045e002428400e0044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 678112553 1250 678111303 678111353
    0x150e0a090f0507090603050601050303190f090f03080a1706030d0309050c040f0c1e08010504050403020a0c03050c03010f110403110d0804090f050612060f0603030d061202030d02030a020a 82
    0x15a039152800d541030b4041004d1540c0d4100034405c002e0240441401444214010b42c2003141c024129009440c05269500900100c984401500380c001c03455100107154603051001c01d03690328108050158041244c0000140da0307842114050000c00480030b00803003000d0001c2040043c039400983c0145881e401c01d4a0a100b007035079020f001e5846004245291036042804104405012009092124a40c034502206201003404407200c660020b0032904541c01142c0204240d1150300302a8185200d40070003902c00d00881c030011092200005002400c048254000c00034508500c5503401201d400f8450400010010001000454401c4900c4170b02d61000030310310b940107092030395440030952040d442103c0c0305488012611034240c00f40710315a4030440598150700c00d07045442c42240c454000401d110040003405d008107030161020401d554101d12100b030100141911000c1840c010380412208910900c14482007070015840441510103c40303e980040c4407100180d0741e1010541203000d0f100c10484d40c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 678113803 1250 678112553 678112583
    0x1090510050a0e0703110a0803181e030d080103020102060106050405090a0507050405060412120311091018081501060201020a1d0d0602030a02120f01080307020402090f030a15150e0a09 81
    0xf05100380c00007548901d440a03d01c0340407a09200c0d81d42d41c03c5d808907009800a01c4280d4407452030780003060b104030089850005000525500340301c2d040720345044503018451145141885600a4a62410380e4002d80032140680c0ea40c2c801102c0030b10079070042d40d0b04511800081050b015030340c0c0095070411942c0c284242032a80b6071010402c0c3d90001da00429103114046100802d10402200103044212107180c10b002449480c00050000c0c41201c1150340981d030080400100b003485a20541d40403002810403a19265a45c1da9881e5108040003004280e640c401000044143c0144202c2706a814152520443c03044154000a840510095000d40080b00010140f0026010707200940c4244000d0b4001a1901c4000803140c502e450024014282c1185840041c04404030020545100c598102c90141e90380b140a8046010850408400ca800d071082001d0710301040811801c2a551090100f810080c41c0e80c00d25654140b5a018414a40c14614000109246cdc1419801040741c41d070199800c0c2ea08050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 678115053 1250 678113803 678113831
    0xb0903100c0c03030e07150f1202070c0e1e16081806040b1806010f06022a22091118160c051e1f0e03030105010c050708030a17070201090510050a 64
    0x31008507032000007800141405523107a00800300d20414051070000b1400e1001954801e0100b1250b800b4800048100d5000903011841e40d40b0100201d403d80b2504043c1410500360740390310515101400e0300412800d900040300d00c0943c48141c1030700c001c180c2c01000552115110007190300406800345001040540002003d110f0410559008000540300d3b180150715042000b07007071081400c00007a02c900c000700070000700700c440c9550030400c6000701c551b1854050b41100700382e00b0494056119481e641000b001100303000082100070010b01e0181c0d03c0c1220000aa043c14801c3e0408592030045140d40e4220740c1600c3c0d11903012080450700c101d00710343c402c41c0400d5000e04410110301d03018185900091340380030311a140c49a03150303144441e00b10030310074070206405031901c0340014003079139040100e5901c6540511004120034001041c207603041c4e95807602042d60040030704130041071a03110400020041800c180c8140304904450f6000380280102800c58222240170780780c00750021040326190889285002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 678116303 1250 678115053 678115079
    0x2010b1905061e07050d0e120604080a0c0f0b01150804050d080a23040510021e030907050a09020406080f04050a061a1c0209090d080a0209010c08040b0903100c0c03030e07 75
    0x50180005004d030040406c00140040c1c28500001c1c0036010110701034140b001e001031115049603022110306d8a841898108441e8a81803c5001c0e0818040b00d801100f40500c1e550f030541a940c9169003c2115040b01c00240c0740924160340051040d40000401d142c070030f1141c1d801640259510601080c05c81e00c0caa11000b005408108500340121044240010001f040040c4182200c030b40f1000d40c2003034403d03803000b0f0003048192481980040b0010008094480900030301e005480020000502183c80d465804004d4100d4000c1b2400310301c901e8045a1480120080144500d81c8040200212075840d03480c00c0203008844034100c9800020000140c26685041c02005014500c3c0d2002d0094001801000000480078002d549207030011580310f0318071076200c030305540d020225a4025030380e00c40a200482700c0440c0d26001610001c004280490004505401003c0100007102182e20041d249440503049601072a61000815084c2d021800060f019030050302070703a8800c1c41074800b05075480400443c0e00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 678117553 1250 678116303 678116317
    0x90b030117070509130605190c050309010c020c0f100e040e0a02010806040501120305130306062303120a0315080d03051e01030203030720030a0c0602010b1905061e 72
    0x40d240103840e601c40c4004001000c000c08003110009102c1c14500403403042141c1001d400380000d46c031030740041c0c044200b008603411030840c07040c410484000840b0000786550802d07110502154200344035085e84910000390b44c14107500042c030900c101c0c2d040c0e80420031030b07018408413841401010030510f50650348a200700404500390354003030804440688001414041d0080603030b4841c92415006000f2030642c690328440c1c080d0706080c6a0b5850f0400c1200c0200440300e540700400c03150800382e000ca0340c900510321402c00300c02101c400000302c090b1781080644400311000b0034040e069080c802a104203120f5000b0010241858490100e20b0b81c680d5041030500c021890361034003282d220014003a080c110f02c0c60000c160303104822081e90341e505550000391648940c030000b40109c01800051508615144642c00440d0801000c07296108100e10389076041030500e10a038070140d4070700502000541840344004060b003640c201002801d0b400c01042285a8005032000c2c134000c00d40d00050080354050400074803d13 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 678118803 1250 678117553 678117569
    0xe01060b0901020120030a0c11060a0c0f021b040f23060a12080301030b1e090c121506130204080304060e1903020d060b0102010b15040905070e01020d0c03090b0301 72
    0x3079414004006402d4035a00d070a1150201c40885aa0034840014000e80b5006641903c1c04200c3d0710130100201d8407010011820000c238043c004c10f1200284e403542c44802c1c81d8409c1d85a10b42040c01520007603845000405001c803c4034803600d02006140341650190602004444c00000c10310803800041d884000803040d0214031103140424800302c0d14104969400030008203540702d035007940c2c036601c41d402c500042c40000c190101a801095049003c071004080d11120f07907002d0500340c03500440c065900c4071411046402042040600d04218401043c000c94a400c2c440c000021074407408140540311403c40a0200816400c2c400445d41d440184000c0c001000d507951002e480f03000c005c041200740d0348130000300214950900300810044c2c4034040c40c1600d0035007200000440b505080c0040c0c1c09042000d072225444001d00500c121442c14120242c0141c0303180781000c11107a5070f0b211050b10502011030341c40d40980c1c01041c0c04101c45101f404030070340c550303c24034082075402da68014810080d0401e0b009956 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 678120053 1250 678118803 678118807
    0x9010e130e2104030507060807090902030403050a0e0306060d1e14061803070b0720030a0512010909020114030403090503030d060603050f070915051605010606081b0f0901030e01060b 80
    0x10320030b00c05440c1400b410300501803842c074040c51540c0d0990b03919103030320441090000003000034510b0360040202800400d4462029580d9150a1400505a6001c5000b100c0801d5060b5558060380c100024000d114540107000000e400b141c80d141c1e0180b408251100211400030f83c0c420b40e002a20f0740310340c81e10360f1103a10010000c5040c0300740510b00380740700b9000c4101594414801200480d80d40c0011540040181c140841c00d05242024120b04c5508243e01c00c0041c400010601506035002000300300d50410048884210307626400880e0a581c0d44800190009403203c0b042920f80040c0c0c8025501301d4824185400040d1342c0b103001c02d003150414000c1c0f441550395801d08000c400e40502031254001380300e81264405150200000d0700c00001070144441030311a100e41e802c0f000e40940c007240e1a440040040b201000000e25265010384000d02424000920000c041806400104280c0680f0385001042509104a40703184400a030007080c8614101910360740f850621100a01c1501d029025000c641c2d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 678121303 1250 678120053 678120073
    0x10f0c021501151b020f09010e1f0b03010510050c15011a131a0d021803010b030604030c0206130e0901050a0b0f0102252111090c09010e130e 62
    0x1940c1100590040403210807511100c500182d01510b1038a0801a02c4020f203844844c1e800031804c01403641c0005900b000c010400891070381c0901d1051445020002100b0400000d070b000740030844071040c0700303007e0603450a01c014403161038001c488100a5080703103019401c108400081c11b280002c05140d0703a051048910050051600d8941c000740c01c03c1080181901c0d0100f60b05100f500c101c4e10788a49040f0021113075210751110b829404a0722040702c03034003055460f0740c1c004984c0050001400480c2d8483e610b00b1051000328140440da403489a609512020300c594640d809005940d032100451280011002901090380030144403418040c031045000007a0a00e4a09503c40c22103003900b81c200d205405d5203541984c41c1c2c0c0e0029403542c12415080c50002d0002c0d442c140e0456500040e042800041300846884120a0f80a800940540e00400d00c501c0708210400c18881100006d68084500380c0c0c0c1081a000694051313103200900520261940c5e1101c1e5907012174500700c90556209103004d40104041d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 678122553 1250 678121303 678121333
    0x61b090d060c021204060e0d0302030c0d030209040c08010608130c17011a0f0a050607061b0f0f030204050f10021c0e0111070e180304050d0303141f1403010f0c02 71
    0x121104d2104e1004652404c1d013890005004d45052054061141c0404600074081610a0081e0b40943c60880220b07420440e1a8401501940003038540713030701840c0703000c00c0c400c007945c412424207048904984421a181d00c0341001128000d540b081c09480c442e00d03100c000100d1004540d070342c0c241d400d103403c000540000c40301186481c5121810380c02d407080100340910300c0c1540c0c07215955030444404642c4240e44082031318054010300100036461540340f00c10302016140b0f58010b4001d071170b01000e95a0f20131404000c00415401c0380218090075802404110200e0440c0c1040c81e40a005c40103103004840000003c0c0d48024440b1180105540010742c000310f40d410a541c1008864841581c080c01502c100760601d58020f00c41c95000307144000080000704014003017002442180d000e80700c0908201c400103c01d04014028207050341c0b88085401c0c011000030702800d010140c5880c01306042414803000c070b16218648006240304810319505544e0354101884031a05482a41c6010046130080c01141e41000c1e01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 678123803 1250 678122553 678122563
    0x1021080a1205090a0c12140d110609012706140a0f0c0503010b070605041a0901060f0b0a1d030127060b01020a0312090c350c03061b090d060c02 63
    0x4100816071161861000080b005c05242d0b0941340d032074124000341c11003814903d054110030304501c8641d0090f010130005680c0d01002042c10669540d08075122a103906807014200d0f80c1105800b00f83c0d0110220741920b06d510300b50a0740c000790190a001ca920001e0301d04031050b0300c10a0f110003083c1035a4250688da4007041d1b0155a001c24140d0900c18115890050310702d01901c41e00c00f0040c50ba5503100c00090400800407483da200b10105c1c10003042038544034084900801d968010725408100000307000074401281ca080316008401580c0f071000d0303e00c001c1500c0912032105043d4591554841c00790303c1482c0c2004500c140700c1d1280d954580948103184c00c10354100d4444c00c0708181103401001220307010130b41000c0c0901240c04602c500182034041e030b080560750405241c00c0310300522080440002580200031a01445440f8000150b00c075500f1407071115596150400391a8040e00000c00280c8950820148031038000c80b420301051600a40c10001030281c808107070708031009540c6010120940b070381000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 678125053 1250 678123803 678123811
    0x9060e0105010f0906120206030c0c030c0c03191211010b12150a02090a0e06060403060f050403030e0304080d031a0301060806041214030a0c0c1e15051021080a1205 72
    0x240c100b05e40303402c0000e140c1c40340c1c08462001c7d0007010008007040c24423040c10308480180004c081038030b440708a8000610f44986d940d510303040c8244600103110a8000d0301c0f101c140130240d8000f50101062120340f500b078442c0c8540d01580c4985558441080250703440f6040d0315942100f84602804060800c00f03070f142c4c1c1078034000d000d842100380705210801c682e072255000305040c1c5014000e41000307a512500003503060710850300010f1032241400744607014409140c200130f0240d4843d48081c00b0780801d03c0c40c1c8598038080c91003000d04903032040d1002c035a5030340030350301466000541490140d660000c00e00400d094a040b6400303502c8a078450020801800a41c0026800c00000c610f4880b515034400e004003034482c003001c2c0103282500c0d5142d510741e00c154024410307001540c5e8001040319003101c050b88040c448200307407035080e51466110480303040702010074810075200c0c0044c0d8103010116400c15100080403228149985104044601c200c0d010400e40b01c00740010b04440d66074040031a100c1c403880826154054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 678126303 1250 678125053 678125069
    0x12010803090f0607081c0e0c090c09122d07061d15070c090209120f060f0c04170c010e0d0b0402090601180f03120c0b06011209060e0105010f 62
    0x1000544666682c00300e0414440c5040703a1680d10341e1502d003010422031080c445200d03400302500650380c510811641007050355070a8107041d543c450403064103105403c00b00701c4051000c00400c00c0003194500c1d2000019006140010480f001d0251640c0c41c03001c001c03c0c240e034901da4010340c003a080d103000c1406c101e244050070b49803500d44015441a400c42600201c1d8010300d84c030412842d03401020b2202d41c10150b07016185c00c910100c2003d596580780030025030201c2c0c4024022800380040800e1000001685c0710006080b0004254907960503040c0c2079101d82c0a0141d40040300104400111803244e815a0f100c45c510420140c015038000781b0014025044000c00c460103894100544004904d49180c150340c0241c040c0e41e20354080d41c13441c0040301d01120034502910307602407845c00402c00405080c1c60f4420789124161402c00b07811681003d0302d14055103100104808540d600040c46544143d28040740360440d5940400c1050190303940800b40c42c03205a505e15142e5442e40100422115200c03014005c003d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 678127553 1250 678126303 678126307
    0xf0f0906240f03030507060f15080f030a08130206190f0207270b0102070b1611040e12090d0c12230d080c0702091303030501091e0509010b030601060512010803 70
    0x2140030442205074612000d01440780206d208024000340741c0014041c8040c00f0820002c06807034041d81001f00515009040007032180000d0984041e500000b104e00f000010f480e6110079580f03d81801103c40501c24049070486d174244014520b610f140f4410003d456983d0311024003004007240e0007881c2400c50361240ea042504018030100c101501440824420b0b83c4d040013080a0340c10701c0041c0e00d40b51980e880b000703001e440041c4044e54070092510190410388120640fa503041140d800300400d5441c030700c040c044aa00403a1031084010a400b00a1000705009488041c040720203850300714810815602c01e42c066075822568400704581070090840603542c8003502c401400f10a402280c0d980c00614501083c002c01d203011030145035025096405035a030040017103c042c40c0400364105104130a01d421004a410517002180e007400318014009078020844240f050751001e0150352000c0c00c4044c1210149550f0340c54200c4d0281c41c01e00040d8040c00c45529002d6480301600a0300a00c4101680010115001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 678128803 1250 678127553 678127559
    0xf160f0b0603060c191701081b040905070b0304030323011d0c04060c02010c0f051608011a060a0e0904061b030501080706180906061e020609100f0f090624 68
    0xc280e0907030b00c0d02c410280c460600d00720512410360301d003409800c604080d40c812100000c1c0022300000c06141407070b4881d0b1665800c0904006010a4070150080100310b078000d020280b014a4801c0c01450b48540030b881c0c00701c1c000d41452007140030700c42400900850700404400602240c11480000d80d942c4108001040c02898024140150341c021400350404000d140000c240c00d680c400c132081c0c0c02c0b41c0d0300728802c034800d280c42d03180140e511b001550000341402d110040010701d485042c410750020b1004001804205003d172410080c4582c00210700703405009206545410a40360b01400c2440380340709440008100d801c100f105e2440d400410f07407410415050200501030400041648401c40724141044446406100c0c1c1c803420ba00d1158200680c202e21b040400a4000d03071000749880c0c0c488506180c29407448500c8422038441c00101c500b0485070f0b00180b500848501203500501020b0308a107000039003500c0102444050f01c192030016202d441d1110200b21040030301d260003500b07401071590648540b6103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 678130053 1250 678128803 678128821
    0x1106070309090209040e031c110310030b060d060f0f060b070f080714030d050103020f011d0114091e0405062d03150903070320120f160f0b060306 64
    0x7094040c8040c16074001c41c00340e8560325035400c04120340b410354081e240c40c1c0c58001040d1415807003158200b00d0346d42c10007140e00841c00c0500201d9000c2c00f2110017004141d400c54507062102080507104941100b4030012650104105109602083c10221004110802d52070840380544055400c00b101204040041d80d000a4041d121000603660040c641610750206050803200e80c810100411000e0000003810710300c0701010380c00503040e20301c21640b04a40c490b2907401101e845943c01031000d041801400150402e43c042d0203120490507003106a00c3c0f5101009011403000d8003a5420300c01910f0006843c0c400610313050254650040051307840f08040683c40f04821807203003040040314018001c1c45134030f4207541c906014040c14100076580380c150700d060511800e0ba4a5001c004c007500040d54a61200c002145800190060180300c40b00038075003c44200c4001820f81d1042a0421a0036030801600d08a60031030314000c6e100600030450741c0324100003400c000e00801b400400c8188039402c03000401003142 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 678131303 1250 678130053 678130067
    0x33003050618060303130b0406110a0308041b0b040b0c06011202060a0f030b061242030106170703032303010603090618150605190b03220f11060703 65
    0x10b0480041451a02c600e000709046100e244041100b906001c44003048841e00b400050007150030350355800c02100b10f501d2400351555607203103005000554a0011402040b0fa41540d14400d441100e030440c0e0003a0749001120550307025a00a0f5605138000c00c1622180c14140f1056004100c800307a6070421000f03c2d800180ca600c00c00f0f10300801d10060070312110845200e94041240a00041c20044e6146940304510403400b10807108410042c10311600f0107842070108000c800c00c9101c0b064a0700f00c07a203046002c01c00d00c540520020780c045d0350701c810024500390303584282c2681180d00005409600c1c02c506005101d40c5612220003075617003000e614070341610010380883c3e0441c3d80710301d400965400940761140c05041c203000403d0020100740503541c03d001d604d24808403d0300c02e040007000001d6907041030010124016180b240c100f0b144080c00c2240520b81b1004581c090301d142c0c52a0720048400211a440c0c011440056403240e07082c11950f8100401460981200d82084414508100086d90f0003000f071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 678132553 1250 678131303 678131329
    0x1090e010e1f060207150e090114030114010f03170406020303070302090a09140f0a0b1c031b240b0f040b041104030b0603160503150403090330030506 66
    0x400c4005001500c009a4030070710b900c0c58020041d002c00031596941000b9514010743c0140140c0d5208501160001400b6404220090101400e07042860f0301e8400d04108034201c16843d55019501c0e08543c030000c1c0000c0110b140178110711002a12410b0a43c1490705a10881c140c0030800349a007084103104407074000081c9c070b6000c2c2140c980543e644403401c010034a04d408a61080103c1401c15000d0300c28010300d1040785100c1c05420702074140700d0344ca800c100800d40b0103405240790403000d43c000706001d600401940e01c02c502e0090401800c4121910440d0744090010349007540d484003100c810704201c4000d035507858a00c00b40c607030007406441280c60001e5042c030310803000180303d241c0d110b5420713105072110381202011000010149442e20345c1e03820804101032044032003501c6806420401028002118481010345001600501c0035074450f4007161221180a030095080c0680e0800c00030005d1855000707040c410400100c80c44070b41a150b2100d00407117800340b85003418142040304108940e280d0b4080d031560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 678133803 1250 678132553 678132569
    0x6091803050304060515040218360406060f0605120601081b0307170117070f0b07020d0f08210f01061b031205010f03051005040201050f0f1603030f0b01090e01 70
    0x170794a8040100d0311100202a101c0c0c0c0250000c00c2c40000a00c00c48858039501c0700940c0c102407004141d11514500341c00c46054410340030035480305980301103170855010380d00500c96440000e2280d02c40004400c42c03030055004000040001500382203005a0600480d003064007820705d13128a041070054000f6598071450012064000030002440480c812420300801010484a403030003561140c41812220240c035400300494802c00e140002c48580d802c50440840b0346440459040c00344950800043c0d0b28142c2090314101d04209110010815950040c80100f25507000d0220480b19220030000d4410024800e1071603c0f8100010050107810400450a8114800003003445036030615068445003142050003120900e80000410030801e15140d88003924040c00441e56020840460300003a520700302c400034009041031240c864103400d15805800d401f084580410b0030603003061890000102014010740c0001c1e00c44500700070030451403082c08000b207001e28000746120b00303003084500f240c0b0044c4a80e5038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 678135053 1250 678133803 678133811
    0x1051003020904062606160305060109080105010f0614070302071e1706250f03090c2d080a0b060d05010b061908070503090a032a060609180305030406 66
    0x45814400c1d41115000500104204542a1100440c52031600c1000c0c2040030300d001c8003510390000d4000a03003030784504400c46000ea003068059500310060302c0c0240c50103050044151010460b0b001c280a200d0281c2106c114071071001c7d02e04003004006036412103004c84a14020055480400e90100c1c60317009585070303855642c0100604d81d0306113119801591185011840a22141da03405002189560003020411800903d55840349100701c003400300039000320b02040356003505824060281d0032105006001e410101060342d40d5005400800c00c08000030006c807042c080311044001200d11201001d411010b008000300704803940e5020002d00060070852044840c20451270400809400c850a0528064901c644501c0f0300100030003003100000202011426220004a50902c5034041d43c0c8070b5490701d00244006c103032170b48003903500c5c110b260400d10256a00f440110040307180c18130100c40040c403600000076440e1030000310400b02c40001d0307600948289440003120209600100340d0750401d4000ba0001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 678136303 1250 678135053 678135079
    0x10030f02151908150301020a020a031b080309030c0706080606070f0c030f05030d141905090735010603030c1401140a1406010806030615061b01090314040e0105 70
    0xa00d40b402020111446030030540e00c04168142d024410383e00440c04400070b07900c0303108000105404e070b0140040310401640081d0320900400c1c425142d0050307400d541d0f01054003070021a1580c0c001d5a004441c03442c0f840d440051502c1810034100941002418940707807206031801c0c900f000039000e10808070064118003c4900b208280304c3c03da0f941e50300540c1c0c041500c0b1041d461174039100e030f101e0300801102c000081c5024004582000c460041c030b032051407400381c80114554201d019200400c406040314045219a0402007018030100310f04000322099103080c001d80c06510401c00c00005800181744c02107905110b0100f00081e0020703000c42d0140e40c8071803804a545074035074a035401018605110f4140344d2a803414020382c0c0981c4c0c0e00665141038400d01c141920b07a00c0ca00107440c1b480e8261522134055000c200002ca417140d203002c119110a000130081854012140c0f502c100c081074140c040341a90355590410010160050504180f243ca040c2c00f140c00c0c1b0f4508046202d1010b01441254011a10f40c80f000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 678137553 1250 678136303 678136339
    0x2011e081603021b07030b1308040605031302030d1107090e0c0105071506030b0406050c120f090a0503030a140105030601060f050d0216050706030c0c0c090b0109080a0b09010510030f02 81
    0x1031440601050700a6408103c6aa0005d6488540e0f12003503d200d0000408281c050041741003100314503821041c1940340c24606042224103601c0200913030311411400901e1001690b09110095102e41c159403440c648011407020981080741d06d500602c141440d0081201d0b04c1c2e000031900c218201030900b0400d03100c041c6400c241001c01007160300e0701802c0340b61072008020000300391003882c00382d40214070030080c5070740355a0340c030349203200d00004118011000f10018488640f140a0554800c0000c0c069541801c07155550502e0750f0015a8103400701511100350011002c91518034a004200840081c40c0c3e81d4944007029201d101003040d600100400010720704040d0800d074040311045044c0e12011840c00c03c003400e05540b500c1d2540a2000000d0810850410840c440c04055a201e03400103044d02d01ca41c54000560010300c4c5642003d0f040c08682440020b04078001c0c00b480101900030241100c2c645403142c45503003103d800600d1510501c0b6600828008034094440d9041303000e50594031250100740d42018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 678138803 1250 678137553 678137557
    0x9070504030803010b0301150906021e0f0712110d15091b083409090c03050102030f01150507231e010e010b04050103020315041403041202011e08160302 67
    0x409040c0b030600000025a0703c0441e80258100c4038040503840002c0400b48003150071134031034800c0030016030000791040c03202c01d22000030311a10f0b516402254049000e0743c039014148201a8840700011000005280c188610104601c21a00080341c0300701d100c0000c3c0c2e0f01c1c2080c144008080744804d542d52a01507042002100201c1150b40e514a550b00901d41e4130700c1c0f142c0c1d0320301e860100d040c40c0a01a61070b07100c190380c000c40481803460319524060205420000c0c42d800426445c00305a0355000e1081c800030202c3d04c20310056004c3c003a5814801915818580020a00745091031090300b049006c01420020609007445c05c42d415084540c2c540c0309402d980442403528000045030340420b09a0a0703070300f03001031341540202100044040207201841e032100800044420174400650980c1200e001c000d492415006000e82c45841100103c11400c6402e00d03451440c3c0058001d0050399241e00b4649003550780264540001c1c0101c0c1880d80f011150043d4003d00b00007004d170030748103d94403213100606500c1c02501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 678140053 1250 678138803 678138809
    0x150313030207080114250503060111070b0f0903070b070302060402040c11070605030718031a060d0f0827130e0a050616180b180f040e0c03010c02190209070504 70
    0xd100c4034080f0641030017101020348080078802003029040b1819181c180300f00c1c1050f2000e8540509560720364005480300b42c2c6480c86104035004000c0c02103050040c46000d40b4090203408415a00d0381e100d002070600c1c28a064002424810f001d10907400081d5000600a9001c0e80c15940030404495281c001d6507101c00528044805000305400402c8171a07200300a10300c104500d07581c1070783c100caa42855200c145680e000240c130800c11071036407215200b0500503c41c0c01074406407003204100003a44888100800c0488100c9110b2000190100ca890080d10810010184081c0040904446400003040300f05800e0301c0c4a1020b49540c0000101d800a200351840356400078107172074240c600b10b5400c0b00300c40044004640420441e8403981611381e4800c0a85e01501c0030aa011071521007004440704192443c18000b6a120b50035040010882c1c50341c0c05440c00410b14000240401482d081c101400e458001c10700000315171144038000c0f140041c00341c10403096034042c2c80140060700c82c0c200c122403502c42c5030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 678141303 1250 678140053 678140069
    0x9040605100c0501051803070825060b03150717090c031509160b0a050c19030309021518010509060d020c070303090e0403051207030605040c050a0905150313030207 72
    0x59040c680041e00551010112403058008020699411504640498401b20b09a1140c0d00a0100740006014070004020b0403c8c085401c0c43c41e045d00c6852076802c6032161004642e015100c0001100c203040070440c840504a62010a240515201000403d801c00541d40c103100742c140c000218807500014054500c44010240c1070320234401446101500c0340c0c509480405141c0324200450354036240c013001c10016a0814048103140406444048a95422501041c0007500030b0155010030010700a4440e031126209031000700700100140100100c0091803110031400c0c940400441140416035050100244400d08169498541d2000840d14500809c3e80305641d103840062a1503040000082c03c100f141d10035503d1106103511204a54080d03070068074002c000c6130081c00081501c01c01c148000f42c0c050410f10b0000344903a99200090140c2c0c5074011840702003500000c807600c00c582c1c0084000c000d820290b80201014001041c00c1c001444010000568480c030080f504003014420b00919000b40610 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 678142553 1250 678141303 678141319
    0x5011b0204271403071707030e0a030b15011e23030c0301081e0d26040c14010201020414010e06120108240601020616170c04030c0f08030f09040605 65
    0x2034204284602c1da091041d00c07400c1980c260740d0b007000d02c004100d0b90b075242e00404c0c1c86044d1014225012280d00841412014401070710b5858502da103420510034020340c01440008800d0806104001c1c8841d80c1c81700707850402c22011452418083c180003201034031445403802540c0304078031540c0e842c071203120020040b0780b038000001880340341c5c0310040196050764030b21815a2803281340f1802d421582022001c55044540080783c80c03824680c05044440740d807031101c09444051486055007000c00d908101c1d4112002d0581503403c0c04864004540d0200042c420700003145001c0c20001a2076070320540b1200581080300218041d116a2682419154641102c1e9842c20113075840f920207030348038151510103041005490b62002218861070304258020101a000b030a080e40381c100d9440c20407030080000e40c2c00e100d1a10516141c0c0d40040b01d04a10034640c0300311080d203480c258580440040c0840d0721400300d00c62a614103026064002c81101c4500c000501c03d44e82e01c0e0b207410701103005403a2755400158002d507a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 678143803 1250 678142553 678142601
    0x300b0402090604150510030e071d06100e041a100327050604380105100507020d0b090f0a0c1d0106050406030902010201060513090b060919090212072601020405011b0204 74
    0x12b061482c0b0745a0403e100048c81c299541d400b0301110115981c010400550140030f4040d0300d01341a03114000308450480802c14210848000c02c0a006001c402040041c3d958400c000ca482c50146000980c040304203c10390a4022a07142c0c0340e6941030240000d0142040c03001403604400600201c460320341c0c0c5042e209120101548840c91100d50b09104050140c8842c44594682d50b100300203d50031540e005240c512140c3c9030781c44035492900028002007243c80b416201c070258120800c152a42c0c6441507080c18509420000520014403000305400c0d100c1d544170005000c03090700203054030140d41d4640b8000841c10030b5400104d0162485902854001c488200e030b60200c08110f8001c1908180a00081065070300e414092204002c8210703481540012014400410390107540c2000c0d0341c55000501c20070180645802da641010855800b03401c419031601405503071116500f910180d00f54810000714145841c200010307200c8130300c4171010314051484a42e51421591694000c3c12844005a280200e03030340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 678145053 1250 678143803 678143819
    0x1b020601140d0807030c020a090f020702130c200a0f0c05010e030a170d0e01060905010e0f0601140a020102120a050a1103060a300b0402090604150510030e07 69
    0x160a000310010041d00c03800c01c1000c1d0070b166607a50b03000b591000c1c4141c506040fa8a044071002c1803403c00300d80c8010f8031000041d801e001d40c0a2003510340941d99005a4809691042040140c8440d5045c9207040c24041b1110f08540c05c082841400028a001d58401a031001b03101c50409819400090048200700740c0d03d02409400401241564400e80314146611046410941c0d6032040000041c503042408000c204048410006420000884a000b180d074003402800340d42900c01070303044011241e5440004004010404403007030b40021041c10400814107101d0002802d180003902d09a80e0000d00089480800780301350304031413103128505100380103801c0c40300300280505020341d54a221641030045407030038074080404032070284400901d0004140d1038194034404254894440c04451003803d4030b01400902400d00048910380b0440c440065840e1a20401041c1d18020f0a114000d52a1008a0000290740308030b44061300c00c12a8038010f501307010b1000724050700120640c0e03c401d00276480009040c203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 678146303 1250 678145053 678145063
    0x7081c091a071523010b030412050d06030501110a080c0c1902131b0f02010c02031905270405010b030c03062b0f0c08010e030304120306091e051005030d121b02 70
    0x4004c4032042803c69a172581e80300c00310b000c117a902801204d21507045114013405440100f10302e864507074002c505655651240c508480501480c000011000500c130b10085030700139411540000e2044d02c10b070819040307505680d41c030250b10300441e003901401c406100c203644e00d600e2404071105400b14184108460a9200e60b000d0311031841c0c0c1c078045089405060790450060281d5481704905500440c00c01c2541480305901c0c1c10440d0031041401810002c0c0f0202c1da02921410064840203404a900c05180f00d0901040b02e070160b001d005454414014025464911001ca0ba00680c4c05c0358040c402e88110741c090081001d8a03501030b03e02c1071110150004116807854071400b00ca0240d5115400942e0711101c00c2d00381c410b40b003130b800d4041d001040014001014000000909243c5207400620551584207442c121580031070f01444010300070301444840e2050f03001da240d000356680707401c4003060300d0000402e603100b5124102d03a00740150300d41e00c14240c078099404007113012020545940b614803440c2019450b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 678147553 1250 678146303 678146351
    0x2090402180f040209010e040b120715090801140408070c080d020a061805070630020316020a0201051c020d050a0c1d030705010302180307081c091a0715 67
    0x103101051984600d494a1310903101d405006840e41218041104200001041c42030b043c0b03580081e0120f046001c1503410020400a48529006810a00c891500140c40c020f0359030300100c0c03d40e06144c2501c42900c24894203c0d08254400d000c0c0380c907841149401c0342544001d030030007500e610828045000c02540007882d11212030107020200300b5480080d003400f800c1945c2e24000b810b240d0100d078042003910300c42c0214000320740d0f103d02d0500c51100b0086440f2844941036004007a030b540c0100500c00076450015009549a40c5e900042086207900d5001902e18010110403c510b100100c8425203104601d030101c0368610000b1100700180d28002008500501ca55802c10700080d00d28032883c1d140e0401c19071614031001c002801801480c0c54100110003940c4400f16030b4003252070307a0b15028451b4908010300ca014000d4040a040030084044240c090002c00f000c07082c041107070b400323010040610b4007a8000800020800300303c0da140036600f801c0900e040c2d880180e080c491302d0080c00c17080303c0203011208408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 678148803 1250 678147553 678147559
    0x7030e0d14060a060905040c05090601122c0a150b13020f0d050108060705181c260a0903120c0231090809010c02030708030f0c1501061d040209040218 66
    0x552140001c031700f11002240c000303160507003d50003400701c0d10300110a0760344400b0514101d14881a100740900540d485804408000385c1a9011000c215103050511082007810342d0040c02d2a521903160317101854004c0c3c8980005c9503480c04039043d151038031103221011000d802d0301903546088a02c82d107001c69101c10440e002c1c0d40e00d80700010031454004280180903004a60380c0c2410050740400c0d800e2590400e010380c2d03a100101f03001c0036480503542400c840710b86004080d600a0102c840f8030031401581e000e0000412000104500100c841c1c00801903400d807a003103403082011001d43c10060355903c2c00c0b90406903015150880d40d5180c0d1184c260065000c101c0e501ca196140d0101c401484140d4035103804c020f0030080280300065881d48030701e02c01242e80c1c1c0010110381e440ca64566100e8110780c00351182e840158400908100039000800c03001d826122003000703440e215850542c004000b091440c0b1180801060302c0e06000084da10354041e2904510006c008540d62004c0000d031910700c0ba240215580 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 678150053 1250 678148803 678148811
    0x30d0e06090d091a090a0306052e1508090a14160902040e0c031308041403070e0f0c0703030b03010203150102010c090308031810050a0914060c07030e0d14060a 70
    0x1070b106116410070000c54040350001904511883c1903000c054002c207010340d0708403541a100001045141c09102e0198503800ca08400908003841c1c58600a0060402210042c811113410854441c10085518100040380b4010046031640d2482c0303414400b50040251907910b0500b03080c42000c2c80402d2410b00050b0103aa07050000b13540b50f901070b00341c0c0198410b0164041040340016003a6407608003c40c0e2080d504083c0e078044640307503516900721743c2160f004032a080c0c40e00550798605040406c50b80780500b0440d00e21030785c5440c0c451036181d501c040040146569500c04100842010b02039042701403103d00040003991246010507007076810465034502103006600b40180d180703030a800703008000e00707803074000c035429166a4a07504080c13651500c0c15441c5429100e03070404c1411044041c0314480c040c0e0b246540100d032200c05030074040801802d0a003142402d03001641070002401c00d00049400f11b542c5402c01c407101c036202d030300080c07000c1c190b000010f00108988003040c550b000010a04078441c450040c0100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 678151303 1250 678150053 678150073
    0x303090501080f070912020f04060b03060f0604120f0804080f0321090a060c0e0d081b070612200c0105040516050a0e1f0e0601020d030506010e040c02030d0e0609 71
    0x303c000041560f03460007040e203000c02400280020006401600c0c0083c0c1101103503407900c0085001c5030210792045400c85008400d010352071414014040d105001298118201424512861a85032804100500d044101c1503000100030b14502500e0082002c3c070196498003104124076500d981c0a07522131142c41500010032040c03144261603c6004021020040c2070000060382d07858002d00c1c0c9180710a09001000c83e13a80c3d819560b0b01d48000d6014862400c154440340b480080e001411015001152a608194028810700d640119100d40701c004869001c240f052202c2294000da0340c0280a42c150349100044001c08900305410150080384520200d807010040b4041d18032071000107025803075107e0320031b46007040110251490b098201403804803126560303000000d104c807440e6281d03000485050602080200715070b010700580300c0410403800c041c0a41d16012000807c03101115071218440c0341d540789585c12a51003003055030000c0186040801500d600c4241e100da44403030440e41840d292081041d20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 678152553 1250 678151303 678151321
    0x6030506060a02060711012c010606050403050a060515090906060a0f0803040314070510020a03020105150901090903092705060609090c161a090c010c15020a18030309050108 76
    0x50b01121556405080d160b115584212125903004440144c2036481d400f045101b507100c6550b131040038030100300d01d090b030340380034140a800c3d5000c907030000301401814803040000c91000314020003441d41c0008000381c01c0c0c0c0c81c4100c825211505018940d080320300c8404110480000207a52800b5120885075003405035640c0781c070544090114060304019402c103020030000254105c24440032034201c5029108032a8840b0b021414141468510b82c0042e03010b00d4402e000e0503020b1040c640c00a454001c206c01200036403020825662041c130a2003945640c41c0c1607901810300c11000c0340081c2070384068203804804001c50300c0807440d04680108008901e02804030f500e03850108210b410020700503003c4040f6580302106540a41c02c40344024a040446643c007400041c00d82040700450002d000c044145814101d0b8500e160100030350307a645c10300040303061803c04140b1000c0300c940381002e002800340e0740302918807044941200d505002000c0c0612030b0000b00c105508040e0442c2900e0b400c1e642c00115030368108038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 678153803 1250 678152553 678152557
    0x6030105010b0d09051023010b0307050403080f0702100305011703070b06010e150f0711040924020f04090506010201140c0301150c050a03080118060303021b040e06040506010603050606 81
    0xd0030350303100b4208062640d42ea000d411110f00c25000310166800310400400140603901521244600210140c3d60700360642d480050f020301400b2500625811442c01042c00f52040c406c03404058582840410b04102d0501d0001c101d680c010750260004440040340c60000c0d014110030701031743c8810f8048070040007a40384c001054950994004031803040c01e0301ca603001501e0800c100000e032074001c1c0c2c1181c200d00c22862110028aa040c40100880d50785a001303003030811200e99213140a51140d81001202004a050940c03c1154603060070740e50007a01415007000002881544488802d40c0c40100700010301e0080b543c4014030038102078000340251042515106030700350703048901c006180c0e820b10041c0040c541094030824080c0c1241000c4200000743e4581e5440c010607420b0480014581000500c5035200c43c0d500c40c0e504040c3d9072810302c5060304668019448090412244841d0751068502110031b60b5907030080c618024902003626650308003820001d407500002d01480c0046030614020035031600749441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 678155053 1250 678153803 678153809
    0x503011a0f030c060708030f1e04062f040f0905190b0a0302120c0f030d0207060525030f0201150312110c1e090a0c17180d03140603010501 61
    0xa648440c0401010800c5080c540501c81c0903050b204071001002607460b0741d00203161260080c0111038072481e081d4494014100020113421800034503000040103801c07030003800d5401c07590001c0003080300303120320300da042606081202a07000001500f103d40010340c560750091003610760b800c800415658480c20050180e4000365040300b00c041c01940e100c03104c1e1045502040c80920010007408400340d5a0300001c03428154800d600700c1e40d07007244480745003520b1700014012800406070050071800361003e50103902ca01d4248034074824440e0001d81c5080540c4072141d2440035070402c003002c0180040c0c500340188190700c00c21111016602c1d04651464594204468000b100c2d8070642030710070700c0e94071402150040003002100a80d0300c1507468160440e6200554002c0c0f42c8070007409016080707489401c0043c8500301402550301c0da490306640125069128803481c0d6462120840c0c0e40c000e80b81c0d40342c0f052259404590400700e40c003600d680017181e143c2c545c010100d01a00700d1901086903c580341010301300c2c0c1c403e00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 678156303 1250 678155053 678155081
    0x70b070305091516110d0c1709090a2a0f030e0a020916120608030414010c060e0616050702030703060b010c05240a023906010e090d080f01030f022704020a050301 71
    0x2040e46000900d1100b20300c5410710741182c0c00b1b042c10080b0b00070804000c002c1c0c5017580c2035602e03821720314039003184072401c02ccc4602600c45c11002202018200500300300544d04000080503103610250154100c00c008803040c0302d130301820360346082c640b9a0400c04680c03070174400b00e0700140b006510b88021144d035005420649908034080c5161034901340d015442c3e00c14480711503050051950400005c40e100f481210311380039598003e080c0d5460a01508544d03613092113404018444280801005a200010100305072540094000360030600000107071400001e201c002403242c8030f00c014141b251028200580050501102162010746440003071106030302a160510000031010210381c0c4c00081041d00b03425914103c42c0c1c203004103207003413101141000030907080304050171607020500c03400351810000303512060781e00d2070240158200300c4480c0701c0d000410b10000d40700c061b030a040401595103130914074050210b000c4055100c00c603400c4140c00d4200040710282c0c03103001c066a0029041c201030040d001320f01d01807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 678157553 1250 678156303 678156317
    0x106021f020d060e0907030308060114030c030604020403051603051902030a060f331706010e040302011503051c030e0304051306030503030103031d06070b070305091516110d 76
    0x20032210029000300d12500800d5442d020002040a00844898064808600034081c05811418040d0461401421705070401800c090300003c4032196030203a0341c210300c01e0528259661a4000080d0180c0590b070409071440c0507041c40208044008200d020460348540140c0f4070407151a0382e0200b00250f001d00194064114101c0c6078000703503541c0d000d02c0001982202c0025031042c5030040d43d03101c0c4100d030001a805004d48911172441c685084908000b0100440029400e210007078100d5250303401880f4500d0161000030110b020517000390004491582d2000f18500120f40d83c0c03d04540e11101c21001d0340c01411160310b1910018460f005400f14075880d00c0056141c0351506003400800c0702c080c54042c0406589100220000b4401d0004500840c081d9640042e482170b031111400c182c4840e010305034851035081154038009814114a01c3e40031589050004907a43c030401d08030706044000042450403190308040064440748144108821b042d981d403054121401842001da640e00000d071031401123141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 678158803 1250 678157553 678157603
    0x607020112140703091407120215040902030a0903031d2805010e01050f01080106050108070e0d06060e090f01180b090a050f0d0e012f0a02090f0f010602 67
    0x10081140c0c1840400c40c00240d1280c8080c1050381d407003081e43c0d0440000e840d0b5404400340101840d00000e18000c090182084c40d00d41292040104490b080003401042403012181108601c0004e4600505035100250340d240740030301b0701e100248106e02e01100841d2402e80c0c1c0e00350002400004011a4115000801c2d500301e000c6500382080285803903140504610030080380000e00c082c0620100b1800a0700082403a04000f200c40c06208016042050707a40e152850400440ea48019006d4210669082451002c0f40c0c10300403410803c2220000380805041050000f20030300e1a07000c40307105116038000d40c4c004003920607009003600c1d45030b2404101035012500d00004204c0d00c108041d00180a00d0480304078901c29a20030f42001c044a400015a4000d40121401c0b02d0300b054402622200901c2d08a800200310015600c40f0ec80c10102d1005031032006011440342c002c108459000d19800914443c0d0304c1c0742600348500c03401001c55610480c0e0511400020384540001103010320280710035a40d880c0401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 678160053 1250 678158803 678158807
    0x60c0204060b031e31030e060a141e130302040b0d020306010306021602180714390102070b04020f060c030301060c0f120e120c0307060c11060307090810050606070201 73
    0x980202d1724501015101c84516500c441d4950600300500c80c45d83e5801e4060a0190205a0008003c0d020311403c000c0049016071081407150064407000712241c0f1020100b46440021a07070100104107402c0004001e14400008a00401224800c44081c81181144070900043c1c82c003070740c8000e40541c000001440040ca2a4001d428804064511004902001c4d00040c000c140a800c1c215800d030300c04414000141d0b070159044000c0785440301224540080c200700f84c0c1c1c000c205101c00b0340c01400100ca100c1043d11082c803a000905814000030754690900c0c1c180041016816130b8124424080341c114550a4242078054642525110014606507840c04000740c414084100c000c541030480c000f1254009204521403c811101a9030359030480b601000c107000049414080307601495100c000b0700d89450b81d0010350030080c3c800fa0b01c0c0000307800c05a40742440d4440000380510394410b902004100c0440d40c001e007803034102c07020302c0100c5907580810341f0080b040303c50a490280c3c000c14100002c0700594 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 678161303 1250 678160053 678160111
    0x118020405090a020a0f1701091101030506191d100602060103031d030d05070b06040e0705130207060f05061c0305030105010c050c0a15031d0a1b090501060c0204060b03 74
    0x242c44038155a890703061640024103e1440740c008510601005400307100c094440a500300780b650050002700b1090f849d94a802054401110000c0d04054032000012550b498811212844245100805035140d0b01c0d0103103404114140800d40104d10032140020750742e4140c0110b07200031610180c01a088a0b402d40e10110703030780c82c0c103d000b590a0404041117986a03480c200120700e40d410311542d074252565603e1a0600300351130042d207554411400d20f84c0e81c040d110030200c0d9400031208100c44902180558201030406070044c0440036007924503000c0b0560144140d60401403250314101c4a0345c0c1075800b2492100c0c0145401c1d100a0006030b42400103029950107064048e00241c083c40032105105074010000e240054240c0000c10018150b840c0d600b1205c0d0140506080301c1914040704d10516420322080c3d03613400351101c0140041205a10158600000764480000b0b41401c030b005001c41d607120000600700b03200f40fa4089005924215000840d40e41c1e10041d00c1c0140343d40b18a072840040c880310025604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 678162553 1250 678161303 678161311
    0x93f0605041115031e0c0f161104200d090507090c020d0203130b03040303020c010c17010f030f0b1e07050703121103180102131215090b07030207030c0215071101020118020405 77
    0x690000c2100c04940707c4d1140140042601c0020040c00d15500e03481d00b400c4042c031403606503000d2801e0100600c86c103006a10410f010078009824103071101c0a50030702c400a41100c05000d016401203135404180542203401460014801e07408440129240c404102c1c1d03248a20300320a101d20070301d03072002d100f000c000000564200d130180c60050300301900003060034212444c501c0d0708804104481040240080207451003401049002d030340017440762450f2942031140528810041c081d4101d074001509002d800440003108016003081d2038500d16000038040d109500014043d80440e942a0b003a01d0100400c1c02a041484d10030506c850070b6450b418415102c4041e404200320b901d54090024103410604201500c1c001c1c81d2300002161031000318241040c02050035103401403501e04210985000c00d240400b450f130080414900140c0e07a94282c20300302c40c05a02c82100035486a544400c03800c1103010403010f00300740c0f4002c60f4042180d204503c016801c039002c06c9030f00000d205518110101620346540b0a50348 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 678163803 1250 678162553 678162571
    0x5190905040206120106050a090501020d1b06180308090f0309011b0201020109060f02040311030a05031e0c07061715030c010c0c0b0a0f093f0605041115031e 69
    0x1040e141c10f1900c1504c02d02604000001403000c203201003e070f41c0c02142c3e00000c24007030010b48041d02040c0c9000b000c248103840780c802700d10456050181042556030000c4c290140664101c0f45e40d4907180740092aa5000360754400c6075124050026902000c088112402d55005031148038581d03c0040c40b0310f510019508099043d0b560b182850401308ac030034010400400341e50880140e9507421440d104990318022562503003e98801e25030200012400002c403007400c6594480b035032513048240c09135110b600c40c041d05102a0300070755400050b09600042004240e4106802070061959400d01c0d19100301c80000c03031181c0c95888064210245c0d40651100710031540900b02c1403400315101c03042801e2030303440a04a074001400001d01800079950148100026040a1004140a440f000c1800c201100101c1050341500300f031003081c0d8804a001c2d80500c0c0d1603540407a081c80580b8007810700600c808224076040e4003c010340070310108811940411a4850a1001450540d0945804070762a0820004144002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 678165053 1250 678163803 678163807
    0x61407140a02040504050c100503240607061a0a14010e10170f0402030f1506040c110d08010905060f03060406050403090302090406050901110f09090a230405010605190905040206 78
    0x583c40b075000d85446280100010084241d0384014007000307402002d40d640070004240140700f403000d0595801d100010401081c00010840980010b091780b144000050105192600f444881d40b06060000411074081b102ca0409541e00c5284507400d140505125001a940509140d05454001c2c00103150064074030f8040365094802048150302c1805445010000c0d804200300300842c50704214011200c4003a4001d4503281001104810000c01c0103080340b44250745851841348014454210032104160200446003032104101c0c0240030740380c080c0115050282000b0000708103007401c0e01e8032a03980b00058002c04880d50346440e12402400c1c003030310840c00c020100c403000001d0b035180a07130140140e015210003d030500300a0078071070031500e002c108210340d20003d010400d1a00b2040058408c002000d6840c002e0554035120080000c00ca001c00001032900003182d001100c40084122501ca54401c1e13008100060b1160100411200c2c0c00c03400350030201d8080824001c4520300d03000b81d50010310203843c1d0781c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 678166303 1250 678165053 678165073
    0x2060d1e09050102070b0901020a0c0f0204110409050601021e07050f19031b0609050d030c060e0f0c010e03031201121e0f031b0c0614090604060e090106140714 70
    0x40c0540d9004402582c480c0c4d000b01e0fa03501801001c0703205503040807440303000314036140f180f11000d4101302d0700b1003028042805000c100019515284c2000b880d8901c01d926140c0e0700c985410050004040c10b40d640c1d4010301c1210349008405010418581c0d9031a1080c004080c00c0b032401d407c101c0c1703070440c2d000359907040360000f000f403000312607030003402c50241d8407813800e507400e009410744500b8a160095000408206000d802040b60b61103590000c40590340501e800c828801446c1842c0f00549070303161000009200d10002105120b10126240f0540c8200360b95641900e18507004041d500d0248104492203442c250004100c003a06101f51a41151b100c0c091a80702001da44030100380c1842c01890503191090041c1c0600100340c0d02c080310600704660b81036940980711660301c5d1000c41c1d4045008500c14005c0e448003d8860b903040405440c005080200442d5403581c45960041c15401005056409004104004199540102d400b0f1844143c40d120783d40c240345c1036840d41254441d40003050807140c0104403a203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 678167553 1250 678166303 678166361
    0x8220c030305090112061206050402010e09070f090902191808030319050108011b050a0e0909030a09050102031c0b0409210219050c10021e0f0607050702060d 69
    0x580114000d4035541e0320b031111000054000d502c0c10b41454440780c40c2040500c500e41007560200803081e00040c00055035a0b03a0310041e40e54504002c4c1355984110703480304221440b5880044403a000b00141d4401c101c55985250b5841a40074500c5048030b60421898812205c500c100401c508029807200241d04071503541d083ca50440e802039828a0300081d01c02d402c4603c0c0d0540c0d001d04d90041c02907000030098401742c0c03148400c0d507986480c0030034100700c00054841c464600c564905802c0d02c0c00284006010b041040740c1569036403003205954003007280380784001ba003980040203540b09030380180b07840021302007028180c8008200362100c1a5200355a000c0e5240030840906100d0b805003262511110060f14500020b40b62a2000d5092002010704000c0c003030004070081400702040d101501d007564800100101a400c06000c20171142070042c00e1409107407040000640047c202d40d101083c2c404c0ea4031500c0701100c5c58850840e000e500164100710b420741074031043d4040880104109003601d1840402d03644 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 678168803 1250 678167553 678167573
    0xc0b090a1703130501080103050d08150a09050901050a05131415011e08070f1707030602030f01030c0e0708041b031209030b01090209031e241e01060822 67
    0xd5882a0b0021405480c000351503024100503010900300341403258919901c440c1d4951105a0100c2044010342c04250652284d9150000d000070080c080c00b25680c0310107a01c8004c00c42221403171510b60030100403c041082d0f41c45190300030580090955402d0300652a0069208030108900010b4410b21401c2480e002900c6810f9018110000c0c3d007084c500c0340200280804a540d07003000302680c006141c01c003d1501c0b0b8103041e0045888c062200202c0f05800030880d802c044c02540003402c3c032030000082144c0030040000e0035040c1c9104440150a00e40c40d8a40381214040440e0800003042c4118041404180c02c0310704590145401c3d140441101d88a540703403900300428004040c0410f502113014000c00182c200041d014244001c0f0031410241b071000021740e9502d50450715409001641280144204103004540e40c0034040a911282070b9404140d8841111045540c09003449400e841000b11301c8118a9081c1210140c1e917450501d615030380f071001d480c04081461008070040f001503580008400442c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 678170053 1250 678168803 678168839
    0x1b080a0b06091b0a03200f071208060303120402030a150609061e03291e0601052a0c040617010b0a1a030c21071202070c0b090a 56
    0x80810190030701600340038101c1d20140070602807125124458000c0c01d40c0e8030503164800328515003c90212502c00141b02491611408161000f00c00241680070003c000003e020aa100311011901e0590400040320309000545a05a05400400000081d01c0c42e4403034554006000a096940021283da2101070150095150a216644945040059504620520000300001c0030700380b0508041401c241414a01360000401100c00c0b20300501405181d030b000100070006c085034140b82d5007801c11103043c00410002181c41a0500c9100107100765104000303440043c8800200700d01218200a80c500b0002605812107034144503500044505564600504005103000d80d8502c0c110011213a429007507a52618119000342e0030190100b01d540156081601d8041c03181c0070302903c0c2c0d00e03400c40800562041c0340b80003c80c49034084101d500302494544050103015a5255032030101c0000440030240e000c2c40502900d01c2d440c001042103500c0106000304801c140041034910241e031281c072220074000780c1d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 678171303 1250 678170053 678170063
    0x70606091e0501060c02010203040e070e0310090501180206090d0204110a120c050712050d0209040e0f070f12020402071703042103021e0a030905060106020d0e0a050901031b080a 78
    0x380448404842480360b070b8054801032802c540310070800e80002c3c1d80c034400c074807800d4801c078481c400240019205800d40902d041004043d960f14060002140e0090000204156515482c1c001c283c042e195403008040052580a8003080c1064112420090095220842030b41c02945955159941030320107401402d0402c1c9030740718a101e03100303a94659422280c08a4005007440300400400010511070100d51819403428034005958030340080c00c160190003000c4829030841d0628041401e1400081584c0d807000d00c00340c0071140155960700d00c0740c4003089107208030405089030509060141c142034000f1305c04680142030401103407486130b481060303c3c0d0046034150748811060818104206500100c20207400c1070b890198140100f0414142401c01414081507800e940043d070b10000a01035003001e1035403a00b0005550312903940d031a020b91551840600076000640965012446150505d008400c0d0350000e01681d000d40c5c21541c9021900c8400402c084c40000c03601c40000e20038608014940840c0c2c811 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 678172553 1250 678171303 678171341
    0x303100302041e0518210714120441010f09030c0b03010503150609070e0d02120705030709060b07030e010c050a030504061706151309060e0621100207060609 69
    0x5d0074a903003010b94007000010351045850350813072548000b0042e9900c064005040d00104410012403624103642c080c004400c4ca5000300d03000030817030340344104800108140282103000f04406840ca030803400100d580303d94480c0c5041c81c800e02952150042c0108040c1c18188203880303c0d16901c0d045260009540500350300714001005001d5402c0130b002c8a5140350035140b80b00e42905043e03001a0b4100001400346040007400e41d06108195165103101c0304454015001104900c1c42860f19034031042e0500840e0300902c076080c0005507500310381c403540c0102c441500540b8106650342d034081780e903000c0d4004560304121000200c6030100d0070034002032003410b109841d0075036168036103600903010089a2441c04100070489040240035165004521890701424608c0c0303588181d1080b111381c944d0116000f00190510704480405c122a50881c2c25010302c104484100c0b0403a141140d002c55034000b500b080d840c5030017060403050150b030ba0360081c100341449600d000c50000d458401c074034111041d1585034085043c0c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 678173803 1250 678172553 678172591
    0x3122d0603060e0d0806041806020d0902040b0102030c150c04050a0801090c0e130308041415190c1d010509040216110405161416051006080303100302041e05 69
    0x2503c6062658030348038014140003120144003a00780d440041059000700d0310345410303001d104410340f055140e19621400445d250408020414010904090308a006610348004140a907000206542040e0901d030028240310307a201303001024030300003c0c002d0314200030b00780320104d4955200c2d161740703020b8140b001c0005100040c50801c141c8031883c6901083c4403000d028140942508142c600d81d99498150401c172440b9119403408140390502c90034885850700581d0b10000c0300c008588909401806c1d0440c00c0b5100804c000c2c1000304a5911032140070125a500034041400080440790400d400c40505095051814080118007a688005090190360f0500401007041200642021680e02070607903003001646440c4441f103051084600090b8180000c03400442c1d0303240d110303000320342c50040d4100120105a0f500e00e010b41e61003940401e009080d07420410041642400002900d101e540c030b45400203416031454080c08000c140c82002042c82e0100c40c040c80f8100907041c000c0c58042d070201c1c40c44180e9180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 678175053 1250 678173803 678173813
    0x3030708041109010311040b030705060408161d07180302130c021009030210020d06081b150c150405010f0608030903070b03160806030a14150703050403122d0603 71
    0x1400b440040c8103128410042c0080303440e5010940400300306880000e907441100002a19120565100c60340c0f0003000200458400c00101d401c811030584011b01c2c15040361250380380c0c803114200c2c001c2904400c900b40009000144240700c1440000848036070200e203d0346980120303144010500340b400ba42a114600c3c4070109604100402070f80b20182800c000b00d1217a554003e480d200e44492803403000d038010402011565840d80302c00000d0500390200c0341040c0d0018202c5000303030860505144100100c5403803020040c140b404a40c0c800202c07802400c91525003c1c03140400c0140540165515036a03921440500d5003d48100006089843c00a51300c60200c03004040c80e180103500084034001050082c002600f10300c03a854842c61036a814541300c6580c0c4c00c03001c0b03440c0c4002104080c1800c811241710b4000b6000100b8076171520040e01210400342d598128055040c2c44080c0d030000c001440e50790507080b0207815a4060981e20094201d1111041c0744d10100c0301c20f1043c0304520a0758940d60f8602042046 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 678176303 1250 678175053 678175073
    0x903080708070c02240d060315060f0e0a02070f0614090606100504170313060c170406120f02190215150a090c0203072f12030703030216050303070804 66
    0x320162612100a000e02da001c079509040315078170102c0440d003a1030002000442c22041c0c0382c41c0203d0b146c003003260300e42c1c80c10b213078a54078001c0d03c100600b00d140c59030105004411418140644401680003103650700c820f20030390000c0d8000d05040c2d030449045903040000400b80e002d603000c0840c100050f14031341c0c01c0402c105070608001034001c0303201d010f44009a104054000041e03600306c4030b0390000f11648406803580e180c114880e4400020403602d0700c41000c96900e4100441440c81c9004400d6034015628904112645d449a4010140403c121743c180303100c881c0743e03a00914200c085840001d4100390001c03080580c800c2101030100050780143d07401c000e0044d20020080e62110b005400a82c00118080128a810030140100304c0d5171500c9038040f04242e4000c20445800e2a48202505516607030700ca00c02448850b40385e50030003c0347c1a4034002001d860800d071030b1aa0011400d011354580340c00d56409a000794441581c41815070764407100040400d000703202551090090740c60398039082ca4607140ca500c040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 678177553 1250 678176303 678176311
    0xd050a02090f100911091f0e150418060801020a02010605010e040b0d080a143709061206051c050f0f1c1701090605010230030403050408010903080708 66
    0x160441040203142d100c06603003030701216001c83c0000380c00120704001708000d10440c40c40d43d410460088020b40c80000103660750000041a03920340204280c1032041001c83d600000501084401c240800d01003140049078021500f03400301e100089060343d03032103c50f013a600b10304015000b40c0d40d100d0080000e56040b4800c0d00c41c51908440420540400c1c03800a403003001d4030100035040c01c101082350f142c030303074010302c4d580c2c1055030502801515400c071012443c0408081401d0442142c5c07044400c9071a8080c91043c8010880c00c58881e001d06a04140045410b00f64100ba80c0d803100b40c80d60710025468940c00003286100804d142e00c00d60361400d07400c05034580b0707c1d1181c035001140c5c0711a595643c160804901c1349400130034800c81c8055454a0314040760030040d4a801d04414082503400050401c0503580b01c82c2c1103560a8080d202c0ea0700484203500060f202040f10960101083c0c0d010741880c1252000a5610506c2401c04a0030107031100e04035801c5440c005001c60120706400e05000540307420a10080d40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 678178803 1250 678177553 678177571
    0xd032d020306130b03060103060c110a11210601050121021206120d0203091020060a0c020d0804110d0506010b0c07091e0504051e1506010503060102030a08150d050a0209 74
    0x20200c80d0304c02280c2da0364014800500620366540092040c03610510b513501410141000b1144121317000c1c20002c1e0781b01510410300d80b05808010b4448400c004101854100030144c2d000f4000683c6403800542d62a520000c040e00d580c60342c0b08005072008801d20107481407000ca0303003903a400d61805002b48000c0850942551429a2220003005251030340001160342481003a01c40e0340000c407122070306444e03445000101c044102100c0484406032100003034014402d9900766800c0c0610071212a041e61181100010440040d1654000a011407104000c8200d09140540410003241e803d4a410381800030030b030000140c861000a440107024400c104110290810032410001030700251845010f4010350174444400603241d03c001014800c0074441702c0c203107000c0701080f011071600645203e40c0f5001c80c00d0305200ca0759071041c00b1079080e5208000f80c81c0314076010307002540b90a240c82c5003a6070404008180f010394a04402414040380c81d2410070140591040c1c005000340040d51041004c224401006030b03030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 678180053 1250 678178803 678178811
    0xf1d10030f0e160b09040b0409060903080c0c1e0f0118061a0d110f060a020f07080105010f050d1104110c010e0606011413051903020901080a02030d032d02030613 71
    0x143c502140e281142250b0b0250300056441030140041405024512800d6a00528100000b002d10030705801c10842c451080d42c90801d17554540350b242c0c00e80d00a802d1a049aa804a150300000b054030040c403049003c010340840b001c016001c40b420382901c501c5460406446e4001380200104911800b40000000e500e0b25680f807550b40740c00c0899000200d6820180400c00805a02c1c501c0e5107032000c1c100021500a083c00c2da8070b070401e0700060341d928a281107014852140090010b070002042c0719050685580c040c8070a6130034505400c0216240e4484000d944100d905051448181c0e5036110380328144910b80c60154942c8a050743e050b0840d1000740c9491840e0308100c040080076a0700c03020b1390105205000141751a00301d07001d814050742180e80c1040f07410840b06605060311158200e811b034200c1e4801c5445c030b9150303a280c145550315000200c80094041e485078100840c002d010307810120302d402003c010340d0300500c07469200f54440240a00050f000d0340c0d000003409203038245500c421105642600043c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 678181303 1250 678180053 678180073
    0x609010516080403050c06010801051905090604030c051c020d030501240f050706092012030a05161b03150b030a060902010c02060301150f0c030f1d10030f0e 69
    0x941e44890203264508111800c80020201806a8103440010f178018048814641e103900b10b6a00074081540e1a140e202d00320300004801c46080d024452140100c00064200381e242e665003aa0104071800e4102d5041c042c0181407405070001e504014014082a8003e100c4c8407640347c806412a0010b1b0000000c03050392100780b2005058103c51040c1c014100c1c0740c020300381c1d00d035500103c074180103840d00148050f00700528101070248010314005400d10032110000c60385911000c210030141c08071030f110001d400c02e1222180660240e00541303603c3d13500514962203803d0340c4d41d8002c0b03003040e14060b104c0c120707860120600501919150008003c40141c004102601102c40040ea581031103443c000c00c403985808184045920035002c0d05900e03139010700216102d5842e100825440102006420300041d1a00300318405203114140315003600350541c0f9440d41d0031054410441d02041250035110f0100002c45025480b9190610200305000c015500001c0c520000d12149090708e42124250749150f1000c0d2102d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 678182553 1250 678181303 678181321
    0x6090d3f05070f021201060b0d0b0a080d090909150906380d150603080a110d050403020f0301140c090103200301150309050a06061e0f1a12010305070806090105 70
    0x80b0240c44e0121041072404484012a60140103103401218903004041042c1e07a8032581038001d0499141e08803020030501e03032207105c1a59a0482d1411300c030000345034054108504002c0b50b0003000224013034194404899581681c4030144e03440710f00115092030380c40844401c62051032191012640641818440007120039950b52418146818954800e02c5998103800821020091243c2903400c8080280502c3c0ea036420120300c240c00490b28000481c0d0400340203182842c0114042180da020b54a4050416003541c090125550302e00c0c003119055966408281e40340c089200e2094070a16690341d0296079014000300040a503290204031080510181c100c101c22800202c0659055800380c0d031a100030602903200480c0581f454500241440c0560304041c0140403441c1c0000060300c01100d6060340c000040041d0681803040391051001901c1c440c2d10038000201c0c44d03540325012440070081303103080c40700c01d00315a41100000c1e1300440381a40082c40c2000307c00c20a000c4582c2c840c0d299070081000e07207808191 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 678183803 1250 678182553 678182573
    0x210503030613090609081b070f030f03020c03010f05060406080a050d0e031f020706110316030b0102120c060114150702220e0c010206090a0206090d3f0507 68
    0x81c0c0c49418200341072030015000354440c102254000e0028040c100d0745081102a59204100b0324042c140c5001010000c50300006d0110215818841c4041d074280c41d644540301e0000290400b1006c5001712854a80c3c903940901a410030004103100020362401d04004000c21034080342d20040c0140c2105007040007040b030100f824910300c44107007003040740040f40c000080d04181521500103045108003541440c2c0400c1540a450b003a031143d0000c015852901310001c030240000c403640f8144980d689001903046110b904207168281c0180100c0c3d40c8810320b02004000c0d500000100080b6a110800421010190200880300e081c402d0f620f01840e5940501030311200e11032981e019018030300110802a40302c00c821001c102070000c0d0102004889042c42c080ea484035450755040c1d0040c072504000c58822500031035007a0304994000c1c90f0707030b2a06110f1410f20042e8082c0c504140c4080c01050010354400c05042007590b0b03c55007060134040c002078000400d0780661030100407841000800e205a800060300740322 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 678185053 1250 678183803 678183811
    0x4152a020105031305070b0a1101060f03080702012709020d06060905130b030304180516050309280212070618140603150406140f06120c0309010605180121050303 71
    0xc84c9605144241c200b1070700d81031260b403201c1700c4c042c00001c01808055001c4800c81b00e64a03468024803d9940c0c400e0100315030032032408050070402e0b04000140c015800744140e900d10520040032488081c0b5120038071030005d100350b4448454690002400211018a40700304c001500781814140c035102d09002c081242644840d001d811000d6403641d00200c241e8080041d2001415070648441910703a610340741d00702520b0140c413a40020000c810740d00f9402d60042041c0c0e0300c44c0ba0903078000e04051007068540c1a07440110f04040070b0a28041c0c80c81c4015855412440d4000000b038030040240625089001b821035130124010265245009401e001c0320118140340704249004480c2542c0302e486021000700d41454040001d5800703482c111000a10b804070390540400d00b50101d98800030303821520309200c60391080c40701280401400b10001030322030003440003443d0028041c500006619803244007091984007900000b040301c01458004000310340d041c12045103441c03001030380584140c0c1c066890030f59900002d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 678186303 1250 678185053 678185071
    0x5012a0518090c070605070f08150d0c03030915091401030905161701060506090d02010c0302030d051015030c0e130e0601030b040b0c03040c03110604152a02010503 72
    0x390340d1048240c94454429084004140980760f0400150b9880e9590103401c00b101c8171810480041d200038020b0511030040da0302d50300d03010040d6903014007600340140710300303ca2030b40f140308080e1310400314400c26418006988640c0310300f003210f41854211810300e0a080c280c4c0c02007120340ba1003446014034041c8103001a03034082c03c01280d050881c3ca001814803402c0c4480701040558130100084095150841042c1c1d040760340020011540c0b0780d82400010710400c04025001000c5c0141d0a005522a0078100d03c03407802441581c0c18011484010303003d5a80558103a4050b1107411801e00480f10070000c0c1424648040c141007000c22202e00c806421001032803c807921510700307030203c1e941c420f1407608208407002841050314030562b11f030300d018056450140c60540d00c07001c104000072a0b004038001107030700482d0010040341c4003525641d19006040b001c1c0c1c10706500308006201c000381d00903041c0034204000d60b40d911011144444901c403002401c815080c0c0c41e5481700e0307020b100c10150341c02c142242d811650702c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 678187553 1250 678186303 678186307
    0x905031b1507021903111b01031b08010509040f02030307110915010f0305061c0602031f05031b041b0f0e030d050418020903030a120501150906050705070f080a05012a05 74
    0x42e013020b03070740d00043c2d4005003c18003462003207480c4010525491f55076100d00344c80030041001100c800c224007810560788440461840b8006120f079262000b141c9a10500c15514402000f4556012074219000044121400d4008050803000707450b00304000703980244044e500090110840b40000c00301c610460501040c10340d42c0b0003140441c0c031000c0308c0e21203c445485c103001d8203203810b1420a0080d401102c00c00003401d984180d604840d04104200000c035940100100510b02c03d6010680e49141160200f5034171550700c2c144881c6e4036526100003945011603441d00d1300e401401e081c0c00b404108003203030f00900ca60408410407640170341001c240d40c103990b0000302640c2000b101000010003403081c1d03000150f00d440046200f6002c19400700b0424600c10300c8403418003031a640c40e040f407100080382803c04c0d40030a10456091143e140b00d100940051070040e0304a80301c040da03e0713142c8981c0c145c05411540e450340190410b00140002401902444081c031807803015050100115640702c440b1184510f8208040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 678188803 1250 678187553 678187603
    0x3031214150d060902100203130b03060f01120204051c060513021011150a05100621111306111501051e0d060c08012c01030204020d0905031b150702 65
    0x1940c0c04541130542c0a40841079940c51340c40081e42d25007003031030407a042e504148000b0841c4088002624000c041c05070102d4102019440103440f02201e80c0c10708040e0b00e909210000326070707541c00075038030301c0c2007100400b034335181000e04088051340c80c0207048016a95100d10158016102d8007010035170300e1100d107080510410600d0400703040c0320580c00131140329407007030050108800513035001c580141a1081902c0519a42d00c0080d69500b15107204000349407492383c0094bc103199030742c008e44890250b02041c285840c00942106600103450303044000062200c003602081400304018503003515104503404010b40d85480001903d0718100c090343c044112551604900e40d894000e07828880c1c0394400c00c180300718400341c40e006002803000d12512030110f4030701400d4110314400d003800070038040c0c03180640c4d80c851b806c1d40c00b0302020b0340c090308011030b265a4500c1c1480200c0c60520207840030107503541c034550140c08802c6009241c004484d050046107080e1310b090001c41c940000c1c01c0d40c40d9103400c0035030303d01c0561 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 678190053 1250 678188803 678188813
    0x20d050105030a0b1f09050c0421050a08031b07050c2809180c092a020c01080c04050d0b040c090501080d0309020402210702010606030b1e130603031214150d 69
    0x1442c0d86c403008a00c2d0501e400d200490103540090815240440c2a11030500200c0058400d941000c550207030890304a0100400401e9a001c021540004540b103402d00321402c08042149a5016450a41c1e207508108120409854036949508031003140390b00c0c182503d180301040c104001c0f030a1040c0b68460341d40340110300b50546440d514000c25600b11741d540c00000c0d922524400584521100600c043c041d07000f80d800c80d01300f4190b6804448070f46900800f040c1c24203500549644901402c6007181c10410700c80010b85030340f40c0001d1168a4070a0a20a606060a2411110004c500d401c85110b05050034014420200001483c0c049011949008075685103107001090091150300a149208400c2100c0c1c28604a900c1c40c0560042481d03500800100e07544d00b2080701190721154a40b03074402007044940c5c0110b030f11040c0600d100d81000385081408003403031480c9000c80e501d41e44100c0c0400c00c1d2054840361319440d44950341550080102404d481d1502828506240d030a104a45115000450202042c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 678191303 1250 678190053 678190111
    0x1524021213060c1109101802030f010e06030c12010e0f01020f22050303070309031101020d0f0e04021b0f151302040905010f06080f0c0a030c090c110106030303020d050105030a0b 78
    0x9102605e04096414552059000200300f4011616000640f0300041c5002c26180308681c4a060140c680c02043e03402e24607860391300035001c0d01140e814450512080629a038460714040c400030004000078108036840c0125084c003440104500140e403041c0300a400f043d9035502100c1aa0079880c041d0700a02c40d80c1c8040e40b4003844550800c45c0c05200c00f240c1d503020581c0180d0400103032030092820b00001d0540300300490f59060300c00c20300000a0307810340c14403403458041e400c40c0000950007000541000000902000d9544401c03d0008495002d001c1c2200c0c0d1101c188404450340451141e010200d20f00005040d0000342c20301c0000303004a50700c8680b002800020f5010101c0000900000d12000382d45105403540e0301a01451545640991450010304d807624400f00000c503548808451405490440c0c4500101080703448803052240118a5030b194400c01c0c40340d88003461013074500580310071961240b00200c0700142c100038040d5202d1400390780400c4601f102c15a100c401c0649103c918050501000380c26 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 678192553 1250 678191303 678191333
    0x3060d1101140a020a0b0a02030411150702040203100f060507240b03030307080114041a0d020301230f010e010b1e0409021b060601050703050d1524021213060c 70
    0x2c0e2101164a518166001c034901158a0061010305010b45440c140c00040f8401510002d115482d00400501c01741004540030300501021280e050600340503070081000d80c1c0c0200c1e403400000716400c00a2007507101404043c2c010300200c4c41c00c1e5082007925a038180290100405134044070400100c0c00e45401155013124500c6140034098035104d0420321005800b448007030150f120800b80e04800f001290916114550089010207103000b09030030b03071105008a85403141800d0b6010f548030941ca8806070481d402d540b0903c1070a940c52407403850142905000c242c41038020b0b04501031b4480041000300d40c0c00c0c0648184482d40d02e903000e10180005800c1c05244101d511a00c45076002090b14810080001c1d4031140c2004130300103a4809642d2280111414490044010f003c036000380565400140c0c40e90000e200031608020540780103485103100420b8400501c9035040290f000310318000c00d1681400744a650182d46a491420445100404ac17010380c0140110010800020901001e10100c040b02c4510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 678193803 1250 678192553 678192587
    0x1110a08041e050c2107030308041e030903120c0b0118090b0c09010e04060302060f0c010e120702030c220c030b0607060e0607080f0606090d02040e0c1503060d1101 72
    0x48485285402a2250038030440c445c0301380110f00da4808900e076510180401881e01c00064000030703056540654161502070000d5070060b00000016a18400c0004d44040b414069115101c9181c6036203860442241d13000244010003240c0c1441d01c0008800310001810f44403051781d071054810800207048000c02d502c0170041e0440105070140320380c04102c3d00003405004e500b0b0380c5080758007800c2014002070b01c070300e031000030340101c0e00f007080f030b140501d800e0701510340f0910700c2e40042050038540c81c0e61072034520541c1821a216000007520411490100812491100141d840c50b207142e2001c00785c8807588103408803010307089464140c050b00300303442503110740d4580c0001040d03e038175680703e810010010030266140080e188903150120b40281e0195100d0751080091048a145caa40d07075005000f0b03d50801c50060390059a020003030001a55580940e000d4130900000030700300d4030072842c2003065228514480c2d0f20041002c006100e0242c49564921403c0c0d60443e00b03c0340703a25600d0004968414000590881d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 678195053 1250 678193803 678193853
    0x1e0c03032105071d0d0c1203090e0a021206040b100806010912050d0f0212180d02040221100b120402010905030a030807090609060e090a15080303060306010801110a0804 74
    0x1442130304185402c14a9642e860400743d440e00e000e05000541744e080b1000390809000140820440031050f00311a883d61180c80d203100b80950741c00320b140d0024416590141c10640101c1c05207040c20030380308003541c440011103083c4030044600c80450543c0c21801000c6040000500029110740d00581c203c200030458141006400b6540d42001030b140c841e4100c400c0001604503c007850314903c0011190280c074415120146809003012409202c040081203d0350000318864000c405030b5114401303440300020005c1c101d10003207043c550300d03c003411000380750803198106100140900c261810030f4841407110131001408036112400141c55600f455817045038548918840c010805a10140d2507001344c9040d2030390034510352071759000c1e545241140228400102c2c0720304244124902410700c5034201b02d10480c00112600105200440d0429030f03080348020340d10020a1240314102000294010701090000700f206503480c0000c14079611800082d4810000c1110104040c0320a03640c0d0a03140800c0139410b94 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678196303 1250 678195053 678195061
    0x2405090d150507020a20030a0605090c10050a0e0409060e03031303090f0501050a0302030a1103010f0810090809060d0f0f0b04230a150801181e0c03032105 68
    0x1003040320100100301c50340d030801e808110100e0000501e0000c1c2030344542400d1500c0d4022454501e6284500801541403051003e1500460102d11440340200650406060b80644400138040e404040505280800000b00005c2414980c00340c00040c1030700c0101d41c08680c0075a0341c146400508001d480110090100006002400c104859040410f620945403100042e56815038040289514030455001c507004000d0b05003500e00c40c1d8010341e031194200030009510004028444200c1c1c101b60848210306400c18404d2204110800c800081c2081c440d9003403088188a071740303c03011406001010350240740302041401d8144026003016902d001c100c0c2081094540303800e441000340c003038603500038065032070300001d0004050a07001c0c128881440d206121410f45500302400c0042c8042d80a485907080038200c007290707081d0b080c001d031500e01003082c4403d4441da0300b40c00c00c00e02d400c52030001180c0c10445030300240c3c00204800748402c00c403030301428261410340b100900c0c800d641110865940885242c00204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 678197553 1250 678196303 678196313
    0x20702120d110102070201081602160b030106030f05130809030f160e0604051501051303020d0501020723070b0d0618051501110304090e030c03030f06030c0a2405090d 73
    0x200101c120079550280036480319102c140c02c0303100350796001c0c0c001010080000c424099101c4007800b000b081d4030443d9081d804010a0020001240d0052014038500000401c182e5500d401406075046000e00100002c5c1032000c010a51102540c00c01088010007040c40525036401b4400804810341c0d07a0f040d40c00b5090034000c01400307030669014081e8144040004592142030903c0384074030505d16103081c0b4442c40c2c1c10360019a81c1d604081540c40341d0b00a10310b0040700684900d040d40501034410f40015071610503502c3c002c01000b000d8030785240ca00395038251101c4891030018040e402c44a9905545944410345000e103030190400360003104003a10300704186211440700c0da0102d88515840d03600b40d40d9501594004441641c003880403090142e2003484240a103006e15400404418004011a46001c45011520341582c0084850300c4441d038034142000b081f03003001d12642020034030449290505030b051104150050103102d424040b203140d886030300004240a042110110344000740700f403554810030320342 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 678198803 1250 678197553 678197563
    0x109170f060c07150e0d0e060903030c030d0c0c0f0602030403050412050f010b0604230a0e0f0f010e04120f0e0303040b040602120403240f0203040c05010e090f070f020102070212 78
    0x108440c00504a2130440307803090140301e452044804440070703102d01d01d61340310308450415003045043e500680070092107803981da041000b4000124070002550b00c0b508010600b200b100e00400c0c4107001e1003100000c0b04000b450111043c00d05552000006807203441d9401d04982601458108914002c200400442802000240742e020501d00744003d0249003406804d0251500852081c004e010000c220035109542c20a00501c20011015040c5000a40d550291307485200096400a4074050200107001d08143c00382003c42c0174200c0d880c1c44a01609050760750180d81c504842d806010031941199020509201d079041c0d50b10080300a04580d02c46840d036070f012689511611401d0302510030b1203a100000141241900c0c1100d0b04829000d00344a1860202d48000071003807118140c1035074610b0080034404480c400f943c0694029040400c1d000d0410002404c580510101c00740b040f8034180410607a00e40c80c0c021350f507202c4024580100f0b1400450000d1b40640100d23840250f0105c7c1004492080080c0010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 678200053 1250 678198803 678198817
    0x190f031113060605040b1813050613060515160b070f180b090402030408130e01050f06072d08120906101a0304080403060f060303031a0109170f060c 65
    0x110500c607031035840d02190440301140300300340c0890010301c4101310401c020760181161007640c4100d01c044c150a00005411851340c1401400740c0e0307545106005242c204201402000f811750300040003240c0c149000901e480242d4a5440c407680c50003e80343c0b00306126608481c1c11664010400c0945080009000d0102403020303040c000003407411080741e040301c4105403510007200c003035103603a91408003000180300c06036000400640f42014108048100c484807074120000a02c1144407031321155040c1020406080d40e2441c04c03521480042c410b403808500010307401681181241d1900d50281d081030041d0301c0c214100c10001d020b070301000c585400702209414000f803081c03c0840560326030707568411480034440014018992107416040012424040701801180c00c540a106180d05007996a030b20340b010740b080c1d06600160320752205410003c143d054001d00c4003036011001d108203190064000240210301c2c82c410b2447e8110f01107800d4031b054505001c888800d0000e0401d90b42c46191629500300c85901c000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 678201303 1250 678200053 678200059
    0x170d090203010c0c020a1701150605040305070e012409090c0201050402031903020604030503071b0305090f0f31051611120306101e03090b0123190f0311 67
    0x4014400301d031340300f4030400c1206a4010072160340a1704204030140c2c900b0940306007642540d03a500c800d090582d60820b601c0010407513556416907441c103518082d401c1c1817550b03200b81082c80707550005210081c1408111841e440c500c10421004540b204000c0b5070a03415584202c0340c8515200c01e8116803581034220b42d10940c020f404880c880c1c80c6800e05400c1d00000081c1c0540103801600104000a20800007150884114505a402d1000010307210103d1107481030100c0c017040c1300103110011801c207841040c0d00043c04541c1500d00000382c0d40030902010706601c0089200c48001c0c115100744040e41070a6001503003e402c100920301e04024000510140c680c1c0300000316030400d2021014030320001c3c1034044244280d0280b415a01d07010180950111061411028000c039030780c4000c1e080c1007a100310701c1c080340d482d540881c0382841828603140d20281038014440c1c800c1860b40c100001044c0a5600ca0711400c01d6401d145415100f5403801c02e1450590054017604262000000620040d2246a94030000803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 678202553 1250 678201303 678201311
    0xb1c09033e070806190e030301120b090d020316020d0b0c03190203041101080403050706110a1107080d05030c190e010e03030304022101020c1f0b0d03120207170d09020301 75
    0x480207803aa1000b06202d0255190300c071100080901c0f21803842000d51014a40300415040030220500f8150780098000025461001d8040d80500008807400c60b0843c0100c0040e29248156040c02500c0c0d10075032040c2082a9024080c0004644031503105140d1aa00040d081d04c40342842e02e40403080b544144c2c2c0c0f11400441042080b41c1140040c401c0301c2c082d562144800d451108494015203c28a0060080c0d0038404240300c003c1c007280e01c9005210a0102d2171302079541c1c4040c4030314060554076400415820a40c0414802d010b900c00000d20a81481c00d1403c00d907403a076a400680c021207110307400018000780d403000702d1004165000410001c0750f5400340c0f2a000213044a9050544e240012100a50703c01c5001c100005003199908c141a070f842003200015190000080340c05180490b000c0349018590440b019a0001d11900e128041c0700b054102c51441e4004082d4078020f01c140f1081800c0040340764005608404c114544521550034840404659110325944242000034580c0e003209a010b0350078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 678203803 1250 678202553 678202667
    0x21909020c1c080c040e060406080318040c090513020309010204080a060c120b0d0308060112020a1806090305060a0c0e0a09090c05060a0504060c1109010803040f0b1c0903 75
    0x9600c00b14841e0540306603450170b20707251010300b41003c8400740c040380e000fa98409001c948490203000a00c250700c07250356030f4054803800809000450710117810120801c00c00d002c0512180e40e6404e40c028140b80840c01c003503100d8a0300c404080c02845250f0114120b4800c00d00301038100071031a0050700750030f046900c50403456441001c400e002d0350700740030380710f588810b80c0ca0000000900402206400070f07010315010b0b891b21b4a00502c001280e0051030300401045583d4a4500d444052040c00c0c0d02800c2c103440c1a4001c07038959918141e0300d400241c50042102e84840c1c140c00b0640c8510701260740068000d1103101100d9550b404540104494403055840110324a00860503041180c2210482e03001503488520b01840d01e0011500740a5100044903400010314690420740d0305d0840560203090700c500515540c0d0f15105030010300c00e6640d030144401540a20070b441c0d400205044a401c04d1003071100100744881c06150488461685034210708005100c25019146490b10f028913107542c8034088064860400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 678205053 1250 678203803 678203807
    0x3050609060720070f080106050312071a0c07050601170105100f090f020c2407110c060901050706110c010c0206161b0606080a0c1401020a021909020c1c 67
    0x7808072514408102c80d0003100c4a41c4105985404203090000103594180d500c5080a65104450303a01c50a40c0383c1d101d80c014041480c0520040311010b010716a200e1030058280d890100c545640b5002810b03107107a030340002e2101e0182c1002c403510a0b61020a49000c0e40e1100e0900241c224408004c102644c605800944c04810340c2000d1000d485145c040b10b6042440d1012640140040c4204448015028080c00c4000303601044104004284990421101411000002da03488c10080ca90800c02c40c040c0c4480149030300100308890600b505a0794181e43c3d440001c01612984140c04004005515100c044c40015005d800a40302e5204c10600030300411035000412641e940040c0d071801c40e05201500e603140041d003d44801c810500c0c070301000b80c144401c00d880c3e140848100750703c4140c040e0440d8568408010402510310302400110000c10400300150b40000d64503806588000d0140c1d181008031068045070504000041035110030035995000306032003054a40040756500303007a500d442e00c1d402c0c08042c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 678206303 1250 678205053 678205063
    0xa170f0a050c0c101e1a272d0906010e0903040305030d0e010b09040524010e0402010815031b040507030b060a031107290a0515060904140106080103050609 68
    0x820f000300184184002c40000802c202000d404c001403449a1440c0318400034091500c8183e00484000c2c9920711203018860a80d032003115400c5101e11004038a031100002d211010b070032071107065031a01c01c0c451300c80a90b480400010781c9200000c900804018801d2000a8914141c0b0100c1a050300e940e107030484035959174061400000c10a0300b00f44481d00300400c1c580c2c00f04040700032100010654170038910114496580035602a1610340185032a0382e00610641000101c032250080044910342c5413100190300c4a101030002410092110003103100541e07144e81100343d4078801400c0c0c03000440c50405e082c00c0f01041c90302c01800746040c00c3c00100c110b802486015031040020f0100c0385000440b03402107004080c0f801498190b44010f2203e0000f01d0f0303130004e09944400381e030007040d0507002c2078003460089100020302004078203050004011541c0d500c112071a403010b01c2500d48a07190340060780001e0152101c0300e00000c244100c00000150350f68802e0005040341c0c0030700d003500d450342c0395a50300136100c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 678207553 1250 678206303 678206317
    0x2010c02120702091b070317130201080c07030c02060f040306180b04080705100204270c02070b0915070501050403080108010c0206010e07053108010504170a170f0a050c 74
    0x1c44801d22440000d030428041059202c02140c800710041220301ea59010710b41c103c4501a40081d02210307010f0b190794201501c141d0404400ea06294034031180360b000900020004000814600d00442c001c82094000d0700c45c1c0302500e500810301505c4002d0b917003144000750000d10080d03c800781050b0303290300f50090a041c6c4100706a0000640c105942c0e4545520490340d00a00c1c04460901c18542c00c40802901880a4405041d112000e800703100c160303034071640c2c0880c509000700100c146080e21600e400c40c0c00150020440d01803002d41901c480c1c2000008000d100303101c1000c510140001030301401c204065001c5840742d88640ca5044250362220010303804c80712800386e00800350384030000601c04402a034460940c03141407031130044e1408c400d4008201450407120601c42040400f400030003240150501c0d80e00c040d01807071008004524250f00c40046414540304d01d20110100054515100c81c469264500e4526815001d52080d0800384180040a9011109a241940351401146844921004684a0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 678208803 1250 678207553 678207583
    0x210a0609020315280e01031a090705090604020f031603050903070b0a0f090609030f03060b0f0706020d06083a05030a05070905130615050307050a0302070203070b030c0a02010c02 78
    0x1a6407000d0148030800036101382d201c1c0c0e6000c0f0a03111001d094004a51031010b454058840326040d40755191a0f0119140410210b840c0c0402d00108032980e080010b54800b1144211605d8950362126400311b4024402d00820700c0c050180003080050f0951003410040f5946020342d0108901c2d9600c000c030715268024910001d0035508250007080d64213505410003e544074002d000050800c1d104d07a05c8030111061a401207000c41c010005021410340c0610504000302044061039240c4008260591428410001e00806055000c03e21103482003145e8407480103040048111001c462540c0e0320b04a03940c003e8030510800c9002c030411281d010524020303680003c181a240c140c00e54480003041d0025110003494501006807031a4002400d954840542000440100e400518141840501d040b480e820384403034005d100301042404159a4810200c4024031101d2030f00580303594140c400030b41030000b0b91340040e1040b1004003d1041440c210740041c1030000302c9400070841202036242c16030701c0e0041030780c811078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 678210053 1250 678208803 678208831
    0x50c0d1e020a150f23040312021603050d110408071517060103091103030d0c080f0402010801060f23090f0102060609060f030a05061003020109080f03030714210a06090203 75
    0x794640a80c0003c0c66550090401103908030000d106100500c030805c202c140c0c11310b084001e11050640184a441e028000400d056190401c1800140180d41c0e01c0078006040040003d900c0c0a55030726a17010301c622420380300265980d0307641e07005180d54030a00e13809620200c07440e078a405604580201c1c25081c0410729110307940c4590340d403103005400030300810100740d54105101e002000359942c248018403008190b0f8100082d00556403e004240301c900030902c1d07030324890040034480940e0f00100c0c0e20381101d20901d00701c40e00ea84284412101c1a0011003d90821801c4110000032101c0c10340190a1600e4241c03140e0003056800c000482e03a400080da03000341c100558601107101800d10b11441080100050101c03140090180d4038986004e9045540203900c0248075002e004540e8000307440303001071803007900801c0407a01c0e500c001e40d240c0c4800360580090160002103540300b14420020f5881d0100191981000000c42e42603900912204407904001e091410740c0c00f09010b450b510940380201c084d820941 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 678211303 1250 678210053 678210083
    0x60a05060f091609050d0506041403040305010509060103020909010b100f0203120103080903010b060f0a051b0a06050901180f12031d101a011707050c0d1e020a 70
    0x2090058040c40d0018014a5116010b0b12011042c41c0541c0501c1c156900950107640c1c01003080d601508003510400d20300440902040000608540041c0c0028654180000d9600c84900e0f52080e076000415a5003000304101d01100c0c04501681207a000782c0e195041c035a115107545e82210ba00b12082d540c403041c10340403001c1c03692040031220016800303401203030300e010303200a90b00800c541d0036401264a40f0000491254508082c00340701c81000d410313982c1c181001c2e881c3c00700710014043c43e0301d410100304000c500c00507089050103081680c0c8080708148d44844a26040203c00341004407800c00007582003281907110004a40000c507000703500408402c0c0ca55080d42d407905403050900c070b450002c042d100c043c214124401028120031404410b00105007408480388041c080d1030102c40729030400303400c03136501041d02e90300440c0d4100a03d1040e98407182e0b030b0f5079940f41560703d4010b00090390759910840c648281466001101d0302d0001401c40da0314510548043c41c00c170faa0b5248180000d006d041c080c01d4203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 678212553 1250 678211303 678211321
    0x11e0b0d03141309090501111201090504050718051f06051b0309030f0a0302120301060c060902131b08010e0c070b1b0712030b010809070512160f05030d0306060206 72
    0x308210b05045880c0b920b0724818804030000065140c00c01502240e44007070b02810003109102e803060b042000c030400c0d03052039449480301e8051881440b40c010060785803000182000014046a00900346106086640e400801c3c003040003407100b01d40b40d800c5000f20450000d032448806c2c06034411183c0642d540c5180800c20360540b003980000b10081802444140143c00340b6642c02d100806044a8110007400c84040d00d0500910340000a20f0308045a20200014080d00b42d00c81c0703900c1c0196070007500c04500c42c2540d10210300c54641c030816135800b4526007118210b407407803504c0390362030301080ca559a10340590b02d5034840700d110f04084d80e1220845004201c44400030300e4100d0744035405050895002450003a0f4280350380e2582c070840c2c04407004125140c050706895014811024400d40c20302e000000d0f860206120341d55001e207401082c0c07042044116003100c0c40400c01118401e4250322020000c2ca44c0e03100c0c0005401d036818007403d446030041c1303c054181e0b144284140012280103600070141500d81c0040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 678213803 1250 678212553 678212567
    0xb180402131104090e0c03070e061318020405010303090f050406050904020d390b0c0703060e010b0402040f06090e07020307020f01140714010e030f1804021b011e0b0d03 74
    0x30200240707800d101c005013030f0525200300015080400054108542e210741054280000782d0007001d0075208580511002c0d40381c204810710020400305000500400b04564040c500c40728080003544030341408004010913900c603011170126550805c1c03090910f5122010401070f40c01c64080c00303800c0072002d00020301502e401600da52245001c3d911003180c0018440347d040491041419510b100c03429412511110000c03510154000c002010070142040f4070004115110003641c030001e001e254548100c19034100c8294001a600d1600a008654840c0e5451041d803041403644940320100c1c208440005400804554640c81340c00641e015518291040d400c0041c4800c0001c84d10341004840e2000070055001200140314103401000312651a9201982003030079a00028051009604144240c00d14079610105950304c00d4041c030240c0c030318501220080703402401107942611981c4001124500c0013281035118080440e1450086102e50180058120545032403429881c1c025040d009a580030900c1086 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 678215053 1250 678213803 678213821
    0x7060902120706030203150a030b34030f050109090803010e07030906020c0c0a140a2303011104030b01050402070b010b2107110610031a09070e0403030b18040213 71
    0x5801d44511074405251501e5a03c3e0001008a84d000041c8091400d1403521400d4030388003115456046419540d400010490240885407078562458403400b5010509800c060280c000b03801da004e41d210345000042c0070b809541510700900d4a0240003060191490055000305a0030503405455640703043c802d1743c01010024909010155103107408400980f041c0001d00390b00d2400002080d8141032030081211001d6698001c0c580c0c050303c004010f42c5a124109a6011180040a000c195115004021031003113000c200c030f690325504e8184400c0307225030440050410799004101448190380c940040c04101c0c071452801a1400c403030000100001c802c1540140540740c8038040c0203640a106c0c01c0200340b14203042d52007501003003c0020344c10f40540b04204241d405406080718018241c5551614004820301c001d02c00c0d2000c14040001c2c82d64081000150000e00340c09810a01d00c0c90070303040080041024917551880761050026409007116030341106405160020b03c26640039030b5071140c02d00200b0a81c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 678216303 1250 678215053 678215059
    0x11070510120b030607123606090c0305010603050706080618040218040b070314040c17070e01060513120c180b040204080c040e1b0105091210090c1a07060902 69
    0x10b00d400e0290701e06101440c016129a141c510104c1b40c243c00c4901a5180c0224450004152015860b040d01c0c540d540c202403400050703a0b00c0740c0c0003010b05014010b0220802e01400d0000c00c814000308000055010604590042d0141e41c0f00c56120070040340c060360b045d43d48136400419461125001007039007550316003123440101030702c4d02d4402d1104c025903122000c40d025101d0b90401420485d800b500750040b0740c0604c0c584c00060140e03140c26a00c40707a482c04540116407282601c004000711004d4200820700292441d411071302c41c25a5102c000500c0d030b40c8014045c43d1202c2504000051810030b03840e0312049198050081405107080107604203a60494240c80c0c06038544900b10258503440e107200600203000014003a10340042503c3c1440240c80b880d003010440e580c442040e40440780e12a405180039504240b81c07080d0b0380c2107046d000034040f91211041d10518043e092140b0301c0c01a107a404801c54500c184484240310707584052a11b8404d5034100c80c907600c0c0000f007001100140a640c005900d0320301c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 678217553 1250 678216303 678216311
    0xc040e0d09181b170c07150f09080c0d030b0d12140906040f0504050708011208090303070c120b010e0720010f06120b10050d060c0e041b1107051012 65
    0x11030b450030340e8400e102d1100f800718018040a889802880390300f20fa101800c3d00c103d07071500b6a02d903645589007404542d580401c0d96035800c2c8140072000781d000f0100064100d107030641c071100c10300d040584a140312100c0c040031901e0545120828141806402102500441034100b500b046040590703485001181035901c0c0c08003000303030040c00d42d100d2001d44041c2c031105160700c40440c02e010500c82210300241000c4c00b0b020000004014040c00c011010701c40650140000e5100c0e104200424654091500001c08a4943c0c03e004611803016440d0042c1c50b0b03020703034140d403034a980c0c60500040418041d141c4030002002c00511450251311248122020b1080302c000207818000001030b6401c0301d206810880075004540462014008024811071700151345101e940c09082c98100000c0c08000800030091240f902e5211407440b481c09a0f007003000004010b04144411030344030031000c3c83c0058055402020944009410701b0384400007800f2011b41d1b00181403014210384910781500c3c0c3c0d4002500c26003c0a0b12 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 678218803 1250 678217553 678217571
    0x18060d060305010506090c0a0c030509040633081302062712120a0e0607050106060201020918040f03050309030408030a090513092d020a080c040e0d0918 67
    0x1440009102091511000003140390951410750709444c00130b04494440c90160003800b2403a40703100102e031000d0700c1c1814150b15040d507615003900d09010300c8410a900525100c4001234040258484000e05804400b03048a03041c21b0b0581c010510090706e40a5001400d140c0009444020701c00b58600310500043c140c905200c0d101d812100d10f03020105101c0900f680c0103e401c1e0190522201c040380e0011000080e0111490b54450040a4003880d1b8900c070812940fa002c120031906c902040b00c80d042c0e0008000e00c00e00f40c480311301030b010798400c0c2e8109005010480c141e01034184403546c09030250350300998181c10054146c408840d9600040d1130742119000030000000c400100b0070061820040e69110513152500d032904028044c0100140c45038424104612000018901c02c04210714030b1424040c0c40302c4200b201000e41141c0c51f1098000c3d00f00b40541404a4101d0740040e80c101000d8007210240402e00001040c140c5138826251903402040c980340d418000d44031900f448c10406004114000b824500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 678220053 1250 678218803 678218809
    0xb1c12020102040512070801060b0c030f090a2612090a090e0319090303081b03191e020306210703120314070c0209070206132a061d041802040218 64
    0x285c40d40350b800309944440c0040100301002e0146000030000140b030b007801d041c0d240d0740c0701b510b13440740700c05480951100181d80701e850b0752404001b0010340311900c202c03507000510300300f00082900d402d0b4400b1100e20600d13a104411076036003000c5417100c51000e016402c81078940960240603000941d2041c50b180010b0214002021040040140c0c04a2580e00c414071946141009880900c2c00362008000340341e003840609a032a14142240c0e0000c00391001111007603c0c00b0f02d042c005110480055025480c607124804100201d0b401960140f041182e01c030b10721134400040300b03484804550f08000681c0054600b00040341086800110900141c10f0110301d120410303003403815120040350441c0224812a03102e0003907007402c0c1100c59002d1018002445c1030308100039060500d40035030000400c0e6507540312418203c0c006120a83c9040d264580d400c0c01c41329240c1d0350107007408200225882c0c04a102842940062030700c0c0c011030034203105001800405001540912001e035120721000c00d9042031010304050151 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 678221303 1250 678220053 678220069
    0x1050715091704060318020f1002160b092d060706060f06050406020d0807140a051b07081b10030b06070c080607030e07080309041d030d09060b1c120201020405 70
    0x4001c000d0b84550b5681000300240841c4c00c2c0c64203c10110380325800410042e10b0300c54170385c0701500341100c180c001608081000c07458010300840261400d89108000124600608017400750941d00316500c0c800480c1c4040400107184115050800d030305203d005500c00d43c10280010440c440c000d0f84042045134a400a4620340c500c0c0f94440d800084c0009020020039a06103c900e40c101854540381400d4240307020000e26113210401c0d81030085000150302c0c0da10601070f0044508c000480b90120b846032088500094903400781f072048012600514800504c3c900092a14290500006005031b0900f43e40c0c440440c02070a101a0094000000b040400042484550840001c021243c024182803070100c2c80101901c002e9001000658032000007481802004400d0394080f41c410b490000f114040441034210400130074000050b103000008244480605c550006c04105018550600190003103406010900c1d90020310745c090308071241e12213400241d00c0465550070303401600c0007504040e02c40c0f001032801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 678222553 1250 678221303 678221333
    0x90c17071b0602040803090108010905150402090d1407030203190b07030914010f0504140703030e0603040218010b030916051e031c030e1603050d0c03140f03100e060105071509 77
    0x9941b004c111641c10f5030b40011510301400d120b11060040d8241020301c11001d501000c0280c0c89a034012500c1c2c170031511540c841c0e00d09217070030880300d00c0403148101441d904e4004074001170740a8041e528021244912100c142522103900c0074041d202559604c4c000c41c000c00c94200e04559880d4200702103051404240180065101c0d603100005641c01d152504061002c040c1c404400a80c206440c01c002280e00205031450094041d00c2c0d041d03803a907c620001d4008030b10030720401006050304002003000e04864014600c0380c40e0b00e2040712004c070408e00c0441d0401800d07100d200c1c0c0c0250840310400710200740480d040303c80c01000e01102c0e0140403008007001b2500f18105035800080e52a80c1c8022002c1d401c01481c0310030000a44140a01c42c2142c4070035841d4010350241d48207000160300c0090405106100c0c3c0b981c00d861122059860380401c54091003035504c1a210609404100381002c180181601c3d44c0502400050315030916082681d645d041d8586400010000002e54403100a8007003466000e03083c0741303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 678223803 1250 678222553 678222569
    0x250204240320151801090503032b1506110303010509130f080c0c130212130c081f1a0307060c2a1d010f030809030f0115090c17071b060204 61
    0x5030401c0c0400000d5200c9114501350401c15407070b00c01c12580e20003204841180c0f01d039421121280ca81c4800703d00306910f0341c0c001d90105e20b01d4003c00c04c0d4a040f4443c05d103800d075410750307890390010b202c29005282d0300d000c00e00685500207440c00110b030641044c041900011072050b090080004440d40302d072045a00600381d000040c0d000394403400501e140c1b6000c0328040c5118010214102843c4840d09021480700a1402c185a01d44040c000b00b4461030311010750040540e0400c6030101c205044004012040c500590382010b030805840410403003103070155180100001e0001c1c000709141c518100d61524039500c0c1924407a4078089030740062028446c680e9209606140300300384030b92410052441000b040015282404104001449100203103c0f881c0112034002428a4031110903000103403d006032440c05400703945ca07050011031000314032003c990844504c50010400b9015144041d103045a26078125001004500e002454080c0540701c01710028200c80e0b00c0349446002d0b41e44141c12a8000d070000d9a03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 678225053 1250 678223803 678223807
    0x60f0608010b0307050414161403090304170a03272309010807080c210624040b0609100c08040b0301150914120325020424032015 57
    0x104070f007001c1102038010042941d0400c581d4800c01c1001c0c41000c4d0241a0302c107105001400e840b55035100300c02c42c0500021001a00d42d690620990040c1d1340da115216075034900078a98100c2002110102d403401603240c05450300f130408020440100382c81c001201c00ca08500c2012100801d8041d521000191103040b05200550400e400728200500804140c0c0810207690200c01d090148000100d804200ca41050380c0a100912190394610524400302c0b01d004000d01c05e803002c1050200221901e05032002c6440c0341b50f18400030300c070140b1042c2d6000441851f00b040d42001004094280f1940b511040340680c600700c090a4210f95800d00076034040d0344082d181c084040f0040c00000380006800078643c00383e0405604032450450048144d2007802c03111440380078400e1000e00b010105001300c070500c806421026429844c203009000c40030034659816070003145858650488005040d0020796904001c0c00c0042a2030b02c2c40d0b407222140f03010b0008254008080300f401e21440d0315025100a0110080c2a984d9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 678226303 1250 678225053 678225071
    0x20c010f1107031d0105071a100e010f06050913020a0804050706081308071a07090602011803080f19020a120c02070308030a15120803070f0e0307060804060f060801 72
    0x20140d8001a4541c18602010080c1c980025003000b0310002d0080007150801c4a680d41c840161582d015440015001e4891505013114155581c0c02c814480c50184c070f00c682841d51a0643c0c64020103090040d001c3c2680700810a1101031300407005400512030050414060385070700c1e14014140d80190500d0000710781c0f65010301c000c2150610002024043c1032900d0074051a100d0008030910351001400352040300000b800506001502c0c020902c86651000c00881509103028005c04000c494402c101c0154644034081c5140b04002c5002000c141c2c141d030710b20446856407035081c071624602400484150b288030f694020188160300103000c55501c0f40c0c642c0500e02c0720440c903120989180600440454000440500c0011a13040c28ac0e85c00403000a00010764120f0708020a4450720b082c1c00030b0300c0210304030f407080081100160085200b5145940c0e20100c075205e070749040e2100d5480038050760303140e08540d00a10020b41308580c07650b8002d00030312000c5903601801030050704a500302c5d0403000d581d0351180804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 678227553 1250 678226303 678226331
    0x51603050c09010b0c0a110102010b030d2007051f05070f0303150905130b0603120c070602012a050702060912010603030207050d080306040c051c0606120b06071b09020c01 75
    0x503401041640046440c0070344090344191582c40039000181f51001d2213500e0402640b00354000781d00d0701405811210b4145800030060801040c8005900d03004418409600c05420f0225180049074006080f450044503031032400c100d401c00c00c460440c00c0203001c1c84480d002c0341c580350f54035008600030749002500101e0504800c0c00040980c1220302d0250400c0705000074600010f04d00ca092030740106002d1f1040d1501340010741424040b00000c2180c0c2c030089549001c041d00071a1400442d12150001c0105040030000c0d0240000c100c1c00929003810348017a20706d500c074041c00052200c0f501c005c0035180b900c480c0300c0024443d0009088003032500ea43d118424800c05804000820190404a070000850300c01ca0351550220b00c002015280502d841d01191000c10740508260303a001d20300300705403d00725000d524805c8001c0c0b0892144c0c03000240c00040300342c0140507911038203c07290f1000d40003500e05401d5858510b20032050603420300c0904614217000070700c0701051000e0100c1c004d02900110300000c0f13502c44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 678228803 1250 678227553 678227569
    0x60a050114031b1b0c01080f070e0406120506150a0305030706020a09050d14120301050f0f0a0503120307090509041a0709081f14010b271008010e2809051603050c 71
    0x1e006d050241c460305002d00040d0311041d2541c820942c3c81c04d41c82c4d420159000ca000b500250740414408401001308108100f07012a045100b08850580310491486040070496159840e101c080e1540c0c00800800c00800c196030000c0c0300c010f0147c10201003995460001c942803900caa4001e40312503210b11818083c103001800040705080d405452281954107020000303071541800c250355482107807003166151058075407240c1c80c0000c201c02010748801803400d40410700300f6413045540b00c0000c1d80e85400812036140040c8014026500000715500401440b10811620341e405407005051003864100010f0b01182001041d040741140c4c0915450302000f43c0a407800d4902c00001407480600d0800103201c0e65031520309850080d007801103401c0c1c650744e00100c43c2c88456a82d1180d0307500f120400c50030030341705604880802d04039041c0c49000b80060780ca10380100980300c0d0101c0590840320b800440c04040010541008100c40d004606645e03c40d0003142c840b141c8540300d43d0084545420203482c000961030210a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 678230053 1250 678228803 678228823
    0x106120c0201050121031e05040f0f030f0b0405160306061703091008130f050312091506040c020c0306090708061f0302040f060306020c15060a050114031b1b 69
    0x80c000e130b5040c0072015088044070b090b407001c44030720f802c101c0302414411240041d1041e1141e01e4500e03644201c0030f0060807a4030a01445010700580000000c4d0361110791811409c0f07a40100103c0c440740c001c1d03a030300380c51010090130a880a10413050703116040d50f84000b011006520039240014101d1034401049510070300d035280e02c40150414811070002d034980c5280480a81050300d0408400d07a102c0c17a52800032106180064161500ca00c154410840004010020092020110300d019590102816910f414140c0c040c08150711000208040d42000d402c91030b140d01c00703030040d40d00317000d1040d010918081088488101c82c1d0700605082091080034051190003461491591848401c96070b00201c40710030911000703000316a6443c2c184140d00d045c0c0d10082c007556000c6020340d42c0391003c1d66010303610b900103250b01070000b58240c0030072140e14014080303800b101d40607164001801c070301d14051460b0b904014241d801c2c00c000d510410081c1b0b20560001c080b4071900c02d058003401c2c82013441051034003e03404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 678231303 1250 678230053 678230057
    0x4060f1b020105090a020102060a0905070b0d02091c03120905071503020301030b090606031c050412110a050402031909170c0f060109020f2709100603050a09030504050108090309090106120c 83
    0x8400305c1c025036804658264020031400700070442c040c207440d10924003043c0380d1104002d03140c0401c6241c0750808580080c07841e460100c4200382031094005002d03010b81c051410050114501c91811404c4510942090600501504c140d40701603568041800300d00a860001100195000005108002126552542109481d00101184e00c0d106022a03035400080d18043c08401502601052140c81901285c0c06007255201e5812021005c1c43c007070318206a20751400d8890b0441d014003040340c1c00c00b032080e0b91084a42c6d1801c5c0c44072803e0070b0003000c0186400c40c0266544441c2c801001100d410580003054000100300080c203400b10b0301c10303405042840680060644c180100314110848211000341c6005181a4010300310480781f0005003129039610840035900184420b0070441a01d84a955020489a40b91018800c560351030070f0030000ca815580c40200400c4007484140318651080304d43c2540084a05c089a1518803c00c00140a1a00907132040c00000d20090600c43d1209084c05014a182141c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 678232553 1250 678231303 678231313
    0x913020312161e050a03091d060303040b07020621090d0512070338210604081b030d090201120e061b1e07060e0307051504060f1b02010509 61
    0x1d41c101100e0002d40c0d240a0403d408400c3d1240019281c080c0c10102d680e445021120690010b2801418804040c03107021174402c0b01142058980080c4100e00d8414000140690310b01800c0007134a100c1504070788401d81c0c014106000e01f1703091115041000d41040c1c02000c0e00201c600e041c40050745044500c468590400c0300600c41e0000480b118504107800282604011540d010441031090310783e4502040c90020401c040301807680700c4501c85c1d080c0805041551030031010130040030b00c4210091020705010455014100080c08105901e0107400700402c80700c030742456100c0fa030350070500c2d5030000345143c000c03142e40386182c030219070f00240b901c800700750000c50a1003c07998020559032580c01c01401c1419103050078605042c1e4036000c6044803a0540090400100403005c0ba07c604460703002768100721040f07486c000817004110800426502041c2d8840010b007508040c00c05c40040b04079018000705d602035119501c10b45054810700032400420030034080d43e105440150360003420348001525040494201c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 678233803 1250 678232553 678232567
    0x10b10020a150f0b0d14070b090a090e0f100b1e090a0905010209121608010519020c0a06060b03040b011703090607080d231b030114030109020913020312 67
    0x810b0940d51290506440c0000e102c0c0701800300440600301104840d6404219601032800700550a51104200402d41007102c00741905c0c0e00b8441c00c60301c6150804d41d030101010b46d0400242c1c0032a00042651412700003641c025020340c004a505d40110700b01042c00660712401c0e050014284445080e02805508041c13044004200c400b04448010191050ba0711310703210400c840c1070010940440301e2071040503240d0f0030010390b510b10107612422120700b84a15001c0d40a00080c00c40c00c140646070003281c4030305840341c40000840c1c1d00740080d4040341186086005001082c2c0c00300e4181c0c41030350002c06081446d25a2440c10380303040071a4520582000c0e070f0092800c8035024901c90b0003c280c461070705007550312030b82e035100600341000d1038064224444211803e0034401e5503100c80742c000e0380100e289001d0000005488003243d811202e4042c44405039440c0703040c0010001c00072003008413811000007900020b40a2419004140e450300c08540c40340f03180c55a201c640d01181000c21070314400c070f6040a055828210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 678235053 1250 678233803 678233813
    0x10e04050a0603170301061d062502060c03071703091c0908030d060608181009020604090c05041706040302060403300203070f1701050603100f0312090905060a030b1e09010b10020a 79
    0xac45014441a10801d0101301310109104048025190000c1040d41c4401e80f8080040e0f0b2540420700803204031903184200055440700c1000e41f801254114058880b68001044810003100d04d110f5080820043e40c000150b6080c0c1840140100150800c02140d8981003034806094090082d010900408000404081808010400800070349000700e01042c000c1e00c074000038209000c4c94010744a840c0c86c00c1c04045036140c00c00700070000c0312000c90350340341c030304084e0801d00703071a00b000f1070f006405070700920000750001c0d105511641900ba8041501c9000404081c485081c3c1d0300411407140440d0343c0082440304240d08001401110314507894884511001140520820b25040c03040c0b500841022010032003e28007003203203601801c04400001505540c900b82450070581510318400403030a9001c010842d40301d14082d451103418041c1044180a186581d400740e1003030000d051040c021184c660547c1c00000881c00180aa88842c00200712b00c0400d0042040c0c160300d403c0e44100b554030030b0340d4403400a2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 678236303 1250 678235053 678235057
    0x30307020d0509030c04060807091d070603111b1b1207140a0e09060a0506040507050306091f030c050901150801120501061208120c09010e04050a0603170301061d06 72
    0x1480c68a096034441c0300f4440030034034110084c550940c1c8541401c4003c2813001c000a9880202e421140052124250b00010f2259850f20701190000076080300304248030460007900440b00e410705013b2203e140800c43c005070044501c81c5230711031f60b06400c089051000859240720071015480221074000c0d0f00d10801070302507525641c034410f221901d001a0000501d5955801649000b0b100e81820b442007881d081030b50a440303110031184c08036a0751800010900c02d003041e02c40d00340300300815114030740355854070020409521802001001417050031554601490030340c0308100c00a45c031440800f040b442c205801c004030414141c100b481c5042e94919082d0499500c100054111080c08a5602c41c01001e07041041c0034003159004090703c0011880300307900300301541c030080003010340f1002c1000d9941c0341d55044800c240310368403105000a1200b0106015840e041c1d100ca600020b030010001400c55503640c40b480c510080e440044070502c8040300401c901e5800c64607071014892582415181c0510400004000d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 678237410 1107 678236303 678236323
    0x40b0a110a090303050d0e121b010e0c10180f08010e060601020d14070b04081209011103040b07030e010e030408010f3606050703050f0903030702 64
    0x9458401c0d61104000759407044007052070f5440031600b60b00400c1c1c204c0603c40c0eaa0030b8049210b0001c019111001c084204aa40c85140380c00c02004055001c440c61030303040e41000c0580c0b2a04002117511501981c0444454806c030550007001c90320b10f4012642075060318003202d004208410b0740c065850455400c00001c0c03119440c40341d020f544031101a1582805680f12801800314103005001d20101020052403c03800e00e49152111050150b00381c2d0159080400010202581d00d045130070581e00a035210000c0c4441e20360341410b8000b901c07009002524900d0002d003c039105521940028402c81a0f00c0b00a1001c164241c0c60151264801d00c03c0900030f6180034001d0382c8036101c0340101c0303145040c6010b26020107480d10308011080e07581d00c1c009500000549da400c0002440c2740c410303280900465500010305c0d181141c0e80701303840d000c003900e8000a580184200050150700150300041 = true := by decide +kernel

theorem cover : BRFrame.Cov 678057553 678237410 := by
  have h0 := BRFrame.cov_init 678057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 678057553 ≤ n) (h2 : n < 678237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
