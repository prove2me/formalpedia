-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3687
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:11.86576+00:00
-- url     : https://prove2.me/submissions/ce575871-fe74-41f7-b0b1-887cda49f450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 662949640 ≤ n < 663129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 662950890 1250 662949640 662949659
    0x9090b01050a0b0d050c070f0b01030b06010201020f030115110d03060915141e18090f5502040b0402162d030206090d020102251b0f 58
    0x5030001c0d4442c0c403500b10180002070031001614200a00120001703500d880f01c400c041124001d0020040108101050003c10010b45a4019049030f1140c0d01802c81a25100f005a00340d0007103071460780c0381e07800c00d000400c0864821000b0014418880c20001154444c080303d490030501c03030601100100381c4a00c0c0400501906100d504807080c41d0b508d020586c3ca0402185516118007282024460907550004104900c044001d4a90a580082c04113003454000c00341d800321800c00b151042d865005214040d484058081408040389001d19143e103403a0900445400c903880b901904055141400080c4101c1d040b440e850103c88034400241207441c1d80d6051041109803414110442d00683c01131188200c01c1d2145003000d42055400103c0030b103c0f01d05249210035988111003c01d0440c00521031b902e040c1500400d000c6e01414032013064480204001c0e0041c6e080c1c1c800d01d109140c0e01c9880c40c1203030100c85042c10128407154403070401158400406542036840c81d94540000c0b136040307015001081101030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 662952140 1250 662950890 662950913
    0x70f020706091413110a1d060a080105010813080f031f15110f03030a050403080a090203030d0c02010e060a020c010f0603080d0b01021009050a0201080708040b011a0f040909 76
    0x3031494900080b0341088020401c0035900d407a01e074040c0b0b80310b000c241d0041c0041e800c03c40380c020145850a854140b40d2200070008500061405900e041807014403030b40d400c16000721680143c840e200c40c5166440d01d401155012001041124602602100180019104030040000310b510302000c640700d0401080000b0202007403075080c052001d00c401b00300099184000c01001e007003143d0402a03400c8002081d45030070314109030310141c05404000104629001c1c10760045002d14004c4d640c000c2566070784030020381140c44031007001c1d605620a011081c05480960441c10307580c11641b0011400354002ea00c803e00d401d034180c2d03602d1001078011132050185102403040d00d16903180300805000b02460743d280c05142c2c0c030900844a1070f0940b80c1c000115280d000b00a000ca0700702510b201084941002d040c02a102d10800400700e00144c0144085540c00e889540c40c40c0c0500d8119042d00c000781d00c1c3c07040300c0b960301456607030402c51702000f8060858000007840141c40100b0924a01044a54440c5000303800b540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 662953390 1250 662952140 662952149
    0x7030c0f0627050d110309090c04090e0d050f070204141503280221060f090d080103031706150f12060a0602070b07020d0f0614011a090904020d060203070f0207 70
    0x4040d00848049040019004e01c048101d042c4220104900400f01e4103511031254011340101d4840140708900031184000c2044540e484ca0030030a800049504a4031481160800e00014006000d60720701d49843c08001c14400d0b200400001e03001e2407804e80401d00142c225000c40ca40382e80d100f214071043c1002c2c0709070340c030708900d400004209021100c8188100000c1580103070140841c3e5000c541d1031032981d11a20031140360001140c1851030803400c8495540c01c201e8400300140244148111070900a0212034182c0b5416100d454600081070341c1c00e01d60a10052207184d004050491080c50f2068520040080c40c109c084c03011b40e2042024020700b600c2c4005041f150154040e0402004505d80c041803050039101701039140765032004c0c5c1d4000034102030110980580b100304115440d03010008144c0c0400141000450185000c2c0e907102a480040c08041d0892025110108000140351074282d00d203541c400c0c4000d081e04e9000d411a00e0300c4040381c02c2103da000104c0d00c0842051402c58041100074004c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 662954640 1250 662953390 662953451
    0x7030b090c09100c0503130b2d030705090307050a080c0a14010804080d0b060d020702010e0f060d020702120a0b041e021e040b12240402100507030c0f06 67
    0x4900c0e0740200314072120f4000400200700308104a5801c211051085401c8903600d4400903480031340707031a01300195070301480b1120782c481e052400014480354042049066040003036141c40c2540c1c2d176240c09550580c001c0c62020344c94002c4e508081034030f82e90028000007404911004004a10540c010b028080c0410f4000078a103000e4a2084440d9a03803107000c095004d42e002c0c01082d140c0303542d4440300025041400905500080c08101c051b4945115409401094003d80c0c6036103150100c8020f000105c0d02c0400b20b69000281044099480c0c16140c004007421071020b06120410070201d2889400c1c0350301c03403004a50a00100c4144024001d424048071100c035100c0b4400c0d200ca803510317400580405120031b2030f0402c1c04500720302c000050395203070303c801d00030350024154142002104040c0f82d01da6014024650f403040e802e04804003c00c46c032a407600e1041d54042c00022100200d00000d03202074118050031020031140720f15910000d98641540240c0c1886100c012401d050031003102e41c482d002654051090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 662955890 1250 662954640 662954647
    0x6141302180d050a0b0c070b070e0a051c02060409021902030301080d1d091806010f03082218020d0c0f08150303041508010f0603060302010221070b07030b090c 70
    0x940d1801d0300015001e04129000003003080e0074a071a5060104880d4080d10300c3d010081005a07808418000780101482010b0541c0942c0e940f02c81501c0094034541ea840c0c01c07034030618040c80141880004464400001c17000c0d00040040790b4002203c0340d015410421081c0c4e0042020035404c91603e0b503521300070500707002441c00c40d8100a1250f0380d80b81c802001008000b05541e40483d000c4650108103000030020f403d0750071510f04201a03a250304207801c221229480794000005282180a43c481d00b0740c0e900000b103134580049480700707141107000800803040d08448d403540045d00400d440d4a1280c00184040c2c050303102d500070484002185ca254404209100f4281a0b5062450344991000e9016100400781d160951800d008a480c50240e5085a01010a100302040704180c000d0382603412a141080c0d00740c112504c0b40c81c100c095a50711b00c8005e000d40d03c00981d441d40c1e20003c9008046001c1710520032418251640c444615441e015100c06d000300f41d862102800b141400c00701a5030105080321002d26 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 662957140 1250 662955890 662955907
    0x130c0e0f1f0c0c090609020c0c03120409020715090c0e1506030a0509152e060f0f05130303080702100b1c02010e03060403090e0714030106031107050106141302 70
    0x2103401c480e09104104207084040030b081001c00d0140001510101004012441d1602c910308020350046090540900c00d024412417240307000580b280003440b01006050811340341000740400307904582000c85101481b403041000c0303850a0300c03810322003900950213900000e15200c2e410070026800f0f040d04a08240100d052151070f01d5240440317400400304440060701ea03485046030f80c20030140750016000c146580040c0700d0f040303c20744000c50925030800c007811455540c07030b527864505007231911524001c9100c00f543c13840340c24010070f01c1c3c0707100c00c400c0d0070600c2c904501c0c010314402001d403542040b40812403c0052000d42a410444130514051105007001000d0311200000c84c160b80c02c40b040c40c0d01a030684404001c69118070b0000c1d0f60300d00c1c0031f007ca07822800c00380b074042c1ca1007801c0c1c080c840600300d120000400309845450898902541c00011510310303402e001d03088015107141010310b69503040c10040c0800055003446120700400340c4400d43d0980795240380403c1080b1104100c15090107005005d14003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 662958390 1250 662957140 662957179
    0x3062414100e0d02030d080603010605030102040509040f1e0f0c0506160b090a080304140f03070c0e070c0f0b06030708030403030e211f0507050720130c0e0f 69
    0x441e1400d0a08042e14101c1d407840c0001c08520350100000c1d00341c02200e81c0c42d40900c0d0007202881c0203280031402440455260401d0500300e0085124840d84441308001080114049404007160540104070b00c20a50030f6002a50860b04201182100d18416142082c000c1c030404400380000760004549032448c200c407104460b00184503088011f8100903218001c18a509000c2000300342c6c880d800350314162203250034182414200505d10626a90b4000d08012404964020040301d0301154000010440c1d02c2c105030078484c1202c0000c00c03850a2140300c140c41808200407003000d9689a101d408541400e140c041c1c1403500f4415540d110300001d40c000e2106100003900502d035180c07050000d540c03202c110803800102504040e81800c8840c1c040c05030502d0011014031140208405241c0c41c0c2040c01207071194082203410707110784500900740480f81c1146132140d4401c0c1009105542000700032040d40d2510039616012a5220352071000801e40c60f40021280e0b041000740c511001c0b40407540800c141c0340c0f5903940f2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 662959640 1250 662958390 662958409
    0x30c2d120e0a030602130b1204080304170c0105042102031c0b040903020703170f040b0307020f0717060a020315101b06050708100302060a050a030603062414 69
    0x1010000121800d40d0140d00c54031181c0740d21600109542c030242e03502e06103103000794041c4034682000301d8980b50204e490390310541164521626152119081d503183d8441c080d641c0c0018104981461004812042c20028400030f0035428120303d00004050a040c54181c0840c0d00000618000c4401d40038401c0701207030044107540210300320381c682010401c1d801802c030008081c2c040c5a560310034901000d01050503800038030201646c0c0301e001040e542003507500e40b5282c1402040740e2003803000010002405201c10040c0070f1500580580100d948014003a12580d04020385a005810011042142315400d510100046078115002840852035428080311500000c029095094021005115490000c0d41304071000341603d10070b4000c4d650003225600c0c2c55809840700340c0b203000000300c000c40880c4810421140c1c03d400c1720303401403420b072034019808403e5615800c50000302e014140e80d4100007011404c18050b03600c02c0c2c040c0c102201c60700100708a08001c4040f054100031031410701c100b0784095680703600f03c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 662960890 1250 662959640 662959643
    0x10e01140d0e060403050406021209100c02040b1203030601091e2c190e030a080402190f08151e010302010e130c11100c0503060d02041404030c2d 64
    0x12203a492240703404080207003650460320400d5208640800c0203040c1c0c0803003d80180c58550782542e10f620440c2c0000030050141039600d0741c2c0501c44901d150403050084c0300644841d44050310100d081c105000000d07141d065601c02000311138100102700300081d0781c042c4c620b0000d03145070040d41c030b0403040698503055400428001d805c01850440d544528010100710015140e100082905000e480c200724025100300e8040044800581800359034103881d035020090383c0c01c048071980d07101d10075511034007084010715843c0340700b4007103185c44800401d8000442c0c4801c0d014020880092115158110704041940b90041c1001c0c1c5000103008403910140c600c100039411a0b40901c3c0c512a009070340350004400a2110038141d0403070349050100800f00790098a0503019050540c10ba0f1030440750742601c1c80540303401329039010004808000003590f900c1d0003141d0403485070024100250a0106d0024804200700a9a050340851662107084003008100c013101c18410040c055540e41070004400941b40c03055403000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 662962140 1250 662960890 662960927
    0x13090b0a12020409142b0503010602060712020c0109050a0c050103050408041202010203190f0215160c1a130c120c06030b03162601061212050d0507030b040b010e01 72
    0x5a00c0c18007005e40b426404079911780080c0c030701c80c441c0c601e60041d06929501c007480012400c2c0484072041400342050341d040381c109402070300071741c1d0316280101c0b00140783da85c042e0034032a801e00c4626484407092040007411407240006041e1401107050500c000101503018134105800c040400000034070750340c2602e00b1902c10034008550342d041071005038214041c2040ca02c00c11308042000010040e881444040e000c2e50715006d07140410801100200c2d030750021504101c5002c01845620041841848110403140c00382c202c64141d110000700142e07038030405480c0c0318400551f074000300d814059100802801416a4000010320300c00e140e5600042540c0781c40382c0e4003416552401d00d41c0390345043c0580c0c000038440b0448110090f8070358003151208105c0b00c0034001c2c0c0c120680101c504042051207814140d9000c1c022010101003103550b41903c11584c1c41a0340e0070031409206009000d28540503203402034146480105443c2c50030800d000844c0c6210501a04111a100501c003040e40c1004c2031101100d10145c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 662963390 1250 662962140 662962151
    0x1b0c08010911150a05070302070b0d06150c111014030c0913090b0f0402180901021c0e1b0a08070f031106070221070b0318011b020c0904140313090b0a120204 69
    0xc00341c9c2090781c290306c03801124100107801005030100781d201c1e80030780d400900d000804032003420084805c218074040081000e40008500300c2580340c03924054140a0702840d0490320222104200c8442e40c2040d0b50400c05102c0200d01507516240102240c06075000700c8500300804281e41c0c840040107030000e0500039002d0003080c0858150345401000420303680000104460609203018014000e40c840d00da101e400032548801c4180c0c1c1c1780c1601486001502c00c2d8003e0290700c01c1c044100c90120380084081e58000f510000c0061440790030b129800041020300340c403804030383c91f5041c020301141407001510702c00c0c80308109000050383d450f13649500c0911340b80c4070b00003962824060285081c819400040840001208122a00c2e0b414082071807180801c100038003022a040201b0104070100300300d03040240c2c2026905807010300300201403982c030030b019130403550b114104c010400f825548201140c800c0b401809106002c1801c00f070190350200c40081d1040b4038180e182c0b402000b5600d0007450000d20444d1a030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 662964640 1250 662963390 662963393
    0x40f030f030b0d0b0109050606070203100509010912113d06080f01061a07050a0807020f100507030f02030f1c020702180a0605030a030804031b0c08010911150a0507 72
    0x1e40c03220b04031090290020010b54244d00709a44032601c244100c04000d41020006074040c1000801d498403d94003a0003841d0039a52100c0541c06080c008100c480550b43e00d5800340041414001e014007451003a840b0400d4001024411034101034003140c444285075121201031090320120426000000300d01150f2200044010200c1d50182190b07501080080c0f00700b41403d9100141076100e2800c031a8280a0104540d0421070302002c5130065040180194201701e80c200003050302c0034000c00460b072000b048244802c46020004800715800c41c20500080c0300881da81c410940c116103603a03091402030000b1414001d540102600034822100303820f490142000540c95400d00e21b0301034404890380100a82c0f2002d4240e6540032080c7c1044400a001d20305110002510703013808142c88644a403da0380b410219502c584068440c11911990507038555040d01c107042c080b4145060030406030400d000042074201540c2011446107850328005032081c0c00481c060005032072141d044a0344a9500d080194442016 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 662965890 1250 662964640 662964647
    0x306110a0507030323150a050f010507021905030312010905090742032c0303071b02030d0e0a050f0a03290702100e0d0c0b100b070803180303040f030f 66
    0x5107010948160404050004507003c1c1e02400d200d29800303a0347d49a2580e50f403410001010488100c0d2404035208200b0342001d4106081e182d41c030280a0f80740d01142e282c6e1080400c0c5590301030000f02c81c01011000040c40b120049015598004455400031300d0140d04146241c1c0c2060078507500742400d20011601c41514038110705a2140107016040c1d54540007007101c02c05009400c1e030f283d0001c01c80c0d1240c102e0061801070fa00518590410100040d030565a603e901a210150346010118000000518640c0142c1d400c0110300c1e02003006540f0140c4c408000801c0c400400000d82102d0f2150915154040d840d4031001c030920100d940240c0e24152404050001c66085d030b0f0908401d800f50f22050040088140d00001c1159401d0220b000c10090900442e078010380782e81c03603040003500082d0700880c40340114070401071107608074050105c404c401a5407560400029888050b040f00c000e0404800c009a8103508807107207504c005481c015514610301513407130800070704603140c00400b403080044564000902c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 662967140 1250 662965890 662965931
    0x50409020f04020915071b060f02060606160f030309022d1003020403020a06020616090506031f090f1d07032411030a0e070602120a1d04090803010306110a05070303 72
    0x6030503103403946e01c1980d4140300038450f551860f0300d0320754503001000084203486181e218042c20701035406020507071141000c000c00359100c1000205280019040e0b0404502d0460b21a00c80c02c0c82601c0010301d07035000e44144943c080424100300b88074010101c0001d482c3d101c946136050301e07240071a1030482c1410540c500340c0090142d0703000a50003144000340420515000210a801011801207841c0d00741142c60003103030081154000e040d08500305002044001104813200b040190b1020201e100040e1034100030000c4410300f00364201541d440702c44841c3c58107051828110340300500c8014050080c21925261041c8170f0b10381c1e100c40340f0021803034542c2095405520031281500c14040d0039549046c0007090754040c00403501000c2c02070007030b480f00207005800007a0046c00c1c3d0203400080e0b41001400c07502502c14040235070902c2003183c04581c0d034280f02d9031075101d180703040fa22620354262254111b060000c200d80c2e078440b00282c42c07002000028400fa0700242a80c02c03450345858040b441200c04002840c000c2d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 662968390 1250 662967140 662967169
    0x90405101a1e16030809150c0703170f06060c0c040f09030e030a02010813150e030a080c03040c0b1b0d1e14070b0916120c050409020f040209 62
    0x7003040a4071101418000202210310146461140d210080c508840242c42041c1800103001c1029050000013401051031541c00403020b010381d10320401d010716980c1c50f040121190150385400040d2038080540120b240a0300c0d00504c0801c4415203003085000300e003860050f02c5a4400c1030049190803003814104502200d84401074814000102d210074048043c1000399011804644100440c1d88107040000318082050f40596427006d0540300c6191100310110100400c0e6000d00d080d181e0181404114040c210710703a0108070045503500a0304400508105024081d20010f6800708248800304280850210554040c02c410a5480103003c5010143c0c83c45221b0000140c051441503000c0c40c3d401401c40d030100030380c440302010b1003406031004450700c082142c1d404441c42018802040820309400c80e1540c003800302802c88040380040c00c1500e002034410752101e04210050b0b410807040205000c0002c00606042e01e040c03116244690004000c20522590607010b10b80c0880c0c4107459655450900b801c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 662969640 1250 662968390 662968409
    0xa0902032a360607030f0e010201090b040803041a09060a020a0c060c1107050307061b020a080a120e061801030f2007060c0219060e0a21020d021209040510 68
    0xd8400c1110340d180e6082c40110749515078045402503a060503c5804ca81c03445034180c3d2070075840010540d054a4541d069407480313045641e1619440c0004c4da124080da40158060a419512031405140c005241281ca2080e003103843e840006001f0381400010301190424103502c405611030406950445140340000b401801090400d110340281d590060320051403a0070240035100002d4039842859529980c0340b240b40e001034141008204e05001d80a50140c42e544001c00c00c40e5240d90783e611051400c0c405000568159142a100841c81c541100d000c412264050b2109400c1102548002d400000702c1081c0c03505041c0c4070598407084022070381c061401310b604115403041050f280f0940b0940c640000300101c0c2e0030f40c6410f0b414907100380001607445d200783c1d40110190f4002981d68415002c2c1c40c9200101d0b806214803030704080000c1c22040450500440b00c5a60102d01810400080c5080403100380c4c00155004040040c050170a180c0844851442c207035008203c039142c05034240c14900403680042505d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 662970890 1250 662969640 662969677
    0x14040e152d0604061502120c010e0a140d02010b06040302091528050d0b1303090e07080702160506030121080a050319050108030702090711060f060a0902032a 69
    0x366119100d0755401450203407403c000d89925031741480f04410405001101580c41280010049040701c001000144002400030a81441c41c418a61500b003841ba011038a40040054508800d00c08104d9402d50130007034030003400400c00d144082005d6105600002c0d000b800075070000707110320041868009000c10b000d018100340482d15010121480701c10039104818a2f5080c80005552400c0c1c0e4803090303425004230b12101c0c1c58481040e000750f0800c2011045040c040903850008159001400403449584261140300b003d103402c5200074280740c1d80400200c045c4680c11000e0240340c90b543c0c1900d0645807490301700901d000051400c031000d003510640041c034808000401440240c0c0c0f000241d4004c8000203c50200c00300312035040401e8400900648802d40c0c0240285400344c501401d405800c08903a0a0100070250107100b4181000d070102c076103100582c014014002c5908201801d040141038400f802c500310308150511141d030f4002082c220a81d0341c50081640022154030089030704152903544c1c070021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 662972140 1250 662970890 662970961
    0x150315030533010603091a011e0b0a020c0f04110c1b01020304060e040c05071a09060916091d343606080714040e15 51
    0x261501c0200e00b81c03200228040708034002c0c0781941c0d10740b12400040c1120340060b07800c0c180e0407001484035010550b00c2c4408610f03101c103a4034140310400d0190244001016920500001032403850000d80c1c0103041100c03040100545899006c0785260440400321004150880480000f50142460074041005200000340700c4100da13100281e40c600690b4403548100c9000d0214005a0f264015445810301203101c103190480b107403610703501006a510090500b02c5c14134102d03498481b00c620700c500b0b0100310802020280f01e032a000402c0031a6101000000a24404061008076146c2c8111889011403032512191041c0c50084144110440030082108542001d101e10504454000f11510046040300045140c450300850728103074802512840303507400c03400116260012004010350480580300140101180200403558081c4a00030300c00c0c00002c0c0b00c0c050800c1c0c2d41b50080480d4141552207180b600c0310300f445c8038202091003100510310080086055840c0070010410840c1c120f28007400c41c1d80030000c1c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 662973390 1250 662972140 662972143
    0x2040b03012904050126120a0e0f060301050d140c03031909081606210c170f250e04140f130809041e0c020120040b03011503150305 58
    0x22020200c1c420312400794441d40083c0821070f1400e02806141000105401c071031426010701481c104c6412104403030084006c8500402103400800030840069101d24100025190403115640d02441c115203440c915450301001490100700305400401030f12148070b1a1032456024001440c55800180550380d03568008954101d030060100f0420000c54900343c4082181200041d03648101d80c4089410540b40c0c0c1849025109944001c030900488040700c19103000112082c020420303612400d8640340748901450f962180c1c030540c000c01c0c07844403078a0b901c03c00503004180b0000d42103c0e50051164a4031000c8514125080d1114400c1c05400c542010442003004811243c03242c46914100c01280d61920340b10101041c81026290240c85004240200c405501d0540e001418041842c2e48580011036000c83d20380989006855240250355961354090601c954540c284c510704910740c021038a8282080b82c0501d0500060184a66003212590411482d9000741c0c0400950303042d0903100c00b040340e52460f10720f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 662974640 1250 662973390 662973431
    0x14190c02130606020a080705011d010f0c18090522050303060a05030105100e070e130501050a1502030406050f07050109051e0106031a07020120090312091c02040b0301 73
    0x100c0c055412040803660724441c0384218003d5841e154080c0141a1054070b48080b584c000303000956082d5070352480c005146000c03040c6901410004030000c0b6840b04643d03d807104507014000d00d24113015060f5450703d0170880400441c4162070a0701e500088644130400d40700b12120a441100180c088000c0f05a0309200c0000003851040104454203504243c4940c103150984400380c0d0740c4580300740c3c5000144000b1600c400e25641c04002407030040c4000301d00400058000440c0c0c500500d04035924001440b080c14880c40d6040500819440c1050304808044000d544e84614840c00f0200a00828001d0b0100b640008494005421800901140c3c00e00d0600640715583c0d40e0b02d845c04c55450088411005006006600840340c005207130180b02d0044400c44038061000900e214119541e13800c241e82c406070007103103000c41d0480171003816440d445104240b5107092000b07406010083e1050000c0d4001d95130b4038a001140c191040b40a03120b142092010402504041e070156903d035082c42c01c292180741c84030455 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 662975890 1250 662974640 662974643
    0xa18030504031101051606050405120a0e0f18040b0702030403020d060b0102060a062102030f010c08100806010e160201110406030902090c030c030c0a0c1a01180c05090114190c 77
    0x110315429003c030300151914841d82400500e8119401c102d5408101d49034456507215029000303882111580c1500040c066009007120f20201e82c8a0510b8003190600c5858441404070580d10100019103429a0403202c4000820007031003025090000380c4a2482401900c00642d4054022080ca66451078810098010820700c0c074014822500000c6504040f03004d06011120300e0190418801c40c24614400310b00d580c4841a80c0621410301d507518081c3c4240314a00d038444160340c40c0c42c0203080c510900c0303610702401c0d841101c3c542d0090b40103010091221841e00d0f0000001b2404988003003203c2c0b02640500041c18040782914408100001c1c11038040d040725001c10310860300010f00c1c0d40e44580802c00b5000030384000e81103000510001c0d2004141000404d22a661410701c0007461600f83d44110390941a6034020303001b41c5043c00100400d40316840200030214005100b40044482100e008029006d000602410002d01d81c0003d03a5603c003000c00ca4044603102810752500303403884117000e410315264000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 662977140 1250 662975890 662975903
    0x80a0c0c0306020715050402060d0c030204050603100302130e0601060c140106030b0702070b0c060c13120501090210020f1f06080f0d11030301030b04020108150402030901090b0601030915050a1803050403 89
    0x40807175058034103101d040e11483c1e005100c0d078204a0404011700040c40054a84c000385a403c000104050380c1b941c01841c8510001c0d08a0500c0c075013148103000600c9110305c240c04000e0301b000315039081c044e80811303c00c0c107603003a0349029612246541170070391051402c4184181c16510781840401440f4191140c0c9106480c2c503000c96111650b1010b48169078856181044c000750005404550040040e20041c550000224030055485032200004065101c12000890b0641e64a80b00c501c21410f0084001c0400403950000d488030300d0210803c0d9490316400490007041030900580989000302300d510400c064560300742281ea88071000903500740c0d649404074207040415036500c03a041c58418000100da0590341e1042400045481c2c2d075005455454000c0d181c00d0701e9200d1000a15025119440038520521034100040740520080c18403140000c000783c502c60400d4281103000d03000c07030502c00c0d40300745180900741c000445a03640c1c110a0000d000d0890711030215550074100b10241035001d0042c0059a00802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 662978390 1250 662977140 662977163
    0xc0801050105070b150a03050d121109090403030b0312120f060a081f18230d0905090c0903070f080d0503130221030d0608121204080a0c0c03060207 65
    0x549060007501c0d002404103200c10005511154410b030614540c5d040a00450421070300d0b95185400d040d5130600002c00200341c90804030020840b4000c090208280020507441e00c0e42074404642c00d481c000704042c061644039441c100c00ca0700e041140012800391000304945901e80005440004e803010784120036081c81d0309020413503900d0030004c007004480d48000106a0b05134540003280c3d280500c41c04244000e47e0b03483c0300e4072001c884c3c89240da50551040131071410404143e0300300b40c10014100e10f45400ca0303200c0001d0458842d007058a450540d0004c039190042e907036031035250441c5440707150381d816014020b040c000a455103024544c40150f4051000307984108003000d6040322640800c0b10302ea071b01c40c4101d60701c8501506115040795080e803c2810400c0c01d105e0700c40300c168a540e10040e1900c28543d80c0305010407441005100c103650030801c1200d620324100382c001280c480d1007009040a4a9140006a011001e6002d410391040032076000c2c40c908480760303890070f0400094224a005441d07a8aa04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 662979640 1250 662978390 662978399
    0x13121205151305060612070c23060709050303030a02280c03021c0f050d022209060509090a03080c04080703030201090b070c0f03140904180501140403080f06130903030c0801 76
    0x3e015443c0f1078a0042c000c9402c00c19801e02c0c090300c6d04c801038841814403000803140b201080900c0485812820350500340b040321800280501c0ca4032900401d403c041024a0009124959012003181c2d00300048020158980700705000c0b800540011042428284030316902070800d0315004901202c2c0b60340aa000d80c0e45030283c443d480d080100441e2810800a8451400340c00500e020300d010b0564124050001401d02010781c5840701104100580600c0c0f20304840c004201c40845030061002030309043c1e071903418034242040703101d698000026005080c0410000010a000c585005031802008210104c0d8030f05c0e030340d03410f0190080c40c034290166420a40b000004170100e01038402c2e0401d1a80c043e01100079590030f510308a80190014140c084400000c100046282d9500c2c000c041c01e101c1c0010302c8a10450759890b04900f1900f10707902c1e41104800d01806c10000c02d030000c074a290301002c200804102c0e0f61360030340043d91030720200e4110032026103080390040900d5416484100e201e201902c40f004640d032203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 662980890 1250 662979640 662979679
    0x20604080c2a0414221127072102030c0c0304140109053c1203090406080c060a030902010c06090f0c0e060303090409170309030703080109051312120515 67
    0x32115004060805144042c0903043c0300d102c591380c10b0154400c10218407420002a8103207c0000e04988410309100c06daa00c0c4020b00285240c1150003400c101e00300c111001c5070350601203c000b514040c41e56000c40000d4220024002300d5036041c40010549a955846030050246000c103210810b001510480c0301180d281028045414103941e54480b80c642a44d0002c009000d00b41c00c100061008a038103010001d45441e100c0301c0800019002c4042c40e220750b966010b000448400b50b00c054400d40c031111946800d620740e00111804c807001071034041044092800143c0b81140802001090341c1e141403540003d00c43c50203601d00c07030315204401c070072034180d82c900414080820a8906030781c950410040300c48507140c030f6441500b200348550340c80345015806d0100600c164004560301c50300d60b040012540101a40200d03810301501c880003081060b8141188041e18444036290000c005800b00110000700c0c6000d00c0c4466001005c2000610252802c01e403501c11081503158158007a110304040b564030a80c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 662982140 1250 662980890 662980931
    0x1709150f090f070e060928090201030510030b0106110a1703070f02070305030d0209030715050306010206090718020a020f0a030504050a05040902130207211716020604080c2a04 77
    0x1c940c0e100384d6441d151a410481403010207008580c0344c8400c00c072076804c0404480d0100303000c0301c2d0903100010405224000502900d43c001e0080514091038101440042e0100c60140e041d9085890409a11103c00094524201420002419900b591084c0c00c3d2091290002144501d05a40d1b900050b59101c0c44140d1b80c6952501005041c0e400520001d40146010740c0901140702c0b0050441c3c00c0b0558850a002c5c0c180718190190700028000810845039580400074690000200c01c0208503240c0341c00540d030320501040030070fa2422a00054400d000034420083c501510145a0960740c1ea13600a18024206601510450b4020440c2910015031403410744550a1069000b03000503401d2a200182d8a000b90f200c400211140307100d0046014a140c9507040b6441058400e485014440c1c100301208000c84800426514925080b582c035004500d5000c04c00c20740203070340907880341d0700ca4110076040c0b070404501808052a0450040c0134007a2146a2000c00810390010380e0100000340441c514003c0c4000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 662983390 1250 662982140 662982149
    0xf0a0c080a051005130204140402040506030a1502090a2301031b0207140103061203030b150c031209010b030a0b151225180c02010e030a1709150f090f07 67
    0x10484062400880d011342c200780e5108558200d00b0903c1015680021b00304c440480311150000e030074900f00000c50805219031070700204114000e10050361207564801856842d540f291000c1a00481c070140141c48040c1c052018003d115080f4100440303280d06011501411103045001034100104c1c03100e0707444031103401100030b4910360141130a20f0030140101c05400c84103500d00d041581c1e81d42d000a040710080900a5401e1080d50046070310806076003009108071403030001200d61441000344800c4400300008070340d80d10482041070069641c440060500404921800c84c0d09805001c2141c400c01403900310b981d204000b20300d8103011102034001400720500720007258545950001102900d00000c1d1154814092401240000140d880748035081a406585010040c901d45a032098040340e80c0a0044205c2010420021420950480c2c0010011510484500d191011550202d480103d00780550180c4e46c008009810300750900d14904521a80103e5180c80345001c0c55003074400325000400c81b001101c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 662984640 1250 662983390 662983393
    0x5090d0809121b01050c031603060b0306130b1e090906130f0c050429101b08090d03170121030e04200301050117130f030c050f0a0c080a05 61
    0x540181c02c034418290b2003403801014010300c40c400203500090074092144105080780c0c405880e030900810064000c5002c81caa203082c0b40c1000000c1c000d204000068941c08142160101c0c0e211602d40c542200806411850070307005001c8052030360114104407903174a4030042c15120002c0340c0e514144c1081e00c4510a4035440c60052410000f4000700b0716920060801502500d0f002c2d00d1550f5600010b001c441d480a40f100c45240b074141e002d180c003840f0a01c00300c008030064890034000104072000820590110200c1149981074078152010300c0315040c1641d4040501030b00c108002d48103410090510484540c0c2c121120003010008500807484805062500d076000203c1400602c8940d0103440510811921541041c0d0380c511200c0c42040100c0c0c024508407441c0b40f00f694950406000405200e01d1804021039079442d8800e100c0d440700300b80003018600381c0002e520031041500e403404650103806e090b409025841001d01c0007118140220b0040761961013041d407500c9035541c0704000c41d2240c00c00400170700305 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 662985890 1250 662984640 662984653
    0x120a1115071805100f0210051509220221011d06160c0605131b06080709061b0c050d05150a0c02060a20070501060e01081515060409020c0105090d0809 66
    0x13034500030b048070f40e194403060040c0d81500d405006080101c41003110042d00c6140c01c0c0e079071900076062031000c080e0030091301040980d01c0706100042000c54652160001d004112000801a14020000c00000303480d280c40000d0240e031044450f42d41501044554003480fa00030040401c4028440445103041c0c4403103074840d060fa200041d280c00004180003801e0b4601d80340903140c194002001c0d0420360b40807406a01c910b048090072f00000621484c002081c4100380544003206025240c1c10040c007401c04080b48107401c0e41c040c0c07540782420011000c4d90080350004c2041c54000304100022400c01500f00400302810b04c01d5841400c000c055616880c0f0010150300050003003505090660030644041c455820304885026180d4048803590744486802d6038244d64849050280d0b0700e13811581e600600126004011801c1c107149000314070342003e40131061303851006480f144142c48100c00d5800400c4405400c64440580c060424041c20044840f50280d0060301c14000c00180200101d601a100000c000c0c60b6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 662987140 1250 662985890 662985919
    0x5030613030e03030405040f020c1509031615020a02030c010b0301091110030e160e15061b070b120106031d0304050f03031303030e150c120a1115071805 67
    0x451245a04071960980400c12010515440c7c2d801400b00524552000580d1905465102e034201542001010701c207100c0c010902c801354100005803100a54a4000d80c03503001790750300c1d00d071181407001800c0350360890007c902205501e40100140c01d14170344000007800710b0340b500d2007050308841c10518002c0481c0121400c41840c1d0426034204030403402241000502030300c0c429101890a5080701c03282100d041d50100c280700d4400b4284004d030708400401307000e241220f044070011700103000f44070141d00d1152204600d800a0f1a08000000c01000180f652680c1c4250a10100400013024080c000c0840d040c400c0c40741d00744840c0781c2051956010407000e1801c26041508110900c5000400355500d407205108100138060920b8145e8010740c07107902c903440c0d410688000e001000e02001015110ba020038071580306005004220801444a86100c05590b901c040006584010550203060140d10420f01c1400c031070301000c10150300401030fa4441c4200c5500f00005284040c0c0759000d42500100c02070030204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 662988390 1250 662987140 662987147
    0x1f170c21060c0f070c17010605010806060d02031e0c0310060203270409020a180b060a171b18041a01140a0509090708070e0603010302031902042004050a0503061303 72
    0x7155128101a640c40d10301140c0303c06101703258982260544d100c00c4010a20049024800d035401488282085440b030301e4031100244481c00b030b100704c07031445540010000300d18a1040c0c8164010395513500100540341410740d04030000d6002200c21f1002400b0781c20000c542940004252100c004118544013440c520f00c0f05150410040c00218170380003912082c440c001a0368401d181d0015007a1584640c2c001e0101d604502c2c1594035410445004a0741046079070040f652011007005070440104181216440e0103415010221850381c801a0355030010603074540c0c0c18500644036040c13410440d8203014458151280192960080e01c0086c00700794101c0301d20180101e440081d040f65036030b60030b02c0c1c0d00700014040800d0780d09208944110000b210b203170030403201c1500100b0315841c04505507450b07403c641c11580402c2d074039485150440020709020018004542d50742d00100d0340d614609000005884551102c106260428007401c0c1c0f04d1864040081200d082c0000e42034070585160034141d04807030040d1400e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 662989640 1250 662988390 662988397
    0x20d021002010f020705010e06070f14090609280807050a061d120f070902030c04140f1906200d051305060304081b0a05061f170c21060c 60
    0x1900799501c030000001c01e0141440908440c0780150300100741e0f001d018200a0a00d44004c082e40e050260141c2c41440301c95000d0040c8442200c000051940c404c1d207007001482034024100701603484000c560040780000c0d11207890100305040012039100441c0c642c051940ca80f84a805200d802002c03000c400c0207220310602440d8400a62002c265111030550408540000e010060500301070744a00d1100c00c00144c100a444010580007604609504000d50382c007500744603500c50382c500c0200c034113480c0c40300e80d40d035500407040303d50020400c0f040c442205550080c10031031441100007040c00081c07001c5a0000c0b80c440c4645446001000c3c040c0c2c10404c00094405400c210188220482050380200701034862000840c000d030b029200f416210070724110030714452202010310450030740090000ca400118000b079039a03000b2051341d1408100ca01c6020a1f1305010b03103154803079000c0b004502410481c0400202e8801500039054500f41c1085455815014a00250440d00e03041c981c800350000d01280d00c00ca000c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 662990890 1250 662989640 662989669
    0x309081c0516170301031a0702030f0711042a030b040e0a020d2103020301090612020906040b0d06060906030203010c0f091809051501090c03091a040503070b011203030c0c020d02 78
    0xc5200f6902c50901c2c0b040754100341c0040380c02c06090700002441c203019165490307104a9a1000f90701d81210300314140124020a44d000303142c101e040e180b0300c107660390300e401c2003220070164180c4100415413052425031740000c00079554042464150050b105040070b00031010110190801000c12100581c2440b2302095010000c2d60440c0d009e818061101c0c4110750306500240440e500503881e941000680c00c1180e40a500030301c99821043c84010050f100e980000c0c2d4002070403600000c088107080003085002d400f20310014602e1749041008601400e682d405402a1380c000d030001c2015090114041d2890001c2e4250707100800d801a004209490404caa85c60343c044d01c0d4203010651541d40d580e22450440000f0032004074581210040c0700c0307250944500d8103000818034060000b29856100d0001d1800c000c404000e40c015041c000406001c820070454003d01e610030550b5007903680d01c42021301051101102100001e0a14480341015403260350300c4038000c0e07002040d100d6100025402c100b041c80c078101c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 662992140 1250 662990890 662990903
    0x1090c080c13080303100303090f180f0b060a120606090305061b0d09060c081b0405060c070b0f120f0415021606060f03021f021c02030f070309081c0516 67
    0x34080f4034640d003030014600a0404200042c00300d070135850003525001e40381c3c0208001b580846010000200c103c0c0c101065801c8400000805d0300c014994040500401041d80e034002c10001441a0071551007207a200c0d1000450204200c1180c441d0b20481e2549660310010b4041da02807000310341d002c110604140030001c0d4000c83c10b40351103035405040c0144d40c0710071003d49065640708640b03d50a43c225502540c0801c0c0404d00b1007841c1200110404503000c0c40c02154090700d03000c90004282c417401c100c43c1c40605036540d0140e441c4c01203a0302c4440e40717510440d8501492104800403a80001240360303414003840d40b20650424180d4030400c0b0340000e411400141440f111540350b40300100c2c98621034200503011001d440f00741c0e5400c60062104014220b5802e4401583d403440d03001e080d540c0400d0329000501d015503810030342c81110030220300c3e50203600030b203040c03840d400038400c0201608850b00100f124040020303a400005082c40c82c4018484105010001c11003c00001c914078008102d400c0c234480c4242c7c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 662993390 1250 662992140 662992177
    0xc020c1909090807060c03112b0207060b0102160602072310080703141b032a0a0909020a0f0318170a0e1e0118050d060b010801090c080c 60
    0xc0188269004040150f542507000250b010611005009964100080d41000c0c04000c074040c880b01080d106400c110b14280100303910441c0d480d40d280c0c08075a084140b00005640783c0d45582002e0004211182549016200c0c16803a044c8103000d0700319000480c1c4090f00500b0aa503d00700941160040c0104200000c0c05244c8800006546805a06405c0c0d40666a01060b6180c54540902203030300b5a209101707807031060810004000e8010b8100b01c0e80700c4401031b601e62a62a0401da2442802041910b40d100884013107000e41119400c1d0b01a0454500303035920701800580d10000c6108a20881004000080d03054140c01002030080d001002e2420481d1400c143d00d00181d11207200c2100c40300c42501c4000400500342d04100d90040c85940700050894121a0b402c5107030198060f03100d1680c01c51418840f2211400b501d846410300440010800648880c0c4074924a10700540184000f41242c2c1c0413804e4800046551a0b0034810b07500140b50a80312040a500c3e8000481d00c190060161481c5118421 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 662994640 1250 662993390 662993399
    0x70306030816050118020303090d021912031803120309031110052a03070309020d0b070c12030e070308090a15091401030c2a1b060e040c020c19 63
    0x28000b841d408078501c01164540140307240003401d42e0502c489200546860790300703280140c0d5011045032041d000031504a0300c0903040e440810090102a0740101c920342c8e00c0400007600305410300f13003650700e51302c42d82d2869010b10441504240ca4115400041c10f06034005d003210140074026401041e8250103800c6c40c0c85204036100125150284600328107404c00d03211001d20822070f50f208010b1054005440030142c5c09195006040d926002c0100280d0400d030f200c0c000302c015500d0f2248003880b4150015180f8685141c00321020700f550410000c22501d4041c42411500b44c248a44254404d03a000c0c000981400740c6151100f04a580140c03040c1c651041c00e40d90001400c45105581e164542c03034039194155510b03e4030300c042080e5941d07032400c0c0c0e05041c10400d1071020380b40d10421280c078228102440c00e0000100040e0b0380310f2070200c454028241c0c0a0a50840f0300c940d010007141089440560300d405140d01c886041c802540c06032540ca60260f0300500d05c1d490070307140c034150410f1120600300c2001007081c0e90303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 662995890 1250 662994640 662994653
    0x31509040b070c260d0e0307030509011211031302130501060f111e061e1308070f0b01081020031819110a0e1018090602030a15060809030a0807030603 66
    0x124518525101000416180b100c0b40e50244107041c11ba01c00195040ca5a9900c0c082e100e403040942c6e65040004018041c6084811940000c2c03180c0e40500351151645801c40400920005001e020f074490701c41d46440e81c150300340300c0c058541a01d0795a0f82e041034492050406880301003a082d01c0c00d44030f00821090f51407034000d080900f0900040c010003040f00381080000503141700382c2c42c07042d0074400404100301b0840c2041080c1001c503813540051501d40e2201681030500100c240d01c14000d0078607012000000320500c0014288141c4005502c042040422003040c021213141491583c4c05402d409100107400b1002c86800e4298a0902c54140c5105900300c0b503640044203007880d011104100c0c90914105542044c1e11940d01601804800603002c0c2410703001881030030181d2003600942200720108002c220140d4015402259000c1c0055440e4203103c0304170409050041c2c803095401007190800284c8603c01c600321405201004055440c0600304c49040320200f400a1080c000d00d0313105c400020000c4e10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 662997140 1250 662995890 662995943
    0x30709052701060501090509040c29070b04031d01092612030417040e040f050c04180b0a0c05030711161511060714090d06060308031509040b070c 64
    0x11214000a110b0381000005040c6d1001a0003c9000725003080800002901001000094034400724154006602106d0102945003400c119000e540401203001c2c0100400428410300852007030311011902d00d1903500400d005240c0550490025140e1034080003542001080d81e41e161140c1c00422001e01e022401ea54a8805414043d20540340c00104000501c004040f60b00c8449140301c042c20318081c075080391b118412501070800f5180c1000c100c2910200b0004111a071070910000e0424040c0800382201459140442107003a038400e4404400943c8400aa103c0c284103d80c06458150650700c0e4100d00720780144008c614034a0ba4803034000d6035000f102c6d8402001c4010410252800c0d8000681040200882402c03500c80782294025428060300c240c1180281404192080c40d00ea140c0c04044002003071000034a201408031450705c14040240040c24000707501c501e4106460646c0c0c0b0b0444401d100d40f5041c1280e02904055102020a00c550700c41c09403000540c0c0200500c0c03401c0140c0340b400e0306803c6d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 662998390 1250 662997140 662997211
    0x4060504030302011407091716060e010905100c03050313080711130b0108060409030537020703020105030f280b10020705090f0c07061802010e0f03070905 68
    0x180085420400c140e424001c5a000400c070341c040e20242c0c01d2120b0098005e94441c003074440414007100e100c2a400f901084140070310031100c02c2d589101981c504021345032810301800719000600a4001240ca81804010342c0d80d00341056480d00c1c000580d94508071120f0b00003410400c01554640d20702c40210f5008406030044c40d000c2c1e00100c0402c400d0b40d04200d02042c002c29544442410714800d0005e0703a130420612640258141ca0100301181d60386011920780c4100c0da00e9034030808400410360b1244111082c60207110f4a40c00d0b40034130b150b002085c140e80e0740c0c5441c40000d0000750104001007003c0300c4101d0f45a0080c40824051a0302040c03603a807865118907160300044803a94400408004e841c188607003880c0c42c14640090a4614104000300d800701c10010580148c5c00784100125030301000500895640c260480c804000740d0320042996070705152031010036400110442c80ca00000e00e0101c0d40c0140c9000010010031402e841c00d10700c0009000000c2410044186c4418600b5404134603000c0340243d10f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 662999640 1250 662998390 662998397
    0x513120e01033b1905060f010b1309020a03060902030f06190303020a0f02010e1302030906010e090307030c022d10050a0504030b09070f03051518030904200406 70
    0x40840300040454040409064031000494a6807898410f001e03101c1c8465040e1442d1400d40d010312140030703890300700f403405141d40c00581c00080c042400004524217010701e520541d0b417001e5999400700b2040c20b000f46114120100700700041044403111650040901004ca0b003000324032243d40342880c50072a00100c51802c100003900e01005094503004282d02107031016130340300d000403c0c1161002551041d940c03a00401c001803107a6036405582c0200300b012250340c401045e00d100d0101d810b549102035001075540d032586200389000070441c00c0c00482528403800c80342c0000c604065503500e0450399150300c42002d0342c020542000810955210402404c80803000141c0403041030040b106210254940205210800c401070103420b81140d0300004840c1146d0300302000134200d444590520381880c0e0207511080040c40111000000c20801251091003440050724a0040c3d40d112400c8c4820107c0290b004100e58104000e0b10707040380b41561007401c130301449540301111020b015003403802d80d52203904041c020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 663000890 1250 662999640 662999657
    0x150c0614090c0f0102012003040809030321150d02011211040902070308370228030506030a02090c0a1103180913080901080a1803030b030c04051504051312 68
    0x30f401c03c259492003000d4207100800014059803000002c2c40b480c000006480800000454240303c450710503201d00c1d140c001c00f5250b07540e1040c41001c0e59006a00c406610001c0f04000080080407554060320359250003403c001c45804103580111000c10340c40040052180d5103034040f48150300b01001a00191014810050742d40d0410304001d8580e140c010312601c001890740581c0e56000c190141010b03500540b09854a5000d25130b0707002c000182c00b640700410060f594449100000041e50400c0b8110080c0a450810581d101c0005164a484c001800a5040750460000c1507032070303004e500101515200b525005e1403400002c000c2d503065600c00b460b010a45c41c8090300003039081c5030000d04d80e070f001003000c0c40c00141002d0f19500c2003202d024842c0d40070f041c4400c810000314481026000407590068211132240303c0e10007480d01074010035242c0081350092080ca101c174006801d1030304c6180d010300c003182e800684094248040002818004001e80441c07a01c00c60b5290001d40c21010344e12441c2c12540b0b82414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 663002140 1250 663000890 663000913
    0x9050a0b0a0f06080a020d03170705070c0504020712050307180b0c0606060c0a0f03030b0d05010c031a240906120f0a110a1404081002090f030601150c061409 69
    0x55841c40000c80c20b0882c6400c00400c00303410002400c68403a0360640d00044540300030706054a0202c0c6007d0602c44074604e8104101d40540d02100034462284141800c0c00595112800d000c201d000d070800c020006001c1e29401c0d26243d01a030301860303000c00c25203000b40102a481f80e40c0050600d056020020358070000c9035400140400340000d9a10440580721103050803425120f0580d500190340001d0140000d48601000b4188039800261403840c2c0506484050350321441c2090091110307401c1100001d28110003080210102c6a030300e9250040141650102c103d90814607041902815288142600c208802212900c1344000341039042c1c00c0710f40c082001e00c0c25007003010b071088006003a000d806240031420080c15000384165501f001c00f44c0303444196040c285084c942c1c588680e4100807203501c20082c2103900c900c40364008104a101c2580c030358456403881014541d42e0f00302809000e4240d06445001c1113100d205a001040090103280d003c942140103450300e40e0205400d03528150a07400c100c259a6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 663003390 1250 663002140 663002161
    0x507020a06030509100c17250201050123040b09090d03051e160908010e0f150105030727060303090518070207050402090a0803040801060e22021309050a0b 68
    0x40040c4102e04050046207004002161030b04443c81d07104031079541d600900311031107105074841004d07031903802c000c42c2d0030f0308100711101518501035110b4196068017003c540d80403403042c000d06040b200d140c0e88050900003036080600c440827200946503040f071b640d00381c4c1001039900c001005000343e525a001d0b01c0b5124409000600b0b84500034281184a0346005088404002900c0c2669110245403038007000000444401c0f030351801940d101d41c0080d0300b01100b8a111000100b619482c50303560a044403100e000040d25101c001c8024811a03030b05801051040022030911501d94000160004074004d4a101410080e01240c0d01504283d00140c0110800d201d41d0401c1001c12240701841c4a90741c00030b1410041c001c5d5100168040c1c5409281c006c19078420310b4035011010000707090a0001c0e02d845a071540304642c0208070034412005080b400e6008169190660180c0030b96142c00d590030520141129000d0140c90090900843c601c00e41d180d1450300410001c1c1700ea0ba0005d445400e11543c0c07410000944c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 663004640 1250 663003390 663003409
    0x106020303192c0d030b12030d0b01020a0c080a110301140105041d060f10050616030e0a050607030c050132181b0a0f05010c0b04080c0d050702 63
    0x1594401c0090064050720403a481010031800c120124501800c40c40030881d506241440b035603c0c410a941c1419142d20114071925043c1450303404224040c0c85d0020488140502d440048040d001080350080c40320341c0303401c103451440c01801240c10382a51503030307001701e2040e060b13104031015048121000c041001c0c009440c180b512085009000414103084a040b104a06109162195a8851802c000718200c482c0802035a50814250740c02c910b800c6268502c8070604031040c00d04e00c102c002c4003103410b00c1d1072030560350090800c03050f14442c03100560b0252440c0e451610550b038485c058800c00122a034650009128503486562610802000381c035205095580211090070b81160000c0303026001080d040340d58183c159074440e00b2011343c940303009085402030320f20b1800c0c06034002c014400341d100c640185101c3d2140b500352001001170355541c0c10380d00f120b82103000d001c2c009001408100003203605030407925007203401488114504030307204092618100301c500300030300454004900c25096140c80c5844 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 663005890 1250 663004640 663004649
    0xf0b0315061c050c07020603060904031b081312030903060b0411040305030a030c09140105070f0b0708041406190e070905090a03080f040b010611030909130b1e190b04050c04030b01 79
    0x411700b442656400070f401c0d0b002c0140460b0085003a200050189441540381c540070203280b60b040c06000da20307410076581c1944010034400a5201c020300000342040b182000c00103060300b640d50710311007a086644107005405000b030030075401a01c0b6118100c0d00d0304040000c0000f144100c0043daa20021600041c003901d401c4c0010344c0521201303160820412652020481c5615024604a80d4a140500d44449a1000080701500608419080100c1070b5000f401082c000c50041e03400f88884940d00e84030582c0c49400301c0b0714901091841c0b03a0040d020005401451400f0a1401a1038070340381c440642108440007142c401c2302c40e522100c0070005158000c401d07a5000000c03280600000d140c240c507200d0a00c034040c4912070810440b0009881007917800e0090350b0406c0b000a02244c2c0600704200d40440d044030b40d01051301c81d09851000320710f0600a83c4e01451110070805056800d560b40e4645622080700b024225180301925207810304055920343c8a402d11602c00c2c00d80d010f44407400d6080c01c00360400d05802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 663007140 1250 663005890 663005911
    0x1203052d120a0b0609040b0a0b191b050a140a050a0b1f0302060702091906033807140c010609051006170406020702120105090c0f0a0f0b0315061c05 65
    0x201d0405484640450305d40060680b070102e40c0039039500104800801a03130056140345004540c3c407091142d07030040ca0142110560310441030b0414092801494225400d0003400c40d844501c1110024500c5e00300c911456080905440001d05580c0750241007000b141400c55000c0c1c604010040c0384201d0700c980c103509800d0a45a000c00354190390108800344103140000c0d03c10743c074030301c0007860748a1942c1c5894402032002e00f040c09155900c0c9052110426211503556407a003e190000140351003d1000545182409122071103a4403075041c26550b85900c01c0455100040400282403407080c2402142c004218001e00015245800042071010b8400e54028104101c644141702c5401e4441d50107164105801000041c0e03903800610006000d000e00040f1000694206006c006100d00302080c2d00c02c8540055480c00c081800300000c02c000310125004074040d14880100c240308000c02100503580c441120400483d01c44282e9000641d0790300001c18641e01e0b0b5007030f5880210401e039035020300354100071541d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 663008390 1250 663007140 663007151
    0x1210140903120a050a0209030d0e090a09080a0f02030f1303110102060709210c15030f1112090f191202030306060403020d060b0a140301151203052d120a 67
    0x604080d4800007403c05001a520f4001044040314142e0442e081100000e0445085001952000e41410303048072100c0c2c8111104000151501d01c1c0340901740d906075000e502246000c189003400c1e1042d1000325035810031448148800007401c03080e40e006056951018940d42205c500d585454012a00c021451604540000d410302403060b4000d40040d00340c0e001c9204084502d04500c031820084c1d658120044d10a040c01c0c1c00000d640c1805c0c001082d0b0140c0b05075402c0c4181080c581c10340d002ea0f06aa4045540b413403080004a01c103204020200f50000c0300c5600756440c3e200c402e03030501d252130040400d43d82a0808088041d040100c000966690380340c50740055070a44c945a00020705c81e0151344806801500114159001c200c01c0303520004a1110081c150749429848084080041c440681c60320b000750320b0304410740c19003602c0c0440c01048420f04a591119040c150758125010f420448040c880c204207100702040032601400040000c000f0901c1007521484d00817010315007424084c1000f40d84501d0f11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 663009640 1250 663008390 663008407
    0x13090515031e150405030702030d0816020a020f1c0602030f160305011208090d150b010311070503041205120f0307080a050f0718080106080d0f2109021210140903 71
    0x700f80d209140107403002c400303450340e541d0800f18203511490000a501d40116407e12038203a07003184106029001003200203518240418043c1d0744d03142d00c80c0c8040c0d40401d0303165172a8110300c2c2c5001c20b03003e0101c1da802c0002601043d6038402050f030700251801d02c0d081d83c0705020040001c0c00041c07080700050301440d013840a54584030007510741d9551b00a025015540000306140e1039101c005400300d00070b0f44200b00c50f030b02800f0717400448004c3c00c0070f80c440c50000c0e0a205150412541c0001620b1006400401540c5400d1415901c174040c0d141120084480340a40c0303c2d07105106807040040c00101f801c005559540c4e00d01003400500c40c03000201305550083c940b03412304c0000c0700304109080c1d100341c01d801c00c11101460044000d001c05205d034031108456003042004203003581d000c22242c000e0b079001d84a21140001f000b00a48104040b1084608206403412240c0c10010241d04030072035031400500481d052034102c1d080709003004aa1903420141e02d4448015860118101920a9108040101550804c0701c02e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 663010890 1250 663009640 663009643
    0x21806160b0c2106032109060c070f0306060e0f090a020f011e0504030b0c0c06040f020d060513112d120a0506010609050d12030213090515031e 63
    0x48000500602441c1000802405520781140c20440141c42848a41e282d501d1041c0c0043c4801c0b00c813240280100503603466a03480901c100300150440c561007071308150108040c48100c1e002040c4041031032146400c00251001006e540f14080c60041e50b0103e403a5090103181c0f00c07182c40c060580b80d00725000b9010002210320114151240a40c100c52030803240020b803004803800c40c0d21504000c0314241245103150b02a030042e00400490788034034070034200f5a507217500030b41a40c05108100d89040e0001030000700007a10416072120558801020111440c299490300305c102d4400f20f89020000f0b05014000d402d1000c64900f0442c1080c0882e032030304101c6400007a44d201040055048620f4044d1250105551390390b81010705c80700300c080b404036110080f103401c00d80d03940c3c1021310410010500c0d261740400c0c075003460800c2000c16500024000a00c0e054504102d00950080402e072850940818011807050000d014240c05069a25401d0f210001c0f000201400e0140c00c0c1d81d00a0194040320124035101d50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 663012140 1250 663010890 663010927
    0xb0a080703180203010c0203071401020c0a0f050a050d0309150504052d0d0f08011d270d0e030111160f03020a0611030f0708060102100c140d021806 65
    0x40c03a000c0b03441840c1d42489500d45181040c0298154203100d040380c189940007000d040e030140100303600801b002ca484580350803442500f0307086000c1d401c07883c00c410201e001e10041201252142045440d0200c154440301c1c201214040b5110000341c49050410601806400c0b08040c810742410800c407030301f025924281e5882c960205d850b80c0400c011031015a04200d0460b8541e0307001e0100c15104e100a00c03200003081c10014140f40000305d8818000840d250104840d4545119110079412100e911900c03078022a908070300030040004c20007086841419401400300328850f208980f14659000794540805003551428440b420040c001440105000340a1244480f0655000b22006007102c1c10b500701241449500c44000d02210304000e0780701640d8004070015403203440600d212003003e4451450445003c08180e5400d40164001f143c02a107622859000f18905030660030b0000003586a40f46446071904880e015401c800d070f000c984014210100d80d241903040c6400c44e40185007240d0802c5007076203881c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 663013390 1250 663012140 663012151
    0xc0f070612230901020906070b220305070b06060d0911040e0f0309060a0e09040f021003050402010c11011809020408010e0c060d02030712020c0c010306080d12050c040504060803130b0a08 82
    0x110b04030b021888454080d0304035144c03070030041e028558030a51400c0801180c4070564180d020b000201e181038484a0003ca41043c0c0c066142d51500d01d00300c507036142c04800c01030140981d40d20000c2000510f840700080d02c1505911071140392070148110a403410002120f502058058054002c001440646030003c012580300902c01c5480c280c0341e11039160211303280c0700314000c200d4200e81641e0601051003540c0050b0786120b03208a03951280d40c140c14104806440007524024049100043c2c4080081c2034443d00800800045c0340030301100e0390080840e0441c0b10182e200e9118940e00040c24070820400380520302d4090103075001454032482c56004611240b2540c03102c0c8003015404004140c01031b203e903e8601c10034034904425515610801607640e16440b0030305a060109103004d000103801000440d5a05c1a00c0040d1500c2003031400b47d91580005e010000d002145c0144100301c0483c4a565601c185e0001c0e0524100468a5000c0382c0c410b001407040d240c01c00740043c4420f0112104032603202804a5002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 663014640 1250 663013390 663013451
    0x2160302011116470c011407031a15120702010b030d1d0102070f1413050403020c15040e0703020c1009050309150405030a020f060c0f070612 62
    0x6908520142450f6010b6641c940802c4168000950340810100301000d00b0707a40215041100040f40310303094800079444a00e480001d0244410f84140243d0020f015884603031800812020755090141c110300e00112108004640d4a140f042484010351220800781401510240e405110782954401540206030201300c2601c0b204d000281118800e4004a156000141c112005100e100401528a22807041803640598040072007040e15840000d00900300c9010015031002c05040444072503c50001040c8d294010119000080801d445846800d1085000b030b070161084256000070044003c940c2c840480c035001b401c0c4014048540e0003c075040c0c110708a03007801a43d41800d5442d890a0207001c1040110305031421030a07009200012000304010601100c014140d8050840581510300075030050301c0d010b500003107a020060810860031801004000c1c047c90801c00e000740210301c0c0018a851110154004004c1044840e4000c0d000000a0340e40401c14018040d40281c07018500088294511a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 663015890 1250 663014640 663014657
    0x10b06030c0306032515030516030e010e070b0301030b060909100f06050306091507051303080d151e06030b0303270a0303020606030706030c081311100c02040b010216030201 76
    0x243c0c0d0401034010507034120640d6080040c0b07818108585d2006038072825200b0703007070b0071400030403688070b449514810a4251407130003101031610303021401040b04610740320056603036030f5002ca0070314802c215a50081001491040c0d0320341c1503141c1300340c1707102000e061a40039003040e00902042c1400402c13000c0c104040300c0d100203441c802d00c800c404082c00341d551007590140580c50038003118140215000c5540390f24428181c00589034000101c60034880c130305c03a0159028103c2001c0c000510901e00501c0da20582c82e2010900c0c02e000e45070541c10300b0455121802c1c040e80ca41c03503401401200000d5100500403030800308000c48910010903100d10a2001d0034520411501d409469412190003000000300d000d0601003045849140c0070350b69001c1615102d20a2144220000d4001c1c46402403038003004d240d56a0781003d403035080f0245460700d0700c00b80440703103804080e101b9452034803103050000308030501d030769003018110301ba00520048844001880c0c2c11034000b1040c17440e1ba0700003007610100f103035420728240a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 663017140 1250 663015890 663015901
    0x1c1a01030b100e15161a0601050418060e0108030403060605041103010e060406090f27230a021c061a0307180f050f160c0c051e030d051b010b06030c03 66
    0x468114481303944c450300703011801c0010400c010441502043c880e1888910703030280c140391910701040441d007860014504200600c080720b07018482c641140000003010074980c2e01ca0040099002c0d00340c000c2d000a42c00403030204240081405280000d040c190340403c4001c5e9044908101880140101c1000380400781c04103119466640c00080180101e00c02048030005000801010700740d808811a11034030703030104c200221076440034184880b56110b4214880700428202c2d114410281d6450100140100302400c00580c40300b0340312040401c5144210301d03200140d844d00700304030740704000d0490b803e41c01860241c0707207074500003600340c1507441e02e11020400c8040c840c03481d000780c500b00605880703031400c1c03d0500034544103459129008040001d800741c0d010307002003022502080c03070380700c098290190300000f0812410409038107017101485507410142c018441001c24544508003c003003000800c00524032035550a0048015411402c640003402a050004002a414003010b0040440e51100002144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 663018390 1250 663017140 663017149
    0x1d01080411011106042003070503190c0e010605041a03270c060d0b0301060b070b01030f0f0515010e07051804020a0507021201020d0b0409051b03031c1a01030b100e 72
    0x503c503800074402c80703169181c80d2801001102d0b035214403d450f40e0054250aa8916010855400340c92019000700345803203c3d45800c84000b040c525054400c0005d9103404980041d9070740ca4035019240d29202d13650b43d60329091000448001c40c0400300c080b14424400d1200d6104400142090f803954000d0b0f0074024500014001e050102085007503500500c00904d0442840700f1740c0110401c0700c0101d000b0481e190743c0d10829240d51240d00e40041801c0741103c0148005640d07250742c440040e010f80c10007030301d0640780d60300e02c2d240c4401810503907c90b0074484010824a80d8802205910005a02c1c0007410003541503100c204070812440c0c07040c810b50b00820b214007054420004d50700c4482d00205901812429035100740c0c000c1d0b01c50300054003524108128003205040c14000c8a0060342e001004010000310030b42c144040700282c0c05003036818081041941c50003584003040b0b60381503981c0b2400103400d0f101c08604800d0090100d07003140c181800c02d101900195110302101c3c9610440d03007071085c02c2c2c251003000039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 663019640 1250 663018390 663018407
    0x100b061204210905040e0c24070b150f0a080a030e0621040c0e0f0a0c02010b041a0a0e010b032a0406050912070807060f09030f0b071d0108041101 64
    0x58002c0b002140310500c080e8000c0f9410225401601c0800545100d52592511210101e0300b151300010003a01c03020310003100741c141041c0c0e00e606003611404c080d416514942d9170b200c00e48018034618101a0814a24505400000441c1d041243c0c21009646403030b10003620b41240d6030010701400130b004285640783d02c400c0d04407004c02441410191400c40c090807030104800c0141c0c1c0c1071703c001d0001c403030100d0502040401c41d801480b543d00050b00b16038036070b00c0001c041c0c54044c030790030b00715525508100003030344450007241c00100700440c24414001c000c400748900312400c2d41c00140241107030401080090403c008494016008848000c001d0119007400d030000c0a00c005000c42c0703601c00040003d03c0c2640701000c0d0101180c2260410052502c000445d5a220102d02840c5074039000018204a00c078010903031800c2080540c10402e012580e0782c0c0301c005120b01070240c00c1c1d581c9441c50003046013244e88150420201030540240b0180e5103000c0b0002480c3c0c40c0300034001004031800345101031079a0b0061010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 663020890 1250 663019640 663019673
    0x90301060f03060207121b1514010311280501030b0303160602091f0e0f01030f060806060916090e04030c080a03090311151b0c0d0c0302100b061204 65
    0x2050030780c1e8910b00403000b580039080c01d60b0034000a90b080306650388140d44004039000c502001e15071071a0651503c0d00c501c441842c1400c00d45135101c1d501c26141644800c82402180540d0300246801d02d04400d05c001400b042c20a4040c072440000b0041d20800004145410340d0000e181c0001c02001c2040442d142d48500c42e0f40c026864400d0000070208400c039002045211401d07181d400e40c1c0c4012825502c6002c4c0c8000f1a440401c0034000490106c0c1000d000001c00060140b5001c645410354207041d0b01180d405401c6000c041d00544200850383c103204000503004201040c1d440e40102c403800e00180325032a28003070300f00610085d001250900d44038480107841d40d500a290705940e58060800640240006c2000301d02080d60f141f00c0d041ca04c02c010483c801d0300303007451803400c0a943c0c40d80420b800100300d19414100f403a40074400d102c00c81004204815402d911504d070144824540d0a02924204d0301106808180c0e042081013800d50700c0e5802529015000f460b40c4003c25141d5240681060204008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 663022140 1250 663020890 663020909
    0xc0b1005011707030e0a0521030c0a0f091d01051005030c120a02120f040302120a0e0420040305070f0e150105070c08122d160c080a030804021206070e0609030106 71
    0x1e60b8040c4080031235a01c031a0803504120000d604941c074a0354030303070b400111070341004070b0000e10420050b0750042a41340141c00f0b8a241000720b551320380030017412200b4071151000320712070344030014012410011500a0410454109541540381c00d0001c0c50803032007901d0700300c010b10004c100442c0303901449130159080c1c046080c1c0c581c5840d03c0d00d024002d500c0c0008403010b038018030a600c940303000b9101550840d4403445440c0d0710000b188684c84240005400440000c05031390b068186501040708500000d0400746201d203000c1c00c103140c0b03000300740100503040d40c000340b1482c500300f424414000516040c00108840030308000c5d80300c00c80c60610700b0100d0714a500c10720302e03801207081011030285d800000384000101e251020100c2c01304002010070907003402c05540404001040300721100d5001482d01210741d4490028400000d40f00c4000d41c0c02c010590b0307030031000700381c0d0081440214135000f84010700e014180b800400e0146001070b0000c200c68000000039014180003e0900a80e03107084d0400b1014080c0740300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 663023390 1250 663022140 663022153
    0x1119030621060c0809062403030f040611010c020c0f04180c170726030409020408011e0b0d060f1d06040204050603070305210c010c0c0b1005011707030e 67
    0x16800c0300c000500204030707405440c0603c403041040c01210703118050451306000740840d6480c100d41700c3c0c42003030580c00000c400351000801605035800700010f041606800346266201da1800c50040c01582c1c040c2603000b220f0741001d068203003080c2c0c0003e45d0b910488045918090b00c08070480414000c2010603007070703415104c01b513a00100740721440e89844111640058140069400406440d484c0c49190240c46a080341001080b0340401421603106619400c0d0010b4034906955000420100c1c4e000d5407007020113075100d0001102e109220740c011409815585020320081ca8010002030406804040c0102103981d070300407200b050700566010341504854038107480b940c5500c00089580d80c5000302e5040b44602c2c2060700082041c240030035000304030781d4850002d2026095101c25041c0700184203440e40c0c45607100380034a280c244002d00408050303070100d4941102c1e400c81ca003004010300b2002000702000202c403060801840c0d07408070300782c0d40a181107140c0050f1522500c0e811405042000321511080c420355 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 663024640 1250 663023390 663023429
    0x10b0316031e0f050405060a020c0a021509090f060f01031103073203180c010f0807230903070918060b0a0b03040812091c110a080c010f050a11190306 66
    0x40d40218050343c080d80841d18103a588d181d01c1000c3c1e129402e480c0700d541e003110400d0001410b1440203150000001804203040c0461600410b4041d1340440305092503801c15424400b40f41005007582c80d06c08404c0c41e080c001c9802c040c000c28420322001d0300e500c00f00084e030685036600300529011900c40e1011400301e42e100d8001d0300c251580c20b810030b8503686214007001c030301e40401410004031040f0408040e110001e07040440c0308141c407030090051030101400021501c803802c81c039041c9440300840554414941c0c031030800d07409252600304180c00a00c013651a040001c400520700d110700c210410ba01c41c10116203410a5000f040420308941d20501c540314010091004000700700000c0c00840080904140c1340b59213658085503610700002c40002d00e80070000801103100c1c4104040004208048100e0700c0208a0ba5500d1b48142e0022180b117109940d1030720458106070340c5001c0e058006240c040c007840b8600c0b000e40407045070311842c0b0281c0b066032484490901494080c2d0000780080c40c0d040801d400c4070080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 663025890 1250 663024640 663024671
    0x4050126150406092313080a090303030e0f12070204020c10062301090b0304020619050a090512060a05041b0306060501080c0703080412050d0e01020a020105010b0316031e 75
    0x68a4940b040e41020008120203806104600d481545518815900b4820f801c80540e071481c0a050000e401004080c01000b20b4411001003c404016980b5003e03814918140202102c4200c0b102c2c450300e07003050302d0452001000103582271041c0045908940c0e01c8042c0d20024000340b0560700700c1091401000ea0904a015403a44284100e074850340042131425607010200704107000621686000c40c0000f82d00380081170400c1e001d1503100d40302419062920707040c540506035403d00c1380107900000d17400090448040b641300003620002d005c00d80d140e120304000420526180d00000309440801c594035030010b4180504280850717080c04240c6c20340e1403425280e062000181200b4040d1a0105100d98085900070a011003100d9580d9010b90b01c445e502d45941c0e84040380c8464520109081050038040010784107120310070801c0100f00310b00010390ba02e403540c074060300b03480b41684107103981202441002140e413101a1001c0d210f030b029140012f103080b220034800510410300c000300344406241810f000b084218 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 663027140 1250 663025890 663025921
    0xd11010323060102060907030305160f150518030408060c1612020610062c06042c130305070809031501080d082401030908070f0c030303060608060604050126 69
    0x901307030f00341e609540d00c00704000d030f48900d035202c003d0001c1c10420240c24a51042c8102107240c0344519259220303031b00940c9a110390109070754601c00307071165203c00348550344070030369001c80350004060084c608040c506101151170303420040c101d000c6000d00003400d5100022064920b001e003644407203803408440019400035913032541221002017a003683c1c400416518066203201000c001001c550084100810542c400520205d0300c1e45a0000414070002c20245003003440072941040c02004250060390f90f0146c81d651400250184d040e0700303480344003000440d900008480c2810b41115041c0e545600960209103040c034a00c1d10f8810703440e01d610002c100914040b0780383c02890080d40c1c0744050303501c6404004002071000005c0321200068000c411040d54001d421040001d405513150605140c690740b560360061030002011a040940204e06004054040c400c0e0006000c591034110050701c0d060020a0340c1d1700c240e000301c505014000401350b1460403c4240c9880c4140e04c3c1e403032070700a810025850412800b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 663028390 1250 663027140 663027151
    0x9112101090b011e112b1b020604030b0c130e04020f0102071511030c030d0e060709030b180a021302040f1e060f020a1712150d11010323 60
    0x1030401d03040610799132294030107407840c4001c2c1542101c1030880b0401541c10541c074100008041c090a40b014441c0c26405010084400302000000902d40700140000e080c40c2c24100380840c1501c06e51080c9000d40c50b840d050750252030384010415450b880e44c05e5107181500660740e0307800180040080c041203031070007080814080d5200741d80d202001c6582500590711010780d0700822000b9507030110700c00101c520440108140c002c42200f62440c02c00004102400c3d54006051041040d441e0080d10040c00420040e6a03480a07661900602e09829595070900c005c1c006000c0c0035503480c452180254102c1e0900a101c00a0303030080424030582140d5030594042c0d0080d11860800c08a45403002400c82807402040000001c46049584100d003009003d4441c2042050074004500c02c03031903010001110311125491040d105860180c460100c000d00c604201002480c41d0303c0c42c10908683d00507510b840c84946840c2d0b5014039503102d28050f902c0100c000b80a600c41c6038003096028180c0c0c3c0f58520780541c11a0180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 663029640 1250 663028390 663028409
    0xe0108092a0103020c010603050312010e3603070b010e010602010c050f0705190303050406110711151c050108060903030402010f0e060d020c010518010b010909112101 73
    0xe565054419840303810228007203110300000070348407003080d00ca10269061458141401030400305000311090841d0500c0d001220240d00000300180c100d51514a19401041039a404030328a00e40408041000203011000903407803006150446419040c207090281c80188a00880340c6500b03a0b4200109582c80a10800452000d190004900307948180100c161100440d00c605141c000c0d806d0700032100f54050002680c20307026040c01d0902d207005842255a825000f540c010071a8181424200d08642c8400d02c000d4080e1420403040c800543c82c494004803082080b030380340400060701c907240401e0344500080709800e41100ea607400d47c100365507401a4165088001215001c2c0d40d5191425070f248070644000e8003041100c1c00e6034405521445481c044000094035650400e0f500c4100f910a036009a44030203466512001000b204014049c0104080c4260000910007803007100c00190100030140501c03079001c0d032183c8107a200d01074040c0c1107a007168190075598140341d140d0110a50020000c4c01a101031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 663030890 1250 663029640 663029657
    0xe01020a030f0203090304051e060a11100b0a05040507110304060c051902060306090c040b130306050f0103082a031602150c0309040b0d060516020d03270201020703060c0e01 76
    0x3502c00d284203a03449030040d20010740c0b4050030034080180c00d105185414907034015003415081207841e03010190000340c81c0c9840b071039240060794010b0b900309900103803c03070b0701c851800601c0c2200b81e1300c040b10300040750343c244c400050a89405508403a8030007400301804440c4000140003c44035844903032501054090b0b0155403013a5200510f202001110360700c0031f03621110070310103c1d010785490b050141d001030418030300b41e107400e1b0b440003a1021904501c002c2604030191040400622005000d560b5004905078400500ca60440d40e03500704074069100d03508812801e80c40b1408026010103240d031030f1420380404030f81d00c50f03e40f0325a13910014008401240240340c802c0305100c0308009501610384108200e0050b606080120703083c040100346000d003003540030560540c040003003440c034411180a0500c01c481c5901000c05540b0280c0740c844007019032810103141c9941040c090903141014282c2ca000303c0111400d034a11800100c0c41d0900680024200c189400150702001e0341221990a081200782c0b5003108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 663032140 1250 663030890 663030911
    0x905160e010e010501050922060f1725050909031b030408032706030a050105010e010e03030316090e09070513060b031f1806030b0f01060f050d0603060e01020a03 71
    0x104040a100308420b4160580040c456517006502074100b143d4050071841881c1c4664220b8110941395454580e1243d03a101028001007144940c030802400c0101301c90302000052481047e5140e02c2c00035122400c0d240036003004000140607554034002d0600070a51400740c1040c1c105941ca950114544500c0c021000d0344041c22601e0110541d0300310384400014608048a0f0a4501c4039888811540c41034441d8042c20529541d50303440240d0700445c0d0600001a09604000000d40140340e4251000d06005851074641060341e0000f0840e075000d006490001000c40c0300842c1912019860b0308180340c10f507440400c100e006d50740090700d1001c0311000c94911040340c0990507540200c1d60170340564090a541040041c010440b8980b01495480c03500114401d5541d82e48804002409400c0800c18030649801e01002030044a90710070360482207180c0d00840651400801800b4605040c4004c400e120b008036001052a5140c1d121038000c6030800414480100d4031000c040c000e41c09041e242022034600b480844 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 663033390 1250 663032140 663032159
    0xa080f1005100e15040f0e0c1914030f0d11010b0609090a020a09050a0f081506100f050702030106030303050618071b060b0a08060711030a0212030415090516 69
    0xa008034055041590083c0c1400c07000c0d100014000c2c40d95414069070082403c1c01d840d10f00c5180241c40302c0020000303025172003843c81d9080c180b2048065103e1482110031241a0106285c01000c072140c40040e03400001c012030100342483c000d4260800a030107810714a15049800c041040000300c050710082000c40c1500041294034090b2030b524942020320b8500151010005074010416810f1b10b040030240b81e03136100d0000e00c03c43d000e5001046002589802000a0b01c0f0410203648103101603042c444117890401d021406806038600390504228481c0f0001c00c0c0d5902510440e0000350300a0000d21046440e0304002c1c000e4841610384c0c901400c52840024640660011072601584d00b581c0c842d40b421350203545e55070240034046002d030b400035510465560076680e9614542c0082c00403c02a01d9a4549840043c001c40612040407401d0340041200c1e0451581c04600802d95601143c109510390721941401c526481c0f04a919520382c0d442d005140c402d11400003429181c4001c0021605941354035012900b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 663034640 1250 663033390 663033401
    0x9090f05042f0f03010b030703051c03021e0a0c0819081e0105090c1303050f0106060207060e1c080c0604110612062403010b030106090b2508090a080f10 67
    0x402c200707a11018540741d1881c111203150a41c110050000c2095204040000c1c20300240798001c0392943e000e0701c0008940070302e1440d1b140e40611541411810640d409184200300c80b4051922003e4120008044044c203005001032030041d41c00040c016100d18200703140780c2c1c1d56402c50308400007003543c50b00001c011001c02c2050540392500c0c1d006012a503440d00c81406000803001c1c00c0303600d21000902000f5408600b20b05080000c4d40190300400b00d03811003802913421074242d80c1103e011900082018020181c124114039614482a0b8030035100c801c104c03400c056050716805000305030480020b1455001c0800290300c0c1d0099024407001803440086104100719031044407480d500120220000561620380300d410058907201455542c411088200f4451220f84c0c8244c010700080c0c08007200502c04154007080d4003000d020f2281160b40b40c11a01c0e40d45284090505c030881c50b40c0c14070400d040b0108031006090303400c4500c010344980740583d265000355844a007040924040f522454820051003030f51400f40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 663035890 1250 663034640 663034703
    0x303180e13150b0301090c031e0804140f060403060207060c09120605130209010303081803041d0402030c06190809010b1008072c0111010c0207060f09090f0504 70
    0xc08030342a101d0b9110007544542d0704000c031156940714007003502d43d10280990740c0e00d10f1162a40f20354107030441c9800e0043e051010030781d6601181401031000000c0c031460446007683c61260f0100750a0b45024006103564281010090704284003140000402c003194001d0440c803441400c00b4000440010320803a010340d90b62040d407035a00760035071040020445580c440341c2c00104280c80700808203295000716540c18400e900441c0000c8421081103444841354250000e100b0450300070714503162034a601580e400c0205504e04d840c1d0007103400450304569003003106003041140079000984420703231807800c505c0b1102d1600800f40450301740d0000030b010f1501032082c1c1c0200784008210a04200d20950200e50101c0014044030902c01c010b1a5000f010049042843c01f80c072602050050068210f40010004e00d040141c080c116030504090002c0540c000c1180000c0d500c1903d041c001407602c85508691003011907000f000780381c1c03428004203112445070704110701c6140507102e84008071946400c90501c1103040b955 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 663037140 1250 663035890 663035911
    0x3150509030414010c06051017011a221b09080a05030d020a14040b0d0c030213060503062716020f06010e0c0909070e03010f06030f060e0312010303180e 67
    0x3081c00442803840c0200b101c43c006141c201040744203996440121001500d04100c40407005004010310210a012100c80b11408802400420094003901648401e00000c1d607101e5010203407800c601c03d1510b211546060803c0805001d81910f07402000c01c450b8410070210001000e41d60041500311300043c1301001a6880401180303041c02102240c802500801c03c010100000c90004c184241c1410010f00080c100d02e035491581c440c040780d0a101100c02c2c0100e03100030b142c01807240703a0344c2050040c6004211100740c100b0070b44e02e03654603000030f031800c2140c0804070241505c82c48110007aa046212548910125041c0305808a0b40900599a503480d0b080303201c40c246d00010051011480c0c05c04001d8114200740c40301130500c2381c803200089612174221000e00c001102c4603000b001d249402d0141500740c2203a100c04104540c00c545642c1c00d2056401406030001d600c40640c496055010004c4402c0b0303521802d00601603507101c0c98003c14040d140da034640c405c001c040d9404904158442c1455002c1c2100b00d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 663038390 1250 663037140 663037147
    0x5072a02030307120315030305131d060f03160303020705180c04210212030d0b090717060a0e011e060906050409090f020303131e210c0506040f0315050903 68
    0x54480f490720144e441808205038a0399513a00d1084850b44400c0050740c401d4440d951039141d1940b142088000e10360000c0300028031184110501c4000c4001140c009000360b071445031804c080800700745403501c1c5164a0b243c1c00741c8008000181039011405405403441190401041404407159844600d8299812220380c0410802000a0036403007400c0c260030100d0703464100a00295030000b4407002c4e40d030001040184c2000420801070f8103603104807900800121049016400d01a10051240240d400300510304900d0350007052042d550b9111100c01004055408060356840342e400302540351882d4149107040c0201c100c04070700c16019040314026240c02d6542c0e5400c251504213840064100b1480550704009403809402c00742c0c034140000c0c0080300c0c14403c0c2284552509841c0c508041c041c000400440c02034138418042c02c10191920307a010071242d18090a0483c260401000c0700311264042c0d40d20410000f000207041841c6071032078003200d000d10044031042c040200d01c24166002292300c0002a0000c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 663039640 1250 663038390 663038393
    0x5060301090b090a2a0e1807030c020a03120c030b090106021509030301030b0f0711010c0302031e0f04110307170606041b020a0318090504050703060b031204030204020307030f05072a02030307 84
    0x1608208524219494082c82010303208004c507a0071f00c3d80c28001c01d4030b030801504214040b03400d0b01a1800401080c8000d144403031060320000c2c0100c004281c11700813107840e03c1220151070310030303084801501d00007005e10780d003940d44600c060350700c8800240030403075504450b000481074030011055074100c90300100c00c0030035603460035061340807038200610310030600240110404000d5024410140308490b143c030b00503520700700000141e80c038004e1088203850058403241000000b81030200940d42080e4050850414210b014000070305141c3d00c1e41180200354000805d151441c6c3c2c0000710540580d0302510100f000450b407445002c051070009140342c0c003503407104882000007807194051341c5416040708140005140c071035100805907003055400f0703601036005030300620a000451003548000c51040b0020001c48405501c01d00c0140a070b840041d2080c1c0d400310005400ba030007508101d18090100c0410441b502c1c6c2104042d0080f03550500180d824045c0b942c0c0301072141c8102c1508410250018010b5051001c1d030f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 663040890 1250 663039640 663039701
    0xb120601140c01050a09210207140f0312040320090f0603010641031e03070c03030c0b060f0612060a2c0f04030512060a05060301090b090a 61
    0x107603900807801060401c00d401541c4820b01c242406281281070105003031100d402e1120b2816045105000c0f032144080c0b01f41e805540000381c034402c442001c04825400266000011858014900d03e107800d4014020814407403015440200f054901c122031201c044c220401a055201140000031034001c81c40750007080c4d511198980d01c681c06000103002180071522009060b00220b881d2044102c401d0020201c00c0072140262802d070021f84400e503081c22000e082c0d4000030760f15101e10505200e20314a1403440800094188122000281c00800f81180590340c1d150080c0059041201542c0030350303003c0040390301c5140c0f511134408182c0008003500e00f40f82901c0da001c0e400d10005040c080e84130819040003d600300700110390000900d18142c030f20000003c003040d1100000401040c0c0015103403000208000207800109441c081586018502030303940e10070010665292543d00702e070b540070902000010301070409412040c0001e4040e178041610f51a5041d83c1d4098075111803035064185c082d1660140c0d90642d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 663042140 1250 663040890 663040907
    0xa080708030a0f0f09140c0d030507030c05010c0c05100605031f09061a031603050a200a0b0a0f020303040b060d0f0b0408190503060a090218060f070501060b120601 72
    0xb055040051039014245000080394110a007000ca140d4890901006116021010000c0054040c000e820312101640003c0c10444403000c0c02818050040307580c03c14940f140d210441c1141d800130082001403040715020309041d0315904100e89071701c60564104044070040c000c2d5070894002400405d54100d4042812981c8030080f01d04000076a5582c00c4000414024040c3c020104184503021380355515420606040200c19082d90010074204072003000001c0c400141c29244580000c012800100740c068040c00d110001c400711544561040d2000c0703200312410000b00191080bd44030858990b06004060340c69000485000c3c1440821000107003a031308101c080d07001d8007840b84c440245200d501e942c45030824801a00c080d5001480825044103814280b04440c0701c010850030300a086240420025031212501c1c00303002196500801ca03c002c0008005507550310a0300103007034545441142d0242d41242c2c11140701a5000d60130640d000500281c1d01044030080c0c2c501c8030341808145d0320750f00151130304036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 663043390 1250 663042140 663042151
    0x1406240d050706111516080619060c0602040e090616021b0d1115041d130201110c0d08030415020403030507080306180f0702010f0b0d020108190903110d020a08070803 73
    0xba8106601440c00c543c400b240c422280485c06406c4c5591001000301168801044e15024000750114000c0580c1e43c0c5040c00f04847d0a4605142030030440c0c81c009010b030180340e1007003130051809014811501c1c4081800d9200f540d0f0a21281804410700100300d90380c0c041d44a51360b00420b03030a1802d0405091040000810b43e0140c0502c00b90010740e940481c0060724001034500c00d192000c40d0a004044c0600c02c1e40c180b28504104504650901c8810188101244a8000e05220504d984007003820010700403040c0759800144100541101d901300041c817075004076411a0314188000341903401c4c140e00d00c01d8a09681e09035070741d107082038550f644010700b551000c0d1003e584022899001c510b200000c5840c10f1061034400c0c40400c0908140d140682540c5810310250540c50a207030701080c540e100e0281080c01650240380c816800c0d110040c0c2d5022003002e0682e0000c0e018102410441415004804800b6100d2900112120080c100c0c408985440e00b0200041c0398102c1008210040340d140c2002d1500300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 663044640 1250 663043390 663043393
    0x91113021e031806091006090621050f01050c0a080a0c0503190f0c0f02010b0108010e0a0b0f060a05030405120906032e17010b0103020405100c1406240d05070611 71
    0x20780c0f004580780070801c5071140200c0d4081e640b0080703985203900950000b0b20109405101c42c9081c40b446501a0801d00102ca0480d52804184020310108100c00e8440300440002006141407801e01c2d24a50b41c80780c01c074480460042008100c07092120301ca52001000103030340303460440e1141281c00007402511610701c00720544405549030703085202d03c2001806445600d900c1910480424040d0035106540101414400000300401032104d0407007403998404da6130300d4001842c840039000111030324001400c294022402103240b82185400400950049024201704c40e4409145062103001c0d00c204601150015028404a01224034040e84070704000100c284491103132141d50504c488a0301d80703078028026a01400c00c051b282c00003c0c810842201820b02c0d0a500e405d08003c04120250305038041d50b02000040900101070042d40846140c6c095844000d82e00581400c2000501e4012550700300c0c0400510b00c0c0c003400482c50000c480c41d403c6175000010b032114624203402961440038080401c4080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 663045890 1250 663044640 663044671
    0x160305041a0f06010f0e0d021219080702180705070615080f1c0302070f08030a110403060606020d03020a0c0308100506070302010e06010506040f031104020d091113021e03 75
    0x1009507480128840c0c000000048664682000010800c00740701c0d000d0b00600c00d4030900120305440e4041e091402640643e1203c07600541c6510440c60204141e01c00403660441014407030401081c4c50082524034003c64845009041d0340102503903124041c1c1d29100820020000040000e0603a00054080f80d81c9000303195405030f1f00c410aa090100b40c6d4115055a084260170b400d603100441f14410003800c40d49401c5050642075600c60b800008039400142c03220601000040249007907030450310304004000c1c0c0158445961b03107803a0000d00014014203025015205914006a00c00d20a44412540e940d80c1d4190107103980d14180c90340d130409007a82c80c801c180300901003181d8071504000e12810703109a00015240a01d65070b81420190306030001b40c0b04020412041091a0002400506480e0001c80c407841071844d2200241c02803241d00401c020b482d0600030580148200c1c4915629555030075601c9808816000c0042c100701d02c508003031410018040210100c0010404002d550712403800b0910b02030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 663047140 1250 663045890 663045923
    0xb18060f04080a0507090506060a030906270506010503012d060b0f12250516021003090302010510030206030a020a020f031209070b04030803070503070c140303060f0916030504 77
    0x180341c0c40707604228400d0340000b850b88200941081240010240d0b0041004a800c0000004080b84a044030f5803080684485a003000d10589611107081d030f0442400399000c28084414a00840da0030310810355a5010b0007000240c10306043c080da68210003207650b4440e40391290001540204405d03c06580082c3c0e85140101d07560441c180100200380005140340e4852000140c178148880700240030710400200d150703296175401c4002091901400c20340c00e2a540b5071038203c1c54007a582c5400000a944900520400403026805910901d6082d02039030080c807030356440c00d0380e42e8420300141c07100035040b42081000817450451a40508280c0300c5a1060711074003c8900b404501e990055582c040603904c2802c144022080100b04090040403c88102c60038503145031100c0d01280002000724040c0500000000c0c1d80f41c1c07141001d400310700e40c496003d0f403044c2c02d4049001e90ba42c0089035041d010b010380c44100710952a0401d0060300c00c03440500030780d00300c1203020811009804007820403105041000f440c1c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 663048390 1250 663047140 663047167
    0x20a0507020310151d0609042108150915060a0314010306060e060319020d0c03082101061403040609021503070c11120d20030409020c070503070b1806 66
    0x5a0750905107400f040380c1340414004518900254022040210f007211031851500b00c0368500356100c0001c49500f01c9a903128188091440d442c811500039006060040d103842c0c1e80c21121700742c024415000440416081d40c0f0500607030002c19941c0d216081080010840640342940c0100002402d919011030b48882c22004046c8000082e0800c50b43c19403120424850344190309625640008114001c101c02e0158901c003010301c10480c000079024009401001003031128001001c0e008591000c00e06a4a4030407050405044c10049004c0300c08440705400001c015100f00004071210b60000030141c95911035135601c8000b0140340380100c0e04090540102ca0455a900002e1031240c040398850300d8441500d4600f10303a520741d010060340d1091006002c01116000001000c80298506003490304a0502890b02c505c80071580c6180c9205078400007601194040d45034006e403404420800c01c4030b0760591154101034603804a0f025212651409102c1103850b00810321040c020103001a108501d05a024072504 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 663049640 1250 663048390 663048403
    0x30516021e071a0702030c03010b0604090506150c0c040b0307052211041212140403030c0510180203070b07050c061803101d010e0712033606031e020a05070203 70
    0x10f2542a80220b06281075060921a00b924806c003100200300b00c0d0303039040004400d03001e14024002110341e241c1c00582907480c2d146078419111801f030041c40d103c62040040c03940c0e8245600000e40101d0a01d1503007015400c000035490250741d0010221030305a04500c0350038458801000500100c948c40382a0f08810300d1309070700100050a29000c102c2910040d905184054030004140c81c401c06c101160440204401d0300252001d403503152034800c1000c1080e0514604d05001802d2085c0b84502d82141861007150444141d402540300707400ba60701c0c85550310800f2855029040340131785142c2103c29502d00910303200c0c0091411030708081e4416601940310000c00d14110001411100343c550328800700343d8001080a1740401d60446500a000d18031801c13070190b0712100d00e8412400507203100d9122400701401a44041080401011001d030581050b140703441b144840c030820b604641c0e42070080030070b00c6d910038080ca07800082d0618949c03800000090000c0b00961290039410f003000428461480140d9050158 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 663050890 1250 663049640 663049679
    0x9020a120c0f080d050a2609010509010c1d01030b1306061218020a05010509060c060a020315030f0714150307031d0d1403091f0c030516021e07 63
    0x10780d40c01801c282c0040e80d2405107070040542c0e680b200c1802c2d0138181d80401118540340041c41c0521041318090440900c04002190a0b440401c9044c100300c0c5490055000610502f8128000c0c422991043c8080e03510103074041d00050502c03410b41c04403c855009070015805588041c11412100da981c404032000c442c0c00742c0048000800c140020015255640078000203903a4205c1b0345030b075048441d80003411011a501c103242c1401800b0420581036500d1809850b180c00c01075059030424609200420025441103684d502913100201d400c0c4e10904000490f02161050380380101002030030300040c0010b03034403080300c0a68402c0d008050ba844114440c0c001d1070144400e51000316071591f11960180b088060607440d90285d901840168141961141c101d1034401e0741e042a40b80c0d6074441010312410b200503007001503244441341502100f0340715141c1c012030ad0b0001c035035010019515421502c074090400907669000591040e6002511000107902d6191003130451021201e95690f03510314822a50201d100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 663052140 1250 663050890 663050903
    0x3080f1b1b0a0e060d121407030305041a04121119050c130c120b031509060118020a08070f020a3810060c030306030b2d0402060d09020a12 61
    0x1040c1c0c4500300041c02c0000360a0b064041180d914011010880c1c040341c509004d4528400c141c0001d4071360340a68103e00c4500c004a294039525029400d000e0050901550200d4034219040300200c00c3c15020126580140e50244012040418031801240c0d81c40b0007401c04012070080721025070b6810540c9a0426506116402034008403000e2020008050301c4401500d0103e42481001c121803603024444116845100c800001d8142900c40400d00c0c140d04d440040b0b0f00000b0500610070a0100014040d041314124501c4c2d00c23041160310500401e9028210000001c244143d000c603c060b405085410904843c0d803046031180840740d200c039454040c0d1410744220007010395001405400c080500541500c0c0000c41c00b810b68240380301d5002c40f41e41a4030135602002010024041054429000800115085842c680c020b0800301501100d00d42610740c254280b402c02082041c4510940819500c2142c000300004d0030800c4400405000e03043c0400203d030300c207040d0702d03006c2820b6548052a400b040c1c024407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 663053390 1250 663052140 663052183
    0x2e1803330603140c181308070b0a0203090f150a0b1c03091802122a040e100501081302011803050601081501060908030f0a050405041a03070f03080f1b 66
    0x5050070f040c400180e6807a4014907140f0031a40c5c1d12480300c116107030403a1105000c40c40464480c1401c10180c00741d4480101030f814007034180700c522003058000c0c5024030240e0080e1030060030f1481030a41d0b1040740102005c520180e00001078101d1503541c2c05840c04950285c00c011100c80b4405007010502c100580c1100840d254140a0020400342402c0d665010030901c0110300d001c00da140c060103000340040c0000d400c44584c0490100c0c240c024060075500340c01c180c0055031a00c1d01d81c0810026508100d034160103c3e1481c9070000b07050340c40b88101c00c0c095520310f025801003840540045418465040100703660181c00710000000440410145000705040000341201d4094401851f28a10741039001e1804c00034070190030702c40858040300f200d2401400340511591020b840c002070302c25001d03e0340301a0307101d454110003550094400840200030032088041e54000c5844124002800c0320a010141c1000d606001143e50303120f807080140140390b4079070104100031500c05665450803404844a44c1c840c0c4140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 663054640 1250 663053390 663053423
    0x7030903060507030204050f0f06070506011508070f12150b160b010e070215040f0c03081b0708070314120703090e060109030b040f022e1803330603 65
    0x28031070b0540180d03e500c0c00b0751805103000001990313105442c1d1910720840026809000300d40e180800c981c411740e4018156100c1d90303900c048051410f285008044003043c5208002000e0134410106115484459101c0030342041d844550a002884544442501d54600e1603011440000200240c0502c100c0c0000c00c129084c1c451034035116148060340200411410707a8244041190003042007480180760401045660b5203501b000355200403025070151008803180340100500005800074000c0440ba8040b10040c4100d4402099841e9014031074100b4540241c981400000d49808500a881c02c2c55401c817002d00d6041c400c0ca44043d40003c00031004540c004001300310700303e0428540c0b03a00c07203000d0811480e4646151201194050001d000800000d8402503840c11550f41c14020802c070170750350203030038803e800c0104006074001708180040b021444464041800c44101e00c0605c06030b130303401030100b00140703102c22781240c036103951440c2411982c0e440d6079400b081441c948144002507004002e1100e0304000e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 663055890 1250 663054640 663054653
    0x240a0504020c1f020403020d0f0f021c060b030f1b13060f0609060305070f11011d06061206061818120d0e010b1509032d1216170d0207030903 62
    0x154030041d280c460044c042040036035074190300500c2030740d000841c402c0c1000483c038000c1d13106c05804c41d00079440cc5c58040c01740000c0131044d803008081c07445410b04002461040781015039909203142a84429440920f060b4040d03044c803c0401c2a01b14003401c0345c1d01034040544840c041e10340ca60890250440a1002003250540c0161850f0081c840380c00c003001541406940207040d001020400001c2c415401c5940083d0042544042200e0551440307070b4408051451480703480342e07000d40b034580c4902810480700c3c04040002c44e2590140340020000343e40c24101c0c080c6c0c880016002004d003450000c007480f5292038110240512003003030b00d00149075035491a15407000c400300c1c1c407448017040090380740c5411961144c4072145131044110306c401c44143c480034080d0010b03190540108201041000e5220418400c0b1040070fa40e41d9072442d40c0702910001c0c640c1c4001e0b070840c0e0140d0301ba01c070034800c10720510300c0204025403060a600c0084000d0246070020324440e42c0141e034003955088001440b07248080041c03040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 663057140 1250 663055890 663055933
    0x6180906061207030203060d060c080609060612060d230a02010201110f03042604060507050105070e01050d02132103020d09060e0613030b01270203240a0504020c 71
    0x14100c411a06001915110200c0c07484000c0043c0c007816400404a402941c502d03100c4550036510480901101e2048240108120310a5171081c2c0103024000c040745440c98101c0944620550036800d41071584d072400d0801440050102098603c401c1c1300082104401488001d04050b8140c0002040c0e1040d03548002400c4400000c240400a64140001c076070814032842245d82081d000182100e601c40c0408940c1d91000068203a0417446200090000701c00350054098420305004400030440b942d6444c1041c0c41c100d0340101518000399040008400005031580a0200408080a550360702512a00303100140d4841c01401901c0c5031805a444041540c10000312800c602c1528210275158541b072805000ca20503c03017290b00c113035000b00700c00700c003c40c40f040e00c0b02c01160420014099940c1d200e011505500c41c003941100c040b1058080092030010f240202c034040c400c0d254200614203a95145010001c83c03180129a10109400b0001401c0da614000352500c2910342020b04251540709058490201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 663058390 1250 663057140 663057151
    0x2061501020304150e0103060b0c07090b030f06061504091d1b210c1c0507060f140a121b0f0206010315021b0f06010e01060503040203120c0c061809 65
    0x14070803c02070003040420f22121000340c08a0614501d04141080182c001c0e184a030488c0040c8440481c0303c541400c00000e640c400c5952140080000122000506072a0040084401800d600c1180400c1460074000121214071080d2008036003083c0c1c540b518002038079680494040340915240701003108003000d100020001c07901c144482c40b0004139902054040280c440d800c035000303070701c40b0201307041c0320052007030410f2070b10001c10030090308514008042001144203000e80e0f4034031418001080d050b000e01058100e0040c29150423080080200d4001501d50010001e20200103030307204545086c862034065200e8003003041d082048100d1180300b0041150709000980402c42d8440401080480d11541d00380f40c050412540c0541d5400d059611110b9913078507000040d42510452003515441c0e0008102a4142c1d0740000350b1075039699071400220340c1404181c0e03000c0d5140c2c000d00801c02c40c0604400003030030900d490a0949038481c0724840014215001006140c010400701d078072040445c50203588050740203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 663059640 1250 663058390 663058393
    0x1509391c02040e160e0106080c0310150c0f0b0a0b03030f090f0103090203120408100c020d0c03030b060705060f01060507121103040902041e06020d0e011202190206150102 75
    0x848540300e140321059850080a40125541c9041030b0241e02d00f8004a240050140000b042850b07551024000040c401d100d82c40000c1c00d102c020640400007042281e000348150241002d527141410043d04041108000036000d00a03108240da0002c0d00380194030715000d0148444948034504a580c1740191040481400e00c00d800030020076203d0344c0800c0c162110000196000244100400c2c01038000303144e28540a541841203191440250300500001d10a50745218190b80c0c5003a50f00e0326070070a85484c0404c5030091307007202840d681000c0c0f082a0b0102c003540245000f0455219074000304000c0d9100282c00e035075540101c400c01050304510301406006142926009140083d15121484403081c68155035003007200360020f0304040c1400704291806442c1c0d03847c00b1583e80303540c0c031001d040402c4520040c69412141810000e806030002c203400c039410300c641c1c031000c40c10304903d001100c160406c261a241d88075030900c02081032480700c40648442101c04c1c0c008042909101984010790405010b03a035045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 663060890 1250 663059640 663059659
    0x30111090a0603091b03121e09030f0c05061801112103090708060f060f0f130b0d120e0316030c0504020901050c0a0308011511150939 59
    0x76100d00740c454003240e07818036000440250900d0f0401c059140e061034100e1101c2d0484012080c002c0044060340c1101c40364440345040c84082214250207000b1105c0d0760701060405a0403c0480e403c4003118841301e115559418100d52a1070002d816a04862421100340d20b140d044c501f400e503005501750704e00810200c002d102400310403c5208180700c03d1101a0943d900100c045080c2c02000c0013038102909501065031100d207001c4480b0300c5100f0003195298801c0c1c5d40031400b10074906111428441c00d22010780b54003640f29034148203001a101005209422104050030f01002c03902c0d88c80e00c1d0383c07030707020030b503540701c900d8644208040c03030290540401c1c0c0710030236142030800024102c6500e4404451040d030380907858180c0900140c906004035041e000041c020301d010310007010fa0100382c00b07068807071000104401d85410703c01241d03501101020000d56600c0100d030811800340c11018168040c0c4500c044800b50035003008508282d183c44d0380e000e012400440100ca000c005e042d010075650500c1510b04050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 663062140 1250 663060890 663060907
    0xb041d010503030409094418040506010207170d091e03061e020c0706080915041103330c16170c0a11040b0a06020a030f1715030111 58
    0x461307100d18400d01440940d10541007080040e50784802200c0304c0000780322604078848138900c104c03880318094882181d031010418007001114130342c190b900a4000c02d07c1641c040078070a05003c0102000b410580c10340c46a03480c00160032081c03908424111010300b01408100c183d180000c1c12002040d00035940445110040f1a15181008100d00449806c607501040c008038000d440300c18020001c0c00c2c5c07a1054000960076041000010318241200c00a98070440b440d03a81e80001501c440462161001c1000c203000840c01084841e050312449620040039101a0040b215000d014089400fa201d04910042411100c01403410040d0503030003c0300d030306800d24003a1854031010780b05038a21402000151081114800b504922b005c0d00c2101a2a400316251510141002480c000d48552114821410050707407080506003034420ba42284c1d4590003c207511111640d0a0716440c03807030840d80d010001081d500a44030100e811000740900d01c3c1031168110b081040c0c0515081d00c41900d801c980002c0100100b14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 663063390 1250 663062140 663062143
    0x11e0e03030403110f0f0c0a090c35070509031204120f05010605091e161707020106150e0405010906080303010e13052b0f052704050702072102060304020f01050d05010b041d010503 79
    0x80e010580d1003001031f00419071808141041e00358171211860b0200c041033070250700301c00200500034084003101c00075a403031501c412091145008000f080c458005141c00080c000301c01e038030000b6100c5d50000c0745142d02c0b24040380d00404115048955000d110003106030100c020040d80e50060b0000440300c0480c181403201a003581400c005c03410340381210000142055100394007000140c4000c180c00c10f42a00c858100030b10103082d032132013607108601e00000020f60721094403c4108941c80380c0c001c0c1d0b0551b80380071303502060100c009143d034000309030740302030600002d00c140a00004d07003504011410f00c0342e00b2081c00305040518802420280100e504981141c0c6411200313070346d00380f00e4001529071400160204103654407052a41c0c55041424034040c003c20607008030740074054400324007841040c0c1103440d843c41c0d62400e5400019400c02d400300b000c500903080c90742c10341100b202c06050482c60542e82c1c1401c00100d54090340690000540460306204541082094604c01d42c10307100904229414240000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 663064640 1250 663063390 663063407
    0x30c040e01231018060201061d16030203040203150112031101020901080a05070c0c0305010506010807051222050a0c080609010902091515030702011e0e03030403110f0f0c0a090c 78
    0x902c07840c3c1041d8416405071140e41055104407000480410490b580c0d40b010380a080140260001140200e08404c48040e00c41c030058810502c030000081b032680c4c0040d09800a61001c4c1040e40c15015454600400369600780030306000b401e540f02c0342100128103040c014400c14600402142c0c40c0d00400c600002c6a900c5182d09800103101d45001400303441d000800e8413440e00c010710081c107040008500005214040d80a00d03c54082a200d09170f5550350b00004880d80e03c2040c0501c10f130100c0382408070f00965100101d1080b4a5410000c1c81100740460302d80318034015507084220780103403034594140301e541c0c0c050100701d400929103002070001c0851a40000e0000c000204901b07108142c8428820740e0759a0740c011456203d070660a101e699040100000b400f8100440046881300d00030244880d4900140c4540008200700c1d00185045480d1654111008640916502c90710f109104000041070824050680035265500040c841a508401070000e8800d4035449403060516020000751901d030030043c0e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 663065890 1250 663064640 663064709
    0x5091507050c010f27081207020414070f051e0c0a150b1c05010219110f1b011d09071d0406050d030f0203070506010f091406011409060906030c040e01 66
    0x2160081740441940446040316441030a45225114021b41401003000c014503469000f900c043c40706608104030841200000e48518001070144403c1c140b01c1d903c220003504040c0c07044450ba044002070124010080c5d00188100c1500707401c005c0004082095200040c5462005200d0074440440228001500404440f00f0b802c07a14035120b0843d07003001002e40c11201c1000740c1419940341e0301108400106004804500a10070348a40078400003d1400011000c0700358130f10695020300048007200444400c803240100c010140352000c3c590107503070745a4405d20300c105140d5803110311b5003108110711035103680040480741c011440c1000600c03140d1500380071344100343e80506103564401c1c4130b02803c81c5180300d1014081c201d4002c0c1c90000c68001411003881c4100d81c41000288414014622030380716468095940b6030124000b0482070303031070794019005821092802441c2c0c6040400950100d1041c0d88100e03550f120001c6e0005007400003c4240c4515405007001304009011007502c20a00525a03c08100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 663067140 1250 663065890 663065927
    0x316050402130f08010b01110c0d2405010608091006080304030807080f030a0f050901022803060803030a09050d171b0c01020d05040618030203040b030705091507050c010f 75
    0x108204004900e1841c90010601420035558603a0366513065802001d03881c001a001828050b4407608020000501c1e8002001c0140607503c041d00903610a840c00c1d103d00f661485100050b1080120b2035031500c545802800d09444185007868007010740c07810404180500c0b055585420010b1001010000640b0252580800044d0388e42003181890780d0280120f00b009071902c000002042004441034003d07803568200c011092110f40c449aa10509074050300d100f92115a00044c442100a500340d004c51101c030b1803506000640c070340c980141e20708560040341c0481d00c1c1911000301d8020404100b0150617080c102c1c1c60002000c40215024900a240140600d204140314444461407821000111a14800724070f0003150740390040c41c0c5200242c58100e9040d1103441c58220400340e641002c0c0e000481180e4540d000e0361915041401200c2e80350009044c04041000c1841000016100d82c413a5452000e2448000ca407141107916100340f0b40051a000c203410019440d03610340903e50004c5c4020420028a413 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 663068390 1250 663067140 663067147
    0x2c0f0601032d0b01050715140109060305030d05070302090d0b10050a03030f0e040b040c020d182106020408010608070312020d0801050f0d060f02120a050114090a0603080d050f060316050402 83
    0x200485c3d05000d1300794041c1070b40d107900c80f03c0101000e451748422044080c0710078060413031707a071900350208850031f912014240c0d4008205000b00302003594000c0e5840b261b903040060400b0540e901060742d04440440031142c045285003072080110403100c3d03407002403d00300c0b1034025050650350000c2440c00c90840701c8040c460b00712500d508a50312500003204810020340200028a1040002559110822506400f0841d040000400c0c95001c107040c105580e42e0003000f104401c00003461206c81710f905402561303500e90902c00030030b03490b200307028180080103060001e000b9a403e5041204443c020034003102e0540d80220300c0e010040380c00901c0b00d0704642c0b040310301d515284032210104003045d042c01c400030002c45c6001401c08615200d940507000d6800740c01c564414a9490800740401c40da803e0180c040c0401e00d00e10090080d14103040740560026030707030740c0c0405c01c00e60303c7c1d40b00c03499500590124038015403901c00b0400800251900c06910540460060404400742004811407031500d028042c021038000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 663069640 1250 663068390 663068411
    0x906080702070306110405092a0703092301140301050f0d022701090b0d08071106070611030708060301051504110c07090905150c042c0f0601032d 64
    0x1d1080300d0045070401d01c2841640c001740700d0b0134050f81c01402400d11441c8000007040c8d901407501ca80b0210300416a1000f40181c400049810f000e401c070803803c41c100400c000d000315010280c202200448440301d0b42607030042c0944000506000c803483c004058842c070601c010041503480703440503180311005551195821106002041c000755007104803043c0c1419100a500501e00b100001c01d040b100d072001d08100008200c0e08000505000380400b503d48003081c060b410108043c140721050b801e600800741841c083c07207540c45501317071402d4a8900510b16404420001d4150700030b0049a0b001030214000c011600d070010302c2c160011707030840c4080c0c00b8941e00e080c0044030703409601c1120070441c030100440c2c209994448020018205c2510100d0303250195502202d9886a038000c814020788400c01d0b07550816007403405d000c2109041c21400342c0144442010a01084a2060b00a000380d950145020712454800c00160a840300044048800601305100b8282c6041c5880038850110b8130380404110304030311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 663070890 1250 663069640 663069643
    0x20090f0d1a01080d09030b1821071518060f0204170a05120310090b0a05090a05250507020105090a0506030c0c011401051c03090e090703031e0906080702 67
    0x40080c0185880d004040107a110305042900c203040b94100011944070501c01d80040300d01c0c40d03180c40010080c90151010940030f048014200426110103012038141072000c2c0400d41200041950194540c04002454800e01821003501c19240005800500c48610060040c040640e0b8201d400742405e661026091500551501124010070005440700303501c00c1c3c000b5540c2c0d200c604428080311680710b224209034411071f189007620f1088140608c400c1405141000510140c40103404040c2d00c8006504085007a66031000c0b158020506d03200c00254134508810000c010301c00d0300023166000284401c22032001c40d440004c03a807a1580c203107440381c0ca4800c8103011a52048050b0080c83d03104101004100707680030500040c1404001040080c80350300c1441c000b80d10380503028024a07030001e030000514110104d070002205100341c400c0c50200079481d80c4502511102d80266540900f94018a00c00c005056125100314180d1078080311003019280303c00d030f0240180c04144100d8051011754000220710a00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 663072140 1250 663070890 663070909
    0x51c031701060f0305220f03030227011704110f120604060b090f010e0f07050c0d051809060603060d1e050105010e0c1c240807060320090f 61
    0xc103036800a209503100d800261802c5100d04060000a1600300050300c5a8940e0201904422600b041450039075400c0c2c5600130880f14415054003070540820440c902d052410b0010991003101c01e41c42e00c848803859000501070790300032a60101c03c2040d1420302010990b141400400c0203012a01404051440c40c0030800301c80b921000c242c030380d0040008110901030340d60045c000241c000c8031004c10340d644001c92285170040c28020152400c07090000960602e1011000603080f1495040113801c1008130706140740303054a031300f5203400003800c00324021044603403580c4015901d900032903a10801d8505040807071814080100f95a04c40c035010080c09050100e0300c0e03114081c09115400421800d02682080c6000c0c11080c4101c0c8600c18040d00013230380e0b41c50722400303449080c3c045c13125441d151818a00110041c10070315506042c0b1107a01e21003044c00d4400d150001004240724005080007900e4a040901101c00411200d80b400710024004080804102c00300c840d00281103446c803c000c0000008070303a180d01e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663073390 1250 663072140 663072167
    0xe070e07120608070f08030406020d0f050403050d21020901050f09180109060f0e0f060f0a0510090e010b030903040905190f051b0c070501081503120c100204051c03 72
    0xb8a00000400c0500c4045400c0c0240c0c4c020140b00b00440d42d403031800c19601c1c480c038400e00006070806070002d02c12511440d9010344a03201c0746816824141c60382c80d22030811440e0740c4d2100c0403419164800600c030100100680c65010b0503142142048a49000a0f10350704c02c50a6040c0b42d1200000e2154141d41c800c80a10042442807400901c1c568407000340000800c114000d0306070b8400000c50019144094484481c894001e02e101032481741c540c8400c5c0b0900300c04036640654042500302d808552622042d0b001000c0541903581c510260b4a8101a11034001c2c060308040501a41002000381c6080000700b04ca04440004100003010355031040f4800386c2c10030710030b88001858100391031040c10030b6440d0041805614a001c00014149174120050440d200e161003c4030a500801e0041100e503016055450b40401c3e00b0700769080c03064030540024104010020881c1d0f14000202d0080302a2004000700c5080e1891140e04600d0541042d002928184051094008000d07000b12610704141c404c1c0321000211 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 663074640 1250 663073390 663073427
    0x140f060708011a09190e041403090607030e04110a120f0603050303040b19060306020a02161415041d1e060303030406020a0c1425030803010506210106020a030e01030e070e07 76
    0x240c3c9400c11b003008200180c80590f4480c203440b1810782c50507030110454400e8a00203100790f241c00c110740c0d01941c40802c61003580e58820b42d01c81c5900f4040118000915000300c2d2559500c4045a03d04998412110300550000c25540741c010306200040b000812290056003110800019075110401d04045445c4180e00c0c25003281045c1000017041260f801401d21f0f180c1d039070280c4000d42401e030328075450311982d88107401d00d200c00f48032550014200140c030384141da030300405a00c3c646601c40003100120107261060950700c2c0b0001003006000d11940045448059100c0241c0c00745051940000c0d03600d010140001d08100c0d40000d262503014083e40882da0308990281e6908680103040000c181c80301e0180d447d8219051200720300f8081707002c000300c0d18400d82e54000091030469081509010f515044000c00c040714071116444d80c6225195244c15900801c4d6a50040c0307200c0c112450000d18030303034403030000506240c1407001e16895048041102015148417035003881d00c07959004422200c04c519442a0280d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 663075890 1250 663074640 663074689
    0x1e060929060408010e070609080303070c031b1b05040b0904030c0b0a2717070503040e04030e090a0506101d1e04060b0301140a060f0516140f060708011a09 68
    0x5030380080390301c404440f5188ca40d40090b81d504c0e190103803644421104d140000344100c0b04940000e004081c106214200b0144188591850341c0d00d080a40361483d1030310000b21000f003010400c85c6000d01501e1600c103400c0d9101402404d2a9501034002069000b00825200351007001890480540c2e100310065011030441482020386524050b920f1400400b0588040d0422031884c0780200c015400c40e000b4550000045241c2031800c0c100400c07a220140c4201c2c02c02c051046160342640d64947c60030b0042c10340300e00020380c1c5d0900b8020005592421300e0100140580f131401001520815080f04015000a0f00c041101c42e91b44442450101141000c0507441494034102007038220350000514143c4444068001c00042543d00300441007116120710b90002d49135649011003103218001401008058080f10000c40c11107940c2e00c46031000d060600340c015800321000048410081002c5a000300860410b0041ca5050002400e11003920342400781003010300044c0480580c40e504009000362569440316141c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 663077140 1250 663075890 663075911
    0x50d050705010b090708060316210c2402010f050103030503010902131a040501090506030408071509020409060903080708010b03011401020f01060e1602010c0f0f0c02041e06092906040801 82
    0x100300303025140d03c1e010f07209414a00711200c50048500c410b071071704d000ac03095906500c05032038180e00d5821241107a100014540005103040d581034101a010803036144405900c00d0404001e0840d40d641240c003003001d0500d001040803d40000840e0305480c1d41c03540150b695424000e900c20840d0349580a840e4a901c1502c03800500b00405010780203a071403d81c3c51045081e0f17118100b2000c0e01060350b01410611b0104200000100001c40e565481d414020020030b0360b802d070707800003070440d400514207030b40e05030b01c44000504240e0301071141c540c4a1501e00700b010b80e550402802c280980414018140c0408012000412682c020030801744045840c0c4020f0190507241c01c42d000d4404000e460045c0d40e1030910185000d1140180685c500c03081140e0344400160b0a00f000c110307180c80c121603200c1d042c080074a8003d00540c40d18021000d06185428100410182405c40c00e000c81d0010b601c040c4226203070010b170b10ba0483c1c4a07040340c43c0300c1c10700e0040c0c5d400708103c0078009102449250f200d814250b10b0240d035820f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 663078390 1250 663077140 663077147
    0x901030219030e10060b0906031012030801140306070e090a110d020d06080f030304030315090207060e100e192307050301050c09031e12040902040f08010603050d050705010b0907 78
    0x1080e20f5902002d4070308800f503401d881030540e4001e0003100705001c400d00062107103007090009035600661000149104540d40c24000426402400c420b03070014149400500019074160850406450103800800040c501424010303d42403801403594400c0c1002e4003c5100e02c142900501c400c6041015650369814107420050029803212804048590400740c0004050b8000700d85d0f2a00c516490015514595407941d086009050402a800140404032000300d90641248041c0c120203100741c1c40082c2c94000b80c42c210b454022030311b402c600007034205440000d01110111b06140d0140c1c1225580d444024146018800f01541c501c03492141004032800c030100e80c40001c0e00e0011504190002c04c8661910f400740380e0306102c0d80c814180c06078400105450380300c03424802641c001c082c40007500c1d424103d40a018001c0d40c41a0b02550300b040d0003103000d11004000d00070140003010210020003456255a450541f139600b07866900301808030100701c00c0c0c04d20000303400c0340280501c010840b6519140050300079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 663079640 1250 663078390 663078401
    0x150e03040302030f120301090903050706020a02250b0418090206121005150403120c020319020108010f15111c030207110a0608180a05071202030f0c0a0308090103021903 74
    0x240e10030300c11844c0e42195841c011940c4030003001c3c9102c40300c0c5141e080c8009400900043e04084040110411013880414118406428a900154045c010030b20091645460011410000725030400303000d2400c0004106000482e4100da202010602408025070484001841000c20103034100702c0000d1090300600c07524103014402c0c0100c0e00701c62209902c2e4424020716a40d104210340128104100600225011754031307841c21030b5100d180c18440d001155001c0381c107004201c0c44685c50707004020007210456030003e4030180944045c0c0c0e40346c8101c0c0d01d025182d000e0100080c1c0400e05020011a145500030f03030610200a001000f9482c07078800c040d00501c002d00a500079002515034648154180f002880e08a41407400c903400e0740d4904056407508040300358071807443c5940126610030280100000b4000b40000e000405812a00541240050041c9820144800f22400d1560082c09200915035511400081602e41000503107451b01e14901c0143d00a00c00c0700d40c01406040c662940520307969168111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 663080890 1250 663079640 663079643
    0xf0f0c0219151205090c0d050c1305071403041109070504080105090c0406140a09020d09020315071b1a3102040e0c09040204020c01060b16050613031b150e030403 71
    0x389840d00032200f00b00e0f02180c005686a5500f40c0101e000386840e49400e403882e407040d501402c1501c1c0c00000c20380006100c4540118955121901c8004000781a50040c0c2c00b9500c40c00c0000b0041c0ca1407505540d10200c1e0030208010034401d0080c0d0002c41e0780180704500340c40103001c0c000c000b004a81800b02038543e507082c00c007003150700c43e9041841c08520545007050085040e900688154142402c011544019400c42000c41800071307a15051000542c2d0b0070816089001e00f035484102c10390a04000081510038101059040c0011203000400069400c00407a0b0a9112089105013a512900400034001e52186100345240c2c1034022100c0c2c20844004086007258030895003041094240e02c10f04e07880e08070f20103007141d0020700303500042c016040540081104031007a80c0002506a100c861745645038014868084e050003081c24a07104010b01004139580241032240d40c0c856403801690001d02020035141d48116001c803103000901084140742c882d90a000301c0840c10700c407a1000130072255498119100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 663082140 1250 663080890 663080897
    0x60a030e100f23070f050c010c090f0501080f010e06031c02150a050702071217030c0322020901090b0d120e180919051614040506010f0f0c021915 64
    0xd5107441c8a54061805007100b00c440540d400681c1e03100f0045c0d80a1203580d8095090001c01c01000180540c00c0c41104c1d200c181c0b90301c030f5201c280d04040c024400980c0540005041c4134424041c010742c3c0d00408611411110078004800c1c0f2541c42e0720100341400000e22000d00b5100344054144402a008110b400b280e40201020500c256104089001554030990310b03040540c201003c148010b84002c4040c15810340104c040301440c8109200c61509a4001c94611407a01000310501030035030299014848003440e031500e401100d9201d600083e0081c0410b200c3c102c10b640da0307141441c1e002d8641c21402810150010014222900001800f40201d450240e820f889190000d030003806440d442c0c004030f8014842d601c007c0032442d01c3e6007420b51540c0f20302c032410b0710340f03102d2880d05103041d038070703042d00000900046a11100c20340d103c00280001e890380135140034140246c203441c1040d5940c3c015410b40b034a100500d4400b0390804035001007010b0725032002094074003040f03c03032002c0741d24402c10505c0380382c1c1841540c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 663083390 1250 663082140 663082151
    0x1003020d18032c040e1509061009090512030a140901061d130809150c0703062307140c070b0711030d050403031d030105090a12090f0302060a030e100f 66
    0x8201409a4480500e40030700d02143c3c10542c520350901d0341c0a08a002840300c1204c1c06000608a500442c2ca01218042217a505c20410005c071401c0b40c14540008200c1c3c1c0000380003104181d99102d44400f810001a1440d207804000a403941d40c1c1034001c040740c044030003202c0c2154140300c1e5060303020740004e004001d85d00c0c0503030100d01e0410303810b501c885104414215002d00b60f1011071f50344d43c1d801e0b84a07081c12a031015141030020041e070803e0b4000c0401c4510310b4001c001e00c13440c40c40e200086da4000300104050440a00454400b50070007546c0135406001494503440d0150646074191060066000d504050722411030045981240c0c540248209d5000e0111048520440010503a403090001614400204207004c00c00000380603006602d01c00c00c44c003405c0c01150014001090840e00119001304030b50307000e81110b005002c603913852114461450b2814100031414049240c081803204e200080c080c16000800a060b20301c46d41c0300208121102c81515080c5003a800310801034403074484001085440d06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 663084640 1250 663083390 663083417
    0x160515070e030c0405060f030d0806242b0603060b04050a0c050f090105091e01030e060610110102070b040b040c060201060612020904110301080304260307021003020d1803 75
    0x74412269030400060040c01031088800510002c1c04014202c540c10120b000f000c400250340074403160140c0d403455071b41c2040340c0c685002001505101c030700040c00c407800310410101880c4108021503104200b8202d2198000d0340e40704c2d000c2d08011242030003603015880c0a00200810140340c00c8248403080c121340502242d112110803c04480c40500c404010401c00c210084046940c403001d401d600c001410010300300306001c40440c0d20380c418103001c42c0c891130302c291020a01c2d42c7c0510944d41091aa0001010700c0d02d400804102040308503131000050110300544040b508509404071554554001d030b816046003014645034140751810344040f1f0ba40503500002145892052040c02c080302c0d9070390307a5281c82201351000c03d002540121101034206440d55034500e0380840010056008098803401181d03175034036003141141440d4100703600a1032008182c50310b05a200c000010340b00e00c243c04440d0595558104403066009201c0c0c50b8075001214103050000509180100c0c0140d03805009481d06060554403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 663085890 1250 663084640 663084647
    0x60306090e0f060105091e04060f14010e180a0501060b0702030d030504051005090a1a220f0303051f1d09150a050c0c060a1a1903080a0516051507 64
    0x8601604481c1d0744200010002442c0001c8880d420000d01658009400b035048a5a04241380c00c841c01d49e01030392140701440280f421032041076084000600618410b5051120003081410050a424403081c2138580081d440300f0240544118280d2100082007115038902040210b81c0020b84107911074043d9840d140c0207940240a1503106d140d0201c094a24001380301c10001c02030101901c20b1940c1e20030344014100052a104050030a4030060303005000501d001002081c085021720801921414602d42d5880081c1c0c600850307900d55589824042440c3e0b44290510398001d00000000490301d0080c0c0c1d00040a00c2d24040a0560300e902e14860078042e40e54100103543c6400c03030204040b220200000047c0701242030b50003075401015400281e0b14061102e4441e0b8544038003540d480f02080d0f51400030001c0d82014070b20501594000340e4510215141800310260b0034156032101402844000401e00e080c244642d04455100b002d1850f880d03000c0e0315030308066a4800750344c0481c10702c0d01480404240110301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 663087140 1250 663085890 663085903
    0xe011d0c010e0102120306220e0721030c120320130603061419050d080d060503071203050a0c080d050f06040b0f0103020906090607261809041704060306090e 69
    0xc1748400e2030b1560300d5400c24400300d40700c0c40c460100a2154103807050407810550041c041c605503410002c10419081c40703525240c100a0340d20302502d40d040001c2000010350403011010102da0000305011040240107402d0700504001e03200d0025020300641c170400303c40410390162041b9000d10003951030701500c0e28001d0342118003a004080d140c1d152214026202c0c58131042003164465032400b07001c046540e07100810031804085600311505000819103607682005c9100e49070003024100c0042c4442485c2169801d0240b902c0c80f0f01170100315000501c041441e004001c48c010305980b018038150389681c0e103885100181016107848038012401e4000c10018640f40c050b200c42414018100f000520708030005500030b46c40201c2c01d507080141803100c04030719528031010740319a41c0218014022034000321b050110450401d14820003554051010b140c9018140110800211050f9103d40c0c070390701d96081004000c0810f5002c0c0c40c04103030004020500c1941a080700045442c2e507182848508441081580c4441d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 663088390 1250 663087140 663087163
    0x22060b04150e0d020d0c030507090603021507030534122d0f090b0406020109032a2d0516050f090f0711070303020a110607050c040e011d0c010e0102 65
    0x200760b10310405850300781e05e200d442903c1003005c901c0c81640e80e95420304204140e841203014507601d0500b081903050406c050140c540d20400610b103000317001e5502402c5400b0710f00d440c44c44ca04540c120038100ca4002c070f8110810001000c145a070b000c803140b800f1107026820780e03141e00014142c821110134049044079003c03140b030130100d90001c007084101c5049a0f81a0501c03264420403600b490009210a0341000520190443d40c1c00400e40300305508014000310001c1503090b009440401034040541d100341081442e859208051a4210901c2086405407070310400c0c00c0194000550495401c02c00c0c005415807840562004c0b91603a035036250b041180e000440074005811401c440e0018100e8455803e1060380155141485004c400b548401c440c944a240d82040b00564000101c0d50280241350b43c505406000869503e8501a81c603950f45490343d5466030b0880c000c5031610a100b103402c10030f40024130b03c2a1220b10710026051000c1c0002d50318451010007c1c041800c0d0a82141e0039440810040c0582 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 663089640 1250 663088390 663088399
    0x3030c07170f18091003020f0a0e010b09010f050309072913090501090902010e090a0603050a150f0c0f030b03030d0905010209130209010219050709110d06060e010207030222060b04150e 81
    0x1346c916000c1c85040c4a00d011890b620901003900411088032000b03003940a4000c0e6518951604e080400140a8400854103a801d1210030b00812900210002c0c02c8020307288240c28000a86601031410b07944c1100c80000d682d1f04d4000407580d0b40d02e40c0c0712101e884c41250002c0c001808581d917510b41c840300b00c5250b0074003c0c1c0061801c01c05003a4a0600395501c03a00301c040000c000642d9076494841c00e0519444281c110b80144510381d440c0e0805100740034030020f030b4900d58400c000c070820078200640314803072082c1c010045c903445402c244d01582d814805d46410445850b028480b44d070081c0b070f2242c000c0d0b00c424800d5100d0264042005140d4143d13100303882581006800500b009000c1144550440000c0d81c4125940d10a9150100301c2c800540100c04180c031039810420b8032100740400440c01d445864000d001004406920661703039a0380065030204590301595070b00c4044e00110703020b191a580407110080b1103420401d0005144030410001c02c11201642031461116010302c400b251040d00c1c030b22130613610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 663090890 1250 663089640 663089671
    0x9090501140d0203031204080d0c0305072f06070c0b0f01030c051212070c0503060f10090c1803120807140417010915050105030c04020c03030c07170f1809 68
    0x103410442d40a455460009080328109907600920440d4184120750483e52000045040c6128084a00504000164034101072003a4070300b4200042c40130521010711f510229a80310150040d030160360350503134441c003100195580f520704041b020f8902090031204648550804002944449214481c94180d962184c01005198648010014881603071300c1e840300300c0d000f0100d4411465244038020303e40d03035100b05a80c0c00e01c03600d01030030142000c20003000c0300848400c41e01000070f0000c4490b070060030341e039250300c00251007800c044084403a05003452100a07450440c0c4008000e0006250048403054469038601d16540e940b20801c48180d04900b60b1582c00007070034030083c0300c100c4034604036140c00d0907110000990310511741c95404003182c0344000c60784102d542d940180014201400101040242518154038119040a14683e240300080480014800100300c5000304010100a03900707000703070702c04081d0b2101401c10440d02c0d141e2101010012030140f40c1905401810301c8031080f81b04101c009680c003035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 663092140 1250 663090890 663090929
    0x1110c030706030c050c0105241c0201050d1503051c1103120c070818030f030705071202010e0603090322060c06050c040512010e15040209180307200109090501 70
    0x134248426482003072100a0014401c00b1509110711407150541d00c10748000c0851100103080c02e81216070b082401003584a0200300500721044804100d0759080c030785650f954000c00340140040c035448641d1020349504840000034400d00040c030101c0b40840c0041841441d9a8180c25101184104031039000c0c0c0d0403e00c507900d540c5001d155815800911080b03141d02d00076083d0f9030268640e01440d15920b16455030502003800d800c04200008000c00540d0085140c8082601c849549806030311482104200c039505241c1164860440440340750400380403151641801940c540c0c694103c001c5050000ba00302c81400b078205e40f1510050b040341c60a88556950b00170a0301d8150142000800501c90040200400030f0540c0703c41c200541100c002c080001016202540110708200c000d904510f03c44c0541d40610006d41d0f00d26503515080024040780030325440040240508601986a02820100160120407040c0724490b0785101d08850907a9a1242c0e00d0315800302c8030480f0028010040e60b400312450103003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 663093390 1250 663092140 663092147
    0x71107031203020d02041707090213090207061107080403060e070e010e2503020a02010b0a0f060f1202070309030b0a0c080c0a0c1b06080903040b0a0c08091e01110c030706 75
    0x2041e91540b0710b0b0240c5407201c00c0e035449003aa030055000845101403004400c0e0f040600b4840c11000d00300d540015840c00103240f16044400c0c996004401119500060074000c00c07840d42d20000118000709400354441e0114203000b0f00c40d030401e100c103503081c03410820a03000215000c0788001c01d9801c2080c620764070380d0a001c2d0aa282c110300500542d005058090101401801e0103070740c00c819038043e074015030340340171843c1d00a0950f14000555401814420780c03c3c8100451544e0301000e641c1c1a01e000d40001100003400c58030282d04c00c240b081910f20006020091582c024a000c09803401189000c000351901031100d81202e40049121002815180102e01c1001c40c0c0703c012310001000340b9004414401da9211901d10000c0c0080c2d03008200318003c400c001c4541c020030450350001c1c0620246081518260320404148180c0560720200b002078010030341007050000566807800c1010f0b09000703120b80074a030151003000c01c60082d64040707000c00550342c0d00804002450b000203107000d00a00728103031038444c003503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 663094640 1250 663093390 663093413
    0x51309050d0c0f05062a070f020f0612040507240818070b040f170a11040b06041211010210060807030b040203010e031c0c080906040b0a020c1506030607110703 70
    0x115041440c10b4842004504104000c1e409040399100c034014614610b00b01c001b1000b4400d9210469060138000c60003c11486c3c00001103264043e82d81e8801c4180000015050384501862410507881030000e210038801c00140c1181a200141d4040c48205601e01c10582c1e000503102030348000880d030400003441900d200c0b404000c0c883c5140211281a0f440c0c80c0c0501e000d404c50782110a6a83e9107c078108a004074039040c100c040440d5002902c241047c544580c0110801112128080c0342c6074541d0010310345a0000300c034000c100c281030029900c41c6a180241c0710100702a28a40140710307a02081c00d8803d0030340f0440080390b503c0c000a048007491603461043c00e0f1401003080ea8195a50490041c1082c010b00040100c6090481c5580c1c00600340300591003100c0019903080100800a001c1040403040010100e4005030030500002c402d9850b5000000a88600300d4030740d03a20b0091240e50402c268103415454010b0313808400f5504651b0381d48a00301d44c0200d03000710fa0000c41c1c2c402c4204001040e065440c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 663095890 1250 663094640 663094643
    0x408190b0709050f0d150207110a05010c0b010b0c033001061805150c010513150614042004080304091d03030121050105160206070e061c09060f0204051309050d0c 71
    0x1006e42c00342040c0f0040e080341c104503800d546611602d4216032091078007012490140c1000d081c094903a03e04d0791200440c1e0392050013075502c030440000700e4200e003c40410949101c055400c00d218036002042e08911a98441000c40c030004901e00c00011441c5801040290740084190075140f003050b107407000f00003422003d091070005840080003091440c107002e004d050302c92405078083c2038142000b0319044038015240d01e0a003205500d450401d0041402450100c0e6000d0390481d800300c0c40c900110001003210307000602400707420400003400958504080080c00c116030303c0b0f203030411605e1000204804540454110303450381e034208000602400c81c0304060024208a80700c50288100d0f41c2d030b42e400303086540c1038030780c1001a40c40c0c20044200310b0307040002c654880d1180c0b81000060080c04080b5400e03000d20701224840308410041c411000d4005d91200030241c3e00b02c08144100e907007a803a818000d41c0a0700810780160364030b64000c4400009800f50106165224005140000e0203801c00c03903409101100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 663097140 1250 663095890 663095903
    0x12020a090506031f120b0f0619090c020f070b0a05071e05010504061b020a030e0d0b0a09020102190c06030908041d25080105060304080408190b0709050f0d 68
    0x1004109a25400c003d036204815a03c1c01000c4a1900005240d81d01004e40c45030644007140320540002400404226400c202d90340c1140f109522180000340e031100f080040e0f4000d0303904080d00001ca00000350042038800b0a10703003c1e00d104e1000d03c80ca0548032005401400c60b404410042175035039a121f8002803000c00d004114000f82240308262004402000380000d840c183e4680050100348100780c810340044003131484545002007281c4202035101c0da0031500140500501c410342c9403a03070326450004035005030b10000350506440c2c0705200b03000920100034103134014418401c400704103984000c1d41408107600040301d0300e4000d2900c00e080b07000d84181d00044440040c1408005100d1040c1d0340112441054404801c1c0603141c03c00100d050f03c1201c40f041202e0401c0034221004417500440f010341510802d031141c550326500d508000d403003442030f50300c00311440c4140070802900c480807520090320b05109041d60041611003034011180d10205005166003c0100300950549160500070385403134521034407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 663098390 1250 663097140 663097157
    0x6030c0303042907031d010302030115140f0a081e01060503160c080705011e0209060904020c0c09280630050d0e032413060e030a110d090612020a 64
    0xc62042d44d0f00024411030100e051002e07007860404a24441d01e0203da001e103001c500319890415030701c1024144c3d180c114207200020900382c14240111080f01c0380d22401d0a03410ba900e09618400520f080700071502d89000300700d860140c00071203c619a00724101c4445c1d80c2e4880c11611403665600ea41182103c640d000c0c0710500c1d4a00002424200146c20168000c200000780c41c940c5200307800461444000c9402d115104129103c210303914072050311001003050360016201e01000750390780c1c6000b14032034809500a800b0410000d4410100e52850348030b1600c02888840c9050b0035100c0c809954550140310700500c441e03540059007002d00420308018800e4102180030700070a54403200c0c1880e0b040e010396000298238105072151410104618100351180e60061140790a0018203000f61000c040d0462880c01c818000c9202842400d03009240441c544a05407079691032109405054100b1040300d1240500030040d00248640c042e00407031003202c03420707201c0c3c020b042907883e120802907205031003602c140000305 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 663099640 1250 663098390 663098459
    0x120c0a2102190f09140603150109110708030a09140f0717031b030406110601032012010c05190e0d080f040909080406270b030601030905100b0906030c030304 69
    0xc01d0740000744004c1400290019181398131a4500d0802801c8a010780e101c44100f0078003100708141d55046400c2e904002581c00c0c102102599244540440038100c08404001e000f94429998061400b25228640b501c0e80c40e00c20540304da4030380949951102264002e82010000300c030840c0b002201d4894a03c040d00d182c10205116a40200108100c1c040c0e82c0d80082024400030703800a46100240e00310341c2c0100300c5989180d5841c02c503611000c1d0355881e0a030b05940b041c18a51030303080c42c1c4881403403600d0083c44072004d80f400043c0240c01c58003003c00c80c49142882080180d000f0960209e51344000ba05148110340d85499940c410340c031004d50f002c801d401c1000002100d5130303076202e2801e0851040f80910303503507481c0200003040d0a440c86003c02180c030381d0b50460300300618007440c0304080fa1600000282c40ba914800103030010021600060118000c04c0001c44541d5a10b50182941d1070007103c0d5101d140c4c0360a81413554a601940e0007640503402004140302c20b0303201d01c4800c4103d40401c010f900780d01119 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 663100890 1250 663099640 663099659
    0xb010e220b1e04030c0311010e031603020c030703112b0b10051e090f01061e1407080304020405091b01031a0d03080f0901021c0f060302120c0a210219 66
    0x2150184e0010f82008145c00405500880d5802a000100001d000b4611400d203001c0d228410061031201952401c014682018020301032680e005100501795902c0507a6402c3c5400c4000d610b1400510035150615581f0341400c541101340c0d03010455440b003424100041c0d49099071100060004141c0507803110000550345c0d01c0d0031418800258404586d940141d000b410303c415480c0c041c0294500c0307541d003070050000d82d50203240c0c102c0e02c1e000c5038000d000c00043c0810581d5804561003000d41c1804001401000384005040158011882a10304110a5680242c0d060300c0354240d0106100303044009044081d41c0d807080c0c00ca503c0000d08041000c1500b6405800645210710086044010070030344000c01403d0503003000440c3d40006184001c3d46414041103141c0280d080c150400307200e0903503c49048442542660040001d5540946960003043c07140300d41d00e07a00c40d10285454852115218081751152400000e1040b00320440f01303031100100c0543c06c00c14810103008103440e48101499001800591 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 663102140 1250 663100890 663100951
    0x31415040b130e0f0a030206060d0303020c01050c03013213060b28080402010e0d03180305071e030803011a0d1e1406010207031202010b030a0b010e220b 67
    0x810350000549080d0752403400341840c501c4241d0104c1500541104030100760081010355000600320b550200900045ca000c3d0b009002d80002070085600c0c0c0130410401d804001c0065050302c1227030400c0c41032003079045d10741c00301982c0d070b10606000c10802e020740ea84030b0b0501d12142161f104241202250064039007030a8107854000a070280080018403808000500020580600c0c10748240780070b095910b03203034001030000c0d120320740068090001802c8072014984941242c180b41c03400e0b90607254501d652420685e40e00c0003140074218401003000c0e0b04a04501c4107540c88022a603200d851179003560304c4c1405d240100d500e42902411046c0041004040d40c010a101b903840d5608e80c19000e001c0c0340e0b080048501110300750b5909124844442081c0a240c1c0e80000e90300381120380c0041c01c0b00c5410070382c2c0c000328098101034040c60741601c9503240040c00c00c4124820075041e91010f8181038450340da0a604007420340e8403512542d07041801c01c2c04160114080010b900e50110030725894840c203c0740c10078a24513840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 663103390 1250 663102140 663102169
    0xf0b13091a191a210307030f09152102090a030809060f03070504180b03030904050718080105010e0901052a120c0304050d030b0a05011116080d030507031415040b 71
    0x300c4010718201e0a1030f10b031110308601000c0700011010441c13500002641d0f0b03c24040f0140c00d10030150280d02c0441c1c07103903101c0d5010f0000c0c000884e074510300710300000d0004a00c00d0000003d00b50600803810f2040400d2080e220b41d454021b00e213104540c40c50f104c03a44103500001c2003a40159041041e84008040840114010607a40c0c0d60650780b9450300c0700b0800f044d0f9031508641000350410050413066900041642e00e8064100c0d80081c0b5504c1c0c22034151040001440500000240e0300f90003c2c1000043d48114106c3d01d40315020540d90792075000d11822604102c416107000c901500c020b100900d6030140949031084441c004a1505005642000b08544d0486100001200000030002046002d00410316000c500307040a01000c2d00100014004400c0d50003940c0c10000c0a040b408000c000800c100c60070080010716040c0055128450b280d02d6111809184010a00f031101041006200b4481c00501c02298041c240322074a80c1d40081d1a0b032441000001d6000781c0741c00784146156900301c00b5030b00d00e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 663104640 1250 663103390 663103421
    0x10b0307030f0c17160e13060b120118141c050307090806040606080d0e1c02030304030609030302031e040807080c100e03040f0b040f0b0702030f010f0b13091a19 71
    0x120706811505c05034440039000740300c0c5410340b031007440020400349490600721980000041840740c1d144000c91090441c08444180940c201107084ca0202c0f10400049045802035184140101a82e0003441c2d58906041c0340448440d02ca802c0c00e01810320801c05141c00100602c0e2218006940344150352034510b0644051314815921842081011002c007c502160019410044d180070301c1100000c50080c0d01040c090781c081d10114202046550510071500656032010080002021604000780250000c54018001105170250b031040e045c1a1400d5600c42c50384a00910310300f101d01c0e80c030805290426045c14015101d180f0100142c81c00c0c43c042c58a02007500001103441e54075208141081e44010303404416501e100702b0092003490407221200007520380317550f80306699200e20f1011910b0401c0c1d150800245520b4200040c40303080c5150080ba22140c02256865001103c00080740c0403a284220001c0c107410350f5011801e0038184d0400c440390701c0607500e004010f0b00b156885040e0309460ba03101c038100e0f00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 663105890 1250 663104640 663104653
    0x7080604230c010e0111011e1a060c0c040f2703021002070213050c1e0a0206010b160605100f0b030604050c130b09150a0f0e03010b0307030f0c17 64
    0x121412058815850988a0050001440e10b00010f8500910141054108071940a01e01c2c4104400d4005810600c80300c180700d02c40d0307102c80c50500001d080088a04401d000c0700400c640c45d038900340d426100100d40c03d001400c8200500b5007004000c040070012500280c0e20b1722200c4490a00c400c0c07011810707600c524401d1080103401d150090030002e182e01203130b504a1043c041c09015849501680c03080c40e109000010707440c1c8890109004038010340d000000369024190036500800f01440190200084680843c1c04590f02e4000e424001d00640762401201c9210550040100c0c0140e0000f5030003894180850541c2502e0311800781c910343c0541c210cd903a0b081d0000a11010b404c0520035568001501c0c840e41e41001031003850142080c0d49407180350707201100403613000050303a038000b40c0c10075004d54070141982e500b240d00406400c0461105010b80440e02c3c440c102d40c07060906020300ca00c1d0040007009810980e0039581d80d0b02c041c00e1290300c161100c00003a40c3c04500600b0140d40b0248440000004001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 663107140 1250 663105890 663105923
    0xb0103030c0309081c03050406020d1503210c0f0213110901180e01030818060d060509101820070c0e070c03050904020309010e1609111201090e07080604 67
    0x101800f16032044c040c507400308903081912078418800103194950340c40c0c04261500c990504074040c0c042d0f60f8100014618044c00c0c003000358064032118080b01e100d003641203404408028a403484185200c4035101082e90601580005a01001d9644400d48000c001917441e000c0403076a101195201208282c0c1c5e014002500700f1a9a0041c21081841070313406000d0705a5414420304412003281840010090038000c66034226101e8084a402e0000402a02180d140c0620319880f0025210a2123114055400b01c004115107070442d109040940d1044840c036000c21201c040f500c4010001d6010400805000f168130b980080c440b00c00510300e09006020001e12542400030900e0b507514007904090500000740030500c00030f904a41900c46c82082100c006850350b403aa50040d0140c190128101e060780078200400303c455201110f490242d0f40039003410008414020300d24260b03403203010141d00c403441c05040100201d070f141d40c01800070780358048165102555101d07001c40c07825070203a4040310801e250b08014007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 663108390 1250 663107140 663107147
    0xc02190906170a050a060e0708060406061403160b0d090609050a0b09030a0f0f2615041802150909010303050409050a06060c03230a12060b030702070e0a090b0103030c03 74
    0xc100e091600b0250a044201e640c0d5640e458052032001451280c84d01140181d90b201808090014030075002034480b185018a400c0703000780702e540211403502a280c00061258100015218440d01d010500754900b036083c040060790f030343c0200d5a1080c2e10340e1540044400600a805007401c401c3c13069000b0f04207107401d0f140070560308070010003a21480e030080c006e0071002c991024900c0036098107401c0205117041040000c8840102141290280b5001c00140205482a9a0004d840b03014000c082d0760603030220030204030a440700e50924801c0f003d0061b00e00d001501c2e11458001d02c0344840d5028914003003118010500d8964241d01c240d000c180c0c0490200105001070103240d034000845442002014104271000d08084160407010701007181c640c442d0b5002615524580e100a210300c4540390701d829004074001d001c0840404110200d40c01c2c500d0000b044400c0c1d2065900030b038042d80140684a0070002144000c600044c0b10080c0140c40d490000b02040c818170805000c1c60080d928803809a08504029 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 663109640 1250 663108390 663108419
    0x40b042408010b0313231006060f0c080903031b03030915010b0f18150c06061c0803041a1003020312040e2404020301121e0302120a050903010513021e030d0c02190906 73
    0x103010301c0280314204104070781c0203505a11107540000760640b20010440032a1550094310003142a0400c40010000006800000766100700029012078000b000c420a02200d109021321880380c07895130a001c40080e1012a40140000e825020300703070b40d0141c20f0000010200542c100104401701746c005076281d03400704140b000300c0e80010b0585c0d40185540c0700001841202c51105070140410801001040410503c03406503409202144200f1000d414800c070301418010340f41c84100d00c2441000b0f01c1c5442c0c20181e10a9904542040c480c0d80d4050740c6841d842d0844102d01c0001d0000c0c400c5150800030740b540d40e88040d43c042c3c02e02210032012170103140703041d6912440340c25104510421660041c40080d034001619400701c46540c0300f1980f910030040080e1164010074810b540d042d402d103001c100303043c2001130000025a000300c4034029600b51014106005540c0201c04075010b0f0018000303500342d07500a003248000301e840035101c3c03403801b2030800c182e1110a2258128804698650804119411038407854 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 663110890 1250 663109640 663109649
    0x1903110a0c0318060f140d0e030301060306050d21050c0a05060a0c0c0f020f0a051c0201080c0c060402060f04031a0103030905180615040b042408010b0313231006 71
    0x141c528040c00c000000d400080030743c5c0c00c501005590018805076800f500c4c05c0d140c165600e603800740b1100106420b01c9440303030000d01903d0300080c80d092000915203040e124103030032240c000e1200c00ca0904065005201d01c080504008103020040140070f000201c1080b0002400780100301401e19424540f401c102501c480038070342420040c00c2051b0a020411003041c0741d0781c0680c120786206281c0360071030202e0200703a000c2c0c1c06281d110103034211101d00c404e03103503100301c0540380b00740d844001d60340e00c140519407030b4041c090105045600074030010700141032541c02011196040d406140c01c1a64039924500141c4043d20700c0921502c207400100101a0040804405460115904038100156040341030740a08014800b0717100342030360344241e580b8896007030840d00034102000d05280d640343c5807000099110022a059030f02c0004282c10b5101151041c01d129058a110100c0d0b0f91858a81004458043c52541000c0e22540c0d5810849102e101c84010149108100d04c00a07001254000200c4030449059070300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 663112140 1250 663110890 663110927
    0x219050105031501031508030d240303030903020102070f1109010506031b0306120d020a1a0f01030b0a0e1b01080a0b010206071116090605030d0c0203031903110a0c03 73
    0x1800140e80007410369070b000110241141c00302c198240100c003d400010214010000c0565011511040103c010114500d85603c1800002c1c401e000e40c0181c00c5e05545c402c90300f9060170f001400001e100350044044a07000c1e01c009820007041f511003400851401701c4c00c590f13503090140d01e50745600700b401c401401480100d80181c210301d41620f84d500340952081024041110010016106070b840d42e170000c1a0310440411500018002c1401035602c503016102914400070140d5041302c11451701c110244201a213042e00740d00e5920b596101103040e400a084408810303204d000d0b007203c2000800242071410a0318900d5011450540c5c0050070b203d102a0100c140e40d810300b0718403811642c0000703006070403025618201c1441c5003441802420700c520a400a400c40070044400500c400c020340000065900840a480c81102c02010a030340110040100a4141d04107204000c0d007050b15071142c40e042c80c0301e4100840d00300c400c25000029644080600b1012030500d40105050590140069680840890 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 663113390 1250 663112140 663112189
    0x150e01030504150c050c0a080319060510030b010314070905100302070b0403080702071703070c0506030601090b130e040b07021509061303050c0a0f060f0c05030a09061d060402 77
    0x45075814040f8022400440c02d40d150300000c01000d01c104111012590618145c4021019515103a100f40e403065a42c18164600c02484030703d02c45051064200321a0010700e9030141c1d007003c040550240680c102818149030f6038208000c4190310599449109011079034844020380e06017800c110a818071082e0740c00805105001c5000000d00c4c00404c02d0704207406040c40a115039942200300c0c641040b0303400c40d14020210541030400300c54000040e00d02140b040610041c5207031030b28203010103400704960690005405d120b0400082c10294020102d410350010301c11106505c94100014980f002e44044680c0c2030a04104009260305100c43c0001d80304100518186007007010103c1d41d980000307040070392143c3d00c040d44181014000c0046500c10700050050314200201802d0a00749a031448809594080c102405069000d4852040d021810071640303500341141c9910427400000c100500c0106c134255550b01c03100d03505d060707120310211140101e031008000501d083d1062107807100e850040f4002c5294440d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 663114640 1250 663113390 663113393
    0x9060f140a0608031c021909150f0e041e0e1f02030103150f0912050a080108160b090612040b04060c0201020418020304020315160305060607080405060a120501150e01030504 76
    0x801201c50545c00c1141524280380e4840869000703100b0000b20240240c00e036a51469582d070818054030480d800c42c1d0f01c4107101c2006180c19500001d40302d2401d00024140d07024241c40d854254014051151072050302030b9204088110b041c01c9548030316003034009500480508682078031580e1110300005903c0000d40c21549035556071000c0300714011480101d50b4a0703594024041045034040c0c142e03290043d40e001901c200c80c102c00340160740207003070460001d145030001007095140000c8a00c606c01d02186402065071601044000c2a0403803848554060303002c21800203a61040408180103500685111060b810686002401c41d603a4a222006690040c40101310f100007a540e0185018160307603005d44e89940b03910010741401201d1560000b03138030096041c08801510b224038005450701c3c58608029588581e020400103006100c0d0062140d0001c01003072240c0e05010003d0428071410b404d0150600280044110580e54240c209200d109040d141d05862650b000b20182c56a03142802d0400072803c05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 663115890 1250 663114640 663114643
    0x90e0f0c100f0f031820100206150604080d0908240f13050a080d0c0801050604090e1c0f0305070813061a031504030206060306070c030e0409060f140a0608 68
    0x160a014400c1c4524041d002c3c5869019403c80d50030b000c82c401c042d030340d030a00b42d1a01c03459014035060f4a0700803040301c050030903841c24803196082c44180c940e00248401d03036451203e090710b4a81c035450560010b0083c000010a010f00300800c84403603c0c5610b940c00c150341411200e6180903420380002400039001540f0030345490036812469000340035600c4400580ea5681c01203d400305021a0050061103011080c00c1400402409002c42a40ea0310301400300c0031121100321090700e028041c10707070701a608100401040c0c20560000f003112081e00d0641d0b6940d819151440802c2c1c0440340c0c10004114504840c40116926204540d402410342c10964001d09050031001401001104014055652984600c402e40d00440703203407418100c014121180f251100c030000001d00d0060358205c001d44a0000428800c2c5000300d25203124441d40d607a40403e1880584003241e0703242d1644150703500280d8a40706000420154010300c0b8105003a40c03000704008400060110101c100140110301d00c514144d41406150b20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 663117140 1250 663115890 663115907
    0xf0606020d0c1214071b170706120b0109030b2e0b0702040b01030209150c0f0c06030708130c060c05060a0501060203070f11180a1109090604090507090e0f0c10 70
    0x420345802072013581c0d503403002e01491007000c030050070b0503141840844000a0500399030040da0040ca8660b498002903000d41c0f40e481c95603015000105e04a07200c0e001d00c4111550202a004105141840c001e950325103071800c03100001d681c2500000c400c0600b2003008100101e00d100e0f82142a03c40c01c610b0761800103103104034015410020721480e10b81641059981c840e405031b0b03489850090a1080c07180301002085032a9124000e0710034240200450b0b6104c514002c00c00300e9500c40050b00c0e01d440c3d640c8041080362415002440400d185104c548210b0200796003420b440c0c050016030300e48d100440d4042c201076180080081011080d18103002c01440400d5020003a1510307554801c954501d501c0f22450a502c40c1c042a50845400101e1071000c28032012100d040180560002d80041280c840100ca1040142c812a00020703040840e90340400c080d81070a501801d00703c1e001d00242e980030740d00d4844810941e22050030303004503070b440601e1141c003c5c0e0081c025480300000485000c0300584181101a24040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 663118390 1250 663117140 663117173
    0x110303070c060503070309060213080c0f0105120405010e0703030827120703170901240e060f031f020405011b2105130609140f0a091e0f0606020d0c 65
    0x8001300210364610300903008080040d911040c290344941c1111604c00140c03000344110821407051022078456418041c4000113002d0041e9580340c513010040b40c000c01e003a103014000b10b46a640c0d9440346403000c441440700740042e520a03603502c0580d04048554020300326454840b40203001090a520000c000700140401d84c020302001d0607522094a41419508120722301400c0e03d188140804000c109403041d0301030703842084100002115000101e0b03052145078494060340b03481340f000710040350607450074000300d0520b40001000c0340e90400d0100128014001c031500201000b680214080c0101e603040164105916a800c10f4903d5801a940350400720300e40b240f0130420300c0d070200e0340d101465500c0356003224100844041c035410b050f940e03000d000b040101c0c80e1007907902c3c0500803240c01d5010702c0c2410510400304401051108101e0030605400c0003001e19074500d000c8066513005180300301401d40074100680c41d103510000b0b111850b2201c0030b810300d041569904104080303200070300c000034070b001420495003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 663119640 1250 663118390 663118397
    0x130e0c131805030d06060504060f142104020f0f0306060d2a0e060103051e06010207091104080601050f2103073002071a0d060510020604110303070c06 66
    0x5030103030082900205107a410403103901e0000340e41d036000e0200010052450540c0703020200071180e50341744200e686006601801d000902150a40e000340b51088184103220440c090b40c0c1803611010500d028400700180c125078610860101c200700070751a00d000707140c0800c0002c1c1d814466503102200007030740381c0c640208103e118403480042482440060310f0352000e511031504064ccaa40701d2013100441c007035080c0c03041c0039180120700000355080d480f0340900e9014003603480000d40c1d80262448440140c0600600d41d034110710030310708001040307661400761440007110041c1c4695618241034045080c0f51050304040e014804030481065580c5801080c14400c559000544040c0241001e20f507041d03110701c00000d46031244c502d4182034110140030301800040540390340c1020381070107010705036290300491103403200b5117800c50044a604c2ca00c170030051144c440e40314400940103482c2d10000384101d001e054283e0042e4040002c000410003241102c800424044000b581813141e00e55918900301043c1c021035080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 663120890 1250 663119640 663119659
    0x501050a060c1505040b10080705330f0418230c0702030109080d05130c090c031514010906170112060e010903110c09010f0504021b0703030e130e0c 65
    0x9011183c0080714000748a1001070000b81803908115948400555680452200c071a000080080c00092040c003200e2000e09032070786504c1207005c2d000a11000141d40c10b240840c080000c1c880c982e203c0010301e903525010a00644075810103103030000707400501c071001b03000c245029031240401041281c002101900410700d81155610380700d08000500031210025011760820f40301908000c00c14010b0b046400c01c2085c01c016913614618055518215020b018140c1084500709000140a40e00712265082140c01c1c0880d560741c1c90032010b01e2490840d4000c00c000903451410000560b0b11944000080040e46000000c0d0300110020504400c0b041c440c0d420020300d6404983d00700a29a00304400400c1d1500c020842100d0070b0801030603184c1c11510240f640d00500d003403100035140c103428440c180c810700404d15019a0a00d014030000394460541c0003e8208103100452043d881008201c0245100b036841540011000d03003404000130f06041d001c5940c41c206841704105450029000c9881c02c1c5c111040c0e01e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 663122140 1250 663120890 663120893
    0x1e03150106120c1404210c1811071703090c09010b0310050a0f090b040b1c0203060c0711100512100603050c0f120612030c01050f25051c06060c0212010501050a060c 72
    0x2c0c846e2440d03000303080125524000a04084401e40703c0d04100c1c802500340f0a20308240000b061030310407100024124545a41c5014400350250041c551215540049130030882c541c40025101c140e0982c803413409594004104000c40c403045201400406e415908c5c88520b60610703245480d85081c500030200e003540d88081c01131081c1d580d40c212541d00c08010b0080d4250304004490408203540c601d5082c0e000340700b80720101e10036a07100c104859119030040c900c00070394146401045a8040c040e4881010014144a5618004110301c4c200e805820101503206a07580340044c05000d44600400c1a1130764103007130146005400078101150744503542c0000d0074032a541c071080010201e00134401d4001462001052000c203010055006900903100d0f010316118170366400d90090a500900307080300403803c800741c1d804c2816030700907406801c0754a00d9812a111800c000040d2404480e07080d401600000d43c0c0a0041081d8101a00325400c007500701c000238400307903050401152411200307106413001c2100c6101e1240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 663123390 1250 663122140 663122189
    0x90a0c03180302010207031e0e1e060c030706050f01050d060509010f0e010c1701050f0d15050a0504030f0908030405150d02070506010e010f03021e03150106120c1404 73
    0xc1d03030041031142154012641c01e000707000350000303402100440c0051084c4005030910080003020411280d540d4803031101070a0500600c0d40f208005191140001400c910301d581e11700018042110f07090009588400c031506221041d130740c016209440050f00388005000c07948401d810a21004c0c0c125402090f1511a28811401000c801c401c12840301d14007980786038040d2041d04202c210414541d84e42d6220680c6994054031010280301d4554000001d11140300303542428500562602d028605441d0320228a2a4030000d44504440820403d9601d004001c10584c05c4403080302c00c2d6a2610308044d180342001281a9a4462030147c14400c800205400c003480c0e50b88000c46640100d850029900d038101071800b00e90300c200078054110405c41d81c80c00410452252070400044940092070804480c5544c070910548540141d02603405000e6005000000501092818001d200c907542c0c002c80d2a06d00c901c54001ca03501c01c4a0340081040e07406282c01d035100700030140ca054a1400b00c1d03400a412503141a43c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 663124640 1250 663123390 663123401
    0x10e01020f0a0302030a0201110931020f07030908030c0c120a060212010501020607020d020709020d090203010e0c093306040f2403060b07030c051207050a11030c090a0c03 75
    0xe582900c10140c880b0101035002c0701805000c412a0002c1c031003003190a561007200d01030042540d07002010304411010498a60641000b00b00c0c3d03005040c409070007000b0810703050341c0c000d01d91440b171510002200c10405511142e400000c081c0307000554100109410700c00d489081c5011100d201e0072040c040c00e00040340074860425007a0b4014411540d491481050400e60300d002d02c40c907030144c06540c00181c104c80c00440c69081c805495800390031910300341420349000390864481240200c1d9210448030058501744908201b8400d0440100381c3d0031442da04110041d400241038181c41e80394808442c1030b0406441290000414503204907101700f02c003102240aa005641c40304880845500700000ca403031071108105034502040f5403844020307142c8081901074688030700c101104194200070010110703110b80c0804c01a03511410039520185008000c607032154008540076034140e04040b0440d0100500a1840d105440040d8090070140c070b060400030300d404400500608200ea241d401684096100b50710a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 663125890 1250 663124640 663124663
    0x506070f0f17130f050a05011e1b030201090b070e0307050402030c070b13030905010309240f0e10050105030c0a12032307030215011511121803061303020c010e0102 72
    0x2586480e03120100f00c808600038483e0910701c0c0341e014804115400d00c2101031040c1c1384180c5a0311403020001c0204509001d40800d01000c2012a00f071a070314403280d1112120059009500110b10000300f802c1200c2030340301c040c0c40c600c00c1c0440003807107006a403004940f0a0880b4030172900107842e641c800c20502c89500c64040e00500d072120007410408136000901c4c1c10075403140030f40d5404032031645400065046525440014285020300707201403400030b2540c01c0c100d4922146100201c1e0b04014044c103041990f403481501000c1c1d41020352010404102c600c01c541c01448203c006040716811701001c25240310700303402a003000507521640712040c140642146103c02d013100e4003902701c0b1071040c1c5448499800100c4114018011000d524a03440d05020146040c0d4150860000e80400c1646d41517490415100042100b4003c604001c0300b0480d030305000e000004020131202640e140d000c02010304054000f040b22701d0501c0800b903800c0200e5400900c01803202d0082c00d1070005e400300400141d07e4120f0b608007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 663127140 1250 663125890 663125933
    0x6020d0f180b0a14281206060915170c210106050a140c0d080a0905030c210301030c09021b0f010e0c0d1e0309050d1a010506070f0f 58
    0x40018114090388018241164550b80313040d00f4207072560381503940b0b20a40703d07030041002c0184000c0790100d0b02c0b0501c414140901c0e0a00b1500c103004c41e00b828054850321381c001c1d80807400f01c803001c0181071a800c49000e8105a2442c1c0b5441000d01c10356101d884100192004050801c04a800a00c030184c00707150000380d003030340c5d0451205580c0d10038004209901040034800011100d0300ca0540c1e0080113000d40d4103101141d0007412301d8074004802100c0304140201084110364130ba50318a4003141c418402040298040005000d000d28002c92030000070301501807001070303140c040004101003601d544050742912000c400c096640c1c60908041c03008000043e0589483d40100941506015015480980d4134079404003561541e20b06441000b240054080000d42640c15a092412410102c0844104001e1083c140a038801d07865601051006161440c01c80341c9000241d44c01e248514481015401000d0854503a49400000eaa4002a402040c10000c107180e900309542410480001c0603099200c3c1d4018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 663128390 1250 663127140 663127187
    0x3020c0d350d0603020109090e03030703240f03170705030d0f0b040c080a050603190206031009150305060f0601050a05130b03240d0201020c102303010603140106020d0f 74
    0x724494010f04140c0b00480c040b4682c0c1c0d4000540c03414a0103032000401d035400265040d907583c1d400c00d40140120140c4608020451010008000300313070f000510260440f800709072401e500f18a03103d185400007240b40389980ea424040400021000821643c04911052000c24555659a04480a001d51409081e481800d0912018a00d0790161281d84100c040d030380300b40440e88485040c1a1240c50341c0310039680300c1031005921805402c0c003070b0003035400c4001d000792100394669402140048034904001d03c152424600e13020418004100119030700001141403003030f524188000046c010344200140c03030b03040c4540821a954041181e80300c040041c0201702107540e5900d810f2401c50501c80307910802941041004a05002d2814010007500ca00d41d8103800410b00d1300e90340c1e81040740d0814080a05010081d4040803241d110201d81848403e01d0f03402103213036880c2d5041113800790559641d90306c0700d01d082d41800c004001155001070443c62021480c249410038514030101102c030900d652007100a07500c1c080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 663129496 1106 663128390 663128407
    0x241e041104030605070906020d020606030601260f0d02010621080c030705150a1b230c0102180a0b12010323150403020c0d35 55
    0x80c59250030250740703079207850507034408843c1000043c09a07001040901e40400000c0401441d900141c007440c0780400100350b135807005118102c905070b00c944030b018080584180c001d050345d00d110705482c9603405030586a9070700c22002c42880019071921f800000c580d2441c8410030380c254010840307148020ba150704d50f03801681084140d4140d40c0000c01c600400034101f001441c032580800104d20040f450f00645c0c04c1c0407103881c80c15000b10001500301c484080341d8440b80110b007a0a8403901c2103900920540001310a000e5031410240d10f40c40060b000d114600e680380051240001121280c0340f090303d44414074418016000b480908110f05401400000c1495050b100d4200704814921041400041e4041ca4881c1c60100c94080141607010b00c818143c1c103010b1010081410754280701a24000d80d2030043c0c0c40f480b0400400302c001402210b01c42c119078230100c100c04d1a2600405611032485 = true := by decide +kernel

theorem cover : BRFrame.Cov 662949640 663129496 := by
  have h0 := BRFrame.cov_init 662949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 662949640 ≤ n) (h2 : n < 663129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
