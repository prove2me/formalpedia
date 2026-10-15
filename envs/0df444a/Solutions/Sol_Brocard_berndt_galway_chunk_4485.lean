-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4485
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:26.654296+00:00
-- url     : https://prove2.me/submissions/2e332430-b50d-4644-a560-a77d2b53c135

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 806474820 ≤ n < 806654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 806476070 1250 806474820 806474869
    0x6012001060909060b04090f020111030c06090d08240108190213030b2a0304020117040302070f0b0c1f0605060d02130609050d03050306030313060c0210050301080c0f 73
    0xb003600300607050040042c0c892074204440c2612509003441801c40158002d400b40442d00341740c2e07004590b1342003107441040d03042c1f001784019107441070284040d84c0150f4852000300500d0b00d100a02a0003000700520a10150328100c49550b00d420300091102c903080400d180981040e59150014031075900b004121060292003c125102c8000c418507083c01940c2c011413103d1440d58484c20b030390b07c0502031501c55403415112105082184c00d034800240d0b4202c0d02c1410709200180c00012440c00c03040003100c041c0d0060740201000c006c6801e180303000c800503140001029282c1600591101da80307000f200c41d200d10000081c000042c02c03202c81c0c0d0002d806058010041540c032a43e00c50044080c1d08550040b880d03d0031140380c00924a800380c20ba100445101a05c49900c07451079480581341a04002c100541602040195440c0f600701c10900313401800050b101c100342e440720b9006004442c008a4101d07c00d114003000140f010140000d0350b2a803510088840600024402021420400400e8000c218503292003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 806477320 1250 806476070 806476079
    0x7020301200306040515030d12020d0c05040e100b0f070204060314100b0316150309150e0c031209210f0705030d051c0b0607171c05010503060601200106 67
    0x1c8000318052141242c040c0040c0c1c4903044103c1c025046580c0d403a40c10380c041c1030031034101800382a50480304038a115005040c22205803494059804141e070350000600300040c144100e032110a101038100743c24208002c0d0060a048807071005116200030a50b00c400e002c1600405c40d074076a0020005142c3c0221002c0c0b44000c801d0119940f050580240c9030710074104101400b090500266400400c8103207510321541070329082d40e04096186c48001d11041540365014040410851000f8142e112415000068036000c21015541040c0030071095034440c0d0060942e0f00790307442c58031003500d84024080320749080401500540c00007424003601078507600c0c0910b1401080c103810200f2440d00300c0b5002c1d419190280410700041f02c00d8030980c0001c0721580182210703016850130580c48041d280f1809080c071494420079855517a11400360098204d0740b498001000003040f4410000380e9a40b0107411000e000b00e50600e80005c0e290350f0018216810803010301c41d0207030607480c0d080ca05a607401900c8000c2100301d849 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 806478570 1250 806477320 806477381
    0x70602030c01060618050907171003021c11100c050a0b04140601030c03110a08010e01050603100603020919090c030b1006050703171b0c010b0909011503030507020301 73
    0x402a801d652810400042c031902411002c04132881e80780d9900081c904040c2008002c600140c008400c02880c5d0082000710704506c7e2035a4080c1010141440c0c0580c0380d4030400403c0300552074007801c030034802d401d4800003450000315170201c524201c0307100325200f0100d40304680c07034107121030040c003644140c40c0d000d030501c104041c50b580070798050803141c407500500a851696130802803000800a041b401000c101140000001441042000740407484007a524003c041c2500c007500e907030101170707590390080c8909450300b00811650704c10000c400f800124074503000606021001400d012807010081e001031800c60750f5601c0081216480000908029200c0c104403e4142e011101d030f208181d82e00344040f511500840a65001c0c40e4195145808602031a01903900c01802900c0030703c0200c000a001c56a0007810006044900e501070700000d848800381c82081400c0d0030181c01c0c00c606d64500688a22002034203001981580d4150915564580b070900c0420300405141c00702e45d852041326035804680454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 806479820 1250 806478570 806478577
    0x14031318050901020306101107050630010b0706090204110705070609052b0c05120c0405010f060c29070305070e040c02190f05060a06060212090609060705010b0307060203 75
    0x40400c05036440240c80d03401c031721042c0e40080d0711038480002a1000e5100c5c10045052102e01020340307010940e41d4001c6042500f1502d440041a1004202c102a88042c0001d031030b9200880d46140340254540796400c0f0707140c4156034000d00107a85038815403042d91200e402c907401c0d01004a20640c0e40d8442400d0030303a11480b05019207000101448030000303542c83c01d0b11808403c501c45042e10309211800701614180200701d9803003110441c038201000280da69850041c624916000c0c2c000c0c280c03e0510904010445005820004028202c0c0400b03000c40c941c840d103200c41459000da02c4c40b140500d09408140c030a00100d0725100d05903691320170482056807541006001340291740382c075050050b00104010585914080c40703030042e44941034001604990401c541c1286000d0400301c0c3d40c2490310f0b02c40c40d040c050100d0781c02281035162042002000da0400851100151305400d09040080d5400000c81602c19108800d1203501c010403c0001d01400b90300540f120140141111101130340c640d03000c3e40f03940 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 806481070 1250 806479820 806479859
    0xa030b1002010504080301150e090f01051c150507051306021f1a1e060706140912040e0a0b090a0617010204060e040e0c0a060c20060304140313 63
    0xa0200c4050300c00d500502689001d95442102c41d41580e00b451540390180e40c110065204000703904403114515100e40300020300400c444010303040d0646c1020107011031845019011320130303a15000404404203840c03c0c080801c24030a4080460b054a807180112018000c105440c40481a1603000181c11500052080c00740c41c15410360401845070703400c4803412500703840781001e20702c4190155000603240c00700710390a003104030804866140400d54085800d98000c0a4103e601580c0c2c0d58940000e17082c1c1039103045e80040f045000f44a50404440d60702924000c510942040d081d200c000f040d9000f015820100e0300040c00340600c9014a803074101c09029000d9441000b0750b501012154610322241070003120300341c5031280c403076203040b41e06002800010b284529840555001e041d0780c03036003265600001e41c00145010f654040c0c540300c49040c0b0003074001d44414602d036203081c1c152070b07407025840b0a801d80c5c0e0720641101c0c1c81c9070080c58420b6840c2c11481440f9500f00d20b02d000300e40c042001d448c045041003414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 806482320 1250 806481070 806481079
    0x1091503020d05070509010e100315031103010e0f1b03030712030212061f05030c09060403030c050f070e01060c0309080115090e0f071703121302040c0e30030a030b 72
    0x503200c22200f92860306c903100c6800d00244044c0920792460506a01040481820340780000d21420003c43c81e1080c03901d40c0d041114440c8e402d52401c3d8042c5001d003d07100c2c12941c0b10025101d03801991552694942401e40e1655101ca0303c2201146140c1c1d052090314181d5030003106c94420b890ba00d020050003507010400482c502c441f14404030308a41058003801c10400070b11076180142041001055a00c1d0308010090151940100b28461a43e1030340c10150000754440d4480359a201503030300e81541010400c0c1c4643e030640e800400300b0000c14400d1000f4a0440c0c40f10b08000012070b0b098102110459559007043e1102c2d8280300c0b600000e60b00c2040c011301140c014490030041c41a1440019071955241c800b0b40f0b685030700c4101c00f88a02140700049032800c2c041e10040301d10b4050300c031107a83c141c410b04a8410078515041c00360b0b881981058011541c1d40c11003460f048295204100002d0604900116440c00c1404034120310740c2c907101e84070108d8610300c0c01502100d443d00c01341e82009010b084070013000d5025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 806483570 1250 806482320 806482331
    0x801060215010303080c0d06230a1d0403050a120e1b04022106031906060e061c110102010e062d19020703030204030803041103071a120601091503020d 66
    0x1d001c040d500c0c46050740da056031540000e80740c032250502c9503000b45801003000380c1da42ea4006100329000604c0310344c0b49101c40c500603031380010784200502d042c05544038500000c002c0b5a082001119202119840f43c0c0c507045c01ca469200386081100c1d03440c6541080c40e02a46030074800c40d500300c00000c402c9628070440c0e0039402a42c500000b80420b0b4000d0110080960081820011020080c5512990720260103070407200044500341ca00d22107980e5541e029542540d845c00f00344a8581c0d41800d8a03400141910020381040300d101404030316000050028004111319001c4038441d038802e400c80c0c00d40700c5015080b40d0315400e040c0c010394416038100280c1c10500d242804400302486122000902c01c118819803081c500d0902000c15002e5400000b048082540c00c00010001801d10400b56010f58090591400005061824140307400c410f6040728030340c2080010400c000070800070480b010340b2241d05044a181d00c0e01d80c01a0b401c0505034115403400540e1465184800d80e041d405080290300d81c80b0103000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 806484820 1250 806483570 806483593
    0x302071e03062f131403150411011e0804030e040f020c0f0d110a0809041b021c050301050d11030a1217010e01060c0b1e070c02040e0c0a18020706050708010602 70
    0x201880350140000e40d280003004c040284c0625480d4100744900042c1c16543e0281a00f02c1641a941c801c031002c458520908400c07115950380401c150340c5e0850052400032050b082900d01800e802c0e8000c0c0b0080030002c00c22141fa03410344844c0c11442440045044c155280c00c44040401d445680085c0104900e109038200b08c6a02441180c108a10400c40f5018111029940c1c89880c000e5010040341078100d40c03513810b256442548070545032030240855000d42102c1400030f400322188484140720204204007407005000b2035840b1032041d0803242e80041901c0e404c0d500d900109007001d60340c14001e0200401d107000320301c0140d0840700d9150003501c016040c0b80d4583e254414244514070038040c0200081059403040e00240399500010340048180c600340d00305d420313080f1000120500445520001800610740d000c02c60520740a82c2942c07641007006022240c0310a00030034018481e030300c1419850f00001d40d11454100b060350441d0b506a4000b1014044c503e03046c0c102030301100c2d085c407400700103102e500040700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 806486070 1250 806484820 806484911
    0xb0603331521011b030e0618070b07150f050618070903060b061b300d11040f0e0f0604142e03121103070302071e0306 52
    0x2159100414a1400064400c02e80705034101075100188103641e500301194805a41650a141c51074050b40c010450350081c41c0c1282c14481e024001130001e0403142c1d00c501d00c40d540495648141c94120300180c1d100c2da540d0410900070702d4031400300107101d4a8034581c003112668540000d0301c580016030b0249103c604400c401008103008648000015600040070320018045070060010054020485410440400307a03100703458101903021101540700d807424083d180d11403011200525061036445c501c15140c1508251300b4801c58444403d9203981e66100b0b99000c1400041c0d8016112141d0301000c0c2d15140d600c440c810000c16a582c4101c40407210020f1064038243c02030b00140096004540c5050b1140d8142c0c006400451031140041661f644c802403000b00184000c034000c1d4054403403070340170142100e000b8103031144860034803449030010400600482e03000520754080740e4401101e91040d900352021590809284d401c002c10883c10105610500400c0b070b80445034a60b905001803200c48045141d01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 806487320 1250 806486070 806486101
    0x80705150a0c0c050319050610051e010504170703110a051c06060b0a0203180d0506040b040302150c090a0816140409020402131e050a030b060333 64
    0xc11041004000040c200d91007080e620710200e101c0c4180150706900e40f8000f81c00c145007407081c05607100d032003000c801c20303c0810070a441e00f003072202d00841000ca007002c0215040d440084090514800d006403413000c41d900c6581103e009001040c80d41d000c0113862051180c07a80303d41d00c0260748541185400e4041440d000604000b01e42c0c00505078044201c0400b6184482e0b0313103c050640d00c82c0d699050018103000b0304001041e0000203075002d580d071000940b9001e0041039118041070301034000088580c2c001040004c103541c0140e00700301c40c048075a80380d180032860881c4880e04810000e00301010300005c4541203001e005400300c1140c00321600ca03110301481d5550052045e06032000b1061701c000b000685000000d40340d034580b0182c804240c81b681600424144e07844010000070280745207400b0003400594205003c52404481007886070940b85c01c001811407195804080d0000da40100030442558003000720402e2203440046003102400e091151983c00030b200c8030b0791492008000c002540311405e142d100c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 806488570 1250 806487320 806487349
    0x2111040e1b041109240a020d080a0c0e0112200c0d021612020f030106060503010e0c030103081903090b070503010611010902030a0f020d0c18271b09020d06080705 71
    0x60f00d04162030501000b00401014810500c0e0080f1101c002d0144401c0030020b02c501e046c0b54005000841c0074038401444034400804030348119182c0610000038a507c01e181e170650200900e400c24140c25807000c040020240b410b01041c4550317981c07086003141210701000e043c0e40010704054480d4219081010791300c0e5465002d4140354200601c0051108a51000d00003110b940042d201501c8559803001180c2101d0280d0041e20109101100400c205040c4180d00ca6112900740da5403800c5514540d98007545000c0d44103550108140702c9100c3c018107200e80d00414016800c60305029082c242090050005d6100b801a200014a42c2c6410000c5030414062850740c5640070b0300030f104081c070540318a0140340070300e20120380c4900d050411070081034a150b8a24003610140d64001a1201c1d40070100088900b00380c02c0c58260944003460035248041f407880380f640c140c2c20000c09a4034806050350180c000005812003801203101103800c0800c0c81c83e80d881481900c090500715032029850b181081120070f242e0b1b18 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 806489820 1250 806488570 806488601
    0x506030c01022d030423060f07031b0515070305090a05120705010209030d030b041b0e0927010204050a12020d03050d18060e06102111040e1b04 63
    0x10301e24002c0b1444003182044a00c204941100f0f6034901840f83c2c1141d0143d801001c2c0350510254921140d98100f0444840d01c4041740d02c0c9184c40f0a0085002e6140200e00740075080c40103a82c42d0a001c800081c0d01e0145441d4460283c8040ea0f200d2070003280040000e994250010785010005807200c98002030042a040d0414024501c5211541d0005800c2c1d101c3c5d0300807940d0355002d102c01e4180344c40801200d00342604070b407400708589440c40c0c00e01c0210b811a03046040380741081e414058655800502040300c0f0882030b201d45200b507681c0d00340d25442031030b541c1d144100c4d400ca41d07400c000f1851040d03025100351401101c0c000c2100d980c400d1000300202c800d400103940050551040000240244000e00900269410100d100103004404904144c0101c8050703483d261104400d1880c20401d000451740009140c00c1007440c0ca08007403220100f40c501b15100303100c80d424540e1031014407003400c56001d200c0400404c140a548500001940c036208251130041d8a03124106d500251485c00d8051000000200c68 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 806491070 1250 806489820 806489833
    0x120a0509030904050a0e0f0a290c0a2a05010b37030f1203150f090b0301090b0a021e0304030f0e0607170306130204030807112805040506030c0102 64
    0x1403c1200811001d071420013407595441c8021940710f81400340c1c0b1422002080a08942105802d0004090018007100031184d040c002118803603100300b01685070005000d011b00c644600b00703240180d40540300a0a85000c01003011381c10b80b0003c01c0300020222483c0710364003e02c1265001d4041c01750200311140c0039074810000024108024402001104481d59850681c105580e501d0f00c0d020007038081402d00740d40b600d0b4025030034038030103800d8041d8100c240349040c4902c000c0761500c090389250300384038090100c0b459120100c1c4d4503d583e094101640e642d80040c0140414100080b80d5002540100c0703504071612015008185101000010f480c4650303050f0701c40d0741465020103c21920591a64992980014140111804191020740c00880d030851840e607140e0b40c1c20484104003541c0200c2c0110700442d40100400c5c80094141002e42d0119a030121091540510140000d001c1c80016604840c01c801854200b14808801c181803604841007601c0c20840e0343c032854207040c0c880c0c02c040f403100d01692040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 806492320 1250 806491070 806491087
    0x1212090418121706010206070c15021b0a0204060f0b030a0203180307030305041b0305150606040302030f1c0c0807020f060f18090106020f071701060f0308120a050903 73
    0x290840342000c0301104040351030000c0c598402c102e54000304011030000b0406540ca141104100e42c20a80081d4240018036061915580040000021140040010b001c044d0036421801c0980c064607100503140c44400ba45800d107000751a91020800c0381070b84100c1c2802c40000b104442840301e00147c0c0c060192651a559072026608007950015100d500c0ca4002d804810581c2401400503228541c400e94000c100d03401c06081c400380100e00c529213912910380d03a03101000040d800155521502c3c248100a100c1c503a42c00300028501d020383c0c1d002a4050040f1042c0e071040c0b020200740d140d8002361030041d2035041503202c0000c64041907030040040c1096020041100540303041c040d210208803000386181d25095449515030000d402c1907940300ca0000006a00c02e4103407034143c110601408032031000349561084240100d580d00082e20402b0703249001509541540c80d001c0d0002d002503d11070f480e50040d10f5403480c0110030341e441940b0070a03074400340c1c0010404440c050701800d402250030030f00560801170305 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 806493570 1250 806492320 806492329
    0x907050f07080c100c030e0f0106050105162111070b090d150603020402130801061e150203090a0b04140d0c050f04020904061203021c09060503070216080c121209 71
    0x4a030030400c4910910791420b00a0130140141c01d0090320030b41d404600c01050120203442c000e4041010902a418800248802d99210382a180800040c420061021030b03e82040c00e0329030240c000c1090b100700b4180c17007803038601d810028001041002c1011100390360380d5082003d0540c0a18503c1640c4425480714101c040f0306e510a070211f0400404000281d15a0f481d400501281c3c00003061403c03c035080941007166010030f2003400c00800c51003200428038030300e03140402d5140b04280035a25024104c0f81003546142e1080003a6030980c84080d04202016841d4042c40d000ea4120344208460440030305403d00a50410111118449600c4007403550b026080508200d61a48168005508581c3c2841407500da03a6803805000001d0000c407071402114491400d009040c2548254000308004c107200c1e070b940c1c1c1168807808200071900c075854030a8070b0382c4a0190882c10588031850002211002c5040401c01070404039602007103840c04c40f2522000c40081010b541c542d0f801e4025042101401d120300551800c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 806494820 1250 806493570 806493577
    0x110d021e0d060204170f2d162309010b030f040c0905070503241813170a02072c0414061501120606050d09030507080a052a0d030e010e0a0b060907050f0708 68
    0x5180a40381040c2307050f0b102100d0795101d40e1140d07480c43d1021848801005451072501c15800c820390742c1d069191704001c0c00801c9407202809104034020284001004e000f00c0420300c06c06040b80140074081400c00340002451504162607050040e09203c608004074440d02d05440e990304000b030311240000c8940f8200000c155401041c41407600c0070a6032540001d03007142904c00b200d00340c000d21303562144c3c440040245840f41a800c030b02c0d0340c1249090300c209814a0703420504117051200c0d1040038203550340c1c50201c0002141c080048420701c12134080c004618090484100c9400c0e003a40e800303503510b841074800030560b1203a01c65070000c07510400a20100c2805038002d400181e019040103071a15141c1d40d102074803580b0840c51a0001100400c094905c40300091858800203210b81d00c5540c0c003c120002c6030386078200240c98000341580e8a803003007120a001c0d0003031000c003161101610740c1c100300d5042c00660140219015482501c0a5002820003130040065400d070104510796141004c83c0c541c0c07114002c0c8e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 806496070 1250 806494820 806494903
    0x1e0412110402031608041e150b1909240b03090607020105130219240201050a11030a02091f090303021006150c0804081009110d021e0d060204170f 64
    0x2e01c485080321031040c89070002c603a4901c100895411801038423031807006c84071034802440c800c000b1f4010301c0001c6d50394969071405580314003070700040204858001c00804118032180e0f403d04000040000789118141e00a9441807400c0026030b8065652640100e00f00d410440d031440c6032018542c4628003504250201940e885a440c181010030b42d2242c085850b0314a248050036054191624504074065081c05850b4004004440c14440e03035410002a24007408010702e00340e21141d01059000017590390104200c40b50800030003242d2144000340d00180003210b94041a8098800d42c4030b40d050003891071207603000300c40010040c841c0c0f900c08950221001c0c0040201a100048280700101d01c25200744000102110940340c0025400d41d1480d0441c4101c900c80b07002c9104061190405000d42c80780d04c8010303140e030f2440c03424040044000f000140f203019641d0014049901c08903003c01d2001c240c0032903606030040d0004507600440c0d460140d81d656110b56120490104015a00b10801a41c0d54200f0304001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 806497320 1250 806496070 806496083
    0x207330b040e15010302011b0b0a05060f0d03020c04390c0b0f040309060314150d051203100b0301030f02040f18121d0f061e041211040203160804 64
    0x11102e40749101c1c80c0c10340c9014144110141040100300319a005501038400c812440b2160701d40c12072035190080803403401030881e180d0b103880d000000c0b00356036903500c20804c90000600314080c2400034100259030b42e0100c19511f000703616085e0b980503042e1035414581c550200c0d030306003e048140c02404c035070003c03003840c0c50030300901c041000001c00240b030900d0401e209825000c0c817154640b80c84e082c01420100f0f6039200c83d0506103058020040c0100024003158000750b4130741403000c000d0303c0e100810560300c0032200140c0540140070901ea01110307094015402100490048419644ca407000c5c2d0388148001c0c80b000b802452518400750042c01d00c0c4e0014280d4842c51030f03000502125118440442e5001c0701821140d12810700c000544094220f8a02c00f02c1c4441002000c11a4030244003141c1c00302000044244259408182c210004100403200314900030100b808503256590b60301c1035107464010250480d41c00081c460010720a04040c4266840386d6265081106400c0d5900d4042d100900e0290064a10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 806498570 1250 806497320 806497331
    0xf07020a0e04060f0609050c030402010c0c050301021b100c360602030912031e13081f14041101030506030705041109010806030d050a110304080601090207330b04 71
    0xc000c040c00c410788220b000b020f02203001405040320804640064000859480c50300d018052202c0c021401d07207910550a003402042c03a00513091844a5034540d5014035070543c00040c5052a8255500c1c554824110001c01c60349030000c02c14204045e01e80c003040500020304002c0321801e100c1c03051a00d050306208084643c0390100c010b0003540ca07010b00c0d59009940076038400641c0704440d06102580314140e45481001c1d5040c1007001c0c1206803401c1021001840b010f07400b01c1c0c0743c811421580d200700d0003010140121411800714181014001c11540e0010440c9450044041d80f280c0c045105680701e070f40d000c0c03e1080004810070042d1f00030310000d000503801d841000710100340c0740c4503031180c40092580e600d65140c175111104001840d0440080080b4000c0d0003403070792441540d4000095035000ca0030f9081500400e004000034031b28500a59001a55511401c0c00000300c035982e42c1e0003008814040c0040720303041d498550302c0000b0900d040e21514070000c2034003102803148000c1c0d8000f01c51410010400704a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 806499820 1250 806498570 806498579
    0x11121b0f0d020343081011191e020105060a06090b0906030c070f0c050418050307080c2112010803090d29011418070206040f03030e03031305071205030f07020a 70
    0x484d0b030038a64051440c110388200388482d0008106a00310000021014448981c8652090180e80100401d100c2c0005500d172400c1803c9000b06a0200c0212007240900401c841d1110001e018003025240c140c01101c2c00c1c0300200e130191203440380305c054502180c0c40c45d1030700b091681849503991004200c07181c0090148001000140c40c0711500110764040c1100300200c07400c0c40f00300021158404150b0b02000d040001c140d000800220030f9a240e680c100300c4203038484907082400d0741410700000503035201c00c00e00d048400200c980c84000e00034894a1400d40210703682c07a811800c0c0e8074400d841c100ba81c00401c0c1d028040004080025851281d080c6071050b9401000b08500382000000070380218417110200208001c8600346078072403003a90072007590020f0190421a0000c0c5d201c0300080d00180400c4035005004017414020781018000343d55800450740d90303140c140745111a02d15a001d0880e014000c409001030303190425a103000c800b41e00030b000355141050258150a06d9800000100e8025401d001c0018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 806501070 1250 806499820 806499913
    0x3270105070f02060709050d060510121505100815060102030c0d0c1101030c0906030b0619031a0919020d0b0307150906020a0f11121b0f0d0203 63
    0x707009006540301d078040304500800290804100800200c20052190300401040c1e5a0f012428146508054009426180c0303041c4c42e0840d6040e601708045103040402110100f104410b8200c50100c0070075002c001d035031141d19648004000b81c4c0301704629980100141411240c0c0304007140d030420f40c140100d9140000100206007401075001c000c1d404580d40000410a02c02e440844000d208024a01009240b034821b1028117003c0080c0140d804041c1d070b403606071407641c456604480d9810841c00e409400480c485030000c002c1c0840300d9010340d05848086011016040ca210500d0041e002e600f01035608480d4660781030025040406001820307070300c07030314240702c02d8809104070000f410715094502072001000002408030396266102000715400700c100400480c5405880d142000d0780074010003032208030380c0e00003500524040680306540c028402a42d82001301c14072a917410140a80340d4065240300d04042000c0d000d40d640d070283d0540c011000e2582c00721030320321a4400343d24440450114800c0b0000c000c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 806502320 1250 806501070 806501081
    0x1020f010c02011a090903120901020f0f09040f0b0108060d021f05090a080601050a090f1509020309010c0c150c140705060117031e090a0b0f03040c0812032701 70
    0x1440982d55031031388020760201c0d007800114201d0782510024110f0070410030341603a07440340d5104045100e40354404561040001c0d011111940007812740300c0e0f141ea00b40c240d0760425612080000d03104500d010032943e0014158010841c14400c161038840540d41e42c2030902034450401c076422a40001400540c1e408001043c0000c00440c149699803521590b54200348011744500e1340202900d075000300700401c4281e4690700f080c403e1341d202a0001c50030b442050b0801015214803220031003028013144c80810829041d44c05184103031a034800034007440d40f10781c1081d1031100c0781510103000e181040840066050702a00400c50380e00280c41c0510422820620720b400e160810f0108841d25041140108090f85000052840354000c01d0003035480c18511f070034019000d50140000340154180400c1546281e034400c03189400506202c01d0701d550301c0c000360354000d4940c0d100700c83c1118407248140e00881c400500043e44e82c0c80000c0c06000510350744490444001c81505120b082d0f003415806400d040500d502802103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 806503570 1250 806502320 806502341
    0x91e050f0f090c040312020712020d080720040b040c0509191205010f0501171c02031b150709050a0306050901020403060207030f03050c090a14060408010c0801030312060509040b0601020f01 83
    0x1143d0b1600c0c11446e000400000c030194141c21588000014040c4820804ea100e0006034102e030100c650340700301c0c0390102ca1805600c0025140e10741c0208410030174040705081e0700364050221000c0040200c800c00b0441105c941c481e84200140061241c44024109032140488d0b40c19150b0017a01c07000d03506c20400e41d40e080e088004940e40d035190684010001190f006070390250842483e11045881035107802d5540345c050f051040c22682260030018241c40c024002c442c000014102d400c50704c00c000d2000fa51390360b802c1c40f0020102c44c04d100d000804c4103101d010508252000142003016962070341e181c3d20b000e4040079100502e103560030080003000450502c01048401d110380c8034198201e801500140450348000c05007101c80b0800c06c402c900c41d940b85008002034403055981010400b031102c01190103401036400200c000d41c40d0034494034001d0b41184065040342d200e5580c81c1da654203a80c0c0c85009448441c4078640d0880c151201180c001608007072400e501001c10300c11544030016002c910340c01d403260482d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 806504820 1250 806503570 806503591
    0x9070803041d0105060901080619030c15020601231002031603031a010c02030c0d0c030f06021902010c1b2a150e060a0c0317010b030601091e050f0f09 66
    0x101d014011019100500621040b81c03140d041c0511b81001034000c0c280105558861091031690104540c0512a000d01441c0c100d00302c42000da48402400300c0b00300080e40c20b24054898140002005009044421603483d000e9200d25600680c1d40c09102c0b48030000300445040d40000d11654412a00e01d07015840b007a40a0383d80802c420800140391001c800740e001c4d0140c10401b0300c802c000050380b000648809102d130f0640702040c0020050070502c011216540008003102c09903541507040c404143c002e49440c00c040002e2500c1307180c8080c0180d08a502416003c4003040750b110341d44610704801e0342d180c40c0140c0504660006c0e815041080c110400004041c0408130814104c140200d4960240a40400707034070741440b03400b141203680020604c0c05030180403810492610311440405d8401c40c254007010868100420413943c4449403002681c000f10b58080c009100860b00060f2400d141280401c0380310034181142c240c40c18501407244004030804810f800184850695005480e4107140c40d03c928030030711 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 806506070 1250 806504820 806504849
    0x3050d0c0309090b0306010e0a15080102030a060509010e06151204060e0d05070f1b0e041a150d11041e0209040b0d0b0f0415060e06030d08011503050907080304 70
    0x1c0c0c081c01881158020300c0d80c652074011684400e40b000644141510394542c100e00030b80d51001600030142548203140c1200358900c820000304004150041c1d070140e40b00b01c07014003403240c9503400e101c0941401d219414102c11088045205070403d02c140117046190b50400302c1c44c04200301043c085609050714100d91961340e4070740c112840e5105010542c0c0400d10303490a50710f0004952580d1290b4806003c01400190312154000e8160794038400341d0000340700030042c0c60114585414480340e08164281c450b101030804000252030b501207946d8041c8000b200230810b0301c911440c0c0d2151080c6c10104103ca541003551450709240580202105110010a0707141c00350f5200321030801e000c1070b030f4620414603001d14180c00b901c100113004040040d070f1040a12440ca2816a5142807240700442005051020396181c14004503942c1c034140d8086110300401d401716102a40c0781d030300449010001b4450708084514440441c2d061724403c2d080300345c01044590480c1c0000b52141c82e203905541c0070345c1c0701d194a01000c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 806507320 1250 806506070 806506073
    0x90307030c02010c0f080a08010602160302060c07090606081b070f030302090f091003050c03030f070b130206040b0c0c100801060e0303090a24021b040203041e0303020309101a061303050d0c 83
    0x12220727405000c1c10b1015003243d84401c00030718120681c0c0d000007403043d00003164a90800784100441002004603002c00e02c800f0b40d40e060090001c1c40d0030f4a01603000c00319405041815240d000850742040c1c0c0c0070840c0309600c80180c600b24025000241c10561102d80d64800e00d200c0c0d40c800d02e83c1405203513102082e04d84145180fa202d440d0003007031661180642c0082c403152a105d1100700507910305a0308a00401402d540e50071440603003102103d4000c0d4001e02c0401d001c20180c81003005044d01c03004d80021038402c10280010000000d80c102c2c56500003402000040c00424812501720382081000350440b070501c050000000e600d4121608500c2c65180c8065038011544690592500c0c422094000341140384410450b0148400340c1e82c05640c0140d03000008501084003052030341d503096140304485140c4180c0e03460010b0103035105a400907400c1c400e1002c12103040c0300707a200708503407490000114686443c2c0700c0c051040340d82012200c0c00f032080c90074100001280080c001d400070750703031969a42400c50816 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 806508570 1250 806507320 806507327
    0x1b05030f0d0b04060e073203070203040f080d0e1e0411040801022106010516170c1506090c0f030f18070909030f03050906132423090307030c02010c0f080a 68
    0x10100307000000600840841400300c7c04800e41d500e40c0034a00701c1103a996440c1141680b0b07510540d4820240406d5040b00002c179010003203000d5103051050758032031403044024820000e40e40217081180d0058041004192580d242a50018481907503102c9440d0500d40d84440c3d40d8220b0f0400c03c001000c105541d28100445000c601101d94440802d09151b400c0c510700c040024910f20079000011f2140d07101c42c160360b0045150340c040d40c1da090468012030701610f444041c1001030503411b9840300c1c0504049800708034581440029a01d0703240d40c0c189000c1c19540c0d03102c105010300001400150300092074450b6034040c0304043c040c0310040c0046440220380d0300c00c98038000702031030032a0080713030101860501030201c5070344c000c560950020a040d0044280440078100300380c007275452000c008031244054648240780341d12600006a40f8151002401c0320503406245a003030620110b0381261150020003401c1c000900441414030000d00624021454600b1030b5101c0350082d000c02d0066901e9170011a05a102907030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 806509820 1250 806508570 806508587
    0x9042a0801090e070e0f0703090b01060c260d02180402040803180f0a05102f24040813050301090f021009030314090409050312071b05030f0d0b04060e07 67
    0x41900108807261805d541c0307400d03852018100c51000f0301c0c2e03c004249113078801d800481c03480d41c010b28104403a50307440380090324415030448202c07030811500b0181419404403101071031003500303401e000703a00c0c1200212417a002588200f11442102d0391400403443c0d251241d2004d803000e0128000196540c501c2e0141800d02e4182d05007203103220300c3c0103c0345052a51107031101c1c201258400d6a112540031070b0000c094820400c030002507042c6045010300f0002071050740811807180c4940d0001d54001d410701410003001801039225010398043e0110110300001c0300040240445403a00c41d114410f180c5071030001c0d0943e00c00d001e040e00d011420561358001e52070040c40f808540c10300380c20800015884d668000c0c25090340048048108100801c60110700e46450f001010b450741c0c00401d99035110030086a46101080c00e455100004111540d0145084034200c002080c03942c004004600307168001c21854079030792020345054051902d60f8840c04440d1258010400640000c4a4540751441d20300c400520390607 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 806511070 1250 806509820 806509841
    0x40303031e0209010518031c12240611030f22050108040b0604021b030d0617030301140f0a0306141b18190305060408041509060509042a080109 63
    0x2d00c10000740e0f2803070b07070044100d41590001c200c0404180c0d12280020b4101008107441c030214944150120b03400710342c001c20107428a1800c0d170041182075001e02401a514540100c02d11032110039072014000c80c1c0c0155071802140d4484c0003160303d03000121044507513030381140308000d100012560152150004a003d294050942031804030380901d0b10741c985400b003820140c030b2180190b0f800a001412840d140081da4640098081100e41d1070b911010250010242840303141114100c0c103081b01541400841140d0484102d100001841082c01041028100715031101580c000103c03480000011154060f905c0015098454005c00789810569040000c2d184109080314007010484244441c2c4032140300300008a0540c1c45800c03190709004120ba100320300c0e8001900500c51001000104030040008009851550070b8000d00c11140b03103016120700c2250300031079010440500010b21075040a80c046c0846402c5d01185c2100210407403806040703040b0085401c0c0c00541000014400401c1c540618600e40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 806512320 1250 806511070 806511131
    0xe120702010f0c08090d20040b01121e0e0606010306090b030d030906020f130303110106050a0e0703110a180e0103080f030406150b0903060609010e01171204030303 72
    0x192559000030004644944840140410490802d042c401804241c4110302c00190000304818500e080581c5401019901c00031549840c1d00d1450b6582494018450108010303103c124074000200c9003480030700101d081222003811840140c46840d440c034062038540c0201d440c0602203d0400c81d00042c140d80c0141c001e02001801e18500c1585928000741e1109038400c0e614001400810510700704020b0700c5070840403501c244012503661220416101190200ca11980b01c000304031211030481420313039416114466010a140b0f2040010180d03100010360310007507619001419900c08460ba4050b40c110608140010381c00e8440d0024984c0d00300c40348005032010000144556155a03610319080c414481c40e01791100011010070b042180c03542281c17081004070300407050282c2d00d80318004119080001c50a10a01c030780000300d13055007421440305058403081030031000c182c4c3c20010601c092248485000b84103102d0f8114400300d421000c005800914401e5030003081210840c2d003402c0142008500c0c00622 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 806513570 1250 806512320 806512327
    0x20c010b01140301060e130e03040807120206030103240e0c0a1e12020d0512070b0f09060f090a020a0803040501090609080606010c03030e011814070b120604060f03060e12 75
    0x3400003075060300d04640d02072800c801105440c6c000704620f1554510314050741418800f906410081c0800540140c81d4103000315091143d071382d8900c1082c600003e1000c0d4020b18100010310100f1184050403501041351488589200d603440301c42c5081b18026411501c0b10303000050039800c14940000c40c0001032a80714000b400c40d0041000c011201807040c400c40d021054142030120454960b00ea21010054202040d0340840480200c0809503500848040b070b024240c8000040c4900c61442c01c0600030701c0281c00030030540e5a000401101d100c4003400b0100e0920030881c0314401030352180785060180003d5000786403a18904400500113543d9508014140100c548041c04034100c00100b0503403203002460140341001c400d05054000740308002031402c0e20350900c03500c100183c0a4620360300e11039119500001440b01d690f070505032074500c00c2c060031002441c10041142102074000500b074000700c000700009000f0303a5030050201d50100035401107461603101e2048040245040c000c0c514214140c4413100e14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 806514820 1250 806513570 806513597
    0x3111b07150509130c021f050906010b070809010e060d06030f051002310b0a02010911010e030c090415020a0f090503210307091806080105090a030801170c090406020c010b01 76
    0x44034000c480c4202100c903591285e0203c0e851081000840c070540c40c1000c018110060500304024103000c480021841c8111400041c050603002d0071942d5140d00301c0780c483d050600481c01198512001341c00140e000c1c40a00c5006003448481c03082a0086200b446a5250010145030483c00c01940400398098a0b105010b01c08803da240040d000c80740b20462000702c03010218120840444d03080703803c0381c0002a4003060100a4a40550081c1001070089842c402e0703419000004403905048180b4060b003640040740c8403c900e0400380e0400340c1141c41340800a5948010003a12801c98008000c2000020008400200201d411503103001c040d003030540c06001c018280f0b0340e26001d050403c00300d8400b0003400000245106204884550103428540030820283c03101840c40380141819024400d0307994604004200c003842c00040300040380d0782c141c0b40c0c0700742c581c030340700f01e59048a21003880020b250142a00d00d1105a907801620b0b8030403485040016190251041c0c030501b1200745420b0941400716442c1402c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 806516070 1250 806514820 806514829
    0x1802011704020319060e0312010302131104060309290106180e07050313020406180c030509100c02070b040914071d21120d0b09010f0603111b07150509 66
    0x40d00448900b41c03504c1880071840c081d0700a000036500352103180000324140605540807480c65048078000c0f1280c01c0380ea04114809400c845c6203100001d0100420402000700b2400307031300160145805030501408940c044c1400c0300081074480481c945401c441001071100580224003c4803078403285000c1d01400b800c08084905241d805440c5c2001d01c500400081e1255443c0024039a00950143c070030320025a45040d8400021001448142414280603040ca00948030344141ca1103840c0c21001021259040210440100b02c5610207404500410700007090551903c0c0080c8002c0c6580000003a12486a1150340032075034018107070004020310516903440d0100b40e0070200b1880d81080303c0700040c0d101400c0110ba010480e040300c0c0d511600030761310110b020708406d00260004c003a0005091214200f00400c120f1020403d020b4400044608001402424032950000704c0700280060105d117810710140944100007110354070b40d0301c1540202020701c180b040138010389400c84814105035082c034a0400008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 806517320 1250 806516070 806516083
    0x12050a020402071103010e070806061021090803010e160c0b0a0b24070210020a03120c3f02031b03091905030a02061f0b030a0f18020117040203 63
    0x3a21441e00403446606022480012011010005000304070000e050b82015454401512071400e0078050800003404509080c007841620f6401c6944030420f299525001811600c98292030400741d03540c03240c01e0800250b10400079806003080340380c0c648045c58803040300c0c0c640c0d460ba08212000c02800c9200600015440c014084d0441c0c003421010480c88400750101c0ca00400803404c020460308050f910910b0f076098840101802d0703000341e90f05071140081407000e990740c810858000300001d0f200381c1c0c4035170303c0c0000ba8407200c680c85041c500402500341041c881181d68142d40c00c80d01079200c00d41c240115020048030b105800c03110b112015030541c54141a5850041c4801010307983c200070010010315501400d100b80c0b1a0420b8400002c0220040b5041144d980e40010712008050701c228404112442c810b0340111301864807071040002402d003814042485500081c10004045444a00e031700c414982ca806100d0150000b102c2c40d4000042c1400018604213003185910308030f888000500c0090b03140844c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 806518570 1250 806517320 806517323
    0x503090d03091e32031006050109050306130f0f0b0411130c020d030c0909021b0d03020301180b120a060f1404050c0f0310090b1009020306090f070903080712020712050a 74
    0x10384281041082c0407801c0c5030380c131012055040c09444061104190b9030b80c8940d00703030b030800c1c3e0702d800305c0d030b0707211000d01d5a5140180c4181c0b0700590303110301810005d502c912001030f10b14460b042c0c0f280224070a0b40c80000149c0c043d502101c05841c04401754059040140c01520241d038402014048a00701e401c000e515030800c0c100e0642010b4070340d10003100041c06620300e0001013181060843d0380300202c02501c049019403409100b100e0041d07800d1001e406100b4029a4140d8414568492009603404000002002d080b104c00760000c0b845810740200300414401c40803281c2c05030b80c000c149000d51420580454401c1c07840da02e15a52003805100c0420340014059407100307015030310002e440c0b90250000e0f1070075990110000c1e4681c02c1ca40c0850411008543c440c0c011741c0e50800210303659445000e020705170302040391503903000401c0d100020303e03c402c01c94070b035034000210b070030840d2140d83c4030307110301206034041101034a40c9a00c42c10102d040c540d0421070319008000b210f41001c01e4901030380d281a00c4500b006030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 806519820 1250 806518570 806518619
    0xf05061203070b04080d1424010203070b060402130312030e0d0201200d11031f0e01034115010501020f0709110d0216151b0c0503090d03091e 62
    0x2240d40711074009622183c10300300200c01c00e000c28a0035080c076920034294400c234a02d050030f190b140c8400ca54000000e855085501c00e14104056480e101404000e4003c1885020907000b030708c800101190b440c0c48409400c01c800c0d5004a540e403096031440386401010012582160b2402780c100051024072181041c007120320480203a500c0040c2d41c00d0501400e20f0b801c01e1214070b4800010322890148807899a810403901c03501000549a90340102401e8150901c0701134880c941c0c102d82488007010034854804120090a842c290840580701f00340c0280004004011940e40b01d04900c0c0d00c20750036000440e0040c0350074401000c151801c001d40d035442e108a841160307451030b16800301541a100b0041030f119428880c00d01191a0036085001c01c0c14440094400c0d285a00c110a090819641d40d000e07c00703403d9412008141c40500004044031805105801510039001c14080451180d0302c1c3d1107001ca60502940d920b0800f03a082804110400321610948580c0940200702008900004140c600442c503010a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 806521070 1250 806519820 806519827
    0xf0f01120b040c05030a150e01060e0a1a120c0f0a050c0106030b070c060b01020c010e06130e0f010302010f0f0f080c070215180118030b060d060f05061203070b0408 72
    0xe80030060250701d50041d0b409030030854944041903100000e14440e200700d010031b02007109044051a901c044031300440c41c06118102c01400b2541c000c2481c1d00040101901010b40b440e03540d2030302450104001001070210000144120200c5c3c100d04100c0d422200562081e464460f03048210ba0306442a00d0b070075030500c000440d4941c0f0310301c0207501c4007009607040100190107150844d0014220088040125007641c60301e11a012194400a1040c200c1e02060b1107500031000c142c4100040c1d40c02803107884485104501d000f09110340482d1b0300d140100e9074000400070650451002602048004915804000c062000000b280303a20030201d0b44a6201030030f001119468a0100b4841d512030001c1c083d400098440780110820f240c41c0c000d100049005d10200e034008007002c0112421900b01c5204216055200b0040c40452075100c40d558105500500d200f5005400b50b41ba02e040d00c4420910300320440d46d5508000c000c2c1404070b64082c403101d411001e585820000d81d1851450340001d00041c140f0350010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 806522320 1250 806521070 806521097
    0x80a380709060203030907030615090504030c0b0f060a05151e1207180e0a02070f0b0f221e0f080703080601030506100e011107030c0503070b0a0906050d020f0307021b0f0f01 76
    0x540a84015040cbd1185c14000b0380780604000d406420081c1d0b044a6050300880000c10f506168500c8038050703c2d0061092050a00d4101000440e240c0306440e107030200e400f0012030f020308101c1040106c801a05500140e01c5da0102e0b1070321501458010003a806120101c4802d040400e400403d02c025515a80c50b424500c3c2c03a0200b0f104001d028003030000302503600c40c11004e0280542d600b030071442150390307407100d10f00c0d60b4950803490285044a056800182d04920b85040001c0d070400b00e41c003010640e102280003800c400c2d10348800241e02d4110944194100280c20350034075500c00a041e0340304a0a08050010341444c0b00880c61540014590074104504141c40041c90303031046480d69900b000f00317012030f0390094990a020843c840d140c4601c030b00c248a824030020741c8018803415107407058256216100c40030318101040d03c00760710419868200650810800103031144100146028025950051084150022000c00d90142c0c60303d0551180c07610301d0b501c1620790355034171882d01c3c103680a107000100f04071403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 806523570 1250 806522320 806522351
    0x303111204170706030b0d0206071110110f070308070f03031103190b0301090317091203010e0916080d0f09030f2a080a3807090602030309070306 64
    0x84480e4800e8800240081d5124100700c0c601c041000c008256222296905400e40460300301d000b1890b00502241c031004098078190f00a80701840c0500896000f01030610001404241301058200200b4000c8290100c5200100082c012400107030005121142c199258400107011f04200180840780d02c0301d00c901054807a810050310460000e107441d489042030701c8040c41540303040c0b4103452a585400c4c0307006030919050107120344403034050700ca105c100403003070700e568200f450000d240400350320800704c0d1040c4400300c0c0c0d4010b500801d2410f500304d210b810001196800c2a24001c00f80c000000114000d204a070b001042d440440031150900462213261800c056070a15415400a042d581d8200315140038008469890b41081e0182101c0c80f060440d003414144c22039202d4003030030f5010b07440055900d002170020641c60304415035280c680c1e00002c0e65415078148039104490200c05800f0410f040c480c036903402c0082c01d009003165001450447c07800781d038581d42e01c040f584006801c8076103800301900035542 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 806524820 1250 806523570 806523583
    0x70c0215090405040503090f030102041406070309080a05060f280216060f0c081f0e04080904020307020f190302060f181b0109150210050403021e06090d18030311 71
    0x50142c020301251820b41481c07030712034111500b81400b82c1903854134a2914581842120b0590308961400d86500030048188500d0f41c1003110102d0078003010340c0e80412a2407007044146040c42c810401440c542c81c00703005100c500e81015205d501000c41400c20031005061120b0400c03020071a01d01e0050725240d0b1941c0c4d540c2c070700c00048006001a41b8044104a04180d1600f1100440700680c607022526240d001c4007405106c01a80ea91182c107901c101709008a05031682c15a800130700404000e401c000c1d0000c002000c0303074419904080580d01400c51100c0c00541441a86500308154140244019903502c01940314500108030503a03004000002441c44481c10a01401d1850300c40c08071482a161502c041a910340000707103040c0441c03000040000c800e44410745405031492140c0c003402340d034900c100e90131001c5c10380907104030300303500440216100280d9038683c5a4a1020107000a00481c2040344e0200c1c2080c0d0030b0f0800e00304021150070300d00659050003009804803589498156049104102c21a05110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 806526070 1250 806524820 806524837
    0x5010503070e0f1504080f0f0f0a0b040503040528060e1305060a03050703081e0a14070c0503030c0109140604051905030d0c03020405180910150e090f0f06070c0215 72
    0x2c80c010138404030000d0700b81f41c032655403800c5810742d510f51013007190740e00010101c0c501d40e9488991410002a911410715070401c0c400d0044a00b06600d40e400a001760880b81001c01c00c50034038030481c02560300303c01c5460340240f0709414845201c0400074040313012030304990000e00303c02d52210f000c203115031103290900006603004001d5403034242e12450000d2060b804079184030b04204120f040d100383c0d20109002c840181404c0d440d980b5652031400c014141a03004580c007551740c042024000181074800784024044089039034000100e943c5071341392045a0f12041c0b1402122540142c040000041c00040d09540e003803150300c0700e558100d100b468200e1852051510025075542010780040410b609a005403050fa0021114501490880014000c0d85841107410381d41551004100d00a0f03008154003183c64030601a4800f160a6120a0020100c11003620041c0040d40300d11011002850b003440082c1c841040070000d440c4e00d051507000101442d43d40c20000e0700c100c185c0039120b032080c3c403039808895050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 806527320 1250 806526070 806526109
    0xe010509191e0e0708160807020109051209031203060d230a0506070f2606010509120a03110303040b0a15090e0a05070b04080307110f09040b1005010503070e0f 70
    0x110b51444181440d10b0521909480314103400200c0d0a807800368000a21507442444800d0504040000032074115002034800c5042d5580c80c40b6030b41c0856000d10409400c10540508555184002d03414546400c10a001c0d40d0010403051003400b0259503030003881c640e40c45e00110071004244403600303c1c40780c0d40303c82d540701136191007000c0c0800d04000300403400c43c4c403e20654491004110344c40c4010b680c0341d20031013809520b1021149445003c103000c151010340102040c90700b6420315010402040310b0000981c0301c00c039982d0003000c0f43c3e0209503114503518400720711903000d14154100703591030b441181c00190030384100c152580700c2c1c00042807524140500518010700b09026100c00c51001c90b4880003500000d54060040000c042a411030b9601228219640c050003035181030314684403403d600030621607056108401c0300403443e13070b5600c1c4d44060740264050014041c040c2400381d11101c0c82c0d14281d1099040c4003061007000001031300f060202020701801c0e150480ea526200000079030780c0b002c41c99080d0f5a03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 806528570 1250 806527320 806527349
    0x40b030106170105070206160806100e040903030518010c170c1e07030206060109140f0303071a01170601031112010902060f070b09070e07110106090203011409070e01050919 76
    0xc2c62054110500032034113078007644c207a5205c10001c0d40c1c1d06003004150320041041c490226100d410008051384401c41b01c1d00c1d01d440c00905900000b8162441e002058001a40300c205008420710140c14008400801100030004d02c002e111015003e40c0070f0b890346080303142003040003403132040050f8101c400c8002100688a004c000e00d000751f40254002c40400c8e001441000d00091055018005420030b507500b841460000d54103a03000c002e40c405501d540d6581501040c4211400501c1400d441a0a0480d4a090750030560405143c4484120f01d0100d60816030300c88401003011400c2000900c032809070645003c68100030040840340500b0007030800030340000340012910f0344200004090014503109070703503030f41150b103640c00034640d210480d008008103018480045aa1240190501c40098601400101d80d15560f0441c1d02c0c1242c009030312101441c03140784181c0c00b45144c46060550b000d8401e003490792031103480200090441c0a6041054010341014210440000c440d0408200070841409681d44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 806529820 1250 806528570 806528609
    0x15082806180c08010e06100c1506030b09030403120c03020c03060f0106090b09060f2d070201080109021303121b0c091b05070605100503030d0e120711040b030106 71
    0x41c14800c034070340360116450640190080c0e44900d40e014100c40302003c0480207074841004102c140319014401c0010308c144001e560b40001d5041c4901030310340010000000310f031031450a01304c01107038001704101903070340040206200061204859110f4890246031a6201d81d209180c16460304240840d903039813611a2804208041c01884061416600961b9a420042d66500106941c0340121259158020300030700910141070700c490083c010103030344030b81000302d806040c0010b500142c40100e4003d0750700400040d90001d558001d103520b0300400740583c0442c51312000051241c5602035501000303014580080f080510103100d01c10458940c10818403c0344145e0b00c07407420f04004109841091100c60402d4100038081c20603840b514101d820700d03158145020b02c95a515002000014844044500014400700d0543c40c100040c101480500e070000503100d00d0201c0c0c151405a1344444000d0421040069100288015040030080d41c01540c0221f02c01054000090151074281c0011103601030030700c0c2150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 806531070 1250 806529820 806529839
    0x60a1505031527151e0f0d0206040305011b05030402010215090f010c021011040806040305250503090f100c0b040606090203040302030d0c260901090b0709030203010615082806 77
    0x2405201c00310501e205107110b14060215004141700c10741c5c45649684644c17060303410450783d0300c04d06110081c50032404800c0d55000074125081504152202d03036540341c201a44681d00f900c81d034104030a50a1443c02c524103540000d43d100700c56190915401c480c1408980c0203403003003000c00b1743d04101000a0148144510b402076850020105500c40181001501803510300c440d0221010fa030800806001c9964460724159800d03400b03120402035160044407000e021102c07188c5200001b5200d80061030f07841d941041000502000400350902c102c1e0042d41035900181c1041019214581c807900d14040f50b51107080c12002001e0944c040b100c05030000040000301907001c0001e0030102840c26041000c00c0440300115800740082010750740d40c440c45640881c900303007249001030303002c1590703400840c2100990303440c43d10950f002d980d12804103032950400d004500d0203000d0381d8003900c14a00e43c9440c0700603811005060307907000b8150049100b001c0c09441e4001000d038014403141101c040b420320007070b030340c809425 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 806532320 1250 806531070 806531149
    0xf0b01090b0301060e011103130f0303080f012106020c070b04030308010b040510030e0c0d0311070918020d0c080706021e0c031015031406060a15050315 67
    0x5600182900c5004181c241000e000d40f4180d80150f82d0b13402d59205201d0041d6807034036681d50380b4015844180803000c902c1061002110190078180c5403c4051840c1d45001703001140c3c05040c0b801c6080f880d2005000e250582d10044907450b028408041403203c0608010b0300900c03440e5601083c3e40240c82010801105120085c412a03110b075440c00c44a83c0d1320200c0d20840e0046002e100d034014010307181c501c1c4246c403a4020300440b010b00004d558003a040c2200082c0715840c2003a0480129585004401220500b0f00824005117000c070401c0c40010750020700c00e070600046a0000784a007409412480c10311219940410151007400112801140c65040280d0b580c004c81807801199201442500308409003c154900d0546003c1d009180c01300c5605c98100c0a8841d4144040e2140031100000020982d9025103651100b026000780c80c1310b0404006111800c546604041092640e00e074070500e61907480700c11241e00c1a01c1421581000f420310700001d804060302000005241c00185e1254150180b40c0e000c2e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 806533570 1250 806532320 806532341
    0x30408040608060303070b07050a1106090109060b0d020d020d080c1905100c050d0c050f0d150b0915030a0b040e031201081c05090a0f06120f0b0f0d030c02040f 70
    0x7005190383d01c0a0070503581e0310503036400408080a0001007007201d4050400340501c0c4130281040c1c02c806450000c903030310f45280cc580c10100d84e9110300070101406900e2241001407642520f00d246060504e4020842d03070000110024016400701d0581c0c018000084203440c40500c440c400d40d0850484011049000c3c0c12020b0185c80f2800348820940c2040c2451060207580c03425a00c3d150300f0001044480c6008000c2444104244041086032846d4102c0c15001080c00d4420040001028a04a00100c040540b10380005a000d8410000020180d03620200149100c521011480d520fa5032088004c01a20f01607040310781041c1090040c0200700c0f0b010001d010350540b0540c68003081d0f81d07a003d80c2e558400d81008100400803001003608480d9110303400500354468003812029082c0c0e6903020607040c4180303079408900010211300d1400344800d003d0040400e4091740010030700c40f245c031082c0015160903148036024403486001c6041d5003014029111b00c07040d16001001008a0f0002ca4070504c0581801d082 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 806534820 1250 806533570 806533577
    0x14060f030f0c12150412030b0303070317072307050609070503061909020a24210905070b0a09260316020103090b0906101d060409020604030c06090906050609131a04020304080406 78
    0x8c001c1c1d50b5080000c01d607144240c240e5104103c024802ea006842c4070801f925800c100800022600c0b10b40541d940701c01075400b00c144803103940f0710050400908042002d000308083d600300000802140d5800540550403101102e11000e40c15040c41c00c02000b49035030a002900080071070800600c0075a400c0e180541402804082044d4074120142140c40c0108131160555007103140140180141066018910b100e11813421506165229846410190002000c4030000750301d0314418090010642c10803c01903140380d071481159143c842010b0b0300c03805070301c00000e1040242c0110105683c4660400b880030394005140741c009044c0801502d0300d48008445104400c4130b04000082c0c06601d0323031407807080c1148540d015207481c0c49920400014100500c4160f9001c54140b0010021070018404e4a008116948980b101c052508500c0420380b00f0720b500003407195105002d080643d0310b0780190800420854880081c14503143d044241d01540c1524940340c0040c0701000300401c108040b8001c3c0155216500c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 806536070 1250 806534820 806534831
    0x40e090a020111030a17090c030304090f061205150a0212040f05010e1902150910030b0a050a12060e10020d090b130503070f030e0414060f030f0c1215041203 69
    0x903c5076600e02c500740441c4000342202c2140401c00021000d981e0700078224809a550242d01080001d1454206400c20307a5078a596110803e01d031103c6118540041003041070003a0f80710b14589400e6110003d0015501d50140318000068940340c507035045440300403080801c201d0031304083c10002c1c1142c400c4c0d90100c0e82907290400b00120200d00040c81108074841d81d42d8080381280b245d09000300840c00f44e84100d0102000c0c010b1400a03644c1c0c080c0115040f1440d54001880d1031400d0401400c1c0c80d40342c0c80b01e401624135100a0041040280580d01391541140d03001ca81002000d0300e1030314003c9008904600740f071021a1a0500e00c52903005561080c1c0242c1000c1c509880d0340310107000c1542c8440005065a10070040240018100e00440d01d50502a0410080b03030520000481c09407500107150b00104110a800c100c590314004ca90044001415002405004c503800036941d512000000001e11456140da04003041c50300401400310344c54030b500021400ca041c40d260013812130440d2044103000c00d0600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 806537320 1250 806536070 806536097
    0x70219081f020408071205011407050705010b09160c0201110f0106030c0b03060f100504030c0b0703030507030e0705011b12080f130b010b16020d050d02120c070614040e090a0201 78
    0x5000366004d03104008003406a85140c00c0341910b6a4a9040c001c480c19500d840303d0f00110001015072510032203030b6803525607031804285031460031120f020706c03024440c803504405d1101d812131100441c0001056400c0210100b003140c0010384a800340030030704908510944506060801d419003208080740d2081d45a00c821584414086c115404200d456503041004404001580c1c80d203200414264680d9080a500d0642c41c2e41f124a01d0807000e8200707034807000000400b0001c05074503108080d0300000314a010802c3c0c00408031030079207e02d4a40305488c10800f000b541e00c40c0035400c3c25403020b9016407241071042d5440c126400a07203c03003012a4030b030000c1c16444000401c907805444045001c207500c90010003580c5e082c440440015005401051417441c014610700005840300e040600c48035016070001c041ca0940107030001c2c64280d0300f01500c81c100b40d0510015180c45000602081610802d00b025103e0b4004511441c130303240195409103503200340031820711003115008521009a103000707985103c08034002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 806538570 1250 806537320 806537383
    0x3011a1c050405030c0c03190321020d060f1409040b060a0e0a060807060f0f0f09090e0a020a1205060402040c020a05030a09150c03270b0a120501080703080d0207021908 74
    0xc8600d048d0700850204080000d01c03a16074000850807003403800c85282c044229400807a0800c2800c00801a926102809208800c00b41d00008140755268002c80d8071200e8041a44908082c100030802c22001c0302040b100d030303aa14519000b400c00860502001e1811580800c05044544900c07400d0f40100640070454502c11840c42281542c2919145540c400f584011503542c010300c1c103000c0c200446801d01241d550414000c5071404a68807004104800c02e0740100401c050055011803143c07401030f04c80c04005080403070665440760b0125000208042099400da00b40310400b03200520074000080d5496802d40c000245c04180c8a0302c1c92000000112050165100051303154080d01080348140894907407003031600114a4421162040120f0541d11008080d1a8110010311400b14013825100c140070302242c45294010701c1044004c0501c1803540d15070700300d03a1082c600020703880c1e60001034050a40d2a2102e000401810407064480004c0d52003680a44841c14800d00d14500903040905507016003e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 806539820 1250 806538570 806538583
    0xc0d060f0c030e1f06050a030b0a050603160311240d0522141507020d0822030521040803090c10090513060305010606020c01020d020303011a1c050405030c0c03 70
    0x301c41c0200840c0044803010503180c440030302251210303502c4020215041d01c4020081c0002d61149a0200d124202000135002f038600060070580aa40540c164203101c285070210301c000c5079001070358902148140c0e00880c890b036000c1d0302e44442a03110325086900070041c0034000e04650b210190100580e4644001c000d9292440e5408104e0390700105d01c804000c505000340400c0b6a03c0c440c0c0c201c030302d11417960388005030341d040496122016810030303402c1409083c0c000001d02c2c1c0c80302008034a0400c40304101c02c015004401213a02408100307002c10190a074016441032004050780403600d03c3c0d40c0b031600d1b141901c4e5542c402c070703020012402407800105242c14400c8501003068141c0e119002303070a00b49800e01080e011180c2110301000e0f250000040030030420f02c504d4000e013040f64081d00a0715425000603160800740c2c8840400c5500800040051152a071180c02007003a82d020400d0b500c0080300c020504c20760b0850444002e0a00e400148002c020300000240f070700040e40303019100318003a01001c16441c1c03030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 806541070 1250 806539820 806539841
    0xb0603150a090203071202161203020405120708121e0705030406031118090903091206070807020703030f0f0309080a020a14070506040918290f1303110c0d060f0c03 72
    0x403185000c0203c8240c031ba4001e002400418400c10301030a0b083d80b1145024180c0f40c07210b2000c654000f40074442c50502001a4510507103100040100924150a9958401e80703450806801d100129101540b40030038618008072109540c1500e894203840e0500e00c0d144d500c14429070700402d16085200c08841c26010030f40f601030021900301d0911281c450f081c401081d40041c1400c2441c00104a03050055070746410300841c018409000301103030b140441c00a414207801070460807e56100080400000c1c3d40310b00b58808400c0d41b49003048450f580c0310340a802030148810000d1101c0e0b40802c41003001075000500200c0c980c01102c201c090040d08544003900c902c500c4c00b605820820030002401240e0140d0003107a20b80001486243c40c0d2000c0341c80340e61100844030120b04124a4401c1150381104291424507040102e0040c0000141040b40e00795482d0020658014140040c034020035080640c140100e00703801e10054020f41c8e04410524180c8000c107189100b00c607000f841c001045002c10b2007031040764101c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 806542320 1250 806541070 806541077
    0xf030c020c040b0109120606180b130b0a0b041805101d0c30070206010e060d03020708100b03010f0e06180c0a0b03090118020609130b0603150a09020307 67
    0xe0412100b032101030400c0f441400e0501204c9000041c28440303441d001c00c40d050248200003480d904084441480f01c58200103000c40c3c038180f05000c0280d9440c4212825031254804001402c140c5600c0460840903003680000c0382000080340c0001c1c52024029078142049a250b01000300f5940c80b90300c0f10038104903001d44030040c242070740b43d041c020808540c15900240c40220341401d20520000b0520803004809403000501d40e00c2040c206103401c281c4000350000c0050019080d11740c140709810410a200402c0b07584602021a10301c5c0a1500030300c142c2c1c014001c418281e1f0280f0180c130500501601801d0311042c002d42c60308803442c1c488403051043c0d030344280c030070000b406090301c44c0010b019000c0c502039558007a6000d903c000303140e00e59401201d4802440c028501e240c41e850134003c42c50849503889255a8501c40004005005a036203000311240742070300f00e80d00c04452070440188001040d00e10b41d000c0d04660f00105024044200b00d20b0390803030200403103518081680707910b2000c2c00d9010568a80300803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 806543570 1250 806542320 806542333
    0x25170601030c0b0c03041e0503101107060b01032a0f020a120f02192402030702070603021c151a040609030201030f090203010203040303060e06030703150207051603080a0f030c02 78
    0x400743c104000304a5507041c00212810300b0344903038081d4007503115951030300007516645000300b203642130a208582040282c4101000745201300c5412031004d1143c007a005000903950b28419104d40e000351302494400b00c0c08010007061500d0102c218a1109090051001090115810038403441c80000da03074500650200600090cd0304401d0241d403010790704042e070801d40c02070b0501d038181d002301d8070010080d117405001501c418980302c0c00c01d03007a158101c0c90081c2600c0d004004015100ba000140c10040b1001c5240059588059004611410315020340d4940914241000078542402d035000702010788145010460301d0803000c0c0d4180300b180c4030310301c10400851040e00040001d50301a0b4000214071036000c41c00301e0f15145030b0707002a0899004031012004640c0d0313030200344510392442d0742160780a0004d030010a10f85041d6201c1000c41003000815100e0650000b5800003005814048c00c48114000f203001446151a440c10303232002c0c0c02c885503a60014250074050301540c2e119000300000790700580c000e0041c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 806544820 1250 806543570 806543579
    0xe011a0f01020a0b0a1e0c08150a0503011107021c02012a0605090a0c0b041413020408030304051f0912230408030a1403220525170601030c 61
    0x5000c0d600e80d6140d0541c0112500780c4041055041e419105885129000814140d00045c0350400c4a10440c00f075691483d1802c0880c4454000480d66003208610b0994401001014000b0300e4082d0650070141c0c01d0b508051820310380340044409062007074800c9030451140d1011412900201a00490280c0025800c00c103210f00c001c14bc2110b5951031811a15407203070318019840b04400d0b07400990310a00c4585c0111205018030170700b141d1510103045804101c501c0d045c41d11142d84580804081e600c1c2c89010034220303030850110340d80e0403100207094400659031a86002d081440e2250070060030a01030120701e40d84021459424450b8a03c65644034401507502d2003d03075400c0b01e0424000c44001e410b01041c001d4040d1a60020018200030a0b0150086030366002a550007010300c075074500003603203500d0140140080c01c3c580440794414041d1008060403490f142d4184549008000c1e01088a040044c407000401e042100c02c0103402d85960035031541c076840d07140d141316544141c24031000c1d18612141ca404e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 806546070 1250 806544820 806544829
    0x1b09040221100615020c09071d01050d090c2102100507020d0f0b0108010e0c0907030209030a08030103081809040b0402010302090301060e010902041505030910050c0706050901050601030e011a 84
    0x101e1044007084a0080d400e450000046600640201c0191018030840010041d07040102184d500c00c25102c514540c1403c120107042d040c0d0b81240000d542602100c40401030344101d054841d0400c10410902c41d0416506145040b003103640200107c60044c040d41c00700c030050018280d0403907035024104c142400350080c03040340c058000d80c0b000c80e803095102980e2804501c00850085807079000748140d42c03a55241c004600d00b11004039031815900c0e080129122006e80d50800020340c00441c0741400f607551501500046d0902c55005402000c1ca800440044203004010001e4600900c040065440514080081001c01c020071a0001e02480ca100c0000d030040d4480c0c0c010303100c2c4102c0900007081803520703070708021210a0241c1105c0080c90707000c1810012111912250030140200b41401440d50600d2822180c44452101051030314a44400103d604e01090b40101c1c0c00081e0004020005403d1401c2243d000e04001d03105140024242070718811040e0041c8504009412681c02c00307001d036400c1c4410f10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 806547320 1250 806546070 806546119
    0x121303020d031503080a0816030621170f09040606030e2d07080a050c04050f011e0510110d020c0a030605041103430905060409050f1b090402 62
    0x9118210ba0300004c00215244050711840c0c0107074481c60103902c0d107100403520306203a40c0300d000f00305800d00e0f0f400c111384510f03d010343d40ba85160b20345041142c0180c0c10700480742c1e1f0702c000041e080030800113002c14100310745402503c1031403000c5505228007903407408100c09a82c0c2804000d543c41d00401d207641e03840d050782800b41c0d141c082c0c0844401401e190100c182810009690300840c0c80b43c102c100c0d0441086000d004542031440101c50401c102d04001028508580701401102c8000b2144511070fa4020401001013000f0540208025a00011800028105186510700102e00e1051003c620b14050010a11a480e43d1000c0d00c0c140c02c4d540745803154805050f0103082079404200340070020b05140c03400e0003c00c044079075032019249442d5003660140484c00e82e0fa4500d804c8880702540c1c60300f60841e020800411504010404550b94941c400001e004011138103000345640300701c5040e0001c1c0071010031086030018400e41c08c1d40490806000340101b1003000c99000750310050050540c0100000507515 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 806548570 1250 806547320 806547341
    0xf031602011b030f050c12240d1103101a0f0619030b1503090634020d030e0111121e0c09090109090c03020f010e060f121303020d03 58
    0x124a80340c0e88807407041c84042c100e05030360010f502c0b070071007a2101e4080c3c018550001c480e00d00d0700e86050300030a80c42110b0400581f12403401c1107028a10407507035030f047c0407032664044024000d95580103d441e189402c980c424a90710f000e0300500034500c0070002d4500c101ca4a1a094081c01c1d600340e5240c500304499210b04a071620341c001c0f0140030f84104210407600c11750200d03080d510002750301201c060411044c8040454204000d1000b0001c00014503000319405070800c00b086d40c6c03070200c003121600d180d802580342c0e9951039100018808551449a00040709800e440c000d48003041042562210039003a90564005000202000c000e01003403002e901c01c441b0ba101d10403030712103030141204103009000044c0075034000c805988003140c0e0059a29042d804503005141a003010005040709541e140000d818a10000c2e100700b0310461450b2039640140d400104144000744015a60701207080c500b00c441e08800000301318404020005145a9180c007220280182c041d002420010341c084800c401820600327a8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 806549820 1250 806548570 806548573
    0x2060c0a0201200c1c090513060315090606060912170c06070207050103050a02090904060b03030f0c0114070507020a09020d15031101080a1109091f0f1a0f031602 71
    0x3e0350120003c01c40200c80d48408440b01665403400240c0403841d00c42c2d03003400030b0800109120020441504112003800b1600d094855000103055484040d009050a07070000d01001d10b0070745506d8030424a43d2090503918801e840400900e501c40300110f031744009a028810006040110329004100c20702e0762221003200405c04030345446500c2c00e8403801c1c41c00c2500c40a0141c1d12040c0107212a68050086543c8010444021421b225610001403000314014101510309551001c401241e138a081c812100c40030601c002d0550380341803551070f050003000d0552146550340c00d6100403c000301d115004440c002038004080c060007070b04001e5128007d40c0b00045100b001580c48140511490400718060010350184070120070041005001410f0448018444030186140000e02c2881c151030f0343c10340b5104041a55209c82c0d0f5603d140203000101004000ca20324818030140018088050030130120a41b4000e00150030340c00004641d0582c64040c940310200000320510015410401e01040501c40c10344510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 806551070 1250 806549820 806549831
    0x70b1b07151d031306140a030b030708161701110712020705090a090515010f06110a02060712141204021e100e0f0f0a0302060f04170c011b0302060c0a0201 68
    0x1140c80c0d601c080b0b0020b540307900350000314011401c44030100c3e06070010441820842130601428030a03070b81c24801c0110b400c09041d550484030f4240d407810061000a003c00b0001c660314515480707040300500c60310b4462502d461001d134403503800ca141d060140058022000b681d10382080d10640d2a1110714003c81403c904610406000045964643c14000e000c0c0c0951100080d182c0380b18204075081451041c1154419252200100b11280708415040200d03105441c102400c29007200040307040000117807002c0d40c0a680443c4100600c001c424460b0f69003005a02d032500d02e0556620141a60b000b851a01004560083e0002c2c0141c21b0001c281002d000750311414083c604502400202c0701203944103c0800108092458511401e2450b5440010f06040f54607000c054200c8000070509525800024005c0e1004180e040c1d07030740d210b002038038007812240321500d020800d0000781a54441e1415601c600040110400500541c0180320308154250035501a108541d20204101d1003940030700d010303404566950 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 806552320 1250 806551070 806551091
    0x7050304022b020f0d020a0303030213080f0c010f02070f0e22060b1c050a1b15020a05070501030624020c03030a11100c0f0c030c0b010b070b1b0715 65
    0x690354109102c2ca1a1000036090303a0500600008202c031403240ea01500200b00c0603000750395004101c20403298189805641e40b03040d0000108c0200299000c0400f41c4595400070120701c10100314050406001e0b60307929070302d1201c03c40882e903038003144c481c41c5955802c800c2c0610045078441505a0f0041010101c130300151081f030041003040c820b0f00c60984035581d607210390090300d2403c078100740a940c00302c510482c00d00d11144c50f619201d08164000801905242e0a8542d48020540581c4020700c2c400080a8a2424000c00a5200c0540b80c0045681c8d008500c00801c096019104440c19a44850003d0036150001c810307940c9500785038200b000079481241c00140c990707a0100010718980c199559440740307840710556294501041059215201030520220030074081c1d00c401e030b210031041c0c54a0030203010052801c05480c1c80c40c501101500c003014910011440c1c02c0f4040041104912400c501001da40d90902803042e03103d0000c0e99000d080601f001540d012409001d4910142010341c0000107524401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 806553570 1250 806552320 806552359
    0x20d2c060403150c02070501201507180503010216030513180204090b030f060f100806160225090917070609050607050a211508061504060b030705030402 67
    0x40c0d000f207891401c4412907181801042c010140c0300b0b4507600041001c0350402c2c0000c0e1920340090200d0090840409103c50600410401449004005c80b0310301100d00f416280208058908242c0b601a0b006106c2c0000e56401c0500c210740c8000c3c400006080b55410b04c0e6401c0300d207035012036200c80703600315005400f04003a01c2d0603c0c40d901001c848000143e407103140081580a0300d100380d607503504c40c0d000174004604c44a00032036450380c008144601141d0b540d440c04103a19600c80070303410803071040c4280b00400c0301154884005550542c0d9039021114140628501d1550100300801043c01c443d082c00c03801c021402d5030350020799006100b444024142e1a0030703d030501041c0c002076000da5120b40c80304055018020207010036134102031145052407800c2d01e10341c3e0107004c036098144042c06010310141074002d0000503a00c44d59240001990202204c1d0b42c0d0f01420307641d003405486102010386602c3c07601e192440c00b48120030850394948030386403d699030341200340c07200d802c028005d0b078006510320201e10314000d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 806554820 1250 806553570 806553577
    0x318060106022a12100e15040609030207080d050307080c0306010c030807121e0b06040f0302100e090a1a0604061b020127030614061c030306050406170d020d2c06 71
    0x200d00f40105000c0c0c0600000c8001d03105402c806d4049034000001008400440000495005030060710200d00c00d602d914080345000b40d0307588443c5042c001d4004202142d58058011405071986aa0780010754031003040440c000d1106580312130100c0c03040f982e504000790003032035116070000190801d40c90004500c840c00381a26201c0d03244444070b00540010800c11515446801405c50007030b5201030a082c18645401480b40985c00080d2042003580c0c1c3d600d4616200302d0805201c0c0b600502aa42c44d4104421144e02900c009444010901c090207030103c2c10b4181407040e01c04444050ba22640340384142844a880810344541c141d04105c44801d240785c91107012a15241400440c81d1070080c690324508141007190140000c4229001e20402400720340c0e940c2c80090a401c500070a02d12459030200d14054006041603030029402500303104001845c0b9440e03540c07160400305000e0644510080140007240c13510724807401040442c00c2e076000c1038130206208210485480c84816424114608880050365a81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 806556070 1250 806554820 806554849
    0x1803070f030f12020703030c031d060f0d240614040509071107080102130e06010309060f0e060a05010828060f091e0305030112050304030b0c0318060106022a 69
    0x1001e41204008000d142c3c0e0f10300e6412911440a00a02d5081d5075006002048814002d410018800317280405990984110100303004002d040c0c964444458443d80b10a4002e0040d0120300341c41c103688a0805040c0d010014841520f4442c0a41002c0c02c202d0140d50010700c00348a01034100c400c1c000407440e615501700341809020b5a440f10f0fa9043c804141c0c0f07d1600c0e800c3d4101000036401441180d000001030140031090701c100d00401d030115661400120700400e2510b401900560500c13148424410140e80070007070345441c09060352000d03602d60503150b090311400e2058183c960700072109900341b046c101d900f126030010100c0c4071100e018016118001030f255001c9045514030381e21682c1100b08201c410782c04d00d0703803080340f520094400215100580540014805c03031881c070f600f41c0440010858107108032409140c1c040c3d490340170303810441c4494074070750412298030f10700c0c54074055510340c9000002212812a15240c0c018104580c94103014078815001c52081f0008001c1c020821180c1e03035a4518011000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 806557320 1250 806556070 806556083
    0x512070309081c05190e04060306050601021e121605100b011b1a0601050702150703091d070e0a03050604141209091f051005030105150405061803070f03 67
    0x40d0804802904150031440300c22a100e18496800f00020b0300107003610039400160340040f64490b4892002d544180401d000154407502e4000d01000b0040c1c03940c49140244070a9003202d15000c0708506280c0b25024100c55010b0952202801c080d890394844024049a02e103000030410440d49075032040d01c1c0140c002403042f1369548812040202c1c0d41c1c812400d600401c80c104405892451503150020f21207880c10010b22508082c1c1e0008486034010780443c1c2d403280e40500020078030000c200390354425400502040700001d00d81840000e25859180d1583c81c03c3c9010840081e180c3c4a103541a501c0360780d850402500608180d50010100e103091001511590007003181e11039281012840d5810000c034014840440390090020b129030f5120242c2e000d038010040030581070114020b1509028607046680305070b6108281c041c4e13201800741d2180c09103048690039503480d000d2204103d54085940a1801944d070403520610504a4a8088003d0401041d502030203071401c60f900c4004040c0321000c87d420a80c1d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 806558570 1250 806557320 806557337
    0x513030b040302150708070804050c030f07050a0602070608130f080d050f0c030106170606190203070c0503030304020d020f0d0804060521070c030c0302010e031309180804090905120703 81
    0x103054040c13288000503042e101d2090500c1c6013602025040c400050721000801c40780340002020854204000b4280d124000c0803141d409880e40c821541d07440f0540116030041d01c402e84001011400010b00005642c00c6448000440e0382d01840344107081c820074010350391a00c0c10782c4184003142d140c800a0209600c1950003207610302e41044810204a000707050100151020801042840e41c018982c00c19900c0882800503103440d03100014685009040c960414805031513100070402d5000402010885d116000706401c7eaa500c41c101a02d0b03000440d0080d4005040b124000700602d0f01a911400c3c40c500208056074195107600ca104040d003040c2c00540c0840c400140144030b036107207841d00da050310a1000304804245403030000180814042c10008003446400c1041008150003900100803600e01001107948a0b623540000c2c0c44080c3c038912030304020601c1c14004034124032103c8080c0200e42c0c1c000003890314052602007800010440c009043d2100d000c0e03181c081c24060940e0004124643c001e41c0d41292 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 806559820 1250 806558570 806558573
    0x80d020703031d0d110109051504020a082d010f1a040b24091807050d0615140c0a0b0f0402030105060604081f1404030801170307210513030b04 63
    0x8035880c1c0340141c01c00c40c3d118000780c2120034001a00796808980e07881c2c407400344080100100c0c05801012402080b9024101d680349080300d4115039207102d28000c07100c102c00a80d841140545586014500c0b01c061071944840d0390002da040800e6050641d0224000103501e0b013410003e0045510faa0394903020000708c109040d03100d2419000d881d20380a011554140900d1965a40c40b88094940d1a420b403400c0c000b15120f402a40c0f4813040d02c440b1144a0f001890901d4802c100602a0f4010b5090a01d000d2800030b001c02c0c01d0411000b41c0da1030f41c401d5110010080c04980020b0601e41020341826568072484401d50f0028942e02011405a0b044c0d400511543c01c1a01c101800d4940081c4424000d0209101c05c10450000140383d0b800e88403c19038046030181039010340707405005001c007024207078030614042c01304142d402824a81200e0f9101c0601d1032100759107180d01e440e4452520060000c05103915519480c01d00d10700b0152380380b410790501914140548e100000c03801081c0d03200f0b84684a40004010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 806561070 1250 806559820 806559827
    0xf0d0b0108010c030c020304050f0402040b0301061106100302030d080a021e030a18030807030b040207170702190501090521010c0207030c12080322142a03030421080d020703 76
    0x103003c802d5904040c001c40340d15200003075a074095442100d2240c40e00540880301921503a048401070401c1460055484da107030745014092112a48034035126104040005612664000c50030302681e43c010090a0700e604950002c6031200c0024113500134440c1d00b040a20340c1c00f60403e0318440040364011115445e8602910344101b15403008080406d5401044d61007400281e00102e02c82c0e0240c10b60038001040040400450002c0c0500342c00100303800040b02003613003240d0b802000f905029100315078201060708142d02e20580300150344110740c08214422414403003481e140942d200c0c03c83c0301220b00074440c0c0d051b100c1d1600b5990003169050150300064030502c1400303000000e60000e0255200120607030012030f5110712070b61100824111100718031904900c000503080414050003070304441c1264403403242507902c0303480d001ea143d484180e0254544e94100041801c001d81710003001c1c001c1c065030a240c030381486130607103681c1c1c00c4408032001420108000040c00400c0944281d200007000140c5400b41d0b1300d0081d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806562320 1250 806561070 806561081
    0x171f08150f1e0402040e250e0108030405011d0d03081906031e02131406091503030711011115011d012615100f05060304050a03030c02032802120f07110f0d0b010801 72
    0x2c1c000c80384814012b21803aa800001c48084840038078008000d040d004108002065085680c60380c0128000c6100050560110030640103141c2000103d40386030000469070102d0744035210040602d080d18880c07102501a0031000f220403070018000502918a0380884c2c0d04a8148448000c07020b20304d030007805850b04040483d10350102210070702090440814000960340e000c0e000d0014800d0b160150000c0b00c9034451003611641503c9101101c0740840d846800541d0720a0900541420900d203504003c07030030500e01c04080c101d40c00740202c455000c05c10f961400d240d5071544c101d00341c944a07007620010711500e80e4840d01d20a115215102103100e0805480010080c50303603010a110326401d1051002040700441e415042660506002890450703c100c2a41940684101c5001c0e890000c1c89200040320f400403504a140c15660907110513601c05644600140554090100c10302014010b42001514645243d58800d04c020000195040000f001843c41610324134101c071006008001000041001d0058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 806563570 1250 806562320 806562329
    0x8070e0d08040e10030c030f0c09051006020c041802090603120705010c0206060a0b0a0f11010e1b0405070c060b03070302090403021e0d171f08150f1e0402040e25 71
    0x1a241c40311710319254020050702500003d8071480441101d07404001d50500700c40c0044c00740c0b0304240030502d8a07400c50000b0511500c2000050700500c81102901d02e404d00c12007205040d180c164400a4034150203100c217811005150a03011b1040d003100351142d4505001400d50345104400100701000d03003590080c100000946000d001d1820800140007030610402a0307141e07600307945017604405401070003c4844964401c0001d00075482e080852000c1d00700414419100e102e25505841c3c2d1001c000148411078170121340003c00a02c44c000000300140054210407440140101103030817442d10b0f030300022038620050b03804072301691007000300c61640c242403c890070320007082d41e01400e146d0020100240495000310b540303c4945090030001030760041c0502c000c050302403882040040040d125400243d4035a4803440030181004080c0c0019100440041102c2c442c40840343c850004024202000001c6071000c3c2c0104d0780b0548944014101c0c401c01c001100b0f8402d101c112400a11041503106920b9840a400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 806564820 1250 806563570 806563591
    0x3020631060c03030209010e0a15031d0c01051308060a020304020f03070b09040929040c12150b030c300109080414030f100209040b190608070e0d08040e 67
    0x20200140c1e07030801034008840e501030030056580d48070b000040341d16002145900c0d40c00740120102007a0780201c0c041401c03c1140f00d0b01d0400546020919070040a0101c1807903007441d610038610310010354031031400f9006903011003040d68440790b1554419410000115880321240354044200815031034003d80601341400194050121a4280450310400f8410808058010360b225031900e41044400c04098403103030b00150603861250514243e002826109881c15200d0144d12030b0040b80000e4084415038040743d12606050182805882d008064446002c0d40c99144c080c1240348100d036101c640000c540c0c824001c003098910014580440b66811100100246c030303038509075107800000c40e4581150103403102c0450380604040701200081c036190303610300341e1226406242c0e0f40e8100421590090080d1711002c80d800d1102c44001070a210004074030940c6040f90346003604040081e035003c0c1001039004000e604c3c0c1061a4041080410340d00329100c001110042170005042001000741f003c2d40d03421041e082c030f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 806566070 1250 806564820 806564917
    0x6010905011b02190314030c0c010914090a02040503010903020d02060108031804050405071d0114090c07060c02070803040b03101a072d0b100e0c1c0204030206 70
    0xc5511a4698007040b00034050500c106031110740c10280301c2a48000c5038481400f1078420401581603489030408940000d1a11800ca0301c450258042d42901013510041c500416211444004201d07000e03c025002d406442c2c1c0c200070100d240d48085c041d00d0b078094001d80007800c1d54041c00000a142410582c8040101e03042400007480220001c410040540c00440c0d010415454074101075003042140e90200d11100010344424401c0c811003d10581210340b045904040d005407242404001c2604035004001d25504010740d00c0000c42c0da51020712420101d10403100003d0b01c03100700381d242da4010307004000d400d0008410444010140209040a480e4002c2507030007011408010010900400c4401800303c01d903403c401c01142c006a05840b541c000f40d0768482d4600c00e0a04108103a00310542e0032036520b1500740c1010444400c20240240580c00700d18107180340041c401544c0788000320340018180102c2d02000000b0151340c591000d000c000380324400c08a460182d810502c0c01e5065141d0183c0040b0f0b0313508 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 806567320 1250 806566070 806566097
    0x90a0b0a1709030f0f160f11030d0806060706150609091104030309061101090804030b06090702010b0a12080706020c25050901060f0e030604050d030c110601050607050a0605070302030601090501 85
    0xc004e80c0c4640780f01142071525481d0b09850b0700f002d0301564031145c010800284003c414060303c2200e00e03610f18000d40f0701c2c40d0a9464038050584644440941c0c2000c02c3c0c20602142082c20003400900b0b409009840001d1403074030201c02c412040225a0081e4000b031006d26091102c0d06003071090078a028a0482c0b0380d842c191641d078018000710254401d8000380100c408a20304000b41c00e4000e011400e9001504a9032140c81e45800003005200f61125402000f0b04400070344560700520411082c01070042c00c0280040c9031005001c0c0d000c132000d90844085038144044000038600b030000d801d00c0d042120160401103021401c1811940c40c0203010300070f5404200c001c00454840600300350544404e490a00d03100c2c40441415105101e01e0080c0039018450502084184030000c0341d88082200c6a990500261810500450b84e0b5046c01c81c1c001200e070030000042200b8030302030000740680c2d03100d0410756a4044041c1c40d00001c40c0d60807500c02020a8000007009025a403011842001c0c0509082985005101d07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 806568570 1250 806567320 806567323
    0x809030d02070f06080c0c0601290306152511010f08100b091203274c0e0a05060703080a0e0c031605040b03070315050408090a0b0a1709 60
    0x8901c9100217100c0c0341c00100d41b509002c03074101da0400300180d08071001c0e07507522100d981f200c0041440b011249440000380214192442e0704807401220300402940099a10b54030046859120200502030f6513404040515080d80320007038142258020554441205042000036040c1c003500c0114108000c40d00007040044a085540c910568210250450322150300c400410500074800306410810311002c90307041c0c903401c641c11448400490a0b40d82c448000b00170014820099035081d9103210400340f010910400c2c0b11149090182f0342c0010000080381c45500341c5010342c0e0800648484001280700c81540010306082c6004001070000f51542860900e05440003480c50b5405000104042c2e203403c81510000310400c84900110360041c203443c1003070111202403a12a81e24801c541c0624101250421540f80101302602101c1e00010b0f03c68040c01d038a021070700142001042107440301c1086c80500c40319120008150007803c104141c06a9440951401030f00c034180007a440074148802c40c00304803c0080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 806569820 1250 806568570 806568599
    0x50f01080a0f0201020a1a0a0b0406050f0d080d1d07050d02011e0e0a0f08010f02190507030909060e0103200f0f0402041e170a0f2004090809030d0207 66
    0x20065210368600d1403c0c0f0040b81004581e0001074150a5514500f0f000d103001100060b01400c0615410801c2400c05010300041d142c2522078240c0c0801d44002d280c107103040080c00100c0c454031500c0008d10b4031a0078441c4c1c400b1561484106a003c42152008400401e4100000d8015060440e08242c40c100f50741e0000348014684144100b0300005000c103050703860b000e40200c10030079000038840500e454558180c080d0018243c4a168010740c00c210040e5221991403084800400714083ca048038800e64030f406a0f03695000140032000c2240302000050502d040c1d100d03407000b070910344010903070b035500d1800c1800d03150601d09044102600360002c0070140b581d50060040080005480003110001e01100240c024002e0340d211511502000c10388540040c1924071700002e8981030006508548405407109550703085600300100001c803010a4080401c090b0040080d010520394842d030740078000140841c0650704c0c8544203c9195a020424542030701e001e20222184180d64802828a903180540118682a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 806571070 1250 806569820 806569823
    0x60109180f03020307060c03050618040f0308060105070c1211010e0a0e0603011e150605040803090f040f14010f081501090c02011b050c01062301030f15060e04050f01080a 75
    0xd40001d1007504050003802070b202403c2e04802d04020341460302d04040d0213003008483c164802d01c507103107a100342c203070807031203a00d01580d08850003d0361124103030341c1034901c403e01038000d605006047c420071340016405c1180070050802c805641e0030354251807814800c400d08a0607200e041c0000451691010b45501100400b141e483e1041c540c036903242c0b10003290060241600c14002d40000b10940801c142150b0448031042c100000910421075881208031550b000d43d000350740c1641c00811011045241504141c1c0c90164000d100007820581501d80320100c62060380b440f00301201c12401000b0740f880b0910258001c003030078000350900440101d02e581e0940814051020101c1e590340407410414402d40c80b40500562500d005a100045c901021b8095081140300d0300d050742c01c18001140400d029110b188040d80c0b86502e000c03c01d2520b0005402611004641400c00c036510042030040c856030802410040c000c6458030400d00b14290280020364000410749041d480c83c0c0700041080300c500140c0d000805 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 806572320 1250 806571070 806571083
    0x1205090d0b060a050607060203060f0609030307260307020c01030c02120d09061b1e0216052403010605090406080a02030327130203090c101b1502030405010b0306010918 74
    0x381e0302c41c4001540400c0f1a001150000c00210300042000103640c0194003030b103404c5484c40d45444400c000c002442c4035080640d50150818400900010300307982e091140d5280b50518403260044511709421740e600112610801039100340356019503560188146651004d0502c080d110011083d0000c040b14429000c500c0340b4503540b00461000e101c20b41c2c1c00281841c121882001ca11110043d004000400f03d4030503e00e000000780c3c800700c2840c000220315001420508003445c40c180b0b40001c00101b121903826800503500810880d401e003c04002c02076020341090380f100307501e03104d0f200d05000861f245a0400303440d90344601080070259400009540110251582d482120400d85035240c0443c40c443c0007031900b120f02512141e51140c142c0d00558032a04800040303d00c810440c0003040b45e41940900171402143c0449001c41080d407040c0081c501040c000d002c064440788100c900319040768400c03a001c2d10a6551855440743d0751030144101c07401005043d206002010700c20507148507000086d040205203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 806573570 1250 806572320 806572343
    0x100504020d06150c0b0c0a0c020a0603020909010e010e010e041110031d070806060d150f0c0e03030702010f030222080609060106020f06070f1b0c05040606050a020c1201090c121205090d 81
    0xc40e20416001409a501424400d0300ad41d64041c05400381d000004018071541e960400406c0300300c192002c4a040300e01662a00c05180d10300381800c003108102810684044e062100b0604254070b819a03081500192950001000d981c0000030030944403070f1a6403240c45d03800c0b41c4002c006002c400680181c02c04402c54800c00013900d14a0840060300e04003440d0503042d0306080041d001400b40b60300000c40c0303066a448440740c11940d1801c040d241c0c80340c518001c1c08a800d0151309a00b4500c280c0c043c00d02c0e1a2100d000d46201c10001007401c1c2441000d0b030042080d50301610400201c3c2c5003c0c800c003070040155000510080c03440c60512619490020444410400c40c000102545131040d5808010b548021403009100805c0c0d0030441c000c0e5031315004072401982044800100b052041003110b05a0260345e001d070408150240410100c200d2001503044a9034884140002065820701d44034001c080b05100e0550581e91442c0a0b000031001c4c42c0820240141800b2542003625104e075a00f0b01c00c0c1d88108081030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 806574820 1250 806573570 806573587
    0x7020d1709031006050415180b150d0203180303090a140a1a09010e0c01020316020f060c0d1b080304021210020f13051c0803100504020d06150c0b0c 65
    0x240d6000350024940d142c07140c80f0204407041c5480e0700c22803d82e00e0a55090207030340a9a01004001e01c982d01c40c10b40d04c01803044a44080c0200d5521022400c0c20080c0810000c4500d48040009030b00070f0202e809807554000103001c0391803000b49074407c03511440c2018600b14680004000c0d280c000e00903029007400074162610b00c0820061003503940c09035100805140b206524200c00c90301402c1240c44102540c60200c429942d000d00117901c40c0c401c0310590041d4502951003110305000607010400f02c1e04101141d400c0300d07069480f20301400710304000030010038210301e00c0d68004000321314444040804450143c114804540000e0469a1050b010340d200400f501600341c24600c1c290000c04000d022038400704030401044641e10090103144446e596100460744c070745040010103405840460703200300f0011502c90005002d00003940e4060030103c41c0307505060740d94020805070380c0000c3c0c50880715a0395600521194140b503108040d160103c2c50b05c0710b2084450f0b66000902480034105207452400404c904a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 806576070 1250 806574820 806574863
    0xb0402130908030a06170a05060a0b040902040203070c0b0c03060312070f05061018020310060e060c030a0c02040c02010905060a05090705060f0307030c0c0f030c06020f070f0210020307020d 83
    0x10308440e80110b22540c0c0f40f6000031031000401a0f40103240001c0021212800e24600000c2e1f000c280350341040c003800103600e550320904020f25100101d01e4009071501414805039a9030b1000c0e5125400303d0320307a001f00034054038000440c0b801c010b0440074280c0040c0144240d03901c2c00101241e0080810078130315990385e5103041180403c021270800a05603c910b804220301041c14007410340c121810000c00348102010405c00d030041e070000710340000014982e9402001003d02c1281142d14040018121500d0038114100c41819607010806500c0031a00c020750b078100b1401c0c24070907141c40c0b05592008018564442d03035543e0719004050082042c0e01c0d10792000c01c800190620401c3d00602008048696a0402148004003604111500c1c800300c3e01e000c44900b8840d003c1c04058800550001462940d9102654243c0e800441e41c40180c0e4003a03802d100110541d103460000b001c0c00c0340505141c0341c20200c644108405c0b1030310700c00c0e00c90440d00b05021003c010f0721100c58041009a00080d070080007a100e08800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 806577320 1250 806576070 806576081
    0x605040f060c02071406180607060e07090c0f0e030307030c140d080f090607020709050c041208090a091a04090501180f0c0524090102010608071d0604090b040213 71
    0x1d04110720b4400c2d9a0002e940009400303084403241c2c0800584a84502c0402409000d00c03c08409040240003426200340350600040003e980f04a10010380c00d04c0000101c0d2501c012604540d035900d55031040c07013110a80050140b000c1c80541c1c5400c0b003190540901007074407802415402024001803400c144200218a840d5410400030741c0d0460300040614180202441c40c180e585014140b03581c0d012070384c82000811050710a03107954008000803031a0446620092100404800c031a0340c0034800465496415070200c4415401048065150003220b401c00490381001c4e407128406500d0400660209801421100806a4212000200141c0c00d00b007140c05805041c0c081580000c100da2544c08018550400c089642e0042040e566000d03110310920104400804480c0440c01e004488a4140081d0000074507440e40103200204495a50f582113078a440010740040c1483ca590040304108001c2c0040081d5104408403010700c406100360f110303007585840190019000b07502c01c820700d10305000f064120 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 806578570 1250 806577320 806577323
    0x103050702070b03090114010e010806070c0f020d0c060315181d10060e100b070602030702210318010204050f04020f040317131410180308040306021b07030f0605040f 73
    0x59507245049000603009121140300d4501c032548107c00480c401510380d902038161680d04005101d561509a02928003851299044a01901110700307a00140c44001a10038001d118801c8001c00e9810310304080d003592000c1403805494120b2341401c00032141400b6000384401501c1c2d00004501100c180c202c404d100c07110703401c2d001c103126000410341840c0280d03100c90121120301070004820348442e09550680c2c4003503c140025441e00340300708000310711541d0003560000d80900482e000e500c0e24281d845940382e4003207120741154101104002c2c0001040140d0b98080c141c00d002145454103000008180c43c803c454070a00403a400b06103003410100c80d01c1220055500544240003038200b40448400319440000807402001208600003003c805024124550800081504081c407100f0f40f03007118240c210541850440000080010100794403c004001075409603601583c0e41915550b010401c40903142e90030346551051408001140054480fa8007696010501041e19202c45c00c1151450035178840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 806579820 1250 806578570 806578589
    0x7050c1003021e03070e0102161a07020918010c02070807090e0c130603030207050108151905040f0f050c120c22062118030302030603030d0c0815060a0e010305070207 73
    0x300b000c61211030000c1e6100301710382d9131b8003500c483c1e54400482c0c407030034004020020091007040078803402500c1c0da130044101c03ca20803d28200481038000490001041d140401a0f04000c0c0d81004d00070400c7c000c04144070014001081c95502d40500184d6030347d01445070055080e40d800020040010a04c00d110782c43c00c00802800d00c0707240d001000c43c02404a88002c6000d4412190000b1302c1d94014040c1c58400e00d000001c585508030640c6c03e109158590303142c00385a007081c010300032615907280d01c1a1169100c85840028a29807a003100c2c000302c2d04007400005203400300740054030140c80701c620425480300c042d05189440704c13000226200c862400d010303403500c25000a5000300b078060384192070a00c200543da114400207011022003401f205c15140c000c9000e0035440c1200004240603400131900444041c04603850b100d8840c0400080310700a10100c4001054982031280c2101c0c0c80c20500c0b800107007201c07514070b0071136145005019484074640c86414980c4990000d40b11500902000001385620340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 806581070 1250 806579820 806579857
    0x912040b0307203301061707030516030b0d021c06140906180708031c1a0609060901121d06090d050403021011010e010e0f0f12070c17100b0607050c100302 68
    0x200901055211300079280c14400c0c801c0062300e01486801654001c55040910b03140c61402c09070202c020703210a03881950001140014640142c86020000c0b0f014030307045030514440da03007a14050f01543d140020509000c540b10082c040c1a15010580b5a00200452070405c11245014032290615801d07074402015400082004009100016420f0914810b0300b0000c110108000c5d0b0072143c4d450700b0000c41600b01409000640342814198010812000b05050000240c0b240005010a8030b1480000d21001c000024004180040400c18503401c100b0b200080c0c4103280030a20001c00030b000c0e07448064400c4200749101c2100341e00801d07240c000c10050074004c0c860304205442607406000500800d06661080b560034144440c8040f45184501c2c024102818106103070901c0b2034503940000c07500792040c03504000700003100c0e16800215031814a002024040392181202148210740100c00114001c8030100100d000090740400c494801000c1214a06070002044804a0090050f0b4000c0c2035031601e0320 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 806582320 1250 806581070 806581079
    0x614071211070c0905040f2a150c02040c030609021605070501050a0e060904182a03020918030f0415030c111e16031a0901021207080912040b0307203301 67
    0xc44142340085801940c80030101c2d5a070200c042c000b4040800c00340014810120303c00140751640011690712414903002c15255102c01c0003c04a0f03000e42c3e00c01c4010401c882804082000a000c480002c28003402e00c542042e4070550050f0405141d40556841040c00095030302072076481e9400f2103460250810075107450f0103103151921402011000141030000300b03d41c2007441080d504101000e8a80c064003a000701c1e1900f08040c0b804540801c210100c600040c082e00889a0680c070140c0000c09040fa61080001d00e01540581101d040c81b44020401c40343c946000074509000070707002c50f1200002c00700041420180720150820400340c04c8507804031140c1a0000c00e010303408c03c4c901480302108070070155a80310f1f40c034041e00701c0c800c1440d820b120039605000100d85c180914922940321501205441260407540300d43c00150b841078100003d500408400c4c03100e0300c0c0d4800b050034600000031020101c0541c6079200b06a80d1204040e040c0e100d4018002020700c080520303210412401c180b100151202e5865 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 806583570 1250 806582320 806582363
    0xc1e0f0903070f05030a080903120c030304060606080115050d060f0f03060e0a03020d0c08070602030708010e06190b0a090807060905090c0306090c070614071211070c0905040f 77
    0x4003100600c00d1041a10200e8414029000321040780d0300240140104d2440790b0341c0c61515040322600301e0b8903009500d4186a1103101400610405081c000903550701d04d0130740340140c00c48483e03070400e100f005404001803001e05d144002c130344060351035400d02648a05540d00c501001d0080703034011000303074102c00e60002080307540c41c00d1310001d0f6446003e042c8144034003012002c2e91803d4010018005034004404401e50900030884041c4103070141c15203920300940e94039281e00383d0780181d0b8180c002070900c0380100100000c00d401c050f00480c1c1103444004000c0c49901c4201e0b0012240079089600f50b00003007070240e0380e0048111000802105054030040b070b64811014020200c648580c030700403c641d1001429100005003282d1007410300504c00980c9031244601444a9040810103c600a41e00c0c10001900b551b01809107114079469a20b4001c40c11103450440103559980d401c82d007003450203010703190014000c0c94240c001d55202c0c010000f01561076052036107041140040180041d911543c0d43c1220300079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 806584820 1250 806583570 806583577
    0x60c060f1a011202070c03110117160806010c200d0c03080c070b03130b0a1103041124160f0f03031551020c10050a0203030c1e0f 57
    0x3090f207030f01c04407803940c001c40d0003a80302c0e4860041540308411000d00003c2c64400c0709085c0d002041c54400100b00000440701100303801030b40c00440c008488500892010350200c0d000754001002e207010400b0a0480c0c1d0303080000d0242900c1403100d4612011300302c0c00d0b03840b10040c602d05c054000c581000c81395564104040e6035070010003c00c12502540c480424038451540c1101e02413440c0c0d903941a40380c041074503001005803028041e0031480341c40352400c09400725100095400345000e00d0143c00c848405000f0862100d500120160300000d4040c1203c00c1c1e80b102809503034219a8441c14944035412510b044200800208001441c4188100d040d0040c0742c3d0652148001c440c2441001004030344503c400041c0054002c1001075074640780c0d0314412a40081000c41c801c681003905107910f030303c1000307440c4081c04000000a00050344028120062407904c01d8414100035054140326190510180c002900c1c1d10000b064440c61413800079400e01c8010031084000c600c40d01280c400d07900d510300e001d8036814590 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 806586070 1250 806584820 806584871
    0x4032a0b01050409080a1101020d11030f06010806030c210703230a020f01030207030309060c0c0204050a09030c1205070602040b09030f0f060a0e030c0105150907080f01060c060f 78
    0x85a08004070b1682014400c1d40400e94020b540c1a0805d481d01000300d4031040e2503009840195001d112204802c0858041c084085401600300d40e1030346410101c24081350401040c5504110001d4103104d069180800d680c000031505450070a2604203043c107511050401061041461040c00c90020074001032400c0b01e8200c1c4c4001548400190410f0b6250390384000490b000383d84034498000020a540c002ea0040c45010302c0390902060281e90794541e1821241150307016030100d10904240021458244142903108951803000c104e124816140101292695940280103c202460406400d401882528405640200d080d990750751160f00740e040d241c1000100d58040d106078110501100400704248142840d19001407860740d848529003000350038222007a10f030500082000041c112401e001c0c980c03250382c0c4110000440542c0c8070070300100e8000108408100031100c800e02889068030000503044600318035142100d07091500340803004042c1c0840b00305c440751030282400c442e118800354114060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 806587320 1250 806586070 806586083
    0x10e090a1b02060402220b2d01031b050306030a0c081c020a03020c01031a0a2c01030819051b0a030906050c070512010b0303070606140a0e0a0504032a 66
    0x54140c4140d90724802604d009501480403800d90100d80e5200350014511652800e01103010b114680105140901e5050711400c8001c40d078032400390341c002059031520f0301513007841e040004104070301d10300300c4451201480301c04100001000c12800d0381e0400c0000c240b41e41003420100d00c0756640c3c601a5a0740741c0142803001d14010903484400ba680041040c400403501a00a40204105c0c400110010000c41c0645141081d03007443c1120151183c44521015140c0c0070360040100030f0001d00902c480c4820180c42c501e06508100500000d200307103090b00c3c0e01803074042c00c000d64030041c814151128080c034843d4550b04100102183c003500c500141881000703010f078031183e016540328481110f03244600c044403071195000c0c101c10409401c00d242c90030180c940110002810356540800281181d00118081d00c005499000c2803080d0760300105803001281044542c180403a01c0c1030512507100070000c04410010b99500d0006051500030310500c103a00e480c0405c0892148018540e183c41c6d20303115442940d81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 806588570 1250 806587320 806587361
    0x8040f0801020c100c0f210911030106050d032a0f2a1508040807080c07090b040203040209150d05030a030c1d181f03032007030b0a0b010e090a 63
    0x20901d80c5d22518600641603078442001d00003600090f40e02e860000b0704030070000a1250014010440340c031801131818032880c0d0301821034051104060070b503034a0b5000f85105004004103000006e030003545026500c111220074104035183d80c643e00208a02d80741c0e02034015281c00742440100311110150031042030b01070300240c02c0d1031740c0074200440d1540c89000b81030a292043e080d110302240916002a0b00034410b040c51403a144040d40c0d4442e2036004440c1094040e84440410301560031a40568a00d1103401d4030304500310700d480d400141d50204060410107050b21440061420b07a12031940c105501a0407078104c1e940c0710b815110080080095201010019101c40110040340b000003800e40406840246444d0b01d800840205a1904802504c0c60010030824100c2d520f810005c00041002580640c88810038400c290030000c00c141c01c02c03444016590400c540a100056059a085410108100303000884592500058941d05030403120b02e5030000c901001c00000c54242c3d0005008510303804540c41c407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 806589820 1250 806588570 806588593
    0xa0f020115052d0607060525020c0402160506040b0a0b0909070e0717040c05090921090103020c010f06051c0312020d0603020d0303061a0a02150408040f0801020c 71
    0x6140c0740500945501919030100703c1c14010f072040b200003501c4056110116907420b0900010200c1d88400301c11a406502c54082042091500c4202c90740e001010420960440016074001e48507124811280d1085da40480d040e180030348004000c00e1040d9000c002c946a909081c104142030300c104503401e80303a182c180707041c2c00b0301400c20300e071018094010fa00c0101505400c100d0350b072150600082085040100c0b40c282c3c100c525000c031075040c1c041e038000c42004240509042c01d000e0b01c210003c2942449501a4060018160030301003a000c01180505c086a10b0f0780001c0c0040f00607104655a5142c558200310a0419907421640f2400846000301e80c50881901041c0705120070070410a030107008107200704000240030650360010724400b48080400100641c50350f0015841c03e1810805a00080e503442d02403004c20542c8942c211a0000042454189090280002e6988125440c0540d46200010103d4100035444007aa409000b0f9500001002e41c0c803000f03c2c1d4001d400401212645100f11705078580c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 806591070 1250 806589820 806589851
    0x6080d1b11060307081015020c091806070903060f0603020f0108090f0d0e1f0f11010f050405010203070810050a09020c070506030115020c04050f061926060c0f1902030c030a0f0201 79
    0x103141a542c0240c07880402700010012102401002c09620010b6039844003130140d410300c010742c4145025100d0b03698040c02c605040c0e00300c903c02c810b000780041c9441c500f8005644c0d00201d40341c1d0720030b0900c1c1161490f941d036840c403070809503c3c1c588a8800d10410014032040c40c0c005661000e5580c09442c40d4410000390b030740100c03000c040b940c0d80c0d001280f501134a0b082082c2c81100074441500144001103a0b007008c00c424070302110000ca5080e10540d60120500030078680c0482c0058000c0c010203010345006040c01d0005e803c0046034031407850401c2d800260000381080a000e52801070200410403a00d80d81d41d07500001c000312180b41c4140c0140618030503640a4605807007810301400900503140380d9036170f5841c1401800c4010b05420001c002145a00040c0704490804003000c07840200f001c102c0058100c0f00461901e04080d02d06801504188014004001c40206683c108181009154082c0c5010f880603030031849800b1440501e80800203c610300950405401001c011603035000304040e1040012a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 806592320 1250 806591070 806591099
    0x10b0310141f0b0705030c0d0e21030d0b040912020a15020f09040b030109060f02180d0206030a091b09090c140a0614040e010f080106080d1b110603070810 68
    0xa02007502d088014003009100e903010f4059a481035080f2440e0210048204d46408d05200d842800600c2101803c40756040040c9000d115205424403d1290010461140c9e103d003d04421100310a42c0c3d150f000307145231340b960409040190428042c031610200f59500a440361122607050f8bc0c2c00c1076600c105058202540308403060610f00d901100d041510711810403015020301000a039141d0b40300c600c00d401142141c402c3d040345102060005968110f42c0f00070542d001c142c1c030640e503c190124001403000da01c40200b00d9910001441000079003040c80e2401154401e507103003056080c409a08400301e03c2640300d600c22115640541c00c0340201543e103460354184040360b11300380c5400c20f4000c9010080d01d401524441d14010149000b03d00b040e440303031b01c0184003241c264004501c030780380d00404200898080c0b0861000c1c00304c04000d440940d00441020301622103068111005005a015120500c0740e920200340ca90038000740840d0b600c0c1001c0400418114082d074003004500700000b4002240c0c41c004042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 806593570 1250 806592320 806592361
    0x616020316080304151a0109080313030b042409020112092301062106060618120213020c010f05010f0f170c04060806091009020a05060705010b031014 66
    0x44603003840d0740ea0740e5420a40004d00b08807512041030301c20054840301d50146c036540c1e90740280c801800070307441000105100011345c80303101590001c025000c00495503203640f00030760350002191030680d20740d4a0300c400c0081c04820310010300402200c01d80482c201540000031558002d985507501c144e902e060f0082110400c50004050405010504501100d050101e06401d4006000050700d541e840c1203200c107018410b00c501c8139550803c401181013007590311074080905020314243c0b50000c50300c0b001a4441e10b642c0503028450804411800071940c40050403425054588401d5407030b01c40c1803a803607001c0c0c0506c0d031040c034910b42400c001003107a24071000341c0b80480341202a4002c5072464045d600940809640c042d00d8140221000139501e603c42e401031800512000c0002d001d98a01601610300b06031440511405807800e250540b405070343e80103904410b984044904035507446d09860200d0040400c00381154140c042c2c0070100165030fa05522447d505101c03136041c0038150f40c2d041701c451007030f0032422003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 806594820 1250 806593570 806593597
    0x30d0515010c140c0a1401180602070b070f020301021c0e0c010e060a031103040b0106020f010c1706130929040203030703180801061e090e0a023006160203 68
    0x155880400c641003000c3d4030b0710a0400c01e49845028410100300d050a641d00b028940030204a034101032541d02141c110513036826141441c5409060604c029200c3c0720511038241c5003034000c1a4201401051900c3d101c1c0203600900840da81c100d11009440c0da049140f40408031140751611a0007204000318240d00d034042c0503540c041c0c1500440c07040080540046070140704059603411140075041d20200107601a50040c10040300700d41c90140c000f4030b410284078820031240d0400b000e0b256060b070000e01d880c070100400c40040c030080c1d0398032020400181f52091b0b42189203040030050070500941c2034003034660f42c80e2428140d441c0000c03035031303002ca011009a9000f0f4140d40700304010b01c00300344684183c0c02c03070300865250b181c0300360303680c1c0304c0c032400c1d40c05c00c1e00440d07103440510a0311500e04800d80c00000080c806004240710ba10803090901d511031249041c040c0c0690012210f40700d500310040303481e000030400c02c011440039204031034402c4d0b80c0d440e0868ae8a0340d01041c40e42141040c03070000050b0349842c2e0303080c074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 806596070 1250 806594820 806594837
    0xa0f020402030c0903010f09020307050a0b03010509330108060102011802060309010914030a0801170d0e150406081f1a0a170103050c130c05161a0405030d051501 71
    0x242030000035031004000e0702c031000c0244540500e0303940a009500019880380b2000c0366002150040504006142c1d01481c0f0809140307a0401c8404085016241101c004584000c41e030394030402d401d0881241c1d9450302039004a009030041010340f5084031b401103032400f80c3e140d0b560360703407171030016422035100c820001d40c021107040c00d680062070990000c40e406181e41001055200c41c039950340c104a00303a41b2560031079803c00710300301280a40c0550020700400c800c05090480a841c4a90346443c1c208140341c01082008440d2400a40d84801009110712391600c41c180e992541c1c2d0b4ad4000340b0f036070310070b44509944403403d1203030701012484045180141c42c001501541c1744d5600078481c01d426400301603840288411207c0c681941e40355140114006e40c001d00140c051100b84008100440c0c02171000d10200c9441c000c0c0c40c4000f43d5000c4240d8406c0c407000780610303807049800d0a11406054254422072070550300d032801c20042142c040060a140100d0600610140d243c01d02c5190160b00e4040907140041c4414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 806597320 1250 806596070 806596073
    0x181508250b071406090102030610030221180f03030705040b030406140f01051807080721060b040519030203031603120c03051506040510052b05180a0f 66
    0x80018420604581941400c0d481d990010340c426900866026a22540b01071070f00d408085082c0a80d5030300114400c000c6140d40b03401ea0005200d0814021000105035000c5902400c4401c0400300401c82145000324070610b00e00746040800e00c94070341c0308480160083d800200c8074100300005403409181d0548442c4d040505001003003c558100500684449445961002c00a0b03c400002c9004d50740c01000f80c14550f0400c014806413440201c445001c542d0b401e41045185980240619000aa98505246180042c8100f24075081c03040b915000846c0c44e03d02c0000ba2003814200070011a0310580340b138140f42003d02c0b0200ea104107640710103501600104411001c0c4075004072001012442070900c080c804503900308080c2183e9802a650000c2a0b03036000f40440c060080071249158901140c03140d01c0c00f4102000300750942c01d032025074414004081240000741c18000b00a407010202000f078103001d000b10f00000806401d0a4946031a08130b040780c960303559241c001c03c1d2024420b4200c01007400e1044503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 806598570 1250 806597320 806597353
    0xf0201051c06081501060512190608010509010b0f030316150e010c020604061d030f0c12070c0f0906030b060f03030423130903020a080906090901181508 67
    0x18080c84907140400054224a164a20994010300030000040503964002d400000404806810400070710105101004285225146c00d0f6800600d0798200e0000d9a8018800300c040c10860300101d03680d5003010104a403800301544030801e0710030f0480310f668075080c1035001e00d0b403a07100304101e9003250003507200014003260711086949219081101c0000e038150704000114210b541c0c5800440050b00b024040c0401c1c000c1500410421401c500783c941090403c80300720a59a1080a0321803540075804903401c5e400c40c4040c080d200b401c43c4075002c1603a8a41e414030b40414050713054000e640c00c281a480c8040364001152041c0c1d000ea0380d00400006042d12030030104000d507102c0f440100d515120400c00070518840303404ca10040000f03074080e0361304458144d008018540840043e0702d60301c41d150000030404a9070005024a8454000c44038954032401c81000c2500c80c412080d20300c4d0400c2c0404000038039044401005940060150010022400e0406076030700b5004240c0b0442c0c00c2c0794000300310341040410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 806599820 1250 806598570 806598577
    0xe010b010e01120c0e0a0902130b030c0702011b0f05070603050702060f061207050307080705090a0c0e01080a0207020405011403010c0306030b0621070f03121e110102090a030b150a030f020105 84
    0x1a05e04041c0c0280c0101000104855500d40044121701d0b0089903e03580540da64010401810800c0300203421850800c5084400d4043e0601c080d04101090780300034882c3c3c240301e07080003c0303940021f20545a409282030569440304144201d60001c0e21b810001100140b011464a0150030454922041038442e541041310a880350050700d0300c5401038500001b8596405c000d1400100f0044c405840718603d050100041e6940081c21700c2205410400c6104403107a0018002c0c00800703090078030f0400b0b0340740c00303001c0c3e0020700a04600170b401c01d10307103000440c0204010901013142c4174110024403c0d90010107048040d41c42511001b4803021140300440c0700d03887e0101d41d800b201d032200380d4001000840040500e02c0c148599110105550082200b07005100c0d82c2c5400001803002401c18040c03441120f0a0418540e01c411481130800400401a0880b4082074044924144004000e81151900e03030501a181312821744403c001c074100507181310500e080c14050345013203036082080c2180d0b2400b50340064440317a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 806601070 1250 806599820 806599841
    0x71e09050c07230f1606020a080706110c0a06050402040606170c0c01090b010909030908210f1c0c03230a0b0a0f0608040b181f1e0e010b010e0112 64
    0x6288055880f9410b100308074408441601c2c4008003030740990380074038151010807a08102c0840d0060044e00b03020600e0300003140d081c02d603c00710016a002c00182d82c081d0a009084550a40740203940440060201c0380d0042c0e40982d0085504212943d83c030141a2049400203501c00740c0044810005030480404a0291100c61003a40000c10402819500d507010f8a200340c124000d00f07507481144d0f4007415070140e486030250610300000d01c00c020f0000c540201120b140c00540031151400103030304e020015544280c1d0750490b510007040c1d0b0790244030008038014007540c1d0004d100092038424508541c0c85000c100c8104080000c125031940e88809e4500c1015181806110b600120030000006225111903624001480c00360303240b00c01d0f030401c0c5c5449807207500080e1041c400c0403506144906400408150840c0039040000030720403c003e40031184004d000840300800d414034002010031060540ca410208070401064001c011050080e4015100b40c1c140d12038041c001894401c0540e0204026805140d035070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 806602320 1250 806601070 806601113
    0x50d08151e0f15070507050f1815090c0a0206070311040b091819150501170a060803040906240905130b040c0c060b03060105010f030c11071e09050c07 66
    0x1605220003050032108010503ca011010001d50700040c02001c1c4026000340204031820f45160b1840300009160381c40c6c01013140c480c0e100c28004200e0040302d054030a450700402405808141c6000400a030300c1d500007100d100054050440003902c1507100744103c204140030000c0e0070342000d0030043d0100d040c1d0001071140d078014010101d14088800800034062261808200001d4200c81601042043d1411400f1220070004900c3c4280140da8203d00565051840a441184160b841002020142542d0780c030180c03444c0000131300828402c0090b0040000e641c8007611040c0440e0185080710407045841da0b507c00000c0c00000f041c03000307180c04503035034101c4044003c0103e0024601d030009801c403594010030344c0101300032081c8802009400d004000005400300c01601d000d602d40400a0200e507660180c141c01c05540d040d0420000e4081e038403040d80c5000d400111078000e901c1d1001d903140d00c2c8192a00910f41610190005100c495078000c0500c214030350002c0909004032503480d0300c062001080310f085071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 806603570 1250 806602320 806602339
    0x10e0f0310020d060812031b03010f03080702010c0b0708060a050a180b150c03040513050403020715050d15090e030301150e0a0e0406050a0c0c05030f160c03050d08151e 74
    0x110b0204020702c2800701803042c0407d80e40c0c00d100c18606220350b10b00500340702c4580f09200400100310003a42c0e034001c4075005400290340c6d24072440100e9a00306030071002440290b40c041800b00040c2c0c03050126100303000070346555529030740781c0041203c4101e07144074641e51038001c1c0c04140160740041e0842c0e94440b40c06483e00c07a408204006030740d965000040c0001941e44045401c00c06450071005a0001c050200e104014906040e02d009460340c0240c007400d01c155040540e81010584134104550010030075103405c04c404181513070440d1208483d4443d0032041810014072500701d41010017124101c0e8040e0200e40040854030070180d4281c080025110340c05903001800080442c0040c60061141e0b10958000900d4601040c06e04215200428000c00b04054014094002540041184c140d50412044551542074a011403441c01c2d9003900e004101c1c00d0420310000c10048005048807081c95140c45601071a50340300b0300400341420300e81451b64480c981074000700b00c495000720482c0b50480d014150400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 806604820 1250 806603570 806603579
    0x3062208040308030f0a1116170d02030103120e0306010608070519050903010f480c0309080111030708091501080f0705040b0603062e0806010e0f0310020d06 69
    0x103541c00c150b01c01d5070444000401c00100c0d02c58010700d954802c0d48940100045405141d40300d941d0702134201d4041404022485120500c20f80d561081100751106110603960b031151007091010390802c1c07004803119448513041d0450030340180e120a0031848094018a1a80e207044400c40b08001c0203030076001400386c1040300007021601c0c5420301544c05650386807140c1c2c48214000b414210780700850310131151803500021444200d0800000202610785409000c019408034503868200d001c050b141000202d50b901c4502080e6422a01c1c4054007030183d16040d41659541548600341d900d40d400024000b0402c000207004a0700501d001608400078208461000c0d02c1c105111040f040d0030781140303080354000c5051406070b40701003024001130502a034052042d803d5000108059001c058150391040c0c2018400c1d400c08845030a802203101e5100c0c801e00446031032254003800d034401c1502c0f00d17400a08a1005070b1254144003032156105103000e802411241300c018003420094110b4003100407240d8403400000b5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 806606070 1250 806604820 806604833
    0x501030b0604080a0b13082b1a0402091206011d01120f1403070c080708071e05012a081908130602160209270703030e0d2d0210030b030622 61
    0x110420603200c02070850300340c402c40c04910791684c1c088000e9550412708414a15100b0144040c41c11606407000341c0c540c810400020a842101007402c1c4003881460000540d0030440078030000b46100030150a41c3c1643c030348070344003c0b8051608019000c41c00f19500c2a0020340f000c405c40000307402c0601924202071040e1380d20405500b40398041845613114103424070122400303100100060605040542135400704020046802509110300c1d81070264042036418903d0202403083d148954442203009940c0e1a45031541d4140c0001d54414401e44000015513100c9020703d108034012090720148107100f15903a0703118406503000b2003401440b803003040d9850006840340c0f00000d020f010f11080c2a1f0441954030200d180c0f1100c28008002c1c00c0d800050b0810101380c10524a101801d410354100c84461980c0c1080b81404045551800145181c0010b514101d46075690122009100b04c5000b0f680900020342141507440701c4031559030503005407001c1603007040f60114a001001c14840000000c206070788402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 806607320 1250 806606070 806606077
    0xc060e0109080313090c020c0d020603040201051207050a03060617060d0203120406020a05100606050a0809030405060c010b0103111e2104050601092f0c0c04060803040501030b0604080a0b1308 84
    0x410801c4c400f014103011001c66030188982e040441e200a005ca541a000010890320075100d005e800b41074000081429644100c0883c1e80034000c460f5182c1c003d0030b1414000304035511018201c4002498010b01090091040710204046a800306010005448500411440028000040340d240c8a503d204c40880258400a000240040d40141810400e181031403070800000280d04c124041c41d140e0706110b01a0450281c860008507460120314035071391141c00c24910310a0380c205c0d40c0d00c1140410744000e40c5005420444d01032100780d905004008403051540390728000d012501c03070313107080108a0b46a600c0d4210041c00202044001c07031764608104100664150000b0343c2d0649403600200010f200440c405d000d641160142c9162400014060001d1080b0b0322101184d40038020b82d00040c0c40810140c10040c3c1d0400d0701005004001036540c500c94070380c0d694403522909010909290100c100303858220142c40444400401500000c13080da6224591070303e00801441202c100f0b150600041007104018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 806608570 1250 806607320 806607337
    0x111207020a0c180b12031603180b09041a0105030a0e28120504051c1416091401030c030b0601120906090b0c0903151308031e0903070c060e01090803 65
    0x14000007081c4040301c4020350311345a1410740104000f050310340c1480d20000c11106d1010b5a0035040e030100f24031b498125066203c00040e0112220060303130110303c00300c111008100c65034003141c040200ca00858401344500c03186105072400b103401480001c3c4006041d4218030150700803402176642030020300c24800000703903000c0441c2e00e0650480d0808010000d144c2d04102e0010402d042a900b0940352200086081c6884411308508201c0800400200041ea400c049800c0c1402c900b0344d90300880302410314240e2030051041c1d140761810040070fa0811128134500b98107032034002d5600c0c1a10303811034640c0307008180082d0070f0904120345071a03080900c0341c0314400e4001d058410354010500803401e0074800038501b409403005e00c0c1c81208010300c025550780000c494460303078000659811140c0d1401e04540c2c85401200c0064043c483c00410000d41c01e1045a900804c00d040c103d01003100c0e2198040f45603a8028400014490301d96040c080c052240121018120b885c014508201d080381c9170388032241103801984c039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 806609820 1250 806608570 806608589
    0x60509280303020c030a150b37120c1a04080a06141608040f111305421507140615030c0f0d08070f15111207020a0c 51
    0x1807080603414401c1c0c1c8240c00080300240b0514060703403510502072038401c0a248005940b9801d2403000c2c0c031a10007401d100100300080e80c095140620352a427000360300b5500d40724000b00c44d0324042034004000c50445003041c0c110355902e8100381800e02031a41d041e09030718510340c440741c148400280c0321001c1001030740c2c081c400c5030040f95155510442c009200f8000d858864002c45111245d241564040070056115800692070307664017295080948024000e09101504000043c080800c607840703942240703001d168800e114104103204071510700c0001c458440f00d080d81c0c20940320064506100c0e4460344069540c0180810900600a07080094030b130301580782129085130041904040c0c2c3c1e010f000296121a6100420309401c090100080d168061041810310811011650f00d07016240d402e0b00b02081c60780311080310703520511402c000c407220780400c1d000c0301d0010100580c45a80303c414003034050350703034004140717241002c0b40b010150340030100040c428000c40c4102500280415122280d0030300078400c460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 806611070 1250 806609820 806609899
    0x60215090114070903060c02030f0a05090a091107020f04061d0702070506130602060f011a18040207050604051c0c0201081f0b03060a0b0c10090201110105090312060f010801060509 79
    0x7602c030050747c0984509a00b55003060200703640c1910008212a00310210346004c555540341c000c00a042c50100f40c00c0101441d1800240190400390840200304d158001c640c0c401c2c9050324542000191412402408890390103400307110308580ac00b01c061500704200340180c4070b20307580f6030000c1107850700180c0c20728803100214ad204101054050003119000340100e00401415070620788010a00c441400c1c1e55041201d00140300c01c1b440441181e001e41c04d142c001c1c000c1d075840915042503076850005940640d0b0350700482800805e20701c440840070810100700d031100d200c05502c1c1c0c0c005440c10500200750886403060000207480c0800700803013038005001403000c03068490a11800307003e1911141c0c1c03c81d48a441c1e0810220110260002c0e140010030580070020611598510040f500c030001294081000d600300307400e104003a00d020015101100400304002071998a410403c40600c4281080c1c602060726000148034492190000700341440740605046400d14480e818061001b14004000b031280180c1c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 806612320 1250 806611070 806611073
    0x8120f1e2502010f11211908150f0402070623060303120a0c020a080d09060506010516020108070e030a0317010b190c0c090614040f06060215090114070903 68
    0x4580801401408818001d00740d20580c0c0003804103d04800d2403001d00c40500720300d009203041000300740c002c82907801700300d10310000009400a00713030005641d050602c2441002c9410301d80c480c15030300c1e03c03803074070304400500100c40c10301807000107031225460a4029400300074840128105000d54010000c950b1083c0304205080b540c00842d202d4054140c6100e6082088486000c25603501d280b50040c0712808006443c41d543c1c9130036441d004203c04003e00000c004148012030480765400400b1060040c0ca0900903565280c0044a85115100a01c040b00b03a0451051025520a018a503030101c1e82e4109583c80b5408000024a044075600084000505076a2980d4290181ca03000a00508540d100715090100b03090611250100d40c04000c0100b00b2980500d205001812184000508000300200328071900c6822803c0503100040c0136a01450034100c800083c0303001803103280c00310b40090340640459110045c03103072422000904010801d40d203600c40c80030b010304451030701401100301d42c564007002441c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 806613570 1250 806612320 806612347
    0x1a0904050c04050d2009010e10060f090e090718273305010b180d210917010b1002010209030a03050703020a05101d0708120f1e 56
    0x2070208180c0c03030307040c44104803644a00340e201081c10350116030381c98150403d0800242c0304100d200c15590001c40d03003000180e4030b282c44800034040c1c030904914030200c0740c485005566000b0310160041c0090030403003040204079603e106e0300390010502803c0c1c03003145668800b01c0344a513a00010042d0401c0c0d0b03032040f03041c049440e00450040302e030b41206200d4900034640c440c1000e02413005880c20341040c0c65615140100850b22100209000c00340c070802c02561604030300d034201d810110480718544c50030405045c0916117503034041d81d100e5100f0700c1071090b00380303c005502d4075840c90400d0ba028803d88090100700102a00781080e62003035441c000080c0c5070022020080e00c0c40313810030101d056910411446881c3d490101342e103100309806013000d40d600d00300751804a180020b001ea0281c0540503024070700d102c1034280c0e00041e5072100c01242014444c0c40031200180c5604461203512078aa000b18401054080180d01800c5ea4110712410b01d404e1002130f06001700d40642ca0010f10b00c0440001030b52040e01081d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 806614820 1250 806613570 806613581
    0x602010f060e19180b090c090603060906012117130f080d0c150e0d09050102032511100503010303090e0112060509240108060c0c1002131a0904 63
    0x5242d10310750342410450b03004110408281d002c0601c043d107500030545044010000003045a900101721269890320a076180e44502c600340305140b0502002c008201c2c00d03c0c0c0025554080c02717007070001d0310080e441e14070300000004c0101c221100385002442c01c200420301c0d500615003031b20382c04a03d49a0740d01141000142110035500304140c030561034501800350d0003002506012060701820207864440007818401060400c0000441d40c1f207007044800484d510022941403d0076034107444000c0e40f00e44070b00040e41c881c0112402c0400c0c010044440e240790840501e142c00d40740740110502e81c03215071100085440100080200c5e0049400000100205540980d60800604901003e4241541000304050102c40f140d0b402030441911800440d0543c001801004205c100c0303038403200303885100b1401c0d0768805c11003486031050f0384c02000e0010750301505a00844600c04070710b1010380426071000038500000e4101c540440203507041001d01040007000c1081210040b44510541c3e074a40701e030101000103641 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 806616070 1250 806614820 806614829
    0x1020609030d1116060b0a05011e0c14060403180b1207080a0605131a190303110a1205041707180e0109020607030c0507080f070b0d0b0a0602010f06 65
    0x14894000c01440e06404015264841d40d12a804940c0e0303001d030b400d0b0901034000c0c030490030301c2d03141507241602c100103c41c1e0001038280f0080ea0703c446580e1ba12001920110b0703080034450b5500c0c082036410744400d807180c64006103081c80f0703042814491281e1000c50b131a00d07a04803011408a0100c03a90102003030601d003003000090404400440c9070080f182410380d03c000e005080403040c480b915000c00d61041c41c0f40c12030401391a002d8000b12011083d00700b100082c1031500c809010380c0d044c200c030300c60650800505032038060301c0a100480244d071440e901102c02070101404e010460107140c2480b00010b64000d480e1000010759550203441d5800c004c200340b0020311241c0e0480055000c0d4000300070b160101d1801440240080000250707802d0300703194150141074001c10003548640005140780800d500545600c2d9140d00400861784100c1e1034000c840e40c1c810b80d141c14a03409900510040040d040f004005045014040c1c0c1c001c50b007103030040f001c1205036021f50044001350f510b074a000185414180714080c000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 806617320 1250 806616070 806616073
    0xc0a0b0f16090902090f0d050705040b0901030c05150d0608010c09080d0f030b0a030804080304030b0f1311010e0d0b250504050d0f02180f0c0306010f080405012c06060102 75
    0x1608910781c06884401d00d0b1142000303107900031491072a10f64980e0f840021141c0040c0c81c03d40300c2801803902603180d907803d02525202c1c0d882e02d80100000d00b001d5021a050745e91100c86200d01038103102c10410300c8030000403480a451800c1101e4100c01c4604e0017400f008241c1c0d00008202100c010402034180c944940083c0300b581d02c62410030525603130005480c10840b400b400c0010300c56a41101145c1041035075000541758100001d400a03000c41e0000080c801c9a0142001814030f481d025101386281c0300c2a1181081c034200300071004042041810041d848030b03014142281c0f01481e0a001c140340e03581000c0151001c2001000f0054020114260101ca400003034050421f15072450320050b0240c0114003545000d032501011072001c00c04107284000c03055400601e0204191046855441c0d035400440d680d415161004001c10801c130901416240030341030585540140c06103408049445a074010410780703d030342d06c0b000c2c40b14981d9880c2c00b0340f5603940a900c90007164001c825502c02e2400a006e08a103045 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 806618570 1250 806617320 806617351
    0x1514040209062107030302102004091116060c030b0111070612090506100f060504060c0f05070b0c0d0305100f030215300906010302130b0301020c0a0b0f 67
    0x59860150701e81c0d01c28011200a41da1480b80d052098141194241c59046071244c01c1c00070040c95000646913184142944003840181082c1055a00f02c00d01031b040710303e604509101c28040c01480d90020b5100745180e007a068200000304080d0810b07403074500c40030b44601c2c0e5078800d4861036913498000c0024450703082c2080300c1400203848009555a000e4031501e0200540282c1d010012509030700007000880e04036003103a03018200031000300a051043d10610390460301158002a0080c0508217403800c03030303260f03841c0c4508145464440a0300307043d0040c4102e60078068a6070100d50703516550040c0c03042802140041010000e00700c0058125a0054211004944a0041003001c002911040e4054039410358040140e20000106101103000380300140d507282400602c007807400310110104801e00542c500b03603142e40b622800b03216602c2d05020b0102a400c110340c40e6041c6041c0030036030004800d14201a000510349248a42c04600b0300680c0201160142e580100340224100d900b02d0103030300b04000d000b03030707050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 806619820 1250 806618570 806618573
    0x1d130f060606031a060414030a120201140f0103051207060207050f071e080706050f0705070e0412031a15130b0d0b011e0c0c05030d2d0c02040b0d0f151404 68
    0x3980c0280c0c0700d14111f0303e141c00c1000100d510180882144258000340c8070050407141c01010707000c4c226000c44218065180c01c001401c02d210424883e048907040800303000b58902500030494540c1c026030094928540070407406000840410a10341c58508220192003160300b801c030300e0540b0582d0080700c9600c200c3d21031001d00c500e0001150a100301c0b0389506080c5d81c1c0790007814800d2a18003440002422500404100089040384030100512440c4220348941c40c905640704281c045441d242a00c10344842e030707008500400d00b070038059103d0072080384100d241008140280311030401c07400c1e04840b581088c003240d030365181c08190140c00c1d503000c800d00344158180d0038a0f11506000314901c0c00401003000095624082c000707804610b00203000e000e0180d505010440c8400317000345210354200c20254028080c0c003d5400e0b02d260464030100b00c941ea8041d40400160200009018403000e800e520203194900040003c442501c070088461140983d1840250707402e41d05c0f0101d42e950001000c0c00907a0004110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 806621070 1250 806619820 806619829
    0x5031b10090308150a17030403050d0318020d0c08070f030212010203010b25081803070504061505030a140103210c03050301050616060f02041406041d130f060606031a 73
    0x41c0e1068070f00e010f00f20040d01204c0011101d40b05540700c00c00458a00011094101022000b4410382e0b000c0e80450b101c42e48480c00840440e070300440400a10718850350f41900501e80b6041c0170440500500b00c1d5501161100a81c600703100d407a0380480c2c1c452881442c10811400c2512250b03000d5400c9800071070440d1b00d404090200c0b0f204564280c00032411860307020303400140f500c841000160b044007241d5140c0745940c80754810608041320b5144079102e5240001100c2c5400c0c000c82c03042d40d80045804040c03080501c0280d803242c1018006005503511040c044074403c840340112402140100444400e441c000910300500040b01001c26040007403200d506c0700400c3e080400c49045650903204a43c0c1c40ca05100180c810a03240200245a1800c0c000400340c01d4141e500070300244c520089841300400540d07000c00880d48114030950380300b203403401070101502e03002411240c1e1040c20840c80e820b0f0340c00243c2ea0780300c002d10107243c00c850940d03640b5002d21105501d489040142d040303002140000c10354078000078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 806622320 1250 806621070 806621087
    0xb090d0206061926030313022107170109021203190f0c0f02041b120608060f040803180d1805060c0705090709120b01150f0f0c030c05031b100903 64
    0x3000c140c4070340325400240101001c1c080780340c0c11180017a80d4803410320034040d00c044400240b06070b01c507002a0301104444000318200032090024440113203000e07440c100788803102203402ca0159445540c1d404540c805a124403210a4004140b14082e50343c03802280d040100c500c0503100c1d1001044060b6050354012504014842044c5422640c48a130160031840000c0c05007502542481900203450211401380703802020642c4500b40020301805860f4484500980d1154119408900803003d500410301050f48cc2c03000355042004a0200503008074068a21071800f2506012040001d00051003610003038000a1280b028000031109203243c00305600d00c0c5070b1b441509001e8203219402c80300228240d0f0b17024604103030040080300078250308d20b085400d100780070407424840d9800b0010248610502d0600c0b580072024009030a0301caa1614058400f13040343c0007451801c080301800003c05048001c540100054050300c0e1041c001409084802c0d1180c41c14041c0841d10303922190f0928038800000303600849a03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 806623570 1250 806622320 806622329
    0x14070903032a081c061712090301060e0712050105090c0304150f0614180f130c03061817090d031209020a0e041214030c0702010201090b090d02060619 66
    0x2050b44004605528451490a14001056101c1c0080c40c550a00312441d010b41c00c0d025518810864240d6520142c0032151801840c010150131032000e803104030f0042405030500c10000b41c000a641a02c0310f07905000f006041c6c0c0c0400c04101070100c90007982c221405841c0c098442503510f542c040c00c001c5030a410034040070740001c0004080750603109648119600c902c442420355402440655942d00c50710650588034001c0714012060f20544241160807030200b24000d00c45000f440d28999904410000380200746281100c0e46086e11000002003038150003102d06541c5a024240e41c1c01055190028038000c1e080d050180c0d1507020700400d0202c0c3c1c0c0f044141c24096400d41002d2001e075401d581080000c0188020083d1710039603800000c5100c0340864485032145110b9074071801c0100300d0070401e540081e0010094a00104104000340880017024040c1070030f84e00c18000414240034603921601459011203507050b031135000703100030321206504100d505c0d0024130984180700060381100007061840264041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 806624820 1250 806623570 806623607
    0x60803070b0403200d05040303081e0105060f0d11040e06011e05130302100c1202010207020d20040f020c07090b180c0c03070c0501124b1407090303 65
    0x12240e00703110b40c4240d00054200103030181c917504081154042d242c3e42081c0015000210f5031300008a500000c0300c44420304090308404429a070780380c2400c020a650000740d05052192050141c600c1114241c0070341c845a8405103031403511941007a00c4603501c600000e0540c0d04018148111000321201c4401b09010101d0900d40140d0b621510705000c40e410349590b20007500001c501e4141810700394051000c103000c9200b801d0711046c2960100d02242070780500750010b0b50016040700c00c0d80000c3d40e58400f00d04d00c00c4288140d01d1072500c1200010f0300f101c0540ca865002d0540010b2100000d03e418006203020f0141c1c41400c014289044010448403200389003203040d10000000411081c0c115881542c406000c3d00c4201c0303a60300d1461900c03401000c168440c0c0c0b408900540c2040c4118880d42c040d50102040c2244500300110a68040c0d2060200c0c0c038450b050440c045e1006031018109102d450440c03075000c2c0d6008036880e01c08803409003020400505180801c40040e806100083c0c0c45166a0500c500081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 806626070 1250 806624820 806624837
    0x1030c031e0f0e060a0c0f0906020d03230411010201050702070b0904020a14070501020405031506090403080705090a030303050412030207080406030506180a0c1e0f050c010b04020c03030a060803070b0403 89
    0x142a64014565480c0a90b4613208110801104004540240c1050315145e0340b00c017003071800041e0544a84503103004860158028070740b49284280300790b0101030703c0866891242d41c5c4043d116850242c507503040d14259002d020081580d40340756024081c554100c02c040c40101501890f025150343c5070700445880a201e103400140344aa00e910440d52041c1072650281101d40d01c9566183c8107001703501c54841c040c001d010740c100301c4030040d9401c0c04d518443c8402400201540e5940e5070121010440245403405110050044403145e40351400c00c00c001d035209031000206070a00b400c1203044000750310798407010940104803000020315980185c40468a550401068a44440c00000c01c035811001c5400d00b0107000204100c04500c240e0820b690444a07920340590030408140523852110051a45402045c0d04004c40704581e0300c940d004052071000e1400005900401c140000c0680e401074080e40043d500c04003d112503050035114401c014540390000314502030041d520342c10502e000400c09028031540a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 806627320 1250 806626070 806626091
    0x15090f032c03030a0c02030a080a090807230d021908070806010b0f09062b090b0703050408180a180518071404020d090b0420010509090606070c031e0201030c031e 71
    0x10000c80d08189d500040c010f80341d20081e80020710b00c41c2144510303046442044000581400c1c0102800344003044a5a0070000f41c40c81014000400c016640490300000b207581031610201c068010322010b400c2110142401a02d417466192a1810607002100c103d80c0811043e00c204940200712215003d064074543e4550400b4030b090702d00c0380c600e0100c80c590b440942c1001907486032640d0200e240039200b000c00c0070064440d24401c1742100c0c0c0c11200100220020401740305035500440d0311003240200105862207250700da1075044091100e4914400a06131039800344400120500d030811240920500100b074100c0c40c0c4864403400070400c02c5040d000d83e6000400c0021202980c0080100390303000940010035044c07600d0402c222811405e18a04001400d01d41120590301c01c0e0203c4041d100c009240c440280c803000c0c00c01820750b00c20f030403c54956070301a40000c00591402d815032007140c594106c1402d840820300014007a1407508558070101860a0740045d0714141050400e0f08003d030b074400000d08070b02003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 806628570 1250 806627320 806627323
    0x18060c1b030d051302090c12191e090302010615050307030209040902120d020c01142a06041406060909060f091f1d0106030201090315090f032c03030a0c0203 69
    0xb2a01c0240849040c10208540d540c42e0100f0741250a1003134a61444036510385181542c1401003509250200e51b5000200d0440001221a5298401c0e10342d00061240d0780b4080c0d084044460064070314556445400d80014180c081c4a000c0c01401c0400f140e003400400300b00000c00b180f10040c141014198045110316070f9844551003182e00b076034040c19102028230307103000b2595502540e003200070043c403a0b00150a2a540f04417210712480040103141c60825441d10740041c126440c484001980400c0c00511403004d04042280340d0181d4011b00780c00e03048541510689060460003480707540101203d00510449800026071a5444201c0100154207a11001010750810624a002c007010f041071030303920040321146a0014840800042c150b401c0c83d884e4100840c03c0e26100c1c44080d001c100c1180c801c2002c101294016640703031320201d0300020245900e0341c0303486211040e2541600040d00d44402c0e2081c0b241000b40040500590176945410300c000b04001940d0791140c05101d104120502484c2011502e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 806629820 1250 806628570 806628577
    0x6090703090f0b01081605010203160609110402040b0c10021305190b0310060e0f0306040f0c05030a24050105280e0f06100e060301060818011418060c1b03 68
    0xf4400c4801d201542d44200c002e03915000495003000030f16100c440054190300010880c0c42d40032451040030b00407080c5483d40c00003440c940f442a5070050080040c100c2a40e00c034402440540281070100c1e40360241c54486620b054000d010519846104010088804a0350200c071422601e04640103a81c000b000300b050041c0c0f00303065100c2c2840900c04400e01003810540d456420a8030455942c100d959810042081001c910a240307158040c0c100001050200c4c4080c0080061b143c09003c803041200d665a001c01d25200c41c43ea01074440440c0405400104034032044820b001c8104201c0521503541854000b60740491081951810101000c241c0301005a00b0741983c03005101482410b0441c1c9402c40c28a0410075040f201d1500c2503d4046030329100a0042c01010081500902054150382c248001650f0008002d05640d44e030340720010764107251030402d0045001c40311240840840e503050450307508007000380d03a034611441c54001504004018148409860555406407080300466200c0f05c80d450441c0b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 806631070 1250 806629820 806629823
    0x7030201140c190303020301061713030e03070803040803091c021003020309150906011505030106092705161b0b06151b0606030d0801060807180b0714010c030506090703090f 76
    0xf400d8900c081c03e041e01540514126101c075103e41a03c00b14107103014406070406c5555242100d1100c0d44a4042841001107491920003e000c0707803812610340f0f0702c0503e0f5410a501c00300c0d041d4400204141a405c140b840340720680785506882500080b654001128001c400446804059020000400c07454041084d1204050403101d00565800c10940c441d48401090080c2101301e00c900f140c1040103441142141d04032030f030580c1d84006003414010040300c00c130056401001c41e02c00c502090b050006503032060174002c0503402d00394198043d4001e8042d040501614400c0c025a10000100300850840110780da8000740c00c94407a80c00c0c8264042c24005c501811610b5060365580001d12807040400248081c0035590460403103002d46401142228051000d0207808c0008181d000414011130050000c0d2028845003203940200d2a243d80c1c07400c119800400c1c0c1a00d401054440b040a0010b007882010440303803031442c061040d460030401081c0d18a9002d8240760425640d86001c20074003480498021096 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 806632320 1250 806631070 806631103
    0x1611131e0c0f0305070e18091c09030b060a0f090c080c160807150c0c111f1b060e01020a030e0105040803011a0c060406022203020a1205070f1508070207030201140c 72
    0x20703600c04801040411040342d14074442c1c455142c1c21480342441d81c061110f18550340d42d4242c00c44bc00d50f80c82481488018100c0d9401c003400d5a80031445059415035080a40300c0d09400103480140c4140040000c1c401800f000b030b00c00c4040107114046643e48200692483e040854241d4801203480d0107100c0418135011523000398504a02c505815a214915640c41402620003840ba08000410012151003040c07010218511514040950074000c038003c0401c105076440c0828070182c1da4564000f9540d031000800c000d40d50001c0c01200c0a9058440c111600914000030001441e0640d04c1801c0703840180180080f62041c8040c40380d52102e01d10403581119001c50a44d021801c4c40d10300039019400c01d00000c50900001c00c181746900007810b80e04802c41350001c146116551500e095151510354101c019107850044040100341e115026550703400800b2800c9480d1044810144000e22004014040d441150080386042016030f80c42605800c0000c8003031002c582c3d41c0c4403110342c03074506265a000800b04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 806633570 1250 806632320 806632339
    0x30d4805030307140313060e03162301021e09211e0105040c090e0c030a05060603120c0a030f03021603120c0e061611131e0c0f0305070e 60
    0x800001201a6010b4807030794071030030313014118a080c1413403d000803101181c1d41d007045441e40002c11107582115026686c60810380e85030020010b843c0c04905013100d4207407850002d40c0304d03c014110500c501d04101d020900001c40c1007400308014801c1c0403200c400c0c0602c500602054003401c0d6a1030040c1e848049182d8845007449800075a903594881103c0c42e91035080302c44265040c1210320060180500c916481503941c80424206503802c0d000700703c180d6904c21144144118003109480801180902ca800391006098510345642010325041000c0c0390280b541c03005200348603288500050f41c0344060303850b0400305140c0070701c60000c6009008000303642c41d41c501c0e050300200c00e042d007104211511480c2c022041c020300041e000161103c80344051890780283c81001000001510302e1010310000340300d00312a41400784900d00081c11034840d0740c03007a0b0344c9079030702c40b5034009013134602c0031030003120340001401d00000b0070a442c0038100003600382c200030516490700c000441c0796100303030505056850000d294024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 806634820 1250 806633570 806633573
    0x260c0f030106091e1404050a02130f030b06040b01021b0103020d060b070c05090106050d050604021306021c020607140310090e2134061109030d48 64
    0xc241c20354400d1545001c0e0181d00c0c1545082641110fa09032001c83c003040205c0c41020040c0310091400600c95018103600380060600c00c0d44661010700206600302c1410042070450030b001c0284e100152945114501d401c04610300c0343d030085014104021000c40e0710328850170010041e8007910685146450603441c003030011445c580000003404001380900d0340c000711036032102c0900c0500403081c0507190200e1821701070700041c00d03895000668420300103000541407503d8040001c800808a404c20760250300b100c000c80ca00010307090044460303028148001c000394140380c18003800c078007076410505012100000006285500001844c0d004106210b001c00c8107021148506885003290303003000c22100c4661a41e141400c40313281c00c2e1042d500c2c601086440408200350403034007900d0140c00e490310101210071410080b6500d48500852403c440e480c0d15039411215080609140c0700102400030320411a11034004210460074501e0000f140d0000b907100d001003034030490414280c415540e03004c81c0e1000072000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 806636070 1250 806634820 806634827
    0x3160c051c0903150e0304121703010f05090c0414040b010216080601051512010902071e110909061303080601020106050310090c0e150f0f040f050f07260c0f030106 72
    0xe0440e400341e00071300300c030b00680440d0f04140c071004001c0b00c606900a00c0300307000384018039411400c098410060005003200842c0c00c601150826406540020070142c001c00c16820000e07010b50344034102801691405013004264007080c01d0300e5400e58000d981ea0321034040144d0003000010104050f04240307949680d900c1d0b29a9680e008240513241c000c3c03403c032010b1529001000300360b800241f900c9903000000c0e0b0070222840029004400d09503103420040318000c00490380c40081040d4036020300c80f03021510b2050010b001c8025005000f0450b41c1d070203c81009134110140e24500c103c503900d40380c8661551030300d200403405000c050700850f51501400381c207540d50000f29800f44828511940c500c0103280e41d50314046d0340300c40c01107030b101c54015050920548203141000002070b00709001814040d00d0360180340481c0499000b90803602400e503403031060019081c8010f1050740e1105541c6466065074999081c010703d0400e044080c2240600e1610101d40c43c01020b105494910b4410320f0559200d42e900d10004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 806637320 1250 806636070 806636087
    0x8030d0504050c240a020a1e0303060b03060127080304080313050103141f0f0815011a070f08091203181503071d120d031103160c051c 59
    0x1102d5520801080581d18200461210211500983c40c030b003048031004a90390144d4003412158045010710200600000d80001082c046508107180700390343d44c40c11b860041d040760b06503041211400400d001f0041c040c2c0c1c0c030004031480070701c040000c15003030030344e000750015200c0310b68202100c41c0c000810b010a211100001602d000d5040015081210740d807000190116051013010551014605c0300094005400400b08003050b1080b01110122907510041e200036524180c004443d1904000d040c203082d40c800e10300c0c1c28050112260f1400b074012000c000145d0740e00c2410001068207034121440b81c10321a558055440551015240c03021117014815081d80b02c0d4030160b801c0da400151007106404c1c0c1e003411142009004104c09260380b41d0780390514151160f000a010740d15481d01d1010314018642ca59011139682c018004000700070010480340d01405a403684075003503010581c24004c208004074210301d000c40f03400c0c0c80d00303081800800354103025007050500750b0a040c0544103c90300c8011541c1c000d114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 806638570 1250 806637320 806637323
    0x1109040c0c021c03120b0f27072c030309040b041404030c0c080c01020c0607020f030a06050a240e070c0807120801060c020904120219060b040605060a0804170408030d0504 75
    0x100001145e130807407400216520400c18541100e224030115610b400c0c10a0180c0740001d203c00e00b030807500c1420203140e0600038125041000215000421101c038400a01024112070030801600884803040c0c01180d9a4061800c005114984a15603000c003501c1d0b9512001c00c1d18030318998040d981c036190801403e44e04100c02c08840d0a174502e000003130358040214203942407400503409803190007081000c00459070094a401d0742e0208818a022038107075000c21429000070f10a106c00b05651520446403400c44035001841c4a458000036001047d00c112074183d80280c1d81b1509022095484042048481601e40d0000a024101c0003600720244131000c00082c0316005595665030700d913030700d500c0b041b22520019540207400c08080c0e000328000a00080c074001c503aa84a01c101d500c5201c2c444926103200000c0c45095510035582e0b603d00d050740c2082d001c0c460241c4010f848003442c1c6040c42c0001000f00d60002d101411800800412944c0d0714084c0742103030010505582102d8455800703002803c001d21003034a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 806639820 1250 806638570 806638577
    0x4090602042c100306051803030f04060612080d09081201230a1d0402011e03060e06010801080d030e0313060f02070f0b090607060e1504050f011109040c0c021c03 71
    0x80c481100c62440403083c814405200300a2000e03245a803103401502c805410f002010515180101881e034003080910b100307202034140080c0c603041c1810400221003130b680141400541c150b80b180c0100d0b00200c115808003220b11000608140716082c6403c55000b2a02000d4450814000000340500c0d00c0b1650380c0100940100729054110640c100100c0384030078401c05009001f00200340b03065040d81c06a00f58000d00605000c694140f122008140030503070400f0420110b83d40b81c40c00e00021018075805980240c0030300780312840794100120f00741e4403192134000c00105506c0e9940c40c0045c001c1030090711042001001450402d94a590020348800c401502c65001482030507070011f119980ca000f031008a801c04803002c2d241140e5001400b9607540300e58003c1d180f00b900d481c400c40c040c01041000c0e5034500d0380701841c8445402c2c0313403510321706042c4d02d5410104c060303040041981d00f43c4000300407101620800c5400059600c011003080d1800f1300c10f05d4000e0b41c0005400388441840c6a90840b00035070328882d95 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 806641070 1250 806639820 806639879
    0xd0b040503120c03190c030b100306080c0d080f031008060705190f0f030c0e06030108030702010801121101030b12070611010e0703150903050f0a02030a110109051b0409060204 77
    0x20f50803c1d00d40411175400e603140c00030b880d0700e030400c04545e84503940c103074400d00d4003280303034100f54000c11071010140d081e00c03001030b55802c002c111051003441034050b50a0b04650840104075a615a0b1140c1d001e4038500071a420300000202c1c02c98100407109070001c0c403660065070785920344000c000c4c240c0c0c1c2006403040405881d480005c01880d02c150003030084414180c688601d61410500110001c00c0202031860030700440510519441c0e81e02800346008103c5040210394641e25071000400095040c0d018088110792002c50790300044e03d00354401c040320030a10f00082c4603002c18001850311804044510000d026031000880c000f94040b11841000404c44024046030030304000440d600c003101d03c07014140c0412141c0c45a40c0406c150001d0415a0182c5821401c1c0710310350344071034100d90005454001507400018640351154204010103c0580b039140200126003550712519295030f4550820a800091402445800d6556030b000da541c0c6a04170b581192140c0e120780200a400c0100c4020141145802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 806642320 1250 806641070 806641081
    0x102270319050105251e02100e010218061c0b0f0402030f0402031b150c01020c160501020d090b09042c011401090501030302120906041503020d060e0105030307030804020d0b04050312 80
    0x172002002900c650356004915020491501c0340384100320441c00450080580c0c0c83d6400311680610304803002c84100069440248080000305422091001401407000b48024064211108885844098824004034070442d43c400087d00c52441241440e078031a02c08004e1080030b02000841c2c5110f035100303034221800e80340c5903000e40070214021010340781d00124100d00826404d62000140c991800e00700005400c0c41c404403109801c24207000c015010b4803502050400a641e03040140c0384207510b15081081e90941408903c1d01f01c0e10541240d03601442e291004625908440c460158818803140071316604048030010b25030180404680c81b001c003264280c0003040350905032040360704803903041d001880ca0180344600d00c1070540000014507400780f000d01c00020044900240f100c1e400c7c6003a80c006a41d0411107c80c42c00300c1e107964200e80d803003c01030300050255880c00012030b0360458150030902d2280c1d89178130001d010350300601c1000740303090481d130148400c10000202816910021840504107681d54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 806643570 1250 806642320 806642371
    0x11b051c050606300108152d060a030b0117011b022a1008061f1d190b0405090705031608070519080106030b030102270319050105 57
    0xb0766036964400020808140c0900111321032511204840c111090901c68503580c41c944410240d112100b00e1b000381c60307149500c0031103400031a40a080c0c40350308003c140181d403003408100b000060401c0c5c0c014402010800360350752210314400559106e440881d00e9038407101c0c074404001c0c3c02001040704c1d6003001e0b40e01100d40c6801d408078200d508540d00a14010750407600d00c0700e1080200c58020402844070701b0000454440504a03124820540c4400e40300b41450740602c803568500007010b03581c0c501d40c0c2d00030981d80f07a84451003030750f8450400301c9110b0f61450b640010700c070350580d01c0740300c1040715422100264403400000680100c94007101e4002c015680c081040e5150306c002c4034044140f1490b0030194404601644050340c01940d6482d0841c2014004099150750304120f03080341d4003151868004005a940c0743c003850000076004c0d8001d504007110140d01c2034107520005841110008207030030380003503610200000e04c2c28855804421030001d14a0900354003c19003912086205900b2442c0e00c1e405800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 806644820 1250 806643570 806643581
    0x1141204150e0c091303090801020f0702011403040308151c0f23031c0e19020a050303040e0c0c0307021305040312050705070314041511010c0206070f0c0302011b051c 73
    0x40903110203034654030301502c001c520717503e04005c4051201e000c00c0482d81040c248040c0c030301c10300b495074a15581c80c980e0002602114207800181050740c4100100310000e54030074405134020b4031030300c082e01078030007000001800e8140d1840704641144011561b8011f100c08035011258050298100ca4100c500050321062108090400c0921a6004216400300b02d1102d15a4614400064100143d07004040d010b85044c00e042c030310395210f884800d100c6d18055242003010100108012130085103004e1820f8038011a42500500e075202141c0003043d0300e591603205100312405158020460704d10408421101e000501080d10301b40d0000d08450f00e800f040c0c10f00ca22a0390b0084500345c035582d0902c00b8607070302164841400059002c89040502000500c025480881c1c019000700d41c4981405665440c96a401c4500c10f415040071584501c090005540d003009420381030088078a03203a220301040d401c0503405002d80b00da10007007041440302c04003945603000028100e0401d400c042d0000e16444640240282c84 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 806646070 1250 806644820 806644843
    0xb1005030c100f0e060705010e060105040219080603030d09080c010c03060308180a03060e07420c0803010e04050c0109051c0507030f030e03060a0606080601141204150e 74
    0x1c01e031031082c0c1c0c0c03943c060344400600b91058a883d81558602c00081562500214422100d980d143d100005840ea0f090000310f024000c103480841c107225404400c481010301e00c000140500c110400818460b4500f1b1003115030500140005020700b040341e140030801503201160407010b81d440c0c403803804100f0b031080c0074400443e0340000c1020304262045030444c800c25001c00c04141d00c10303450100040011014050400d80711001006448071a01d822361410328a1040c2011558009643c00e1044d00d4085d003210700000d901000c02c92a42400148500748e0740c141d1702102c09045584040b00001e22040d4000d251846148158280c980c44180c1c03900541c2d6242090142d1076001070103441003e00c0c10b940200c0721003a04d000c1d1040780d01c00307a0b40e86c441e00e0381d80c02c003070350181c3c0022060850741c112818100425604481ca10908020061815000801d82d1001038002d40c1007000090b407107080040b0b05405d84020218005560a81d824589403460001c1f4000c3c14060010b81002c600d03080901c0003140361030030070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 806647320 1250 806646070 806646079
    0xa170702180a20040906050d02130203040305070605040c140402030702071e0f2606040f12121a0102010e0d05040315062117071a150d0b1005030c 64
    0x240031410046031a00341c020040c6082582e103181074103054148032070200c071190304903802954a80c00c3c0030300302040e50515040680a03c414661000040c6c56501e810004a09910001038880e02c032460b003158284903900c0058001401c1c2001d00080c4901101200c0403100d041036144189404102440213030300044510744e0150b0481901005884031564402003101081480e00c2c8500b903c50a118499801c1900a010070b014150700c042e802841008102c0c000d0029803001f00b000d490643d442100c00060b240f00140a401d0141d1045c09850140350300d07020398000341c003080c400103c0300f0031045043d8800c140c41d00e00540c2008a161080880419490403412060361024a01811512580440203030074403500d500b141e40381c800140e0b00201000c510310203c030000c6961100416410046607029211103900c0001d081000103a001070220f036040700600d8800b0f560000c13541e46041488698492421220f0341042000102204100c00109642e11035290034822420141d00d9409143d6558607080c07078079422 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 806648570 1250 806647320 806647339
    0xd0507030b131d0a06050a050c04081209010e0a061205220b0c070501050702250f0e09160b0d0e010b030303040215090303040b070303140705040b0c0307050f0a170702 73
    0x7603110703d0700142121141588109001d03286a10380c540f0b007540f0481c0036a62942e48005014401c401c40c01555004141c0150307190a09060444182d00e5000d04041c500c20100c0018102e0041d9001d50309102c0d0740b44008181103170f1195035007009070800b090444076080582ca0309000400d22040c1a0340c40d440460351400c030721200609a5070392952070320080d003603030302c901824061000014003d000e0395101d07000344c3d40608905041c001d11841ca40e11074408455500003110424004500c88902d8541180d401e90007213426603c82192150030114440042c40c190828190041001e440c2a401400005000718003000f02440300a99540bca0341c40b43c81c1c85030316410800c04500035292040180a40403106920540742c801c05900081c0303503074850340c460b030f205400c04240700060640600c500c1a624080e0944452a4a01001300a01511481c01080b484141c041809607500e50200f099902e490350080c00c40345c1c00480480ba1540e0380c921540112041d684511056500791101c8050f686601d40c0901120721 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 806649820 1250 806648570 806648599
    0x906011e05090d0507060c03090f1d131b0501090e0103050c0d02032406040f0e071a0409020d060503060c0a0e040c1b0c030309060e060d050402011407080d0507030b 72
    0x1032070ba0240a4003507000720140010004180140805002409561195104020035107006440d005040c1d0140120407004541040341e04040302d10700311a0141400202d0080d90f0303161041d04440c590070700262000100c03000c50182e00c0580d4a26500f610f1007621440d4103165942141c009011090100400c40d40200307500b5001d90610801400d040752004003510681c04448440100c000780c0c07130b074540c0c0103565040c0502c061820188a07080c0480c17030f090030a12558a484040300d94800340b41c400c1c0b0b04072807841c400b00d40b4001c4284040e200a01aa840c0075541d4100902c040009070560340501e9201307001d0900824100f1401c9412142c2c07014898551482ea43d01100411000b800c1c07030100b901c207004c0c035861031039214003403224450720032885203201c80c581c103086083c018003481494200c4070500059002d0340c00c6584d183c0f4240c502508010f040800c2550351840100d56600303490400c2808031704007142030410030a400d0042c18458206400410503030750365020071802d43d10807603011074202920295a50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 806651070 1250 806649820 806649827
    0x10e0c0d020105070b0f041e0f020909011118031509100b06130306090506070e01051c02040f080f060702031201030f050c060d0902011404060215180a060203060906011e 74
    0x80c041070050424600749442501e400600c49422903000d084c00642804100070441c1e00040102c411313201c810510400c0310580e8417148500300110021740b086242100250740342e076007504800e1a850458032a11388800045c0d0783c2c001d2844103c4403140c840d008403a04180001c4030a10303d61721608503000100400075007107006400403c0e5002155030090380800962141205400801c00103500c81c0b0b80c009407081e10380c207240d420401c018001c0030400141242455450382c1c0501500c941c400980b60241c2c0d801542ca035008020710880d8041c160700d9045a400141c003842c046060fa1001c0e445034255100c50792a000100d849202d801a40d0810303028010040c8082170440d07403100141d92050b802c0b180b410794400c00042c210b80100b0116034103203860ba654102196845000c2e071009010300c0c1d44642c181740c02c0102c00fa4899034401e1012207172410860000d0b400090360754003044807a641300181e6420412505001000c0d5004448481c0216400004a8180c0d440360b8000c1c66480c008815009041100340f5084 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 806652320 1250 806651070 806651089
    0x3051c080121050706050720090106030b0a03050d02030309101103180c0d1514130209041b0303031a030615130b06030c0d050711060f040314030a05010e0108010e0c 72
    0x1e441c0b04410706444800150100100d002401c026110651200014a403010480d1030010492080c50800c2c0039510454a60448240c1902c0791401c0c01304030249007201240b411503096001401d1885413a5010811903008402103020f02d074602c0659100c80d100740002d03000d07250002d50b0781e1000c0008000040c598180c882c003450407000813109a031400a60140024000f062214094500c042840e5000c840c40c2c0070340c80b0340126004807070038084842c41c1407038041c5860300102c000a801695014001410004030401c0918240d020500c01c4000c241c89080040060010b43c03203ca049180200500281d8900001d91030720490001c0105e02c10035100d18140014120304903e050340c410744413001b82035035540700409584201c80003000c0300d49800140340180240e520141c0004c06015038040e18036000c1c1800300300158490311189500101c1e842d04d00e021150000c031030071800d2015001005018074024680c00071412600300c8400240c0d5641c840e220503080340c04000f0b03d040c0d158070a0f0103100c41130a000303445 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 806653570 1250 806652320 806652359
    0x15070c050d0204020408030c0705030c010e01020601030b250f0e15071416080c030105100b0d1517010203040b0f0928021207030606090b0a063603051c0801 68
    0x1350909940e54480d0f0700d9900b01800083e06a0400c00c0c0038055070400700482c81191009103040c807e064043d00010b912240127000280c140002100090003c548414140c1e810204842e00241c80c03022000c001003826601d401c400c00040d019603d100543c1c5820602850706050301c0424518101786980c070810324541c040034002c41400340f011090700c40b002c602c03260030040640c0800b03007007200d42400c200350841e0801068200001c1c0a084240030010b0700c40142e0720740100100c00028161082c2c1c4000c807803003c0d1603000e0306e51311850000c4d841000b1410340103580168420a091f030b40740e4035101f0262404a80c21291101d540c0c6c024001c5880c000592244100c401c0780c0a400380d0040c05064000c200402c4d2007814503040355102d1a410410400b80744074010003400a200100080044140040d00604442c82440c04110704210b8441940105035082051140208000520042c2010b42070184603860302c001e07141c40c0100e124582c1a071500075104070a0300029914803044d80e08251050701001d0071101d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 806654676 1106 806653570 806653579
    0x2a040602030a1b050d1229010e010306030512070c08060408041403031b01151a0a031d03071a07031a01030f150b0301030215070c050d02 60
    0xd4a036402c03440d00d0035000d00600200c1146500e00307191805019030150100030410140c00c8605034412000c2080240040070006808a01e0302d140d0382d62103506e00d6035013000b4114541c402ca1200c00300301e41c14140041c0c01a00c07500c416150a04040e41d0f2902e903240052484280059125448020b008140040c5000d20305a42d9000c418000e27440f46040b202000324001d05c19650034019580d54000da440e11502c000000744d0440d01070001401c1030200c00d403074120003080e60794203030920071a4840c0c0070070346524110100004a0041c101c400416034010b00c090000a03600409100500708603006d1003910340611000798070b004064401a1860301414601090321100310065032400c4d105d0102400d00042e450b82000f40d90020f4104d42c60308141c5004d80c0741000c07480f0546000514180c038001c1d56000f101074440c44501d041c03407081b200040c2040020040801c041d2802600340c42c4594800340 = true := by decide +kernel

theorem cover : BRFrame.Cov 806474820 806654676 := by
  have h0 := BRFrame.cov_init 806474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 806474820 ≤ n) (h2 : n < 806654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
