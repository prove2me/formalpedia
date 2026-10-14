-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3403
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:07.115557+00:00
-- url     : https://prove2.me/submissions/14a59132-70b6-4aac-9203-e410575fb63d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 611870503 ≤ n < 612050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 611871753 1250 611870503 611870513
    0x20f0d090c05040501080a03080403030e0d0c12021212040201031d0102090a0e071d0303130e0a0c05070305090904020d0204060b040512010b0d1b0806010e04061a010e22020301060c 79
    0x7a10291108640421065141001e510b507501401e04005042c010110000f4003418080da01c40318012550f0015a00906402500104060744401c0110303114100c94203003114192002506425060b01c902c8001c0c078000d1014491440c030003004000703d04041d200c0c0c0700d40444001c1c1e1180c00880056981c00561900007900420591070b44a401140030346072408104450198412070f00307403031400b10501002c44600d81c4400f10342144201030940c107200c2e0000b00005140001100c0140c45940b10907000c1080c103119817401c071054480c00c5405000560140030f80300d11303890091080c6421a2004100000000455000c10b090341c0c803603803004401c908081010002414401c03011001c1c01c070300030001c008116040c0001000005565009400f24a104a19440c814100d1144802601864049032241d6a4400e8001c0c40804112402c480d0b8034100046103a905c1a5001c21105002058541000c44100c0d44144019604d40d44e070000080700f00b00b21481003664541c070042d4068046580d40e0850760780c0750304107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 611873003 1250 611871753 611871773
    0x1030f051c030e010b09070e060702040b04140105030f031e16060f05091207020312030c160f1110170a020f3702121b011a0103050709050306060f010201020f0d09 71
    0x10f0180a4090f01c02001f020507441608450b02403801ca48c05900e0743c0103400820001c01512401507003140c81c0c140c0d000d200c00d16a21815040b0340d411021504040704140e1102d880380200c00c80c0101c03a0541546584031500b40d000034060744400c0c1d002c047c00030030700c07034803500191022001c0c0c1c02c0c1d88640c1c07041403000310041880071406e5150301808080c80c1883d0740d40440d60320604e810405407004070110210b0700c0384010310100c0e0240b1000d9084000d001d08181030824910045d003500721020140d216100405040010030040045c03040d88841c48190046155182c3c54040101840c54a5508112008565480c1e001804000b800b0400e07840100000c2c034000c1c00741008a02070f054001c602e0380d45114201d0341c0010740e0384c14080b440500e2529541c8050b007130300c3d0030221401301d0340807542088812174680c1c95840b11280c1e4102d09980c02d1045071109482500c0e41c1420b401920741540092001414905000004c0802100103100041c60113000e180c62072080d400c0084403206c540d484103503040501c400c200d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 611874253 1250 611873003 611873021
    0x11070f11030706020a0b06010219081c090f02150f04030c08010e011e0c1b032d0905060903070e010e07030b0a0506040330180909030801030f051c030e01 67
    0x602c819030828401035074402c2c164000410407129100003402c1a442803000c0629100d91170740b000b6000d00d00e450803040340c0d00582180c0c40ca10988003000588000e00d409400f440a40151103918607607815000d03c44a81c002056404a00f41c0403c00098400d2034403005100031802580135642d42c0d400c083c401c600307680c2d840708022032a038100f0440c04883d1040c120f41c0741d261003d801000440340208a4144c1e95032003101c0f444808000040c15803001d040d04855204c0728880d56400c5441509d10b0411202481e524000322600000c80d0094240301724100318000b001400c1c002012500e03c10796030103881c542500e003604000b01e082a00414402c4403501401220b055607411103691445900740000b2840314000c40c030010b402d55000031402d03115545001201582892815a140c821240407140680b0025403070600840108582400040130380c01e130700c1004d05440c2c0c5030341d42c0c13990f6034a1b588401c100c074035200c3e10070748040c01038610b2844640c2d40d1000ca02039601d500d0700d000c6200c200d0010544d0849060750 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 611875503 1250 611874253 611874259
    0x60607050d050d060302030d030207050c010c120e0102010b060a02070521030906071a04050318040b0a032901061e0203131a0408190b101206020d11070f11 68
    0x210141001a1022604071460a841d19105071298040d02c010400f400c030715800690540a0200003c05269054004100c0e142c0160111441c85890900454004030013010143c00c0b5900d9a2000c0d01075481400028803543c0140f00101d00452041d0014030540e00c030995420159001800030803140c2400100b82c183d180080c8000302166140a28107500d070310410400b540300c2c0500040180800150152817000d00f5902d0024a015180c5458015617a602840b800c0d01940c030152090203680c5414010010044800f03040181c000c5e10b10b9403410410700c040e0240100c2c1d0610385103400b8418800040c02402010140d503901508074a41036031441e031036903d00e101021900108510482300a0702400d100480c1c04410000411160b4030040e01442d000e190042601401404060115410b42d40748072108240150341a0005460b0301d4400044100d02d403203040e502010704080c82c00842c0c220380c05003400c5440e8002c00f060b442d01c0c0c5403440c03200307911004045415081c00c04a10303050109490065480c45015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 611876753 1250 611875503 611875507
    0xa0605030708150601080402010c1b090f0e03180d05060702060a1b0c121206080c030d0c02090a0b0a05040507051c0c0504230d0309030b0604050402060d0905150901060e0606 76
    0x1074050700e0f00380c000c02012941440240c5010900310792094080c2000d094201103103185201c812201c2d0348084030180b003442d4000707040201e612000c200d40e01c100501111258001c41c81c2000c0c0c7c40c0c000301048100e240c11580554000c22440104100b442070510405079a40a41400d1a00c0e1101e001240c20b00702008502d01c115081d403001c61504051000ca51030b412a03a004a0121200d400701c40580040c5084241303641886000103049600284c24480004110146c50250340030140c108ea148281c1c04010398000c3c040008684803186651240880600203003464142c6074030f9001143c2611803e4500000003240010707000b0454050725503140305039a00c1c2c1024850710100500041071405140640034841308041e003180e611141001143c2c40c00f24000d050b016846400e801d028010400e14441030314004240c030000b070042d241504c505031040364000c0c8281d080c02d4042403103800400c0b510324103c406200b0040010702c1c42e4003800145d88210200c0002040751030900030700311120308c40078003024028001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 611878003 1250 611876753 611876773
    0x70e04020607031101150f06020601050904031e02120a2a030f0e240301330c080c060c0309010f0603021c231006060f090303050913050a0605030708 65
    0x10801182c60098040c50706180c844501500c01c0d00404020040c910039405420b0000b44a0700c030042510116000c94081e10302d645e0361101400030120080720700500041e09120b01c600c0090341d04400030b442a40b83e1044520789001102c45465a9120011342c401090a403220354030300d00c04402c0e0104c001281c00e01079008540c055035000c3d004030002c0c3c10140c280170090300d1000c541d403a000480f40500c488458001c0d02e03a110000030301c0881d402806004060801080d02c05010700d400381d0f40310302d0281c00c00400791412114000c21141030510f010212000f10b0300b004000183c201c1044118001c40c103c1186540d80e09020112508503105d8201219a40382480010000341c6d82c2c1c4070313040b1100a90791802c5000040b540c07600302441d016007403050815094900c0180003400000504a5008140c040104980c0e07444210590f80301b40200ca900c800100c030400d003400000d01c1303080038190300c0b60058811000440651084829200200d9500781e409558080400ca6860100300400c0204a00c0020b00701c4111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 611879253 1250 611878003 611878009
    0x71e090b010309260d05010f14010f1b1a09010510090b010207170a05030d14060103090f060c0905040c0c0c0605030f01090b0307151805150a0e0411120702070e0402 72
    0x180ca184051002d8481e41d6000381441d070344c00304a070322004486404000540e121802004591780d0b50140b480494002c0080c0c0201e54044c003d1200410295151460300c240c810301c90051800c1811000c841c078039502c0d103070b0255103008041c80b1801000b03c40004030f442e14181c01590780000c101c1e0f00201e640c60034590003ca0740d0b40c022842d5000d95216200440481c00141c072050b1400d03a110000904078400058161170850895118001080c640201c00d5020b841e8140110f050300e40c2518094000c0e41d02c15580400078205034041e8003002540c1c140345a4042c0d6820001341101d5003619008045901000c482c0d02700b110342c103110b001902d09070a01900b581061000b044400405001c0d21104560b41c44096109a030100305082c000d158045145060003c0090010004100720020350003404184901003140c0c60401060345040100c61401030400c140701804841048400118540142c0d0360340e48109829203102c0101180861400754100707600340342c00000d19161942c1d015071620b0031002c06020060b6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 611880503 1250 611879253 611879273
    0xf051e0c120120031f0815060f0603010522150807090203090a020d06020f03010303091701050f1914090d140a170705090a03120e012f071e090b010309 66
    0x40d483d03c0c401d83c076a9600f030784200c42d2400805030b1000c00039a0800000300c07120005081018602046032200c4561030305018098500f8558170540c1d40320106100501607803c2c0070701024220200b1040f0074400045942100c400c0701c20750f5400c00792082e47c200d401d111440041090300001e1181e5581103285161805140340c403020310307080003032081c0180d0120f00705200342901a02d0018001c410015940e5039280b40180100100d44105c5410010035407026090850610500b80304603986200f05c036196a031108002481c510656402c0c00e007a981d00e482100014403001a6841164800c000f0302c00c2100a01d8040c1c846450011103a5444904010107540c0b2640800b41e200385480c041d816020a4480c86000d642501035613030440d822091540001050144900c01c0c0e4070a1026034a505500304100b900443d02d80c1810b40c120540c0e401402401c0000420742c40d5444480700691302560f811a484020005100b0244a94404510040e030740034003480016104030707407908001b42420040b614955662203014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 611881753 1250 611880503 611880551
    0x102010b18010e04022d040b0409030905090603010e1902041b0219170d1a06070305040314010216030207050a1d240a08060a0c0504050603040f051e0c1201 68
    0x180741e4071030202d8111346031a00580e04a022074146c0080b00f0b845280300801c4800400d506070b10a0f0300345450211581094491050400e416545020500f030030101845000c4001600b42c81e01996201102091860b0500c0000e80c0c40700342194101103c107407401040140c03001414400703103648803280310411507500090b13901400850780510500703d04040c101148403140460306044080d20006160049142540c80882c100c2c03503100300b10900350a0704003440340c503000300f14004020074800c100510201d1003940003401690154000940b514010041c3c8030f50f1025009004c80140c0d01000f4180481c1c50401e05007409007031800003600e1106d130124541d0f104c00074090495598600941c0450421101b140f058041594015014620003503644181d03076a00c0004940401c00305284c40c11030100184510112030890341c0c020b120a00b192503d0b11441280341000100b22003601c22100c50000388048000d1400d9481a540081d25092101c1300a000907010420b0b42080c032030345444140d0452181d18180c6a000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 611883003 1250 611881753 611881769
    0x2040f0606020d11070e010b03041407080c0f06041e0e0708040803180f030c030a03050c2a10050c0705010b030616181a0408070b0406020a030c0614150102010b1801 72
    0x46140710303e030414205d6001040c000e003182002245902805001b14002c9116031138182107900c541d040e894454903540107400b03098216a4250120b0b1502801002d5013002c010071103840c01ea9119402c002c0250a440745469001e003925041101c1c01c5248000c9500103582c1c2440b1240e4901a540c141ca13620005102008101c401d00c004c005000c801c011440114031403804999540382c80e03040941d6a90003118031310f0002030807c0002000e621061040e40e80c000c03500da68507464030b100c10f840540005651707000c0c00a144243e4181190416850158074003421500080c1503468510b070400c6800c3d101c454115074040d80c429070074421111040e54450b40b0705e14042c5400c140510400150701c02c000c0301d5170712411040102881920790403103900020022100309004440000341d5840070703c1624011352003a0350243c0c10103031a40003c2806041c120301f04a115580008140c8012801a0303064541500c581407101410740c0c02d0940d5580901ca015202c1c80102c80c000c168402906003101e0b8104c050103a113003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 611884253 1250 611883003 611883017
    0x70803071101140702010e07061103030601050c0f01020f070201081f14010e04320c0403080f2b2003010b0a140406031a0a1409060f040c020303010302040f0606020d 72
    0x3085440a6000543d9903100000c00b003064100080b0003400b0b050410140a03650050001c0025040d0256044010748240f501c080d5045580725001500d04d40c2007001080e55038002c401042c4807601c0284001c00c0b40c1c0706211501901d4040b1800010b04402d002820082042861510b640c903202038071407004101d58403c0c100c85115400070780126046e1181c800065082410542e940202004805217401c603c0060205d403485000d030001c0401e451711054901c00c80b100410002400401c1c0c4a400419002c8802600039181c1105000c1c0410400f84010031309100c0064140c0e50074994480b80106010704503543c201030480841035100c04210300c8103209900b406107000400d6080c0c50301034a0042d0481c001c06510a403102e554801c00b030f0240035100045d10107404a902c1c0309085280a00a4034140c6070104103255044d40d4410a004680700f02078040c5520401e12080702c40981d4a40c041c0c6000c001441c0e020b10380f294550710600c0151290000c880760640d00b40305003440950340c000340d6a042c94080c3d00d07001c0c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 611885503 1250 611884253 611884277
    0x30615010509060a0816020c090a0513020907030507030506030f03091314040b0f0f10051c08030705130b07020d0206070602070804120210110d0e12060a1b0507080307 73
    0x107201c5100d01d20015030484004140301c4015a0041c69091044040e0410800f60300004c0c3c100300d0b1601c0c01410b40544c00307500c40d408224112039960146501c4041740e000041c0c802000e4001a00200007124402c00103a00c5100b0800c80c1a45401a00d0300114290018141d03025842e288940340c1c05081071300f50194480b100300c840034501c640c10016581810302c0d5038443c182002c1c1071880172800210740e1a00c40744400e1011401038030721a50700b240701c1c0002c0440042c640d8281020071004040081c8c0c020841c41c901d401541c0420b1043c001980205210749030aa981d40c0100c02c840000a15580025102071052048101503154000a000415411240d456a0b501e061034160028024084086c1221602041c041000c001414500311014000c4038003400c81e0100d440e04a861358004ca00480e02c0c2d81241d50590101070060100181240000b0110100e80c0da92003200b51600108882c00c02c8080d4542000d10360421030611640d41c07400c12458060728111070760f1112546488040c1504c0104000c50b5180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 611886753 1250 611885503 611885507
    0x30608070b0d0b06071202190305040b0a020109050f030d0b010c0209040308072115090b0f0f12010f1a01090e0712110a0807030513050c150c070803040602070e010503061501 76
    0x4071401800084c03100d0b8880c10542002c000c4c903120801a14098450012040030500820904000255143d0380700ca00c0c0c61300f0848420241d4000d0340c0c41c8e0301503648a02449000580500809880b040f0090055448501040d141c4050b200840f08050501000003011005a100c0700c88441e4003540508107216592555001154000b4440541a151200561160b944a4178941040c240310b6485041901d986440707d01d08004c490283d5001580540c15000c99030309403c00200c011104040103081b43e99a4002c24031007829259410808044150399024003a1302c40101d4070391240c00c60081c40c2071501d2600740f800362144000050520001c0c02400c0d1800c00c1d44020365044040c000c080805c200380c6410760210080c11030070060341c0c0305001c282021b00007800e6401c08414262100d401000401c205244103050012a000700b0a00d40c03400344080040c213404010402050f8000c28641c0000c582e00e5240c140001c0c1000300c203030884a11414140010080b40d980043e8668000803040c5204505070110001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 611888003 1250 611886753 611886761
    0x1403060a05031e15130303050411040e03120106050f0d0e07031a090d030e070603020310050603250c0b04120309120905040e033405010603080712030608070b0d 70
    0x8855070511406804980241c003160440c3c03070504055040303034200c1c1031001c601c0c005104d0403a2246030074401810800086442038100710f0300940155204444101c902c3e001c00c0030740d94040d001034155400010101600c007144070070180103048614265080800d8024040c040b0311139501d0b40d06909071658516221107000f40903d400441d40280034604480300e5a042c0841c6000499803000301e400345045d245100f84c040c0c05802c0203120325001900d80303d8205001a8000d41000d404805240c0030701c980440c1d1a01c0310b0b4011030242040071048189403010680b000b9030031a0341e1a0101c10084001c0e032510010b5403440e5520b4000d6440710910082c80c522404c110002d1003c0ba101400c1000e01110107440c10f03400480710320a455060300c06011056000c42425928480c3c01601c84005030801c1c9000c6a50b01c0c0300d9000038909003001c00f2a106090952246400d5903802d41082d1500d000000d101d904002e1000c0004200100318141448a1450000304a4951400303205078541d030100068000036481603540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 611889253 1250 611888003 611888009
    0x309030f070317090708030307030c03110c0f1e0712080c06070305010503122505070e0a0b010324060e1309050d022506050708091806130603031403060a 67
    0x1195807118158140200548582c880d081181c2ca40f1030003264080c580403404030142c40d2a00021440c58580c01012002001d84c00c1e070180806680d00d1101407409281c0004115207403084008042c0456405034950408481e0501049015080c00c0d0342482e241002c1000b5003107030000304204640c0c40d030030300b81040e0b00e1040107084516030054004001c2100e4040e8051416200190211041081d000150265902c00c202d090048a00c0d03807001002030f072114280c6000c00c41d200c0e030207071041d00f82d480c19030b80c80c080e005942c03c800140d1940c804002e02c0d42e0521a114640780004030b005040c0c01d00c581040b8404545004403010010395084020150300c1c0d40300b298001d09640c1070308102001e100e061164071102e102c00901d0060159215650340c1c0d100c23600414000c484140030050b06586025002e9440750700c040b104a860f008140641c0c2c0240e55401104c0b5600742211880110741c1c0782a104204450340220f820f04c03c0c091a105040c0003180e40480c004042205070000a81d40341c0300c990005910002540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 611890503 1250 611889253 611889277
    0x612090605090a03080c0c06010312050903060a05091b010e011d150309060a0504050607080601030603140c0109050102010204120f110301020f2106090406050a0b10170c120c030903 79
    0x41c0500c4181040002c100c010715009640e084266107503400503114610841c05902099031080c2c0051010031031030f044c1d1583c48121030404a1800c0c4507503010a0924008585c00c1305159511000c01880300d100f880030f001003040a008120f8118499000a403695040620160411030b400b10f826003140041c00d0700c0740104600800d1448281881c102281c0640e0048a0800403801400301081903503000b8080c1b03a0042d94044060000703582c410310115048000101118105602c0312800008208640d443e0b50403841c000018140d0514144000740a82100703a004d9811a0301c100003c125a5801042019149a00540342e95410f1154100a1002c19420002035419440064182c02e04084140146540400302e0341d4168801e142039480c070b100c21000c0340d000d50003022401c0000d000500c240d00c09980a0f011140001d20302810001040001c038244901c24041030500b8043c1654000102c0080c0d404240340c0300b00303881c00724100f9004003400b034080d2640000e101c0101c04558007043c01e2040c3c0700c0d080014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 611891753 1250 611890503 611890511
    0x7200a0c0801020d0b0a140d03020307200f01021606050d0b060a0201090b010f031703061f050a091e030f0206070b0a0f05010b03041a06010306030515250906120906 72
    0x1541d40c80c1e00030341c001c910790020145001c0e04c03418036051803880081110690850714a590400d0414002c400c100c84108404602007007020b43c0000e10480011141c04010550045c2c1030349010050004090101804606644c80750841060010038038407500203a913001d2800742d0b244c1001001030780c060050140425804400450000411581544180f1025001d1007800d0717891303642c5d050100030104540c0009844500703105010500d00c030f511401103402c80400341441340c06100c62610751380e205111040b07040008200052444200f035101c04c41038041d040c40b80b420b846200000b09408801f0301d0502c0000e050095004422055544103420380d12200d4220070116030700e1515081400c0184500811040b40b14540800401d01d850b41d0403d60384101c1d842034080041513038112007184030744030090106040503101d19010000a506000044429890440000300c6091000c0310540011003440c01c0820200c050441440180d4491441701c111169820030010814502e683e41028020010b0058603181c14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 611893003 1250 611891753 611891759
    0x9031623010f050a0605060c0613030e0d0f060510061b02060418050a0f09021003090819030e0609010504261312020a0509063006040807110907200a0c 66
    0x702e604464862000000200045a211010400580111a00c1d1162036000c5030001d0107029405540301c4001d0700a081492820074a000010728031581001c1c200c4562000c42d80505c1080042d00540750000c0981c091f0002242c1495801000d11086144038821f08500300b4003c025911031001b00c0c2c1c003404110301c02c42e100c030b503000c50603402a003000d81e103c0c0d20f014501003401080711058070451301580e40c020800b0120403c1c005048010380f400a10a0341c1c03040c410058115803224600800a003d003040d01c1c0428058040c012090400c07100414070101079060408110026a0080d540d9403c0361303805007240c0c144010111500907034010038481501200d035800000c90700301c03401410b83c1c003081d108a0350520110340300c07424010b40002c00d80703429412280701d4001701280c1810061120300503540b006041c050703442030494141b4109096030103803806000001c0050070300c015128243c9016009881d21045400c1c034020007030003080ca400718940000c021400422070b424007031140c0c0703c1058016600760307200c0307807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 611894253 1250 611893003 611893031
    0x10030225030f090801060e060108062b0c0e1003080310090504030504080f07050a050409050c06070311120423121f180807140a06140403080903162301 66
    0x72002d1245804201c075901c00060380c280501446042da540c10701d52006035202c40005403400c0c1c07401341007581c0c0403003000706084d80000c1c850104001d0300c084c610340ba402961281001040e20110341c0000c0d001400d000c0410140208408010301201d5001607000d81da5604c070b00c0c612504142c15003100100c2c07800d02d82417200740369101002c0c000752a5201c0a8501541c054004a562a08203225990f00301d2040c0c1410049807916070b0140310703d540524156100100d00500007500c650000e00100c000c00d8841e074440450290400103e5241c20080c1030f880e191a0410f42100c1d42440301884000768040660042851134403401190f842c900101d030b040320020b8050100031240a142209400c032650724010290b010161070758688000d0319004865945441142c0d11a070700880082d007007004041c030500a40c0c3d000141135114180b4441c180303104508407070410b0b141c01060080301811503860703684180701113500c2105903d00303214502e501002004107071002d0a1002003011080d01d40451a52034259070711f032005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 611895503 1250 611894253 611894267
    0x120060c04030b0c031510022407170106120b0a090e06180a0b0103020d050c060c070e0601030908180102010608010e010b030c0a03150b1302160611091003022503 71
    0x68400d5049600303640d2144d2008007907000440303c28804044c90085502542420012240d8000c0903206803094005200400d140140c0416040c50800c1d91a400f000651544840c1101c4014a0b1180d0303d03560754581500107001c2c030540d1120442c040e6030340b109049240c0e191226800100000d03c2c0030b1140100b22083d44c1d84a500443d085075056400385881d070034018001c2411403840c0da0101011801d6420343d001d1000c40440a981203e66107e0342c0903aa445969a0000e8449060a0001040300c0d40c28880091000000a081035040c14100001c2c4400100c114056403113401c0c0116005c145040d43d100102d026021a5000d070248d94600048910352000640000032000015400c4515924100d414804806528480070700000c1c00311100c0e1403025216001003200c07031001041d8208140008403054100c3e4001013a26450002000d440f104004260007440c40402d0480383c0359080c41000004603842c0c12444a04e003040650003e0481c0690b00050f43c40469442c46094040c03000c00c0500e000340441e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 611896753 1250 611895503 611895509
    0x905010803030708010e0618150d05070303120615030f060302040609020c07051005030c0a030b1f020606010807050d0b060f040b0408060a09030905010c021309050102131d060120060c04 81
    0x184d0110012613050107000117a8001d12001d0003221750b4011040100036248005800c0e4180c0030718034400603003280d4400f222040403c2c0a0405418014550310740541407010030001c1d12401c50804508010154980c103c0b103d42a2043c20046101c0c15a102400001c24140d08000e6110740f5101012480150940c01340050340404012030705c03403503180c0007004030510b801001d0a0020742c04100007071f000c49c00d20020701451111404c0c04600d419251001440f404c01c1100c140384801c0c1181c082054983e410868190032510a0908610714204031078018041e10a907502074103220388814020011782c5404040791308400000500685583d2038143d201c649a0040c4680300d640c0c8100350105d00c42c000e01c1c0c41001d1441c0c1d45525005801840c0000650302c0c0d622490007030707a000c186000402650041da004980c4010f214400059603010180c10b05030030607855401181d03a40e03640101003600d8280204055030010802d0826000e1200b000b0300d003455103000540155914090181800803a4124502402c19 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 611898003 1250 611896753 611896757
    0xf03170702250f121406090303070f08090705060a0e0a0306020a0306211b0503010507080403031a0108010b03090c060a0509040f090b040609061d0a021203071709040609050108030307 80
    0x1448000144400700301040c0074503000e8080748402003068544e441d480c800207034818200104400c0354061080d051600480b170300c1105400c00000c202d8021b40c001e00802c0500721a09010205041c6100b0895a84001d401828000c0700009220b00c41203000e9440300400359030080600121945034a00140690040300c01540482d092050103e03c001f0400006030303a0501250400c989500c460b2100d44020244100c0d141000324500800304140d202809075a05c1400140c0762951141070500c0e00400b11814900c54103084502044030700100c0c0c0e80a01d442c2c0c11100d07000c0240c0e0301ca8a6000b0084d080c06450078003da8894030001e91942c465801c00d01404c138122086130100044140380030810141d078500300004100b52030ba00c0015000404980c82048120300404c00020081c240c00d40654040170000c007410b220354403c0b80710404524068034854150148100a9418105640d43d03c0e07040c020311810541c550034003c10411500d0300c07254010740c014034503032030203012300d59503519003130349941c015520341c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 611899253 1250 611898003 611898043
    0x210501060602061324230609160e0307050a03150b04060b09010f0e040e0c0906030102130e0c12070302030708090c0a210b0106081f050307030f03170702 67
    0x11414004684281300d0100703282445a000410396841d1482030414038046500010203000c01e8008000f44078003501120050305400310486441004201c00c0c0c4014903540c82400250100008030b06520142002d00744581000c544c450766010009040c0b2454cc0c101c00e0304a18400000002d2268405c85083d13910340c803803810015a1520f2080c1b0003621081d0049420101c4100a2035034a548600c924080900d03440c682a0203c22454000030180d80750075003020031540c41122006440d00d001c4900c02e4101d94210000c43c40c0c0900400e0400540603603218101d403101c0ba140001d03261070000c0046624900c003071510881c1030b15003c40060001d40050780e00c0d50000c0c1b40c160005000b80000a00c44083c4840182000041881d0150f041c405481e42c076600c07990720043c0405030002844003845c02e400703000141c076221164980360118913041011065500c5002400c0d807000c01c0140c0700899000213580e000400b1848603802e43c10f064410b5400f18250625500310761080040c0641d011070a0080841a110168 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 611900503 1250 611899253 611899259
    0xc030705031b07150f03140108160b03040b0105040b0604031401200319020309010e1006080d081626280911120c060406170c07110d020a21050106 64
    0x580d0b0303c446004941c070031807082e07401301800303401842044050750691070085a0802800c030b919589100a0f40300c114907a110b039165014810b41d441425020b424001030341c506510381a150900c50030818403a1754090340c1d5035880c105190311000c0488000e16009a4a84c00074070300d80d01014001d00c0f68036981c1c0940300d10b1194401860403d078044a001e280040c14959200500481402c000c0d0b001500036500ca641c1c5109803e00b484c814041c0740b100207100100020307000d141511482c10400e00040f004d042042d1101000514030301000300c07101900061a0105c00c0c00148140d80030403610b4200c900040d2180f0b072701040203600c40484520700e04001e203180ca10502c0c036551407031025244c59030390041103080102550104c80c01d0401c1100c1640c240030301100e003403070181d01c0455441c3e40282c21010001d0021810300720442038803840550010001c4140b00c2c9800705036252910201c0300800c5080c03241040300b10b00c0055540740070f5054060b246800e29440c030f00324151b00c141030b140030590302110f0a5003460000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 611901753 1250 611900503 611900557
    0x3060109090b0402040e160f0f050619050c0c150d0f0e071707030b040308071107060c0602090a0509100302040e0303160c03030e010c0903050f0109050309060f0c03070503 75
    0x7044119400300d803020103601d441d030820000d00041c2c00c1c07660451140c0800f02d2000200003040c2c90041c254243c40c584403a00300003030000e1000c056088039010311403c00c0800340c80d90000c503030004401002c1c0340c01030300c440f0310000ca203081c00600001a5402000081c2c5e9841401980000708032a0b880c04104000000b40d9400030780c2910048030340380e40b45811400042291607510300e4940020b0310044151520071752695910300341c0342ca003583c090b070005142204000b43c50341c2158040d04101d04840040c2091883c1c040c1c01010b8810b5903400611894010501a5050f20b550820402402e0001d100d05414905075a03140b05c002460722040e44140d08050b03103c00d101c107020003128003503000c01d105114201014001070b10010480a0110105076031400c201107080002c4c8100c0c05501c01301c2c1d6030350307070210b00d541051807505071641e00044490349024010000900c0000440c3d201d60701c1503030026111860003070303161414024008052214000010000d042060102c02042c00680d03008000c144050000c00c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 611903003 1250 611901753 611901761
    0x71707060f1b210209060a020a050706210c020f0a03021f1406010e06070507030302010603110603091e070911030612120a03091e1406150607111c08030603060109 71
    0x502c00303d44041c20328000b00400c903000c41003810070391070090b1819408801242c0c0541c00000c21070700580010b581c0350708014052002500038a21480c001101110039400008900b81001404130140d41cad03180482c0c8581d00a008154181800c0f9003a59066015414065201d021f04202c0b442c140325460480d0748529054070130300b04c0c41c2c01c00070070040700c50351200015528000410f180540c401c006100e0980007410400540d800746100e64004103c1d1803551500b00d410109421400d0b10402003401000210440094002c45e841300b0504195807582030224400d040800580001c11520b0600e6501b01c201c40624000318040d08081d2900400407208020403078860003400220501a00200010040d0600c00e802001400707010340c840c0b510305443c00ba03043c400000c65080880707e2040014402e024403205101441d0300c04071041e042c80ca82802140014040c0c460301e00010522590007942d0394003601c0b0f1a04008107588102211030f034503841c5e418aa044c82d081156014400c0c40303180004030340018030f809 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 611904253 1250 611903003 611903051
    0x14060c1804050a09170a0e0121150527010801060806070c020105120a090308070503060f0112060b0406021e0111030a02070609021f120506010c08071707060f 69
    0x5204900030600040002402e0042e0540741c905495601c0351001c40c0d102c2c9195050f00428002440d134500713501c03502030000f1207090441d030705010a20103101c20101c184150804c800d039045400003a240c01c849080d0f80b008819810031500841860804101c6001c04000744100d40011043c20401daa40c608849083c0c800358004c866298001c60086100c0e1400b54004102040c0305040c0381d41006003000c100c2e112000b0450741c03000ca1a031039500741000e05400c421200d0b08444189001841d518000021540500110301003d04128002c4400c0003181219031021001d40303e00c0d4a580d80d90741e501c030b1009644032140c1506111841c070208407a01545d90503c40c00c816005000b140c5811130752080450070081d0400d02c0152059601c90341c661005070b803000150080359150700205010002d1049000f0010705840320101d40d494585018403000307a80180c2222010307a80b00d581f04c1e680c3e50861820384104503404030055010100400c0010400106401c000c0b0005800d01041180028140080e203207841c00304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 611905503 1250 611904253 611904277
    0x17070e1f0314013903052211040e0c03100203040b070c0602120406290d1e050a1101030f020a08010317070203060a02040801060503030703050f0d060e0414060c 70
    0x120040000034040902c4820342c410003000000d810f481c490b455a03d0001120090340c0029140341040c0c5801d500c003500c804414407500c2d0030030003450545050380c40701a00303c03002000404081c40c400e04200d1049582c0001e510003600c14000f9402c0200f68990300c000403075a061081c024590181d00da08803501c00d891103990041284000d60700c82e09410343c8c0b2038004a10561303050f40c08010081e000c2481210131400f82c2c0c402c40c40020501c46540d81c0701c985100840c11011440300100b413200032139440d20b84038510160081100021441c0340a940b0f00c440c4100b01c401011030040028036010b12141c40303600ca52040081e201804a281c0303188844049216104546000c50b04600c0140003068008031901409800100b00510701411500000d140041c00c55104000740e4000400b0700c140e510a000c0d00c2c008010541c02503040c1909a60060f11500501291100c05140858070a0360300400d078001e00010044405240c1081c18581004601031040d081c1c078454074452407000c51002140311013199400c050103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 611906753 1250 611905503 611905561
    0xc090c16030806010e030604031205181f02130306020304064d0c03041805010515090301180501050604051609090510080d020a17090109030807050717070e 68
    0x65070305440d00354000c0c044504200701c0f042c1841407600c0406c480350003940203868010240514182c150140c9030018450f150009031103003040c00144e0000b522289400d103103464203040d0a100b107130b841c00a001d6080d48171032098814000105012066004501071400f6810070710140030490801400003c2e08070307141201c600318640904403c4011000d100a0325071900c848072505c4412111044590001c000c400c0302c5420019041002c54180c500074003201e01d4540040c8025031400c80080c1050400d5a480c01c50aa00000c0001e416a0b00f944410051024200f84144814442c10800d000b000100d480501451901c00407982a016041e00451114013541d40da02c032041c202010f6201034940600032105040585030080790219042c401d0301521819680202200e14050400f4100038440f03040d04600303800204014100c40c0d82c0b0541c50010790b034020f50b81c50382c0e402c800d14025203000c00c0c50340001200c05488040c0e0700700c28804500d130412210301001654036a101d140071f401c4d508201500c4c0049600704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 611908003 1250 611906753 611906797
    0x180317030415021b06011a090d0303020c010f0501030201030b031f020703020120070b07140d1e0510090614030c0405100f060924020706050906040b0c0c090c 69
    0x101000a507072051051481c40c0002c00380c02c1c0544240d03000f082c030301d061018480c440d0b20038044040101c40d004040c0b81540568110035941143c2c00e522406d50258060845603a45100b8140240c048404005444d0003c000c0c0b5a04220000003c00c001c1c0012800a414850028424030300010725000048410740104c01441c0030106000095100c20811003d554840e2040d0010100043d65104a09101d4098941c0c0b0006803414604405009084505100c1d03110016100e014045058400c16014014005021884600541303185e450031058544d07503605220400080040090b0000c0c11600060341c10b0001e103407030300c406c00c8076100c0c1d101c03019400d984003041d1070201d49440c2c2c201d0398200124140c01c00300c2d2038407170701400314040540d0090808681412020030954403c442030280030381040d540248020340d5070354002d40719482c511030794081250108803100325035525800c840007880000f40b09a0f5a44400306000d44540c420011244200712440014031566050700864000051480ea00000290 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 611909253 1250 611908003 611908043
    0x203060f040209092e0902070201110304081221070906121103040602070f0b09240702030d0e0f01021b0d09240201060e04030e030c1c061e0212071803 66
    0x170440c0113a80d0700803910700341d912401c4950044800500344610700580d03030b040b20340009043c842c030340f000c032540c00c1e80b0400c41001007002c04104503495880b0034040b00c1ea01c1c22006034001c01e0a403510f03000c01e00d8060303881c1030010560f0861260030880b44113484081c3c2d903c0090003c01c0844149190528100300708000046c00519a58001e0012620503400500a42c0c16a05c85071004441210545c00f29030000c005403c08602d070100c0d1065804000301c070280f01d460540030003920f0b80150504041405d480d2801461849030600c00c4510801c0103100854460444840011807003100185c80300b624051154007542041c4100188401d075500034890340200e900c684262021050201c89080c2195601c0102184482400302c2d22402035000e9035910001030391070b00c02c0508024001c6078032441003249075040b042041400d10110561030b04030710000740b5001e64240500c0f03803c82c064200860540b0018040745041350240340d01340078000d00d9030740d10b030380c08600348207000710415900003d40741030360386040818000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 611910503 1250 611909253 611909281
    0x10b040902070c0815070327020103090c051f030f020406091205070513020415080103051c0c12170f190e0321061002060f160903050d030203060f04020909 68
    0x521800c00f00c84a10354492600b414800101054000803025a06001d5190380c1800351000300c4100303440009652000780007000e0400c20090000b414141c40e050039400740225680501d000b000054100070708401e66126141c2c06481007032695001c24504003030000714485900c00d440035a1601d071946502076051900700c000710744007144100c4e014030980f030b03000c659a00c903106071950300e50a503900075856038101500c019078003401c00301c0c100406c46180010000b00d840001c0070b41c446007044840385400e4035074940444000e217400070080c0038519900d0a070003081d988405c0201000f124001d00310520740300e1078038070f00041f60155009942d11000262900c280c0c4034942c006001100c0b01021249010244007a0700c4007030a2004040c1924030180041010506081e0b00c030703002c2e040c06403001d443d051500c40950007090306d01422100451041c1e040d040b002034080c6d40f04e04042c503002411158003d4800d00001c020b9401115060f000e0411483d000f4864180350096440b90400100500b10740d80d105141c981c286 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 611911753 1250 611910503 611910517
    0xf0209012c0904141504020f0306042402091c05010c020a0b0609100503010f06090605100813060b090a09030201110a05180a09020a092d06080c2503110303010b040902 73
    0x40d80244d0b0051071003a810403881d101c5590400700709070103191500404c0050300d00644000d010350810700c200f01c0001c0010300350751003c20400740d4240850580036a4a4002c1c0103500d0b02d660094580940d1800402c044a0320078640b03840b42c030090107890a10031040307071580907980b0000c0502983c40041622890103039441684021141d01c1600b0302075440c40002d0946030006036030b410565503190280b1021201d4011400038140a44400710320390a070340030041032084000d101c1c5e00d08000c2e031002d00c420400240c000300030041000300314a940d8203150041c64020241100304401640c60b144520440041c084d054071400c00154950a04003524142e11230301e000d41504104e42d0000c0319000c0440c00750303668806011940040e580b010603850401c6101c001161900c010000144608a001301801800108200941301d052400b03071146c1c3c40303049010440d405a4103a900c8209209202408100841c02110350114040d036200c00b400c04004441035241d02c402c0c0507100000c401000144400302d0160014489 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 611913003 1250 611911753 611911763
    0xf03060b01050909010e04050d020f0304050402180a0f0e0106020a0f0206131802071506030c1203030902090112150908030109150302030307060203011e0e06090a0f0f0209012c0904 79
    0x64840f0900001e0701005091300460401c814907014001800010030000c00b006000d80000d01d5030380381c22101f00d6560301451092a11450300010004a5800b01041c01c2000c3d42d0017911301400700392611564414005940100c0501d000b2100001888a10000d11186865008907101034901215000c3c4420b070b0344040074010414481040004e420200000ea0079020301c0d07602001600c6001511704814074804403401044c1a46c10100244046a0519040ca003160001902e800c0c042e4500d00c1c080d00a40f910680c041d510116000001032030b800b4081801b42c13668898207882c92000c0a4041d204100d0300c00c0d1a000d0729848040c0b0040c49180002d61040c18640b01c40000281c00690f44e42c00a441e40c0d200150496a141c2c012004010440c0c10f1400a207001a881204c401c0d640c1c20003081d0300f080040106494030a40c21000444e070b10380b015034030002c1303041d414038000c3c030070307110030070488030182d845200070f14000740030100f01d508803205400705007045000c1d942ca95100e10122104002c5100e0001d041511 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 611914253 1250 611913003 611913007
    0x403140a0c0b090a05090606121e100e0a09031d012309031e2e0905010e0c06070203060f041109040f03082d0712090c1406040f03060b0105 61
    0x10400d080600d5006249000b416642c8003101024052400e005130702150080ea011b800340046036031408241d8a409152010902c3c02e0f5460040203102d2018071241201030301031030020b10204000b0490b07100300b9a84080a100c04c507440f600d40850854003031103006000204190042c403c00d558040c0e6450b4054414500300c00076040b021209811281c96100c80c448034a400691140d4a05061040141d45400904110a8040d45d888803545607500304441d0182d00301403101210240ca0031001407440e058811000b088a00c01524010b4000d121604903441e4601c5041d07900314142c5002c204640710264081c01801c0141c1780c003015618404009001202c0c0301e11201e9030080561140c00040c1d04c1b0b0350061030f50312200289401e001d8480344000d08410b00740c01e0614651201c00202501d49a0840c0f9030000b03034a842d03940c000d07044852048240d6501038484c1040080000d200c1680c01d500203541344000003040480d600d104214442c803481c410342c1158204800200003151096204015001046c18014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 611915503 1250 611914253 611914273
    0x3020106080d0512010b03040503070609061e02210105011b110607050604171204120210050a1a0607031e0905130e010506010828060b030f04050d08010b040314 70
    0x1e04100c0c2c408102400148013282c1349600ca090f0349070f000d0062100061a516608140e101c40d9143d1054103409014240ca8409001c20000107602c28551001014081c001c44841c8000321000703940041445800a14500c2c414250138042810450403264141c55072130b0181040a000701510141d400b040c2e4803c0101051200e29032100801001094415000f8014500e03061038180603640740c1400700b2041d45c90500100b4a14160a22900c0c0c100c1d400c4012a02c01d0400850102e140103004480611000c0c1403030700f40034040d03689070020404101010000100ea890007400d00505001740c4501030000392864030042c40503103019020708000780c0c080c81c11103030017a210004985022004402e1501c0c4e140e41b1a40b00e11001d00c20710030690021403d00c3c0407401d6003002e2000000201e980d00e50b101851410225403c00010f4a0f4002002000c1d50120f86440e890302c542d8048240508a80945090007010381a000082c490100356050740c0b16110290700340b83c19034171048100c4481d580f01c91400c1c49084204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 611916753 1250 611915503 611915519
    0x6150a030c050f04090207020a0f030b040605190e0705040b0609030d03111e0901080604090c060e060c06040b041101110304090203060429040614130b060702120c0901061e0c03020106 80
    0x1384094180400096580c0c1060b1050164001080e40480d042d0880e0003024070000e00104240e41d0040c1c1c10980200c1c4580740e04512041071010807100031f41c4145031144058001e000401c40c0401c0b100102c40c100010030b5010188a454400c05120f40e51503040007052901040c0030382e1045020107481e1252904211411410300c03003007881d10035100350907500401c500400c0c4d82e000754880e0b84201d056505200f20701060380c07200c0d140d00142c02090248010b0500600035616194280c50055542004139003650800e030802000c050360a40c0c0c01d80d5214004014075585502900701d11030074607030080066240034544500c100c02500042c00071980149c8030305001c2d9034110b500960a1506400100550410400c50100802c50320254010580f1141800c20080c580e5541c000b1940d10082044004c211502240c002507500c1c41901c100075032203810210b46100c050800100300a01d42015250040166241c000a455a00c0010300c824071021002c016102c041d8400c44541003820b00c01c1c00041001c1d0b07150310038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 611918003 1250 611916753 611916757
    0x12020a0f0303050115050c0c120102160f02030706031104030b0402190806060906120c0103020d06050d030504030b06030102090a06200d030c18030320101407020606150a030c050f 78
    0x55000949800c01401070141c00e0380c00b00c0c009007807806c1052904070030300502502c5440748810070b440b525400c40c41c4c48440c41c00b034040f113020011000b40c4819841592070601000130002006a00078800d07102c000c25041d019200c0d1403d000f084c6240181881c0c510f640702000300c000180226040800c40711503001c1190490076081c05801c820740038080524000090000c0c0020040c001c2e480b410000321f49140031070000c44d9400ca921000e00e4050b913030350300c28007409025050f1036101d56008858050800e040c10f07401005030098900c101e40d29540c44d16140304040c283e00901c400c41e030784169940701c2003010768045d9452420055441294a4020000c004400e051a5600c0402e0700440d4031100b40d411101d501c8071605e030042442c0a61824054110780b40144500c050f51400e02104501648446507140c08200500742d0010402007402030a080413620744c0c40c5d038000e6030200d016110749000300e9200d00e8402d044040d494080c250090030056600710880c081d24070b601c80d00d0180042040078150100340c40c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 611919253 1250 611918003 611918033
    0x506030c040801050f0c030c13031202030901141206061b0601081e010618150305010c090302010e0f030a080310030c0b03070816680d12020a 62
    0x50054440c1c0c41c2c4090b150950f80010218209800c0e400c040100c80301d1138000303480d00019014a00380d03c940000302d01080191b12600064102c1c080181c0298480394001b0060482c00000e0303890071404424043c0c007140a00668a041c840440d80d03800088842c20800042d14440c1071165a035046101c0742580f0b6424948282c010069a8000c5424400340d05500100c0040d0016000001c00241e860025035501290862907400c8589480340b1014001a400701c1c000c2d0081e581003402000410a4010040d001d11150310049003c0380c01d0001d250700614014046da84442009030260080e80002c0e81d03901440e0740002c1c52031120348003c10010000c00c4c0b8183c80345014011280c0e100750742c1d00700484050220000284001e042d1701808420070b86c0341ea031007015100c0c000362605944680207005801e4000700308942c4090790044040e514095a0f084252031140082480002c404118404180140341d0f14040c410322181c000481e05a40e800255a1200c18103034003400d441070340c1c00640700b45d5442c03440700d10500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 611920503 1250 611919253 611919271
    0x509220605030601051008150a05120c01121a040b240903061503070303260c0d0b1c02210304030503030708060a0332070605070c0e060d080d06050603 66
    0x840601079030404112040c0581070443d112680303803010303440003071031044002c1401e5125541021401c85c0764039490400006860020a00c04070304000d60140350341c40d86048012400a00d690b24000e0104145101d8410f80d18550f420402440140500384400340218440854200d907040362160098400d11041c4c12142c1414444c06070345260110801d883d0090203000c0460b100580b20031042c07540e800280200889600d400c1ca1000000c03100d0b01c070344881c0c66000440c1480804182006840f41d4400c00400074900141420082092a1b01c00d00c51013041c444080c00040d90242500405480c2801a0307850214070b0b220840c0c459013480b90003500350340003a03000b2101e41e8008000d100110b50801e0050f03134030080c2a21207200b242d180d0f844003400c0e590301d00d141c031050032015401d116048411040609a032040f01c01200c41051f500c250061155216110594081503042d42c049014500380a1050081c03400800c001c1039940c20351500c6205900050340c82c3d0b02280e03100070000d290389521020718403403001c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 611921753 1250 611920503 611920511
    0x306020c03040815282408060a050f010902090a080a03090314010e0a060207080c06070810091803051308010903050d050c0703020a030e0a0e01031506081c050922 71
    0x302e0301142c42e02c1000500e0520301d200240070070070545e0040712066085c0010342c80b8405102c88800400b40100301e814103c10f00c50034080e40b52103607102801d401c1c80490b140c000c119042e40c4c0e1400403100456006452481c64401c100d4010882ca0b0342d507030050311a592000b000a0f0b40c180d40c42c90960310302016a0300840201e04503001c1041405604100035000e461807100900c072040c1c0c11008541c031440d0301d0000804059020a00000f440003001c269043c2c0c1e8052000c4510f80c0c202410094855081200d054029180c24000820324142900943d0364080034146c0b9910780f040c450f07505036070603000211100d00701020304070001182142401141d800b68040d4032101e40e19403600d2005800e8681c010301c0b0b499240000c000180000e68006031003902140c0518100f02009089000a60301880303d610504400841d80004400e1007003100e000304411800ea14100980e035920b940c400e403156058140810000035241d08401014042c5000300041c000082c4615511480040301c9141c401010020120241d91303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 611923003 1250 611921753 611921759
    0x603030913052508010308030709030b04060b040c0903020d1e0c06080411010e030a150e011d010b01020601080d0507030513180605010306140d0f02030604123e070306020c0304 77
    0x540402c8207030109401c81510070450300c3c500040c2a811041c440100004800000104110303c1341000801459029203550780740c3c01c0134205070300500301500480d880b0b03600d0000101ca41c60301504801041340e5000c1d24007940e0f040d6680714903c03a6030401505140450f501c0401000017580c1721800009003401392180c101034101828240104bc00a00000381800111092400ba0344d42c00070710954600da001245801d0804140c22610107050440345002c3d156082842c44001003584440203005090280d00030800d040e810001260707a5007081c410341e001c94018400b0a07014a12600044c1011130007414079901d04803680100311840f2206a100c1e031414110603c40c5001a141e47c0100c43c0286002d1070188070309030034815000300c007000b4408414415010f60b40487c0400a005c0f0a08030782039001401e4555a00d890f0401c40651b5105400810010b0226210b0b03c040d80f440000ca51540780402070f103000c03403e8a2a26003001442c10134022101489030342000000121680020248440034602558035545 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 611924253 1250 611923003 611923021
    0xf060e0f01060c03120b1201020c0c13020a090b0313020d030c031106010e01210b07051b060f070518090420060412060507050706021909050103090f0209060303091305 73
    0x301070b0860010400319507900b00c08698003505902890310803510010741100c00000040d1140082c0300070100c0c0d940041082c80304c1100c04101286820b409440c86401041d8540b0312100328421002034402140a00c802071120410b10310156a20015011071404914140d8000a00d140c081010407000650900c074a0420180d10940304e4000d0084500208920750400c05c1910340c1d4481405818202c8174546078407270300e01d112100007605898210550301c4e983d0610301c000400c03940c0000c60604240c5018201d01d201c402c000034450340306003c0410030880588428004943c3c1c2d40c4001d10b040e081805040c400e101c559281c10102780210701c11213000d031400304100482c0c0c403200c129501c0c040c440c11003404100100540134080c0c400055102d1000100f540d00d514059034a8000c041780038181e42d1000c100514451080d11400031116525241d00b46002d80c0c5400440954601c8000200309001001c1c0385d030014108680da040e0015001016207003403000e524080b40d4040208400200c40319290130520580c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 611925503 1250 611924253 611924281
    0x50f0606011d010c03121401090f1d071a09040e0f1e0604062d02090103110f1c0e0a11040515010c110607020a03060b2e0e040f060e 58
    0x940044801d95014041000107010130449480103800d20220070b140d1404001c841c1d024120b40b0b01c81071107502d00c41d42c41301003240080c91100ca00c1003906243c10410346690000c503805414411103500184010b5080c10311180a90810110500c1002024460b99035035681d80e006105100185600514144e03806084861506001d07185103542041c81c0003d0000182c000b003070580e401500850b0204a902c0e212a191800d615135001c01c69a544444480c0c2e407036a040d0b50010202c00d0003da84c01c0c840c080450420b04028443c1030070007110518108041010303c2c00c20a6a103180d408040000502000c40c2100341d820852040130494511642403030b08207403464107100712508000c3d045060301c03100e42070f50006008800c0c22580940a07003641000303030b1800e0766460101e0311140c1e0301600c08544140d0301c1c90580d0240549000c0c071442860390461110134183d042075810010522520344400e01e801c5a902651117440d108061504981c54001000805c0d800b8024180108500b0003000384034944446106a50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 611926753 1250 611925503 611925527
    0x3080c060f0109050106051b03040305010507090e0a1406010c0609051e0f0d05120411060f0a020d0e15180415150e09070f02030d0c0210060f030825050f060601 70
    0x3c50b01e40401441100e501006603014a1001c010203100c0148503814580f4500441d80020165801c00c810040d140d5403000f01d55044801c281000380150301c800c0302c3c00003690350785480d2841800c03051002585070341c4034103400c00318240914000160a402501e0780c40c241100c603071100e0391905140300a400e4a42d0f0810100c007142441c100a0310800e45400300090061003822510340d518100340e004241400b01180c615560003c004001903682d0b050b014190070181c100a05003805805540320f0f441d2164080c0001c00003442c4020004003075440004102d8155030041454607025265075010310456440e284503054117644003001d408203048c5484d14140251245042c000100070840350207403059220000180d40041c000d0400c00140c45481c0400ca02e1402140080140c0d6414a4030030300c0580d40100d51070405c0458640140b1400791240c0c0010110540c920004048484c02c115000400107041c846003113070114401901c4601030641c50703e40ca40821141c0130b00481e040710041c09160f680001900c019 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 611928003 1250 611926753 611926769
    0x60708100806060f061c020711012010110d061e121e11060a270807030b060105040f080c130b100c02040b0a12050f01200c01020403080c060f01 63
    0x2051400ca004a8540e0385043d0f04c0900844005c60111159246100ca480001c0ea0041303045450f5901810000300c000511008070780484c01d41509100341e4a0b00000c68400b8034507090050600400501041008144c0c04140404070f8409125445030a0382c51300400c0b0040107004403040c1410a0840c01c035031f520145501c180781c0b04105c00c05100c0010744842c0075405040140c144168911140c1c10250002070085000700c1e4003200000b08440d0450704600d01c0340301034110308880c56154030b140d18040040c0d104d601507400e860703104601c00c00024249114140d401201031400600b800d03a1444452030305001c0e40c11480c0d103034101036030400d03050415a10540401146800034003050310070a010402e405031070f51410041005000f561301c155110780e08000c240d03050150500044680c1e54101d0b0f0592180710034100c80d030340260b125140c0c01420501501515140c49550310401c0280001002d1003980800d00250300e80d50240000000705101c003028042c81c0c07400d500602518a4415901d044041d416041051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 611929253 1250 611928003 611928013
    0x2011b051e1c0c09090612060e0c03190c0e010609080d05070f0f0204061815240c050c03010203041101080603071802090103020405131d011a210607081008 68
    0x4a25924140b100c90140c10b902c0c400030b0b5091021900703c034030042c0754016003450b0781440400a21550020308100031113005007020816035802c0740203140c4540045e150280c0c190b1108444040620240d003160254a10400500340700944c0d41d0016401103c00340e00c102d010541c401c004005c00c440900c4602d103101510301d041841c00243d50b4420140c0054220064140b6001340242c1085440301d17403000e0042e20301c03540881c804100800c155409401540c00100c81221000c41c00550300588010940126504849030081942c480000322500c51050030709a0341c5103c1c800716040789407020300c000d5003e6802a407030340c00c10320715a10014001c0c08000d85030500a41c0b00c50010002c03179010f036408140000b100140965119902c4004030701074002d40e001a980004500c80c02800521603500c0642580c0700e28039211840000b83e4002400c2b40c407586100e614180401142d1001c1c1d240c1001c2e04d804940c0b0709850361300c210903400074030303031504208680e80301c0441c03551400d02c58003698203041000204030341c0300282 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 611930503 1250 611929253 611929267
    0x10206090d021e031c0e1b09040f05030d15330809010f150807120c12020d06020703020604020f0d05120d061a0409061401021c02011b051e 61
    0xe50311412204610030303203e142204182084410700403030300c0c04040d10715051000040080c0c0341004083c641103071200c0f0712410004032010340d140c041c9480840c50041c1014a1039599440e0000c1807002070204583c140010408001060707003a2048819003200c100301c1c5c0c030003a801e04844503010428614040c81401e114600c505025805080c140c80b0316207145481341694840000e070a0250038030f855400500c605000e070401413942220416811201564100e8000507580e120800d1041d10300d00c00500100d0b111f140610161182c1e480e485070381c6101a06403941000e07280c0f02c6038200d8201c0c00c01240140c1101c01400250b141c100e0311030110b0700e0226030540088030165211551159003800150f000304010861010014890b07010000801907645d489189000c869400c5419601ca8000c20f42141d2a0a1000c184061042c407582044d150680040c0441d030603550704101c9100c03d24079000215900e0751100f503010480d8203451381c000f2000b51655a20358001c00c0018106541514000c050010103100c2e071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 611931753 1250 611930503 611930507
    0x161205030609070309030e03070303080a1b0c17120117121903090812012706030f0602070224090108090303070206040305030705040f0b041e050114181c02010206090d 73
    0x1c90f0b003082c21400e0002c0d050a2521302a2840a00a003006505005160b8008107040d000051a071081c18083c108024521603064000707480190124032500081c244502c000c0003840d82104020b80414500c0c250703052142400800d180400260042d00b050303900d5146e08a90f002d820009a056010441c400c0360400e41003800011084415040600030542c54000080c244211a01121500002107000010941c2c4900345119204c04503101040041d0119011044c59996403083d02d06a81e48481c0503102c1c61030f00d0b226040a500014020b81e408031403c4441652a01c0e5145011420314280020588a020040000d046154010a66030044c0c01c2003041185860b4003044040c1d1007607050030841c0c0c0325120410300b103c16002da0f0300300c09003c0c45a41000301e1083d4007100648122072010305454880c10a1071409890081d0360301c140e071301141c14002c40e8429181c0d610046c169204a02400040c072807400c00014001c801094400a09280038950010640d40e040c80380c0c6a00c40318100003014800000800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 611933003 1250 611931753 611931769
    0x614032b03060801050f090d1e080613090605191b0c08210114030d090501121e0504020910030b0c0a091517090705130b03010608031612050306 63
    0x1595004018422096034903000741d0040024101e9040208603034504030401c1180d20406a55600300b522441c54407120042c4102c03081e440942540c0036229075181025000e036803000340034106541c81661140c202031000c070751f44114031001740100008602d07401c00003021040340160341c024600c070506020006103e0021024515130900356460070301c18050090070850203e025a4200001e81c20000084200341100c2440440c103071210710f24040d400c010701c0410140d0b40e4040c0c8800001041c10f07000100500d600440100e045c10401c0310300420a000e850805032040991440ea60715510360b03840c24030085d418080e241a5001042d5115581402d04603200d040c09600c00402c00d002c00c3d100020f04900051007031600724020195040250310801000c4e4002d8801c0c03001c07596402c001440b490015030b9000c4000b9468003103c1c0b015114401d1035045480300c102808003129016010b64a460002418200c2000102030b003107032042d281081e0641500d000f604070751100e004442006400c1c07042c000d2940d40d00704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 611934253 1250 611933003 611933053
    0xb0a050105180319050705010e04020c0d03202b090201050f0307050706020703050d0c0503060d020d0f050d050a030c0c0b01170a0206180102061308030103240f061403 73
    0x100b0000120781c0540001c0c6000b00f81c00d0300800708001a181c01c2c0420000241031426113900340c8600ca80e040c030781002d0204a011b004daa9140913400783c0200300005000303a00c00c1c084107440e03807850320300d007841c2c14400d204642c80510155055203044d941d11151410303000d6030740504045078606000e0b040c0141c0008086004541181c2c3e5030b400000701180e6a5801102119030782540220255110310f04d40c18041d10b99000700343c0c5640e0a1b0b04041e0b40c03c440912030b0007100d1191100802440325580d1036000c0c0000c0058001040302d000524202150103d00100191408451607545540d41c90900f128010262420003548109014014101e20005001aa407180c107440d2078885103544c0d0108403a40d40e182c103400000c042c1d0444000100c4081007002c62103018544031003a0212101074503400201c0c070000014900c003a0000005100520008a000450300090103032008801e27000ca90400c180803c54840501140b080e5507140300401100300c801c3c030351048500e0114090444440b112130445621220b01d0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 611935503 1250 611934253 611934277
    0x90d11071208181806030c01141603020c0901090b0a09050114010f0e10030203010f08030c0604120c060c02071802091e01090305150a15140f0f1009090b0a050105 71
    0x802d4034032114003c800e040b061140000c103424420072260401c02602d000c1500c489001e070080090741ca101e0350041d00741c1c5280001c0c20050380d240440303004c0d030105074003200c0004034118000c2816000c810343e00c00141c14068140c101000940300080300401141d1703800e55100c0c00050b4101401003202c400c26900c00004c868017820020400040e0080407220035401c240080d41c0124107018190042e5850f902541c16038041c50b44d4581c601c0e89800e4620382c0d90140030001c43c210740c08140043c0c0003e407002103241e03981d80e5034101510784c2d038025640c030001d581c4035800100047e03021900c10001d10ac01005240c0e000860b00c401145404035000114582c0c2d64034803840402c044903540c60124991080c0c404a00560b00030007680c5a00074003010100e800b42c000c0d58404001420011640b00951040030800119040c0050108503000e4001c144814040b07016001540096000c8001d641601c070034901c82c0101900c0c2e543c810b409420b01e960001255154201207005102030941407065036045011203800c0b106503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 611936753 1250 611935503 611935507
    0xf06080d031d1b0a030b0f010603060b1c021602090c0a180608060d24231329070c1a0105100c05210705010501120206070f0317090d11071208 62
    0x54001300e4841c0d21203600045c801400f80b003c01005994110303029041c4d038400d5600340031a41c1da5551840c0240100703103150000c4104c0600017080300c1d0456006004a151070050240041c1403900090b401c05800c0310a6648880c0000d01d640344d01351300c65000145c0020b0b440900d9482d03400e241000f848800001c1070140079100011039507041c84040d0040001c65031821011085090312804090040c0049000f0070b00d41803401990306000c441c0c0001034510071002038000c15040c42841d25142c2141c4107008810404041038020214000c0c070404482d0b104d116640c03520380707181105103082840c101806d042201d084103030100500095480380050150100d151422510740343c410700b4102d040c520b543c076020803001c007030302c91648050300c02802611415016070000c11141e070380c440c800020f078030001070025446030040090800050702c0c2819a451a406407400c0640420401741585030340c0010f9807010b10b030354824640031000c5a40568440d154094031070152004901c1c00074803429140e080ba41c02460b003100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 611938003 1250 611936753 611936803
    0x3051212040b0603100f0606020c0604031e291812091201020c070303080612010c020706141e0c010609090818031603032d0e060a030f06080d031d 64
    0x300175500d0500705200040007444807501e01080109841d100d03020140c00340c01422440c0303181050a54080325088020310a5007620428000c051062400c011603c0d0700070f801e120603070f01c822031086001c11243c12501500340d0a00e08903c0c48465144d000d0a40e03158403118441209440810a0b2004d044003a5400011b104080d405203019004d81200e02d00b043c401c5040c00028035a1140c40f0078000c10080e604010600d41145000307090358041d001101c003603170000034104441031040702c984003000384204020f03040c070200d0310840800044250818144807004642c0c01c920010038800c0f0001009071080422001140703a66800130350050b050a4156000894450025510306101905051030803d00040d1080d8603468081e151200c0daa031880c144160903c04101c4450090303000300c1503005152900110440560204007156020003a0038041640b9119142048400f500900340036040b0780d40607164808012030014111154038403200c00605028249030b03043c04000c5a00c51450086030355110326441 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 611939253 1250 611938003 611938009
    0x50322090e0d03050c1b031b19030e0d08180301060b0c0a0b090102160602120109090807300221210417070b1b031603020912011503051212040b06 64
    0xc000c1072960015103d88403905e800c0001c00104408c0140d42441918031880d6840c0e2aa82c0b82000180c1441e116010000c3d40424000c9030b40c0031600c0c000500040b080360b95562510015000b0380c1d9180950402d041010f80c07249800e00a8030b0161580c540c01500700600302d07107940e50342c4e002c100700645425070000201d5203c403003e4040365561004400d0141d500143d034a0400e000754400b00c0c900758400e00e00e00011880302440e010340307108503400500c80c1d802c0100b25140c8043d040c100c1c010046541091011400101c00301900c40c2c2e0a894294014005440340c03002408804900e00f030501d41034040400000300311904500018101a50f040c1000826544900d840f440030311940043c400300c1e00002c60000108284603501c98881c0801c9810300c040200355004424203400142c1d48880c0001e0b851b00062100c51080c2e000d46400319004101c580d80b88101c4480300c0c01c4401c0c400d81c200d00d005402c034091040c071804010080070941d5051800d407504242400b113074103040d40134000070506031920b400306803255 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 611940503 1250 611939253 611939257
    0x3040524040305060f0a0b0109150e030d0c1401020f0a050c01020409110711010305040b1503150108070e07020a0305182205190506030721050322090e0d03050c 70
    0x80c1102030410358454880c281a42c1d14070303003110b007800900030f12800954000b0590060811848060b11840d001d1410b001c40100a802e64030540c504101d0149103014543c1e0703040050940ea21419180c01180f4207041c10124841180124000401c0c2e00400c18480c403000080d00302c0c1d0b41d01401d03240050b02c40030700d031000380e01921450303101d00c408900300b1603203403180060b000051000c50f224448010a0490f100300550070703240201c2c1c01500800782c40f8002480b8007000f20182c00012802010b5507410402e030b20b00d56440348000e0b001540c855205071340600c01d42240000003a044241400108240c4609941c0100244500c2080d407404002e19540441d050b2900c0500300801c1000d501d45000d403c0b0304d0550900104800c454194030303d0380200d4a00650811403080a014050150103444001e05044c00d8100300e00b900c0c00c0591030f0103044003801c80882c100b44090318090012886407103041d0720b1000111700c411203d03002800d6182c94004400d0941c040091040e1007481e06003000b0a0950300e07004c13900024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 611941753 1250 611940503 611940559
    0xa0e040807051c0203031015080a0b03070504060b09210606010c210e0a060c02060f0a0212031003021e0102030d0e0304090c020303040501050a2003060f120f1e030405 73
    0x181c0b81011090285a80205c061889600d0501105001560304c00c12072001d83c004440d410041040352000c60b41d042d001d50041520307000081c0c2103c20041d5924013090444005501074031002c0000f060750282ca14100c2c07400040444001d114004810a07108101d84410700580711905110054440108002600b00c5c002c40302c03180d01e0038001d10181c501700e01808044400342c400c0c3c81400004d0f00031580301c0c0149441c001c03d50f0098040340c00c0440a4400350341550090103040305502c00c401d8418100614031008500c186101d8402c0440705141d0301c18425280b1610ba08110342404500c00d4040c280d9002090303449407440c090700445d034403400c640054110f20036a0400c1c1c0c0300b81d05041c040c100d00c030b80001c01140030324411402045255200417469046907051b00c0104c100281c40e1001c5110b00301c2c00700145070403003c02081c00d041014071030b000074a0764154607070060701504590303500303400501c06020b1480324106030311070054641201540e1607101d102d03900895204814107180500b000d5440c103144114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 611943003 1250 611941753 611941783
    0x1020114072111090d02040207050d050c0f0705010f051602090a14062715041b03140c04060c03020f030309060115020c0d030f12090c050f0a0e04080705 67
    0x4182000c2800801c9560b0011404044800d1202034261007421031140710000001201600d0900c1d003614108607a05070600303016640190240311040202da8188449100750740c02da07d40b0755403544c00e80c4d01c050038000c002540c10840e40140d8000c0140781d03009a00100d8018051500a40e644602081c10304035044200010350001207406c2046034008044c0d000000405201c151000b256035a44c04001219000305946a034025030303420002035603d540c075170b100d400950716041c200b00c00017860041000c480070a48e0a1290707180460320888070f5a0540315420502c2d400c60440049894101240459031203944a82c504002d080d0801f1401d1520a0007105c0c58810040d003900d0b940d08284214581c0c6000a0055500c60291108240242d80c0009110f054003e0040c0c000e80c1c205540f51800d44451032900a40c1050058078204482c4100d114400d01c09018440c158140c41142001c05205040c80408810390050703d801e01706000e10000cd0711915031055000070051380d02c40281ca001401c007820720040d041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 611944253 1250 611943003 611943041
    0x20d0c060e1b03011401030c0303110f03160308060301090f02061b1b0a17060109110712080a05010f0819031107150e15030a1d0d05070b0f010e07030506010201 70
    0xd02e120407103080781d00b2460480090044016007080303903410310021300c001006200d100d042000041d0281e0313000011641d0620540303001c1d000c000700b82d9046500004841d0414034056002c2070415400100460300f065042c1c0080041c4e00b815034403030b85140740c6200c010388079200108500e0601c0c1d000039080c0a5910410b4141c0e0208600030001920001e01c2c0a8680e21959210301e0100b00240e03040f0030003c00585220082100e80d00e090050b000130101c004403010003180801c059004102c0300482c018100c1d800d640c4003200c614055025404071801a0490404a40c0d42c9030304010340b641c0020342c1d5151400c0c000303194007030f1241e80c41c0a407a06403110052040c140030b008800200181d412040151202d25901c44c80000ca0004080180504200c100204440c00520115100d8001d41c1d100b480601c0d54800d2506519908007800b03864110681c51030000201c0001c2c00c0b0040103c001c1200d500b00c4801800d50049504181c03050710300c80b10052000003016a21400a8039580c401d401005000e03c0c0409210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 611945503 1250 611944253 611944273
    0x12181b0d0f0227150f0907030c09050607080a02060a112b050415201b100204140f0f010234030303020c06130b13050109080c010203060a060f020d0c060e 67
    0x20b50200c1c007104c1c807408803514481d5107001410002e81001070502d00501c1000035640d04c0070160028920b49030b01c2410030030140000304a9488003401001d07443c0c01406034648070b03143e031100240b500300c00800ca80c0030f03e410300381c004d14002c00c604207460114440110f983c400000418003041200995103001706000c0c00d1400b80418451404070354001c00c0440b0205201800b00d021040e003c580c2c04c1e04a80307900301001c0104180d039944910011100001030802c1c1d8800e003100408000680e046a00a00d0100c00b10180501c010320b800e21402403050b0094506010307030922400003075207070100034110887c0c0520f1210300c6480c6600f441c8210a110f0388140c00c20014070f0310f07814001c00a40009000030868460100442d91125640c035030b60003265404400d100e15030b034070b030b1501c101d00801e808001c680d10b64803005140006204072019002808101c030005031280b400d4404c101190645a1041c0300b88001040c07911002c60780481c1e144803000c01801c180740c00c0543c503c1e108000f0f0440b04407000c0203010740c0c0544 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 611946753 1250 611945503 611945569
    0x501050d020d05100312050f0403150e1608010c08041505060613030602040614030609010303031d06010806270c0103051503060f010306050a0c02030405100512181b0d0f02 75
    0x644c050302e020b0600d04404d114026400e072000d00c180c080721070840200f0301c01000024a0704281c0c030346145101d10082442100448428645030794a031111050401d6041e061140e0395092164550350b030402e1500c1d030741a0900740c44004248071440c00c0f95500e039448500240c4142c440b64100c0300c0110651104961069590801100941260041d1700000301540d0000b0414940301c1d044c0da008450041440007141d103995020790040c010320000418001c00b5480401901a0500115009003c100045c0100746000500240d50f9030510611529040700303452088034111000584d85880407003800c0004058844035038404ca081004d6a85950503c00c02003044000c181740020036040301e100b84400c0c0b0036600c038400c02d00305031240112144010b9205100800051400045101003120f007418110b00e0105051510100c040c022142c043e001c08400d241e1400000b010000780028248400110101101c00380014103480e00b1120060310700c14082280c0c000359900d6070034649080c000754448032268413842800c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 611948003 1250 611946753 611946781
    0x609071d130b0a05150906030d120609060f15030507020307030819090302100609060602032226121306180807060c0c0e0f0c0310030b010306020909060a08070501050d020d05 76
    0x2800f01500700c40356100103030815410087c01508000e014211000302408204c8507007820046ca811600e13202c0c0400105141544102e030060441c4491641d4840e0401d04010503501c503800c000c0003094030b44820480150384c00300079948840d9240c0b0700742440307032941001c03095021a04c0708034503400b80ca0403200c14101a000a5030b0081038003225401d0016503070343c0c10031500321400c0c2c1c81030b8005a00704002e514140410100407028244041c6c4c0c6422040d0340303454208070312002ca070140848024007810794004002d402c00480c27181000c1049010700d0f10300d08981004040303000e846180140600f12301d1400c0c0c00b2580001400c0586403503011259666034070700d0028040030300a03505880c050107546c4045020000c0e404a10f220700c442400c85011612610300b41c0c00554002845031514000d1040c0c0800000c80310f50540380214041d44000d03031556070206c100100a5400303081540b103200b01c07034810440f00901040341c0c0d00310340e0242425a15004814459406885100d07403040d00c8501e8507040050f941d00e2041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 611949253 1250 611948003 611948011
    0x2091507060c0906021018140a031416080a1214010609080102121f030b0f01061706100e0f090906040c080f030d2a080402030609071d130b0a05 63
    0x1091001c038491102c240c0d9021058080c100040e00402e107490f0810312190003828261032034544003a4070354042e40707076401e130303840551007040443e00718000d00c1080c164000712015180420b9503201340707005c4c0307504c803c400c05891500c00205002008210818a1400380003625a06a1180001c0c401003201410460b240f003000d01403000402d48001001c01c0d4a02c0510a5400180300b40e0350004054490b00000001400d00c00703151003501c1070350132001c000a1032054043c0d00a00303e10381072228550410002030481080550900054500e940030841240c0d104000e170302c8801441d003000d9030072503040000300b22030220072150035401801000502104102c0012241e1103a8003841001c0c2c015611900040c0d2942c11002184505a00074802c0d641e01500c07a80c003010649000200c4403000e5008440300c0d08145010103009004103140c9030401007507040512820368404072280141440c00d0902c02c3c400c000214400344650310070150400140c6018100950105050f001285003010346003400c00d0f1000390038122 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 611950503 1250 611949253 611949263
    0x180f0714130908070f022b260a0302250f030806010504051008040615050a0b030a0f0e01021305061c0906061d04050d02061005042409020c0105010506131802091507 72
    0xc210b5465401d030040403040b03a4095003020f241c0302ea8a0780f145601d08ca81d40501420050601c034a044c4400c04050007445000c2980e02c01585583d001748030300101c025284201c8900c0741c00d5034054800111001c009850b00c42d410700f0b1102a680350040100c8640c081d9030040d503000209210a80b5100741c000000d203104910070042031101c90400070703030351040b8002c4d48580741d0416109801408100400005540e10241c00b0b8000120364540403403403c2a034041140c51851030750300281c91140201c00701d014174042c26040d10024034010304000300800800e400002080c0d40d83c0d0f20b801c0601004065004140100324404030000070070066064070400341e4050302c5c1182d191040d1100d00b00305c1800410034500c00d6800c109101f003000d1900003448080c2441211884d114032890402c1e07105030000300d09640107450f6040006803075150800d00c0360f086a4040e04450710800e014402100700345415400d80f4241e40b840800124036500d000c0082019002e240070295120740c0c5c000b018421070140380c4c09003842501034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 611951753 1250 611950503 611950519
    0x230d11131814041211061e07081501110a0f05010c08090120181509040e12160f0609081903090515090a0803180f0714130908070f02 58
    0x8041c0030708a500840c0b44080150310440042e001c160034013081c0d0304560850a01c0208121000b01c050308084085409a480303483c40400807010261102c9500d42c00002414240400c0c144a940c907a94401044e4085041000c0510368a07003260f400d0100c9a0801d0388003e6442c000716041c5006806408840081c40004811000141d142d11050081c200043d21055258800c03c10181500d00d050307200c49240031001a00744503036142d54a40c6c458941c0c04640c10041d15032110004070811003a900c61041c010220b80c0415000c5580301c99242c1100c01005211a080d1104002842e00504952000c6405030081c1d01c6c040100d400d001000c0004d0a162080f0f81d81310000c054240016000c850b6821409003840d031200c49500c07803600601080c9a04a0b1210041b1240c1c0c1c40140e45086040d8402c580c120a0303c1a01e103c0705000c0e190400013070603025010320180c5907060810580c005d103401c98842d990b2046a0402c81c43d00e056106601c1000d82e2604060b00580d070300800e080c130041c4403010f080100d010f1050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 611953003 1250 611951753 611951789
    0xc050717011118011d030f01050604290904030309080409090507120305090420160204060603090b0f0411040e0a15020a0e0607082215230d1113 63
    0xe0021642c215060b410040600584440115117041410940c0107554184501040c0320395020040100c00f13448100000c240e130700e40001400184c405164099100c044062000d000c0500c0702c07000204c040c0c03420355800b14141ea481c2022005000048000f901c15503001401156040094002070740e41d900640403102810f0740c54130090100000c0b000301800140c03080c01011305616040c1c00c03242c101041400400b0629581010160141e0300c0024000c0d07181c058030820714114103281c001c0300010078a90500b0041840e40c0e8880d6401080010542014824040700040400c9011100c00709000005070040046008200201c0d03501e000d0301c00c041d40c0080c21440e20100b040f40078021108284480d54a0741459844081808525004548100c414a0051100021040c9005401d003600c1c00510300d4040d1151612013440c000d00d1005c2c119508211401c0c0d4803040300d0094200181032620840540c681e1044001c4105000b02491400c20040110000ba0300300c513028255100d80542e540d0103085182680 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 611954253 1250 611953003 611953031
    0x2070303080c030907030b161d0303030619080610030b150a05040b0303040b070f140307051203040501180c08010b060c1203130f0b1005030a0c14010c05071701 70
    0x15100003030024000c040003802c01101c0c1c1c0059504000e1040c00c482804c1d4480d521121005c000b1249402e00c000c9100b003490319150311000c141c0d0841c0040f2000c191520000c00031035242e1000401e9a400343c11000000010611300c1003804c8014800081503c446080085104508a050b032005440741d500d200c010035110301000003200c02c0e07914000c041124452401e0b0510024140c68600154940014400040c03071122400003030070241e203d003250060021003072514004040031050070010581c4148180400294000b0304004500d204281564503907469250a038094103101c10300010380146442140308014083c0c0501e0103403034416000b032001d80e000c9418001d29008001001c2607607030081c0c4c403400d8490750041c0115003102c03400002800c88400d03610b40800c00101c8031700880d0740c00400d404001c214510070545002420f0700b100600400400c0744c0316000d05504600600304000503160315000681e0155000d541000d40c003106507410b5035600ca22103000c4440d1954480003a5013020f2601062103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 611955503 1250 611954253 611954263
    0x7020a020906010f090e090a080309070303260105091008010c02060411040902010519050f040303020c0102100501030b041b150206090601060905031507051c05062e050d1104030c1502 80
    0x2507590b90301c210780540390106d542c40000002c0d003c950203001d840300f03103004a20b40d40000c620a10041004084041ca036160041600c2c040c0c01358482c009204082c1d040c420500312071024110f50080744c42c2c841507102e200054a2191450344030400e03540c030b00301004505a401017074951040c0e008190458081826400340310559081043c0280003450802c249400059002d0440c0605c401d103140c05c0f820071085540300c2c68680e01640041d00983d00000070103229607410408401d120751100418420755255a40b00c08c030020005d0402080203420701e102c00c8003600d260041000401481c0180000d00c41940c030081c0d1565405e50307490807603000e00f200200c0d11902403490341045a03405002400e0322202024075005c0400040c101c0f000f0010108241745009503184c2a016580b40d0400002810b070401c01c04003c40c0c40c4425030f1404030924100900b005160840402c03141052141c1445996282c0d00c207108002003421403a008242035001c200441401208020801503c84035007500300148a4444203903030310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 611956753 1250 611955503 611955527
    0x5060a050702040f02210a060801021e0c1f063305030a150611150114010e0a031502070c080a0f060902031504051f110a032307020a02090601 62
    0x10034000c11021005041030ba1141094a194450041c10120950380c003840d9080b00c1812000b688842206104208490340700783c0009081200c0210300d0400044204a1107480b642d034070054820010422001a9406105080344258140c541841411070701d00ea00c4000c0c15940140c40d00180d071552a0500c0c041d840e500f0102d602d5035502450401040d18104885950006054030744903a2940e0300305506922072084130000e00704940b503076003920f450800040e2404110400c140408802c00d801006030083c0380000b136007140c2e000c2c44c01c404040d50540c049040f01559034401002e484204a040c900724030181c1c0035200316442100481041d9641d540001c1d914003031200c01601900c4190400000240d0b55800355000610140c00d481c02c804e00b2910740320b840c40e4100c0b01520960800300038200450325019145040002002d010058144229100241030180110f07200c10306517184c0c01100740304e080c00100f01c13000340042000420340c07034124002500c80003540d0040703008418400c04030381d070b41d03004070118422 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 611958003 1250 611956753 611956757
    0xf030e07170703141b041b080c04120c06030b01080709050f010e120706030b010207120618050a0609050105070509090f0c0f04082401081c030612120905060a 69
    0x54074104040249000d001e180740c45140e00c0760920010001306103280c4004005450f101500e44020a60081040d0442040d0014441e6180c0a00328190059070000034030510700c02e241c843c07010f55400d1a5035000e0300c290f4000c895404401d09000301000180042d000a0351415982800a04200e50041d1000300b07090b109580402c131000400c4c82141011080003070380610501d052482440c0000c00310f602a0030301c2074155070743e8001d03003810311405415026911030700f40f0a00c024940d00d450207461400030380310098000c100b503407280c81c3c08800c1400c0b030a680300c00c0c1d0b800c0b00a9500010381850010014022440115615402e000000348158092015601c4014014100d0318884d07560004040c18160002c0072002ca05100b031100c081d0007882d80c00540041e150b18001410b0a001494401c0013050144441c2d16250b9060300040c000780c50046134500001384103010a40700c8280094080d400b0741030640050380c00d03501c2200840e0030300811418911801049403940042581c40740300f40500d6108684c0c00d500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 611959253 1250 611958003 611958013
    0x120e030c340b0f0d020708030708090c010e01052508040b070506090109031710031401060e0121290a0f1505030c060d110703031407110c151b0d0f030e 66
    0xc801c3d80209809001007200500d4811107658412280d001610300d02e001a01410400510400411080d17200d081700342007107112302c800340000070329901c14a00208800420000c80307429080115071420341459120000d203844035201e413401901c64015100a03541d0348500700225101d290180310b4145025019560f583d000340c0301e201100d89104004d4058100e9003958040080401d0320200d5070303290600380000118a542ca403d900425000c0d045c0c0003d802d0b40704212150100601e00b48128500796070282c5540ea28980d0081c0780110940c0882540c081241603404001145e512a40201c0e001440100104486940c20741d030040f02c04038a0240c280c042e408a17100c101140351207400340400e181c000c54045110000e406404503507030085a8100d000c030352101900040c1e81c0349251240e40c41501c03454800204280d05440f10391f20100c10544030301070691035480c800c0741401071003101e002021a00680780401c4564420301d940d0102c5499140c0014102c0080403c0544079000c0c40c640d61542c0f1000701 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 611960503 1250 611959253 611959267
    0x5070f17070f0c08160c0906051e090405070e1609080a320a0c0501020c120a03080a090602070f050c030318040c0516030e0103140403120e030c340b 65
    0xf491079000c4030000d4490306001d000d1102d8039200014044015841014a4050705d40b60190810944103980c12207403140c1c5003103281c0c554604841c2d1210038860310031078042e035464843c1c1c141030382040690340105070310740c0788402080311083e401210403190078640e5460102c03d13a03868034104d80742e209104006104014441350b40c034220802680e86041680c01608900c0401c1d08e90403a40d28111000808403500c2e0f4030081d08110568050140d442c14220a580e003040030600300c50510313180c401085000742800340305808104c51030030340c5d070108651a500038001c542d1852103043c0790a099002070800c6075244031302001da070f01d1418040160786205024008090f586030000c0c0420014002000b10901040414012420b208049811945000f40692201908603144100040c155100111000030344840c02042c000001d601204103d00d050031500e00007054240318090a0035440b9420340f1114903c184105460f0700041c00495610301c000b0104414100c20a4600c440300703034101c9100306404200c00f4404c0c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 611961753 1250 611960503 611960507
    0xd0f0c1208031314030a021b0d0215070609020d111203270d0b0c0d0e0102040e070c1b08010c12090b130501140c1b1612020a0905070f17070f 62
    0x210240d288102521010a9600700313250345142c04c02042c280041e03108803501c5040104d0201e200341005000c0c0c5242041080301d401094080103a00681c00c0404000a061000d015181d07110205255005110311807070115400c049280c0461860182e00c941480e900c0d40030342c80000002c6440e8409031044590120001c0c0e21110791440501598541010b0042c181d4400100240703403a03032150811420701e030748440c010b070300310411a0f03440180b038840b5030300c104024085d071815a10401e5112080c1d01c0c107440129003501d000002d5800e2025144001618150081110141174104c4140d0101035640d907004044c1c180311b140f05a542c01c0c60050300340c2d07407000301003400d890000060300c0006010703600106040e03c00030218010090126030068140d14003107655110941032400b2400f14150710401801402c0302400714107180c40070f03886038001280d440c0e02c0c0c100442d00c95500d142e00410103940d003000180303021800500490032070310b034100010b030300c403501c003501815001004c1e4082d24039580c68805078502d075802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 611963003 1250 611961753 611961781
    0x308071d0f010c12030c02060c12010b09030102071a01050325050f0612070305040b0702150106030e07031410060f0303050301030b4804082a0d0f0c120803 68
    0x3014100b240c411202c0001c644c0003142d52815541c180d80c00184400c4440c0f0003820301c0c0c1c002e80700d03030309807001044030084102c43c4e1155a4151401240030a40e20004080002d0083c85101c030300500c030824011002980c02d07038114110741201e03c20703415600b0640c22603a43c0c10346821031801260041d840041c0070302143c105200c800700000f00280c882450400903150034401140101c130131000194030b400811081280c030410198020360a4001023580d10310750341e4000c100001c14000d00c010190b0301c8192442c0302d14100801e4004681240307060301d02040080c4c4858440600010188a05040180014034020710100c502d08480d050341e9490b0459003150f03911400b440000c0c0040c040d10f0204091510717550a13283ea8040c2d4401c141341555842d0b00030702c80c00b0502c20804101c190614200340010420008040784e030340010752003042c4034003003500d00038402e00c011200301120b40d40082c080c42510003044001d010400d03145000c3c2000c0000103a5504c00061a800d0044005043c0c2170248040703134500c800780c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 611964253 1250 611963003 611963029
    0x6020105131a040c0f1401020114190b0f0a0f0f050d020904030302070c03240c0504061b020312040b030411030303011401030f0e0d0c02040b0f0d0305030408090604120308071d 77
    0x14070130100ea61494800c0c0c80c1c41e0780707801408514408100011156809100c0c1d400880c0382c2c0c140ca0006031820554500008502c07582c081100d40e21900a040559190801d9400648008022070f40710b83d2101c1c8410708031001406401070385200c0c4000804d6610349401020300c0103500901100d002c3c0d403a903a00314080c4d00a6082201d404061072000300000b0107001900c5846443c07400720307040d40c01003048078030291184802d02e4402d1140411051080e02c3e8401d40c0b1201c403e406c0001048038403505c0c400f081c40c0c0703c54090b042188420100340824a00000350003907006a02804043d030389421188100b503220b01c400c0c458107403c200480c41001c01540250414240f0014244000a04000303c03000142014096030f0000001061000802d0451609104141420a0503640c11081d450588003241800c20f81c004058180030000c00054100251802200c1000c4800380c0003680385c90369a000824241c4a204080740031800000018803411b218400d5460b0b01c5d5094601d52040030500c0c800c1c0980c01035452 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 611965503 1250 611964253 611964263
    0x16050315100b1b03040611060f04020f100c06020307030603020310050c1209030c07030809040e06090d031d07121406070e040b041103010b041a030106080402190e0405060106020105131a04 82
    0x80000fa01c0081840544010901034481e03d1064040ea10307414104007000b000b49212030501d10600c405612203003840b0003c1d01d81580c080014007c08002901c0c400c0340007d00030117003800041084a2264550004800c0701d00c2a0101c8860132151102403040c0e0308125120303900d207141071103c00f404207480e0014076000303a410b0040c4da20b02440e8a080c00d0401540390416601c5040000d800c00c075030f080c18407640d00100d050343c000c1c1c01207040c401d813810748951a004428040607141e8011111001d01035100d01d4001c0c6004040b1520541e503000b500b190070f040500140c590070204040c00c0180f00c4003050040c42280a80d60b0500c0850100040100900210485640282e41d58580703000b44601540118042c1c020010800d4480345407144602d40030380e046a05443c1e1100900040007920303002120b807504154115048003c41262054052590b4042d41c8440098410103060005100d008110941070f07030342c2c1d540244110340d13942401c034410148070107000340140700061801051504400741d135034000e4419 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 611966753 1250 611965503 611965537
    0x210708090d080f13180207080702062802070602010b04060509061201060f08010e161208031f150905010e01020a0807050c0405180606040c05070b0601030e16050315100b 74
    0x82082d0f54000c8003400e040030b2425a01800107500c0070741c0454010303011440135440c0401c5965180d805003d2410024090880881d001c0041400d4801c2d0304c401460444a40754415480f0b50025601c1c6001e20501015501e00780b04041c45e82070600900056400c007030001c0784280c9622081c444d220a4a503c0140c01c2d5580c3d44000c2118148811540300600040e8000b00702035009010140c00c2102142d4202da480c004290104540c451070942c1d03003050f42d042045c4948076035848004807040c01381d035169200c2070040a2008a141200589024043c14032940d03011440340d160b100542d888019800340e54056445100c400e00000c4000b002409003620540946034415000004101680c3e001c1c0d0783c2d4200d112144082034840e000400540d54400d04c1200c050201201080c0b000d41035200d0010b001c0c00b1144d117140018956402504075400c079030801d0341194000c0e12218844294000d41e8014030b031080c046ca05080c1c551081030007086000780e0f013464141d10b000e460300c8442203580c2d00100900202ca005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 611968003 1250 611966753 611966767
    0x120109050d0c02030c030106151107080d03140603060c0d090201030213060c0b0901020a0906030207110a0905060f03010614091b03011d1315110d020705210708090d08 73
    0x4103114040101d00140c039046070002e4079204050401030100c02081c02a8035100d0104050882a410340d03425100c9400c0801e10f00001c040040e05210b641e40001061344295a07100c2c09640c1d05038004480c1c060f2109000107070392180020561a198290b95000f2403031b201780011002010305a0144420324814140140b0f400140000d61031000740580c0402c000c1484d2004210034040880a110703801108071001710300d0048406000b801084050041d2005c056022072004104901c400240e44091002400c0b031281642e41e40c001000b8240c1120228000c030300200380719440d410140100d0b010307101610a40442c2c480d1040a008508200810721854500d0003124000300c8100c51008601820348914410384441c1c0307050400710040380161009000c00186170002c404030301c0c10003020b14403d0081c0e02c042061803520307513060b849018254a024400f48005a40000c000000445210601301034020417000078203401010722034064000098080a002c008000c061300c0d000b0008030b4158404ca10640c00e003d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 611969253 1250 611968003 611968013
    0x3020904090602030702062d0711012904020f07060b0616080a0306060e0f0d1103030a090504060801021e030705071e031e090605161a0f010501090308030105120109 72
    0x607401090341c100d940002848030141e414002d5590000d00d80c00100c2e003901c0681c181e141500c19444406021440d40703400300e100d00380b0400791140160822402442030200007012603403a10040e14500341200f1030b00a40b000282414001d440810004515030707400c02c191601d0302d4020b040b8069001794811000c000421644e03c01e20101d0030341500418a0946400c0001005401c840706a0411424000081c81030656039940c003082d0300001c10281d642000d082d48034904000c00c41c400301780055140c00080b0390034010950004001f000c41d20210750a11080b981c0c0c03d0058200d101703001140c140d001e00308610b000b029542200541d001900f51a045181c1409512441a0302050380305440d003c88a0003090414154031000e2400c0100b044092145002d103041005001e5040c0e1b0b1041d4028840c1c00b250340d0b10420070040c00311307100542040e0145419a4141100207030760000f21441148610040004a65075120320409002d0729445101c43e4616400c01e0b0411008030761401ca400c400b1341d00d50a46500290b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 611970503 1250 611969253 611969261
    0x10210203030c0607080604050c16032d03110c07061b0b0408030a150501020d1115070c0c0b091302090316150f030b130513050d1713050a1203020904 65
    0x1c14003034083d01036410842d200804403600504428822410802807111f1803215204840300b0030002e51519014014520b170a0300c0c00341941c1c54241c840040640011100702041031016a00300040d0740c10400007040001c158040c0c0540503041d0020340c40703440306200d00c0c0d02031718501044408500c80e48001a10035038808410b07001c226402c8031040c02c04010720078040b409008156119081c1c2143c40041420a40001d640e0016031001008108100901c1901b5140900c02c44000000d02d0302041c0c0349141900c80034121000c1b150049401c0e40c1031800c00600f100909060310000b42000780001030070354488010700040e41041500c560705010b4050f4200b035400100c02c5100040c0201c10b41545428001c1f41c01504041d80e00035954113241c1042c0c1041250341d1082c801c5100c03500c0000000903a501d421100c3e035060100480010054882c0d428041402030700700d114507104a441e00005091507462400c280030801c00510001c1c0aa400006031200040c0c1405140c01c401d1107a02e0f00504041401e40020103075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 611971753 1250 611970503 611970517
    0x1903032f0102070606080105090a0314070203150402010e01140f0a111609050901060b04120f0203030c010f1a130c050d0603060515010305010f0e070203191707081021020303 76
    0x1a0360000f425010443c85000b8036004201d881c1c000c1004e0300d46401400e03103882d1360b100b0080070031100b500411100c2c1400710035100242e03000f804a4118488510794051081c0082d01c003039003c42c001204400903988914640c4d10b0003000411800c1c20041d0b00305841c025034104120741c0b000c0c84000c4100c810418420006110400306101e4a20070444c035000700351b07040341c0300039021582c00d9043c00780501c0321079403490494040300c08100b0361041c40314450030701031400070700d0f01c0c070080d41808000b506d840300ca1415005809000c040b07007420880200329021a81001102e0360545030410084000d40d45904419442a84030524500303000385071060900185040360a40c0e002106c80940d0740e0107102d11000385800701920030a0a003800c005e194103201b00b0641c0b5581d28815402681c8181c00000e1000f4401d10545071a00c7d4480700da912815861080604005500120483c1004403100000c1401d44140d0f20076004003201d00031007070792030b0900890450584110b0111030413194400421801030714104000c2c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 611973003 1250 611971753 611971847
    0x3200d020d0e0a1215051f0506070c0801020a11010c02030304030f0810170115080c060f07030e04090c210b0a150807060e0319120c06090501050c090f190303 69
    0x41003042c01c0310000f42045901507e202045c4002500c1400b1240c01d40c2e030112506616a1801d25142041e03002c143c00204c40d5500100f4504c50301038000c00882eaa0903251030003071103c1884134808a0741c0340411240039000416400800c0c14103800780c81529000324000a1034500c45032241d1400c401c0c4002c05100300d4141e907603280f0180c5444c5d50300d92028054400032010b440c41804180004646002d48803204480400001d280c1c000c00d400b0300740c40d416040010340103110781d0003a81040308660000e403081c0071031021703032088000301c020407a42044901e83c0c1c814501075a903140c904612006100211901700c07142c1d0800004644035104011080041ca0740e0364444c120b500d1070380c0c145810b280c840301404080c41c3d2a890b882001440c044034202e1206841c1c6048614000c05041403005025a244003a04652801041c003d102e40c0700c02c01000c2e0000d050300c0006008440f9800c0c0510302101c00028030301840215400d0000030700c600d803502040703611405413291117040404d040075404012940303460 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 611974253 1250 611973003 611973023
    0xb1c140703030f170f28050423060f2a12010501020705090f04120c12090303030b0109050f042a030605030c041406010f09090903200d020d0e0a12 64
    0x16816500c900c0070082c000462444c0c80c81410b01100d0a201204054000d4003480581000e60112422541c0d050000c296000c60900241c181418035001d101f0f80f04c405801c204408000c00d004441740040d5150144110303d150401c10382d11081030800200303138101d42c0320b01461014224111038500b2000b03004180d098507010411940341c04006490404168171060140307840c1000c21460070000e41c50360350b000b500306c25040b00380c24080a0440e141420100020700e99504458180841d5034450a00b2065134404e48082010003e005c006648070000361003020b0f071050f95040d8022581c02d040d00501d40b000c11a0110b140c14006000b440c82084031381034107400c0000d070381d02c80801c500d1404200c8203ca80f6020b0302e0400644400c0340314803001c41d500038011414001200c2e25070f1061441f85a281b4000e0010000822000e0200d1400410000510544050f2010180c01181c640080843c007103010500c0c5800502d01c400780202e0944a498050060a90150504100258000d400300e00540302034400c0000703030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 611975503 1250 611974253 611974277
    0x10e040227091006050304060f0b130e010c020c030a0311010b04020c03030702060f0c070f03140d0e070f06080f10180501171b1908070e01030311010b1c14070303 71
    0x40c0c04100604010310144107210410480c1e070840f0449402c1f0b44c00101c00701e802c441e018403c4d000341081c002c02680020b9080840304070380701980d0201d40c0d0301001000900c136150107024102d03520340024034895030580200d400b000009000c0c1080c503066480020012074001070a000003012a000802800100e400000400500ba581442200c3d40010112070107241418004000d51741ba009220f4001d200740342c01c51b84082811f001d082800e05100681e89104d6543c109005848042d02d4040010300b518070032200041030200043c0c1d10003064660581d11450182c4d80d03c005501a48006090405901802c180210701001000090042c442a850000c507555152a64140100807040ea0316001ca030810703840b901d44411000c82100ba03484040f2080754400c0507840e0103480008c4281c0c41001c01d031140d1440015074980030805a41200d02a85941d90155600300c842c0b03090b03a2005c4c4503558480109182814848088240404e003580140c5550720b5a0041a401924062041e0416401b00d41402030751 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 611976753 1250 611975503 611975509
    0x15010b04030218040c030809240c070b0c150c040306090c0f06030207020f01110c0a0e06120a03080123061201140402070213020f07020307170d1706010e040227 70
    0x3444150002d600c0f0b60465181c6501e07500d002c07107100c0c08000c04d12000020100c241d0703039030034810302c0441000d2041d24031106c01041d40c0000a510800c0d220740c2a000b115000507408015406980407504044082c01c075002c0c14002d485050700c001000714068010510010000c40c105200c2c281440b0b100ea400d10346243e0510040116410503607005204040c0100a1840161110400052220780a080140028504103801ca0410300341c0d00c809034207c1161040000c105800000c0d0328000c0d46c0c1600e01400031300c201e88a4540700d03041d000024001c80d4480c001040080141111114a0b080d40e021601d03101030307010005001640000100c140a4401200606c560120740d6440703c2c01481c120f40440c6041142d5001c515a550880e0a400d405580032900d50999101142251001540202078628203a20b481e6500380340d50251800500d540710300d1042c1001a4000e9400c040101e00c101d07852070135a6111001102c88155004840e40c01540074407502c1c920740c0c8145c0740042c0503071480d08448540340055081c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 611978003 1250 611976753 611976769
    0x103030c0c090c0f08100504020c0604020907080601171902040608060406050f01170612010c02060108060601020114010b07020a030c0603021b060c0a0c0807080301030303050603010f090803160215010b040302 91
    0x682c1081c50200c64400843e00a41e0001c103140d4581031102e0b07035030f489003043e042e0003501f1b40c41150060f0002400600e88100451000d00c52442200e845011b510340030003c44000e1821607109004c501c0c0e41e0079100c80c0d040300c03c500d13641c4800c14000c600d4055140ca01400141d03045507104402103806c0c141844060306e400e000d2000540004d8550f485615240b2000038903a21103410341407491540e010205e90607071110600742e150151650000c0c400c04580441c0203681d21001d1081a03d180209404074041d5031041c025080c0110080140030801d0b4207004606500e41e02a660072a8440e0302881b0000c001070740c1c20341550040c41e440d100140c0300d090040503081000302c0042c051100b0f0704000d00300600791041506580003018031340f50400285600d8684166148a148005084c421021000008050b03040e088a0f1203150264020b005921124503408d060341c501d86001051080240002840041c0d009950001d91400340304842e0701c3c141e441d040c0100c903c02a04820900e0354002428000c5d4100f1400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 611979253 1250 611978003 611978009
    0x1e0804051804080a031d01020415090e090a0201050c0312090d090914010e0403020f06040f0c0b13031b170a0501050c0c030301061206032f010203092b08030103030c0c 73
    0x2441680600d803d9407420000c0c81000c40030002e1644c6d581a541071a980c181c90b40b80e1940401d4021550349403204c8020f41c40c0040c5010f60000121109000708100c1d00e640441030086010000822180005030b0054442c2c0e0848410100948402d004000482c80340a4003280039252200c0074104e08121004000c1030203c841e04004180380c104100c80c031810703840080b0581140c6032016800000d4a0320f00e012424854010300c1002a4842d4105210600801d03041c6107202c284a0444110362031307512508410507004c0c50fa5070840e8001c4114042001c6200505650710919890300d42c496140e07196241410004215941580c555000061301c0041020900c1110f42040f5049100c0342004258400d996403407105000d01c104101e9031000301000108a90050005554441002942045c5039103459245d0484002c0360490b124100501194550011049804450028205000030b6803401c018001100404404003060884201c2d40c00201e5943c030042e5000e94400d03900c17221204154200340400b02e501d60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 611980503 1250 611979253 611979289
    0xd1107110102100908030406150f0b040509010609030308061e030a0b06190f1403010609050c1c05010b1b0c0a0b07120206100302130f0608010c03060b07030503060d1e080405 76
    0x41c82c1302091044007900c1c1e0103984280d001c204d84241d0445146010703041d901503e03a401004401003000426030014209844042d20005010383e65900202c3d504000f134400a008580900d02203042c82c20a240000c14049440402e00120841c02010a1500ca03608006a030740d00e01074030a221081c9031015018454070703101d0b1105030400d07091100d00e14268059115084003c1204030842e4080d0b00d0a401100046c40010780800503031400c4d01171880554002040680d40042543d401c07003415505102e481e0584400e0f1140c6410b201840300100100c481c158440f000701d01c989141e10940340d450b40c10401c05012548031345c0d62900214a0310556141280101c03600350b401100400050301940b080810451f0740441d003495484102016540003040b036a000351f44d170b407411300c48013180f509415007050700f054113180d404010035507403042985014000c4c5a4001c001030001c1010640038500b45d111010041d0003001c0b0303c01d0072404038a805021000e64041100c58142c00b20b420802c524241042e0890000a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 611981753 1250 611980503 611980511
    0x51503032b0b030304060809010e150603160b160309050402041d0c070b0f1302030a03111011030403050a020f1b040e01140c31090509031e0d110711010210 68
    0x2e00020340c4074000d03800f507002003219010000700c003800250488510001d0b40000d40b845031644804030442d01c00203c0f442070091144c1c07a441c0103442c50a1203690100ca440003003c5040c6903c90382d1040d6a40650807040d010400980c3c0013044980d01e030310040008084814183c0210b040300c2c00c07059020240107040d030711009400c0c032a01001c2820007069a0b804141034804207095640c0c1000d10911700410a4041d405101d24440c1d4010183c018104103596940700301101c41050744100c914056030103d40c4401d039182000d101050000740a00f0140c11005075500595141041c0b00083d0b0b494102e100713032102042d00080e82520707600d041034400e110422070306800902500340c106200c007081b00740217482f00344107540015455290510b0070092804690040c3d403a0b803409511600e07058980d802d03602401c209580f5100116404850000480c0c60140007180c1c00344088120891051441c2c204c030075240c800c940c072003801990702c400200040c04140e10408021024503101c100092915a2175008060f6540c54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 611983003 1250 611981753 611981771
    0x501021e1002030406110703020c01081003240603150b040c03020702010f0e060405040212040b090105091f020904050a09120801050d151b0c050c1005030406051503032b 74
    0x101242002107014851030140e038980300e40c90250000e010741c0360b41020300303280458004109603001c50511038819003660340c8011603c601f04000300018041c0700007001c40d5040300710000d41c0342130b114880303010300120100041c43d03540e2900c07a0715855161024100405581d503043c0b504900d01440390780d00da0780151408500707090309507001810304514541800300307229601d00c14481541d941000c8402829000d1310a6468000441e8030344c0020324156421030341100b000340003c1d030b20f81c4148607180c803910078035000f0403054041c059010301c0c61080110f00d5100540802180e80b031034a031401403038040c10000000190742121410024016184004011304110707040c40100403d076102000300101682201d400305c5421200c5c0e01c40d500400020124075807003c40c80c43d030004617613000350700342013458042d03000e448849040c2010001c6174180c0d1400c50005c18002d101103804216180d01456001e0740e4103c00d24a01311540d80003c0c070b15045100e803149559410b51007001070303e035000700d840080f00306ea0b5418844024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 611984253 1250 611983003 611983063
    0xe0702120909060d1401090c1202060a05031f0e060112060806060f060403021003020909100b032e0305101a0607141f0c030e0f07053304050102 63
    0xc01c00141c5031244282c20701140301540e07001d10040240740d0121840f108400114401c1d401303080c104406a4070340c20b06c030b0b81c0026005681d1314400c2c003865006029a01c0d004800906032503c0d00040c3c0f801560440301c0c070304d400c0e60105c502d925102400000c1c03028242e615108000512042d00d080b040030341d0a046c03e8041002500000d40350307070030180c02c03107415002a010345c011440502984c0e2010f544200e100c002d1451762505076005058145003500c10050079583d400707141c62040c0d120300c1000c856a00400000d284100042c100603c5160070015424044034400b940700b01c400c44039041501c841d0080b180e081c1001c00d01e0311600304608290028043d16164a90002d41c50b80120788000d01005540c2c14442d40c0303088180705120402c00c26001900e1070140c8014908000c00000d810180800d1601e17050b180c468a00068251058400d20b00074640b4a040c1414441150740c41911150000110442c6410010280b0300c8400c4012119041030703203c502e8003000a03c0d081500d541078588552000e16540c21342 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 611985503 1250 611984253 611984257
    0xb04031403120c091207090501060e0316120c151e020d05070602070c050312131d1302010201020c0d0305090c09060a060e0f1e190807031e0b100e070212 67
    0x1034503010f0184c070340b0001d0010888110028240c00b103036003e001000300d405a141c0d03200506981d059505c030740007201000c05165480106a8081305008040c03c010088040700040994899102e664004012544c44013004003c819603800d40c0c000c42d200220222902600318101c070102c441c03610040002da0102c5401620520805502900075600000c10030140107048408800910000d0100d5020580b0345582c2812034101001a2100304206640010f028814021410340030228049000361921b4460000d20004169401281555000d01005220940901800b580008151004140c07803074031f10500c900b003640d03010000e48588420700500005403144840c0c0000e032025801c11088044240c000206041540303503c80d0b0344244c0d00c1095071000c08000819180038041500c14255450512483c8500c1010718016046681c0c00000304101040c07841c0c2d590424a1341c460361000d4142021349403001141802c4030321415070400f14504110300e0200030b0985034441e010303102400da20400550b40d103400d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 611986753 1250 611985503 611985511
    0x30519120c0f2c06160c030c0f080606101d06160209130305030f04050f031c0c020a08090607060902120313090c08011401120c030b033007030512010b0403140312 71
    0x813107001c20002c0b80d400e80d40120000154201246003461a0780b442d041054a246004c1c5040501e0f040300001043d040014405018960003050800350409000e070407503510740020f0300200284042c0c51917a121340c0300d5000030800845952002c942e00301050051041405000c0c101d40340c00d540507003a40000c40d501600362904110301a80c0c032042d503103443c1005407401200d052041d050740800542d00008041c102d40e800c51400054505010103180e80c01c080c1d0300c03440030140c0035028600c00c002c04810f616003036000740040c0740b1031031000908003115004101c01f01e14001c801e500b103500010390b0403040941039080e40000c04030300300c05110703144040340000c080751410711801c0c2a01c4180d15403810320f680284403500c421810020b00300110240b040c0010085c2c40e8000e2054024014030912107002080c600e005210b851001c5502e50740ea0b8000c2c5d0450740c965201304415020411f0500c0754081c45000c00042c0350090280e107400a480b541103051055100c59a5416148254010010070181002d200d49840d44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 611988003 1250 611986753 611986759
    0xd0b040803180f01021903090b04020603100e040501090501060f060c15140708240927030a0c11040203060904030f0e13060e0112030519120c0f2c 64
    0x80e9151148080740c01c1482c03041004040c0a5032640502502c4150b010f80b4101c0e01092118640205441d4280c6c01ca0f5025031019114400c000009009820704500441d000b40409000c1c0b40d005a45000c09002e4032015201114a079440c2c032407501c2805024020f24018102102520303e00710b2030110080c026034940c42c0c00402402050641d03a880c1100ca80c004400c07500340458421085c0380c90080100258000c6485061a1005050300c40351407403038450070011940301a0008a90352200c0d4400c042c900410b0b12079400640c0e660700107410800b0180090440e01c2c18a86508401941c1807500381c0c2d44030746200100c0d00440c814070400c40166640309c0304075041074040c10060320040001038103c48030041114240c0d0060000c210814103403a0560104044401c0b4125420560f42c94040801c000e2010031000760004006000080b194221902007184009a030704241d10368403190580003054810344c244207000314140600d0110b615801c000c512050031000d07100000c00c00745103603815040c2d40c601008240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 611989253 1250 611988003 611988007
    0xc0d02010b1e03030d021c0f06080d0804050a120f030501081902040b030c0a151403060a06140c0105040b180c100c0f0204050108030a020f03120f091c0f030b0d0b0408 73
    0x40d510280110356034145d9a140c150b42d120446000d20402c103144204443c00189010302070180984548601000e9504840c06040c03244182c42c07044036107000141054506003ccc050058001418001c2910b034400e03125164040030640070680034080b82d8050b4003003803540d00728140741001d907111081c1000f106503040760000740c640303c0003010a00c1c20182040c00e5401c041072a0011428402c1c142c00d03600064041c1d42e60f010070206000382e2401d180026584150000380c0c104042c0401409074181071490380e144c2181605201d1814402805d59409450580e40c000c1044148210012030201402c5040700580060403060301200109140c45600c030080344c100440d00c00d006007000354001c4030180164004101b482656100c903042c2c0e869a006210980141c070806850803003511021054580424050201450564070b82920101519004180300d4460042440a0341e143c0364200038260421000d82c2d91509240510001604840d002031841d80308104c001c01c0e00000a20f444903141e4070941c000d660b59 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 611990503 1250 611989253 611989309
    0x1f05121c02010b10050d0b10020f0d14090f2704121e050c0a02041104090b090c030601080411190501080106031515030615270e06091009110c0d02010b 66
    0x4020047e046d400c40c1e100f9402e041e060006980080c034115208212803c3d6038104100c4482510358128048062102207421f214ae000b1a1401700d20343c1c0b140800c05080407180a5489058642e1b44e288441210a8920324406010034400345440201c40c0600d0350521000010080101c02800101c581e5018100840081c1c440d0844005000649003254003500a001e404241101d0014039009800380c101b10610741482c40d8010315145440c2809030801e68a0149540c480304011280d02d01c0084c002d03596000f11440c49103039a1101c1c4840f907502000136201807202410140010041c1c803041c1c0c4504205401c0407100b40915151003011022156040c08044410a2848003078005e40f9865200000387c0164000c01440c0940040c00484545185406010f0340d80c1c1d013803d0b4521340100740c010390300f0421102002906078181444c002d0303003003041010400c404541c3c0700c000000340e90000250b0101d000c2c001c00c0f281c0f414542041482041140c6000074810b8480c03031008504800c02c0b035103007141c91401d038500321 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 611991753 1250 611990503 611990527
    0x904150f030516060e0f031e0a05060c040605190516050c0906040c0203160c0b030f0702060109060b07290c090f0901030b0714070b0109050105031509061f05121c02010b1005 76
    0x81081e4000250b010341503030303a810200d427a0503030f040003558240150030009901403500c4045805481d440c0c0c55850034010950300215100710181851801c2c1304003040441c184181200d60710114501ca01c00400426803844c06000380200e0203480729009a05103c004070300e00750080191040310007001740d048100e680600340904882c0d503980c00034854400000078000c5900f5a100042d00c40d020f940c003168440e9076200f06000c102c4400340b080070b1128a0030312003000000c920f541020040380040b2401d00c0361001101c03545d00341e0301302510038200c00200010a800603007004562216050400c90780c81e0615803450b200d000403204002d000307004201d440c46440421000d50030544491a4104058240660310340041900504083c042c0304c0c480c1c0300d01950990302d00d50f000300c06441000258007501d81a182c41d403500850b01c0e030148080300f0343d844103200850640c0f100c51130a65004041c600507c074205a4104003184500513a040700110390401102040c251600606404001c245140090f0b64010040d49 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 611993003 1250 611991753 611991763
    0x412020a12050c210a1515060e270a0203040f050303010905011a030403090b090307030b040812101d04030306090534140904150f030516060e0f03 64
    0x24084005101ca042404400941c1035050308095500a5040d01c003454003411aa03240f4481c080d00364401d802071000203083c0c040052050031205804910311800500441a010030344d00503500103a405203545450345819800c0e05441b90800e0f105c0103540e400700d8078169031300e4001003001e0f449540010100e03080140c1c03400ca00c049503800c002501d443e0751711180400d000c0e000c2880b1340101810b03025103402030120320504507401240d241e240c110440b460200c602c1c030503800a007256903060040c00d60001c08504281c2d80a031286108080c0d4a581d680ca1400c5e01420960241c02d96404071000e00050003010079228481e00c418807040300314000c9640d40e14084020b8031031a0050701800d410720091102061260a01074000e84e1021400d640343c0040029442c00d00422002410010b01214441e841a0050724020000c0c2000032f0404500c1048280700d04083c1c21450707000c2030030350f40100c40410074444140318003000e07010340b8954000754601d02003000b00703039101a124880c440c0001d281c01c5e8205507000c004c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 611994253 1250 611993003 611993009
    0xf110a0c080310030b0108030310141c171b0106060201021606051009020708030a110306010f21140403120203070c02220f0b0a08010605101808010612031d01050412020a 74
    0x40c45c40c0c0ea940e141c44c010b540b40d0300181c440102c00400700c2d0011030403881c100f0f44a0000280030307101d01c481c11413a201c4007011491801d002d40e41c1304200f00390000d48200360030080003070240c950020402e40c0a8105480c0c21103646070301040469106101880d03002c01c0c2403120748505900010041510340b141c1d04880240d40699000d25540c1d88001074820404c00e854015512501c1592001c000303582c840510740389284000c42c0c0c101c0c0050039049503404064054403440c1d01027544014129a241c03440c20051085404400c40081c0b007032083d5040004040c3d11801d10391034001c1c441d03000c2d4154200b0b0b00c0c024ac0070344203c4600130f00c0f82c1100360a10070200800103803c1d52810b4041c2c01800040d0a00c01a80c000b08424000d10380524907500022510107014060a0100c91024001c0c0200b10381c401002c803800c1c2035a402d002d80c0d100b100d900015813150309004402c050b103910384024485080c41e1501400c803050840c4003000381990851035081e140c0e006001c1e80d08507048440e0b003134212240751001070340001060f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 611995503 1250 611994253 611994263
    0x16020c040f050103150504080d020d020906070308090706090f0b090303070218150f03060703050c1603020d0f020d0f050901120f1506020a150b040b030a060f110a0c08031003 76
    0x200c10892120a070000c1e41200d000711220802045e5006001c2c2c1503030421140580760100410000084034103950007401e901420302401410920450001342d07081e40441e1060300004c2e081014080a24001e00c00100101128200440c0e10391818508103e502200e10903485441004200386c4041e480070710803a81318640c000c2092121020248042e1040b00082d201c8800c03600614001c80d10750f0805150900b0640c074018010401503481c680200d01600000f4a40100d00b241800f11210121844c01e00d00a45482600a00700b0b181d01140002d050850807080042194803010b00d60300259000360520080c2d40962814650316403c41c00141c513152485517003038040d5403170006c2036440502c40d42e1044200001d51360b0000202070341e4100880e9155412080a032203090241c03030203c0741e401240e100c404a032001910201d82070b100e00001904118130307580141c40d070035102d95075000c450005220b074030851031303080c0c0342503040c00d15a0400500014014200501450000000c5080081101c4050009607400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 611996753 1250 611995503 611995511
    0x306070f140904140a0506041806051302030d0201050a0c05030f0601500906040608060a030209070201090c05011d040207080412031e020106050d0f02040e010c02010204030c0807060816020c04 84
    0x405410b0054220403100000d50f903141602041c03072860107016030040380103000609d9054542c0d0740c8500c4001c18010b00110a4490420795030b0005803000e2000e04003000c2150000541d601e010103080094901e41040c0704100503080040007080741c6034051a0360000030a1034900c10108003014040810b4095034810040c82d001400c090010030346d040c2c010800c04600001040c1002300010070048103000e01039500ea4802d00c24002400010300c1580381951100000b850002034a640c2d401141200c00c050b240c101c0141d44940c0814140144925071b400203140c01c4c40d01d8030350b50018507068041001c01c01c0d42d0300d20039500050140244007480084c1c0b40a407030743e00000c503903c0e440c510b8040d240b540d5000711800160340a9070fa180b07020740103104003000c40b480035004803c00b00141c0e441b000c411106038002c0740e219070740e01c10900c410b1200b445a245000225000142d80310304605010f007161100e540b2201e500d600c00f0409010310307075208011941284611400101030580c0c010280e0410784200c4400d0341040c50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 611998003 1250 611996753 611996771
    0x307081512160b03070509120705041b172203031d06040201110304122a06091d0105210f0d08070e1215091005090106090b0306070f140904 61
    0x3140d0440340b041c881c05146002565405101e075580000c6503003a010a10510199529040444400300c1040c40e08040d40c4505441d500040c0c100d800a070784610111400080c45900c26400540b45440f510602c3c6c2c01c81031130320344940c01c0180f28080146054122070f2404503002098004e0300100080110700e002803154001200901c0e686184c00c43c2d050f0700140c510b060012584101100b01c40a0300c1c10600304031802480d03522a01c10030303c480c1034403c0c0107941001d108548038038022011f90107001d095550f105004d14040b5039814000043d41600c00b03124180b801009207a03244005418480540340c07503007410314516a645e60916003508480300980c016000c202011541c03244401d4030822080d11030b481100b81c11024058040c2251401040c01d5020300700303400c0006503403441c8507400041401120545200681c1d403000b40c0f03a00f610b910f00d180c1c0d1914818080700100d801102000c0307400703a0003045580740c0380c4001440c0f0007140109a0501c0003103504030501c0c1c00c9410840e41c0d10b40c4054014418903003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 611999253 1250 611998003 611998039
    0xc0f1b1a071b0e0c0f0c100903020c040605060702190302120604030201050a09050a0b10080a0804090e030702180a02090409050609011b0c0b090109050f0304150c0803070815 76
    0x4040039046030201c2c0302e1081074200424142c40102a03401e05001006280d4851803007408540c07203841c100702a001d003400319207a6154200010010401d040c40c0106002d070740ca103000303460800d002002038443c500307100d0300780300645868050380c10107501182c06180015100701d0030845001d072600065007009607034803090040480000c229000300d200c0e40c001c0140b0f81c1c529a15508a0300403000040c100c0e000019207402242c11813020b40d41000b80764945020060f13442f0801454030035481400c880200c8042000c11486c00c042c461040d800350844c0c040d5160040701d50000768210904120b0084044d65100440d440d01815030607a01c80d814041c1080202003554101140da40c002145c82c000c1540c05e18810207000c070080511400300000507244c45180301da03265505200c203400102440410345d0b0b1341c0c9100000c5042000440280342400005d140d81e54104200b1000d207039500e6902500f4458892010400200404100c17503201c0f00900c0e00d034035035888411034040a04025500b542d80081020703c0010061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 612000503 1250 611999253 611999257
    0x3181504080a210f0c0201030e071205070b0a051b0a0221060a060e071d060f04150203040b0a0302030a1d010c03181101030c110a0804150c0f1b1a 64
    0x15004030a011070040c000042088070340c43c50031224001890b00360781c1c07841003170103880b0702d40754503205060214800c1c241340300c1c00c0d14010486d13010a803150440302c1c2200a00000380545000790500300101c0d851b01c258024050003e1180040c0c00701c042c842c0082144030844203100c19001c46a00070114011138440c1c004406032184000000c0b11325000c1c1001284860406201d0f0400301c0307000c1c0042d8401651000000c6c2c6492696841101e403202c41900046900d6031104020410340055100301910781c3d00b060041d00350807221420003c01d42d41f080100b4803d0948040c25540d070840140ba000d07a407036941da0300e0f01c00904101c01c1480340c1c2050b08a070001040c00c040d005040c8080140d0703000c0207500c03084141142d00d80e0142c3c00107480200004030308502075120703810989895050b400d220f4160400034001c01e103400981b06090300ca03094041024011324a000322092410101c45c030384045002c0054681510100c7d0242000b481d08400c01054110469030b080d2801c01007803003801c0c6a9100503040c3c519859a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 612001753 1250 612000503 612000523
    0x20a03020729040206090a17060a050609090a080a0918140907030b0c030907030b0f040c0605040602063405040f1d0c07050c041b0215090318150408 65
    0x6403100d6140021805403481402c012480851003041c081c3c4440d000c2c030000e680a644225004008800c1c0810107840f04070350b6810b44008280100b80342c1c50a01d07401800c075400a400207200c0d1801000780040070750006907a96106800c0708a09942c0c09000c5020b44840d00203031b11a00714003980807010300d500341117640300c101c112005910200c0340740e6900045a4a440103400003c00b41c031410300c0400e01000a100c05541d10000c00c0c021a8642500c075203400802020407951402d122907201c0070002041080d50a100c020590707810401c6c02c0500b801c1d4082c1d1591001440c00006031400c11400c520205460445400c41040703c828001480303c0082c0188160b02500810340c4070b40c0e0400d000912410340003445010074a05a11903002c0ea112803510031015070041c801680c4910a40031a4401c42d03507184101214541c90952842418030852406030520000b1490003101e010b01501708080c899002c022111009003240344c49490303950540010b481d140905400a404940204010980450000302d2101c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 612003003 1250 612001753 612001763
    0x1809011502060106020606061c0204050411034f02060d06080f0a0c180f14071b05030405040c0908070306060816081504020d02040f02041503021201150c06020a030207 73
    0x45607884d40c405030780e522415946560040020002d1a44a0603e0501d0050a240c2d1300f00140ca026030301c10000d002d0b1172032a400c1003a90600007080c4a0301c6e40c1d008400440755903200b075011b600d03100f03844d9924100042c0a07000d10a040300d01664054004c0c203501e1960043c1354010b01ca06e07124002c0d005140e00400941c0101d007014418104040c07034090002404011050f07010322403d040600301390184803002400c9603030043e220b403902540040410540100e181010300c003100411680380502e001800d074443d00d80d4940c4214150a0954085240801100c06681c020341d0080b4000708460300c00c0343c03510410362005455014640d400310422846401c1070045541c1c0b04116020721408107407113040783c00507105034030817076004003480700200c42000f8080703034018002440301c3e03e8100107030085070544d40400c8940c01c180754002410710200d4540407080d06086024030b821803c3c0411056071144403c010300546401ca80c124252050b068030071003560b8071203036000c18155110f090b00900a0301035009002c003110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 612004253 1250 612003003 612003013
    0x503090a0b1c060315021c05091507051305040c0c05120403031103040e150d05030705010f061719021207090b01090501111911060a02060402180903040b1809011502 72
    0xb4403401801000213403070b000300e4040c280c1c40318408418002c0d4000e1103a6154224802200324200c0c8291252a101d1281d0501400f452070707140740000c0328994018610801d1280501402c01490074807841001030302c2c416140000e964080704070a41700610582c000070140e00c80c003000b20114064a0002e88126482a250310406401906e4869164002e9004040028140800007211241d6280d40d109402002900d0100c04203a0341c1c4500d41507901840080d207081e910f4074110425000c0d5442241c004044508414a24004540106032078840150302803460b04030900000301950740b040e008007400420b910440701d00541d101002806418010245c9003c80d101c0b02000070b03d54007400124281a4446015021112842c08003800e982c05005042d106825281080c01007903e810008201c02d01640d0010302c4c942c6843c0c41008100c03d0300282580c0c002c1101c4003484802070b400005d59081d6600410303080d1b1240c4189140c500b500c5014401c141e4804040400001d08042449406c08008410350a4507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 612005503 1250 612004253 612004297
    0x30d060f030b1b071506180c020709060f0e1f030c2d032004110c0f0c0d021012060902070629060a090305070b03090f060f0a05040503090a0b 62
    0x6440e1407070b4034034901c1c0d0f8180204010400104212120181819003c070700080f103503103030310204007100181c81c1141000c2c0c0e59540c103042d1242d01040014003e0580c0c510901046062262140003804a4800c116800407442c000c25903c1140f15100ba4400504040100c0e00d0b590f81d080c4410b01044501c100340003000e10116030030380c0c8001c5c180240808880e944905052902e140c1c0d0703440b20a180c013058480181040d99182540d540d40c0c2c0a445500c1d039450301d200e6180c0b072034242184c2c20700301d8841c107650103644031005034a515101c0c0e60320009910740440e1510807c2403020f1042d104000d0001c1c55100003480e040001c140e03e503959000e80041400354a041000034078407003144c0c40060006800c0d07000550383d00842c001c0b80c9411001408042e030313140380442c000c1c1d40d41d6030750710300c1c0010316000141000400b008001d00c0c14420841803401c85040c41c0105940d0030034090381c034429440a0700d25500c068a0310000381c00d1140410840721100c50282842c0c460b00d0b519156030720950044e00300d050035510030039481c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 612006753 1250 612005503 612005521
    0xe040f0b1c110d06090c1d010b2d2212030809070f06090e0619050609041104030b1f180b0d080c01090303150b0d02030402010908060405070602060f07020307030e03030d060f030b 78
    0x340b0190a011544183c10303404c0103c0e55049030801c81000a12000d20041c2902c041000701c81e0130f21807925840c0e815103c41d8807908445140bc6c0303004411114038000d400c1002a800381c0b04141c0a40c6400d41001001034450480181c1003c9440d0031850292100410000303029601c0030080c0219152580944c48685584041013441c50461102c10a4400011410300c01340c604003005190300c800040c40060174080c0c920860170590411b81c02a158803001408001f0b0a200c58242c100400040d0720843e00400d09201c165940c43d035011071150146551a0f584440e2500c960800c841000d403c00c507000e441e0b901058176103000e01314400d070440010342030030713982c0c0700f11513190381c0400680b0f40c02149113090011501000009400c0100142d040084010740011140c00901070140104c2c000c2014000190402c0d202038504100900078500c0d6421200030844070690200660781c1d0140c0c1858500b02c1c1401e41c0300000d180d8003e204441190380e107004c2e0700180c00d03e032645050084078442d10100b105581e40100c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 612008003 1250 612006753 612006779
    0x10c0f0b070909110912010f111207021c0309052b031b052506020301060f030c02061509070207150914090c03010605070501060806070e040f0b1c110d06090c 69
    0x403098542800340031001080c608100031000f06c501c0003000140c6820048515010348841001600b00344400144c03081882c450304d80345581c005014002805070600710280c100c40c1c071006d01030120400da46e410714036080000c248941c0d00740015140101d49000e4014120b03445565800003004046441c18180302c0a288600a5440e2074401d50780315a803c1003c20081c0340ea20304520001e0280005040041c2800a2a188055800703040300e90781d4014405098207002e42164269080039056510410800c182c3c01c00042802e100c00c9015030740d0a40e5034590070404d070705e050011f03003000d90750702c1a0701302d40c200756640402c0403012520407a0741c1350b10245c10039040c0110b0340001c2e603500020320400c00041c0038980c0254002d261061050000241c140d43c8c81a6440c2414015100c18000604030940c031103440c6007902500314004050309040044451601c0092248d6240c9002004502d0709132541900b84685000f0002c01c2050103130000940c61900d140600040520703040884050006c480041003e4805080f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 612009253 1250 612008003 612008021
    0x6010501020d031a0a03060e0709181716110307240f11030f0921150a0e1c02010509070807031112031c0501060c02030606040506010c0f0b070909 64
    0x30b001804429102100a8521011300020340e8422100b032109075200d4461942c003c50050000280003207a502c1c20500b0b100465014210300c83c20103150020116121420070350a65010091a0403120a043c40c1822801080c00a140500010002c4001e000444129200310702048041d60602525454554008800c0c0c0e2400d86402455442d8001094080c0300c03091045100c50500e10f24031501380c01d00606d99032061140b449801d202090a6500e414640f910b541e100d80c120710f0510340307040000130f900d03665403417070560030080c1c04440007044003071103e98400c3c9841d29a180c140d0b09040040d02d0103144644d100419180190700c1d00000514a80011840c1c60550b2211006040301e01d2035901e0310010000010440d50707008405251420410804000034410410322059405007182d0440b50413080710790503448101444103d108075401a82c010279220752201c8112030000d03540d2113007001210103180d070443c01000f4503201145038090020781000d40323100e81c2144d40c4143c0c41d5500c2d205e950068070180d0b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 612010503 1250 612009253 612009257
    0x705090105101d0d150c080a0908070b060f1023030103120c210c0302010e030c4b0105160504030323130504051311060c0a02041409010e06010501 64
    0x20b501e803412459802d05401d040e64000c1540340419043c2c0ca17100004e041040d03245070b000356540a002141381e0031800c2c00742c0c01181d44504108099154031a4030140c030803040300400c15140c100c0000d125070740e820300d03451051001800e07104982044c0c8102600000c94030040f1b0b05009000e10400324464000b034210781c1644d90120341a0810103100c1400d452a145080e4112000e401041c1c030074040340f03d448102d01d40001c1c1595050000100e5003006400c449095503400c2081d0000c1184d000400303000a81480d000e81103070018500858444a180641c22028070200030303089500954034a480f12042e0003c10340b03610704000300807171303120100400d00440d00c4005000c0811002d0104001003070051a03c0206106181203c0302164180c1c01443ca4650020107400c01202d0211000e0081c0d00f030510809521001e011151000c0c1007503619012059005001d10520540d4005002d4001d514203000380ca44041e40900240a80b00d908504002606011250b100c101d45c6030181d406804c03000043c103181240c07010303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 612011753 1250 612010503 612010517
    0x40509030429070606170a1e03030e010203011d0901020306010c03030c03020c06040b180f0a110613060801150804151a060d050103060506031c050901140c070509010510 74
    0x410040300d0b14407018070b08420081d640441c001e00542e10b000300000d6105850008490341012032088124000e41d21003103185e403054410304002080c40c0174142541181c1c0c1c040c0114011103140460282140c95103481d01c550011000154007075013500d240a00c0240d004142010788c0d618100303c1c0c200d00007200c01600264900c2005c1700464001d500c100c0408810f40b40c0949001c0329101928980103090750100d81c094a80003c02c080380c00c030220340c0154201d082d009451054400d8685c207a94111804015005c1c0d0900f02800307c0b60350301c5a041300c24007001d0714120b903000c0c5d540c0c3d080a070200b14241b15600521441c0f418540950740300d07801e054403070b592117400745031502100e450100c010001c03650f100690034824240700100fa41c0d03160203030284001c0380201007100e40c114901b8009890000c0c040c64029444541002060f655012038003003500210300c0c00c0ca849159200040303440401c82c01c1c44065084000500644d004c6010511005848080d5900102640c0c0e480610482e514400c3c042000601c030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 612013003 1250 612011753 612011759
    0x15080c07120309030c14060708160207050621011e05010507050d030f06231e0604060507060f02042d060504090203191b1407170d0f1a0108060405090304 67
    0xa9018140f094003900d05483c5560003a5980018100e09002c000c0081d800502008861030344038034403640c40200050500d00ca100c0064001c1e40d101d9450203005d11a1902043c402d0700381881d004150010005a1605206941c0d07075524101d0071800410a0113111203140000704040d4040d508507050198004000d254209410000314002e040e00c645000e4655207400f80081e03052440351468001603024418045008495410040341d403254900d6070502c10000c1010030700a603240c0065804441e040d0800316914031b81031500380000d101c044013016203680b0200d808503c4043c0d240802031501c1808030b42c030b604100b88452156110b6198031036540014001c00003400380c03513082c2d0003568020300a5540e03400311802840d40c4906588245d5168048050008032100100f544840090ba03441502ea408904c0c00c070291300c40b0200c10500c980481103a907400529070301305c0040c1e81d000190034912500100980b503041d10305203e02142e030135216400501008082280307441c3c540309041c080c0ba2004011850f1600e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 612014253 1250 612013003 612013007
    0xb090918010203010617010f080604081b0d0e01120b06031807080d2106030816020315090f010b030615040e190c09050f190518010615080c0712 63
    0x400408000410100354000c502003103090000c0c601030440754a030b00020184045d00c1c0300010005a202e40b075041c140700410050001c0104219802c00c0e000b054040d174030b1940d80302c00c4080440c100c409035000d120302201010219840390030180d0300310090340c80c4502802110680400ea642203250550302103010070100b0405600584400d081113804000d03284040e03519440f01d0f04114880d5400004030303101c4003141455026207290b01a8142c800c000810420742161a00000c9000d1030000ca07a00000302c500f0201903582c104119140707421002e211000d640351202d8401e03151000c0005040c400d40c00e09922084900c1c02080761403103101c6111540184662040400001c0c180440b02400c283c0690018502c0f0450400180b01c6528082e49420044038a88003042c4100d80f401050389000305405018400030840400101c90408503654000c2100d4a9010845224a20846602c03501d5880c1080c002040701d01d5001840e560182e545600001c0c0e41e803200100418819900d000b0700d414646640b4801d81c034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 612015503 1250 612014253 612014269
    0x71b0e0c12180111030c0a030e030a08010902030406060312020c0f0d02090606030c0f04120308011d1306110d050109050c0a0203220f06050d0501050103060506040603050c0d090f0b070302040b09 85
    0x2400100000c80d85410b00c0d404141198001e5035044106c2d24001018000c460b0136001d14030004d45c0c800011842c007110322100904990042c040d1400e00ea400101003414010a0781084000d5a00983c10421650060307c000c3c0d92220104103441c010743c0c081002c05550700c0c080640850551300a0400c1c80030755112010003c3c55400203040062018080c00343d4240010004041c0010b4404036510f000500700d18100a071201c18144d100c2210a1028800c113052413503520030564001040382c00001e0f54071010300d03011014018221081c14076410105040c048050326401680c12114a0b600820194031500307504c0e911382c03041027551005a4800c0040003591741030901c503218640521911072008a4480e111101ca82615a002000103400410140d20900c607502c070b4207005107002d003400c0100d83d1402020510758000c1c0c2c0700703903000d160760380c0d0006030364a90074021910400c0300d1100400c1030305154600681141a8800305507844030302e020015205500038402c0740e040d20700086480b824840800204138040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 612016753 1250 612015503 612015541
    0x210109020901140301060e0d2109181b030c0c0501050703271a0406090f06060e10050312090607061113080a0b0105100507020301060902181c080708071b0e0c12 70
    0x103900340c27801280060b180408440c22103034096490100a500d41241a80441c0241d507014100038900b1402c024004102c4561068403206410046110746810805450788580c04038090700039400c00c4200845540d0660001c0d4140c5e51422040038951100c41102081d40b0b2780389070040c01000c407003001d074228620001ea4564028401da90210f400352031551001c0c444035404104442d000c1d250102800740300b0000c0b9003180d0100001c901a0142c52034440001d41c4e4036011081c07515042400207601450303450b00c002301c80070f040c0c100c101800002c442c01041203c95100005008c0e400f40558808141030b103020400c0d05800381c010002110301d90802e0200318900b544500b066040c0281001080016102030082c030004042d01400141c4460090840208003e84c080307089211380862901e09800101f502c101031511900a5500750302c80c011490809010301c10310b030001d4920684102004a40d01400d0010009d81d800200305000c0c548603091043c84a0040b08080131324101c0e50000200c924508602d96a07076 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 612018003 1250 612016753 612016763
    0xe060f010e0d0f031d09060a17011113030512131e03050604050a030f14030a050a020405130204050a06080126010209040c08040b010605120705210109020901140301060e0d 75
    0x8074074041c1d0f106200100c240070704030701041c88001d050300c0f00c0c5030256101501316401c1c0c2d03801e03e1a1506a0014414200714083d0101c401050502618880c1d800d5002040084001c11400d80c0c1d030b1102c030240c1c0e50b140742620085845210b045520f40351904820150f41003498030381c0880b400d030b9042680e8074a003040c00c000f004000790031941000000c03503801c0001a0040e8000c50107800d500c1400e050040511b120070a4400501a080100c0001e40018004032540800c0c203203000501521002d02d000d01034412540115409607484d121108a10010fa0042089800c00c40386901c15540d550b5080d2100b2009101e41400441c10004410308814040580801d81c2c00e40000180317000e0200c40090100e840c0d0128030000101114200400c1060b007040d22405001c141c00c26905018246104800761a0002d005404100000c9040302e441c00d21003131403281c449910320304034040d582c56201d460000c2d04070039140c0c1d000074200c04140c4440084c901c200d0381039892a81c3c890401044030018001441c00445044131 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 612019253 1250 612018003 612018019
    0xf0206180a15050f090f0d180803030c0c0c01030b1c030e0a170f0102181207090203010b25080f0a09030804030f1202011404020f01170702030409060e060f010e 70
    0x400074840c40854000380c6900c0d0b00024036130421104e04950018018010500c0750710195401e00140800201d80d407108005107401307102c950690650000c00358240d4001304042c400030041c05540700040300507060400c015011130703186540c104011000da4403811261070300444501c0d8401c80320401c0c280000d0740e090190410140c0c0e03020100110390140c4107584805000030402141140c8100203200c04070100e0a0a0002d600303189540700b18090100c0301c0c5807600d01c0360285407068003510805100760001041071081c2152290781d038450890301d95000d2030f500000f000710706030050011010141a104800c1d0041c0e0329030b04280c0c010160314081d078000c2c50403a00b404070001c0e00000080758900284042c500c10103001c0908511840c1288030303e0300d48000101964141240309260000401c0d459520580440d0018640041080140c030000c005c91580f441d10808042003211941c0c0000007001100ca0981080009a41c0c0d0006003034441010b0380c10300da01c0060542c82580540c0b141c4030500328007000404400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 612020503 1250 612019253 612019273
    0x1504080f160503040519050a0522020d020d051305100b030a05010e01020903010b06160201030207060b062703070803040905090118050c0f090601080f070323010e01060f020618 77
    0x811180c034441c0c00c4449500c002030500c81801c0115000d074100307076951441e01d035090a101c00242d50100034080d150103800107540748081d0881c070020f441e011030700d152070441d5208000565a0082d40c0f2401c1010107090030403010640e10b1201c100801c4003903030024007030620000800502d9000d400407164560703141c8909054100030540a05c509041da940300c030001662445603a003807500355040804010310980d41070049c0286500c4031803c100c0d110342e09113001a40c0b59981e10708030000b481c42602c00c9800c9400496044c442d411900d10105841442d90340c60040c1c0c20400c41055642c041501803402c4607002404200075000e4160880754220025034004100100c0c410820b051081c54094150380c194000481c0000c075061600e51b90402c11400d69202c0154940400040c21052020f080c07012849081c3e0300007141144a98869103011200191115150101181c1081c030340700203004540e0f141d0700800000615501480181912800c0da40207021181d690419014034028010552004e1380112902c0da = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 612021753 1250 612020503 612020527
    0x2270d0f0309320402040501091406040308030c030403110102180d02030304120c140102190f0f0b010f030201021009050a1e0804060804140c01140904060b03090606121504080f 77
    0x44100d255010b5088a8440b0f00e0b18010381e4042c1c03d0301c82c0b107019620402092050380d9025490a064034000001d80c5255000907003c10080d100b65400a03000442c040184900d200c00000154002c50182ea83d46103d0940164494200d1041c07000c42c0c03180c0b0420096206c540d092052406910038002401d8030708044e600c0c4041004120031a904442518802c00280607000b1200e40001c0007210a2000f03041c980c1030800b0341035502c280c003100a007040030701c1030a200400138416820349141f544880000c1c5256075803890411620042c1c0012805030085e01050321206103d4858400c20759000380060400b04481e441e0504041a80d07e003803030009103480f24250208145100810040c1102c0d0703914501031406081c5066107944116108403580c010459510321030f81e10070085c8030030050341e00000759074410181c009002130901e03030312040100318080100100040c01013600c5104000a41c2c0588580000340e6200f52601804006041000c529002090205001c0b102805480034402c19180c5012000100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 612023003 1250 612021753 612021779
    0x908060a09120801061d0303090a0303120c0809030405061e040e060f060310050603070c051006091506080a090c1d1602030c0604080901090f0902270d0f0309 69
    0xc0c840e1540c8070030a0070100061400341801c1820249846462941840002041d02520388185000300103100a4525182c0c0c1c140304076182040020040751480b6600c3c40c01a280021050351071402d2403402240c8030b100ca01600d1b1a40c0703d009000f01840c646030a010402c100b5810a50308001100c000c910800360030012040100050400b40e40402c0e0b0030720f02101001b1891200140035401801c042c070a20015485100c0260151a0b04407061910b82e075a20404998107600c2d2031003c2d01e584921050744280d400070b030b8418003c0c1c034002a000d208207010000307007002e00c1c49184125000161101d000402d20f80c420390021212503c00d418044140365245400302003134081040780c50740070356500f003801014528903860001c00d4125001039410503030003000454407a135005101410300c142c002600d581580c800d041d0307e03000d8291040113040c60b0f83c0f2980c060009421045480030021250800e0300707280207000c900d25130f0100d0001d0800d40007900660b01d4111301d1403407503000c038107100d0462030105484400b030803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 612024253 1250 612023003 612023011
    0xf0204120606030210050a0f03050403120617010509030a0503010608060402070c080c030d181a0c120c0f03030c3c120a09082a0a1208310201090806 65
    0x4400705000e410342c010003400051224001c400c6c402e0070090341c1d441c2c035001094841c0300c1c884c07824002500e54a5060030350780c1010340d004903a0300600d000c0d40441c0d0703540d607081140c0750398103403000130401995441c10440c0d4902c14030b514030700800d07018801006428401e02601d036000364064000b6003440c2060740c0f0b04240b0891500809225001f1840b079600f00d050401406020815520b0100c2c0b603502c0901103070313220504038050108000d6040c0302c500c1c0c00403140011503103080b40750021541071110b108044109600044c041e03070308074001c030312407420f8a400020a80c0e004940000b00c80340342880740d03c0d00308a0001058000e03800107000f4003074504400d840e45171076404070003120303100703540c0c0d241c07291488280440051140d40058a80400c8001180f094001d440055040d20030764424203206054075000e0b2006510800128415000d490081060f0b8200c2500030849540310030b549926041010b1071422561911500d121600500c1e40000c1c138990a030b01c8400302c2c01170416005c000d460304070403810010121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 612025503 1250 612024253 612024263
    0x160503120a050703110313060e0d030c0207060504060210180b24040203040b0117151005010801150f1d06180901060f020a021e180907080106030201120f020412 70
    0x340400495651500420307a00500e0341c501004040e41030804000c15020150442c01704503100b4002c0c0040001d0350b0301c1100b201240c80111100c024080310000c003d0403c80b09606c006001303070303600001c03800c3c0603000341c800755a00e64000d07000d002011848280204056042e8500050323031440d4044c0845c017004005800341107019000344a60400078543d800e407009812269000b680f04108000118070711000d40c034107545410342c0241c8041d0401c044146080c6903409010000709454080c014000244205602160801c0c3c80c4e854960380d03140a065090400d0005080101c1e14058603d0205442401c0700030b5892501d900080c02403001d0000f06c1c00d5904030710550003c5680710408522140703069a40c540c01030200c1d1034611000194900002e464070346165000b03010301020b1492881e000c40fa0b5601c2030640e04c020300440d031070050701c0c1c40c1c4102c00c002c26100000b4a018502000c03486600c103000302c00c103480d01070715481150000741031500300134143e101038156995401e00c40841c01a1001c2442c0c40210302071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 612026753 1250 612025503 612025537
    0x1401301509021b0c010c0305160305090a0e010305010c05030403021c050f180315130803090a08030a05070e030601080c090c0d0606020a05120406090909050a08130f05091b160503 78
    0x20220061804c60382c68140c5060000ca20b103080002075100080321400c8103601300a420040c1140f500b81c0c1e070b500a804019a00c5181908003060243c480e0034680d048a004000034096034407030780380945661009480280058002801080302c00c9400704410302c040c01070386001d5103024129a00e03252281c204411160366902001041c0403949400c02c4240301200034982503401c141003c50808001c00040f0034001c1c036408001c0002001e40d681032003101c03002030b0407010640e928034140380c42100800c422242d01020502d0f24003446414100000d080b410307143c02000410648a00e03200700012014001d210b1600154100704000011105000f00d03030041030540c0003001d090b2420300d4020304042c0720000c0490b0909081c401008001d80c4103201c1c00842c0c0300b2110010f980031080c28002d040040c0740d10045d144c1c0000103100d1024164090441d01190700e400305101c085070316a0200303d104981035507004040301040441c4400301d00c0c01402420170950b040440070170f4400716070b9464295000316402e07040d8500c1d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 612028003 1250 612026753 612026797
    0x19050304150c26010f3602030601110a050601060e0f10090302130b01090303030b311103010e0402010f090f060203070317091005150604140130150902 66
    0x6030312002851071a40124040d50f5604094070711600803040d100d10900c3c040e11694902d102c2c072030a4584090030502110000003002d6030350342100a5402905c006000070301506141000c2e0078007241404150354020b0203462540d02c0d254003110305682e403400480d0f0112603038403202810340e2804400d21604502d40c842c80d50f420b10394010006d0400840580074066400e004007541c69a9010500c6410b4a80c07504000030159a14004980c400c01d00c43c2d07611200820b80921128405020340c00802d550940403002d004405000001c41d41501080c403521042c4140140441c0056011f00580c1010002030315068500640c1ca444000c10450b0b50703840280582c00018bc03200074964058501800307079044403034400711820401003440d5030711030b603010307040070b1507501d0f40464002d66040001008115008040f1a290b03510794018600c2024800c09407404141c10344010000e40960585a8204540b59030358003078040c3d03140703111102074614061080c1214035603407000310b5004203d1020300341a040c6910407020400e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 612029253 1250 612028003 612028037
    0x5031b0909030301061e120f1d151b0705060c0c010f18060c0908030a0302040503010e0a0b010909171c0617030f0c0712140d0519050304150c 62
    0x10001d000500c07290410030052010340d40056105090320140818100f600b01452000ca03650704494002c0e4455a087c0701301c0000b0368420750091180c4d142c032140101d60010201c01c44541d03810300e0700f000700d65211004001482c1c0c110b0f2840f0710684850100c004d10315020642e600c10703080040844810802c190045030030880d41c0801d204524100c00c442004100740120303441080c0c040d038071941e802400103840e4545140100d1040070300c000180307260310880b5101c903228180940650042c2c05080c1c020b40c40c2040058055000040402d02e80d9008803d00e05581d0038150f00701c020f802c2c80f00c0706503006000d4411410782d05008800401d101d040c401480b07107a0708601500201903800650040490800700c40c6c41c0401200040708070303890032811b0380b140c42d59654900c1615041202d00e41c84401c080700705080308014000850b84d00360040c0f4596050781d085284a0005940c540030302645080e101000e000c2100305240180000d541103801a0076002105103040c080d04103a480203002d400000e0700b640400200c01c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 612030503 1250 612029253 612029269
    0xb04050403170a06030c03020f040e01050114012c0d060b0303030f090607111b030c09042402031329090c0114160b07050408070602330c1305031b 64
    0x307555003d013030003018079680b56941c001d0703003d000207445520300f50034541e0f0964035640100804c0d04404000d004ca07680d45c4c07414450010305081e102c0d010500e6440030109000b140b003c04150403942d160b070307007c1005107103060103041511441c080b91003640e00c02c103240003940c0c1007000c1c3d441382551514000c0c031840d2210f01c080c1041d0014268106000c0c20b081c00069000380810500c40c25038855060313590402540001a261540140308680c002c04003509100c180862201650180121010a211301000ca906400103d2004461009200380d900700c0410028020035848280b0788050b00f0310034800455a00c0c0c08603044825909030425500c00599101c442d41c02c040d11400008042d00c150341450b0401c40315410354200f00c08020030700c150200000e0407031030003941690090a4928201c5107056100c03040656621300c500354441411014503031074582e200004c00c1780c22141c003144a0b003640f152501d9040c0c4c00e00e0b4000e1054460042a00070300400c02d0384003000000c24480c080d0704458a178900880611180c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 612031753 1250 612030503 612030511
    0xf0308072301091a0f060909030403080d020d14010b1e0d0c0e0a05010f0e06030901140403030b04060e060d061104080d0201060f0e091902031c021c030606170a0b0405040317 76
    0x200c0205080103854045d00c041990f000c00259030b010345560360441d8860552049070402031002c41d01040300c01c034014040c0c0c0a0890041d21800400c02c4011b0030090500301c00b024452003012050030070010a04003003039a080590081e0250700b0034245640603400754255000c440804000031603551200760285040424080100000c1c200802034240f5000c008100303c0411a00c03500a01000002ca01441002d41c0651790a001501c80100e00341014a002405406454070b414400d81c1404008100207407041340c014000d01d00200802c2000c4000d58a60000c1c225082c0d038007010039001d21000a42d07050500158030040b4050f4000101d960a0000c002c61400441e0004500c1019460421100140010704031190403180b0155044c9041c040c03001a01d4000070000c200380c00f100d101201403040c1d400080003100814214900c007010207441004904845152103a500058076903010000d00c500c0269480b41c100e411010041040710034640030030107503103081d20202e00050000d01c2e800c100c00b03900b54041d500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 612033003 1250 612031753 612031793
    0x90f030f03330504061707051c02040e0705062a03071205162909060903030112020a1211190506040b0a0309050d03020c0f06010f030807230109 63
    0x31080e80d109400e005845010700000c9000d241d58030141c22910042c10384030050100400c140029038841e2418402c1e40c4901050341c0b600d01c150074001c0b92515000c0180b0625060560443c180c500940d003c000141680e146445090b000380030340400c3e52f44401d4010000b6040058204100320002010628240c09451b40381d20305410910000000038440f220110720444546051070721584c4000e0000c41c041140c2c00010700701c0094a0548482d85641c08800090103d01c4460040550302d003503107582c0f291401c55000519400400040c040e003c540c0c1c00401019001a000f11116500d03506c01088607041034009544008a0004107065407410310380b031401e224222400704044625001c01f00701980103600441d240c00c00c2c0456940e6000c0d20a511051806401808070ba100d01e4001ca0043c0003503100b50011840c90007000d220b11410140016241d0481d9a20346200c00d025280d501d603620740750022401107400d0303c442604611030030b6203107113002d110040602c00010450200d01c0d12420001d58003c80d510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 612034253 1250 612033003 612033011
    0x60614100206060a06140409060602010617150a02030702100e250602030f090f1c050705060f0403140f0a0b071b1122091b0801060e0a020708070204090f030f03 70
    0x600c0340c88001341c1c0011a0218106034482c0d518020404502d030049800c1108400d1418200048259054000c0e004446014142000c0c50010390403440c0c50340800f181500444a00c01c01103071600f0700b43e60056030b20105610607645200100010b000c103175590510304200075848900241c820408203251110204100c41392002580d20b84403029489008980920351580400b040028480d140c5000e212803480b002856880703401c404495041c0449039001041e038140c03242e003802064504116046441050321040c19509084c81d40c5d550351500d1100d0203030003626010b00700c06c0c45c032070350400c00400150620501080041d4075000030010f18458000b2081c0c03a00f071072071030b070700102040204542019104003610700111403140046850010260b0b0110482002e107082440014020a05482c9020004955803215003650350070380c0c0340c240d4902e4040c040f10010120003107117456006500401c0c003507200e505101c0c281072143d000a01143d036003030740940e10142c10703817102d8080560007840d2811003241414104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 612035503 1250 612034253 612034261
    0xe040f0216060f182003060903072d0c030b071d040c09050a0605281b1a0c030403080a060e0601140d0f0204170f0a1e060614100206 58
    0x1000441031220042c0080b60344403d0440d0108440c0c0000e01c15502889240900e0181032038042d41c184240214201c0440b006070100c941c42c9408580c19000302c5400c8000d40c201200307500d0710a59004100d00110300009d20001d0034804204668001c8003a600071010184030718a1400c04c10200e03000201440708015440703030845028508840c2692440342e041c0d60009111a500030240c0300350070260081130344240c01250000384140e00030020070304500c91311404068000f00b41e0041d08500511b4080902060100342040140318078602219851405202002180c03080080900d0f0070303c009450190765008004100000c1c1900008042c0e040041080300300419490101000e00c02203000c0c15a40c10400440c01e40c02c0080e12250a81f10b030554001d000b0801189a04808002540184117086450303110b8188001144804550502441c4c80200600b00e1f02c0041ea0302d03503905001d4040c1030103118800b07803001d5000c210548203420103002c001300c1a001184618080110b080c454090355002c66008030b0803c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 612036753 1250 612035503 612035527
    0xc05120913020901031404080301170604081912060f0509070507050606040b01021f14060111030d1104210b0604060302061b0c1203120c03010806040212010b0409030e040f02 76
    0x41074895036280c01070701d9004800040380548074407010b6403805803100c0140414000c01100a504841101100448541903807078090349545d003ca5025000b004e0520071560200b040c140d40d11a4829a45880e0300f42c103240001c480100d07202c0303401950070540400340c18403190815150a640041c05800c0c1181040d8156a4490742c0d968014642d601483d04c0c1c610f8008240d000700007107000c402010310100b9440d10302a80090061280c0401c00000c00400c0c008608554001e0201580e00164003000d140f402c2e020501c10741c060300084240710b4458a013080300180100b82803200c0705610140384800c92201c102400c0415100c0001303003645108038584001080165074080c229a1003e02111300c03c841b0a840c003510301e0414070b1040c0420340000c8035052060004001000800710307500e04c1c1300441590b031603a0003c039429000902070f0106030707400304010401500e440081d00990705c0303400740003091100000c800700e015120801c004502242d080c048041880c9070501520007034800c042411030410a035003200e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 612038003 1250 612036753 612036769
    0x6120f0622080711060d0e1b0111060708041e080a0306150909150305060708190605011b05072706050415060507060b090f1915150912030c051209 64
    0x1004007600d0422050744c3c05500d816080e030b40c24070712601080202e0071000107829110191744941010f41c254201d1070320103940c02802d80448810545004021540e51000240d41844028005035880b000c26031450860985440c44d460304207200c0c82500d03454000d6401c0240613035402e07030402801e1100c15814104016031100a1208940d03d413840801c03240c480c400350b0742c0c2d00742c001d400c06032441c0601c02c00c0000c1070b504107404500a101034111200d0426002c0340e1481142d88038041c140c00200078200103521038134039090760481d80d401081600c40e00c541d5007810109114454520900c99118003a0031503a03805e6907c16200107010564043c4110a40300d00251910345107030207518240800072605c0d41c24411181c0c003c000d0000041d0508803542408540c03107868000c121b8110265513036100491284002070700401c2100c0384501801c10b401410441c80004008a1402c80420011450300c00113482c070f41040e0500f5007a001e5249d0a60000d5181801070a0076880484122500001c2040341c0d03240c0c9800c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 612039253 1250 612038003 612038017
    0x30b01090b0a051305030a06020c060c0f070b040302031209010e0c031b0108130605010905010f0b070c17150f0f0108071a0a030e0d0908010b042306120f062208 70
    0xf402507038524100b1511485101e0b681c00c22034041c86010010310130014a64000c203c0c0708840012904c5550f074022042e80c652054060480c0341080c14046803002403d95141c40750403503c030b801560305107032400c03803102c2491004030780c803081d9a0f440da9000d5503021420b015117090b00d0000e0340a0600318081a01c0c610081702d01410540c108404580040c1c0340035021842100e06c070354081014086543d46404480182a0a01560301e00104c15032000030034803c10000c0307621b1035030701040354225149400000c410701c5a1401c418101130241400350041c00c0400d403c5280300725913541c00403080d4200506800320b2864160004001c0350310542007803104003012042403541c03600b01c9050580c1c49450090440c0580000380d01c595661150881010a054101c00220140c134100710003000b01c0c0350050200819500003060661186040140c0b090400b9002160644d0009014000321140044041890303c1c20380c0d40d008800786500100203022048806102c0030041440c1c90280050f07400c45502c1c0d00c042881411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 612040503 1250 612039253 612039257
    0x105030f040201091a03060108160c02040906200c010b030106051f05130803190206011a090a0b0c1c020105060a120c09060f08010b03120712140a03060303030b01090b0a 74
    0x80300140440e8030070880750740900380d1001040e0341d5005607000142c994005803103150102c1e204500158124100d601130020175072669950070500c800c01d400744002004d0141068514548455061000e44416010b4995429a8070301c0c19a88110390f071303841400c584da1001401c2c400e0f410181c042200d46c1d5000141c0c0b0030413201004900d0504d010b290196030611401814001200b80800000385440c0048064080000c1041003071001d03d00a030b0301240c68460074065400901e0142c3c2c1c0c00c4d14000000d01c040e0001c00b401034460408035440d5030541c1025044055600126030100d1a031120100714601e4600307225010b8002072140703003021f00000707454644600807403c403541c002d00180240915452441c005044030b4204020103922828801410070741d601074000c4660800150380c50074203002440f000160b4515590741c0c10309200742e0700c585c00d48049486002c01c21926611050000c08040001c1c42c111040751800500d940ca1494040c050726505115903041c0514045c04125000c1810200c0c0c84141c064 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 612041753 1250 612040503 612040531
    0x9230612011803110c12120a0210090804170109020105041211040c020d0f05041530140109180311071d040c150203070f0201030b1f0f020c010503 64
    0xe4942801400b030406101258219100314005140e00007400c1341d01d036100c0d4025145640b04030001d00120380c0d48000c810010b41e1062114880c41d90010002c6d0040c40c9461050b611017026074015003081d00d460041c29582e00e10002410080a030801e201d03004401c01c50002844262030980029103640564414030101a0718414200100302c125100421341d803000034401c004108000303500940e40c000c8500c6c900040340c1070045160300135000d90150703004c950302158007600070184010112450fa03e030107400741003504162180f00341c038400203107441c0e50900f410740001010b00b40215800010401a844104030394902019250f4410560b0300e0280101c0d01420485800b480d5481c3d07e0746800130319480600c0c001060010030160b540022592030184c0e006001a485c0b25454080c0b003500303500c8000410016a008210450001da100c6594006041c01414005100410000840c1c228940210b40301e2070300c4130303840500c0c0400d130f00240e01c081142010f200400c3c611100c2000a0428070003c8c2c8120708110305 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 612043003 1250 612041753 612041779
    0x9081906051305010218190e13020105070803071d0405070507031d030a05060604051b0a1101061203030b03011406060405090603071203020d0206010e060a0b0315030f0304092306 78
    0x242d40000344200d0340140219038600394105c4900500b0306504d80c240c400c031016010a003d11640b1407503c1d003aa81c0840a1a0321516407405441400c00d5a0307800300d05000084c0040d90116610300302070341c030174111900e03501c4141240701310220843e0001c0c803031280b0462030801444107455012096035002c07a418100711040601403031404141900c5034001d10380c14404c44100e001003100124110303005817001e540c1480035444090480e011810803505a220014061016018142c45140c0310607120710b41c1c00002800c0b81e00c0b0200f410405803004020780219444152100f400d090900c641d4000c0b800c1103004062900340303203000400324841c0384210b030f2207808894081034055030300740566401045101d041080d52405880d020303450750021f82c82d41e000350140d000002200c0c00101800351240c0d030300034104030a250a0000c07103e1031b0341024001c04004807100070401240e807001c210f41084a42c00c4d178000c544840ca0b0220f80d206445101c00c1b0318220f2852007104560040d00020240c1d04508210b860700030401b8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 612044253 1250 612043003 612043021
    0x1c05070e1f0e0c0d06030c080c010815010f05070c031a06090709140d03180608010302130507020c090a14010b04080d0306180c2106050f040504050d030e0c060c0106060908190605 78
    0x22041c6c0001d1302014204c08000b038004170028003010242c0083c2c90f0300c021070fa07030351820600075802081d40902050440701c01a8005220302c00810816100320141c41c81c880e00c1e900d03031000312221403050b60402004e4030140041841d0038007900b9801070300b40c5401c001c81c17410b048612040c0304140002c40d0084c1100c0d410842058056003058401441c05002c1101c99613541c0c0740144640d100303101c164000c00703d45a150007842414091980300e50907903002402e0422030941800f00e1418010056071010740d0722405a6240d1f003100c043d590080080c9000f06413244e08002841e410200d021103000d00385880d00c80200242121031102403100c0c440d0510000f1090080c2c032041d15181011014064000407022100381c1c0001e40350300c00c4003592000d50780d0004030707110002031008460701030310042c009a1081c242016036500c80c3e0441388680c07000505940701554010045403190308441034811a80e51550424400c056001c5444002845280001e04603031040308210b141c0345034655000750485440d50f0000302d4880e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 612045503 1250 612044253 612044261
    0x1b070c2103141e0c070302150708030402190302030a060c020c120a080c1f020a0305132307170105060415030312110f0d0203090c09090c1c05070e1f0e0c0d 68
    0xc9006040303da1303400c180100c041e100e0b4200e01007203101d19005066515205046000e480c0c18941c0640d0720740c1b031070301e4a4080140c04c1e00c0c000040c0c0b01d84c00301c06c0c0300800183c400307100c00d0501a21445000c107615959000c040c0c108442c0d01c002d98007503928020200c0351404c4c000b441c9028181c02094269840311004001d03410058000a01082041c020206641d202400d5000740700044ea9903800304000e85503c4050404c4843d035060103002c441440005420740000305002c00001e01c042022103076016900c0728400e61000001142d00f1003a555101008401d09281c01284500da15007003013164200e08541e00588211421480e000c5059a44c90102c901c2407401c1c0308840e405802d9202c52078a400a0040050107940202c503082a6409200c40c0d1a00c20f00f040c007020b2340a2440c2c880a03102e55072500c418040c0140344841100340c13002280100318049142403010201410304c1c0c88000c015841c00a0b40b000f1111040200420114a518000c020b40c10703107003d40e550440e002c010748681e00c8144240c55000b1f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 612046753 1250 612045503 612045547
    0x606031207060f060609081015151106071d03070312300c0e0306010602030a0f020c0a0314070b07030f0e01050706110c01200d051b070c210314 63
    0x2d130701d40080031070002c1d000141c41701103640c05011200706d5207200048070141c50001c0d0500b0610048850700740135941071400e00d001c0b00d2030140344c801b0800e080107415601c1c24405551402c04142d1002c0030005100301c5001d440240a0b041d0005c0c20017500c9c5664a62007810286403040402c665a902503904050102c20038417010028050202140c6103011208000c1c0b220407000c00c041552041c0d107036524180411a5412103525401841c14445040030607241100441c0495085006036100700100d561208031101c05180152203104024044110305031610700590400d90f5001410301510001070f80c000180c0080c000c0030300e0958100e92003c3c0040e100e600400000030b2815040181e180c042c02e54203805022402803480081c008541000c0c030203481004401c3d1101c841000c00c000c0500d442c50f280e00030940103c40884001a241c581115860003a0400e0b83c08441025025804000206000a0840e42c11203100c90240c000005079074080d284d01d44103c24403506071000301d03041c83c0310b01c03905221140c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 612048003 1250 612046753 612046781
    0xc040605090627010b2809032307080f060705070c0b090406090905210c0723151e041401030f150602060412020601080d0509040b041418060603120706 66
    0x25517195006003466422079111068140300d0818409031800c146003145002900d40d4496842e031604607202c1034813104400400214205a581450320301180030440000100300c071034041c0208a4500341503904043c005401e02e01000014002c4c4004a0742e0f00d1811804c0f200d1560710550344405100c04030307010b81720650290103000e18000001c0140400403c074a400680382c5400c5131581100b698100c1c2c03c6008201c0c01420aa00c003600c18040702c40015070744d090108401071700015441c0090300003500d4003922005101000c8001c9040d001070003024040c4009101c50945203802c0034200f24002499034010340f100c030704268030380d02c4610210116a025104804013078203080d5926484500c042e645a03816030b000c864036046a600c00c0322441c404900a07040e15020800351030308143c540c0c01194507410408000f51300035560000240c16644501c00c40fa0b0b4030420341d0326404145041d1842172103840038004034000d541c002c10100120795501144200003070755101040394656034103080105c0205100025151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 612049253 1250 612048003 612048079
    0xc02100903090f090b0a060207120b0a0905071205120301060c03050307121b080a09080307180e0f06030c1503061504051903050d05130509070302070c170c0406050906 73
    0x98403200f03170341020200304026500c001d0b8640c1e5818040b0ba98880364402c0c610301c0c01c1030354004000070341044080b6400030306400001c50012200c4d00c905080850a45c000c08285001d00e420b84100401440805210304e08019154107541c9040170140042d154598000c04016000001541d03403030294640708125150035504108800c40d5011200900030800c445502140440d80041c0b00c2c48024014184441c1d07012003020f0941d110303d08181d5502104402111000d8100c3c203022803090401c82481d4428081c400c0c0c2805907041580602d0b0800c01641031182c0a1054200c031480c4103440070302100c3c0c01010030303280c1100c04d1010200500043c0a560416a031080d08201e580b042906291501010703280204103684444048180a80700c1e485201c142001201010008212a10b090444941c6c010b4803410050f1a268490341e8001a8041e29004008000400c40740c100000301e040001c440b4003030068800b000401c0c240070010f28001001000350b8401ca00300d1094030344401c0f60204c002000d00d00103845070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 612050359 1106 612049253 612049259
    0x312280218040c02100507080f0601050a1e0507020415080c3109140d0f02160b0903010b0319060506040902060307030b120d0e130c02100903090f 64
    0x2825400f81c80d0b0940151740050040ca4498801980d0b81c05440c54501030b11030140c0c82c003401d814100601440503429540d00080b64540d11048074400715600d40054104685070f20400c03100035000760400c0d800701000707907001e44c0c80030a540c200ba0035502101300440910240c050040e4044882411607904620590381301c1e414128045024034011a0001e0f8640714010152aa003540044075031000c00ca04055607480311511b81d0b0a2954401343c40180c1c1d40641a03054441c050140400020000030702c09510b50f401d5212003e40807002d0b00380c50700c155001400710348201e04648181c5d0300500f04400180c035407900d031003140c020340e6005001605644554208500600340c0e94060782c4c00007084200749140143c2040200203680f0709554107190b1302c1c2c0031030900066614a1b0b4010010f40e0038414242c41d040d4002c58007041900b80d594000031030100a0608031540c0c6405e600100f880d6801c42008 = true := by decide +kernel

theorem cover : BRFrame.Cov 611870503 612050359 := by
  have h0 := BRFrame.cov_init 611870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 611870503 ≤ n) (h2 : n < 612050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
