-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1829
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:49:33.407319+00:00
-- url     : https://prove2.me/submissions/575cbe3b-a120-4e2f-98c2-e011436c73dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 328776978 ≤ n < 328956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 328778228 1250 328776978 328776983
    0x506030a09060905070b0d051003020a050d060e012a090f060c020406030b43140c060c0a11010b060304120c0f030e040c0f08011e0810150e040c03 64
    0x803101c41e20300800070301d41c01030040203502c8012208002d0312a41d0107480e503006600060b14151038900050864990114041c0440384c01410300741b01c540c1031005200084d240c4032000c2d10b101303132500e002e84884002440b800c1d4081d030170840c00345c9030b10380c03640d182541041e216240709080018000080c004a1200384020007214898180800c4034200e038808140580300036400a42144105e20030002213280986010210a10007031002134005502001a10b032104962420f6004003010007a20541d07500070156002540024211503081c141100041032074000c08031120300441001147c0a081e45401942c0301e102c000c0d296000740205610080070411502000b040035241c03c040d80000510240114401003240c0e400120900314000c0031304007d400c0081c4001007034000da1511841d001d81a11800501a00e40f6660340c950b0010703440d01ea03401c09514020300341c0d020310080395240002d15880802207140c140401030408540c112641d0750b085003490940e80a980b18181c01420400060191040c000a5a6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 328779478 1250 328778228 328778231
    0xa021c0f060b031003020901080a08030a0b010905030d09080d03140a0222030b010e0705030618040c120f0c0e060a09020a0917060a0f02090f150d020f0d05070201060506030a 76
    0x401560000c040e0034580e02c08445500e001040c003071003900307542e90710044d04e0007640e40300c425903031f1001c0c00b0f5603540072040701074070b03c450600c080382c80800740b0f40002618800500d0f12160f0b0a461302c0000741042152030410001c901100410401c898042c04084004001428100722800210324040303184000186400d050960001d0b4041c4500120383c581024440e201c107010451541340c0c40c1c100f402e90000c4c06000d80c01e018178400a90b440344200d00b1644140710282110016101c00d0751001854031000c3c100322000460070b0404900d28505003c5442c565006a850100c5034843d42044d55001d01d4503000000007000740707410001c1d41d481c0c00314400e040722448200160b840140800481d000300c400e0300010704510b00300c0c540350712101000840e54002d2080010420804400005140480c810307000f110b6000380a1642d4041c3e649403522070710007800c0c40c2d151001d10b40b08420202a007242c0c4404040356800c81c0200d110070310f072011445156803102450000300300341820700001540e41d0100910052003039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 328780728 1250 328779478 328779491
    0x20c010f1e080c0d15170102070c0501080411151809010305070e1f090e0609071a0a020109020d12020d080c0d0209061c0b040f060e0a0b2805090a021c 66
    0x48031144201d50001800705005c0100e11030380303807001040c001d0a2143c00000150442030b20440032045c422a103038568800041010f0038540001035404503002002039a4245035260144525200c0d081001d542080606016540e0030304000c41c00705e2100031060b464060580b04006000040c1d0000711300050b81da02070010502c80d5690040020214494022224401c40700320300000c10900540100342c0e0307192105c00790f501e1a5904903c150345c1d403050b44a820306c00701021611031005104900204000306651001158480e01a004600118078002c011074042030040d01c1142000c0c6e041c001811401c101e0b01e884d00d600e040174101c8440394001d03120070350354599002400d001c1c2c40c2d441c04100c9100c00c88049108090154440c0303000700400401502900443c00c2030701c0c0c020103000902c00c00e426188500c035a060903844e40814100100300380c8007a940c018a5010407094100090b01303101200c034080e91602d0071568101014460207620160076480458014032103003110103083e1900c480303448110040040c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 328781978 1250 328780728 328780741
    0x9080309090a0e0f010e0d030507020607080610050c06040b01030c05030d2c030d021f29041e06060f05030c0904200a0315140a03060b01030603020907020c010f1e08 72
    0x4000e80b40d540c821080d880c04410780080d00010400840e107d42a40301000107070f03600503041e611680220b4400e00040c5031000064402c0c80c2503244800074203050f00c0c00c90b05007415014114a0001d05507002d650714121480100b0070000c901d00410003602c400e40c060409070b501c09401a1000b0302d5001c8d0ba07019042d4207604044800103507428561010002030442c1d01407840c80001a40750800c1c21400008000804014460006a40124015420004600c082d0b00500d10056486a2240c6000e140d019496109080841c4541d80e002040130102071000210180741801c09040c82e2200000b841c2800024000c1000122501003600c0407454152000b240940f41d40d094103440312255080c0c121702031404681514050392660002032a10482d618030002e01d40c907024900c0d0440707030911381554003004681061000561320782210100c140c0605001c2400c40d00da60000703141c0790044420780c0040c0d0010345079902560b880051000303004514141402e048c506081c04000100580c0d41c2d80c0180030107400803506 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 328783228 1250 328781978 328781983
    0x1103121602030c0d0b07020705010e010f23040f14010c030813030e060c030403051204050603011703090a06030c0210090503091c021003050405120301180504030320040609080309090a0e 81
    0x80c0400000d001e01404c000e00d1400c1030354440242c078000018403445034041050350164124000750765050f1604100000a070708105e800400711017010510a21240d0351005030246100035001130b1900f4404c031064541032516140caa00961201103040040850058000c40e42107050303190000e848480c0c8000b012024182955505076139880c45412880003d400d01042c0800707c0a4004c2d030348514103644141080c0c01c001001030255018980e4480001c100400a14200940b508012141142501e00b0b001e03501000620050b256841000841d0701c1d07843c410005030317041c0301d2450071303059640c002c00c0244056101c081da030b401001481400360501c03036140301c04240b01400d40b05800340d004001800130180e007600100908002d4804503201d2007008118180d1401003c203681c141c0b10b207001c0540c0e9207002100d1281c05070001420503800d00d07a460343c12104412100c0501c10b09019135045c46c40d911441c210004040e400a036002c4c18045d0828010900950340d001c404680126a5000c0411102d6001c2490760 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 328784478 1250 328783228 328783243
    0x20a050f0d091208010f090b06180102070f0320010813060507031404062003040308060d080c03030a0524010c0206280e090f01031214040f060903110312160203 70
    0x43c1a0040b0039000f05040e0750285900f03050701c4065010510995a9100210581c1c1c07256110a90002c0300b17201d1040d251440010007600080d0500c102d50940f991640c1d0301407254116041964010800710081a650305440d511902c140d00072310b000c080a1a0040880501114108005080b1034030b800202d00e15500c640c10128400c0d6440910303038035038201890040700074041079804c103e200020004510740d440c0ca180c1070781d2080f81c054440d40c1c070f186e90351010090030741103400341210242818094182200c40401c0a18890314a0800009213400e249502302445041040009004091009001d03605c0e613208071310b82680b55058800c03644600c40c607400821100e1038a0181c0090f195080c031040c83c40b96115070054804441618075102071340301e596040c1c40f50f141c240006029101641d41c0040f5181c840d444140c810028007410b81d06154650001920382c14040d40140001444040d0620500040496440941074220010040350701100a211164001c20440c1c50b443c01c40c0308650b02c25902d0901c00304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 328785728 1250 328784478 328784483
    0x9060d230d021c05030105060d0f110f090301060f05010f0305130218010306180f0210030e0f0d0206010b1206090403031116060b04060b0315030312090a15020a050f0d09 74
    0x240d845031511103000f940c3d00340564040084000c10108080c503d401503040342c0c140d60014100710302e040c40c120010301c09080007168a07058140c0d1120482c46070524903003e464200000ea0b0a00e07035500c1d03008101802d5550b190000c50502071945001c116503038010140b18a10146070402054654030010b140001c92081c0308080d4003d8500264036840741740b012001d5050300e214090420040360450b408400820300c0c044003c15070003030145000e01601d80020b0190841226207000716650b51a0040780d828101140012501d552040c1c07101281c480c1c05110040c007410001403210308010301078000c0003504030007800c0315010f5400100420b003414800d40001d605c6a00d0201c4107070740e40b0542d00000c503034520340c00e406440c02c80c0303071800804591a046c05030b036084441142540f400d54070b4100910f583c04440908450703251108000380001d195110032100e201751003010180605504130b0505800e641c07100842e880119204014001310b25030000266036140c03100702059900c694440003500014038408902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 328786978 1250 328785728 328785733
    0x203180105072708060c0703140a0203160206070212010e07080313090c1403040803180c01090312120608061b0a0c0f030504090e0c0112061a070203010b0907080702010b09060d23 78
    0x4100306c40d941c0303400401c8030382e10039652182c5160210254032845c0c000d0025030001604104041102200d400c0140e04180d40002d01241c6000784a60020354041d40320001550303d83d4444801c00069801401400001d02c041c2010314a40400c04011000d500940e00501202da070b036940710400480d200d00280e5880380502404607035603044c0740c140002036030002c4a0101c6000050250354516010102d00f19007102c0d4107841d2201b04c03a046a861510b01d500320a00c0804100324044090444106802044020581c07507000c2c0c040742c1080907100302002d81d00d8040c1010410304008002c0c4403548095408060360704518080510081481c044465124680c4203001d041d007403200a00482c04007040c1000192003d03210100c0246400746070905460603841400201d0014025004018a4904c018145584014000510381c200311001500c400d00581d0b6910016000309d040007443d0740c09200b00c9200329011903010a242ca80440021810718400b9001801500243c0011290000c034036840c4072110282801d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 328788228 1250 328786978 328786981
    0x9050607060b09061002030a0305220303050f0c030606030411010c060f0e0c0108071b1e030c060b0f0f01050703021c0c0b010b090f060703020a06020409020318010507270806 76
    0x14588040c201030140180b203414030401013000c0d8a010040f03140d01500c1074002d5801c203890300c0d8056005150040c0070320800c1c1b103442d9050443c140c1440c4001c0f0b48a1103a1400101400c000072800b0241c440101001107003002081841483d550300d00c00d0701d920542c0800c413007500c2700d2003030012141417161800c0106800e060081c102c404551607081380101c41c8210044030200110f4000445400e542074412401095804400001c02c107400e00004801500032100c05550000b005924a444109010150001038021025004000181c0140c1c100c002c1c044864513040314040c8001141841e50301c2400f0305002000400c81d04050083c003400e03200c8010b1904101c002c1c441c2d00f031302500900f091101241c00303c103000000701e0354810000c151090580050840b02075000b0001c01d000096000600030740035031060021200014500380010000b81007491005a01c03400c11401d103411110248041600990410041081c0207602c03090705940d424000d010032000000b1600310320302c000c0d05500104200d024803030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 328789478 1250 328788228 328788233
    0x70b0405010b0a260c01050d09030c0f030302030105010f020c0310020d15140f0a1401052d132102060d110c0d020607020a0c060c080d0504110906010509061909050607 73
    0x10a144e0b4401c00c441d9085210400040150b40764004160140c0c00701c3d409000c0c812241d0340d903070b11440c1c0c240e00c01c0c1444450f11000341c541440032142400100c00003038001006001c030b035901c1041d050030288a030005008010710000040c0d16495400d01d20b584980d80402c88028000c0c1640010402e0a1003041e2585066143d41342c050903604c2141100c1d00850b43c1d48400079080c14021814011184c800c0110023000c141d0744011180c1d94031548404603182d500b5040300142c015502c0c2003288d4421a014482e94071841c4e0b00c402102141c803a88001c02200102c00d2000c0300341b4203d001908050340c1120800c0e0ba450f242c002050042980e0034010b0401000400c00c520104000501c0318450101502241c035255640e04040b03980d0b0300003000040c10308007c040100030740c50007041c1c00c9030454498441d40303042008280c103000440d07100b10f4040e12405420400100941024400b1a4105500303180c414603041d007041c0441c2c81842121036009011540506001d1400c1c0b28800403000f5160061540b0799840450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 328790728 1250 328789478 328789499
    0x12030f0c1602130c020705061e0a0e091806180c0904020604090614040e0d0f140403200a0f0f0b09121e0d030605090a020a020f0304081609050408070b0405010b0a 71
    0x5813400036110b46000416940f42c07540584003110014140200f030f880e034480c0d8610b1541c1103c052503003401801078440001740e0324002140d120700380200812180d40710002c0014a068400381c4001802e001d070000b14020707000301044100c001c410a560f82c603003d440790b20110f00540300756802032000a00d020804584903a8100c07220610480448043c404400595065615400341c040204085185861145811400341d0060840d0b00c0e9503160301070401d5601c1d2111150740f4800f020030846a4510180e41c002032800d00c400401070150103031540e41140c1010300f20300c0c1407a282c1c01548055500494038100700c0e42c41940050266401c4010303101d06022442444104650403000034a0030700a40700c450503054400d105d0741c000c45500509aa03802d454250b181002075118412400860007012a85910441e0800c0200020421342c0010b100000300c44403503e400202c00e400c1150154289401c2c0000708042006450545030000b010f40d20b030380c41c3d52404034010860314401c42e800a02c450b41c00580701c600b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 328791978 1250 328790728 328790741
    0x90406031e0302100c09030618140f0105010503070b030f070905031912020c0307180603082808040302070b090402070606140f0d050717070911040e010e0402090a051306090b01030512030f0c160213 86
    0xf2f02c028009643c9036810140c5403e22401112410807040c40062902d2405012140e006002420b00500580c1c540340400e0030490245030444c6003803003031014041000050494118100c1d000d20190500d0b00c803410000b1b4440003180f007441c44001600000500301c0b103459006000441d4800000e0b592400c1c201e9407a2083c000c00400e1441644031801141c0410380110380d281d00c02c590540c00f41030828140483d001054001410040d0000d900740107a20005416110ba00702404220305040307240000c000070403040030440d0500318080c1c180c1c440400c00150000420205807103851504090a107075918100d841d0820300e0b80725602da00d00b0a05400780717074003200000700305031507500d046009140c2e2500e20f031000500b000d48000350010089070019009003c0e0b6448280c02078402c007143d810400301c039150385040d200f0244d004d0b2680c2c0e00940040082001c2000203202000b41540310500750300c4d1100000722042d000400300c2d416040e0003c0d011851802d103e041c0051150f00601d6401440500c222541c001c100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 328793228 1250 328791978 328792003
    0x1409030609160806160c112d040b0603040602090f0307060801050a140102030d1e0908180307030b0c1608030906040b0f010b0708090406031e0302100c0903061814 71
    0x348818046650030001c00c0ca14410b401949085e440c8094035181112484184403050f9601400030300800203d82e01c884000c5c00b1800341240340e207148909502480c3c0e003040c201ca940c41c4900d00c1c1c4006c42c29180c071b801094079070080d000100162122007500c04110741a41c8880d1407030b418043c00101058035a041410b13281a50020b13113030100c1c1d82e5180e01c801d00030100303100080d6001d81c2c818414007040920301d400498244c103000c0c6a13140c0d20302405d41031506039140ba00c021250081c0c0410800d401a0354602d01c002090b0f01200140341c00c610355101c248500c03001414158441d400001da4044111042c0c070380318842c0ba1310648135562031409501c0580c4a40c1c058600300d0704181028007060042c032122044605980c0d0020ba80380c54148155150600755228054840d0015220b0000001056150954905000614800920950207840d00900345841100290342d00c5d49425210310b4034991003004d00c400d480d4000000290244142c035143c000031501c100c0100090342e141c840e101d02c110b002c180c0031003024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 328794478 1250 328793228 328793263
    0x506010810140103150e01060f1806060c140a050709020a030f0b0108240d03030e0f0316150f1a0f0d0f03080c16080414040b0a061409030609 62
    0x5000d004250266078410300d510058801c40d50044c07020500c444516030044140304030001e81191440000350a440c003a41c403d07600c10301c40180c10070521104100e90320004201d00c0341040383c141403d10103800c040240034007802640b03035941c040c030101008201c000c1c1c0f65600041140c15665407101c3c000060b61142c56907078006400d065441848004c01d000c0d01000d030905031100d020b41c1e542e01482603800080c841c00411054100502e5110319200c0e000851040f40c0680d41c0400c41044100085160159000b1005c00c545e00401c145144040803000165103154880b226401105030010041c01504c0392902e0580020720b8040e0070465030006122020905c54190f41d100d01c011100310030420b16542401020f061188040e0101c03000030f1080b28940c0e40700e0406d0b5004c90424000c80100c80840340440c004a8001400080c28416100e4880c51b42c0141c150895051202c4241e0401140d0004580c0c401d01e030520100c1000740c0c040020803416501d21110180840e0b1051034001140f60380c1c1c58010600710707000d9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 328795728 1250 328794478 328794493
    0x10507090b0a09090b040b0d0510051b07030309030314181209060f0a1107080f0c040203041101120209061611010c050d0804030e0d050c010e10121d060405060108 71
    0x10300e40030042d41e080c101c03640c0f200c1404a260900c0781028000d14100c295200b65207042040c22550740c4100e00c15014001d40c01000c00c9680084050212039010344203101446c10405a0002c80c0c44003000c4854081d4107240c04a110451071a00780c000c2c000c601090034001000a003001025040118200d585000580031a01c43e62000895524503109451215400003001c115186e2044d60850013400303161041d182000ba010b070080202070601d9040d82154000b50005201c00001401c2007080b6503504508036011171440c20030340d9603c2055424011000d050010b00320050200031032650640d0346800000d480543d9511004424200c482c0f800b01e800c4603080510004101d080d44034600e11a0a10390001c001c3c030b2071000c0301ca81540c594a000303204030100010700b10301900035200d0300f106d00540c52040c001440382c41440fa0000d410f0003c034080c80b07401034030300c0900940d80f40d601c00504400741031045400103510f2104815000460410780c1059030520465051000300080061101e04899020094030441c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 328796978 1250 328795728 328795739
    0x20c040c0318020103090c03080309060702010e0607050304150b0405010611060928170a030b040b0d080a0f1101021209100603020f060307021906051b03090d110f070801050709 77
    0xc4845003556406402e4903540b0010055010f0b900c10f11042c0d018052240c00f482e502d5036030046c181d00c00c03503031002e0a40207681070003038594090044102c1c1c00b80000113404241b81201000300b607400700a10103400c00650742d9180d404100168008603800001030001c2c001503031142c0780940800000c03240540c440c800c250000b1003401011a0b20b40e109045178100c40329000f6481d800b0f084901046a05072400042c0100700c4d082e4400c0713a0010040118182c170302040c0b01450008200440358482441e90051092144090016810204540c43d41010f800c28001c0029100300450300003d0740c40307804005620002e5141c3c0901c40b2140c1d1140309554182c00c5a158a00d0ba45011055a0007444025000f4a034599a80100c0c9051005160311402600c102c1d44681000c50221a44c0c0791544019240c40355213400707000c80080302d0001141004004c00641d403640c1003c5802c66519440d000c461000c101041d0840207c4250a0041315050303200038044840c130b0360b182e0005500a1106403440b101081d1101c000045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 328798228 1250 328796978 328796981
    0x1050903040627060e030f0627011a011d0a0801090605060a0308040e060609090f0412020f190c0509040302010e0717031911070b07021e0a1a0415020c040c03 69
    0x10f4025044100c00d80701803504005070385255400800652501401d440340c402490304000d060300c00c1d8140d03c540c41b0643c0d048140480140001c0e0031880301d690402120b0589188403c5061449070800e21f031491019030b07030303101c112076454840041541c405044000001d07202415000070028030b0042804220b40d44800e0108107903905184402071002c0c40030300c801c00000c213407000b00541c0408094442c901d440d00b40000070b045107070b080f5015600200e243d07003800300f130000307505c07080d0702614960004046030b15000d20481d50350303101c48210716600701c0c01d000940100301c0401e0000000300806130212485080070701e0041d018120341764060b40e20b40b03e02c040010f0050940c2c0000c40c41e891508014626020341c2c0030f036032170401a5003c0300c1b109201442480308920101007000800500301002c40035111700280c41007004e2200010101108180260780c0a0126034944280c1c070111406204240d0901140100488803402603600c54030784480c240c0000c0360016004903441441c200d04540c00c020001088a00390b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 328799478 1250 328798228 328798277
    0x703121e24050916052a0105070806061803010902061c0c05041a090102010e031605070906050303040b0a27031505071b080c010c05040608091c050d0e010509030406 72
    0x20380c007811a0001ca125103613241c20b5200008000c0ca843c5280a00700c407a48880019244071120074410b1081c0e9002c8405001c3c4291900311500c1d00d880905400d01d0800200c01b40607100c10034041500401030100980e409500c0b00b500d1a40c082c1c0394903203c4100d40d004140502c50061108611420107144004141c81001124103440f1141c009080205505000314895008026054190f40d42d0b080e050380303000001c101401c001c54120180d003000d02001d25103a07040c4103959200c1c01c82e150a000040c800e43d6800b0003500c044c0c800c144103007078941c00030040841c0c4002c50080042c04000038020400810b2101544120969001c2c400080c2074083c02d1310a5000c8034400c41c0c141c800510280300760300d00702d41000800064580101070301410722514003110360840d4040141d110224200290401003103805c44c034001d5000204001805070034101c0c80010410b2071600c00c2c40d004003c00091010a1440658017031881d010f00030008024614020440d159254424010400030468551049448021106034907 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 328800728 1250 328799478 328799489
    0x105010303050f0a030b0d20150a051e0d0f1a0a0314070f1409060604030308150a030b040b180a02032517060105010306060e03030703121e24 62
    0x210b24200f0900c1158690b504803066903030030561560124401c0f5030315a030348180700a004030240015800020303240c6180c6e040245100b4041d02a68500d203c1d009040310607191032140b01d0a20990f00d465000c2d04288508468010b0180007101154103070308521603602c40300c88161114000c01c40509400321290740c8400125404da4060390b00c0b042840018016043c0416141d00130b0f046071040d940740e0303c110b0580702040d00040c040c29032039011f158203413600408080c0c0004c01034420a181c24116140100100d400400c010101c610901c0604050380350300e50450020368100465000ea410a440e00d00542030341a54250341c480c0e000448035a800d01c0116a401d2102d5008006000086944415142e007030346840343d000c01e0507000d0304001418000e83c41c84804070342011001c1c08856040c01d0014044501c1600300ea010020520b0881c041c1c4d46000046601480d00342c141540e14500b9181a0409040c21140d1200300680c100b088102d0b21081e600514820000600300c1e08840720600c0b6082484121403156 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 328801978 1250 328800728 328800737
    0xd050112021e011209050c0910030201090e06030a08040602030c07091a010333080708030414010c0219080c040b03061b07080702090705030402041a1f021c030e07080105010303 77
    0x22820541920141c2c000320001810013094020401c00103400300c0d80c0c8450151525084150030580034542880000d83c4980c450865410b2142560002440001035006030100c6100c4040411450b0b030301044111035042c6d01a80440e0380d242c0302d1000079242e401441502c4080d200c5d105011902807558003071060f4141203401491524034848004401407c51800c3c103030f00d18202140100048540602c10701604000c2680500a6a1a00390301c04d107031101d01e6016420300d030803e0200f070002044070700b040e44480c1c8091030031100940310740c000038121501c14202d900c505840071100140c0100e0204440c142c001c0e0488040040e10655801d1545492045508109402d0100b0000343c000380d0200280075414020080c6a0400000754007062211005555a02c00308034007000300030031441c09011322007000184d4803500101040d4a408200c48240c0e0700c000c2811480324216010401d842040741c1001e00d10300700c0e031000c400c60032140c010b0000c26110401317454034058070707101107001101402454100ca0349a80e5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 328803228 1250 328801978 328801999
    0x2817211504090609060e0601051806130b0f0405010e0a0b1c0b100308070606050918060711120301090902030c0303160b040204110304060506010906170402040f0618020d05011202 78
    0x1c0000411a00104580c1d0b0b03036403054a4004520240315210b51500c00b1002031006504010400000c0c0303a46c0c207290201258241c0401450340ca032450b08600003400444e01140d000365100c00101c030f90080e240390a4009192600028460341c1d0540003c2c0905206181000188000001d0100410250911041c110b5981011700001030640200c4d03640042007030b0403c0f0385e146c0c80356504032181c0e00c00780c0c2c260340c0c0c9030700c4040500c050320309144801c4c0c216a40c0e02e9480c85560030003d4a40d211400140000b060220441c04a1001d101c01c0c041c5400380c0340d60305a696507940c2c44a040a0040c1640a41640a8495040e0490242c1000030450ba103901024044c060844010344d03d80c0300041c070050080760000d445a5490000c5401c01010354011849024003196928000c80010560078140c0d00c003204101103401124032100d480f64850381c00c250107035804aa000240000040030b0700c1e4640c00b0b4030310a490003143e5003c440c6d003a4090035035185508410b100300e036070b47c1c580c205080c0a400702c081c2d03206d0294407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 328804478 1250 328803228 328803271
    0x50115150215090f1009021c050a0b0619030506090607030c0203041401090f03290c180406030209010e04170a08010519050312090a1205281721 63
    0x11103a5031000f03036203040f01c00114006805070704000c003040290700d91540ba091402c0451802c1c0310854610000ca903180c0c1050082921995074841840d900070704600b0000c40829504e03120711140651000c40c9100c50a2034940d40e160241e6600001ca07034039107881c0244000308025034400c0c001c21020020940c011414103043c0b0b280c207201d000e10207504a0601c90440b070006070781e410180713000d0001d50103002c1410f52007a49541800c607405440d050162020240e00802c1800c0e0039100c240c621041d11904a04c207504030b8140407038010192500040c0d848030b001000007681107412100203101700d104c0c480100c42c0140c070f001445440c1c003030200100007181c02c0c04014401800c21001c25524560b030702912508030369817600401d08007243c1c42200c4400201c0011a100035017400c40368074004105940e140e8002e10440c4d294a61200070070203c48000d43c10180003415072400901e140c552260b00076180d140e044034480f171490025408411103c841c0100515504e0070380100d0801148110050a4232900901c0c114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 328805728 1250 328804478 328804513
    0x1e090c041a01091a13060512091612080d05040c030240021e0d110f04050603040f150b0906031b061308060a020c060610051606060b070501151502 64
    0x386144c2c4981009000700c420301e5248048400c0240003d840305652112100661a454030740240307156055400a0301245c6c1c0d1000404c203200403507074200d613400307141c4d0100d190404280c82810342e25281142013600348402c1c800008034542c1128401c03210301083c0d02c100b00041d0b80c51078041224002c048070141e13a13240080034140c015a042c0e03815800052a06440e815060402d40c0c10f90b121421102011689c8824940a4803541d899004840c903988e08084501d02110882d10880c01098091030000c00400c0c10810300d107a09403c0541d000e458154002c80300075200004040f0070301f04a104510b40c20114031981408100c02015116081451302c00042c81300c113226a17a44002c0d040520220740e5100003665000032700c90203004420440c4050b07a100e00b800b40461a0440c068001d40c890031001c2140070760190001e08543d1800032400c003000f04541d050034480020710b00d5900115829600180d50300c10402c0c1984041e400b141c915180400c1e00351221007a481d0301c81c120440e81301590001c2a03a80c81004075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 328806978 1250 328805728 328805759
    0x10804030e090709050109062115031401140109060b030a090311010e030d0f0509030430060506090a0203090a021c0f08040312050901090b031e090c041a0109 69
    0x68103050440068501c04200802002c80d095400590280e00500040d81c1c000004801480c1611f0518241c030006540206600c408844068200d83d0b1500c80031080034840003114025900000102c0031710000c20b14560181414114001d80643d48a002003009140b5110355815a221400e0580c21035440c201580d0040041540039814031981412055100d03500f400713a012180141d6001e56204d90604c034601003a05c1404c0000700c481410401040800b074000000d403022070703144510010650031991a011080c0c07203013540c070090030420f00c0340e5042804140d8100b80d000c1c80c402d90300c000c0b055a5221b210b0302280401c0d00ca20301a60405081070f00940b51454035001305000442e40e4001504031a030340d0b44118194400121500000403a0030028090502200741d00d003400c5061442c0303840540c5c0c00003040100b241c000c1251a01c40400410100008203842c880d9101c0d100448a4081c1080c4004560f100c80c40004107105038181180b4004812184e00c3ca822490010303141e19201c1801c2100d031001d000301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 328808228 1250 328806978 328806983
    0x1030216020604080a020114160210050409320f0105150c010e0a020a1502030a0323090304050a060509150a020f0d050706050601050a081f03050102040b04060207061d010804 76
    0xd15003203060159a400000308000c244038801007032803403094800580062031100e40c00003801c506104103002e1100b10401c1000c00c59044a01c0c0629814101c016140c41c003a5822400099142c5900054103080004041c00b0302525025512800c40c011020402c4041d0101e40510300c040c29140100802d0078401502d401c0c110750354858904101040341c0c0c1908550b0001c294005075403010240c00c0550502c601003802400e409071a40030700070105003020b944c80c40360003c0ca10030103540e58441498034820f14108003040900d40d041024a00302920056502d80190042c83d10440d0100f00000e0b0030382c0210122914035030058034507554004040b1010840f80c01c403040501c1903000707002c610081c0380000d104111400c001911842d88686944c249801216801401103040c0034040000f2900640c00a4070030ba40028041404050410710541002100105a200503c1d660002c02c003c500c06082d48003078002c1c1d0b441d6600b00c602d00c0d03646e000700301c17014604001d40031b6a010240300329021b59481541b04660050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 328809478 1250 328808228 328808257
    0x3160605090a0e0a15080610050d02010e09100302010f180302040c050903030301060305150a0302030616030b060c0a060509010b280308041d0108162106060323010204030f02010302 79
    0xb565000c80408820003100c04202d2160b50340310b64190500d441744a20090115940180000c0c50412510450b200e070394002e8034462070a0220b000d086a118034004008868064039a10003030421002122034021540400ca0120f0208081c40200d0751280a100d000d08180c00c882ca07480e18699028840100100035011040000402400c111610700704000c0d4002d1140750350000301850001c2c0765402c0e81801a010038071940554004202580e030004045402413800c50317882c04550803c60701500101407a4043e9508140b012840ca45021004a00711880c94001d03e4280820358541c8030040c01c0b1900d0700142c0d5030050305409011000b4030028003080101c0e101019801019489445241341e0750400e611026640303000f1030141c1c207151002c29820380100f014000801c504440048200d4040c0c40c01c1c01a0303010182c6d212800c0325480e004070209040c850700494200082d945034140140c1501e4100040c40403100845994003140d5030510888040302d42001d04c0300b041203900e5004401030b6005850414014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 328810728 1250 328809478 328809499
    0xe070e060a0f120510050f07030f15060f080604110a0804140709092001120905150906040c0b040e010e180d02010209040605090c031611011b0801050316060509 70
    0x1542c000100b100030300f60703444406144415030b26126103000c182d82148982039007000d081c01000c080980c451904031240342004149440114100c200401c0004a200300007401d0000004025400c80004c8405038059501e0340034039602c25061000b940c4031401c0049020038200315106032144900c4269030000c0c410900701010047c260b41d103500d002c542e0340161400c0c03a40d41d42d00200b0040e02e000701070070145c03180c060b401a6005c1d03000040e1160183c00c010794a2551244840800c02009000d000391400b4403ca00b5103003800c1c060030f8981d989000301c41c220f6144541600c003150903940101628120380903070b2000d112503800e01020300c00c40c20f80070b400442405a010703c42d0324411000d000e01030344e809480c0e00050700d42c000b00d4200025580d09521540c05402c5034000d2108650007034003140e601c50074041d1242822801c2e2030045490200540d1040001d520300ad0108850903030804203000a140ca503956824184d881d40109600d5006031005200c103c0c4800b5010090340303000e440500300400000300b500105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 328811978 1250 328810728 328810739
    0x708040b070f0606180e16030201050c010204120b0105031e0303040303180803181b01020a02090405120705030711120604120e1201051f060c030c02130f0b03010b0102010e070e060a 79
    0x20340e00260005e1103d28503506040707204428611a055000700395400a01d20102076a620103104617640c0006410048000351021030302c0005d404403002412102c54460203030445080081c05e6903020b01440b40300e409490301d5503000380180749000c0c80a000b94000b95141d6201c070f550503001002c05510b088030500b2403c1821010400300400386114043d19250381130350801600d100fa042c08012841c1c0201d0700041e806541c001d0340c1c00039610300b0065064403031509a031254144207240240003201e450074540d000448070304204000c800390220300c0c402c1481c0e11850241004001501d925180c044c9000d40c091000603010584103980c802942d2801c0c189079640d002c1c1d40c80880c80c22641c0c40c0002e849a034540060080c2c9003101e81d07400d040d585503031200c828003a0400701c0080c0002803c2001a0070012182070081c02e5544440c02d40c81d8060580c84100001450180b85001030b05040302910320a520380003202c511540103015013076500008902070400c2c035081c00d00d03215a80201404c103580000c2c0541c4003052 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 328813228 1250 328811978 328811981
    0xc1715010803090f0109080703080d0b1c05010b030109204504050a030f1b0606053f030702040e1f020703200a12120e01020708040b070f06 61
    0x1a100641c00b950f030f241c401000740505410660354480c100b0680d01410040d5081c04113480095035409160150b96210001041010745a81001180c2c0060000800140031808140a0803a0f41c40746000b0b0107040071034070403d800c90303c0c4c02c40c0180c4038000b00e14505000984200b0500c00c0078200030640c24079070300c0f60f0750700c1442d1100c08410b011070302507050099021136a259400070307560100440103600b40e1500d542d80c2512841d0382c0071300400b480200c1d250b008000b4001c00d0341404400c450213042070b01c80b66a040290242000d803240314056001c01c50120f4080c28100c5a400fa0340103c0007885060341c04c403403803a0865504045034442640010701034080141e03914007903070300040745a400400711000010f42401402800076880c0c0917281c41002b0210000349c020101003804140070107075525000341e0b8240c0070306004160100a0400b0541c1401075a034681103e41d8030034401419104002081001561500301d10400e803025186110900003040b244003e41c0003802c110384106002105c542d400d645810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 328814478 1250 328813228 328813231
    0x20f010c03023a0504230607030f0510060815120705030601060f020606010c0816050d0f050a080c070303090203030c030403050d0c110d05030f0a05040f0e040c1715 72
    0xa0009400207240f000003440c10700400b095455070b03800b942840d0b42c1842c184200e0381c0c684160412442d143c400040912000c0800b1403100041c8900c410701d805102540583c1750070080310280046031400c888100c070419544101c52049058052100c0e80c28108182642d103c0c40041502c01151422401461540c0341c01d10001000d101320401070000904213020141450f074140c11000411840314400f12004c1da00084040d0807010078285036118142a0912010358070819182e140000e43c1740051004009000400c4483d41c0519501ca81108500080444291061034070301400541da040100b48020602402045030a20134100090481c10903400f080c20750700002000c8429810205c0d0800c184039080c0240d40c5407100b00e290004454016949446901d2805c078180c0c0c0c007480041009204000d402c100b01c0300900303d07000485031520026075001704164401d004800070f1682c0007000199220850781894007450384200a84152814140c0080d001100b2101001c2c2d10f204d50004180000040700119 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 328815728 1250 328814478 328814501
    0x190831170c01031e020c07030f120f0509100e0a090603080c0709020405090a020306041508070f080607080105060c0304050a03030c1a04051207050a0b180f1504030f020f01 75
    0x590003495002006042812140c105818941040e074045000320101a800c03074040e18059005850710069a801d51414140303410003450060000040410b000d10001e0005041e10240d841d80300e0616046000c4170507020f15000103400c825003001c3c101080d40207940d030f1111100f02500300010f0950720038880040d0b8a40e6802500d12030f10000e840d0343c142c60140100800352011070b0007035150500c2c00000c119140c000070710093390039a0100200741d0f10703503a03600325134442041c070000b48120b951661107903520303601c4034401d28074003114004000611090224503a03218096644030203050f0b07841c260034064680d2055503040c52a00003000003140030f6540031030300c6029600a0b6113003c2018a030703103407590803849140c2e451500500c1c14020003000036000101480d056030400061600c0d11100d02c0c3c40c5240c6001d40074002c01d00d144450400c90350303140d400c004400b884030fa00b04440120304081213040d01c0c0d40d000d010154001c990000083e003c030380520710505c0c04505e00e00c122031a10020706172103030856910f029036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 328816978 1250 328815728 328815749
    0x903140f0703020d020106050303041517100503011d0d030506210d0806030f0c1005131202091f0b0a05040b130303030b01090e040b06040b12030705190831 68
    0x21000b8180e0410211440200c01c1c0003c000702410030740043c0d038034015880350000d0035541d007001225040c0b0440720b5240340780700d49002881c80d087c006030312455810315004180c003c0d0b10b84208800d09600342400c046159610380c014001004081004030050440240700581010300313003200b0780581c444c9190300d11241d900314000d0405e801100074000c06c681c1015052500ca0f501c007a01d00104640041000c002c44c40382241c02c00000001104240c40600961011941c94205031030005581d040d12140d01c1441c600c00c13030b1201c485a81f503035120350080400200b986101820040140704980c0c54000400c40211141003e9080907034401051820f03500c42d400b202d00b6a17490300000c0040507014000c41000481c01d081c510000c9041c000080c0507040d005201601d490f8411012810b0398460381c4c0300b1000d03004058000034a0441090301c02d6600e0340a4101141d09104508810440ca0f592074820179580d5400b00c0704034070303040c040c030000711204400c03003914401c0c29041c4c400f80f40803461a0081a0050070030208 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 328818228 1250 328816978 328816987
    0x19090504060908190f0903120e150c0f10090506010e04061409010c02070920030c0405030303070807170105012016081510060207060c050a0203060109091412030a0903140f 75
    0x4000c04c0051502c45c41d400307001100b1014030000b4402c007003980d50304c03015140400f60725005038001605411821521760f0400c000107095494480c0200b03680000116040c21925184d03514034001c0200d803100e003000f03086a04103000600c2034403040700e055034000d40182e0000c43c544070329401002080f00203803039030f2400da903403204807080442d0103004403401041800710070084542e8100414a14050a81e400000140000001495030400d1400e44021301300c0a41225207031724102c2000b81020009032030701c0010030710f122000c050406503840398a040c3c0c0c0042c0d40d015090071046911048016100010f40814050b02510301c8184000c0040c40e401880c9910091200d003080d40c0042c24003000242004401e903030810028044240c001912100300c0e41240b03090750100815060083c1400980b55009526004450001481c0202d0741c2200c09000d000390240003a01d1341100109941d03802004011000203011701c001003114419600c4850b8450007401c15003004c050080c5103450320307848031481c205280004903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 328819478 1250 328818228 328818277
    0x160615080606150d0b0a031a0106111603060518160603140615090a090c030504031d03070306110c01050901090b0f0f0a0f06120309090b19090504060908 67
    0x121890304814240c800506000f980c0107050100d00c100c1303600c2d841c0251550004401c0d03845000d4200025600007076801e1020314289100000700000b0722507000013403003038070742e02512802c085030402c029849040000700c0d4074510341e1040c0241000400074030441f440792987d000e840a0900180d119201c810040c83c5c607050034000c0c06012100c01304001d00b40c15070b100003080580c1c0c680003003020a001c2c2d032010803502d070710150380040d40004040d0040c042c82c50038881d2504049406410060003240302e501c46030702c5e91a07148800d40c02032001c42c2011781d0682c400d40301000450115484181c10b00c40c0480001e02d002e04491805080d80c50a44601c02c0303ea546011074414050380d17108507600854515140072203400d1400030307007542c0c22026142c500030559a441c141080c0c102503006500030609a100d0902041081c100545840c40512035401e125091800e443e500c4c2c584090844d00091a42003c000a1400e041c41107008000007070080341d0141c0d5a01d443c0010503190300c00b901c2c0460078400803075840300601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 328820728 1250 328819478 328819483
    0x1b0c0f0a0b1308030604180807050c01080c030c03070e06220326040902091c050f01050c0306060f0c0c040612050c060301150302030406061502100b0a081216061508 72
    0x10050745500440350b61880015400c10100d90300214100c80120300b164400c140303021440340328140240003c50001ea0a01040804030b480031a108098036418115900c44902c940984003ca404020307120301000054042800707888408200d040c040c140c030f428200100b581c10030b4131850390741041c1c444910440410400514031114162001e02c154640b602607071280c0e00c0f40d407038003603402001d40032274000c80c1c40003554403100c1c2080021410342c980304004111509105490380c1d4029034051183d4208000115080191011240103090190a0070302e1300048000c0440580c10511000321580035494880d02140d54030b00503240a0880015410b00201c400d10700b0918145403104041c0c05220103000420154101440c489650703002814007503980c0e0396a140603c0102544c1d000f5a400c00350341082c0301c6040d9800103000d03a445a00d03401c1000304410080c108010b204091264100a078451201f500b0b91540c0d55002e0300d01b0b215011101c501801d4143c0c1c492007510b119400100102001540030070202408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 328821978 1250 328820728 328820731
    0x302030106090225050c060304080903010906050a1a010e010e040905060703020a0207120203061b07020904051612050309010c150c050a0801050103091110050403020303030f010515030108061b0c0f0a0b 88
    0x200304904c012100c1079912551100c085507641b920507000030000500b400f1300c00301100d00c2403400400812204056181050080c40f050301c400560340d01d02450849611a02261490700030016101c8502128840703004440c48202b2555103a08142c83e80c052000085040205500a910325203000d40c5403442e03900005d203000043e500c810f120300703d00c0071004090385000c280380f0f03001521188078201c0c1500743c00d540c034814414008001e401040c454108002c3c80008100c0c80403c5d001c4440c540e0b90710707075265a0509040c6e1032580260068004000340c801c42d40c05140040d000d82d00c511490940003820512010896a0f20b02855000c1000024132400c1564000c060720301604090808101c808a6a114000c0003a401103040c1d0045140701d5000d070806000e1000d407401550300804403903503841e040e4043c0c81300710305c00c0c0b05003401340846c1901100b14040c1e038019a4180c6403003c1c001e00982d034550316003111030050302c041000c00c604100001141d41e401400718048100e504001400c0100380c5c0d1500c0d14032400c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 328823228 1250 328821978 328822027
    0x403080f0103210e0d120e190902070303090c1d070f02030d0b030c0406090e0105060301020a053a090c06020c0609090c0f040e0403080a18061503020301060902 70
    0xc001072002a45412044a0070014a903440602020020041d0b442442c0c0760669a840312240200c001000420101145060078036500c080300300b0040e00034021440c0061019180503141c1c0c44051000351400c0c1d015100082c001c1c40d020544010340d84035411b4040154000303898081c00000746144501c42c01100315080700043c5000b6521f00c10310b0100039224000d0740301240000391148078404195508101049012a009000308522a500d150341e20041c41c00c51203800b415400d220000310140341c18401e41d500c58250f501c91900c7d00b5070181e840e101134909200c041100030743d0703020b502100ba035a080e404c42074465203100c0001d0349201c604081c3d00241c00b83d40844110b600044604031544c89070b0050751a4a80152002c000d00c2d00e82d040c80b04a0390180c50700802032400003080000d40b13840851401c50246010307803560b42e4561118880c02003680c4150b444404040809270408002941c26441070000b40030618a013540280c580d4000307400d44450b54080b0f85429004103000050740480f0301d000e0051103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 328824478 1250 328823228 328823251
    0xa0e0307060903030f02070801022703060105010504051302040b0d090203151012111504150203040b1c020702030a1202010b06030610032f13050d0c090c17010e040308 73
    0x2031901d0750040070310829000041c00c100c061070441094034020000c120141034164020f544071001c880040c1502140001146030004040341cac2c41c00e40741004900903050322010ba4900749400c0c101800e101c180c0160b449a50700081e82000000740d04141d40c00a454184807584011078842c0d0540105403801150400420f0030407503031824424000b403403038159401c407002280c10101d2414141040090303014040c801c1900f0442e020300f03503e003c180e10b2001f0400d481e84a9038040c01021001c50482e900e0281d8002d10320440b01c00c110140d100310819000c070b1002150701700094070300f001540c0402c0c00c08400c007408030754001c891606107000540a0203030100c544001d507811415460034200054106148001c09402d055a0360848005805038040710b0320b40c14000e0b03143c40c40d000707075035400c00d962580984001603c0104400000ca280d01d01400b0013541582c1041c81c20701c0c12810880104010080c090000003400384400341402820f0042c80c0c40d500a00d080c04540c0701d04d2509050280c0304450017020b04070300c00b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 328825728 1250 328824478 328824493
    0xc200a05091e090a021806030601060f0c08161b0509130206070b0a0b0d0503130b07151a19080705010302090a291206041a240d050c0a0e03 61
    0x40c4082403000c0c10490620011640b03451021031305010301200065002514008150302d4491417815241c020f401c1941100d60603a62960202c1d4150743c00c04c4884002104198824040ba140130003410b044c11076800c1003c400941aa210320b80c1100714200b503500100108010440c92030020131666000c140600c80d10031600695001640d103116a0600410810348000803c0e840c0859502204290802138401e42c4403c0700ca00700f095403078101251104059031180350100744035000205a44030b031a4050065041c01262845c03407000707060022600000e8940c8400c04003c00e60701c070303c0508070040040c4000844541090031140c101034050f0005410305004200d8090f20752500c44482007100e09180740317100d9840051440d040381c510701e00711a4644d16004070b00c0040420f14410320f2401803904403010021411040f0f900b0101030402201e6540c0316108888030441c05102030115400b04044204540c41c1000501d001812108146da0314003616030042800304000360406401511114110001d1850 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 328826978 1250 328825728 328825741
    0xb01110a08030c160305031008070e070f020c090a0c0806060a0c200d210f0909020901120609021903090b01030206071e0b1603020c030d0c0c200a0509 66
    0x36009012001072100c500003001402102110095a4500d410352010f19045030f0203043c024050340090b074100b1200c003410b001c001814000064400c0855042151403413055540400680c2c643c0000035000080d80620b0040c0ca50f66901c8000d42c6100e04c441100020300020000340c020b0107504c00502d00307402490108218a60300d03400440005030280d1103080c4150030752039003250103030320004ca60b5001c0e0022681c0801004100c000f0300452103006948050380c40301d9006100444031720740c45060803400314401c400103000a0702d0940003001c0c4000c0605001d1400741c41580d04008460130b55100319040740c0e000c2460580c000d2a58075140c51000c952070240401e103115266400d200f030b4103200c0240724500c002040c4041099440c968800c8090002003146450b41a0030301c2c1140c04c104442c0d1094400d8038640101030745000e0b100399145007440c00021818984504e862000410f4103150440a00c1029050000050840b0a480e603088102458210342ea40c514406d1041309070280d000503203d2980741d81000711 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 328828228 1250 328826978 328826983
    0x15090b07020613030503070f0b0c070312020d11040b03011d0c0a030f0b0402031305010b040e0a020d021f090f090e150402060c0a030918020703020727021207030b0111 73
    0x90391501110040d660b02103150800300100c880c4e40c001007440c080400d00fa424000d070074850000c10740c0601c065411942e04c80b0000f01c56840350700801404122444504042c500311980a400c031343c03030046000540308951010380d4481b030708194020f50741c2c00300020062002c030342099864500c0304045c4540164a0412003c414030f02d0140c0d680020800d50303180812003800c54150090703c87c100740034100f19030321309121b900e4120311400600c1c107841c10f41c20004040c2282c1854442c4501030541003015290b42100c9500300100ca04851900b0b03a407000c01c1440e01c52003001700348150842c50b4000c2e00c90440031032601218402c500e01f6548000449403900400070703151000480d1200c84a03900045103030391603613140b0006070140200010301d80c0750b201e000301c0e440400d40c00c22924030a8950f82070500240007801c4d0b00d240f00f41e1144000c0100181c0042c501088140c001303901d021056074402402c0000103c2580903c01281c05c81030200400251900034420801c5c0c05215081f4004005e00e8101d402040e900820340c0e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 328829478 1250 328828228 328828237
    0x7050f060307080915041a0f0c090f150f0409050c070c03140109080c0d080a0510030f0f1a071709120a030b04090602070c0f03051507030207050a03050415090b 70
    0x2040c03100c0c1200045014000340640075038080c42c035688420b642020b0a000310411200d00a51f9010208000403640c94050000c40c14800c00491100c0c6280c4620301e028045c00c50700a082550b045031501c00301070880c0312a0340291034400c1e8280d80490b00c4614102a036000d07a0000b5082019840c1e0400c01003010800b69074045046d02d4003c0d108014110b10b0742c03a950b00425080707502515030400400e4506034041c021524a8414502d0f940303200c203e44607014002c045032002c1ea16504c400b00302490810018040034070700e24200d80115401c18444100e600d030040210100b80c10b9080c10311240017084805904000c11031400e04c1038000c4846e680c80c14000e51a50fa0207410328040000d08089035401115101c0e411255802d40040c02c2401050341d245014006074110807000c07100c9031400d5501080304001c1904100403a83c00000070494458501040000500040c1a07001055020804400480c4003002405101803099607125a51460115010340300b0152403c00c10030018980400c01a19080d9000e44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 328830728 1250 328829478 328829491
    0x1419021302031e04060510080624130f02030103060614030705010e0d0c080f0f2e020403060e1506010203070b0615120a0c020118121413080105060307050f0603 70
    0x680ea6100c0c00d101904414151050390203c0d44a00108410040103030840c0d13000300c100150892002d91108000d9848000031603030765541890340c4083d25031400b8401e41c90b080ca100b01411000000340c0301800c003019034003901e00c1c403502c0503000801001040070a1103450000c00c03008039608880d007034000c000790310b60440f841100d04000390024441e04666524070761010040e84154800a043d03030301e01c409522225000103149090003503e450075803884011452485003808452450740e145100081091a5002130b10000c041a41c00e10000c40041d0750b920402d03610210100c0140343c0e4000c00c10b4042e4444800070116030464006000790800a1200c032070b1240c00650464542914245000905005004000e076801c1d0340404041400081081540003488040d0190300900c0380900c041c540400c1c480d0440300081121040c0445108414031400701000100440c420b0b5520341180c01c00d0701d142c440c0158000f150b040c0d44d03035420300165203000c000060092605503a5180c5a078007a0b800108540401802c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 328831978 1250 328830728 328830731
    0x80103080d0c0e0316080106060e13020d02160809101404060318050312040b06040915050601020a141b041104050907020a050a080a030e070503190602070203060414190213 75
    0x10a04080c0169283c1c1c407240006411592031843d002d8440c04d040395148110706483d4030340100890070342d10a800c1080b81d02c2c0302800c40c1c6a004e403040508802907002c0c13175104003000d50900082c00710320140340748040c52070301407105503445624060030042c006402500e01801c0c0f040c241c8092421031111020b5404444050800190000180d010100d41400200000b0f01d54080003035040d9248194040c13860003940100f0b0350314075682c2c03030809200032501c4d5510701900c142640d081d00041001540c0080e540071030180706a910b22441903640c54a6801ca107140d40d04c003a0803824030841345104507212800f21200840e42402500005508c7c1e80c110310845c000c03180180700c12000104401c1c020020020a6580702d001c070340103100142000246a00041d03141000a0309250f1540000c1c0700009880c0306a44000700071f000c031075000c40d600992203422040c1c11501c2c00d40074001d05000d0303030b001d00c465071040d8010701c001040d80001d10f49903402c0001c4901d6409a1003403146029000d41c0742c982e140320381289507910 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 328833228 1250 328831978 328831991
    0x207050f0315010b190f0512090f0604030305060f01030902060a030b1906031406101713170c07060f020d121107030c140d02031c020c0f0106031101080103080d 70
    0x401c1c02c100900c101d600040d0002c20000503068a00e000400601512a05402041c0c18143d0201c803100070b116100d50020700c0a000d0320010b102075610150308080e100d42210715113030368040da40342400000c41c0c086c0c01080c1e50394100310003030411500070347c0090400d10303041101040070340c00104140222103e01c4109652040c0680b0b00b9218000d00302d403032117034004010003050307940c0f003004004c1d01a408840c10304410a44c00b16202d42842c080c031071500840c5407a41840b060360130401c42100310008207044002c501074441107002c12140c1f1240310034600c045138400c2c0d450007401c2e409031908145500880030400c2000c0140480f56000c20324031600350b07040c0380401c420b9542e40b09401c0a041d02400a09030f000001030810b04140c1c0089406003400e11a1701c00c3c2d040d661001003655160010456140c005d030300f081014881700c82d10a5102c3c48103002c9084014105507074154800d14100b0050400341d040d0707554000c207009101480b60380440480092030041001c0d819540c401d0941d004450b5071901003901c0b4070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 328834478 1250 328833228 328833259
    0xd0f0f020406080d21270c0e09150402040b060406180e010602030d0c030b1203070b010b0a020d050c1005010312090e190e2a0f09070507020915032e0c020705 69
    0x401a45032200d904006c1d0b122180c4c4ca0b031040401104101d0125440c24082200003200d000101711144110072840291858200c18401403c080c0c50080040b40d00656506a10103981d441c0c50280c07015002036995640f0882000d4010030340c4a01d45d03000240b07001807820040002c00c1c0d0010440b03d141014807804240c6840707444d0250040d0404400c0c1070340c0070398440c800c400000c80000c0a40102e07800345800085907681c07144400f001d8411b02d0080710068102c1d00d400e03110035001e0740061159402c03100440c0c1c40c1c90b10440c00c080499100ba001101d01602070340000350460f510001c0e1001400452907180d5040c10408640081004545940101284c0b0f5207034000c607110003404120450324001d0031a400307821403c0601840ca440f2203403070b10711801c5281d24058a506025288500c50006516890f24200c0c840d020408400d400918160f440040444502010344040c4801d212200480a21540e450340322010400c2201c5585050f5000d180f510314000d0155500043c14022210b050351271108148894 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 328835728 1250 328834478 328834481
    0x602010507032c34121124030f0601030b0f0303040902070c1a03071d0108070f17010b030105011b02030304120804080d02062d0402090a0b04090c05040c0513090b0d0f0f020406080d21 80
    0x64007440c14980c008400c2081d0301000d15500ad100780030990f0108204500501040741c01c0715002100e03509a402804203004a0545900038010071703001d0000501c04654900d09001000c2d480d41002071200700c08401d00820725003100c3c4203e18240c1009000d040982140002442e1580081684081160051a041440780140842a02e444095000303c10a41c2c5500c1100c80d02e9100380709080c001581c46803c008903643c031040700e07010365500802540c81c2c103240c80e0030155003c40003441030f034107079108110002e807641c804c00c078191142c04980c014010a1a0004501d17640c240300041d6002d410f400410009208442040c9055225078121580041ca848800098008003040034410fa045454442c202c0c080c007070340307000841c00c40700b040305c09129000b50201c04680311301401400c080700c682c3c2000c044c0f100707080302c2d005a40e0005000c1c1207410345015079240c030075400304c5010080d180740c00400e0044066007401d0040034080c0460500402e40000c40742001010240c0d40c1c81512078600c03c00c1610030804016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 328836978 1250 328835728 328835779
    0xd050a030c141603020f060f0f03090717011a0a080c010809071d0405072103050a1202040608040506060603010506070206030907050907090602010507032c341211 71
    0x182044550303d2011445080d031411140c08240c0c81a45030f908003c3e014a0003d0480b641c0760b0889110310b09003281300544010b6500050612015805000e42c0480d86800107040840c5401c03007007002040304048241c100c41c000442c0700019015404141c0305100c2820005140c105000081c41c00034003039520362039190304165590304000101d000d586441d15826030b0601200d8040e901440c03d861465644001034440701341150106030a4181a10824000c01c1c000c40140600340c00504001d100c52a4403640c00f42283e010b60800400f1800050900085c8981003100542c009810780e005491541002e000a01a0248a0009104000000014080c040c05220500061201614007241405c1819010b0101003450140100540c0380000096100d4480d0107880c410000790468682d0400a1000400d0712184145660000f840f4448900003158070390318042e10031501c0c44042200080210650b01d03c95074441e4443c0000780c11414005010490000e0415000282154803060007a034950001003102d0a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 328838228 1250 328836978 328837013
    0xc0f04050f01110106060314090102090a06180b031006020f0c090c0d02041802120f04080904021812030406020f0615090414010e0d0305060306071709031309090606050d050a030c 78
    0x914000140e407941642007100c107009200300c00e42d089d648100245080340030708140c8607840a044001005118051604051460810400350700001e03180c48503101103078000d0b0741d07a003400200580100006a810b1140c881001302c0c0101901d0300d8610500028a1103401070b00070f54064400040400c070105150f41124000c110000002c0c012140858162000750440d1040c000e91000c4540003c20b24a06600e9552017940d00c1a070040c00c1492000c01d0100a41140c841e00d8821030404544c1c8201e5603030018500b081580703d400559459080c2100213080220b02d000310f0301d01d035201c80103000030014010b800f40c0001c1c10541701c500107903a8600307082d500d080319541c8000300380d440c0c0248151000c0300824907001030071980c0c40c10302c050345401e02410307654031044440b400003581d00480301941190510710300da00300200d401100e052820b017001281d52807695911000c5403d40da60925000c01660340120780052008550f0940c05c410360351642a140c41c5089c070001d041110041502040141c513260785800b442 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 328839478 1250 328838228 328838231
    0x1030b030a051005010b0c0a0b1909050a05010615080a090303020906070b090c0a03110405060a0b04120c080604020d240608010c02010e0102160212030405030609030a080c0f04050f011101 82
    0x8500b48183ca036003210034408911070a05002041440c07680003119035040d4040c0c014501018191200140700c90050190001c89071010740340105c01c0c06601840031824011000313064001294980030f804c5a5090f4482e072401103030710171010722003904403d50aa001c03100040200b1101841c2c41c04400a03c0f51510040d881800441d003542441100c2002c0742c880e03c0f1400848800440150800c01d4500840c071004003254214160707000d1904140d0403460300140082e0181610360344562201844d40c1241c0c100c0c425403601c0500c40c80a100c4000c120600800c4000d01602c0380d4100354012540c0800e414001030001d410020713402416044450750091442c03201ca00c00c00005803030707140c4280038180c3e50a00300010360a0110b4120140c4061003111510801469000300c4041c455081c08900342005807447c01901003440700007034a8409019951003004010051595003d2400b40a081e8180180980c1311b041410b00947d00544a104101c906a400840384041299801ea004844001c00c1501d48030b901d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 328840728 1250 328839478 328839493
    0x3010e01021201080c010c080306010c0c17030d180c0608041a0103060204090e01110405040b0402040b07030207060215070f14070c08011505010e0a0603090510020a090f06080912030601030b03 84
    0xb0101601503030503143c042d416034458030100401102c00c0e40000340090720709201040800c9496000710001c1021234444c01517040819541d0310282c00541c0c01c01002c040a800010300d0001c8041284141c800e41318891b002c26142c0106034032800507090003400b62005218150000c1414401d28580b1031801250310a000b1000b036850b03140501c0607402c1881405151760400c80d13102d240c90410b01038081052a8281c2d11404c0502d41001c03c0003038020300302d80d9034200d9800c01c004a0b034604040004c00c4418007a40051150504d130282c02850100088850000d0002840c00c1c891070360384c4040b0500302029a031420340c0306a010600d5000d600d114020300180b07650140d1070001540001900015468010780402484081e078840055442d1718030f000c8030365409482c0c90401d001303290190344100e02c4180a841101d80ca121440141412a809000d01a001c81d00c4500204900400900e40ca00a0559440c003490582410b456040e61140605007201214a0210000c0d81c0c5074070a5005040c0380400070102c8414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 328841978 1250 328840728 328840747
    0x3032705100c030b1003110702030613021017040602030615071b08010e030d050c0906041403010b011d220c030f05010b0405150a051303060c1715090603010e0102 71
    0x22103000781e00399a40241003140006510b03000c2e00c40d60300c0c0d009000d00100408160707118100c2c02440c40d21a0500301c414107004440141c1c0701000310354850540f2050850f000000c5004000144c068034025404004a64511008000310b0750103064201da8000c60260303e90325008001621450813589070084400082580d0082c085000c0c601200b594000103a00195515428620300ba1440c0101001141c0e1040050b1840d00f03544d03500c03442e03002a8440000b030030406135000081d80c42e03001c2e40c0b110080c03504034484c142d0540380c28490130b4281075090030302500c40a101c000301e040c0c4510035050360303205414007103882c0c80c0320324100311200000540342c7c0d080042181c4c80c100603006018604d0612951494040042611640386084034181c44000707101246002500150100d541d2001285208206040c032144040540701d014a1000c0d41c0720303d80206211f101844001c050038600d00e00250f805000c1414000c40c0f9000741d040500080043d512140036a80341d2001c240580360b1280e080000e5840000c06290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 328843228 1250 328841978 328841983
    0x40902010c0312020d1a13050c041e051018050f13021803100606180602070b0f07021f02150402150703020c030a050a030801120809011b140106060908010e070303032705 74
    0x1b0f8401265603100c2d640c0f45442d108110b840840e407228841e881080180032020840c000030b04442103901c40003d002e500c07000030440031180c4c80040b801155074600750307040f15010545194040c103816107482c4000c070010000504068800c0d03a80900180c1c0c00074911b03860150b0682980f41c8040050202c841400b80ea9800b07000800303a0b8896100060030740100c01e03100700d0f411300c3c418080315103a50003041c10364200050010f480e84407210070040988108107600060310307011006020a0203006128041114401020f0301307004400b02c2020b0741c5a070031010080103a442414064090481d04003103130301c81b20280340aa1404405100440e890700c0342412400402500061407080c0c42e12035640d58426980e5694070006107103001d54010840401030040d02d40c0303075114006895082241040179010f501ca20b45035000c0c21440c0b0441410030780d4454200340980c64000c1e218000601b0044000c01c00d8201d02c560b401d8540200740801410591551095159004811484072070440003400c0d1850301300e40d5103422076 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 328844478 1250 328843228 328843271
    0x131514040605030102030c0f0307090f080102030a0e030703140a0216140f0108040c06080c160c0905070507030207140402040e1311011b03122711040902010c0312020d 73
    0x34400c500380341011803107080c18000d5038001c0c04115012030805000307810b0480150801040c00d410010b11490014101110403120002400b8040005a503403c1100c03c1a0545180f001d410710182d00402010b40000c0c0d00c0010300406150990b18551201c0e4002401c81c2044220003406c04114080c0c5070102c1c0f450a01001d0f503e03500d0040300c0003c0499003d00042d500c1c400122009415011070100410805000b080b810307501081c0c24164a14006c13400d8808100314043c0782040d5402c540384142030000c04510310400b40c103c42e190034101d040c948660340003552404180602c411a801e0200c001e50319480c1c03a01607a010700f9565040d580140380c01e03500889020b071a80401c5c2c8420f9411110680c070740d4018501c01c020700c0080d400680c2068040d0714161040c10600e04042d507940c2e40e681129034072842c042c0c0d000e602200d0020a40103804110b0820500103001c0c0050b0501c11f070300d04501080183c0e008031400c0c00e100c0d80f5007040117064258100d02c030001d010390140348001c1c5051042c80d03107480d85030b000307401e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 328845728 1250 328844478 328844519
    0x130c0909061d0a05060d0605041707030816051911010e01020403051f0240090b0f090717090114010b04030201180311060d021324020f06061315 63
    0x403100d54030f034424442034400036195150040880b0750b01c0c001140c0c45402c03240d030182c01801c444240070b0f40003c20000359840b16006600040000c81408010a90994101c0401c8018500503080c051348001e00d60040d00312011250600440c02c602d1010460300f904851040b4001c40c000310345480d6241002602d9210500c89600886c40180c51042c4162940c800d0b1120014070010885d24112820b0301a81c4818485440101c405000d41401106560403400e08000e441c140c100800c9080d030241c2400415070403012203510804403003080141c07150f84801c000745030003d1445100d10a032207200700c0e0390040504ca54030300d003690410000031030648070303220050084030700c05e0340c40344120120052000c40d843c03054000101820707403031b000303041d0035247c007801400d0380b0302613004010b1030444844041c0c005075903150312000c19911101d103940208002288071004050f56800030741900c1301003001440c1c8036100180b05900c5141c2c001216240d4a40e50303030100004c0c1802c1140c8000c610348a04100c0580308010604 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 328846978 1250 328845728 328845779
    0x41e02120a020310141305010f08070801050f270708010203071416080906040504060f03060c08150603070c0618120c0f0807020301020c030f0306090114130c090906 72
    0x201e0042500781c07007200d1040a040c414040d58a080c052460b4801d1034490645501080f00400c01c055140705108941c000e10783d0900e02c80e001440d10083c0350401d81346e41e00002840e4035050070451340030040608103601c002100480004080b051040d030601c6075914011500d5031182c0c440105411805500860064011741c41e00038090040b0000c80402e80f1500982080c450114210180010401e0018042d0880020049810300303031078101081c101ca0180d4010f21105202403410010710011b44207440d410140da1800070b1441c585807604240e00307945000ca05008050010000d8281d602c078503012455a58010420f114081c041240d6410b12212100d0650780419440701081159005405051046600c004805001e07040e945540105801050069070155020805903184a1050000b00b9400c03294005c85601c80c01e000c1c0034801c2c2c503a0142c01100a0b60202c0270041115aa203008880041070285c001085010301041c00310b030100c460b0361190302c4040c1400c1d80490107646904031007000c004031104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 328848228 1250 328846978 328846981
    0x50301060602011119170f0a1512240f061409010b0a0804020f04090f0506060102030a0f0e130903020706170f130f060516021002130521060c041e08060a0902041e0212 73
    0x41c0700d0001ca154850b20ae08180680f04000004100c0d588003078029104088003d8800300044a4100380c856000200c041c0f10355400707040c07005d44c00c061000329210340c041d12254025070614426424034890340c800f0b102440b107102c0000701190340300005090001000b078824825514146044812110041411241401800c000a0340c07941300100780d400050317559490b0394941909800980d2a11004968075800c20310b40e01e1160380345015401101c2c8424825401041c5403868880000d060811314180008102d15003418881c10100c40d84031030703800046200b0441c2c0304c0e4010f850140c42d41030705500010b11007401d000401c9483d40355580040c1d042d5095400343c906d560b0360001035200300d2081016200864110b0381d4240700c00d081000840759511858a84481d4803690400403500d40002124032a5450000180c11310160454119090741d11580c0b1603503491290910f0070745a181c0b0002401c1c03000560f942d107a040259903076508043c090001800c0c02503011100004104083e41c010f0094907111081e030320 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 328849478 1250 328848228 328848251
    0x8070309050615060903010630030215060103090b0c030613020301030b130c17010b0a210b060301110c010905013210090c0306050301060602011119170f0a 68
    0xc0c080029500c0340152026660750180010300640442e03800d50030583c24010219292824850040505400a82c20412241e520001400000986102031007550a114840006030b00014250205c0c80c288403102000c1d910f05004800510300300b8006003a50b0100c00522020f50329000003140181015034001c21182d402d404030409030b02c003e1000a082d11081400292842c00c41c1b82e002952612031200b0031451030f500e076a4400c042802e5019055140d64803c40700c6030515110300b4031802880070504008462000120711400c0040d04c100c0a024a10241c0c00146c4d166001e610211611421011342503c2d41d4401040c14001d0000210480c0e20f9840c000c3d8280703500400d1052045000c0f40c2881a0039210b9454a403448032801c05000e40c5189145204040307120000ca01400d0400c2a00b99000103045103000201400d5405581c0843c4c15645021002018041d04000b00e41e031600701400004006403040500b00e070302544c0f84003a60030340f007021800c0c0291184440b5005000d0515500305112032840758 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 328850728 1250 328849478 328849481
    0x30c010507171b1c0f170f0403020f070303080906010e010e07030c02010227040f090506070f0e0a0806040b0f1003020d11060301030c1a190c060603050d020a0501110a0e0d1b0b0406080703 82
    0x401c46801c20441180c0000e80b0801c0e000c0d147c0d070b406480791040d1202da04000e080b09240c0310568000301c0c08600802c0410024030002c001349401803085007950300495161480e000d014330400341c5903c080607220620880700c90b000350100d5000e1009514402c41e6030303042d804031b00410740300403513054816402d04081115081590080850054105001c1e1106485842003561242541090007041c05140340f04001550744030300440c002095000083e20745071900e4a4038403001031004003103498603c004401d0000c0101c581902c1c8056903410b440e0601d0303414007800d01c0c425420700419101d600800000000c801c021200620508640701d01c030b1041d8001d11440c06101040c010b407400c182d0681c911100c40d0018a200e142554a4030b8003139500000c00988a03150241028860442800540d006c1110681041824400c4501120354400c41070f007040f640748002441e11444241503131080388182d03010002d000028842006d03266020304403256883d070318030568002d40c0091280d08045482140002c403458081e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 328851978 1250 328850728 328850747
    0x61c0b0406080d1d030a0c03050124050d0501090503030c040812030105060304060f0902030a06050601090914061012050114090a140402090a0914010605030c010507171b1c0f 76
    0x2540b015010f0240e070381e0340440700c0c00d56036903a82c00050340705035450340c0d182c50030300c09480030714054003c044801e811030800c1402d64054440410b564a044000002c4d2200700c113a01e5400d5030f10403a14080c05003810f08100d030143c1031203007019000b070000106000d04030800000400c102c9200030140d400b0000209156040c5000034451140c025a0170400940051405da1040d400389001200c0042c008803542c010920b050714281d41152145d82c1c0340d0600c0300e070f9a0040d03920002004036400922420070125030642c03030500043c2866000e030315000e4179600c44c03c3c0541044107608610305c004000d95030b9102c90440b44501d070a01020700541010300410540e40083c0201408081d8001400417591030342d80c00d003d12204004d2150441c550360b0a150800100c5007948400c94502c4000003007103847c2020100340c180340038840c05505001c4200000300c0000e00b1442d54058040d5031524070381d124508000e9041a410210140e03d20501414031502c07000e03042c0a21015005549a03150403220f4002070060b50700d040c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 328853228 1250 328851978 328851989
    0x12030e010f1d0d060e010b150406093503070308010f0503030a0c05010b1009050a05010809190615080d0f020d021b0612040c1401081003031805061c0b0406 68
    0x240b41049401c0406070800c80411000b07041c0010030000c41d1661802c03248940603882c000e035114038284181c1d2600d1b4010401e8080501c4110749420710340032001c0c101001500c920b545c03da440000c040028020b1032003440c2030f52403030500c0005059440c1b0000d074072684400c4084020491100c000309a03003447c080c1040903290058025442e0020111096440016040040f00c5544d200c04c01c2c1c010545450029a05002403600c07104801c3e410101000a92007680d040b6504014800c07080020901002603003000c21202421042280c09150511070b000d08007400e002da01c0400506000030b084a0005015094080b055070f5010341017203065001c030b80780d03c0f9000c05400168440040c00351182d0a02010b03180c10503000300003d180401c2c0c1034040e6010b04085605071303070b2000003050410012482c217180d290030070b500b4078114060389070024a250070081c15010180c100b02ca417a2200c48a4180041028040e140081c0004e450b6032602d0b1646520348080545840c21604080122400d030500e80110002e60381c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 328854478 1250 328853228 328853237
    0xb0a18020f060c070b0f04080c03060c071506030609030806130b0102061b040f031a01060512010b0703111507020f0a0c14011b12090605070510050901110412030e010f 73
    0x1c020701080b035242c1114508203c607008480c0b0024208031214010000801c3c040c482e036445600c1c040d601410f01c01c10a049a00a400000c200011600c542c07048441240e0b10000c600039105000e20301c5401081c0980000b0300180c07419040d00e0030b150300b1400807840303100c0172910341074610100c080e03107403d44064000c1c46015038000e0020811617507000c0414072009102282c86420070b50351f411100034007803680c0d106840c2c42c4c00341c44800c0740a8641184040c0540542c1c00d1103032501039030030707040c044c04d080510660340c40c40e4020502c3d004240c4244a5000301e00706c400704039035080d041c1c8594003da1540c1943c1400151103851202e1032008400b18400d507103550000400f4001c146001941400e5560028506040050903c07201d410740d0443c6030350001c060300400d01c5008100c42000c0c06400300000d5040a01403000a0141500241000880030007445c031500b400300e050f07100c515504d4094074241e040e0324010000843d0219908403100c0fa583c0c0743e14044d50312482d55090780b100541c0d94441e40609880045c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 328855728 1250 328854478 328854499
    0x21e0c03122a0712110309040612020312030c0a0c0303140703050a1b0c1e05031908010b03040f0f0302010b060c0606040b0409031d010c12030209010e1516080d0203040b0a1802 77
    0x6011700b50f1400c0d40881001a240340c42e207602c00290881c0c2aa41101d00f40d00341c000034402c1542400c00020403001601c004503451400d04030795031030940c000c9c6005602004004408841003510a0b0041c02c40070041e101079600c0d90800300f1018000d004225080500c0c41d2410309490b03000038110400c0d01400b40241c480c116100707035a4459200c0340c4d0307a405080007802c1c001807560001482c02c20041036921207501114507074010b441002440810180d0009003120010700500000c1290043c00074107590b884001c2100444181c68180d025103489403c1d01d600510203d07140140ba030001c00c51500c2188101d804000340c0c1150b000304412106010300180006000215107040242e0402c5951444101410103c42c81202665034550103088000320100090700840c0035012542c0281c0c2020351003904441c50701c0543d00030540205103005030103006a14801491118040c04091000c940409100c090155502e04d0070b4144001c801100f681d14400c513514100010071280c140086140e82e00d94000e054185a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 328856978 1250 328855728 328855763
    0x90209180712090f021f020120090910170703020a09050121031416060b010f0f1d030a11090705040305211209010e10021e0c03122a07 59
    0x604202c0c0046440c101ca40304c02d01c0c050b98560880e0301c4812802c0168101200c54890000d0a45400c1c1c1c104108691a201a0702180f13840071007620034500741654068110307a81e08400d0b1003220300c00d40c0040b4605015840301070700144007060800a0324000d582903404260790b880701c0c01c00c40c0d009102d0701c207510224808441d856103e035801500c8481c06460001e02d4a00401128601a0b00226900c0640c801c0710684030f08100060051145499003428444c040340002c0360090b0003000c0362404102004a41c6000c40b20030542440c0c04035510343d02a0803642d0040403854030001c8420b608008038491510a400650380510031021141900d60000280003241134030f203011820211801500a50190f043c0031007000344020408070740c031590707070f6000214800b60214090703030034582070901c1011114010401d12031102140e40c00c4040d0f200142d20183d0381ca44a4556035411400b44070a255080b2440394248250841c40e0302005542c03034002e0030f640510488025030100544545100106142045000ca0702d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 328858228 1250 328856978 328856981
    0x6032f100c0f170301030209070c02030d0320161e05030906030c09120a0606090903080103021e12010605131802010c020f04020d021806030f040f150204090209180712 73
    0x24079128008007461a4195600c0c40702048881d01c06403060500880100158500121000d401030aa802d02d0401481e8940110703403550240c400400c241600c600f035040c4070920a5107034049650100c55615249c0d51910800551900181ca01740c0748510154084a0f140002c01c46a014090b800002140f40ca100407080c0005908014030708260400d041c0030b80c0d902601e0300c1d00042140c0f0640000380030380b4140e9160520403120140c01c401001450001c065001903084044541900d40450f090421015501c804103510704c851858650004140c580d15045c0d40015000340c0c054420448284a80c1d90107200603800b1910034080c1d01d02d1900d401d80745040907502520069022900292103000360034800d101050a0342d104a6180e0b050590004451641c03496200002c0d460b80f50440f480b600d10f003440d0005c1c11243c0c0025001401b40c0460b25101d008002d44001c500d006920049400d544403130741ca400c48402900300341040e5004400701816801d00750451507803d48a41c0341f548410103041a4840d8910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 328859478 1250 328858228 328858247
    0xc08010b0316021e01090b0f1311031c1106091204031101020c06190306120b010501052b1406040c080703021e1909080115060c02031006032f10 63
    0xe60084082680700314001e01303010002d0f44001400400c07224014680f8034400a0003d14419803200c04c1030920001c050032042e004000b50300800305481001d142c00000341480f02150130f5055101040c010082c0c03060f045642001d82d02c0e010002e03907825642d01d44007a903c40600c040300140302e0030704000600014500d405252407403001881102e03883c05203c0301240455001030781040340320220340d044d03a04280d4540220005041404448809010385541e5196100c9041c003840d17060000119520210781c6001503403410f443c01c1c0030562883e9103040c400351801000207800d0714607541c01c03410014440b4201b5009800c0103014660304c04c0303555a204070045009400180880040049070f1040d02c5c42070414070080e0200810214464441c0c2d0300000018011494a40c00000280d06141d40c0c4910414184030200440f0f1890815543c203a886100281c1010038050015402c903180240200a101005a52000c245964503010501440d0207003110071008000d028554032103a81122605128420070458 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 328860728 1250 328859478 328859521
    0xa0203040320060108010b0409050c0d050a0b01030c141e1e040e16050a0b04210803090d030b03010e0c0d030504180507020d08010e1f05030a0303020903010c08010b03 73
    0x11410403001e0100580042c6080788010090384200f0050105010078407035079681101c2158104428a620b07a280d50700d41c0e031112956031080150000e4503083c442d0501c1031401043d4016000c01d01903031249800400100345003c0d031140f07104104215840d604101c81c100b2001c22002050241c0484a0700030001c1100d001d84074005c8100840340e00007241d03110340c002c0a035600b08100141c80e1520450003000d90300ca02c1c9600880c8206102c05080200100c144215015581503040d605015005007003002c9515207005001014050004100412b00d080819011421045640c0c01e00101408508160aa135030340440e0105076007003081c00010518044000f08071031482400d01c5400d00ea038551541c0c0c15045e075020403403203103501c880410600365414010110309401e91b0400039029410716804820b60700c4014034541440c41106820080e40340c185002400621006046840c0c2c14014a40140690040141a4065801c1c070324001b103602d00420324203050364158180f5900310f030740b2054040740303030070410844 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 328861978 1250 328860728 328860737
    0x102030912030927071209020a08100b0a051003020c010e0a03080f0108060c09191505040306051503060f0c120106050423030d120e0303071e05030c030a02030403 71
    0x180c90561200e0702080e4070100e4200140d61100050020700400840300c0c8820003842c00c1c0c0074284142c1a5010a84640002507803070302d01140c00c000d1038036800419240d031019500181d203803800103e42c100000c0c005a40301310018184100346200062220058980c003c0c40d40c8210660744c8214040d11070b60260400707840c030300c00100d0913001c2101c1e8103062801a590680c00502e500c0c0c2040901ca040c5160715005085071401001d07145044266034005018000c3c119214504030469500f2001c282d51403000642005002c01c0c2c1c0c02c440c004c4004d4019445848100d95082c2005d001882440203030040c0d00c124080030300035040741c1e521030503617a521910007003115500803003d229056003084448496030180020b1f4139030315a250b040c802c0340380c0125056580710000181494041c17a10307480101308480842001d0805000840d4000940e4010b00f550040c00d1185100120405c13604542c05102d010075502460120200e541554004655510084401a4150504102003002400154001e59009019182 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 328863228 1250 328861978 328861987
    0xd0b18010305030406080f27030c0709050603251203140307080f0a090c0b090111030d05180f1207020f0303030f06120d09090c1107090f0c050a120b010203 68
    0x490011482a04180da0540c40480d09026094001000d00c1c2c2114110340291705518011128040d071540c1014280c54a2101c0c40014007544020000d40e107080a4550030b80d44115141c00321000144403c450140c440d1103849103507142c07a020403000118030403401000007002800c1c150405400390050b0b0048007040702c90442c2c80c01042850b80603500600c09035070f5100d50b6040c000e00c51210404050003041407940b419002c440016040c1a210382281c203c403080c591545039140058a02e4a0001500b8516000c0001d4000c0b0301031407035001e64461501810000001c0344506c20040d035404401d01120417683c00006044c0004903490301401681d0300c02040c84007245180800f081c1903800990380d07050119334a00500400f0310700344204560403a6440f008144050304140c00a0980d040d6202d00c54105070344031202c030407941c400c6407041c02900105085070030b91a40c0b12a11001845200b003400c0b00a413511022046481c4168100c511809942c1c0c1c1e400c0701c5405c0d002400005044002c0388505501c010403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 328864478 1250 328863228 328863259
    0x212090d0c0e04020405071713021f02070312022e0b040c0f030f05070e010c080d06120311030a050307110f010626030c03120406060302060d0501061709030d0b 70
    0x1000203000350034403110b058142841484281c0700081e201000344014107842d24944100c5250441d0b01540d14108007420760518000303d40c8201c201c03445030f00300c0c2c500708102524258000a40e003045038411084424243e00e4ac107030803038643c45d51110705540c00403001212011260121130720244800c2c0b10100080c807481c5100010110341c0f0602131074000c1904a8402c080103038040c07044c41410024600140802d1400d0b00300200b4001d4000380c00d606000c900d0100070144210103040d0741c003103013900c101000039a46601503600e100260703103401c0300045c800200c06c0a242801009540e03545000362655030030b54640d80010b8039412203001c002407442c400c155906001c40400d00682c0010441e00c20034a21447e600160010203801c81150550035a01c104080d03034060704000f040720401c8240c0c00e400d04142c0c455180000181419510195020b800070800300c44090655001c02c0c103c0b19540c454078800105600602c103480d0040f03c0b80e8542e1380041c0888504401c1ca40c10103a8148030090059240d035007104d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 328865728 1250 328864478 328864493
    0x405040903030c0210112209090506011701060e0112150515030c060f09010e0d0803040302150601031503030f090506030c070b0606070f060209040b090708060301060f060212090d 78
    0x7640002d07100c01507100e031a07030144038900340a10340702000e0000c0c000c000d94941d0300d44102d160001d2401448102000b0352044508014040c152040e0140302e0711544ac140381c0e54400c000c0c005c141c0402c605206032505da41c014401e00341250702c0150b01c0b40490b071038068840c0c0c81c6020250196000c651a078640188040c1512400b4481d400300f0802c20041c040031003d051a000f007a4602c280101c100304450f031000e003d01070541e81c80100919042282c01d90369400309141f9048280000c000010100c01c1c401010b40105044181e0a4000c4038041680c2d141d9004409450780213918401410b0b44201c01d01c0400d104041c00304d0301c402c450a0415049a960001c40c0140e80102d60032600390700c1c04241e900400454607030782c5801000454110f41440401e4031000001d0b0780ca5240145003a90001d000d050945454219082c040e100500110192030143d41c00740a5240440b4003505c0b039441c1c440007060320300d1b081c1d141c0003c6c2c89841d8020040361800b0444040c40350702c017516165014259050399800208032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 328866978 1250 328865728 328865741
    0x70302220207121b0b150118090b0114191103190e0310111c060b070303020c06070302030705070204091e0302161202180402040f06091a0d110108040305040504 70
    0x1e00c41c40d501e40050b40c0c0c401000c043c4007076440011a80d0b41c00d01e00303011400600c017030b6400103043c0003400d60fa410344100607038161412039010030020100a10026181d85564000f2550000c07c0e01c5400b1101e003140700c0742d20580704100c200f103c4045441c0d145500d4030701c500240c0d5560b00e1064111ba1901d40c0c4814101040d040d001c000c84c0010300075000b6903601c1e0074180981f007084040c0220a10070700b0410b08610700c2030302581e44900050901200d2481c2c0d17542c4035401401c014000d030f100d425961078003810b005000e50301c42ca074000f00510818012840c42d41c881e01c21039214034103559480382081500c1d4204006008420703015103662100c10744031a850790403105111003c1d4881d400424070384220340482000ca00c09a40f15001c0920381c1100a40961601d140d0f40480c0e0340312050301c004541d500d1001800030071161108080035441c00c5804114180f86500c8441082040f02004040708400c034204282d419036200e00422000714a4446a49540512580c41e0090301c030341000c42c107090b12070b070129080703651 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 328868228 1250 328866978 328866983
    0x406030221011b02070303081b04061d030a0309140f03030c0a050f0f03040b0708190e01020f031c0b0112020d02040515091e0411210f09070302220207 66
    0x260300038004000d0910841c03d9141c29103c0c0900000848900a5101c02261202805101d545000650441701d0f50342851202c0a1034a0f829803170799100d90780105038103da000c5c0d086202c1007610464400303240c00240301e441d055059a41200c024205102007009c2c2c62034031141d41c1c01842c01d80c03403160644d07814006080c2032800c820092491510760b051041c6809000c03070000000d078000c00368070001500003004940946008107182507841d807440c42c04d40241d01c10000a1030041d0080c00721000b8250f4003506000201c18244c0c01c94100e101d80a40240d200d2264849900341210b04890b1007890201603000054460f0050400103182c2201c41c0000050380d000552042c481a0300240501852a0120320040d0040450083c1c6007020002008100a110b0040c0041c6442d10908148001a56180c2204000312090018191180c0c184400080f0b860b002c1c47d41502c05100e0f00000130900b02403c050144544030800043c4255403444c1c080c892109207015480c112059000002010799842e40020f00002d403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 328869478 1250 328868228 328868269
    0x504050c0f15031513150303020d021b100c021306230f041a10080906070c0f060203090102280206060f030c2704150606050f030c0904060302 62
    0x10114010014581e16050007144114411071451510607044820382c1d501c00340c0c0a8150300101c80070000030320380c18907440844154070f08050300b031218a510480c0800459100b13400b100c00d118420f0009a841e04500303c84401c0c1286403c06041561a0070b112440c002092410f05410f0044980c0114640148058071070031950b0b00d9034410801b0b40480449854041c00000e031540d400c4003a140050940d0900c3c0c50600d124607141e800b0f40c0480030300c0c0d0031400280ba070000e000d8031159140d498090001e81c004c070f41c0c1c03554034014000007a60180c050441e80310101d0307010903007181a0845907103590085d0006024101c803503509001c0051080e80e440303c0c3d10480741280041500100d110000243b078031000401c02c6008812503129120180c41c00a21a000c0340012100c83d41c3d001d403054542c90740c3d0400e1940c40308450300420284824010230f08490501061900c0d030520070b55440352000d031858815040c00c03441440d800c000103160300d140c000145c03000980c0244041075681c0d403600001c4550880000341e40180703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 328870728 1250 328869478 328869493
    0x12020d1a071e0c02010f110f0616030509120a1409040612060b01030b0901090c0302070206180a12050601090e030c12030702160513020306011e0c020907020303160509010201090501050405 82
    0x4221001144442d15034501d80b0802071100f542c002000c407000104400c05000c84002403e003c1d80007440f03488052012001294420300d0650390540c0d107100c20500361030103c2e00d003a022484d2524003081000400001c600d41d0343c40c0c1b41448900310f038092a40460b002410f44188003541c0966a503010f640010300000c2200a235201d980e0801c03004a80940c01510306140c81c044001403a511544c3c0701e00c1c1142c81d1140b0020b4298100001600688200b6500035440040002d0600e07031900322480d1410b5002095035051150b0707455007030404034420340d0034026149a220300010400301050341c22a4031480000f10544c2e0404580080c024a42810058103500d1b00d2000710410410980c10410f80400c1303143c3d40b180001d00341c0b600340810b03086001c01c060a2800c42d00040002d03501c1c1d000d40c809618407000c4002c0300c0e00550030300700c008101c50041c072000c030707c1441c81038040b8030600d10010503a400307144460650300c80140240f900707483c1640075007440b60540d521140000f011900c01e00c191403140380204080c0800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 328871978 1250 328870728 328870757
    0xa050d0e04051f05040e0f030417010c02191101141204060b0402160b2206051501030203040203370c0e06030f1f0b0a03060b01081012020d1a07 63
    0x69680042039060481a181503c42d61816480000c00458030252400955a1000a1038a04085002c19000c01070310000800054022160394401c400c614450f008000c0401c850a0407a21084403510042c0001e105a400c00702044003540117032190041410071041006011006203010b400a01e00f1200c1941540b0801080c0b101038050700e260b103882150110725100d5007000441403840b0076100a0088050f000006010340681a20b030344000d0f8880300e0700e03060700b02113140250190a084807050740702440107947d407189501078002c1d41d010721380c000d000d804600707080f071b4203a14003100183c65084c0d142e0341401c00401c0620010032032180d203030280813510f04d52414080c0e000d05101000e00b8041c00f941c031a94030316158a5000c02c1d0b900f4400c92010f85004045511220341c0041c00d1400d0400e54170a0101d1400010041680d10012160000785ca4400840c1c0d41c1c61100380038000c1c20701c508107864029034a400b005140c106007603100f0702e02c201c0e984220f51036402e03d0109150310403078440000c60064a1602507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 328873228 1250 328871978 328871981
    0x3031a10110714031009060b0301020c07030303060f0b37020106080c0303121807051005030103060f06030203030901050c01180c08100608120a12090615080a0515090a050d0e04 77
    0x25003c08400c024004200a022990b203041c4010401c55003542e0710445400c03c00356411201c080b05009000b552101010f08841d03440702103d200440101f0b00d08400040c420000d60322020458261640f22400d100010428404c1d103c0950a00718079078411141513129880e004100d070083e44426400080c15600742427030103280210341400310380300b40d00601c04010186d07441400b20790b05c1910024515070307031505010301034900681034100ca50b00c070204100c0050201c0c0d201010358100c901480b01800b19141c2d0300c1c828000c940003808040e4041d0000c008151503540614021700920341c10000000b003c0f48809194181000b4004d0200c0d000092181d04200440d420046a620f840304008200a880d24180800740da40c0000642c0758146080420b000c2c0d0054007030503c111040313100807000e200c0184203140102c02820031042049401351600d8000c078508100282c41c0030140e0b4410001d180c4071035031a814203c00c400042c81c200e128801c8001c0340b400240240310507143d01500751524903130328202c0401c020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 328874478 1250 328873228 328873243
    0x140408091c200901030f290106020319031503021c02150301050a0819060504020d08070507050a090204060512061c030f080c07030806010e01050d022b0b01020a03031a1011 75
    0x901c42e6181c04014170210b006080006442580083e0600d66803074110104100a80180b5103101d503005200000101e40d50044010000d40ba41c030f0107481105d55005105030f08807000071180c642000c1207800c00b8001410700c420241900d11449010f02c4900303a070307a40050084120303424203011402c0088010482802e08c0d0095001400440024200f0b40c80e510001c0319041480f420301130070842c0c840c0c02040a42d1200b02510041540102455941d07a02a003006546c2d08014440d95005014180c00060034203054420f4505803803a6aa40615041190313100704072614014000e00e60100d0f40c40d00710466215142e69180c0b07040c0c4aa103421840c8021140080e1017070000400c9011134440c1081500d00080d4000421a0300c5042403c0c01032981200c940122900d0045803400520703184009251807141c40c2081c41e02540030101c540705516050061000000d40e220381d0381c881e01517031000b180c1c0c1001074040d0b003100310149280210241c811341d00c00c000802040b0f9048070080030450b141d002030f04d00c0600b84601c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 328875728 1250 328874478 328874543
    0xc04090207050115120b1513110c162d050d03110d08060f01050d1401080a020a090911060f0f040303030506130b030d0f020705040c0e0310140408091c 66
    0x100d1101c01246c86245c50817100070008581803070600d80c45100d1f642d82c52408902080c03031220800481c4d000d0b001329121580300c0121440144a0004400b207010b104006510940309180d00c44c01780ca10059101102e2440350040314200c004031240301141d140c4852a403034461500a554004030319001d1140c10f420200d0b031045c040c0800500c0000c003c540c1e2a00040214102030a20300260b5451203004800d00030100500c2080c4040c6240c8000074500d4000a000e040c500c1c001c880c0206075075541d40c2e0080450f029010002d181f01407201c1202880e207408406800c1900003500d07894640319001e00458110b50098004130b001c6540c850510480b424825038000b140360307041c5010010030351036200096950550b071248c207040104810b071800c4d042b44203004040040001a206004100172100003404400d880c8220901030b2090307080c1140d12080e9409595140307485d18902d14141c0c0c8440c4c903801d416902092290740c1140010320342c401142c15145a28072014050002c0c020a8214581d00005000c20034654 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 328876978 1250 328875728 328875749
    0x304020102030f070816121103090a090b0105070605010f090b031902060d02090409050a030e010504060f0f090816090b06040617060f0604062d170c04090207050115 72
    0x40000607600001210b00c41e070039040480d40c03150201c1c41c00703151512a410200d04a84102250740c410010032103070030a01c0e00340f941c0b102c401c2c02c0c200440c190394074003440c00701740c0d8854842d071420070500c00d4603404185401c4044c94140c0c50401c4030f4131142c0503a8001c3e8010180b0714136084041090a0083c4554005200c3c00c40107440003190036040b45a90754241400a44240000507889070110007940c101c42c400000a002440102e2260401d04d8490600206c250003041d200c2e15810101d40c40384c41100c00341c80b80c80d19400b0304866800e000f11040030000340940284210f411011038482820403840c201c6401002a8540e504e041081080c15500010a45401900180300a0107410b8010020114080f11045504416540c000004100005090707034180c008100050200d010356120f100c1c442d00c4a840031400c3e4002070244d000354a44129102d002002603480e81030058440c40c42d00195810540850740c260501d81c0720078885007241d1000704200c4440e0355810842e408560180640001403000300070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 328878228 1250 328876978 328876981
    0x9010501050f0d0b0a080a0f0606090209030604030f210515030718050c070b0c130e0c180f0a120510020c07170102120103030329010219031b030f0807030203 69
    0x1082c460051001c4070030001d031101018074442c2c50325000c0308010004141100e50a03103d0f410192400d040c000d10540d0142e04084002ca9100c0840c001c0743c1d1060070190062070140d641e502c01700c4418240030090810018418032810400c1e02645805010007420440040d190901d2285400030546501c1424000e0304001d00400803018429083c2d0701280c20030300003040e81d640b6150810354600c290b080042c04030036000144080b11030b94a0207401010701d900c28600c2ca490310f8501d00c14682c44222030200d0604410081205c02c81101d40c000d81c990f1070050603102c084005680028418200e80e00300b6040a00000e6039030050020801c0703d440d80000c4004218039103c89444e001d501d50700d040c003420715850a10850407104290941c11034220310074a12521109584030300d80280502aa505608441140c101003814900c0752403d0f040100d51058005050104a80c0503800d4081c80b40d4000360301b4805075061800d100c00101144583c00c600c20381d0740c401e0221030820040c7c802d082c0541b601c0c041510600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 328879478 1250 328878228 328878247
    0x60e0a0c0e03150a1e1a090109060f05040207021201111c0e0a0f0203070801060e0a060e0915060a09020313030908150f1008010c030c0905030a020105030a090816110901050105 77
    0xc0f10180c00070010301011800c280c4004080c4402d2040350020030302d851800c10224544a44104403101e0030350308840307441c06030b41e0b100e900009803030f020301451004842c610b03020005464554001c000562001e80710080c407800480a440c01c503285a1b80e60b0545510008014000088a0150701440420100c081107500611480c0f10b0755207444070002000d450580110500395039040004400038003404d002444095102c07000e200402a060316407425a505000c1c1c08103078002c0ca5084c091080001c1c0c0003d04840c0c17004160b0749030344c10020301001c1d00940d6851001c10f540c00d560004520444c48041e4000d0585070902e8006c20001c030b258030a199541240c00e01141414411070780d5500013101c0752120501ea221072080704036480c4581c1c40b11b0519807030403070b12240c902c2e050b4119a0320800640ca4886146580c1d07400e050304d642c0ca003c0d000380040d03010400075801c5a0079901441c0403500078180c2c030381030a5540ca214100701036903030001d8807000018000c0035501c1c6803d003d0140500020b29040e401d144040d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 328880728 1250 328879478 328879513
    0x3100b0c01050f180a02101110090c2304090303290a151b0302010f05130606080c01200a060c0c0b090d0804020f01180b04080606030706020706050d060e0a0c0e03 71
    0x500911035520940388200f5544518446a49881130405a690080c51278094100410a54408484039044280001f400507110071440c909510805203000c02010b4002c1084006d0001c1e02d021000c3c903a5900c1000c0180c1d015414403a503948140ca1238200109040040040304042d40d80704030980b90341e000e801240154002041542c858164480151240e800d140581c0500450200d460100c0e15080803c4041501c1c0d80741543c0740c0d0b014483c20040651070301c4846071690400c0c204280850500c151501684034001c52030b1143c029070703805070340c2031481c10b9649a056445861101c00020a406040e0b0705008090761580e030086880b80080c1205148000c02402003100280044d100320000f030700004180e4000c0380d10031060561750882000c081e40b0ba5081c1c5000ba00035029000c0e00d0700c15040019110b040c0001c5c4041561b00a4000b004054030301042215203502c480c160a5a85845102c00280c007401d404000c1d00984544401040154507107100070070351000088218480c2c0e01c03503030441c41d2030881c0c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 328881978 1250 328880728 328880743
    0x30f02041410090e04150513020f06070203070f12020117101701150608070e01020a11040504240902121912020c0d06020909010503060f010b03100b0c01050f18 70
    0x10b550441c0c140542e1041a40e101405500540380407514000b0041080700c60351041c50340d50113001c002c105d240c484000824140c0c0d0707400c00081d081421011a40c40380d240c48409040000e20040403160b00540f10800700c140d5841e40c2d8000343e62041600030701c074119a008100c203828150940480060b9107031800d030001c1da101041c811192b103c001c610004814480a4002e44078614440c005504844e9039045c0c0100101d074200e441000007074605041c0915136202140c4401c5043d00183d6100e045200c0f407003000014640a8400c4502c2055071501404150703e91124242c030b0b0503120310005072001c1da03005003c201c0f051910103580c2a003110824040200d4141c1c580d003605500000f4480040e60202420703880d0840400420354001e001605060030031490b6002400c060368140d80c00e42c3c0603641c480500d03660b02c0301910b6484070070f018440140500000d850155a0081d506500c1c088030a90365281d50215a018401062642e510741d020854a180b8032091b0540080d2801e28410f441d071243c8442584a0300d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 328883228 1250 328881978 328882019
    0xc030601030209040612050c010e1009090e03040f0b0909010f05100c020f0d080304050111030712022505010c0315081207050705120d080106050906041e030510020a030f0204 76
    0x5010580754a5a04c441e407111010b844c007440c0f8186628400e0500d5640e603240e5140d55070009280a000030b160b0f0820442010300c00210f5215103103070311b003080b00b2075010709002144540140f1042c000001d800005201e05402454078840c041d5941840c10103000040005030014020010440342c1001561a03407580781031041d04a103810303a0940640d09c00a8030030101c03061006c0d8484a0f1a80030800d02c0402d500440c041c17803003403008019070b86d0030320040d14490104441c10f03404601660b00d1070701000c0b1180c005110b4860741042c0c001092348400b4982c0d402070b201ea40252000d0703650f40d954040598042c8910250b0f411540042d8400d5458425029501d46e00078041d03825002e004074201042200801c000307030241c000281810320800500c02803a43e1540d03120b4a25001450220000480030700800403070340d40300d40151070540b030b0500b0714841600305a00c8280303490811403079540c0000800c006001a001c44044080050382c1d0301c81501c001010f60b00f070340c00c000603505e10402c8100560b1094540f0041000e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 328884478 1250 328883228 328883231
    0x30607050406030f051315090c08010c020708010c090e130204020403110906040501050a050111030d020714063303030705060c1809060a03030f09080d020c01121811030c030a0501090201170c03060103 87
    0x2072210240103423024a60051030440440008076800506420203043c15480c1c0c0e00b200c111640c0c03091104e0995540d024128041090544107202412100c0111a03000008440382c00705144d165000c20201d038041d60054404410316503c0388840e140c4100c103a50000001c030b60502c01541000c0001e00507040b075201c0e150600032000342900c40d0742818030503901d650b49612030445d19a04203041462600e18440c100030b515006010004680048c01280c800c405282e85240100517280c075800c000d14440349190065161105001c8100003481c20400544183c0c1307070040e4240c90300b0000ca5031412030b02618240610a580b42e008001660b16060036a400300c9400d031030302c09020003100900303494009030313038010869038003807458011840d50300064071001000c0c080c1e03500c02080000203c442d0465120040035441001c0c11400d407400300341c0d01d0200b141102002000e480c00c0300b0381400081d1078000200320855059442d0007401c010340d0b81004035404400d4103000400340c0761804080d50105440020042414503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 328885728 1250 328884478 328884503
    0x203060414010b070204061a221e051e060904050a18051c030b0f010c11040e071d0402031903020307080f03061002120a0302031302030607050406030f0513 68
    0x80d0380d55000444400030703044400d001561582905003842e40709840036409035080034800039052a4040003805001c5154540741d0608a078504e4400364110214842662446809400300d0403c4a07a001c0140805500398a151450301e03007024041c00c094060a07407013440f13205a05035440e98030307440c0c1100c1004600b142c000900c0e5031005445801801e07401004010821f80b02008010003030700107482c2e400040005240da81c540c0406000710192040305600f6504185030710304034203c42d40941c1400140c1d034410303c10081a0440f1101081c210f40c05044000c245a22081e4100003044810903107490a600c8049981e41c3c902d1f2a07008240e0300c4050b031480d04141201c054480c010b1620900c141e44120f5400444503566800c3d080c820203094105030390213849041c1e615241001d0b58000260500ca4191000105040180002c8150001d4100078404044030110516003c0140d406100141c400e00588e20380c1c50712075040180083c200c4d007451502201e01e41c0380209201c17144502c42d004280f1240e22442e200c450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 328886978 1250 328885728 328885741
    0x90402032112060a0609030605100506031006080603070308030f0c19080612060103230708070905010305071415071a16110303010f15090e09030a0e03030c0c040203 72
    0x24030030004000c01a0022100c1c1100060000e078000704081850400c0d400d1580e00c40004202003100c1c2072089401183d0507079030400002d41289c00166014000c1c0240003d1241d41d98007140640d4403c58451a140508c25030600600c1c0e0082845a00014160000d000813800e5640d00c0d4450312015040c0c20052040c4000a41441e5114049400b507c482a8104d8403252020402402003801640c9881c0f08010703420103050031190010b1081d04880e040145180104d030850b00d40400800042c0c82034a8501030203d0100b245581007154000600d225030000540e9071450900608151154029104008280703142c100b03599191400084c1d08030500204070f5681002c0d01c0c10039265070300f0303c1a01c403824221408002c0360290140c00071900724102d841d203034030780c220070b102294581c44240170f0b0118080c0c07400d07814010f52490704200040b030152424000d0240761940144a86800200c465286075800052841ca101c1d6118400c8040760000f60019421f05007460901625101d003025200d00032640032002400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 328888228 1250 328886978 328886983
    0xa0e0906010311060403061812083309040f03030e0a03050706020a090e0f090d1103190e060f0331030e0f18010e16090b0a02071a070c0801020f0909040203 68
    0x203640c825000c1000001207041984807101c5003005823009c071441c3e41e080000310300400d10f5522810503540c504500c562401114101d03074040d8290081d0081d01c2e00d90510079a02c50110b41c1d80214029040c0050b90302d1103150080c191140c007543d907042a040034401100080c0c02c2400e4450300d59111801680b204640e40b0b0440700d80419600c0300c10181c1c81e58041c000043c0440e041d00d1301849000301520000b014084041e1100d0b0030781803200c4881d0748100580b048400200050300d40c1a196442c111014800c07e10000c2e90310341000c0210042c4600000600400e40540d54070301842c04003528045564075420001c03116180c000d161b0103001c0c0140000000050b64801004110091004114008000b00031440200c000401d0284154000100000c10340404002c0782e500340c5402c095890310381342d42c01d107010507131030b07400124601c01544151600030481d40c00c488d00460500c00e030500c4031070700c235404c2c2c0c01e12040400c3d0580c0007410310303481002009400200501142d0f210340c0141c0d2035802c9900d81e0304c0400d2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 328889478 1250 328888228 328888237
    0x4030e0402040311010806010305150402070606030b0c04090b0901032409020a1d13052d1507170c0307050a1106070801030c09050f041415150a0e090601031106 70
    0xe40c041d01c002004410410407040e0500c0c40d010a0740d821000e5990700005504a402c10744d03210800351000041d1000340d2501c0d0300141801807141202290300d0356a642c1c1d000c0c48a0013601c0c4440751640100c1c0034031141e1524810003a03d41c50480300d0a81c6940765445210f24840f014041d02c6940200c10320282441c44544c00c502d81c8151f01401d2809000d6885404141600687c0c181c660b00580e524080350104208282001c074144d000f801600504900404240c156039098130034030068111705598690407502801071255042c1c02185258880c940460010044041c80444200c0004800c007403101e01e20682099980c85525401c045642d044440350580b600c0c04807a0881c05244210010001500d03407003144141240d100d4582da51400341c0340d095000a45c1c41c1220f94600c0c0d50813200004000c20648040c03500120054415607a4665111b039801c18009421264900e024200d40307040521800c202c0714520040036608000e61403800c1c0280c0d16500e9090611015209440110160100f82e840c1c20485c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 328890728 1250 328889478 328889507
    0x3040302010e07061e030219030b2d041b020c040e0c06070c0603050c120403200303040b0103030f030e0606090405011e0e0d09080624030a03030b1311040b030403 71
    0x1102c00c1e0ba59082c000b0400110a00c4580481e005c2e1110b00075224081e000341c904a54910081c50b0b6560301860f000c40081442000d610382c00b84502c2c0a405110790290350711070304590030354840c0000c00d040c00b09000c16613450806800c03d501c6504410300085901180001c0010803c403404540b00d40003a094a10301036009002c541e2220001034060100107031060414101d47d50b07610140702079516420002031501807034000840d80615074001500083c81042e00004144078002e00c003600c1048040d95916540084500303d0b940340c503040040c424160000885044280c01e45010302c41c401d80481426200c1401618080c080d035007036804103041290139040415140e48030010058925201001c2c540a8041500074034002e02894454258481c030440c05402034910980050080e6101c1c854003800c110b188840c02c01c0840c0c1c05032840c2d6a1503405202e8010342c0d5000355000310b050134600080080040e009100d0421440c54905070030008440d10b0305480803200b541380183c0d100c0d039030350070b060326003070700901c0360 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 328891978 1250 328890728 328890733
    0x1204140f06041809050c06032505040b07060c03050f13110301020705060f0106122c0a050118020f040905070e0a02131214070602060105120a06090605010e0a021c0203040302010e 78
    0x103083c80920070780c1c014400280103008881d09070001e001800924442640c0c01050519105168070102403441000d102214440ca0030f640303000d5440e8074985182c2c001d4501181c0d542c0d02c03140b0b902d5a16a0601032a5000460b6010b10074107402c11b9002c040a0701025980103001c0f4001d00103100c4217503029415904800c0d000001c0c0c82c41450120912011040309018450201d4060ba45643d110801f0344034205051111444852032070040b051482000408942540350310b114042c10140090028001c1c0f10030040d12460244004030741c4d104204c920110740241d00d006a250802000c003080c00018600c0c05c44039502610181a116061541e0103440303040305580e4944c026420002e41e800b000c0e801e076116140281c441d0010380c100400380d103841c3e1301c41e44503801c0144d20290040c8180d181c11040703600465508c1e82214505401075646605a40c1c4010b401d5501a0703980004000c1c118107000520b520811840342103281002240301c000c5000c22001d00798030556400b00010381054000d40c031100c06004031108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 328893228 1250 328891978 328892009
    0x30405280f1701020f030403110a1406070f031512030903080301060c02041103090607050a0c05011a040c021207060b06040b0d09020406060c050705060705030f0d06081204140f0604 79
    0x400304070580315840b841d454180600001c1186503010b00c256010b0258a40180c0c0c91620389840446000d5450a0881418003681c0490307000a2400c0c10150307481c1c1604400b400b0189800f0801900b2492550000780915040a18070400034117801c4000c0207075500c40340a140f4008a60500b25a10390309500010320380c0c0300000000c0b50700350b00320340031003040e601c2110188858040205040341c9400191008081a80074001180d03649026202400f141c0c1c07414a800301070130030346481e41c6080d9645403c2400d1181c106024020290420307010310003540700240000c00d61440c01d10714024961203090380c0504115a40c0e070b000d6100303548d40300494000744502c010b12074486480d100d001e00144400b40049204034504600004c3e82e42c001c400d080704094018011f860325600d82024010340358040542100c5a00007001081c00081b8480003404101003c500c00081450800741e10528051140d494144106420f00080041071340307981410000b140160352240d410019500460400e000710742182c800b1035070811 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 328894478 1250 328893228 328893239
    0xc170903070e0f0105060909070309030315090614030a0305180d0c062c010507030305190504050f0f120d0c1e050c0c0a260f07171e03040528 62
    0x2248140120043e81c2c01c641c580e41d0710010003030740d4410508400d0700800030b14000349420303010b0ba0000f038060b4042d08000c04c591070303100c140c03100d00c80158100348601030b41d41d0b0050200701da0301c400903048200c00b507004201c03070601c60b100900356000e4103801c4e29980d10042c0348681c160300d40340822042541e02141c0c42c030506441c0c2101405c10f0440d9910111040c40c400d00e44c405076400d0180f421b00101040c0c544900e00104c41e20f007140545070040041c07186a20703011411090700058441e1510440c0101c0241540c02502803004c0d0070914406040500c6900081401e0039420502e000c880030516008000a02e807000c0031800c0c0c90341007901c1a800740007a101002d51100c0b941040003040d4054000d0103480341c804180c81080401d0780c13140180d00030245d600c501012001a842c5045c85000d400604460303022050810781c528101c840c2c0c1001c071445456480c1401d118400308141380058001040540311600d290041da566030095204240c442c0b00803851006540e6a20340900980d0a1481c0c03da03034203192100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 328895728 1250 328894478 328894499
    0xb0106030204091b090504150302060a08070f02010b03190302010912030c090512030a0503060a0f0305100606080f1b041a0405030d02190807060e0d03050f0601020a030c17090307 78
    0x2403081c0f01402e81072144004541c01001c41411003040300d52550042113090106200080030200120724403442d0b803000c044050380e03c041c0582030303400710382c0d40741d085900c0c02d01c00c014449042c801d440410340e0305140006149940c04a20090303d40280b003c00e01c0054950706040340505000503002d03150800c61030f0745403071055150300070200034001e50f107480070304983e030f102806030702a90170450f000a0780080c4082485148140021500844000c3c055010607171140780119258115500c22111035110001280750041ca41c0a4040101090b0520005074a00341001540c000750040c10000145503010001e100c56561000f0744000d8502e180481400a03940d0030460140d07031240c003400d8483e00c103402c1c1004031343e0b100040186d011801d0a070700019400c1c035030340d404015401400d42115019155400c08001500400042040c1000b0365000300301b80c144420120801034001c0c10f540e045410908151011035040071000a116a1201c0001c8880440101c00081402006205035050040903c00966103205 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 328896978 1250 328895728 328895737
    0x1305040506010e070507080d02070804081014010b0f030414100c02161a0f09010507080d0506040b060a020c010813020603010303050d0605030706120c030906020309010f11090d020d0503070b01060302 87
    0x11883c842c04079200d0850540b414000e05034020900d490400a807034020740c0030b402608030544900c084c182030076141c03801c07182401900c85200142a5980e401706088648400d10280100076801e2040d1a01d1f401c003010002c3d0b848002d001400b55030110080d01c0c1591010040d18900301c5402c0400c202408046c00001c0d1103c080c410301911203410044040ba404000300020107981103038000c3e2a2500700d0403145082113402c0030619a041c000700744200ba010132a03600050203081c0505200203041c4c0340c0342007004200d40212004500501c81405000c480b56000941ca100b05a003d0a001e50f0984c0c4207a0181c0140816078002500950044000810075800201030003040d40150000c1c002d5580311014140d5800c0d40d44611400204442030710403961401d6400741d01860164500440c1d401059180d160036a8401c0e1003862a6a6486008040200180c884c0c141c00c0a62007118510741400b80c0c001622494990034060f1060700c01201500030010200100c81000b1b6100a804600350395640010700250803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 328898228 1250 328896978 328896989
    0x1090320061306110c180a020d150501031505060901031116050303180a03051218010e100c050301141c410703140f010213050102070509010e010311130504050601 71
    0x4c03000c0b00c0d800d8104049420048188050400244104495140440200050044440c00b6400c00c99a00001c1590040765415400c0010b805844d503c1c0200050446404030042040d04061200a02c036558640701110f023652400d20f00400d5405182e07140c05424444c503d03911082e050000e240100300800407001d1840b407821000c20800c85c90b07422441c0303a1a1280302000038001901004030544d610000412281c1090307000300c1d2824011903421000c0d0071250320070140b15056100c5a6082034001040c025207081e2100703450000d01b0765140c180901917911403503000d1032241c818070503007200406460007500380180e080892042c3e094140c66071940b42648244104081c070805030780300e0081c400121020040c03c542c500c0101029403450f1509903881882d210810240d0040384c1882c01a20000d00140c02030305030a44580e00110305e820006482c0480399807000e0700030101c8200401c20f640308800824116500071005100580d80040040c401da201007814a500d94908400c0c0028004001100c2d0705840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 328899478 1250 328898228 328898237
    0x63105060408070f1a0901120b030f1c050c100b011b0f06060f050315040507050324010608010602100b030102040b071b0e0919170a08100906030201090320061306 71
    0x7078070385d02a045d10103280040726040c640c04019000301940705940380a10300c011881c0014010704507100290500d01080000c4615500100b2641e2550300522140d002c0100039052081c07800c1003c041f220384581d04070784a40e80d65503994107041c0c616400b134a280d401401d800c104c418000c0d109407800710340e0303544c640c0000e88980d80f5240c0f01003030202800f00560162140200108460f04808160300074851000303004131494000e0910006468508001643c1c0b00c494600401180000780c40e00b0380103010059200c07d0402050034010410b0a4000c43e9121a90140b442d001c10500e41e0030300480c0c068800e0f540206400a00002ca03501408244000d86400303081d111040b2411a0782d510410450b0002540d0311141a080141034030142c29214042d103d00500c1019804a00b98241a00d2003040e04081c0031040812440f030b040180c4e1111040300200a8110740404000c51403c1d90002804042280801807503100c20207100b68202e002c2d2403420403c010002c05444d519440030501c1034045119109480205 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 328900728 1250 328899478 328899509
    0x3120804050709062102040b0a080f1b150a02031903020c0d020604032a0203010c02010b10020f0318040e070f090c0509030606100c050303070c03080606310506040807 73
    0x41c10b05000c4c2d24203d5600100c54104443c00546400b020680e018007268060369405040e0f416484890581e00100040000380c4400340d5451100c0341400e9011400100b40d182c1a00c0070000c40c0d0718500000140c00c1a80d40180c1c0301c050601c0c0c103a10314803c50321350070a4000000400d454460b490740060410307042c10000e81d0100103201070240d90342c5070700340d50080100e00b101040134040304c1002c494003d804078640e040c042d800312540100b8211441d040c80320700140d449001c00e0006060211104080702c10600c01001c08920350800703142c80380243c0f5000e00a02c6816a013174005d96465130055101344000e85c05071005e0a943c0c0d03c0c00c8500340320602c16111210305180b03a81524500070406d8070b41c81803018015108a5a5031030401070f850b00c83d12002d4040c0005042440041507041014500c244100c1e00c861079845040d0038080c08064004100e84d210320320800000880c83c0c040907007840c20b40c00c141100c0c10080442c41ca8298100c40c15040150804000300d000a502c8900186403c2180c00d00040d03800302 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 328901978 1250 328900728 328900739
    0xf021002030c0d0f02030405060310140109080d1b0209070c03030609090c03060207031b08070b060d11010c02030309031209090a09020105180414011508090c0a031b031208040507 78
    0x1203001d484032994242d00302c4920000c10f140111114404440184140d916090b05c40000031840d41080d1140ea041313044d0440300303000c01d25403102c401703102d6042402c01030b040a14280e051036031f618055030603204001c0010101006060f04118a450241d4001d1008500d4a03050500421199420b1002e800090400e00b00040300d00301c6108518415410540380c0c80614119241e02d006544800030450411000c0d6000c44404012440080708940c4030380304180c2c0e90005400d00050450002c0c0030b81c1d1040c0d00c801d0304103000a00c44050441618004e0801d032899003000e000081c01c0d4081c200d241501802866015803000c0f070740310014400c1c14000c550400c1c05c1c2d140d08440728110fa0410400030f0102d1401c20502104580f4510000001030000308042a4180c451442c01c5c0700050070b0f803000414100349a050705c1d440340c01c105c0c4540d100760a82d0040001c641031000240300c001c0244400b40021210b05041c100264400d516000690381000d0f0750092125405401440207100720b6090b12203002e4048086803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 328903228 1250 328901978 328901983
    0xd0f0210080615030c040f18060609120210030b150a080f1614040302041406011b210e04020309150a05160509060913050109060e09060f1003050a0f021002 68
    0x7890001e4618000c2c6003c940896036140d0014003401e81125003031000113403400c69080c0700b50140800c005103083c9041034511100640300b254000405115950405000801c0140081c0050903011281725a84a030361004c190000c15410943c150411078024849640b035544000a20041e030710b990f03908526030b9841d00f281500c42c0041d54055131090360a6240515070380b02e400b034041d0810f40304050078035140c0d070703a8009400c0b59807140407405928101000c0085035a08104004c01296035043c403510702d500103941d4801004400058075110407078441020b401d80e8400c42440c00c1805002d08110354a00389900a20f954415403240c11400890203000503903c01807500036140140b19a409155401a084030259559042807890580016082c0080000e0707a881803038410068200c1240001c4550400181c3c00c15190a0380240d11446452400c2c8050003d0015540d6070140c590700c4a01c0343d94940706a0b18210388a141d0001c0d015100d11703000d401c144110003403040000d03842180c0c86144044607110598 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 328904478 1250 328903228 328903231
    0x130e030a0c061e0b0a0f1a2101030303150e07020a0308070e1909110c031801050d1b0816171509010303021014090c0907090801020c01020702040f02030c0d020c0106050d0f021008 78
    0x5410101800c082c1c510207c640c4064802d11300300c16003030742141006d500d40d4201c0c120709074002d80000e601c1d80120a40903001100410141542e4220001342d46003140000e592802214001002c200390600003030002c9106041400003104000d1001207603500002c400e20710064030380503c045040c80c2030105840700704c1b01c4084034548402e110145090220050000088000e40668035050140400502401103440d20915561034042c0034250380220803a4401001000001c040c00202445501e9203102d07541c0160000c404e40301d0590300c8000907521148802c500d030720142d0b905504400c00c400040101034021030340f8106003d1110301042060724007244111031003026140d503100c980241803500f40c207007020145164400032500b0440041036448804c1401c80c0c2c42880103402695002c1030500443c50280174010070717a00545001d5045082c41b000c522a5440352007200315500380e0024903000d0545080d0070000007000010528200d4910300d00388002013203800003080b44240f040029010400740100d1045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 328905728 1250 328904478 328904489
    0x6090209060f1309050712060207200d170f04060f0e06120403030906090c06030c0e04150e0901091b0302091312050a05070b09070302130e030a0c061e0b0a0f 69
    0x20b0041d944916902008104d4a0b0050302c96000740c3c940415284660a4842180c91040100594650103420074046a901c950b06041c403101c685810a283c03a80c40c07046c41c82c00541c00c503481e1082a031199000041c14450700388140c09200d0003280002d8402d82051700300d03104440d50303240c40c141c0026500401615105194001e0044402103000c0303008207110342e10441c05140318400010343c42d80c036a110310301010300d940c0c00400066107402011400c1d41d40040e400c0d0345901c0c01c1d1401c0c800ca084000c80400400c415000d80c26806000f000040c0c0c0780c0209410070520942c100807070300109480c040411300c54241a01090b40141c860401186001048000d2240201e40000c01340159481e41003040300c0c298090181074040020034404000400d00c0303402d5007800f55409000501c4c08614600c140000201076580c11203c0c0d0307280c1041d10305403840c0403017141c41600b6149440c0c00001c41d54608407000b040b01c07600e1814192982e46400c1c1448160364800100980200d030070404195484045020009030390146 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 328906978 1250 328905728 328905739
    0x3b0a050d020d030b2d0a0f18090b040605130b150103060506070b041e06050a06091409060126030a0e0102011a061e09120d091409070c0c080a06090209060f 68
    0x42c0a011210b0017100100b002c0f50765140400540940004103031a106030412800c280c4022000c0002080f0041c1080806501b01003e0100c21640c0d00c4451001c0030050028140c5074680c00050070003c28050a1107569130302440e0800c0504003201824081c1d0328218042340800d00d008070220f034515000003507820803503003d10110815501d60391080d0070f05e40c0104101d1091036904509a000940e24080c0c548240514800000c03c680703407442c0c0d40c2c00e68103120460f0400343c1c4006c0600664403c00b060050540d9200032000944c0c5031a0440c6c0c0c0c05c2800640300c14406400f020801001140c1c1c85601000d9542c0240e009102e8100b4000074003075100300344403000e54410700c01c000700e070301c3ca90300307200c0300440c4102d02c02e10305d8180b12061020840e00740d81c0d01c042c509aa041061400d5800c0c0d009100034002d0401c054510201160350404941d010700040c081c0424801e0402d050410004407000741e81c041c018400903959500003e1030500c018040741c0501b02d11030201840003c003079042504800040b801c0007000b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 328908228 1250 328906978 328906999
    0xb040219081e031905180121180b011706061e0f1207030305030a050f060d03080a0e070b1e090f061b01050f0412033b0a050d020d030b 59
    0xa26500c0312495000102190100b0b0160034180200e940444070020300c01e817119581c43c811040c6446100d405500124144589516099804c881d41e800a48850019220010f44510804c0b0400b0510102c4840100095038075070001c50b11403074440c403a07204e00410b001200c0380703912400c003013010b40820805e405a03200481c1407070b5040761a01c8580c0241c0110050b00c02c4900f0041064075a0400303100e81c0003a0b01080300001071141c1c10b22148038055200300018288259410b00760000b81c0030004002010707041008020125003407007020f5008611025040085580865031540f00440d503405ca01500d0079103240c480a0f888841811038100c998101004103201a01c9414004112240d00030120403603003524480700700040d6038030902c9105c0c01080c1010003907423649800d14242e441c100300d0903891410541041c1c00c080e140320354144044a0b1040e00300318160f03401a83d480c03c413109038181c50840060303c660505d040034000041604035080707009600b6960302c170040c0c1e14250261201d5081203a0814010034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 328909478 1250 328908228 328908253
    0x1c020f04050723070c03030e130c08040305030a0209100e040c081005150d06090902121b13020c06010b03070201060f0e01050105030403050c0d02150702070b0d0e070509040b04021908 80
    0x75052554070000224900b4140d1984417003521081c00d42049000c0380d0100e59414003407510341201584041441024000004140300040c036420000d4801400d101000c400314000300c540b80c05550410380003415584d80b0060306003000340800351941000e80254904281f020f8903e214068a0384035034208901426130030320b08030901c0351641c1c812a407214212400e10148016020728059500100f55202e00132070810b500380104250032410700702034100c60340030030450107080d4825205201d0502003113504807a02c00a10041101921510000c41c055000d80c400206100e44c0e100087c41c064002580200011500c50010120183d071700e00030505030740e41c1000108001d61003000150303401442454441c0c20403200d4090b00d840c01100004400140c0c001841a01d00b41d00c0074a1080c3e8800180d1001748031a900e0040d03410382c0c1384030f11195410042d884800301110b14001304003043c014000a003030030169250909060041030025102240f0a02e4805501c1c6001d01300100080e0070368451001a1181c0003141c0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 328910728 1250 328909478 328909517
    0x30c050603070302090618030c0405040506070f0216030c030b060303070201050f0a051201030819081018110a05040f080106061b050a14070e0901090825021c020f040507 74
    0x1000b103401c240c0c0030424080c1c0f40e22601c0245c00f041c03c00200703c02141c0c14800800d030400310b099464900403403500301004082400082d10640021040c1007403400302136981c008070f0418084105041a400030024008100701001294804881c002c00c090201c6465031000c154403481864406400030b1024041c81106903900720050021340014141207203004000c550415900300241e100f9a01e03c0341c041104010031041e19101d000410b003a140000c428585036080000d00000c0d4003d034548662841004111008a58068003202c0c000c180d0054841100a1008007142c0c03080c003529080d01000700b00060104814040c260a840003034a480ca074100200d0100341e5400281d403030650b1184100e206642c0400d0840b0340800502e409000903003002d504240003140c5c0d4200250900425070300d04410030003c42c0840c419078480b1826200c00d840e00020f01d4100100110066a010707500c0f080c004400944441500d120100c002d100317541c90002c0114540800044903030803107018010a044039480d0700c219201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 328911978 1250 328910728 328910731
    0x4110a050406082509050324180307061404170403020307052b0302011a011e05030720012702090406020307090801050c0a11030a021f09050d180f030c050603 69
    0x34070455140468980381e580340c0d031210a021140070401c1c034103046c456401c09202c2c004030300c800c01c281610400c0c0300026107060810000e041c9695412403626483d07480409108403581980c1242c0c040c000c05060708000503214205840403a8001c1c0708407080074054054809840840340c00401401d241c0d03281000f4070a4030241500240c205501c10a00119400d0003102c060070103034000c0d0300000b6075004020300091542000410303981804625003441c0b0762002e40c203014240400c03961901d1a202e4032403d40030b0b1172415045000030205800041c1c0c0d03d03007074141540100c04800084544055641064018480c1070f800c07410003a4200c03283d60006404240580c0046070444424a04020391581d42c0b20420f00f100e4058a800d0704a1100144400c41d4591213010001d5480804000d146055402e100103552040846180c10f03280c01103080709420106240e015112541c5c22206440500c900c6c10001403c00032000d04085007050403020101e0075154500131001503c0d0701212921442c2e00b41010441940c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 328913228 1250 328911978 328911991
    0x151608091914030c010920060d091118160e0108160212040308130918030c020a1d09061602100e010b0409050304091107120c0212031804110a05040608 66
    0x1540c5050a0b00c08000c2006010a00c03a07000001580000707458442c801110b02802a0081003206a0741c25240e6241821100d41307084c04400014480920b01e00a080130400b034178031548c05005003915a03034040381050018803500c00c440007411040c1c030300304080e80c040c0207940307040d4009142d240c0014110701d0009000410407810b40102e402504404035511026441600100d69580d00400c111a01e03804218104021300f1480780140035001034640d4031010b413200e007000501084503401900080d5110002d005014002d0f0703285103100303174135107500a007014542641c4a1240340b00700000101c00c249c00c0003500410b60341d241d0141000b0003803c50842d001c2c210241380389459550703a0017400100c0c1d46521070a85440c0c401c1c0061900d951900d14078004848800340c00d40c42d4501d04010040001d8066441d00c80941c00a082801c114000d50010481c01c460180c190700300d921000800005c542e0240440c4104e041085506224a040312881d102c7c1c20302480210700081101440207100c01d80c01001240c1d40f100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 328914478 1250 328913228 328913243
    0x13060c050a05010c1101140c0f130801060303030b01020c010f0e1005090d030f1103030103020d02060a030207050f010203010f05010c020a060e1f1205010506090901090e030c1516080919 81
    0x60071a1182c40c02c59003a0540180800c404000c2c00c40d0002c0c00303005400750480e074044100d0707041c03030500400f41c1c40c1d00c929000c6480c98100040d08845050614107840081d01010303000700b080c2900c9150103001421a8030080b80035100320050741c502c03907100d0000701d500c2030203030340d20f28034000c0c1c803001408180e03200740e0480010b10505001e030800946403000207120341406541c5005905601a030041c1031801d6001c4c0c222081e4204000500c050703140c550410040a5041d5462641d5140c020f0084000b801482c900a02c1e50040040c003510300c3c0b805401960607501d084d154955066907a000650308030980100083d0400b45165003000642c1c003450000782c04a44c054071000317007909036010b08408514107180b554081400c92740390003800c1700e080c46114090542601c1040ca42134013240003401190052150030306503512011000c1c004c100a10945100141750000c450103034840c03044600e5107500032200c1c0b10584070150031001010b072068500d50b000305003500240c580c6583c1e00449080b41c9180c41401c1e501c40c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 328915728 1250 328914478 328914493
    0x1302090d060b04020403051606031d060601050f090301090c03050c030f0c0609030106180f0501350102040b12160228020d02060c10060902041805060a080d09081213060c05 75
    0x10700238000606894030015402c0070080c10801d015044803400f000a1404045115614150001c0003c3c803d4020509090480e10303242c1140c0d0311103013403294807405c3c0e426508100e03911040081c0e00040d030f01500e200b4810b1341c0100c2e80d441c05043d940c200e00b040c0320040c2d603c026220358450901000034800d41c1030140c0049115510b46403039582c09880031141c1c2103400e54802d003000094006100e142d001d0800d4150300e640b0b20ba64600c40080c4022142c4000a10741c01c1d00c55455080d6a0940c104c0d0003d151043c0010340325155144260845070041310080c1d0a440180ca5146030b2510100780030000e8180004c581c00d00040841040c80ca40f8407001c03080b0707007100e8000b41e1880560740b1030b00900452602000180f601da02c1b5004c1c42e20980e800c991002d4010741c0180014003072150460030070300c20030104100001d5242d4481c4005411342d000741d40040d9460040720700004280354042140c40c2602da40e642140c43c5081500e40a0299108148030600d410114103401d0001610a03084076100600030b000300d4600303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 328916978 1250 328915728 328915733
    0x20712170a05180307030c03020405090c030d0201060f330311030a0c030c0806010203030c0c0304091103060a060c0f03080601050904060e150d0c0614271302090d060b04020403 77
    0x56001004403000b1a10101d2600c1e0301e00c0308202c0a8803540300a0300500f01d13036071071641ca200c8002c1450000a01c910749a900040f03030001c042141001980c0c000b0201d41444c1c10180f80030740284610301840c80203000041c000300301080c1741c0720003074200309202c0792200011003644c52000a1503100000082015103507859900c6c0061f0304009503000d060800c4000840020f102e9000e8120341c4074004a000b0f00401004000040e87c000c41501da2007203003200c003281d866a001050f81e0562007140c1101201c0c81c60060b0540345400c020010714841d03a0190740b600d2049803100703000d035030702d82e07020a0042007180302000c0e00300060f21411480340c0204040c1000340c1815290070010381595484c0d042034400c00c1c40141000248000e00c60348800b10300702515100440071654540c1d0f17922079194051031090240700c00841c0446200c4100f1244001d804801c4600c0c07000c0360f40601000740d030300140940d1240c1e98074164440403041d14401c503183c40e071005100d04042402607a0700406011f040b40042c0e40541c0c2800000003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 328918228 1250 328916978 328917023
    0xa03150b040b1908040209060f0d0c0312090e100902090103140a0b010207091e05070e0312030603060a02120402090a0f0f0203041202060106020a080d060b0a02030c0f0c01020712 78
    0x79015188002d030b00c030500946940d020100c03c030360306400c00404100b48009038507086601034100758142c40440c1103140c800c021a40601d04000c0040c03071801c107080008140022038030f8041407101c04c0c1e0386000540317607152001c3c0400f29043e02c4d00780340c12035110400c106654107070f030007030943e0001070402203101843d80013070050f1100d04540302d5000359140c002d58200d80d0703818454800178103190070081141c103190420704000c1c0c200418010407069030b1640071682c15800764014403c2224010304a40c04203059528030046070300107880081c001d1140381c0c0480e85009060003518010003424007800d40503a20350302001448180134000d91511030f82c6020026900c1550b00441d2800e090008002d40c0c3d038245860407000101b941c500800840d0020780045c172226030b010840310a46a000042d0b980c0741c10348071001c01c000f848203a0180d20b101900042e1011000c2d000302c041c28202d2020f030191004240700780c00050701c07280524240d60058000d45028080ba01d08140c07a401600c5c000c1d00b9070782c40d44421410840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 328919478 1250 328918228 328918237
    0x10020304080a03140c160203010603080f07061107200109090c0e1815060c16030c05010f030903020c1c050303130c080703030f05220308040f0f0b0a03150b 68
    0x701e4000d0002220107026406014119040202e000400c40518200d4035448043c01107401d14a07455070b440701c0b244195502500b000028640001c03d40b0365940359454105401e500030782c0e040f2603403030603c2c0c0c0128164600c40181c4d0b60154004614840261110000465840d082c24500e03061042d203080204509100780b0443c1005606902c0c0d8a01c00340c0c00d074081000100d80c5200c2c2840c0c07000c01d081081580040320304140112401620380c0c43d00c4000340c94009051a01043c014280c100d031100001090000d086910307821130300c0c03e0721340b121325a107030090071420790300c0911700900582e1207002c5010710789c28194221a40d240540343e0035107803050075035a901c2c2598803d542e400d10304041c44d1820000d1000809520000344140340040c540b8511b5a500908020703424200c1c0b0003880408607611010540660710b0041110100c04c00e50340d403546034508900e064005005003000c075401e544e400f05041c501c003a08076041e03622002543d0b081ca40701d044100d003e003403031264011a901c184800090303070641030000342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 328920728 1250 328919478 328919483
    0x1050307030f1401090f0e06040807060e070b030c030609090c09041106040f0f0e1006140f0903030d0e0f01090f0b07112e050c09090a06050a23010206091005040510020304 75
    0xb0916400090038501540d036584c0c181f100c1e5422440510001038140c44c200e40584e0392114003c00d20010360303252981801065401030300760040c0003040101692081d0010342c41031030b01702c90154180c1ca03641d648035942d03844449400d800c21007800102c0c2c04988258074510141000800c4d42d0710340750321444500e5200f18203620210301580921824482101c46120065002800d41c1030364407900d00d040c800501d0849900f00c824482c407000201000303812950b00c1181c007502006400c5a81d211104080c000003403c10421241c164000c204403a103501c3c0041c041e400c01c01d40c2040d20006c42902c19102e5100340a0064054400d010003011400d8600205001ca9100d007000071400810084514031900719400805210550007803810040003016001c4005407035100b5416940300e0010b80c4c455100c20014503094001541c00b4600080011300d08041c03544a18080d07110001000c42e00c00c0303c1c001a070361201c0a80c0c00c42c070346811800c0000c503900c1503a8003459001e8003c10841c0c0c2d1148845110004a90003a5010b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 328921978 1250 328920728 328920731
    0x1210050d0c1a090a060e0303040b0f09014a0d050d270e0406060308030a06141207120c120c030b0708010b0307030c033905040501050307030f140109 65
    0x4110554100b1410035414490b40b501c0ca203051201400500c0041d07181c0035101c02e10414102c1402d56071810025030340903240c03a058856440015884900c0182c01040d2002c1c0024140340540708035803440c0c0039842c2d034075050102e0125203107681040c1c80c540001030740c02c0d4010000819040742503681c0b2224090711081c080c03c00303054400c1780140024001004040d40d9000c003400142c0c41e0100b640c003030b20104111142d60611190603201c07440e1000261090382d0000d45485404814402c91403102d60080b003c840092202001140088007444004405040d9919464000303240802c044d40300703aa00700080341d00c60160003003801d454036041002c1075244503081d140d200712034400f40100103400d402c00703401884504101080390302d01800b0001c944030041100d4101030724bc08500e050702d4001d40086030404103034040381d00c41030141040309520034480e1148c0c00803180d26418110300907015404480545006945161840d990b11100360040c0c101885801c0300b1503074580070316482e00d1000300013601801ca45a070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 328923228 1250 328921978 328922003
    0x5010c15050a2702090714130b030604151a0703181401030c23090607050712050d05070302061506210402030606030c01021f021c0c231210050d 63
    0xa00c10f224001d240f101c08407a030310401c03c1002690720308140c0c503400162481c0002e210115102c19900c0307801045210100807540b150046551903225019502c036106c20344040010201410400016941610038285480d138402c174520842803901f002014424042c1c02c200d804807644104a10844003580e04c40f50404400d424654119a0f06000e200210407144c0703130080c1c959020040362580c1d114200303000700041c2800903d112072502d504041d00d545503040700a60300725079030ba04e4504000d06694501200c5c1d500814038442d110a0050741038039415909940140410764401c6065640c000100306581e074000d00502851900c0005000801da0349a5400d01c0c0000a0030507206140c5441d101804980c869084140d8220069900045054860310007540c0451a20203004864009110b103812007030a84050321a03004040c046500542c521140c60b45d600d120800304450426420020a403080c03060311801c00008416007501128240c003d01c00f14244082c1641d15000228160404202140c0e000365601 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 328924478 1250 328923228 328923251
    0x604090b130501030209070f0315230105070804140402070b0703020702090c030112081303050a0c0e0714030106050a1422080a0201080412030b03030a120e010b0a05010c15050a 77
    0x340003214a1080072824850742d41198001002a00f000b0020010803c4103080680803611a4109214011000c2000000350391074100700420b1504c82e15103a400740b505103004242c40c0d40702c0c50417a2000d64011505500785411310b83c5c00e04280240e4410350350700c075801740851008900320070340041c02410551401039607244030b4418480704150081400604510600041107140d02b15601500c801c0c1d848421199100e407600c0c005850120700707400250683c400d10b0180700070060011642e501303566281c002031000796518881183c00407021640d1600342035040c0b00401c07502d402400076001403552030401003404082d040d81a43d49400041c00c0132904a4590503d1141d82d406c844404050103410001d003450b000030340c001074008030010304000c00402c1c141000910a5109511404d8915001000c5e01d0365829110030040407a2840344002400500c0d2003400c2c09003070814410343c10101d80180c004010300e0308e0b040056520b58011401580c10003000e9003003031840384c4188103251284c00b0092002503c1c1c102c90 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328925728 1250 328924478 328924489
    0x7050f04140f0a0b1e0d0906020304021e0109270e03030115140304020d050a05060a02070b0708040c090507030b0a15030b011d04271208060105040e0c13050604090b 72
    0x2d08405001c0c01401c0410300418412400700c0350b03414105400c542c070124500075409410300c200c0456042c0540f03410300040801c1204e40044d400b49008440c0c10483c0c0d24011244088144030700082800314800b4002081401c00071160404202c00780e224000003808845012416585080103190083d08008014452011001c060082150b201e00d070802c4460b82420214100b480060401391180d00407820142c1081010071055060541c02404d44a040c10441130300e40c040d412485044481d00d00140016028500c40c2805c92f2040e90001102e0101500c0c00c401200140b41c050405004c0603152100c00c00f0701d456100701c860041485155500c0d030740d100c1c03000090440b40c02e001031074100704841c80803000e10b0705032080250710b5003400c8a0012706100c110294003450000e48008010802400d40e240c0203018010103512350342030080c3ca4114456036000011201403185000c3c0400310082c40d0007203014a600500a0940b8045000744100201e8503000041e04c25000750788903000294135891042d5060400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 328926978 1250 328925728 328925749
    0x5150d0c1809022d0c070b040906050924030c0a0605030901060905060108010b09030a0606061706300f07030b0a0e0a0f021c020a1401020f0c0a0e07050f0414 69
    0x1004011402c18114860804003051030418071001c50f9100c0120034104c000203011200c5a62606007151841e0344c0d42d081d00700c015006441000021031900c600007400d4282000303100d02c41d01000b1110901c0d0140310702c80300803600302c0030301607505445210302194031502d5041c00790010f030416403a80ca4032440c100300303011b007983c0c8160015082142050148000760340c0007039940d070540e051100745503102d0003400301103854401813210151100b420214000303070250304a07a00c0c11080e01c5902e00c4043e90740e00c280900815000900040719141c81505004500480700c48410701c1907222041034a080000c56119a464505203070010b65001014000b4000d900b90707184141129080c0c01da0240c10170151584031066250020480680142c5011040e001e000c0070104c0489103440d4020030001c0440d0312200520f45000241d0038650241c452692640d201034000108142d91900050081c01c0c05424501590070700b4030054070f040144401881313400b0115844e5405840a010000c14842080c01d2010802080c80d08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 328928228 1250 328926978 328926989
    0x1e0b0c04060c030c0501110d1a030a080406051303021f4d010e0f0d0804020d021c0807030f090506090306011e170105040215030f0105150d0c18 63
    0x10108400c01c211900314491481480c3c16040c9240b2400c100e090a60141c11408181240c3e403100040303581012285030b001c445583c4a0302011141200f640050680c7d90344a5039002d00068014801000742511902c01415030700216440c6000580d80c0760302080081ca04407d00b1602800c0c182010710101d0340c09040c550781039010a00120640d50140e10041640205050304512241d000700c6011072102116004080c4a420300000c000b03d681c01400280c85030300e641e18081c1c0a0040d90501d0308074070b02c03600b0b0150241e41c0060085152004503400c2001a03c24042429071132140c182c03a00011503002030140c0b400c140a42c4642800c048407580040c01c100d0383d908407601c60f0341e042c05104843d4400140c0035042d1510b0058041140302c00000000100800d5400000b1462490b050b131110701c4c2c41900001d0040d803081d54140c400104c01586038003c3e002c11200e20300e9001c0350100401003450314220740c240309200f40d6041443d00f03540d41c02070003d0b0344030402220003140c0248083c1c2190302900c05101f00819 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 328929478 1250 328928228 328928251
    0xb0309010b0d06052a07060f18050c1905010206010b07020a0b070f0c0b0c06072f01061509060c080a0309080c031306030e030d05041b150905011403160c1e0b 69
    0x5c0c1000007140500904801a0069a8a07240b0010b020f4482c0d1040d103600412140d204040e41ca5071070610395070038104075124000c41c101d54034058990a103d0381003060f01d02c141c01a0038660b08002d1034182c50380044206aa0200b2a01e01c006801a0300c0d01c0203100903801440b00402842090030003140084043e441050700c60010044c12010700004140c00e5005101d07440d04032412035410f41450604c0752a1903103507001100c2044000e035222030540c00304085800e08000a000151400d9040d61210101d124110120f01c0c403070745400c0055000307001403a135182141800110068142c45102c45500044040f40280d88005004401841c90015500040c40e992a080c050161030205a684a000d0500c40b450701c0c80d01d4001143c00c0000000180e00340800004048203503623550049140c400a5a850000c04a2801200408c030707944101300c06c0080c41c00700d14681d8510f403500a241980108c105200d4401c1002c45159440051011604501150006004890003140509004c40c2003507010b440460040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 328930728 1250 328929478 328929541
    0xd0e030309090109020d06090501120606050405071709030409020412050c1009051e100206010303080112020105030432010501050307090203040c0605030702150901090b06040e070b0309010b0d0605 86
    0xba66030ba15000e05603030300c40c6005a111110100a0b40240c1580e0f0401240709040070300104d1300704c565054810055000f010140062560340d0280001c442055400e1400101038101c8054074421988009820890101c21607280a0780c5101ca9800ca030029009200214401030b100d40c18000c040201c000100742c2110001c0f089400b04c00083c0c010b5043e0722803940214501038100040b200101c00e050410100980a0038500d410244001d446e400d0900007103001c540c6150001c140100c10031801240b660781030715150b180d521a03484040403420180032031a080f940403c16103103005054480000018400320010a040d410002003504000b840e8000c1c0314094410300400c40840c0c0b10703005107411a0400d00f4001d5070b81d10361140890800d041c402e82d05490b0003040382030101c40d100c1544280800d40c06a03e01d080d054645d40704210030781340040018074030742c0c0c405c0e1014403282506000a5810034101400041c0c0c16044c0d2001c5040d1841ca504165441503039901080206080b0005501000c0404466003501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 328931978 1250 328930728 328930747
    0x309050a0e100611012409050c0406080c07021c1208061005090d2a0305011d0309120c0301090804080606010e150a0c0f050307060b0420030a02070c080d0e0303 70
    0x40b00d901d4400c0000f00105842d01d503103000780a44c411610280d1361110386070780e00481c068090750030885109005541d440c080004144030400070565003503903e00e070b4650b01d56440701c140000440e0030010301a81d00650200c2e00368501002c100c0001e410a10400da000c284140c40d01000d42002c000a02c901d000e40441180340300110390040484016140448494000d01c81d242001010b030350240c0c2d101000040d60011020310302011240d41c5046902c684000c0c00080c1c40c000c400401554030302d80303002042d842481142100d190000b14401d4482c1c0f02d00860740307084140070019094811181013618448400201846040c0c01404110ba01540a08201400100c0c41c0081440c070a9150032140e00e920002c031303962003442e201d05062054140c00205608044440e402c100f40c81c0c0e0b00010085425070f01d40100c0f9101400c29005084e009407111501c0c4201949008016026900040c9140043e980c208080c00c0000c42e01140d04014144030700090588450315000038101501c00c0011520035407003030110401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 328933228 1250 328931978 328932001
    0x30c010e03120c030f03070c050705040213031101020a06020d02090117041a10080d08011508060f040b19061824110c04050705031509130206071505040309050a0e 71
    0x201c5801c2038a00f5503a010480d030345030660041205e80002e803103000050110a560160806289034011400d6600f19545d540401040303216840700c0701e03160740200c807040004c683c1c2e0110346400c100041c0165900326640f070760b0304004c0380d01c002000412164003181c80490780d68400701202111300306078104003640c02c003602e905090702d0880342c0c020b1b0f07a0500b040000745d0340703030325400c24034003d0074a50200e40740e00440c1c0354080e004c18024000c001e002115601141d42a03481600407901504010309904c588801e0348040c48042d0004405103a00040064000030300403807542040c8c0002d0070340d5038803445208003408070420105550781c4010380c9d680000c0302c03c4004075030182110f591003c0a081013902200070080d02e80c00c083c900f15510b58007078038190130800066004801188075003480e032820340d406001e44081000170003054886042061100b5508030041c04d042d0014110030340600118070040c04000100ea042e100c0450b0101c000440d81102003020b07040c414182006068604a54030303282c505000b9044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 328934478 1250 328933228 328933243
    0x12030c030601110303090706030f09200301020906040e07030b0d1a060a05030105040309080f0a030206040b1305160612060e060d020118080a0515100306090c090614030c010e03 77
    0x6200000400d5030742c0c0c018461600040e0442d419203499207401ea40342c50304c46135036104010101e800c0c03044c1110450314510400c03c40c07a07400410311001c1031101c0c100c2e451801405010540540d401c018110107a0740b543e014100a01250480c0c0899240c040e02c002c06417a0a09180e81c0656034420043c1c0000d240c10b004031240c00c800460080045e50742400081011a03294480303a00741d442c3c8030900041c5540410034400303858502044825201140c00304035a42c291842020700160040004034000801080443d5000f5881c05c0005e110aa12911054141249108070040381e20003040d04026041d0004032110020410440c100301e101c1c03070400e01d00840440106424800c50044d00304401b1a030103450540341a4010000842e601622000240d554078208581603495104140483c11300c070400b031002c0343c4600300c000c2620315418555602c0201802054108031f8410013080030200b40c120700e62107000002d11480704910140d8803a1814503051640182c54103040103034144500407152800a03001c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 328935728 1250 328934478 328934491
    0x10308040e04020d060c0c03020106050f1302030a200301060e0109050d020904050a080d06051503091e101b121413110d0c061701180e03130b19021203 66
    0x14452965140300045015134807440041c0540c1c0307000c40300201694004445800d1510a070005c00c510341d03c44041001030f01000c000c0c41d07030107006030781514100c807400c0d0041c3d40c22496440010800c0d420014070410200ba002007903540d800d00201c010031030b035540841d18001c481020f00b8011482810100490313140220003078041c0c018140040803c0400104025a02d980e5030407004141d110818080b202025104500c50f05100c0c0c002a802c5080f2004980201c074014002789000b44035424010440b07460340d1445410300c40c05070082100e4101307500c0542c00707003100104185075505141011000043c100b25103080c5020b00452400c2c40d2030100604130600307190090562031084055146038680701c0c0c0c42d14100740e621070300200610741385000c0040020910301500c010340c031220080340a0644104c5850710074400e0311741406040301d0030280c10902750301c84900c1c5000c02d81900d00d07045104c110303e48005400d40c8801661030300000c00d4103074513689696641400250b0300c083c0c150801400c80100d150300025140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 328936978 1250 328935728 328935749
    0x7080702120307170d0b0405090606011b08070804060f1d1504080708060105010e1f080703090605100503070f030c0b0c071a03100e070c0b091207150f0501030804 71
    0x745524004100140c81040303500c12200764078803121030480045900158100d03013040d4145503903003c651406014441c42070756000300800f900e6480000440e00364000c1700c0d41d01c0e440304100010340003180c011001070245600800401c0d07521460030388001c0090428000020400c05070300302e220000d42030740f000c0e540c8101c2c0807550010001d40b8181140d600d40f240b17a2204040388144000090072180c0490418101c880980712407441404440c144007400f024502c5042d100c1080c11502120706000d40212908003440349030000303081d003455651008031102a50340409140c01c8002c1080949000c02c0220b0150043c48a4442107030320b0365596054001d00ca0142c940d41180c00329454030142d40c100081001030241d01d600c21025507000c0318601d40c543c02503904410101038800085140044031381e1090082006950b6510f5403070082e121801040310207420300c2020b000e0405034540c0100402e0140a0003801120761902101c101c24640d4100c03100203040714a40ca041800400c00318800703005440484081040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 328938228 1250 328936978 328936999
    0x50417190f12020703030614090f01030b04030e060408010912020d0f080c09090c031b04060f05070212011a180f0105060703050d050106090e090105040b060f040612050f070b07080702 80
    0x1d07240c40a81c10701c852549440440c0204c00d16500d50000c03c06c842142141901044200041c800c00050449040078070089035001000010107034801507510278001e01e44110900c035440e0001c0c2e9682d1082d03000d6950b0b40e440704032000622540713079500011841d50740028008400414000b600c0141c0d40c0e20f541080c00b0810002840c0604007608035002103400030106106441d0001749050785400a50751001d03501c071245d00c3c0014242d43c0c1c000721420b491554643c3c640100800314111741d981e01885003260844840c1c2038a0b000a202401400100c41349480b021100103070b24400c0c40101502030b0340e402c61030440003040c01000e03184400d045040d55003d41d500c5944100300d003403d07281e5201d4540b01082162528000141040e4000d5405060703903d81c0700d92540ca5101d0070070302030a841040e0f8014240c9604480460100e140c2000b0b13030942520058000b1482c181d845020444501142e0000c1d44c0c603800c00008624044000d010000141c4822241c06003080740903181c0e4422405413500090140c490b050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 328939478 1250 328938228 328938257
    0x61f020a050607020105090d09050303030a1a030607080a0b01030b09130819091a091810030501110d0b031b0d06110a090f0503010b0105180a0e07020105041719 70
    0x40900325140c0c200c0200c50355401c1243c0028000c01d4201c8000c0010b000700c410140010344246040011503400400031825074179071440c0c2ca07004040300120801d0303030089010f42d03011644091011902c1070101d9103c0c020030345031501d550001d459a41140d1810180b60214000140c3e0390742d0203864011a0a44181503800851324148500c1d2250f908400fa6583d40110032465403075000d90b02c98155540d00034a001032509520703990080d8018148103950181c19500c11715945000608840d50205c151a6000805035498070b50310308461925031029500c25000601d010030840c580111b01180805600400c6181502c0c0c2034030000d00d48100e5036503c0b54030801d046d4410320603035821191003180c004038141da03100400c0101600501359071003080458081d0301c0d00040e4a02d8103108011034a40d0603104c1d02e180051000501c1d44060304c28007110382c044580c00012800d01001c40c0c0c1544602d400d078000084a0515040026044c02100d200d0004004104126580b01c106081d501c0c0c200400740c02c0c0341c90800c1d1a00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 328940728 1250 328939478 328939483
    0x324090b0f1f0c05151b1c1e0606080609090a02031506130c050a0206010b191107030f141603080a0e01020a1e060506060307020d05070503160b0a050f061f02 69
    0x18007400714400d01c2c04141e0314002d41c1c2e00413806418041c4420550800c544041086c40c000c1c807103005840028842032035030400c4c603900562407a5904508030402805007102603001c841b00e0341c00030400a04000100703d01410401401500705000c5001003104083c15800240c1d0b0b000ea0b64204254840d8083c0401c8060b21840302294040d28844802d10821121803030003807154008508810051041c10000948502d900044030710b04401803640040151200c00203841c5040380c001d42c110301d8810071000201148075501404c020340d09c1202e00740305440c051000146013050343c043ca0003141c40c04000820000d034a0710f0880300c0246060a101ca911640d460050b0309080d0302c03078400303030001802c00500d14080340840c00e9000c4d401c0c41802c08001d00d0f00e0340020301021b40400c4030740c0700242e0720154041044038064030240050314401c208a9181c00030140030711502102084003200c2881000c02400782500d0070303000c0c680e0b00038031004210040e460903000040c03402e803403020480c640110103200407844e02d10a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 328941978 1250 328940728 328940747
    0xc0c13020415030e0d03090512130915050a09020903060a05270c2704032a06021b2a120303090d030501080a031706010324090b0f1f 58
    0x1120b82041640d07035040b80070307016100c480308941c00e5014440407100101d000f4450003080d141c0000080255040c01174541d43c8640c0043d440101090103080c0020310300c0f02038000d18541e0380c00c40203000f032201d150800340023054103607400c0400b4140c0140320005544d28009045684800a09000b0800f9100c1c4001c5800349040303522001c0382d8003250204115a401d002a080d400c420050314458950341c0c801410140d00b44982140750305031081500404e0200340304400c500d00e80022146035510081d805501c10220741e20803401140e20715004561030701d4a6107503011841d00500b41a000c0c0081c1084171518041464a245802d1142d690340408582d168070355890007102400418102c2ea560f0034445502e564582e5403142a1000a003004004034400201140040c44654180c5400600794101800881d85160003407009041540c1d4410780031000c200030b20f0801162415403842100141852207900554240441141c02981c1290b180406501c8603985100e11600c440801c04c1c1c800c89849044803034011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 328943228 1250 328941978 328941989
    0xa1b020f0306070e0a0b090108061002010e0a05150708010602030913020c161401030e1c020c0a03080d0e07180b0a0302060f0406172205070503100e060a020c0c130204 73
    0x1041c0421807000d40040340c54410002c11595840c0d5240d980403038a0561080e1070615000a04110104500381010344074080242070354000880c62615207403da030f1403f00016070179102c944c401760304200150510b0700100d030000d80d5440c091001d50b0502c400650f0303a10604622b240180c030f1030411100f2541c1160f06942c800d09064040e13a0f81c181d12804001c686000300d0081500b800f106000180c00c560181c0700301c41c0b905124001a155020707101c51903002c090f03642e00710101940603050501c0d02c1d603034410145001852246190f59102e030301d40c0112a04480c0e807140742e4000c2d613002d540c052201d9001941c441e55039080c40c01012400d010024040b45580340b450f0f00081d000300e0003060350322a04081401030400d441590341d03403104d04550b580c690314051009907280e42c682c031034102051080c50ba50b401c0050205000340704448882e0303500c1d00400d20301b158000174000f286e41d444010000a6106000e4203408c05802c0500b0f500300f1403040251038882070911825480750008841c0301c0701e00d15080e01074800500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 328944478 1250 328943228 328943233
    0xa05071b02060c1f0c020f0a170c071203030203091005071b110909250302010507110f1009061b020a0905071214150d0b01031101020109080c071a0a1b020f03 69
    0x804104039002d00217108965015003d400180d800705200003840142c0c45401407201d1321450741140342a80e4581c8424823444550041950200303d014055050400d03061282e0b50040e96850250005800c00139058424440e0a08010500c81e025030b004040340c5804a0301c10300034004803241c1ca05070406a90602905800c64424810060070040c0455030422026400310043781c03112011400c91400710542c04000e011030424401c0c400440d44460f41c0405d010700242c030fa58420641000050082000c0c60140b01c0000c9481e002404610703407041c0c00091400d4540e41c2a800d011482d0700042d15611b080c0200d0750059aa80c00150003584580561506444c0062003005101d07100001074400c3c100840741d011511032010f00040710350500000590780c05400c505a200d05900311340c2c03001b04084082c2e10007030443d0b403124852004258050014549400300388000c1c64034a1030551040d95821700704010f50b100703000507c0300410080d0400504540307040d8004d08101d010600d8400a222600d80100440c2c052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 328945728 1250 328944478 328944523
    0x30b0402011713080a020a1403030403183002030604150609110d150e011205060610020a030305150a080a0b0109020a0c0b090a0b190501081b15040e07080a05071b02060c 74
    0x1c403009c0000e5002c1c1d8026510315046041d004d0812809138105e1156290100c3c1c580c0140f40c6ca20541401012021900382e5844245015500000d1919600391030650f403410071542e6800749001c3d180315150061541c0b40c410b0000312101c9500043c2c5025541c0e41892440d110011080841c599016600280020044007102ca584880003100b040ca803920b4222a24455100031519900d40021040344a0801d54001e00c1902c100303503801c401800f400b40060304081910200c0f103403950340c0c40e8113540203850103c00a140e0041142056410b54006070301c5141180c1c0b0400c20500042d512150003500c040c2c104103014110703202c025403580340040006001c2c04d040419020f12182c1d0031055240c82540055000a1145980320403001c1e0315040000d0817036881100c0e441d030800750f5051294003442207051860b581030506644a0b124010300b0f00882d11800016650001c10038040c1c0c9a20803103410a51a01c2d0400800501c0c2c0b000744211410000c02070701c50392002c07881c0404141c04100c289021403040c40840c40c5c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 328946978 1250 328945728 328945763
    0x90b032806051f05210f030c0111041202061308010914010518250b0a030605011d090703110d090b090f031206011413030b0402011713080a020a 63
    0x21040421030031502a810100415820800948080c981000c8589520102881c00007008038104101d101144855814114030003108800c1c4039030140890800091503550406408007421030300c801d04807da401c1d00900007400b9592a85040304001030b8113035031a590700c01d040c91040c0a2610300ea40702c0f600660030088040204418241d4079088419184001e10150b11021442e42c81308810242c6600d003507000d80d004004690725403441c8250054070750445212540c41d5031100c0c0eaa0361201c4840004070362207003820005541c1c41103042d181c90605859288060181d20000b8002c0c44000c0c044400300b6454202c091602c4080c8401c40e012566405802c2054036041d14103145c10440484103015140100c00348a100c4403c00f0041360640d008547d107401d66540ca0200651303103509070381c8110201e107009004c05c140d40d43c0d0380d0019034081d501881c11001140303058800107200150054110040326004030500a40041503800701d00b16591203d07046403220b13000c01c022031805812041c090070298200080c80340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 328948228 1250 328946978 328947043
    0x24050d0501140a1d0f180f03070506010803040303050706200d0e10150e04051501030506090610060807030519140402040b060406091421010213060e0307090b03 70
    0x21003490644841203c40d03520310040044104440d1800d50380c0415000081d00d4a128801c190350001c8115401c08604500b08001c610b05982c5a4031095035500000b540c800780801000b20900402d4004029442d05040d0740d0010024059504011b01032a01ca160341006014003450706c00b050b80b11000f07400d40f01d684c0101e41c8009032040300161400c90007415170748180c0c00702078000c002d007005c104048600304030314124001102c03042c010f0055a02c3d008003007d0094503a040c449007802513018100804190030550800c500303001d002303807203400c84021608040241d107030083c15450303002250741400581503450b01c41505041e1100908030600d6071030090b1043d10b41c28111046030069009460401c00c840c011401c0c03208911450240e400840c1403004104000c031944000c0d1001660040c0c804008165446070301d808241c1640f4045840e650085124042c03605048100b000826462402c070300301c071407000080b03501c1d4080f030700448100b19214000712995440400900e0410000c0c0e01c00c0d000311079100384d400103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 328949478 1250 328948228 328948259
    0x7090504050307020a060f09051507061401080c0609130f0b060c010905060c04082107020402040f1707150f110f07050a0806060901050108040203010b030d050a170124050d0501 77
    0x80c850301c288040410500e20407289406496455140c02d21102e04080402c03450518445141c0e2b8100b41c2004a540001e900d03018512094075100c0c0c03002d44a5041c0a202d0741040000c59100d03014640901c00121655141c1d03807000c0030100c0141d0002030b1003c5a485007006002d55031282c81d00181d000130000d20406056001d90b010b94003c4040da201c90f01d6003401000c10f80728902c1030010691206801e641c41c00301007031711080d510400c3c11409251101313650106041c0d030403a40c40f14584616104041288091420304289108842c0018040041c1007152070002c800f030f00782c50401040727a0b412000c08100e0040d010380e103898588501b2210f4002902c1c1c0c10b241c0e516078a0150740c0c00703800c000c40c0000741c0031000990380d0300980300180f1415541e07081c00011a14003a0040080e6072542d200e094049142c0c8050112001d40c88480d0b0758203555200d0b24030f0251000c0c41203200c01074181260340c0104940d4410108010716501040781c41c500d029084030044420740105940004900c0c0f40c0400004c02d0001038410781d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 328950728 1250 328949478 328949483
    0xa0203030402060c01091406100f050a050118030606140f06090a060f09090204030528050616141602010e01020d0e060d060b0a02070f060512060d060e07030506040b0105040b10030e07090504050307 86
    0x14401d1a00c4ae0007041c84558588070f15500403c80100500556000780380c080740d001001c1c041807200960ba07840d1402514120f51080000200d40c82828a25003400501d0010b9501e05440b914a40607103840880d0380303d02d01b0321820381004a0f0b90307a01002d40d4401c142545c0100110301081d51142d40341d0900d1a00d1b8280032070044039000a02d50000307110159030445072042c80e046805480c159450700803490401c9500c000c0d80b41000b0f16201c072038061240038005031480d480d511139003601d0314a0620014222280341c8103464150742c0315240301c443e160b50000804c0c031294000e42d0825250f0174807072006005084990406000503201242482e801076000400d08112a103074000c0d1201d440c0c1d03c40096949208100c266480101340100043c1030341002c80d05007600b140714060000b000d42c0b00360748460411140d50811111a0400d20030b01040c0880000b44c03901400e0200c8d800c00c50307154080300017070f488000c910049082c0340d100c40d045020010148203603030050202e100e05003c64601464929220f50002808 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 328951978 1250 328950728 328950751
    0x702070b1b06060901230418060b03010515100309050c10020a0b1003030801140d2424120c12030c03080a0c0905060715090305031b0a0203030402060c01091406 70
    0x5005251080501381202c21100c000210910a803e070640206c1d1510b146079002074840b03004c0080b2540e03407140d6000da07900544002030081040010142551405090000c144112003c8005655110040c450303600015041c0050409644e280c200e00707214440303400300e0744415600f24540c08035030007003100307000d2a11540380084903540c0e07441130140d240c9181c0030240008000100600c01c00b180a0843e00e881d02c001050884c282251365200e48024003e0044014240c22220200401044900410749009807074403030703640140030b442c1004240c03103080e00c200d01c40c83e20114a003506001c82c0d090424081c185152030322440c05a9070030040e21840001e4030490000b00f440c8005580e48401d441000d42c003004a640d00185140b9220400a50380c01007481a030311400c1070144598818003a101d125061417003502e460b80c503803420754800240485001010512041d08109130911103030702000f101c0d8401ea0440701aa22088000ea90b40c0c0189201003004026160b00d0304055a402c3d00041c01512030600d0001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 328953228 1250 328951978 328951981
    0xf03020d091a010f06020105072a02030106030503220e060f060d0e070312030924020c100501170a08030109050c0c0607030e010c0e010206040f0317040f110103020307050306090702070b1b06 83
    0x4900700c810881c1c08078001201c01104840e05512890460ac03001001c03074403c80e13810202d0300042c1c215110707940115650f178000948601d002090100500c0c7c000c0c140e601881949203000c044501e41c001c0102028499200000c0c46402513640d00c0a440b558000c07007904001814160000e55500e440074007081d42c0705a0300d2440c0c0c14125100c0d00684811607440340c28035400944071a00030080c403907040b0b4031000045d02802280c4401c042084200340e4603903864400310700c5500d80000200081c1d100709855555401200c03200020072a00c1c41260704550407650009002d549101482e4594000c007001844580070344000d020b05a50b1580140103415520b0b030082000e140400810342d000760a01e41d8240c050b0b00407500060108422500c00c00140e8004d0404280c42d5059005c4004484421541200c0c81038108151005000103406070b41c412610a003400c5280d070404510242c032500000303000901c135818443c00200402e10a2064030020f201c400c20150300e8807514030140074800a0480d80884500c039510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 328954478 1250 328953228 328953239
    0xb1b060c0403020607062d05011e03030f0e0f09010602030d0614010905011206080106060906080723070203120f18370509041419030f03020d091a010f 66
    0x508031401c0b41e500408075480c0c500c16a5422001c0c201c640440320710004030385094404c401d0302d1480000d4115600c180040c0e558100782c680070400e60048400c3d801e2034100c00b0300f84002030300300751500820551814040e01440c8a40c001a040c804142e4215402583e140f000041964000000d00601c8c0101d036030a000c40c0b80c403240c0c1700ba010b0f8403403e01c1c24001303544550f040000354091850358000300c80452000c108103072605009400d49160303601210000c0c05174007041200c0ca5014100580225017454502c0d14201111414480103a1107422120b101100003548411541c1c2001002842c038010700d0050303200c01d00100d0030003603a00500c1000e0100290800900d10a15119545800e41c54066540816000c0651034003440c2c1034070390501071035209502a012415558800d82c2c9442184100c420b902409d0001b40c019040072040303101c6101d081c01000198000941101e001216104240350040c0c40b00e47c1c00a0341c3c006428480006020900d580500500014034070300b5882c181c030300746c0042c0d4684658030ba = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 328955728 1250 328954478 328954501
    0x8070f021203010504020a031404030903140c0a0506090301021e0a201203090a0b0a27030801090e100213030201020f03040b0708071103011424010210150b1b06 70
    0x102040c80341c84410001800f062415601508185110303280c0020098180328144c40d64160544040c2c0206000d50030070010405800d141810505061018010f1007400318041030043d01c1c0c41c010240700300000324a40209803825816a07641c140c44501000b1000c07015581200c013540b04035541e41c0010f0542110003200c414800c5004603400c0400028040032032821040e00444e04003500306c00003405801016000f0a000d4103006000340722481d8001800300b55803d1840c10185290340d001644040e2000e40307404280c20a40b5039044402c090004a09807080413043c600b03101001145111131440420903030450006001068250782c400e8084640d036000600f50190303a4019445581036a0b07000304491b100099264000c0d001c0781d446440c3c00712841550000003405c0d40c103001030003170b005008141040342d019403200d4a910011081e000c00c00c103200303510000035211200403402e8201240c48201911440c44042d07880c3c03005005d40d41c0300c1c0741c4403900d0040c9504000d100e01440351003445590041251590351 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 328956834 1106 328955728 328955743
    0x3091415010e090c04050a0b12060115020304150c0204060b03010e0a0b0109180515100504030b01051e1e0402130e010b0a0504061d0a0608070f02 64
    0x480c0d50411210141d1105805001000c01d210064a000c19580f0300c200040c0ca012803942e5806098101906000d160190000c0350f95003800c05002780841c07003070f042c0c6e10b1041c2400047c104100080340d9030300850060104416401001d150414090b480d00105644040c10103d0800e543d805510410380090f444025001107882c03c06c12070b42564845c6021040d02420a0703035000d41410350704065024000480c0e43c07196514808501980070070110701000f900c0040070340051900201d0010420b8006100c11503070a49400008121840c0c090911444c0e200f000340c075121190b42110402000f004000300c60390030610130305400302c55070311503000030b00c10303988038411680e031003464581c10340b2400b081640510040401030060034042c60f40002264211071f414604a80100e8103034402000590a507020301e9409550701000060058020300da6030321460454590040c8a4040c01e0160b8440d540f = true := by decide +kernel

theorem cover : BRFrame.Cov 328776978 328956834 := by
  have h0 := BRFrame.cov_init 328776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 328776978 ≤ n) (h2 : n < 328956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
