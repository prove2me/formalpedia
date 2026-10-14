-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:12:54.32666+00:00
-- url     : https://prove2.me/submissions/d3b63d0c-dd00-4a73-9578-74e74d8b47e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 196582733 ≤ n < 196762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 196583983 1250 196582733 196582801
    0x603130c0303050a031b0f0e0d0b0901060302031c051209070308030f06041b0210020a05090402030a02031b04060206070c0510050c090a0506130302060309120703080406181a 76
    0x20f0140d0000129000030034509400b0b5919005002e16034000b10280c3d1350f0b407208040d1502800c0f2481c244101314150464550b044480004100403540c5201d0401c40e40001042031440c0109858080c541d144400c0c0c8045074100f6030f54903640082158203107044145044200d840d841180f0b860850301e54000303410300401000f800840c0c1c034044141401103408460620050f05120340ca610340d484526411005640001c7c41c8203440300d8990090003151010f82021070070440c00d80d0105041e40c2c000c40d5503012880d800020400808200ca450310803140000c10050f05017418500d01a5035880003074000030a01800410041c00c118003004214034200c00d41c1d034180190b0500d04038810594214a05a51003002c90840c08201420b024095540036004151848501840e40d028400345a2016150034021300074900c51b1981d02560100424070b05201c2c1d91031018034a46800d0020455034402100811324004a01a8004c59a907545100795000800d00d080c2094490201c1e040000704d0001b0a0740f0110204071203c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 196585233 1250 196583983 196583987
    0x31205040605070906020c0108040b060d08040b03070906051c020f09060a0e0109080a0b0a0b01020a0c080a060b0f1f0504050a08060103050f010209060a0c020103020405090a0911010306080c0603130c0303 89
    0x168003c41281d00e84440c035a0301d0302c509071780303503100940760b240010450000200459400d90345144c10a801401c0c2406a0340e4980313034a8060741c056001100340140000c240800b40741e0000354072000b84403614107a4200000c40c0242a110261440c81c070b41c3c45500840c050844007011011102010001440b856540c10b817514040c00070074400d400203002c07070b0004100007008100814803000302540000d030112079944840350440180040c114560440c4102784100740041c1c800090800034110700e0b00200520b100620b009000c0e42c03404440700740238100164141c8010744540380b2001c00d0511110448400031614141241c06014990242e584030304080e4000840e44804140a41602d0050003503512000c00d0458650907442008100f680005041200900051080c01c0c09403c991051401604e0319076600001110b5841c250348084d1007668407410a41008603000600c5468402070034103100e064a40b004e826284e0708402e403081d010f04c20003c00103400c805110400c90600742d0005003003c8940d02c074240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 196586483 1250 196585233 196585241
    0x323060301050c0a0903030c0c03050d0503090607030204050607081c110a030b0a03020102071a1920010506090601230304081207080c0301050d05010b03010f0f0606030902090c070312050406 83
    0x4090003075203007401003501e50100307004880b00061030f038640000d2145140d404a42004a21000343e448460680d030110001c1d100b401007050b0300b4080c0d5130b12500d0b03080c905902070410303030050920000e00d44100400c200d9500c0e13450a846807150001c0c9203a480d03205449141c2188110800c42d405040e1804002075030701c0c02139401604000d08942d40400041d6116405e0215040417400301a001d82c0c48004204013251110b80c40d401c0711000e0b0050740782005103140750851428000703000030380460803800c4c1c0381c01c2825180b0503e06502c04035000910950501e000030a850105c040e090030b040004d80721214501d50580000c139880d284010f110660382e807a0a0800f4080c0380c1052403a060030b600b0036030100e43d070148600442c60080c420009007500e56440c00741004001ca66031b40080f00c46540b10000f6990660b428891030301030040814021800d0240c00210008640b4690408002c0c1450058440d026031100e490242e0f01900311b01c5031564403c82c50506440007070900e4412808182007a0401080080c0750300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 196587733 1250 196586483 196586491
    0x180207020d0303150e040804090203060d0807050a110303031e0702150a050f1b03070509011e0c0203011b020309040b0429100f0c0308181203090c0d03090e06010323 72
    0x20130188240e4442120744001c0c841518060403044080c8024050080700b0780c02540c11402c0145280b84412113591b0714501500004001e035201d403c0044100f0070b01c11640180e0341220720407000356281d80b8014405002d00454000b8526100c1d01c1d40c8001801c1c2402007140009800380800320360128600b0500000103410b0445e092103c292120300410040340991005180200f0941041411695007400441f0503410010045040000d00711041c000c0409869440d10103107040c0da80d8407421015401414291041e042003454281d4039100d9810000340d020068925603102100c012600b80a9100050080c00310000038014010905d0038040341c031031009820366914202655000681103160600b9285010b10105a101054041e0034009c0080d1052040652005006001c0d2144607803044d8040d203054110480c1038980324000003030069100b0200000210700f03100b00c40052280c070b060b5400806820591080340c0c6261202000709810b41c0c000e4224042c2040000c6a03c2800d1041070108100d6040643e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 196588983 1250 196587733 196587761
    0x30806010e03070803130b0901020703150609020304111002030301050d15020d0203010b0421032703120c0c12020d150e102a1b030e1008040311070e01180207020d0303 73
    0x186c00581d000601080e110020f105801800d00c00740f954841c80f00b0103ca28020042e4699140c40110b14072040d4800386014a010303903500310344070004005010511000c00400400d5510601c0108000c2d960b1071400703d906d550141070441040e004032900d0000c0e0103013504051180d40080b0000c60b1459103a000b81084414030340740200426010524840c00c10758a40001c1c00040108440074407d0749040b42d510a09404104450403869607515400c2c01a0540820a00060303080040c88050000c1080d14502030850548a8400e40e58668005201f030140d0b0784000705070001c0c480031041e5a01555029003800f0b00c9601c10350b400039840002c0807004203289542512040001d50210142e07040500e52803025030b1083d100c0d20b032042c030601100464100b102800302c2c100300415051000ba911001401c2e03285a80079202ca02e21800c0614001e40206002444224154406142042020040d90b000c90440340d030001070b80034803013902c15a900603100d040d202232b4000040c5000402059031540c0541c030089110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 196590233 1250 196588983 196589017
    0x3071a1e010b0421120807030e01051003060b0a120809101809110d02040b04081218010e04180b01030312150e06030721060506060306010c030806010e03070803 70
    0x10001a590303880d028010702c200300d4402d220600a864590300301001d0840c039000e10007283c03030342c0360303a207000c0c01303582100740800154500d09110319142c00d40240c0655203072240c02800545480c02541c3c00d066901c0c80302070035175511428410003e848070321007d0702502034450416201a098105903260b54404038280340107401120560800d2f41c884c000382c8122540f01014851400c1c0b07001c203060041e0800c41c5000001900820005964102a100400042010070252a1110320342041e0301c1c03d180c1e4201001020700703010004038090110500200032003030000d0a080b41c40303517400760200d401406851a0701c4484220300340201e05026030305da2054100c900ca552051151184410194160f03486a080010000540c2200384116409481c8040d40110060304583c052a5030b0101d20440514001e0f820951141240001c4140310003030041c01d90044080d604280ba50504c440020301c414640d07040601004501004521581e100e9600c4001000d4001d0480d41581e484044540d22640100c91003c00342ca04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 196591483 1250 196590233 196590271
    0x61e0d0c0806011e210c03150602031603110a0c030f060608070f0303030e0c06070f030306090b0d06020309210c0609210a1407060506010e0d120f0203071a 68
    0x100e03028694442003054020001340d1416001542c0301c102d40300c10b0060301812482c8032401030800344502c204400c49a034011614000f45152004c0d045019009601150410400000e95203404502c02c090154145014440012811f4808cc100441c080000f40180720f1010000184000d6400c07015050b8050542001819903071341c45555201c1280c0714201201c0308000081001c80e00036489440e807102280240c0b010300230b9a000242171517204400071210b680084c20308000b03255043c030440c00a40722412003000902011000038042c2140180d000f05190740000014208001c140070f6042d40c080705607140724203200100b00c843c03281c0d00a4201c2c0f002c00d115074400951001400514202c085001d03001f04044034a140c1c5003110f0552002141c94184041d035848001c490001d03600510045004800000d028107043c0001072600989010030340c401c0c00d030030808a000c92294200240c400e074580c200100d401c80d40d01016811070244000140c42104070485290048100719410b92107401031107443e00000704 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 196592733 1250 196591483 196591487
    0x606120709060b0d1a220b030105010f0f09050c041205010b03060403031a01080411091015050703032d0f240509010503150411060409020d0f06060e0f061e0d0c080601 73
    0x5c0d1100040b507002c6049009a03e1004106240034000c5e6840e540c0883d141503800d012034203407407017a40074200840c0c5907041000500c2581d800d44005d0007440c00140500c2c2013090704a02940a18080c1c403510040520711032042107000d602c4214410740c007609a034524601400e010780240010404c8216082440d580841a580304940c4070348200d034071660001c800c0030f60350103200c4406d03001881080001d00c82c0001048402801500c0e00c40140d42e0340d03c5035507643c11391034010241c9045841c42e85548524401e00c003440c0c1040e54852041c240070f0040000c3c490050519400500745503005101030404040e00c4003000204039540c0000d5440c2910045966603851007416038410320410114004400040442c0028021800c00e07200311900529030760400d80c03195180310499008440d0071402d15a50b107003000c104035031401614000c20490400d14070134101030020401803810f0707502d41c034881c940000c4c80d42d00c5c0205400219101c400c6803c00a0307100c000c13040d0914020404c001110000c540701c1400a03103198 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 196593983 1250 196592733 196592771
    0x5191d10021b0f0a03060902030c1516110d050304030b090a0305030a05060109030b0f15060f0d0f0603140a05010513080f0a14030702011a0d03020606120709060b0d 72
    0x20800703078018940b1003034865141001d0758032058a01d07408000482d00720010f545108000014500550700054800001d104152074a80c40c40201c502908080103c540d9421072817003640c0e0b01e04007110b40002341010603e44841e03c500054003542e44410703041c40840c01e202c00000a0000d803031050114103201e4440d02501655081030b5140100000c50420000700e2552960700310750f80164042c1040c10300079440b40c0d82c0a0b2040d0302250005440701d07041e81000901461500c140c0710300302043d56080e01e040c10341150718102d8862205001c007244c0d02d5058124888003142d0054000715004103a128608441c18455500d401c182d60040e2034945c28200411891300840f03a411040b2a80211a81d10701b42c41b614000340b2035002b21000100b0703c00c03844000b501900d0014001e6110b5400360f4000070b491304061400b50b00114a6000003401645000350040019400155030b54001130b044501d01544102206c0846c0b9040d84d40e045540385c40d08140000803008503550140540341d8441e8002c2c01041141519a00d01d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 196595233 1250 196593983 196594009
    0xb0403230c0114040f0b0304051b1e27040512030108030a0c030309060e0f12090d230a03170a09110108060f09150108070f0c0b060105191d 61
    0x140e004007032034600c03540c0150140b0601540d4000d1560505548080d6140038420070b034482c0014401c000b08000070080b0500c5400b2400d0212041c041400681402042002481280c5211260f2400c0307081d2116a45894a0511400342c1d00a44060969140c1c40040950f1040d50100d40324403401803a403141d624500180c070f041e00d00c240000c40c00e00e40c018030200c48003100c00005505055640310080d0109016000d103941c1c0783d01c68802400b10000780740496141c500c03e40312500c0c4030f840500500420390b0355a000150115000a10010150700001c41c1c0300d02c0c0e00710307407a01d54081e01c01d894400d41015004000b40804e0031411902144c00e0381d031400d64106032170440c1d200904000040f4455215503000e04c0a6540242c00600701c1131481307031100c0101d0343c081020340c3c4010501403c0301821030035684c8079240c030703038030001504d1f04881c807902c1520094460310301840024201444d030f0002030a942d20a406880c010072050032460186807449034041d0501c0f90058800c40c00b0303900d1140410305030400c41e01c82084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 196596483 1250 196595233 196595303
    0x15043206030f030a0c06020c03030a060509010f0f0306020f040503030a020c09010e07020d11070906090504020310020f0f03250c050f010507050f0c070e01060917010902010e0909160b0403 82
    0x36040c0c08220440b0704c1504d08208641c6c155007448400b1070643c2c01c0014521070181a800003400d00d040200700808400140c1c0810038219135000248034410740c0c0036840f03048a92054001d61140294220102c4a02540d084190144400b05241008542c001818149188240c0d142105a600c445000000041c1200c1e10405a40540104100c5c2c51180300910b00040d808820340f141c2a40312003501090b110954810982e0170348840a2200394502803000002010800e40110300e08481030005c0b01c0580105a00e0b40c100d004040009070b115400c2c400382d00384540c1d810241e0440b0519020003d402600041f20903102c41c45101e50080c0c20f400140b01383c81c042c41c1e4688901d424a45000b0b40490341d6400071304805100c2c090002c000910286516441b8068038140d01c2e001407050514000c541c80c00c10f002d2a00d4401e078100741501c070150360045030602d006030050340c860409944051045180c401c17880c01b05116160600390010b1140c00d42c4000d00b09986c070520880d051441070754110748100c076090703000b000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 196597733 1250 196596483 196596487
    0x120c120f060f3d030e06010524070204020d091e0209130c031406060310020f030f040f020a1401022401170a123515043206030f03 57
    0x103994684560040003943e80200d00c0c5610004041d10120301003800014002001d04000c0c21a51054050007030810508025005202030340c0f5110004883d004035003410581c0300c422032901260300040104031014a074019009540c1d54070740d5100000100b074544002c0d43e01c0640c41e102a16825461044035400a4008041200640750301e00c0c0b142c25802010000c8034100f40c0c0002c00000210b562401e401001000700140402d07241c00c005250910459104111441d84100080c00c0c06000000035039401094081c41d4080b15640c2c8d181c1a46100e95002c2c019600170a4484001541078059645500700a402c2e402e4802014114212105458600810a80b000c0c3d50314010300003811070151440c00000700e581198484a503949030346c802060030092060005903000805a10000170700307100c28115a0142003006a20740188031a140ca0303202404607044900000308007906d80c0c2d1560003000d021490700c115040165100303418050030311032440ba07618400e0344460004903d45004190400d0500d01c40c00a14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196598983 1250 196597733 196597759
    0x30509010f02011a1903050a05010f0501050901081c050408031902011508060f061f080106140720030c060a030f0b030708060a02071a151302090604120503120c120f06 73
    0x42100a00ca240503a05c0d00c004840c00404030f0001c00c00c2c4088a805000005895170b2410124401d49005030400c0303004003043c1c00100708006000a0050a441e46030341100440c4500c00c40450f03031031107a580042c01c0c4d44404214170001c0803a0400412482d000d680003000700030400c00d091441640b5601c01c0c020a1b0f080031000456489180c400103a00403802811039a609410700304003030764644003d503008001040c1d5001441015045030105000e154001d205505200d4641d682407100410914810911081d00b280c43e40c682e1030400a07500e032808018011500c851071400005c005100c00c0c0c5030001c2035400d03c01c1c02621400c01040403015940d410000c1c0801d41d40b04c04a0303a01950100d201217410356003100600a40703085010125000d0040140000030f10b9003900100000d00380c9145503091400c3c070410198403a956030b03000701c0d41100d10a012210b2404c9003401c000b4198025090080c6216003400f0800c0350442074100103000924059829202e2030b2140c40440310074038411100a600400740203040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 196600233 1250 196598983 196598989
    0x18100e0a0b190e03180312030a0b030c10210c02070e10050303031005040e0c0109051c0c0e091c1b06020903070b0a0201180209010501230403030509010f02011a 70
    0x110b0b481000b4011821118058408050450b44501401c0a09410115040e008003942441342c41082d40201c005046c08805505800c0092102034041451903540d2108210743d40c82c28002103074104402084090b503895240c070041d05c1d541504161100c49007c440c01c144410000344070300d20441740710344d00901c202c3d420854241c1c070700b44c00540190711104420030f0005003039604000030351240c0044001c1c0ca08640c0303000140800d4506000d08408160003e40e24440a070743d00241d02401c9507000c441052020235070310b002810010b0141d5000c3c3c86400c1000021844048260456006842c00740849008a4108200740300c440800c1301032900040c4001012a18103000b01d0401a42d24014072005282c00046c0700000c4c5000010307403008071102d2002c580504c00a0b0284180001c0441010340c1441c081d941d940064031450050140c0c81c1070080b0305000d0804040644903262844d90482e18090b80ea43e183d042c01391013070300b1001c00e00740000c07001221018241e10600a0088401d40c00d16601014002c205c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 196601483 1250 196600233 196600253
    0xb0406050c040f0b0405040b04020711040f0e071712190f0e0d0302010c080a0209060d2c0a0231091415010e0702060402090403050309011418100e0a 65
    0xa81d07800352010b002c0820202c00962250300240441a1656512031030002031106803a01c0d03c81840c1304030b105101c00380c042000ca0141e0100003038101c50000d0007210711070080005122240b2860034502c100040030800c0d101c0e2620190451045504951440e043c1481ca120342e441404610703161a90729090041180d802100c0c04420b01c20036041a052030070f42c02c00400c00050b05041d0940041c0c4d12214544091358000d5452508550710820075450b010351600070901d030b48104619059181c4c2d6410820f141c00078800d0310459910724403013a002d0641e40040100d40d40350b41c0e60409a1141c04000710152200d500600500c0400200c50700c1e2007008030540521500600c1d119038282c0714072040c00010500210140560301001074442c40320851941049000006403100911000665011605000159945e41203035070b4803a07070620346070781d403660b8a005041c0500304580c0c41c0c80b00c003241d110a00850203100f803081002090801304944013000344410301400e4540524090890390445250701000c1046012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 196602733 1250 196601483 196601491
    0x190b0706020306030c0f3f2d03091306090905240105010804120207030b2d010503190503040302100309050c150301060c030e190806010e0f0a02090103140a0b0a06020a0b040605 77
    0x4092005415000404907666102042c08011234000d03068801290326001c964404c40403403440c8013001b0100032565148d0301e11504410a03c20541c1c428420011000c3d500064040c0c80c800b0070500c144c0c0400d25245a640c030300e403001e0b20510315458103051a0340612004807412210141d4a8580544a54aa088496003c1c0c1081c3d02180152a80030011601078030b00700d4090381010403101800c522050607203d8007601d04101007103081420004002c1a6000510076601c50007904110580c0300c0c840c5000c1e8554401c0d03034070007500b11500012940f006030b0950300100415000f54191400c0c2240c840402201c510b4000c1740d00c003245424401440800e2258000d440c2c03552181c1800c0d000210204000340f80c400320405400c0d1180e0070b09405100e842020322800f4014680c0c54020802804d1040009400300c80c0107018610040e0f01150b4220f4a0b0322a80185944940350480f84501f0304184c007000c0c0c081d00c801d4828a001e0096000c001404501c0055002c80d03040e0054020300303958440d942c80c64041e0034050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 196603983 1250 196602733 196602799
    0xc02030a020901030506010501181a0a05120906061e01021b04060807030b06041d03030a09020a050d0b0906072303100305100203070909020a020a02190b0706020306030c0f 75
    0x1103010380050702c1d4000c880d40a103002c0d40040580e0341c944000103011902c80705144661080009080000f10800607640c0250241d0a04064945030580c1046825002e2903100501f1141080c041c00f01c06040450010300960f41614040207003849103400949001d640c45656005900002c08813115031860801d0142c840b02c0140042400f55580142c240350400300c0c1c01c1030ba00c1010346401d02550346003030b102d090b0007c0200402d441d903242c0d8000c0310540b6408020702c21040a511815203c085596072200b000c0a440028940d80c12104241040d580d4440700b01c940f20118440c1401107007616000b00d12420034801c490707001d13485a408c0b0080180700381c0c10140c0318801800d00d5020200014800380700180511488130401622880c00f45002004500e00d0341c02030b10b103540304000c3c03800002d074049441494990140c910030385a802c88605041190001d600c0079500364004210f000c100a10368000b140a181c0807800c5603906600748080200d9504200e107220391020b00f00c0030b45662402c034000c250708242150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 196605233 1250 196603983 196603993
    0x15040f06090f08030d09060b2106070e010804030e030703060f0b01020c04020f070807060608010e03071b260f061504050f010f150c050a030c02011835010f1e0b100c0203 74
    0xc0070440589c000d0741c113025440405d004c00007106004000681e0310a120345080c281c1d40c405500080e2540c8005040901000074161181d21a03407000c00c80003004640c4601d041216851445401c0000c2c05515407060045c0280c0c2e500e51034618240c0241d8250090b403401561030210140e8401c00c0035401004201e84094550100007410358080c80742c41d0324070740118040d5035151124940b0003103000d030110710700741102d0015405010a8545864005024502c0702d030040500b00c01400141c60003640c111004200c1c03050b1010001803018400e104164400b0569050040d0340301e45031001c3e444030b0300740107500c030340d14050320301304011745100c044d18a4140c3c45003083c4030221003e494141c1010721115042c0c0201c0c2d0400c500000b1943c1c4032681c001c0b02c8543c9003800d101182043c02d9220803c0580440d00e1643e03915280d8110704502030102480c1110040300204814140072005001601c4040c1c111004801e04543c604085040b501a81c9201200240a04410181d0080c1920b594270007a10a070b0f00f51041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 196606483 1250 196605233 196605251
    0x50d0201030b0409051e010504031707020c0a1419050d06110c2e021204031101060503070f0e0c07080403020d2415060201090b0a0b15040f06090f08030d0906 69
    0x250740f14600000340540301808030707004800b042801b0f0f07080813510750015070702d0501013001003580520a4021100000d8003100c4903100c0760022460010308000e41039100c442c5a400140255000740344d03490680050b201c01c10740045122010040c51503d00c039581d000342d5001c680c600065545e61142c1d020f800300b40121410403a0701c0d101103162208486c50912004c500c8101110b20054004c005039010110820551034040200c403d21011080540003e0034012650350036110320000790400d074050000641100c8004c0d42c3d512240c10740d808da0f841100d0308041524081013046011104461106412000322841d040c0743d5801d00c41130002181069400390380e079030410040300c0000311414600311803010021030190f007031028818524003c0e078030040c03d5a1600000d0400108440f18450b407101c08040c00151494211020660380c50340c6010004030b1010000f0007289010704286500c0c01e40b01e070303070f0740e11100c0d203840351007441c01700d2a0360181c900103500a010185a080040e000700326050701c501e5001c01c140c11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 196607733 1250 196606483 196606489
    0x1504080607081509010521010f181506050904080c0102040902031f06090f09020306030c04290a0509040618021201061a120106080919030c210801050d0201030b 70
    0x10030740d1024000303070344001444100c0307101800e00c50418404a40762040303540350400040c0b503c00740a1384d00d186c490b030034002540702680a50080101041c840400d02502c0382c0c0314006140d05054176400c031110001d0b240b50f8460002944905c206881e005010301c0d070355031169250380400d9004400000880d47d020407003c11b81c040d89001450143d0103015401c0317000c1c001d40014842e82e034a0358100c2010420200401c20248280718480000c6814200005949031508801709003084200c000305501f041c00c0039060320f0300c003002c03200080c04003214080306110610320004101180d0401d200d0755511403107542c007107000f091441e44000551484050040d042809a501140d440094150f054010b0795503480d0400c49ea4084940030100e001c02d51400f2460003841c024401070803581801041c1c00c000c1c0200004040f0b5000300074099400c500c90300707505030310103461400401880c0700200849144800640e6006881c050a006c0120390031305498028185e03082505001000d103014000313904050710380440c046103403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 196608983 1250 196607733 196607743
    0x50301110d0612081c06080a030e01120b0303032202030604240b010e09090a02031c09140303040611070f031b0602060f01060305090313090b04050921090a051c14011a150408 76
    0x20327201c2c2d243c0d502e0224001001604d113203035040a000c185410035070041540c4e45d011040b280e05c40b50031925075401255035405400c1c46840014006d4040c03050200780810311420810342c2406484101c41d0429628205c4800c030107448070004164003240300505005030501d80040c490364420001d80465424031119000031b0300e0400003e05034003010b5815042400c0280d80801004050305980142107040e00c41b0340f0200340da920452117400c042000302c1d28210b0a42c4020301c0030b00000c15a00185110140e124180010000040d098001d90156150320004100e4008501c40b03100c1c3c82003000403600d50707281903001e0f005030100900d034001c14041006544003010350600200c002e0421035100042c0070010805110803944040e11000544e0720003c9480300700144804226001c0103c1c05c00c140c2c42c0c0c441c0301e02203615440c142d08a194480081c9020614142402d10390034032481c012001e0020342450910607500301d550500300030900c002c080203504142d081c9142e801103000201500c0d240342c1565505814200707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 196610233 1250 196608983 196609003
    0x203070c0506070908120f0405090702010b03011a060d0c0201061716060203070b0411010c0f12080a2018120625050d090507050301110d0612081c0608 66
    0x108298141220030700800300328855006129050410000d810f040b08295500c0000d8840100c000c0001400c115021924041d80c0040401900081e003505101802078003030984140524000d6103007050002c1481556004890001005000a854494112010130240c041c0315003503070030744d921104001540040c050303e400e139040000e4080d081250341e207908421001699805041194414000b003400b160b80c13103c403a60400c0d0b0200b9400690140d883c01660300400c60000640703d01c0d036816850083c00000c40ea40c200075000c0d0758071a01a66214050201201c3e0540003c14100c140410514030003400070005140003c1c0510840080c07419140021b66800c48680402c56030f90044014000c21400611540001c1100420071802100c4a084000e240313000310041d900c0a03a03203660b1004c0900c941804650098600a0020310402041300d403101d205902a03800780d08481d28002d40014203041c445191070030250f0100b41c1c20700d0143c1500c0d100380240f0f0000008101c090f41e13201700140c42601080900c1d12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 196611483 1250 196610233 196610237
    0xa03151809050c0a14091e0711010c09060e01030209240406200303040b130b04110f0409080f0304021f021f0b010804150e010f1d0a110121020307 64
    0x90000d10340941001c4281d0011409504029400c0c021076583d10403110035017070240c0c0d48012598a441c1400500c40758004104040340700c000900c420b01e03038401038180f0720b0b500d114000c2c403554110001c22104000b0034420500040d0201c00c04503115031282e0000d110100c0300070b00700b241c101031140d107003416501c3c03162144c0310300d490014003003100139000f00c134441880408808040b150056008030315241d1000510082c14181300c440040c000055404255100a4002c0c010b61002d1501e45040c8a040c2c41c01211940b00304003008500050340317401d005009140e98010010350501d00440211500c503000500204d0b400a1541c0e99500c10441002c000400b282c0c1c960700030075040c100d030010f1054510305055800112414400282c1031640c019600c160001e5000d0b0b111401d400c48001d00b040100712180071031030a5400c000c40035003801400d8206044044220000704e2059502d400295038a00e6144402000101c46040c12480c0798081c4074065907010070426000e81421039441281d017241d02c11107000b00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 196612733 1250 196611483 196611491
    0x1003021005030c030103231902040e160b030a020c0d080103110d050a0b04020301020d021201080c0306071407050c090112030801080303011406070809040507051209030f0a031518 78
    0x154504102546401a0607050403807450402240f031021a01c41400050407a101030715207860040350018000030007400c08000c0d180c03000140000fa00820764068001da2040c0e0914004105600000c10281c00c030388211000d00101524107000191560401800818095402c0c00340e44100a400c0c4003000e4039000a669500780c560440ca0400341c400540f1241c2c50143d1340c0c01c1e0100e00041c10004540140c15001508940d03281d131240300003400f9100f81c1c440711002d9030000c12411800c0707000030390f090b040c1e552100940b66140742d01c40034940c0c0d1341001c88441c1c00003558126280c00c00790b84400102209401076003a59401d44c021404144074403405e034008000c10111488003010f055200c20028098440d48019600c1d5516081004289180c15240c081c031449002800a080140c00d40480b540208090b205100c40c1c50b1804001d010340c1c00040c600803860a0100015003182000f104030760440e6402c00c072890500000740001c800521500011402c0f44484610106503002d55036141d01b184042e544000c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 196613983 1250 196612733 196612739
    0x1503010807061101020a0c14120d0e060906060916050409050f0a0c030605060405010f030b1c0302100903080c0306030a050106150e03120d020913050a0c08090f0d030f06090510 77
    0x3854000c080501c160383d81d2040c40b070015205e038400081c06003950043d602405030005d011026040c092407078041c0b2810400040d0302d141c0c6c65030f581c20060040704000190390b01035442c40c008603251b201c100c1390203034010820707400210440f145c1c00d09030701c00152a16003142051b440c1c0f00f00004565090301c0c195024284a001c2200d4a1450f01562900909920b002e0080500c0c01c0d0100e181400b582c0921810b2181c0c0001803110765210b5449888015401410146002c43d0004203101c82140005c0039001401440606c00020303820340100c0304070b180d1641c0c07000c07001c1d0348000080d4225040035181561500801d1a00800304030300340120320151414503801a2020100c000c090000e8900e59480350003500000031944101e00400f0540b582c0c91907018016940314000400150343c41440703c0b880005515080c184030202d40e8682c0007111102203510f4280c9a80c0380c5941003980d030039400c40440d0180d40080e06010b02544650042c2000300c50600e030100314030b80c507490390800340c1e00111203818103d43c02c03140c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 196615233 1250 196613983 196613987
    0xa05060705070c050f090115020a0501020403140d2102090d0501050a0501080607090605090d02031203010b03010f0f0b03150109120b060a090c021b030709060b0304050c0906060a0e150301080706 85
    0x500000c240813aa17186110362860007280b01540140325110130b42d64103c4260500740d0003446500000b07940040215a1030380c691418034407044440c41607007400e00c00e85619981c59030040750700c14a16095500c00310307105180b03071040324003075803004401c0b5820107010481701000600900460703000382114000840c041d030504607070034035120340204004200140c60348200056178106049544540059031000b0000e02d05002003032901c1079104101c42101d50020000030056220000380d0b0580e00c182c002d03501e0311551403808021215060081035000c104c1000410081c0c08400c024444c00b21040c18181c0c00d040d600c040c80d1120102c5c047c0300366442210202000b58510b000700100c8040e01c82c07440d04000320001920001d54407001d846044911a55032082c08507a65403c010714002491209414450952900c081c5055500283d03401c40da144101100003440b880d25280b00380c412070016110728202032140600301d0b0000c91a00b000c039001441464030220241040d030040d0b01805030400200400e524001c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 196616483 1250 196615233 196615253
    0x204110d0f11092e080718050916090302040501120209220314070b10061106091209040204050303040e090f010c0f031a0d15110403230a0506070507 65
    0x482203102d1402002010106040c0c003a100c0840003030711050040300612110b0940300504100542c5030304190000d180400d9032000300588103c8003030b030350101c582d4010350098403078040c540502a0b20015180008a203520b01c40b01004c260580707440d00c04005c0d5500e030080340443e1020307003200e9002c2460841040541c1400c0340c1c515009081d11094544400f41c014282248845050000341003000d0010300c88002540b183c15100f020343c220214401906280030104001402d520548020a18182c5880700d0310101182c410710940800010744072105a1034258030341079121400007a0b200741d0078000421076031020800792002e44130406108015051204040c1d180c00e501140c10350f100e03810021001c3d00c903640b1070405034003c1240d040c0417507151a0088c464070008684d40074250410211600c80051081500e07175003a404502120400400003610100e0703200d40b00d03900014061000b481d00038200c44030001003d000213100341080d5a0a0000c544d0b52034102001610204001400865030405000300300304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 196617733 1250 196616483 196616501
    0x11b05010509010c14070204050414010608060f07030203090d08071704080a030b0307210f050109050c10020d0504050d060b1905030c0409050a060b2121030106020a060e0a0204110d 79
    0x41c80100d20003080c01701c10782403080ba01c00078080d070340714404501085424065003001800800090203503a4845072010350741e050031924819040340340c4003c41c0d0661f02a1084900035803030b51028003a0802c2c442d4040e200440040c1c107100c01c00102c01319000074000001c1c161402140725020b80ca40c0c501c0742c1e04009060359419007141307100b60403030340d0100310340b540d030b40407070350300e00415210011548050b410b20440ea40c843c048054499403d004c840300c104440424840c04950080f00c003861807641c162001c99449050304d5422000c11130800003807060f4588840e034202d041e4441c40c400700c0c03c100e14501040303503100ca40e50207800010204100340041d1500740401161020140d03400c1103400101d0302c4d00d82c2d5513003d004000d40420746d06c0072a5803003500d980480c400f03200c501d001d910410704070601406580d80300c1e8400e1031080101a50784005a99034040440303040380c00380e5004180c02d496070b4481c000100407014031031021303102d101090001038865001c0e280b07808010086860b00e540000d00140103840d0088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 196618983 1250 196617733 196617737
    0x110f100306090e0f100b150304050105190b10050f070507080a03090e190518240f01120305030a1803030204030302160b04170708060c030105010912030503010311011b05010509010c 79
    0x2034200c0400c0100280802d05e69002410104890783e812000c95002c02c401650304400c00700000400051100541015006420601c1e000b200107030850005070132249030044140d400440300e640d540f15588200003908203081c40d080100d00d018039964641d86003504681c00003000e0380104a5030400d00d504488c2190080c03a0a071102c0c1c600d8500541d540e80341d180301480c8208110350310400700d0050070140341c00102001030302c4100d50003c0320003040e604405141c0b0390303120030309a10003000500300e00380304a03020304035508062601d6020000c2e0390144d8013900300038007a42010765180e841005c60344000ca14000721a00070b0300d006940754250304000b0b0900b00200140c451451000b0010482641da500803101104c0021100080d14045c0c0095242481240d03032015034644144d001f480042000103008504a0307a09899501c0780075a40e44484840405a00003d80419020710041012500002003004407880500d00720406116103030300803240c407803221400c2d98140c1d1b41d0000c001021109100e542e031201440c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 196620233 1250 196618983 196618993
    0x12042903010e0610030f05070216080a0506040204090206070b040b0601090602031306050a020f03430b060d080310140303072607020a03080304030207060503090a110f100306090e 78
    0x202a500081034005440c86005100840c04109414465802881611140e4805007c00c0c02d0000340290380e550b0400246100d8a00c51600081881000600d01c13540340c0e122000d00802d5a8035004c000c024680364400341d030000c000b04448000245c491044500c11445aa03080c05641003210004081108a030000402d40d842001a800c4414540c6501000c8802c03a203891591007144010490a081c00040d0721001c0b840080356007005140800c13200c0001268144a6031400b031884107110810507610b5600f2500141e000c1c1041001c41c4842d80050340c015000341100c0051225556070f402c996100715100700c0407141d0a9020b020a4680d040500010f001c04c030002d41c100800d5464101e200d4044054582070000e004180340c0c481d25410050791102a0010400b8040d0769603420700502c21380c82141c080b401405401c20101e4082c0c080c0043d42d00440d00e0f400180900140c699030441c4982d0100c18885c0e1100203e800c8004e155580e00c08102000d41075a17020440d18a000c10400650344611048400c41d040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 196621483 1250 196620233 196620239
    0xd03050601080411030f0712050d030626031207020f01060614040e1807081b0102030a09050f0d060c02070f0807240507020a0b071a0c0306040e1204290301 68
    0x400b01040c2d803ca0f0b08054922500d46040e0002442c080080c06031b00c600e4000c88a0000c0d2a5140c3c500f2805424040c0080e5290400b04440072000c03580b2a0240c100310150001c4000c0c41c01492544c0302507040d8111080fa172401010030400e84074104103c50400050340b01d90300010041000380140d4004010360b040070350405121060886203401a80651007910031072b4030018180103100f420b4140d4001c10507065845040d200c400c2c564131404040340190f610302103503c40d1007507540b00004440100215644128008c2d0034601000a2181d494044650001c001101000880c21900c03640c1607044042d002061298600b050010400102d68000718290304100c200b0408603580503e5054607407a1207041c040c54502c00a01510784d4084d100c4c000c2c0d0010f10200340810f20610035001000d50394000c80d0040800c8103002032182c40320100321400005201c050002c01c40314185a0440c010381c40b0103000359113850010206518264105074411640c00606e40012511903050342c024068a1103070b8141ea03803641d81 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 196622733 1250 196621483 196621487
    0x42a0302030c01050d0f050f040c060203040806040206070f06140108010e06010311010f1e09170f070b03190e061b070302070515040509150f10080402270412020d03050601 75
    0x15070002c0d06061080016021500c82135580c070210704a10b01c043d08120034241700305414035449045900700c2e000e184465001c242c841c000000e640803100c8000060446c0d07611903007842a141c001107821155080d6619079030002420754011500303401d40d60711130084158503144126094410006426a480d08010014408109001c4003000c1e010000e0230540c6140700170250440f0030961121800840e285c2c04039180d01e5040d40030ba03400c1c1c201c0e44050380c000010000c0c00c814507207d80003140000b4242d80100010004d10319824051b59120511749030322081840c81c18040c80c11f94030742407032680f12500b000c42040b1400541000090306036103103142131400e00b4180c1c0d070040d43e102902d010740c91242194196032054005a03404603005010050001101c90400302010b20269040c0e0310b80501ca50300c104078400550401008143d0469000d0381c83d103c00d51119001e01c111408840380c4000c0004544d004c51442c075210502c1d090045114101808400e0500d02c4001d050802d800080d400701810321062200503070b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 196623983 1250 196622733 196622743
    0x12d120b10050313050c0a030602090406051509010c080408030a020f06072f0c040207050109050d02030903030a1805100f090e06130203070309020a17100e072903042a030203 76
    0x49401015440540010b04000385480140340200703900041f10040481000050380203420141c1081e1428401d05860780200000d95038814004500d180041c13107000d02c550702c00e00d01c1c044003e0043d900c4c6032400303885601160555124144803005640805a0303072441560400c4182e80c8000e00b89000c40b88000f114507120000302642e13001036644409030400d01da0000040c4013980e24420000c02c210740c0c6050782e1410764060001f81e80f041c0c601c0d0250f1440c0c0d11420340003100722035101200078051890020180010b4031a1070820317490360500c90f15100701041ca034407803009100e022441ca4444203400c5400b00002070000d801900480b00c41c44650090214070740b0cc184a17030b4445a085a070142c2c40c4d980e00c60045000708100d4201a601c4401580c0010b9924589c0c1038051890071150305071040c5200703481c42c903001d581d0300b030b0141e0013540c0c015041004102000722400307100d8000c0610641820900d242d11504580050b00c0c1a6010501c0d00b01400e500307000b450703c041c03540442c190142c0416181d0703000282c0310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 196625233 1250 196623983 196623991
    0x14030607050a18030b090d0c0b0610090b03070203070b2202010c0521040911030f060f030f06090105070905010c1109070903051f0b01020f0705012d120b100503 70
    0x40300c030108001e001240a2484040f120010402141905a03139081c644099001a900c0c401c0300e00401035003a1006100710130b245245600906200e6040d15198140180003aa44114004110740643e0104000001e030000310b009000f6075008544a044c0c40c02c029401c290040c0c004818144641da152007030f44450051114030741d409007070180c21040f49042c51b038108802600420310700c1c9015803513400c0141d440300280059030341a181c1000300786803041c528480d601c81a80c0140318030881c080000d00d5840c004100141812001e402c0e01c00080f4080f001515005d0700b900d188050365101d20400c250f4030790190744000100320034641440d241a00740c0321001702c0810885c0060260f58040001000b150241040308001c40d030000071200076003d80711030801c409850002c610384040c2042c94981c920341c400904034900b0413410020706a887d10340740041d2503035103094a0b0b0100030a00c0030044410300304801091811100140c40300318402c011040304100703c40007648200d1007074a801ca8605461079105c0145d90340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 196626483 1250 196625233 196625237
    0x305090f0a06110c0109150501050f010e040902120d09060201050c0a0c03030b031204060201020c060606070c0902070312060e0601020706031e05131e060f0c0c02040506041d0f0714030607 82
    0x310340c0702d500ea40b806071182c00c04d2030000e0740c00c004e51041000031184440041c00d40508040241d41d032034a0400c00c00ba13055018440c001200d50746560800d103406c1c0d000c1c4042a00c010100171054102c5003059007040c0c281c0d1500c1c03010a030700d80c000b04405502070241681c4061100742c482d00d00300072610040c00b0005e40b000c02071f007019501e15403144141c6040284e52a05804102080d0f1120350300c140080c0070394405c0c8001581030141d54081481818400e080d503d4040e80442e02d411818148190704000b500403803029010403070340c4100c254414400f881134034060720f0640d002e076030750b480d1031800a0700d0800c05911143c200344c07402c40c080c4204401e020300340000084481c00800c20751220301001034a030140701005030048007807c040d411044a0f42c42c41241c42da2194005110b006120982c0400711410806840f020485d003550b000c0061070241d020503800840100001000b9410503041202e0118183e0f44442662014659000b072940401441009007001d000442002e0110b17404603465110241031401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 196627733 1250 196626483 196626491
    0x2301170c030703030813170324040b010509011b020618120f03192105100b04061e121506180f031b03050609030a030614150c01090818010305090f0a06 66
    0x3080120061f4580291500488540e8907400c0400c0c0c034549004101503150715040081441c2e0301c15040c103000d0036014990507128182858059801520340d4081c8403111105040d036900c4950059072524050941e0000c0805800c01d031420010600403c42c50f9038210000c1c542c030000075203103100000003c403044c0c000e260940c0c1c19482014401500e507102c403c007051401c01c01c01c00f016202088580d021503c03e400101e0300b500d0031a40c0311b03030000040c42a1300900b40025420800c1d4500700c00b08400c0c01410b21124506818110041101c039411100d0001c803055202081c80820004070f0380c000060001170660050008900780391450f115043c0d542844000d00d82d0784002c01c0603034130b60000b44152000359000410f540301454507048064595215941000c04a854504003060b1000c41c1142c2ea080340030b01900e0068082c03200d8180d0002d5404c0303912803807000c0d0b413600c0d215000035200c140a030860214429403102000002800501502e10041290420b40e004641900c000d140010307902d8025904004005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 196628983 1250 196627733 196627771
    0x40b0919020f070b090312060a0303020714150c01060609051207050d0501090c080a0b0106030501031a09011808041805090d0f02012a1e020a02042301170c0307030308 73
    0x10720f03005007140500014021001c20411135404002003035180170380141e001c2c19545090400040c442503000c081c00503403004a0500002d8549403201c9180e85000340b111480e00c0000717140000c0c0750b129034503210150f51152810000150481c80203800780c9400c0340c10f446010241507442d981c1e02041d22400d4800c000c401300400900400703501c107041d05604050f54200303c0b900d88130a241d6547c1890401c0321706141403400010518802e104443c16250310410101c0c0e40401e4110701205401c0c0030b001040c0d41d559954403406920a240104200d06204607034054940d4600300844400400351420b50010a05200c20424a400080f4000000c00d00328207181b0706030094150202d00424544039422078091000744a89124a00c115034510308000b1555a007940004c5400050005182510700d04056804101c8407401458a508100c140281c0b0400c0303842c1c0b042010001710b070054401c0c0e11160701103400310b40c5040f81d84424030941110420a40041040754950359001340050710003440100320302c140000304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 196630233 1250 196628983 196629007
    0x12020f012a0c0c240206011a04030b06010207050306070306080c03030a0f0507032102120601020c010e010f032714010606120b03030d2901020a050c0402071e060209040b091902 77
    0x20700003401d1004900e2184070940160b15400c40b48144d1408050b200c0c441c0005429078040c500001da10346110142803c0c81e2456a4408107c00f0203404030b410350042e41c8020609803000c01c41c681c0704035000d41e008102a031600c03c0342030400140c80841d034001c0e082000145c0307420b0f030441070b000d10000c898a0074958449550034129441c420100da1316082c4d1580100183d036042e8150080d011480d41002c206000fa11000c0c01a60b0311340e544d0f20307014041054051070049a602642147d645201941004156003007004070520050b100580c800701c0f210003124000050010601d00d4141c0701014a008101c00c5080c800c018080140c3e00c04046116600c51507000300780c1c0c0301401a40e401c0e032303e81d54040c401e108058989241850850b502140321321020122071005603c0060940141d0360040e0142652400301c42c240000307940704c0141991500c029810303a19859640c0c080c40b00761140034201c010780303e903025401c020550352070009513803003105081c00340200b000700100c01e004152007219005075038845082c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 196631483 1250 196630233 196630253
    0x180a0206040e061908010c0f050306151806160c0b0a0e0906010504051903110a1a070f0b09060906011703091210020f0306040506040e0a060c0c12020f012a0c 69
    0x455804d4038404000094900e0150400030009440d41c40b0b40700002e01c60b0104442d00e0204036880750340701f04100c081c8a62181210f00502000d185480818048000f0601203020381c5d101c081061110100007140703500340944201c5580240c0000080e041c500043c10784010301c1d907405100110b20660043c00426002da001d24200e17002014041c00e8110a941c6201540d1000c420b144010740e407035075042061b1501c0d850183d600100345c4154080c4000040c000040d01700c0203400c00ca008450101c640006400440d860300555441200084020320552400002541c2007000683c4140500300c60025200c604800c08000d490000d1026500110904882c0140a20b07114040c2d124203282803002604840c00807062000f14880c02082e0703010312168445a05110440c1c030707000921001d80d044042600009912508805046106407a29034a480101d45941d0303c420f502c4050030015034031582c03182c4041c0e1020300800d2640c918180b44003000c10000e443d2042e01c8511040c2d20000c21003005894002c003c20550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 196632733 1250 196631483 196631509
    0x4031404030c090f150602030a0e13020c0304090c0314061903150914060621070807090e10050105010e01111002030c040812070804121a0708180a0206040e06 69
    0x860042d06641d48a40300024841c2c42e00348544203090004544000020b0103280741212071640c002c1d45002d02c640320840364801c1c0020303415480840010302c27110070031031070020b000170150f10005195074600d44080c6100701c0369600c480e4028141088603008402404954907540b0100030344845240401ca4020f490351016590070091407184214044036040741603034040f984a51060352a10741440a40e502181da800e02112800d40c4030b40300da041c40b0b680d40788400541d000310103010211400a52554407040c1803900c0f9801070310300d035a41e0304420340c42d9000810062001c603031800c42c02c020650600000908160b0b400d40b1282c1484520400300132860030401c440001c0e150010021526814844040312107a841840340520610525904803c41d81011085403130380781d03112184619051904120321001c0054038030a48a2030340d550400000900d0f040f0281d842850b055403052110300d417001c0303101200d101e8000f204000764002a03480006840c7d0504450940da0b1143c0d52a40d50f80e80c0400140007411010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 196633983 1250 196632733 196632743
    0x309080909090c01021225050f0d020606043206060c0a0803060414131b270c050901021509011509091505060612060103020d14060307060f02060403140403 68
    0x1d010003481607804a2100c45075102607007510003e109a415104440c000d22143e0884e00200d1034040070410703414001000428070520075500460440121030781860b2050a844000d0380244041002d289050b11400da0141c1560203a4201e150008681c480c046030303030106881601d0043d001103081580c0303a805031a00700340b085d001c8a25091403032514859a400c250790960250b030410500c403054841d150112803180300c0c101645181c0901649a506d0f0b009808941c0703600c1c0c0c80b4030b48404298000e140c1c00d144c1908400020a42c2c08440320402402100e1044211100f0850244180035090307902040088640f02d840482400b5a146d82c5012401003009840402d03ca440e012000201c0b041c42e41c000302d0640c1d004070426440c40036000060010350350100d03100d40c0e0000040001204075414120744030f8120310706140c0182403500d40541e80781220305144018900003101020881e05140c2008102d0152940d0714120b880c0317034004c5002035a1a540a4802001d205000c44c1d420100350048064800450b005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 196635233 1250 196633983 196633999
    0x1704031b03020f01051003050a08030604060e0a020a120218010c0c0504140709060c0b040803090708071202130b0108010b07030e04020d0204080d0c151e1103010e01060c0506040303090809 82
    0x1454043d43e41c0c008018681c82c070f5420140060340107444802440c003100d1300303e8040c00074055a40e03262002507100900c0241d01903034078071001c1620745585660b51302c22001c0c460b0059032030540b18006080d01c10800200904140100054082c500c01042c1d0200707034410030b08281031561034501d0445281001d98001a8001c0d18141c440d010503a0380301e44190007811551240b044880d00c5070811240c3e540f0b10038028040a900c4008100000c0041c2c0045611040c82d2040da54a03c1e1144c00d428104091070703116031405a811485001540740030505400a69800c00c02041041c03408000a0401c101c1442481c2c25020041205010316000b44074103207000100610031980d50fa80c0c0d9010000070340050091091b584504c540325040c0c1800380405903005504107100428162501d40854081c01840c50a84c00c84401c000b069146660b442c06400c1d004904e000310743d030b281d6061490354000c0a90507402001041180b80c021408100d021440503003050b0180b4001c036403c0320609203280700c3d220f00300c5001e17000468 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 196636483 1250 196635233 196635287
    0xc0512072904050303240d050606030d0905030a110d060203070314090f0a0204020a0207030c0f03052803081302060d06030204050a0b060d1a0315061f170403 69
    0x1c0e106495040c1201507910800101d80e55a600c142228001c08590041000c9803400c0041c154021141020514004681e2000c0b8081444404150b804484075404102482510701e014000d640f44160300d07150500f031061400307000940d03070440c2e001c02070705002c3e070000c1001d015120000f09140b402e40041c000d41d40d909214400800402003071100b04580d05c1510081080703da80441e0141d8003d184200610030408250208002903001100407000d6101d400d01c0003002500e014140c400408580840442c2c403881c5080545c14070240906c1c0348440313003d66000d4940042107e0340c200c020b6403d4641481e040e507030000002a042c60b42e000103580f020000c20002883e80702c82c1c00140c103581c403e0740c0510240d00d40354003400640c2c641d104182c0d4440003d001c00641200035a121440d01c004207a12480c1d03c0d1042c00200c0e040496000300118079038020f0040100e00c1c24204034415142030800070390704001341c00c00d5000f0f00541a040e03041c80141003410124052500c20900c2601102c0d03141c600081c0c000d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 196637733 1250 196636483 196636493
    0x708060f01030606060c021003051f080a1208071e030b1c0204060602030906041e0e0f040c060206010f060509011101020d091a27030c07030c061803120c051207 70
    0x6001d102c100c90142c104480414550301c189980c9030183d0f8060003424903400c41140580140c8030091203002ca40143d0003058409581d64034501004000c00750141c01d12103114100240204010950320081c01044418045901d512045803000400c5c0d038007003001007c2c41c40504601800000015503800000a5002c55410349401e12091589100715410481103640304016600c90044100955110206102c1045624421410040900f0b09101c0c0510600d840340c542010968013a2241c0389600f01000400081000d280c074254050482400180311039850014501d503031491900520003080030208015100784d00800062159181c540b00940d102c0750395207040e00c0106102a0142c070310f59151025005541d00e04030304140200c1c43d004844070f01100306014944040b240c00d00000b141c0c80304000340c400041080c400709014500c101e0398100814504000100000d03216071491400c80aa00310400006d40c045658050410907414825410070701420700508001150382808903030035000407100e040103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 196638983 1250 196637733 196637761
    0x3030609090305041d06030d0f1103030a090b07080c090d021c080a090f081203040312060e010e01061d040e0c0402040905060109060215150607060212011814011502070806 75
    0x102007901d2600042036543c441700d1a500f0a58205400d0f400c1880c219001c2e074441e0410408414090070b0003607465240424040c55540110f4100c01c0c6141d46a0313180040101507060581c0001044c40d0119060600c2c0003403601c01c1c440c0042c01c40c441c40401c884501152900c9100d09a500d5204480342c14004e003032300300070300070380d2050720309400040400002148803001d00c00c2c0720f0706666440005045a4120300b0707030341c40242e0001c0d0058050000d2900010501881400344e1006405012602300d515403500c4011282003070180c00c4030044c41101c03a03200d078105602110342c0d01c0c3d03c10116000304148540c0b030149824403ca03409600e030840d00010340072401000300e410440c010300080c0e982c602e0312655040100d0303ca0302c2042040c0111a060340114502d01501c0c6071032100c410f0300400b031601e4a086d40d5115002c0341e009500000400440d50010071400c01c00941041d6814540d100c1803180095584008400c000c3c140500f9081d0320303404a0001641c2c0c800c1282034090503440080b100d650800604460310700c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 196640233 1250 196638983 196638989
    0xc0405150909101512080309030c030f0c07061403060906010519020a0209130b42041d0c040509120307200d0e0907120213031707050a0b040303060909030504 69
    0x200e0074070500c40c400b040d40c50301e16000c1340c2c0780b014180038018172603850400d6540050301c080001c0c4014803d29409890034401042c0d242c04042c009aa44e80c45006018100f441c03d03408502072109100718102d04400031301c2181e501c00003c555246c895611100161414020b00c500d0902e510322810740c1881540d000210140c486000b10365440250385d07080c1d400e02d200301c2d85c100000c1c101944000820100c0c000c2c0c00e040625104400780d94280c4062981c0c9054801c42c07900040d440da401c9003185400541001e200b14282c0c00c10f1441c00814070300103540d03025a2060410350441c01141d5920000e000100c05010081c030b00440c41180d0743d0340c4c0c2002e000060200108940410b0104059200081c01c860300081c1c10541c030304151141d51003280301104004134643e00800b144103010740000b00c4001015540f00420046603d00c44060300795040d82404604005440c003440240300040043c01d000ca040001d012002c01d900c01c100440340ea80c0e80c0b4048024000c1640113803001801e00002c1030030150410042c00503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 196641483 1250 196640233 196640263
    0x4090507060306030c140d0b07110a0f150e0706111603080903070b0307080112030512090f0d02150a020318010207210e100e15030906071404080c0405150909 69
    0x1185032101c03003c021102d2224806d036407003011100114005001c1180c503e40c007220a09225090301c8600c4100f03400c01201c80c00844082844803c054101b00d0a80250030351541803c0081001020b0380a00315518140e6001d41014411640b8400d039001324100b003905640c05c298681d404d001d541d40d15281c01207800c840b840300d2090045460200320015100f0540740b0450481d42e544500b6480e25222030604501088160100102000040380c0f60301c210513440d004200c00d2004003400d040d0098200d00b0055240d400b203086401c03c0c054240092804110940c100c542d0b20001070b034030f40307410100f04c98801a560110406500100c2c02400b80029080003c0b15096114107440440110080c02c4130130350b030380410300ba03403180384034203818407051041407136030500013015100c00d10700d510703010015001d900200d402010340d034014010131060302e903ca21109110320001da91076061604107044e03c2d4643c1003c2081d640074075a58000540e4600782260711203850310020301041201c0c140038002546840007041c503101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 196642733 1250 196641483 196641503
    0xf09071e030611120402040b04020c030c070512030708040311030106050d06020a09060806130f1503060e0c030d0f11031207080403031401081009050c0312040f060513050f0409050706030603 83
    0x2e0408903c000c8401041c1c100c220390001c1e54580d820040201224100e841d0019800e01c00882c1e22601000101061a004001494850b14000410107503040943c1c111203035400c1440103c0000d51b03118259425660b00c540002e9150443d00c012038010505076021a9102c41c08600c9c940c01c0c02034590040c410a0341e659110b15016803078071800c2e0b4041e00161000c40e005040c810002525418a6004a0200d40c0305000070540503104032960313255403959082a91310a90f9005405000301040140c40e000c2c0d001580076107a0003e0780c0c0005441c220b1a0310f102424846110044418801c082c01250b0900001c10318402003801c080c0001401900100c41c2200400e10301007810501d0303072114a6040c101c8044000620400d030403e080720b8080d2001d010219040e105101032502c00703a40c10301c02a60305080b00c015181d1030314900000298038800561001c010f000c010800c2d0b5040310b80c480000c03825903c040c1c1c1c507026408054808500101102d06d0064200d010340c1c403003c140d02e07600d03401c020102c0e80a00e803c3d131 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 196643983 1250 196642733 196642751
    0x11509050d0f030f03111b0613030926070f0e060a0305030d11090907020c01170609010509041b080d0e01020705060301050405060d050114070f020c090f09071e0306 72
    0x4507890210140c00d411400c2e208400003071003075442d0790350782846240120301144c5c100140d5100e50807900d801a106000000d040f040c000007000490750081307030106241c002c030005480c050281c0341c00b8003a0018452a0150b00904d00202220140c007440f12002110042540c624100000007114000c99020713010032808a80036140c82040b030b1098a4011010f5803034520b08030b00a9005000d03036034417003034554000c0c480400c0c190388009245104103040e07000340c004150824001441d40000860300e03060b154405041c04003d403220103106054034810b5903100190348a03418050178214883c0c64258020303542100100d004d0034049050300e10f0910503152540803250580040e0303100c02142c0501070700507105000400c89807030603400007500500044d20b045854a041d88840f07003036440c2000703050203a090607030900403515031040b1803032815060303440900740812481001500f0070201a10649040f40c04101107218450240400402800e0040a4420394001c000307409884040c00d2205030750140c42c0038114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 196645233 1250 196643983 196643989
    0x30f060607020102100b01020705031212010e041a040f0203061e0a090b060d020607020603011509050f010203032e03030c0b09010b0a290d0e010506010e030a140c0901150905 76
    0x18a81c0140d05801401d440c5240e03c001d4802005801c48050441c826017074000387c1a1010311054044240c5a40041c0d5a000d00480a48000f50183d0001f040000d0300380401c0b0124202e440040c80c4501c0038007200340c003902d075420102600b480c5014007a505014200030f20040c04818a01d4002c1d051f0510f0810f0101c0d503860343c0d11710032104101c038060152586000016101d10309100030031030030cc0c401030035541800300940200c2c6036a00260011410780104c0720541d0a11500060700c00010081240d410210010701c100007034690002900f12400c05020040a42e08464820b4100c1d108000c9440d0310380c0c0c1e0a56a0400070b00c000035500065819101d07041c003160391000180911141c204000e040300449034074009450714240f002c01e86541c1300820a0000111440b00017004001043e800f1401003803400a0f10081d0b82100c102410150600420120201c4a501c02090075141203801100750303910b84441c0c9030118100411035412503400220302c4008103200040060142c05c181c016075550010325110418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 196646483 1250 196645233 196645237
    0x1d0108010510170708070b0d0510051503040c05090a0c1202040e040b040515270708070504021806040e0412030e030405090408120411120102031909170f030f0606 71
    0x100070b40d141903400280501408115145451181c1e0411074030515504c1103103a040000340e41051303030001380015110046000a01815401c03402d0090380c203103e01d00d002d00144000958880c003018103880400020b041c0804504081c0042401601c801c00034900780d0005c00007402c02080700d101045404075000d0380354007103100b500e05903210f0f4030b00a091a10340e03444800c2e100000500c02c641d9480340c1c4c84142ca0010f002600b0b280038a80001100c3c8903020640c4c5404a444101480c05101d54809001005000400a840c00464909a60050ba6809000300c2c87c0c00841100425640010002800141c02e04150800078031a0b80202c403800d000141e14001103083d2056101060800d5200b03120500c80c0c0d03d84003e882da00180300e286000e14060580c1c07032170740005074100c0d0250303000100e0040003081c1c0e00384a0141031140c8060402145145408080090341c04a4404078001e401d50796580307013040100102444541d40035408200381c4030b400070f65800340254802c0b901c2020080003c40422038a00740030003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 196647733 1250 196646483 196646491
    0x1020106090204030c050d1509061d0f100216050304080c01030b1503070305191d061e012309040f05150108030313060615091505040501020304140105070605011d01080105 75
    0xc00c0b200040d10301420412210500307c0140c2e11900c031146040e407060b080c0d100d4102103c4c81544003050411018002032546081018105800d40101406000844000c24804000c450107000181c40314500d002071241036411800060051000107070200f080034000540c60360000c0c00341d07800d12441e0028028891002c1d107131401c4881c280000c0c00420a101d00075044580e001503820000351000b92840406019035400f07010b08120030410418103043d00e03509020040d8003c602c12141202e4402a107042c1075030300414820801d03100380500d003441a42d5500f45020440c0d1388014200881420305003817441060f10344003003c451030310450b43c40704030108400034075604032014200a5403c5980b6246885400044144100d82d015500c0d9400710301e0711800354060f16142d00981d2850945820520070090081ea100f160005002d0300b400b0812007aa070002c12201a65851726905480c4840200140c0340c41c000d0901c01458242080300225914202510840286004c8412481507980e0340609038202d0701e00b55 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 196648983 1250 196647733 196647743
    0x50f0f0102040e0f041104020409050f070203031303110f0d090609050108040f02041a100210060509010e040201050a050408030a0309020f0108101211030d020105061e061b0a060f02090102010609020403 88
    0x3d0024100c9124525030541c0980201014030043ca00c501c00074040380c1c0181c111996241c1e80300103004aa04042904d240c0c06141400110300d54107101190004c14950f40c00010100a8400080d81c0080c07010700000449070020000c850004151000240c0100c0180c010400040c220038000100c6610a03124540103540106109a484590380c00b80400341a2110041e001e0100d164075a10385522414040700e0b5200c4554050030301211201d5190041c0c034120f5000a01c184080340060045160300413540f0380040d42400d044c0c1c3e550180c40410389090244d81d1007014540400f047ea401703d075416802280e9003a1007101e15100d00940303440159503180003640c040e107842c0040b20003071048440440c540f16040d8020740c2a08049010080001d162038207403c480c0300107035100c00074071100e0308144010b070404c41000310402e0b502c00391070740c0811806d001d5062071a680c4894889076000400062010078103068000d1010b1001d0001c00da10381f00a58400744180d801580f909600050510542c400d40e42929805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 196650233 1250 196648983 196649009
    0x1005040e15060c06010e0601180b0a0804030c05060429070801090c090b030109150e04030c030804030e030a0311070602073c030c151d0d140703050f0f010204 69
    0x8421440030380c584000c01c20350005030400400000f0b01e4100049402460000f80c4211a443d1120005003c40701c0c0b59920200000401c406101441014050b84c403180d613140f034400d10130390b903904003112030f10020701025006008080c184130500c44206240001d401c0d130300c140c084030300c0c00d814000f00303192108a5001d40014100e8005001421305600682a000b04900d000c6103856182d05000c1d10342e40c000ea0140c010503555401a150844114002400a03d07403401d080d1201e140a4401800e841071916005042280610004003054068185009102406001c40e60f1452a80ca00a00000d0200c1e0340080c2501c0b84240004007603200045640c15220210390201c00100324601504400d014509400050b2400003011100c0d4580503169a00550140030a9944e083c0741810700001243c4282200080000c10911207a541c5141040b8044543e000e032000c0da040801e80c00c0000030344100d400c41c5440e0b03001d030040004c140b0000040d4803c41394106415a02041e450b820303980d00302e1040d131068018803800303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 196651483 1250 196650233 196650241
    0x103050c010e0f0909010219030e0c03011b08060406170a031706180c1b0709150f030209090703120309050c0603010602070e0903130308181206060d02041508010b1005040e 75
    0x121a00b003071741241c3c0820025040c900d0f41b1102e00e09400e62503002e040002d54510280c44a10343c208840104110706030001c000e41d2800380c0b6420082c1c840c00403590180300400d800b149460311707540d110310300030320002c413071000206020300e516911040d80c03c20a400042140329a441030000700e0014078050080180010b490103400d00014000e010000d2079204018000c0c049400181c1441207066660235001025200300c6040078591802c8a0300043d46d80d2425450b272130103115010481d0446026240c040300c00b0106c3e540d400000030b152100523000107051550020a9020180d0945c1007100ca1503ca07030280d0b001240001c0c24000540802d100305401070303005200811400404d03c02054104040c0d9081e02e144c20500440c1c00301d0110680d0007142d211341d00140365258520301010200200004030384100c1a114400c030321642d11032011384001c4c41342c9540000e070000c41d9101d9000048211172040c00b080a156074040040c000c00554600d84d0003040e400203036101a40c490400c403802c1e80e884401c41c1c0e03202e1321 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 196652733 1250 196651483 196651489
    0x20a030623072001090605040c05090c030c03040f06020705160f05030a0f080a090b04120b070507111003060306110409140c0703180b190e04110414060f0a080103050c010e0f 76
    0x202d03035214240303135580d040c51381c1c00f08a207801030038460781c06001d20102030380c6814240300200f5401480c3c001c01803810700501101c0e03c08a801c40b904950000600003241c003443c10144002c0c402d520700101248a003000e000e41002c0f915900c0011542000d0403143d0855032072062688407503003500b006205c030b4411603003800012060005014031124600d080b00d07840d62200c88000741c560007500003079142084a1402c0d0308219142c06801d41c46580c40c40d0550505017150b0720722901e008070703400d480e104a00441401001921941c8802c00454005409010410014480401507030041c002d2104040c18661449608421120031034001d210540d42c0524010701602d0441d8940c518407007001d4258030748074000860f0302d1810007034007806490318400c032010f19000728040c1003404240b03500350083d401d00e012160380c07030f42600130380d0100c90b074030100001c2441600000035150300c1000042c002c002e401044034a811641300c4c3c1002e050342d128108072010026080700660b0107400715080103504c0400d0f413802070702c01c0c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 196653983 1250 196652733 196652777
    0x30c020712050307020d05030904060f0303052a101509090201120902040204050909030c1606020d030f021b06010f090624033e03010303140f07020a03062307 69
    0x240a082503d0038030080340e0001e242001b4044007903e0302d0b84007180c4100d6518061188000404030036045c500101d203156405895409030500c981d00b4000d400718000040455400d200d101503070710805a03200300b2280c0410398001c02000c420110f070749070b10300c4021034004080d208810220b41c0503100e200c420f07021000340c080a8403601008a802503020f01c000a100d440d82c211080c019074019000d1500c40f002101d120303107014403a0890f0a40d071a43e100c8100000c83d00850b40b114070100c0c07460081110300c0d44094941c081c0c070540b002d030200c0c010080395902c5903000100c0d030103050b900c48490440b11503585c0c0c1d8075a0141e403014001c01d5207880c0ca0741808a160044602c042e0030005542c1008281ca0040941d41410843c10481c2003c0c83c0101d1461844445a12088400c9852070f8168907800d650440c0c03030051407524041c040815120000541030601c44803c4140d680d0366500a150420750740e120f241c582c2c0513180209424035900344114040c0f210000c00400706201d503016a882c10802e0740d045041030585 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 196655233 1250 196653983 196654019
    0xc090a030f1b09090b1302010509130605031207170c0712051e0d02070b03090601030609050a060207050304060306140f091503010603140c010504030b0c280c02040c030c0207 76
    0x140c0b070b80e05100d01c0c2c501592240001441c0680c030019008103130741010b484c0f03090010030100c40440d0205030140181c1e04842a1101741d80c3c2900d2448075903c84034050700040507943c201c2541813103507011000c3c0d40043c0c013004018446c401d00c0c00500f542c441c0203212005004510310750001e500815005e000030100511200310590040d412550000e109044061007120614589c2089400c10200c100103e034040000600a1103e00081ca20710301e00780094503211a0306020052640d1f0300c80c1d40071411300c042001811602900310404540d1403a01c0d142280d0340354040e21410010906029000940300300a890100e010b070300c0500310840391028081040322012004084015114011040101a440900c1404040c40c40344000052180c244420b1070700d17050840b00e9031810010704100620000e0880045140c000042e030100c551644401260080c8100a04c03440e44120b540b000c00b5440942d91125003400c400d070003035808008100b50b001085060f201034000d0480580e000f50020460402d203c7c0c489045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 196656483 1250 196655233 196655243
    0x509040807150b09100f080a0b0a050403051b03070201091a0703030b0a091103040606050409021e01030207080a1d010f0509010c1a0403020a0b010b1801080901270b0c090a030f 77
    0x441d1143d40d0010f403a120068444490b07400034803c1c148801c42c042d8100700040c001500c02061442c0b4281e46074a0101c000402c6940f03040e0702c4202140c2058011070070795407107c004071141d0a8a44481c2000740e52500104001e0340001e5460340c000410301c1c00400c100611815803072007545808402d1704e0540c0501901c40140d40c02440406001801c0101881890008101441d540782c1d40d0409090640a8502c60381200d44114078012490b801030f62001070000c415552501c0d07000c1c0401e0b40e500140d00078002d05001804203c0c0005410034040e074083e2900d60064a40400705a89040d40d00c011107070124812000350100d0003c00010f0201c2d8016004070a40301d22a15110a20f50000310413110b003400155021005039015100c030f80c00308520465400d001d040d41501c2c0b60301f010b140b0644030703130340849440c4c0684c1440300b10800318a4600d030a400101e81c40c48160140c06d005103000c41540140b020011081e00c1da0044103010601c10031030101101e80c4c06400510700310000d07045440300d0350145540002114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 196657733 1250 196656483 196656491
    0xe190c08060f011716081b0915090406030b01030b0702010e0d1809020409020903190c0e0414060403020309041104050a03031107090c0315090504050601060806030c06030a0e07050904080715 83
    0x5410070130161020f02c40c01c1010340b10444080280000b90104801070036040c0345004038000c6210030381241d400c0c2c850840003220380c0c0d6a800090000841540b040c1d12070a44c0141c100074010060000040d0f01c2b038122072045e9502c101650303606000700d0803208031450b262015009641200b800520551140b040c8035440400380310302e90b540d581740ca4100e90055205101c0207402007503041c9146020700040020074007031200e03140c00426503070724200752080d10300174640412000004242800040c3d800d090350b0030030f0f034422500681480d0070081e41d25002035010a209038109403d0100c00072001e4260760031210f0280400d1000790039680d0940b03e42e451040410034a11a1450004400317190307010b842108003a545002034115810503141c402e24546411180304c040c01c03c41800005280010f40c13604640d21803500101c10b40b82c0c000028140454003143c641e00084c003006000e40d04056500c0120306100d40ca040b40e444540e41d00c14024140700c100ca01030511841482004c003c00e228942200403d040f0080001e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 196658983 1250 196657733 196657757
    0x203090c091311011731030815011404050d17030106090f06030603030203090918010204090b090132010e3003030105240f040e190c08060f01 62
    0x11021001210a803941401010841c014000c100f202c03221214801c0ca050341641e11030342030540c184003010b00702c07840e4800341401e00f011401948440191402e21801c425218400604000380f00c2e890031f40b001c105114080707200c48142d40c01135883c10307100318600034aa4146498103041081928085070203440c6007401d00d6801c0044040304005501822294030b0700191342381060301e403808004068003c1400e040c1ba090703003070001c0b94000088e10780e40e0404481040700c0d03917501c03150070b2400c60850003400c901c1d42c0046804998802d0942103248016020f895a852030782c4e940d418040e10304503882034000c0c11102d910402c103191032441c0180b61100341c107061500b1000d0160780031580c07088100c0700755400000c044521203207030301e00c3c202c1c400503401e0394100444c01c6504104c005035001403000c01600621124000340c00c0000d00d00010b89944402520001d81c581d03907140801d42561200700d0b4502070b0a0300d03c0110350515600343c07040c1c02000b88181d65001142c0d4481c4140f1100301c4c00020150706000744140c0403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 196660233 1250 196658983 196658989
    0xf070f02120d060b0f07060612020d0b18070b0a02010b030703021c2604080114012301030f0608010501051c0c06051602090106120e0109050a0615080a060207110306060f040203090c 79
    0x601d8a0213101700c809a480340c01e4100b61701240c00d02d4105902d281103a40d070201c0983c0d1400413165140750060280ba00903118514040e9034415403040c0685c2c54043c148000502790540000381880c286160000d001c0c03480c1900800d51900140d0000a600c45d8041c002601c05640c8510100c0d09c50348100140c0b00400c3e00280301c60300c010310324030b101d54492500040c00c0c03100907428010700400b01400380001c1482c0d4100518400030705003680061030705030300415103ca032a81c400d0b001588010301c43c82c5d080010640740c2c152240600805d0003010300130707a85881a40c443d001c5c56002401c0091700300d0700c0780e40b503c2d0400d4401c41e6980d000348103403054501d240c1132010240c2e07900c1c200c041c000e151546604482000d40d000b103100741c0d03000c8400a51a070345080905004540003158040c0019071141002984400545940800000581003070081e4072403030a1400801405074003c0806501510445006000040c1010b503219802c6038016080345500d6002c04041c1411b80255821207810800d49840d00304800c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 196661483 1250 196660233 196660237
    0x4090b060706090c0302151602040209130905060403080907080304050405060f0405070f03150e0f0603010e0a03090617090a03110c10050904050f04080a0804050c0907080f070f02120d060b 82
    0x2080c4c45009025004208500e042e0050740c405418040350b4508040b80310b048010505103026000e40a03d4000400e04115a160034004040c054130420030094285c950500640d240c4007240c040b40480da1810100324007040001c0c0b200102e1300b0100046141908010600000c0e2101616150704a402c010701c951050341c2c1d60048038426001540c81240e48039411030010b0a03102003000a00025294110501c82024010002e55212100d0748900640d0380301e80700441d0040c01c80d42a5504907018030b6003513000b0541e202c00381030100d0302c403980d03110700480c00d50400d2102c1c1441520741c1c0c01c6e1a4040c80259002a028040c1844103e26050680d040040c0d04404180f2000c2c40802c240005403000505c00064503085c030a490b0031a080c0c10740c040c00f0b4541035441c090b41e0f00c5a00400c106100c42d0070300080030010100039440300c5c0320014001d2981c074148008050040d0f4000e07122100d12007540c4000840d294460001c1603e4030f04554014002d500c40299a400c0d00d0303100100d21000583c40e0000401c00910381c2c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 196662733 1250 196661483 196661501
    0xd1a100315140604050d1e0c0611012901410a140706020c030d0f050906070203040915090510030203061014060d0e0d030c02010b0d0804090b060706 65
    0x2404101040c403510501607000c070700e4000b054950081500c1002e1a00c0d650260fa090f40c0c0280e891490070616428034114070504400005044d01d0303503442c40801c100a21450204070790142c1c40c1d1144602400e01824283c801039080c030030740c007154104040c0031008510003c5d10540e0f018100070100400c0204021200e610100d0115505c1242e01a12074018081100030609580b58554040c186030303000034001c220001e130b01543e900855011522005229495044030200b603189800c0740d03a14052620080301408443d180d4000040c908800200480c0011905070320880f481e030301943c03407e4101980790005102d070b01100c0903880b491750b00100d00b010b17051003041d00910f0035621058000d441c510401d413401c0401044002500c00c1d12804210308189241c00042c0c0c070f8400c07200541c0381c000c022090002020403030a8901c840c8a038003048801d85030140e001324410300b03165000340075001044080c8a100254520003e0028808020800c0880d40580c07044c00c2d014030041c00706103003c220b522000292000c40c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 196663983 1250 196662733 196662737
    0xd02041d071d0609060a0e0109090b0105091302060d090204090b091e1f09060c17060319290c0d0b0a0506071412120a0e120d1a10 57
    0x4a03605491040011100030408030b4000349202c50841000101c0202c0501524064100340f00440d1090307540d001940d011f0079013000c0000003503030365101740d0029014480042d44d002101c44004255420030f004031301e203d0600c0104c0c1c00840c45499082c01540d9002d032407404061a951a40400142c1e2a4003c0d19486400b807141401c86080601c086814070b8526207105400340840c4024116400c00402c40081c0c0140c0c0c4105546c48000d0b40d0071800191584401c0280341c245022180c4075150b0b0010180c202d01d0800d0700300075541da5100000d060351440c0d41d50040c8004c020341c410701000104612100d10180081c0014941c01030110a00a00111030170782c0c0c1c0d40d40140010482c0c0d40e503080240b149512910040b20806c04040c600004074850f07104000c0c0c06230024440d460180b0099201b0800c0e1040284001f140c0341c0c1e1120100c80e111307070400080e00c0c2152106d062055400e01c5017400a070944441060804880c07034084102101d000400e4404000340d20541141000d560a564040d80803d90b40526 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 196665233 1250 196663983 196664021
    0x103020c1e010e1c050a0903060c020d020f01060605120c120c12070315050d0501110406030207050709090c15030e0a0609140703080307120b10020106080607050301080c04020304020d0204 82
    0x45000e4290f6020060022050b40702c418503220310b10a01a0901d031444490828940d56031034100103c440311210380018003414108580e005869500040340c03c81c0112a03400c0d642c80a4038004010300f6500b661080400099081c4410921003002d812026080003031402e41c14903083d0340c0300c41948112400c50b40c440343d180c1e0105640d4400580d4442c140c4e0720039203e180400080701d854100c0794a04200d8014180201c1a48243c0340400c02c00358425141d864020b124582c40b85d40c1d402c8010040d5208070421901030090f42c0b00000c518242d802000300300c0342d00094281d1054182030300c0c00740b50071280e02c842c0b0406440e8428190854014008141800d00851b03011600404600704005075070862812452290b00c07042040010031141c0c01501d070092130314078202c180ca480e640d810801030650780034402d521000106940002980541c06841107801442c00c0d504d450380d440d90240c2d200d0100b4450840c050b042215000c800d0f241c82c0e0f008582c041d20081c071000116104d070300458100c500c5208071002803002c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 196666483 1250 196665233 196665283
    0x9090b040905161a040605041a1e0405010f031b0309080d0c0507020a08030306011d010e090906180307030203070f02060d140a06080a02010215060a050303030f061c031d0103020c 78
    0x5441d0071a22102c100130b0740c0c07904c0c06140000c018558401d03480b1751119442d110769480c0c4180c103c0c504841c000e0030f0346404804480d248001da0701c048d43c003610419010418603c04525054040c1c01108060042c601c20100340b84018001a4040c15200c00219040700c000c10420b06942c1c1b46101e1005102050380d0360076140c0070284144410300300503400a0429070300500412050340e80c01140b256400316a400c610b030f0154051303801038403180210034900742d00410200800844000005003a4444d010300610380c401c022000410304c0d12845004409030042e0410042d032404901060901c4140a03c090705080c03030294103804a008991600c40a010500c8010050110340000d50140201502c0d0312000745c1442c0301d81747d00103581e40007a022010b01d0f801c0210001078460361808880c00080c81c010702942c0e030f84c0c601954000e0250000302c880b5841032131003258468401c840e81c4440c03080380d940364481e02c080468001102101a001ca001e090416400308000c082e1081c0a008500312080c8000c070b28980701381 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 196667733 1250 196666483 196666499
    0x131e050a0f05010b18030717010203060a0f1a0c0c091815010b040515043317010b0d0603021c05010f0b06030624030f0402091609090b04090516 63
    0x10820304074005582000300600803a000ca02c105c0340c0c0040110b460400c1c0d05031010100341009059030240200078650900901049419002144145812622501951b03101c03811940401400d0040350300c0c61042c00d01404050b407011005040c00c084460031102c00003402000100b003d1404c455400421030310700c6a100003103108004848140e113802040102e10760514212441c00d001b03a1184500c6500c10400714a4170401ca2000c45001d04209160480c0205461703600703000f01e00c409020385003202001f00003a05a20b100d9640120344020304054040c0507460703d140100143c01c8000003007981941d88a0000c010b03518040c90341000b00c00852008101402820081e003100c22248207510481e0074040c064050ba541c6000316944843d044500012071094000d51103c900300a40305076410343e130000240211184a400c1c200e124610859844813295640c429065112000702e030002c010a880311000e120341880d40e000140c2c2c040c1e014100148000c020344540c0e00e23010703c9111080890b80403903c1800366035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 196668983 1250 196667733 196667741
    0xa120501140f2205010204030305070b010e16030e1e0706140c1507020a0b0f0610030905100513240c09030c0504020d020408010e0601170c0f131e050a 66
    0x10307400d201c0c01095280410a503401d031940186030341100d070140440501010441c800c1d071140243c10000854a494403858050250360180c88181d0310300c1409400068541c0d00c801566104295080c08421100d04140095010780319003400981c20303002e403c15071340c801c440144007608074201240c020644203142040c00b0342140244a088807445008010050a0000014440041300791822054030550b03074490080781000c403103480013482c8a10a9007888402a843c601160040c00e04480a00c40e010703800c0b1040d4222441401c0c0240301e60040054070303078180300303540c070856228002944146008040d59242e00080c2803180d00401074614a91904052010600c5120710702611400d15951450031a1640c90110541c1c0c41124415a00001c01c1c615114882c0c0617100180b1007040244607687d002c424680d00c44800f40901001001c41c82c070440754044000504001c20a00a000754030300c4000807041c851880c0850058001c0706840705000d20460f080703132561001d1b4002c04c0100060340d08007880010159 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 196670233 1250 196668983 196669001
    0x10021308010f1b020c0306061018090f0b010e090406090c08010207030c050705060c031e04050418020108060418031d0303031008061f05011107030c09090605090109050304051e0a120501 81
    0x158005c0d1540075250701c0000303545812540850b07100c1c1494034005000c8070441c01b002c1a00d003000c8400700e80099880500c0c1c1240c129035110000a000b990741714001102c21610b40741da5142d001e60780e60013180100b1900d0344500655809482906401034852901900b6640112421400920810104000d00c035083c000a4058007044404614041100c00440d86d24090740b02c80300300c2c01104010320540500c030036040f1001000d014006001c4014921020203a800000405a001c581d1040018040340b8091290911201c01d030500300c003107483c0580f0202c0d0180c0c1c1e03042040501c40314140400a150b0350400156100d0424130244003c00e80c20034500300d017803003c050060782c003803402185881815008c038860314060b540207207001d1906520301481c09190030020751000d006440270020228882500781c10440c40c441c0a03e1040c00180c5174200114200e03042d071480079205400600003070200b4a0815007c08440b003001c078103d14150310400c0051960702e0700d988040c000c0e0724040d00603401c0007402c4c0201104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 196671483 1250 196670233 196670237
    0xa0503160c0c060e0a0806062206260c041b0c1a010f06260402011d0901060e01090b0405060301090203040c03050f03041508100b030a14130c1710021308010f1b 70
    0x480c02e001000c291164201961006a16104030301c0709512507281d0f00c51b02c014540b070034203008080c0380c120702f1170341c0fa07010010340d654503009080d40400d15048c280120382c0f00c0100d07140f07900c0401010b030900329000c00e1195030455810b003d032031136040100010501c482c00b07800c1c0e0000b0094410301d40300d0090041c02c40d4000032888440002042c611401c0390f010400c0d84140c082c2403000507049805d0701041c0e2880080700a42d4051196400403603510340c8a2011300c035003402a26003800c2070780c860008492600440c80759030352184041005000b2220650055a0410300c1262040030460b140d60301c40307007049010b081100e641da00100e020008110b1500d4005611041420f046ca141d0428244000703100c1e005021760807941c400040494584c06031544000c1840c12024900c0d2003d060402da418600107103520300765110086428007003840001e8514907030020354881700400040d41d90100718000703500100911030080929403000208108280208020380615403800240507910109020901206540c0442 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 196672733 1250 196671483 196671493
    0x25060e0a0b0409020d02191205060d051b15040b07020a0e0f0417090303040807030b060303120a09031809090b0a05070c0609060b0a030c03060e030a0503160c0c060e0a08 74
    0x3004418200c2101c040d9a04031101684d190040340c400f0005c1c0c410320015203543c107c101c0429040c603178040079424070388070340da10b050105855142c10003030070f4898500d02408903040441c0b15031502881d002c1c0d900c1d242c0c00c0901014070040e100c8440e55100d03080f40d40300200d01000041c0410452825a0840003d00641c482404060800400c070001e0303004000d01c01800c00020400b20005c07510801c040c1d811500c00102200d940b15107552429403a141c40c1e12045401c112400081141c40c50f010060310300100400c03241c900241d41c0c89503081d018090395001a41808600c0d100c07900704d1550b0301d1094008c4d200b140d4012803841c152b0b24110340303500070050504950a1904043c804607035886179043d40460340120020556214070304100c00107049862000307a11500d942030010030002c1100f039510881c0c1c041c560801c05208034a00c09a00c9104103801040001c2082000924000e654102030301024014a4104405041a503822a034010250000d0003c0752003400741c11031500c1e158014001402400003e01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 196673983 1250 196672733 196672739
    0x5070b070804030f080402011701091e0902030c011d030d05180409030509040c140d0b090a0209241b071814220c1215090b0103021225060e0a 62
    0x400d62042950a901008000001b003019607200d000c4007400e0b03407a6200950120750b9651915801440071080c9204c1150303281041c05109070300ca204180c910354024016200c8000c40c2001124143c54142d4070f00e480100d1512403140a450400c14101030498030317101c02c0e0340c5040780803105103000b480080c42841582050030318000660b210040e20b6020105603000b0461603090401601c0c0654440d4581c41c0100000c030300c071011703540d05400c81142050306a0303801c1e06540b41c840180c8142d20403428401d030000300700b40a0036070b00c1104c030340030100d01c4130121802405c1806a00c0801c3d511074940304442210b9000f0302c1d090040c0c40c0c2480c070016010002d1002040b00c00a0202c100f030400c0b00040041e42007041c0204c802400618484074080c0403540040005101501d42000420401c0f40d49002c3d205c1144c400e4141e02d09503800d00c51000d83c3c0303400404403c950707840c40d420404181301c242e8581c0114000c10211143d1901c144248081fa40c0b00ca41d0303000003560030040000e200400041889104a0840c1010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 196675233 1250 196673983 196673987
    0xf0302100e031c021312080a0e0a0305030a0c0204090f060506030c01051201090b01020106051003050f151c0c080a0b0f070509011d010e4c031802030a0305070b07080403 74
    0x49419070a120801685a60314174562404030780003903010070000d0004002460401411400808244200b41c65161102c6048070a0060b00b0103c0d00000300180c2c41040b010313552600039230307401a00700d01c020302c00300d650300702036031501e0a04059a0041f0341042d02c6a040c44054582804143d0804200b0301c0c3c81801c0405924440c0d102e0b02061080c241140e5845803155640d9100b0740004c0003600e40980130415034a05a81d009005100884000c0c60400e40762021940006813244030103000710008150344440c0e058102c81d4480340301030728401c4a80425403040081c441c1000d0040c6080b25014008140710f500d01403940f15600b840050403102003001c02c02c00550b0b1a030704280d503400051071602d40e2400c18420f1800595082b80e140ca1055440851822825245c0c50929000303001c01c0d5903001210540851608221940b04500704c43c00d0050f14200c0e50b0709151442a8400c40052041c01100407003072205030082424980114025030024900203110410710889030b101c40e80006e80380c078003400d50745025140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 196676483 1250 196675233 196675267
    0x20f010e0705040b0f0303040312031104050a150e090c18030708070b071505190e010c080703020f04050a15020d260903090306190c0903020f09090a0f0302100e03 71
    0xb018402d9030b5803001c9018944520a51071034424019048a940d5912400d20030559a05205000c00007806c0403034240920825030244c804844000e00340307003001410200740c100d50301044906031041040f00b1151244c0c0707a0703c00030114007640700040c00980e02d0403120010b10584921075000c2c0c0c002d511411040128a60020307012085440320401a51288010703e0420300c800d06c2d51480991460402c3c082c40483c040c2101e0303103034074035030f540c101040040400314000382030311340003000e07200401d0000f800143d940d03010380c0080a0240702d24021925164941e8005800300005401110400700d01c040c20003001501000000212010307130400610136500d0311030320441c94003c02034000880e4000070101e0725020003041940c0d00c0500007819502140382480c9032000d51041c1c10303c914042c505003c114035240380904484401c0d40e40152440404480c9141407080300d0300090440c8449110701600040811100d0107100328403031182d1f02a00c1900720a2140740300f0307106000c05800041d001007040b440e070482e00b640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 196677733 1250 196676483 196676489
    0x22060b030402061b0f03040305060709082b050705010e0102071e0b1506040302042301060e09150604030f031106070512040f05010612060e0607050418050a0204030c15020f010e07 78
    0xc20391501d2481050302c904011414041c41c500740300115002c020008044ac440b4410210f40c3d441030344613562000c02030340d07940010781d40002039003aa0301310a00505c40071030f140f0541501402c0071882d190031395480c1801c407480a09001c002d40d502140100410040102e80b90901003130000426144403035458560b03407280043c09840c912103070410340d03040903101c890031341e001190020010450b00d0521461040410314840401c4192a8070f08004280c19000391011150080c000e09030760560354401a0603000141403c1905a2011041c0030000005d20f20324442d03001948641c0c2d9007030002e041e94a09501e040c8018101005012007840040c0c41091412030842c5c1c400e0300000440000111410020f00500325504010b40365038030b44450206101f141c0c1c10040310130ba004070446405a90b44042140c541c022406414031840890300506030301501a00b090b0307048200340340014a460342c0c0ea991808a0907a0380c2c4007440c0c203c0b06a51002d44d282d01800b060f44142c0b0000024451065000100ca444400ea40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 196678983 1250 196677733 196677757
    0x31206061207051312050604140d1709010e12040f210b1801020406020a0c120b0103020603040602090303041403011407080c0c011b0513080307050601090c05070222060b03040206 78
    0x100701c6560484149102500405000f100d102102c0246e040180d181c44c01214107680000c034141011825020004044c06079100315502c4000150740c902c41ea03041c81d50058128220356403941c24000c1c080605108420754400c2100c4802e0303840349000401100e0719280c0e070040c0c90000c0218000890b4800d601030207108180d00c0848014555181e100c0b00164001e91603004440351310100380416605d4000951013402401489581c1035035503900300f000860040d114000f044030200308010001801c0400141d504644210805400d015461020910756042980007104601402c500058103040c280b280c4800344984a00c0c001142c540030b04040c0a80e82c0140200f4415600000c0000c0107400030350040d121820b88000700740e402c81e0b0781701d0014419000a031080440c00128100058541d80c0041100c100740d030303c94023600d401d80c640386010008003880c60641003400302c204040d000680e07034982e0307400746038800182403441b01d10466010030448100d504412108401042840090380d00d5406540030441c2c08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 196680233 1250 196678983 196678987
    0x901230901140103030e040608030304050a110a0815010302100318110a1a03010e010e011406090103090203150405071e09050601090512010c08071b0609080c0d0203120606120705 78
    0x384200350040041140b0980d4000b1007900100415030f0080d0084c0294a08880c1480b2890720b40d58825107074841610000c0165000101640019592070f04111116400501100340303a590380d205581001c0301d019480790720000500046c4210314112000011407440c80c50100641440c0d03121244030141c616001420400e00380e40e06c0c0b141070f0b44010b052405001002141e41c80302c1402140c0a0b40d9400030b002d5880c01d5030042d0300100300e40d41c00381c00c01d070b0486520703c241851844690050000c0741c2d06c001c500300d04150300e0718654005038400708002c00302c80c644400384a044d46860b081c0a41232021942000494294400c144109200100303900c000380c401055001506441d00300058844140c590b11980d00400d0884a0b002503031410740c024413008481c1e85440f480c1c0d944011302240c0759045610030100b0a004044583c1c04540303a540207102c52481105241e10f4050000282c51918040440c00c2006910026000c45510303e0491015002001641c42c2402e060396010520340008008004400b00310b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 196681483 1250 196680233 196680241
    0x2030a140601020a0f08190201060f0905060612040501060b0f0a08010906141207120813080109030c110f0405100303020f030a170c0403020d110405150603010611030f030109060608090123 82
    0x4903c11101a02c103c1f9600704244803411901a002e01100d118090340220b02c403400040002c0503004051051800074162458060754480310400d04201030820b4a056503140380210f0b0400c0c40000406420b4140f690303a076160060494001d080c030405070050060f540c20700408100d400c9001c280107160050485450464915071004030340380103410380c483c00b440e03007902e21000280079000000f0301001071192000700b25503848050940c2a40c4480300018001410614038002040c41200240f0b000f98004280d01c81c490382c90380004003a1141610700754040c24802400f0010160100003003000541054040d506203031a041002e021801041c0700540c50741c4802c40018111200c0208980195078000c040c0358201c0030a0404840c50300b4050f1405000d10310703040101c2d0814454044407041c5003001040035185a08201045a03100024030a4010500c0107015200030700109401860190a203500c000414a182c00b400600101b80680001c0382a450810b401c15412048100303150240c2c0001040840398072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 196682733 1250 196681483 196681493
    0x20702030c0405070503071206054b0f0409020d060b030a0c06080709080105150f040908070b04120f02100504021f090812040807030f061e02030a140601020a0f 70
    0x74001189944203141070200052142c001300618040d6980b0b51f50b107483c0d443c07a80d201604403041c1e401170340c3d80203a003840ca03614580720482d00740000c0c40c000342001c90000e20003c102801c20052940004000300c603880741801c07a0814010410f20040c049500303112030030280e00400c1040410341c070b024107055100e181c1ea0100740c40030415101032950003080c40008640d1840f004152442c1a144000000c107007000000700c480050060b98081d03018102c1201450305101c041100c0003101200322500701d42c035103803140042013242c0d000d480070300e000e0054080c6c5881c1c41e141911307000070200b001c481440303c0341112944040d80050602c80300503e5840004407078890380002018154000342c00360054003010052400d881d0703c83d42244c102d51400381103640404140860701c2c80e03800703140140802c0798030a001c1000400c980c0c0c000b59030028000d41e0000340c000701c404d2018146084210a454a03590000188204440310344108154200c0d15040c40115042c1440001c0d2a51484800501078031358400040307003409 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 196683983 1250 196682733 196682743
    0xb0a030b060d17030c09040f23040c05120c0f090c0301120c0909080c010c02060108120f040f030308040302160e13150617070b04150c0f120528020d0302070203 70
    0x1c03c1c1c1c900a6922403804920a9005a020429050003603007421035000c00400c4900900040707500035112201248034451060460032801001a44d80c185142400140303504d0708989554000d0540c4040d009200d40300c4244032904812040300d070b0142c030b001c04c20028411039140c00e490640f4240c980c07041d0440803506002e10031040d00d410190015140031085010002c1450081145081103070003449602d4204601342c1c4c552400f4071507015150400c0100501c0e04110100519800300001482130030141c95007000202c0300c403150411000306002c0c0d0203010074181c04001c1c140000c00000c0b4039036001c0c0e08060701c81080d0032010b001d4900e00c0c161031a260080204001c595408412682c0040010595a100c17100e501c0040e86242d00c071502505501052014006044409032080c01c0e44094150203080c1c4204c4584c2110b040a0310446128600ca40019001c150014940c1d040740d924945c90702180d030100c842d082d559100140300e418100000d01d83c0c190b00402d4021141c0014140145c0b6a02c03d400802c0c10700c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 196685233 1250 196683983 196684013
    0x60417010e030f09040b010905010e0f0406080a060920060a03020c1908030610141803030d05010803090406060c111c060e071401080708010509040606080d02070305010b0a030b060d 79
    0x240404560b4034072810b0f1031009046280422039061001c68141b4005680c5031115000c0d00f40041c400744141c2406062000e107100303100e40003410008145d42c3d2904464242501058201c0355036403210100414008000d072801480c086404400c000d50304164005805842910400002c1c140c011a4040351581e0070f200c03099201c0ca09036004c081404841c505654103030302c1140e00503ca0000b0000b491001d9101d260300c0c0500440c6082501d16001d00c226055881c07030032140c003159051008119000c03000f00c19005003070082030b0034002180c4521a0004000c19070710140c00401c00c02c9030801c1030b00c010602c8a1801d6011a0b010f994114407442c506190354010f0303c815001600e42170920403610250100000d00d401180c0c03140c43d451700030300f0804004441d880400d80790100012060001031096148c000d25060f0064400c4000003000e40d5140320040c107060400380941d0140e0400b00042060001c00c0c0165010044211410f030146411030351034024841014284900030301e8a03150760401c0100c1031701c502c181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 196686483 1250 196685233 196685261
    0x20d061d0708210405040209030a050a0804050f0105031e0a0209060a05120703020702030303040303050c070b070f0e0301060f0603020708093c0a05010e041d070501030501080c06041701 81
    0x111840c600c0300d640d01d405100350071a9118080c054400b051400c481c01000c103a500300c10038901450f04c01000060742000d00100d5050281c0000e0900080040010a0000b4402c445070743e1200d00c0e040c10015806c0310301c220305040c03103000c00800003030074111018541150740347d0800264940710303030010b4002030044904a54101d50f00040941006070450054200d210500d203d000c03003a5507240c0c00b00c00740d0088260007074041d8000d001003000a40290010b0390f004005013482401d00b202c03612503c00d5003a058512902207800001a08141d40e48807400d03250b0b0080a8009201c3c00c0d280600502c48005144a020201036020400a0070000028112441e10100030400701000d2020020032001410341510705603647c11843d03407104170104400e80c0b00c0ba580402030a0507882c03403600c3d0040d0b80700c107030f0256400d605c140d440b183c0000010800c01d070340c460360715008002c005103814000003604440040e00224800e0340913000b14441a03640100f1641550740c0404603010803008074640f54050264100d410207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 196687733 1250 196686483 196686521
    0x2060307090e1b0720130b04050f060a140a0e090c0306090a050c04050c07020d2105032202010909020f030a061d06010503090a050f37020d06 62
    0x15039622403103800960311500080e0340640c4901e8042201c04541181049861100788034076400704101c0c010408065120413900240e28003030000003507651601e40803e40c0455a104607109290610340304242d8031a2481d084044181055400242900500d03c2860307030001c007203403010782c10380c54181c402c000a2580c06025185820242c90040e21150240c0801e4002e1144600080141000051402d0100d801070040e2000e00b090000780070140000900e40d01125408000c4540103848400750709c0407030b0f1b001d09415003014400f003540703440e4195080060801c016003482849401c100d80000e4150410445490514071030b518401a50042a2a030000c40340c0c51002c1400c10307986400100440c820300205000b00201a2210580c1c030441c151904002410800b110009a0329400364000b9600b00d07541000310780c001040da03900c2c540f03080006407400c07005401c60728115402100300441e48403a2a0b13900d015010307120045042000700c3c0030400000e0f01c10640c2e2107020050051035401880c581c080400016 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 196688983 1250 196687733 196687741
    0x30f050102120f011505031b07120801050406050f13110703020c030706050c0c09090f190b0906060105160f0c0308220513020708040b0324090103030f030c0309020603 73
    0x20300030740003060312040802c64607001030184241540004d060726440c5210040c8030030b0a11088031103410042c10704800210140c484815101d81e00b01600c0504d120f2342603106442081c08000300901010b0740a42c2c000c0e424584144101e40e10400c000710107101c140c804003600d084203182d640103001990580f6044c4d030000101941495404a2140310024050f41214081036846c00c0465140c1309000036901c05030421200c210662400b4807041c0e411129440c100c0740401580b558032801c0c5403240a0103258440490f210800304a410710300d1903031004c0841c4c090680c40c07030040d0019200f4481c1c010081e4181c2500d0030010104224400025080d0340c200028445094403842d10755425071081812030306901c1100054940c8001f4417852200780e84000d085e4407616480d19140b031019420810f0100da4002c414480401c0c40c1120380041d51040c0407c00c0b12107030308d8800c000c03610841c904081c0d005000d04038030340042c0b000c00c0d0401e83e1040300e0202d070f14002614200d0468100c0041c800c84c0c000a41c4444000140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 196690233 1250 196688983 196688993
    0xa0b030402062107030b0303120a05040311030a030204060801120c03032106060314091605010c06140718090902030a0b06060d0e0606120a1106030702030d02030109020d0605270c04030f 81
    0x1039445035501d901c04115203a4048100f690f2381c0500002c0410002c000400074151150f980c2202d6040f901c20704000001050220900d4110303049a4881d40009502050401455501c00400d6004211f4440d5030b07110206152a81c940340c0c1c910380409810f000000051442040b20b180d2111000401c1c10300400103151a500014040e0424841c00380725020a0004106aa000819007412644206c00340c000050b251000544134040c9041d1f09072955a82c03008810030f00707554180058841c907550360303c0c1e40130100c20522500b10341d1061341004c078203d8038001c2c00c4801a100024040c0b03d40703400051481507569540300140c2144034001c1d034a4201403e00c1c0001d00d10b4003001030403034081c2c401140d0805850040034039641c0d550485600c050280e00202c95070038541c0c00c000006540054031403054070301d4650220b603000280e900a0348900300750369000803c060741c0b96141c40340354090a000c5071101303e074030400800c0c4c03a10645905400d01c01d03000c101c004030f024048104112001554002c1212440005078104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 196691483 1250 196690233 196690297
    0x60b0c0d2d0c0b0c16030f020a081201050909060103050d050304060f09050d0801140d080c070e0405060603100c0e21161e081903031104080a051b0a0b03040206 70
    0x2085410789905004141ca8116000955042001c0028825121407240c0c80446d944c0147c010b542040d40503804200000c591628001c0c0000425441d40100c0365241c4070910010040040c154125a001903005100054001c5202d5502800a00e030081d1283caa81c100791000b401d442000480e02e030b150041d00c40c00c011012981e00111929174554441a85e6504110f000d92204106030700d030702400d40c000310300c000350345040a030801d28294000c64881c030f80c0700c3e007401c0180101a074003034a07030b503000b501006900d1030300300304c0c0410f00a403c20080c050011075940c094400201440300a20801000214226007141060403402c10000c1c0e1048403065141071001401742c0d01c050289201e4001c1c40c29400d41c2e060103214101c001c071480c240081803c1e40b1000c04140c0701c541450310440070075455140144914091030003410203046410301600e1801e005141840c50700c500c0c40c0b040043c00d203040300316507000d95401d10304008032134034580c00175034a5aa610005030340d403181c1c2e0300d40515201d100226042845000b09 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 196692733 1250 196691483 196691507
    0x3090b03011d01140102151b0403150e010b181f06030207020f0907050f0f1606020a020f06040203100c0203040902031806100b0304020d030507020904080904060b0c0d2d 74
    0x10210500e0744c8030441d40c0c90301102008420f0142e8840c0101c0d08038001d02c1c00b01e580d03110265440b0000703400319244181a050780103500075103610b403400c46a40801c020521900d8040851a40200305074002080803880c2d041c99072020000c0d10821074005601c041c1c82880e11070304c51010b429070032440d0b41c454101400940160500b607000b40d03010401d41102c0d003054400d041c043c5c001a1540760911035030520180080d400a111b201089505101d903405401070150190441442404003503221205410020f1426050885c000016403040080c000540c0780400c0d5070f48451008100424041811402649544120303800180702e9803000ac1044001000c100c4140302c4c0c00c00c0c80c42600c0c20780d04c3d282800701d01003107a4007410311a12010030115005185c11180004164401c0c18020b00b0901c140d0002600500201c40c00e881c401e80005030b04c0c0c01c80c41c01c3d206480c080c04403607d403103080940c201b44982e45c5282003141d04041c8003002d188031600500c202410b080c003004240801181e5003240e00010401c0d45507032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 196693983 1250 196692733 196692779
    0x1b0c080c2b03021507030207060e01092f031204030201200322050306040b04050105090a0b0c220801020403050c040905030d150f17060601260403090b0301 68
    0xd00003200364944030800c5045a02030a8220441c229260800c00c1140c1c108202103041d44039044004030a104104030301482006175450050703c51102d400c00c0e9060360400580c40c03060b6450314117540700050740081011101d2113001d00130620000740d920842590103c414040c0e41c507118843c16444010080002002035038030030783c1d801c0c0ca480654291107903040001600c2c0c9074a07401c180507101e400d00d00150302d1a540000550300d411007030b075907101082c00c2100030f960903a540c0b59203c040000340307c02406000e400050490007004603001c140c8900c6007083e0301415a0248400029580d01200309011100e018401541d9202d06401c1c1c3d5030075024000d52142c48121a240100070300705606143c144521a4804d4104018510b000b000d025803100800004516106942c07021ba404034200c290b640f00d2101611001c40c03840003074030441400510b0f0a000030512810000c104d501e180c0b01c3d000c003094500d40c4044141b4400e10940340c600d01a0382c0d0b0300c003a070410a0500d0b800300000414080000313800141c03544034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 196695233 1250 196693983 196693993
    0xf1d0414011418041509080a05030a110a0f1d030102030702060a0b031203010b070c0b0a0c0605010b03010609170322050108070c0818011b08030915060f010c031b0c08 73
    0x1041c0003081c103890a1003e0091030800005000c11014445004149081280007511054035a07615007250400c050100000e80d000c0200400da081502c03c070800c407a0400000b030f081c2284030070010003124017010a0400c2000f1890004c94403480e01390070408165000f0002c1d926864101c400941d1485e0441c0e407030f0300041c140604996207080125101040300d08481013240b8681c00d19041c4940e9070f021403012030b1445107034030000a41c03a5803140a0425600c3c260b82c0e05000740380324141282916410303000b400408104100400415800c040d00c1c1084502038041410b9260b030941456055000320b010607090f0181c50801c80d003400080400d1442616800d80f41c9070f141e0385036010115541030007060700030110b88040115000b928221000102914014902401a00340b00c100c4580a50501c403422a10050042306010b565801031014001d00c2d05110450280c2345011000620013500e4a452036060040f0800c000e000d26109500d101034142e400c142ea0281d1a00d94070b4201c0c40088244148802e40c01a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 196696483 1250 196695233 196695269
    0x212040302012403080a031107060618141303031503050d18080a0215090d0804080f0706140d020a27030203010b030f06180304050907020601080106090c0f1d041401 72
    0x200f90042825280c000c00c242e0f050a8401d41c0640040c006030b10600180b4005001450000d045400f90b000500b0000064083e641c2c4070004040949600780303960100080058204118900b511030351840c03480e0035260100741039604048040108506070806440750081c04c140c07034080d1760408015050018000c603400d07045907a40011644401007400004e500c00b00e28241d81e5481c9111101070a04004020442c804e03c1c18592388080c510f40c0f10381c0c06450203030051007440002140a110303030402090781d42015010718003000240c8201c1c0c8a1000c00b25880c0c0d40c081010560309218154100e414a880420030603510031021080c241c0120610049103e0741c03c122100c02c00381404103498041c0500240140400e40366000e01c10007011081c05403420300d101c20302c4001103aa9521107018003620207030300035002c55410409040c0c04d44110741c001c1c1c1815070410f0f151605a0b030340715007210420201c1d40b0b880c15070307280c5030a007030341c3c0a0080016099009040c030b0010b01da07541d901c8112504070341d603c41188900d010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 196697733 1250 196696483 196696541
    0x1d01180207020f120c04020705100b01110a20060705010b120c0609090a0e0a0c090b0105040e15120f010e2103010512010b130504050f01060e0c0d021204030201 70
    0x451090000c1d040001d10f400c40005080c0400e141c1c80c07801408041d00c0344005800049001c070b0300b21200a039901d0388005402110441a440742010b240400e01e82013071140940c0001b59a50844000014280100d0800301c1160070455204015100f4005004ca82c0d5003c45082c00341c06004a01c2c0074520a641030300100b0a01e8800003122002d40310054001070608186008002482c030005100ea00007503110741410161360028411820054803e15250b822f1034241b1400d8802c98640382007141c14071104200a1003402e00c26103d81e40d01021004c14201c0007990000811850200d600321034a0f54421200803043c0d909064000c130120070a00f0088030440c92003900e211440020140092040000810041c006070400001041c00b0701c00017000410105000c0001c60100c80e201c0c09075091055881051100f0002c1c14091001c0c20000c86000b07001d142e09111400c0712000c0c010700b410001d0040000e01200c07015464050301c907002a40c42880065140c20b05000c0d020300b20703080030340c45000703141a83c001c8515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 196698983 1250 196697733 196697737
    0x10602010c020f0d030c050c0312010f060e0102030910030b0907020d1202040302060a0305060307031b030b0702151503070504090809040506060a08070305070e03100e060627040c1d011802 82
    0x800140314013205554144c009080558680041190800400e12010000c000400d00b40d8007000081115601d0305405960001a50b0442d0080100401d0301110980e0300006451250800300e03030306c0c1c41d49070100308190024610014000d40010003101008961500440c0411900c140350700e86007105261015110224400d42c000294822402d21456604500c40d41c8050b40c004030150031180d0058494664200c084403400c5201044114504180200842c42e4030301130304a8174900042240c10f07000c0051614004c0300403c44c0c001d00c1411424440e80f40d90410a20f0002d000143c410050455642401c0e5210b0780141c8403180120f0801000c02d940d418190100e640c08112035864200540704e50201318041c18000e440c3e00104a000429400b01382c1c1c0c280152403607400011700c0042c103004601141c2c1d0500c80000c000c54071804590904036802d120540340312001d00030b1180500550380d6240342040084040360442c1040c9500e1401c2d1002d0190000005070598201030006044a031036503241000b0381c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 196700233 1250 196698983 196699003
    0x9030201091103240c0c06010842090c13150608010518070201110409150b1608030402031612050c04050c1206151318050402010905060d15030803010602010c02 70
    0x80c07613030b90014aa100005155464201c403164240342d10f8403103400c410500c0d1284c02c2e004040c050300b000e207000080110443e6a19500901503503041d11201c84d054100c1054800c0002c0007131100301c5500011900201032201703026003103005110340c03210307000350711548024851100000306114411340f0101e0142c0c0100b0301c42d4101c8800030400400840d0080c0c140d0074000b0302400d00310079907480b9602c0104a503511400f40c00903064405002079a40c0550484484100d516031040328a8102046184c0241d03e6480034650b499400c080d046542c1d48403440440d00d0109480401041800b04510104061060814581e4140d0060045540024084040004650040d5441c00d01000200b2a65503504401c14126034003ca00a02d039000e2005140320000555002101030117802c800780710305101d80582e561130030b0001070050108006a00d40f90340068500c04243c0540f9101c0c0f00c012a14145008480c0c010960380080145a000e149a0342d15140141d034000707028180255017402c207041601840040c6c04001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 196701483 1250 196700233 196700263
    0xa1505040506100c03090510030e010c1404170705041805122a03120a0b031002040b040603240b030f0901090b27060c040602010b0105211909030201091103 68
    0xc40d8007040f5007a520081440c3c41102802100200081e103540c41c0003074401c0103105510b0200740c00c4200c2d0185400c4688202da070340c051001414030310301c001030400d040d41d0030364503a803500c02603e211903041540341a100d50312040e03205060401044000c1603918200c01007902c184200c60b000d81c85c20300544202c0c0240c841a414802201201c2020606010034400b80300724028143c9180026014a545a03600c0403200864829100c4000c00243e082c1003011202c0002012411800c281c1010700c1d00c00d641c400c6108180070152282c003a2000d4002c1c6402d0407000f088250b00c1d04104664440d90216580c000316441e10b105c8881c1c2000926485042c00b92034030380359015015104a0745c0c1c0c10500410034040101001c441c030700d51040840506010004240117a15640049884a240c14030090a4415500302c1504000342441025a0010b80031100e0302c50b82d0440340034500c96600c082070080052084041c04038001d041c442c4000c2415010360210345418011001c0d00909000308040c19500c20b81801c502079 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 196702733 1250 196701483 196701499
    0x70c0e0705031929010816080c03060406170606040f021204060c1103130f050307060206011502031615060b090607080c07120302030408010e070608040f050c0303030a1505040506 78
    0x20071800d84607981d000c03803c4018001030354582035061220240440d0030241c00e4441845025402581c101c80010ba0100410410100300d160070000201204005000c400800d4404008120b036542c03103411801c090050380c0b1400d0b20b2800d0303e911159a41c0c0040d1100c50107a07151501090500015000326850800014a000340c0394881e562090010003424084908100400841402e119400c0c0020030030741400038022104203007000003440640d88540e000034401d5028000410041da0040382d0241110a0302c10003c0b81e9030f901800c1039080d8440c25050504014101e1104002c004002034101c915400b80306040015580300c1024002d41d20801140c90380c001c0c001e000070000280c0c000e004044400619040e0b884e80f595850420420911034602200543c1000c5018811a20f0034482c2e01d2603d10808002d10308245407200240440c140500081c2038441624210303001e100b81040f6004414401504907592450718a01362801400403212940e0240c1d400303400082c1c00d10301070203811300800000381444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 196703983 1250 196702733 196702741
    0x8031b0f0a08090a0615090501090b090402012d050a12090c1e0503011a130204050109140d120806040e030306030601050d0213020307020102030f0106020a0c0513060e0c070c0e070503 80
    0x35420020041c044400c3d40300710910580007800c40c2c0a40050f03026000c1c4880b20580c1000140c03c26503505800c480102494002030b41642d54904004680240d02800e280041e101c0500000d41546401801003440311588100490319a600100606600400d50746d0740c441346422488410070f5030341002d0080d18405c1c035008148092104142d041c1d00c030b2200c9102c4111519075403400710b425542d096011500f10000340c810440030341400f0a00e2150640801c1d0118a004e00f001e001070400502402066606408500484001d8980c1549081200c3d080700c070714518044203290040c642c0100b02c2e103d901560a004005400030b10000a076401120000d000e401d5a038201001c3c40800c41c00f491007681c2c4006818090403007800e1510041d4004c01c00d43c0e0001da543d24041c9886415420103a03c0003085502103c58000402c01009010050360340440d0a440308403603506e401009001560010407040c0b0f40d010901c0201c002040c020700c025441388034103075003090752a411000384040444143d070100340100002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 196705233 1250 196703983 196703987
    0x90516060e100f0309150b010305070c0c1404090f1b151709031209010203041106070312050612190b01090507120905120708030f0f0903070311070302030a08031b0f0a 73
    0x403c4440c0e2454001a901e4068071480e240442c0c3c1d005c1c45a8240d80c90210b8521960306002e00d82d40a6010305100121400d15629241465a207100e80b000450300c84445640da96a1a000803500a802c03400c0daa6000289040003607c10b113003404880c85c032181010000480145c0ca861200d25003c1320307111b50844000702c6c100760840380002046100e0900041040c140301d500c245404c58010031242c400182c0702e103041d183ca8403a107007600300202c0c46080e09000c0303e030000341e02c0090000c030b0320202400880d03151550703004260b00e00400c0c0790b0440e00e800f880f1510500300380b048039060315080c000c11001d05581da83d14001003c5800982d04880040c601600d10311010015402080c01d0601c81c604948100403e02c1921071541c0081204444800000043c40030310480c000706c05800c0200b1205000341403c0900b00f01e80d50380f00d5980d00900303002070300310310a65012080c0442c01c01144c0142c2074607049100c0d0300d007000b0180e20840d00214031050364074400c9200c00340e140c280c0e115071071990001403400c56240b1003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 196706483 1250 196705233 196705247
    0x60909040f050312090c010513180f1118040e0a020603070c061a010f090b0a0e06040b04060201150906150c0809031209010905030a0206030a050c0706090516060e10 72
    0x40d1600c210900c0a100042c108000820750802c01070315250060070b12104036400d00c0b50440c03001c3d04001e000e0191103103d01d0390382180c03400c8582480a00c490903004802d42800f0381281801d000ca00c914082d0591650f01006c002000203c0b40d11502e038090070501000c0004442040382545400d6100b00200001800c2c4000195000101801c0c04c02c0d05400350340d600002d450310600c2241c40b50041d4549805a541c0010030100b0499071424116002030400c0c4604005002d40e08460342041510b400c0059140c6804040b140074141400b4016134807615481d019000c6d1400c00c04071703600c10920032000110142c00e03200d0031058070103c6c400d91003c043c20040441c0c14104401080d500c9032070070030050f105582d0406c0048a01140d0920f065203c0f51010000742000140381d0080e4002c0d048100414016075030a81141e601491602c00060503443c2d80e1052112401402d02c01402c1614003100d003401e0003400603001104103256001c0ca90036944880088418042c0f004400d0740100019000680b00c9008482d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 196707733 1250 196706483 196706491
    0x304080706170402120a0c0f0612140c090a09050c1b03070c030b2203020a03020f010e060103020409140d1e050c030a030b120307080408100c02030a0c05070504020304060506030601050f060909 84
    0x1044504900294031001c3c40c204448c0d00c4080710000083c410406242c11445100d490307900120108034030320341d038454912101c03401010302002d41c10028a0799415a036020001000d030142c10f1081009260420994819a00100350032201c841c2240e03c143d0714007400804c4130400c030344c00707118003501c2c030b00d9541ca4602d210b20103000c141c02c40c1891803a4030302000d9010200340c2120b002e64010304005083d401e001c2c0c2001c400c498424103030303410901803c8000400080307040c1169815140050310f070040303041064100441d405452032600810010a118562100100d4000407040f15141000540080c0c140d4a610800c00c0c04011034200b400142c2d00c46020b540310001303c0c08040c003610b404154964145003580d10485040b60314450101d4180901581001440e03600903030303c0e400b0405c1c04c5010340086d540c0d0003171520b10380c01c001d15007070744604110080c403040c402080b01400035904c1323090500d0709001a01e4112480707030007131048100002c1c00e403500d44801c1518440181103141b030b190091051148000c0014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 196708983 1250 196707733 196707769
    0x1905030402041b02031c0204050a03030503090307080406021e0109023d170a0506010903020904080c0619050f010501090b0f09030d05032202090a020309010b120304080706170402 78
    0x4080d14065050f80440c80c180b110850307001c0e5a480c030f50f070342140c0c1514100854052003070b1304c1404103001c00d455100701d12083c0c03509424655280da132070507503075403442c414840010113450300072400041e03560300050007145654001264007800030b4200c9001e0308840c140c4002039402600e142140140741a400311040148408a0201002c00d920202d100049001d06079110001985100020b0020f0aa411240d03000502030070140141d05080c00001e100303400601001c1d10520050703020808020b150021030340511030304007d6605605c8c10011a10401c0c4c014820251140d00340f000107080604151182812386205854460300c0310f0910b50011041d4000e007004040d00e400401480003566410000000b0080e00d40c0d031119540d1800810703030f640002c103803a100f068080d902d058004c010303600c1d428616441000388078010b07125501c02150f14054110110860f0f00310180c52003840094602000a0050310f012030100c1d0402f941c1c4a0084030840c4070060400f001c42020000b10f0010b02d0030001208011203c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 196710233 1250 196708983 196708991
    0x1090608070e2e210212150105130f09061e15051204080304020a0b0307080705090114070f03030c0c0c0504020a090e010f0f0b090d02210a0515010803190503040204 72
    0x810b00301c1804a460070f40c1d5000c074050051a50315013440d401c1c1e1a8000d03101000640c101906a2440024000040d01942203407042c0e98603400e16900c10410360382440e40a00558007444e64454500d40840510700800728102e0500030007003403091108522003a1034280306080c0b141c01e031403c0b041c6031100e4030104041341004000c000b0803102814010f00c2d14061801032031210380d02e060620401c1003080280c2c2c80043e0b24207040c01041100394114036441e0340400d203410825600d803500c00c0122404410786815804c81c0714042003100c24002010b81c48200703d4841d48041118100070702c0207a80300180c1c400010915424a501401241011307000b400f00e1400c81c3c1080b030f407000d80340e000400300d200c8240c000da1030303400703c2e10b8041240c0c5481c0c008020041c40c00694003840e105200c40481c11114910001900a101c0758240030300d0209082d00e050714003c905000e40b5210002032400940f0f45d41801d8485481c0440000003246020011048544024003000071428540314081c003a22203410041c800c0c2da1103969 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 196711483 1250 196710233 196710289
    0x41b0f1107080328231303050a02040f060f12170304050d020c010c0305040905060112020d06080f061314010b040c0908060a06300606080c01090608070e 67
    0x104034080103803042d60041c40e01c400c0d00000348001001100022401c1c060a1441001400e4011003003042d040800341080c011104070f1001e859080c41038290700030039441c0900c0d00005100010442d00f00181c0b0032102800b070501c108120314191481c0d406038925104001008020b40d41c01031308104038207842210001401859021811015001124280c546030442170700c2605c02b81e8184081d00c0c01c000f017405c111650080c1c03500d0081140c013030f0380181003603281c2e104042000c3d41c1c014104000174415100055648284040c0b260000e00f2603441800da40c0e2044aa52302090341010039024802c0c80a00d000140340c4000d034444041d1442100741710007181d540c4044400d080d0721180070f0405100c04c40e48404224034070300b540c290328110008250120a504c1c1a00501a503082c0c101490500b08000d114128484a5200d04080e0340400d020300404051501d8800640181c011403001c0c0d80240036210812034654508003511058412a142e400250f505401000340380303410440080c50340075041c0c0e03030030f61180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 196712733 1250 196711483 196711517
    0x31b09051c0b07090302100203030f06131503080415111b1507050604140303070905040c031103040c03020306060111030415141809090a1509021807030218041b0f 71
    0x40c2c00d44a040c0082c07514a07040c03040d400c00c40640780d070340340c0c1e148000c61451403d5014000c040301c0107851035101e449010380441c1c05c094581c001c0310395183c080c4c40d1121038646d02e162881e000d81c81880b41c100c4249142e145414228040d0303100024001c241e02c05007014100224061482d613880400036584020f001d079100c9180300e000000303070840c540300c1c4000709100d08040c14882e00200c08944d0f8400150310410400136040d5000c00000c00f240c030144c0300422480045101074000d00001c08606000040100800080c864007007040030440c0e00a4007274400a441e50301c01190071495a45002030258010441002042510403603041c1c1c1c840138cc5000c03100c0d080c095400c030005900c180308080301c044d070414541a040c038203200c1007030704a0b0248006181405640e9102980f004c1e00d084c00c0040282d03120003003015034882040e0700c841e0700001a00c2001034600036501034002e4008404040c24107500159884150801d40f14140c0e0804032415140403007946440d08440e80c0d042418010300b08441000c010315520 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 196713983 1250 196712733 196712753
    0x7090209060f0f25051c1e17060402070807080a0519020c011403090d051b010603080301030302070e280b03010f0b010806060a05030613020910030c031b09051c 70
    0x40e0543d8900c03540c0e44103020006002850020b0000760b441098204407000500000b02c18560086507400c1c6002d81280102c2500c00181c020500d0703040484d02444500515482030401d1021540b00481d40307516141c038024042280a0080020000c030406c20680c00465105e50241260704864904246401c1e28443c0000000c03920384026005a13000d41008a407a40c1c10510b501341d20902a2203460542c07402c9500306958002c2d85d809182170000018000910300d161200f810354417500c0d10000d0100981d689130441065200740320960040c050100007080c0c10081d105841e0140c08035920303101c400070072071300c20441d00030605c9041a091603031000c9102103a00c0c02e0040110300480031900280d0030740441c0001d000d042008007464483e02c010007044a078941c011040c0c0390401c1c4142c3c0d0306440d084180101340c0080c85610f10480e40034140c400040300c1580d25411a242d0f048181d034040c00180b9500605015031a8111900004104444420301c0641004034010184221070744000760120342c1034843e2221a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 196715233 1250 196713983 196713997
    0x213020d140603010e06070f03021806040b07030f090b0703030509030d1d010e010b0d032f061504090506040204150b0708030402030c1207260f06100f050307090209060f 74
    0x80422a003080b2a9140a1044804e8030107104058415071404801c0109000e000315402c00a0643c08505109254120304039425112000343c41c80b6560fa403280c4440718140c11224003100012080c01c10110b4041c413a020f18812560855150b50610040380d406401a08000340102600d120600c89a6218280c0e405503c2c20086101005403000001d24a02d5003920b4010803000181c2e814070721824a503440c0c0204600d10560549845100c90070403c5152080121098107400c80007049000344480d080045a00341c066910002c8040810f0040010300040e6140301a001e4400d07001080050090b003841c0c1c0149070350701c0c091030310600b000d07454040084894006100540d00d1800c040208000c41c1800c225080d501c6c0e00485042c51025006941035039903d999000d8001148a01240e4461807610b007001005e074202d100d0b0598a00014600c6155604c4070b04503038207038403038400c2d000000e0300401008280381038480c007070041c005082c01c1c00031344406588a41001500078908001c0810341c2e1600002070150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 196716483 1250 196715233 196715261
    0x6020f12070f0206010f050f040b010309050d02252403200c01050a020f07060e01020f0a08091c020d05030c0706110301090b10050a0818010c0509030715020a0213020d 73
    0x1003200802e0003e01d0000140c102070316002c6c1c0d11100b84203e0707558401151074031504650204078800c41c000101d010707000210300242244103049140d02d010381c002c85c0d05000c2c84101040c46035410070183c1441840100740c032403450102619044618101c1c02c4120304d90019500c3d08012418007051443e2100c2c0700914820032105e4100483e070108006030a0246a030000c82e182010341c10900010b003204d8683c42a080010446503803841104050342007901990700c0400c1d006100c2d03803650361007100a88a140100e034440e00794001c208050140e20b200718580300c40d000301a8010141455500d1084d00d0640c80a0715419000f9001d1000d440001c2250040602400403010300a440354940300340034054800e0403000c075200b044032044e171f030880e140d001c0180c0e844140340c2c1c508202d56840341c3c1950389070551015402d003130f03d508204000841d0794202e4024000a0016800c9940302035542050780d640300205005c1e00010f8002110039000340c03414503210051410b10300f01c014544080105040c1c200c85000d0f9000507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 196717733 1250 196716483 196716497
    0x60f0a051e01090f2009060d0f140a0c03090507050d140d020322060c08070602070f0803090c044226010207020f09150604080604110a060c06020f1207 66
    0x1054480d01803035050f54003512807850745d251000b064482d58094030607898050080801e00b00d003509940c1d00025000352003a4010080d02240c541c1c88409840101c0e51100030314104000440070521902c00d50f0811034104010309409400e24080141d01032a600e03080c0d0710185518000e83c800300c000d11080c803520f0382a4005554805040030074912084a003030700440b050740d01e41410811301c0d4000d881d01d00b0181d440213180d0b80e524400e283c5880240039040c000b4200600d0300c0c2a070010404000000c41c0120101e02c100e86920240b0030800c019141520b0003a444000f00088401e1808049400495114010128007a07000d102c0005041910003544c45036000e0041070204449849201e04040f4103400d2031070003503182c28440d40219030030300d40030a2304502134120740d000181c841544040011003400b0040944c1d0750380d656030712115616541030710f081d103075032034554010b888520384402158221945030312400c03145001921424000c1d004152000d07141181001002040e04028810922900d21525450303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 196718983 1250 196717733 196717751
    0x3120108010c0206010e07030b0607060c030501030c09020414040518030a08011a03090319181211090402010c08030415090302030d06081605193302060f0a051e0109 72
    0xa4295042152441d0644d0483c0c3d0061001191191046074803100c1da0602044098038100814070f5441180c1000d46018503160000d0201035054108904903801520243d0360651035900f22001c074881d5100b03080d40414200310704405403e042c2c121540c841020243d05000161b01c20a4030704550082003820b002906450041c400010320041c2818542c0b0040e40d090308500c0d1a981c0d05583c1c1c46002890340510b0818103078058078a10031000a80c24012050010410995400310b0014401e5150011101c03405180401292802d0030ba00052003950140d42d40301040d0070302e480b0042c1507400540281d07148000540784401c454242d010350f46449100b0390080d036aa01c0161030329012200f55030401036a88e0080707a910014685a0079402e01916001c0300c20004814880742c80d0307180769140b940110401c4038591415034089650034480c040d05041a000703d108040702020807030319010b048494002e00c00c03850000c40c284642c561b20081d4081800e00f048684032200b1140721680d20001d0340441c1d05151204185 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 196720233 1250 196718983 196718999
    0x108030307140310050409050703080d0617120403030c03090e0f060f030105160516060e21040e1311031b030f06190c051330020114030601030e031201 66
    0x151280d00c1248800a0450500c1c40e59014013144d5071240c0c034410750301c0e003034440c2c240041070155034011640010100d656104000380c11014001521440300e10715029400d180d01c050340410500540000503120a00c0c0a00315a4141c454a00341c2c00c00f50101301c1c1c07072800803d10000d4800058090b0305a60b490701e00c145030100c10008500b1600340c909020380d04103414440356180c080e10744126052141080364880000303920643d01e0380c4c01d00c40301410f0581030080e034021040c80410181300194140c2c450002ca646118948a2940300d03d210310507a90744420009100030303003503c0d48280900c3c0710b480d80035580311030b00d0300191809007584242109045400e00141d40d40c030341006040c1c2541e45c1000544628a40181c40c18034544000d41095900c40e11003503420180ea226601320b031440c00e00200748841054864240e17909246100104030420200310800140c548403c080c034054540d0f0503510405811442d508404246d00042e11040c18941c13a0425403090030410b1014240000c2000311064042d0716202c0e41c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 196721483 1250 196720233 196720247
    0xa030c02160b04051c020d060209010c020316030203160e0106050d0605060315040608010b060f090102010e1c0801210609030306091d150601140304110a0602031308070b1c11030108030307 82
    0xe07004049240d11080b10051f120400e1201100740c20100058072150404010795080c541c10800a42c1130158440508103d00368000350303010f40380203074219601c00303503000c070780c40d013800c0c500c0c0245a04000700000401519120b10000c261808404002140305a0f80e20302107021074000b6034800407a019095000459400c0900c2004000e1410034002d00c485034000780860b8181c07151070f102420202000450b5a01d5134003d40260a03081e00380c5080b50901840d8000342c85050100030006030006241000005851500c0d400c00d458880c0b16844a0041210030341d1040000d26945500724241a1501000203442d2010703c185003400c900400d0500042c0d070014a000d0420840c00b40540c600100314080c4910360340e01c0711008150300c100301141c0b41d5030f40361418100c0c059500d01054a44c0400841c6011440640c00700203031040b8034002940080352503e40c01e40f00d40340c008500070200c4801c000e1084401e05514840807101030301a8800001d054041010300c02c1c850351003600301089550000040c04061035001c02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 196722733 1250 196721483 196721509
    0x703150506130b10030203100b03040803040b10030c060c02030111130f0509040803010b070c1a0a030f06140625030f020f01060303120b061c1d03040503030a030c02160b0405 76
    0x100f0900318400c000801445035211580c0400d0340c0480043c901c885c00440003c00792400c142015200c1c9094540982207070310848088400da4001c3e004a0341302c100290200052703a40c00382c5440e0051f030030a10300310b62140c00b840c010303a03041d901d40340b088100166860050500010b01740c100d0744010304003035001001c40510352085008030b031080c0c02c00000c01c11603403c0d85e040d80c0c0780d01113480e60740500c0e040c0a1119030701600300302c40c0c1c1040c0c1040b4030052245031000700039030b0404e52420311810029400c03102c1215130a20901c003040400c080e540300035203451002000c0c40040015440400840d031035008200622403001100412403808a9805181d0100072002c118225400244804d03819035500400841102140c41140d82c1c41b2000d40925a071800262a08a481c000300c0030105600f000a450151680d100440405e50700080101001c1c1008011101034400c058000c51801040407000c50007048407805031821401500c100074054005c0d911510028400690840e884604100c01c000a03101091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 196723983 1250 196722733 196722769
    0x509090723030411060c0a05030c03070b060d0b06011101060906080717030a0509131415040629090406050a03050706030b010801050d030c0c12060905070b070201021b030703150506 79
    0x2204120006241031600005540142c45c0c45445007000c4034a2807409100ca14028000d010215241c06600000000b90070114080e44921425845410500500110350600034128814942c00100154060f6103d4262080c010000146c01603a484000040310210f822002c0e050300100410003001b400010560074040c1840051840c042040780043c210f03204240701c5c103001d500d80407407840083c2c0166120400030240754001c2e10682c0380c884101e4080004549000c0c1c406d03864248045403103002c0105072250425900c440d1860341f040110000e8082d00401c000321f90041c0c503100013240340d03141c041518000758801c500401c240ca0901d9000b5007911040c4100e030741000034401c0100702d0b5030741d5134514803c800e0300b41c1803000c09075000e4244424618031540040302c00c1c3c4c0000c103841c41040060780c0462040b50040003038030460b81d101c1d01c5040c410702c5241800381c0164072240600b00d101035007200c00c01c41ca0600070116110241d4966600179000941046450025507860070021a41044841c18500002c05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 196725233 1250 196723983 196723987
    0x209040f0b0306190906050903092409010806060d060b070605061e0607141e160b03240d031e0e03030d110c011104030213060b03060108070509090723 66
    0x89800b09644820061040406080d901480303103404c10759920444645800040c00d000501e8a01c4c242a540c0c0d01903014103009105008800080c06003a1007010740440030441e103035141180c0702d40115003005000d09201d0388044100280c05080d041b074891b00008003034000400d0b454500a0811808445000f8007035400b502480069071511011200340720080002220030a480700c0347ca0500150102d84400303403404038410141c0721440100c56079020045000850100c800c0d619500c8100038840c421b41c4506410301c1c00520205054020308110b011810320402d2048405c608442c3c0001c8540c056554207901081c82d148041c0c1c81204040d0aa403410300d9035007417022220760b59401080e82c0b44200c1c1508600707541d6650303080020081600895402c030680c08001e00c1108965907000c00c0d503034000d02c000c0788108003403040d01d03140a4090144070110b44050400358190b0780e80d40700548103054020b001c0f40410008000d1642d80340e03180e0142c54052041030791112010b400c1008018040d03151082050341071401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 196726483 1250 196725233 196725251
    0x150b09060403060504060f050c0d11040b092b030905040b01050c060610140d0f06050904120c0807060e0c0301180b0402040c05040e0106020d021902130b13060602010209040f 76
    0x30314400c0314101d03a800070001505a0f190b0400308024215101d46508050070314051100a00b03031207020305203030000c40700104401b070720340b09041043d486103104070446c2c00c805000751030052400540c80030341c1c11080b01c003800e50800300140d0000d40d412100c2049000c00d550035030500040c2080d101e40c4030440c0c82030030220700c0c018040c240943ea410b801004684550800745074903042c0d910034201070b5a04502e6090360b0b915180301c0d441ca5030280c10440c4140c4445031418500090b6445c10000c014000c40d00f148462546001f040d00440b003510b100e18007a10601010040c40000031707254400c843d04691044054a18542d40703004050a55074503400241c0da4020310342d001d40c0801c26006049400c103034100c03000105400303001e2042d100781c00f0b00e601544020f41d544000040264001c554144042c5031a8280c030789080d482c080c07840c8084083c107006504046541c1ca584042883d0750b0007200c031810014005880c0324007138001c41c401d49507180c01030310043c0d4003c1100301c618240b50042e9540c13070400c041d0503c5a400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 196727733 1250 196726483 196726489
    0xe040c0e0f0a0e010b22140f0f090c090103051005011e1403070302060a020f01050f10090c0c0212030a08011712030a0e010606031d010c02101d0a0303150b09 69
    0x5000703419644078950f6a82a0140707100d003544001c40c150030141a110f0310303444103044c1000e910740040b5280185414042d0707104041c1844840d06100c0d200080020302c954442000000c48000700500d1a081d034807a10318500d00d20b648038041e40d8002d42c401c00c0140038201c81c0d11b14120503144181d0150004040ca0074035580c2da446a101d26006903211034440049050103140060b00d01021540082d401100008180340d040b0790110f200081c01081d24002d00c419112643e80b03510904048079000c96034410540e003440380440b04e40060200440c2d0b890201105506d64002030344a007a0942016120340c40040e41e07039040c40e008050b050045c5081c17100c0c0200003e40b18045511500750404400d0780640000c001045c0094a60004035410f071a10020440c9903114100900180789240c800c1c642403402d01e42e0304c150844140981021042207034007420507540e80d866103801405803103000c5540c05c164007002542c0d4030b50412038655518060742e8085400b003542201c00c001c0d0b100325000417410f09010001000d9540b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 196728983 1250 196727733 196727761
    0x11070807050f0a03020a0b0304200108070f110607030606021506030a02010c081204050307020a0504180b09030f0309030406030c090803070b07030b031914150606070f05070e040c0e 79
    0x180c05940c0c020b000d180400008050780d02c56000203500440c4001d0104200124401842c0f0031840b0392100340031000d0060082c2c1c3d0b03041f501000240020501d01c0041c2400d48202003040d003180c0b280c00d082c6007403004054114108007003110302c1400240d5602d81040401e40c10800d00e00780300d04414580000e410f162001c00e403505040035010341404228981d980c1003141c1c82e0102d03040504052004042401e2524110b612030740f0002c07081c0c1c49a42081c1c404111883c1c6031061110081c44410030a1401900b999040c0ea04140148420100e0000f4405034060017030210066228405c3c8a01440d592410b04401034103c500f0400442d0400407901410f0094903400030407656030076000350005026a6a680003140640611040c4940600032240601940c00b410242c041c801441101c06004031f000c002c480a5a42c600d07503130000585045c41c80410603d060040c005c0c502940030b01100d550040f12074803600d19040c070980c091002c0e12044400c210a11017405400e00260200c90100041030608649900d408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 196730233 1250 196728983 196728989
    0x50a0f0b060f0d120504080f010b100e0108040212010605060f0408010c02030a0212090f0604090b0a050603090d050702042403110607110f01030617030a081008120a0203070204091211070807 83
    0x2140002d0a80d10001c0c0210251070013058414100c0c8d142d541c402d0b6100703010f042c0b030342d0040d4064000c1e25050b10106001d0a101360440006942c0d200203507590360208912002c0040d0b07142800d56031654081001d458843c01410050344503050315a4440c60403120a00b1105845964070442d04140100101c0c00e0b40401e030040ca1b540103120386a1543c0000e800504401800450664404c03070001c0c0000b5006580d4000f00c0024100b22034503010650f551051108c0f0303200440d20320b6519004500300700e4509015001400c822800940b001174580c0d4004e424030b11a106102c0c41e604d00881420042041145804001c02d550300191250750820400e41c0d140f03020f02c0d82c50014203100f0410300417001da00764440e0780010001c100705d004400c0343c0d00224248507242e90003030b0012000074000c503000039010030120140b4011240700e44001c00c1190b10309250110f546e00f0405084003103003c10130440002d80d4a500407265490302450100c0c02000215001401949030328140f0342194011003001c108a180105640e412 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 196731483 1250 196730233 196730243
    0x80a020d0309050a170d0201060302010207091e15051005070506040308090c030a0605011e0302030705060a170f0117011406090a0e060a06030203161401030209060403050a0f0b060f0d 80
    0x41540149402d546103102d9400c0a50030102d035540c0064000c008001040c220364130361040d10050442000e0072800c0e2911400080e016a110100400582d04551b02449203203e03120402d10041014080c040251015204458050703241c1030000c1c441454580c0c0310070390f40c85860400d03074940011030380c0781d5403516002040034050016101c0022520001444809403100b00207050b00d5082e4214605140108000c3c000c3c04003407000c02e200880c521015020713200a80340c005004048051800c0c1c100104d65000180110400910900e14420f61040e0b69100d80140306038507a104c45903040c0040c044500040c42d4802c58141e05000510b02c140850382012900010b064512000c076039903800000014202600060030030384900070070002602030541c01702e41070300c5c421801e6a6600c4070b100c540b00c40384082409995140034501c0d060352076642c06540107100c061005040305080a0742d0351107490414104c407005403003441081700200100718607108280d6210004946980c0b14032100004100382c8910300c040144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 196732733 1250 196731483 196731499
    0x60b011b0204090804051011190201021b0402040f140411120f090f0a050106150f0f05030406060b030a05041104050c18040617070f06090b030408070303060f0b180406080a02 76
    0x3c113014104045401502010f400c0e80420590b0180040031585204c406603210b001d6500560301105d4a0f203904268160146d004100410b10488007031040c03019211100d910540c01c000c00030b240e03411260050b000306120700c0c2c0d4220080e01202404113613180d555905408900c1040000e80e610000b44000b5000241d29140d14a6130340e460035010320380138003030b2412000303886080b0030542002015003107007040e600040b178101d811024145041e0360301131801603503401081e01d00428040d200c0c03096010b140c0c02405000d02095442d514815440300380d02c1650ba01c0e003080d4640040006100b04449640e500c00c81c10f4030104010b01d00042800c20354090300c500034898000104540c4650740d03568000401400c4000424410710380460381156a07620284102d495000311607c0000744a4001c03240c1d10f044801a0300c64a2466650340d985004551010404400349660f0b071401061aa01c0d101c2d400c0007400c0c0c00300100b85d46a4080e42c00079020b4100140044c42603042a5052010071400303d141ca440d603605980104e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 196733983 1250 196732733 196732751
    0x30c0801120807060f020f0703020106090506030703031b1a061c0305040501030b150d020715020703020d05031f0905010501140c07140607060e0c0109151e0203090a0909060b011b0204 80
    0x8005413179411000300d201400450240b00c03810155004002c801c0c4250020000180d40d04003810617038804a426551540280300c00b00007103030040d034400b000480200c00b18000000e043e9a4260324080f118080f11114562008000c180c2c106075280c001101d60440c0c00d9405442c6c1a61700500d03038401c600940e0704041c3c40c0d464a01d040e855504903045030003180f12109887d0701e01144180000e4215000c103882400803c0e44c5070203040c00502c200d030b8034960540d0180113146140d103401d40b0f0b0380d072000c3d202030981b072071a01d10b080f00c0042d81c108080150407244808500b07949084001040d402c8120b920f140011000c10048040310800281901102c01090008200c802882c00080c010b0150180250004d1700700420940c070100d003c205000820001d88070032521540300d645c2c4648403601c400302880030442660a81c006000c144004a0151090b4030440c3d25000c02400070822003032040e40241000c64441d80e00d2020800c540c090142c1c0d565080c40c200007410340300900e1a94203066000040e000c2c65543c4401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 196735233 1250 196733983 196733993
    0x40612170a020a0c030b0405150411090705072a0f141c08120712020f0a11010e01110702150a0504090c020a08030c070c090605130f061502030307030c0801120807 71
    0x240303010fa401400251105941e030400303141c520400c071400c50341030083c3c110004003100c2c61440940199080410600201c21000070301050040281c4520180030041c4034072070020341001d120256841e07207441c242142c1402c2a81004525030b064000f41c502d801c0f40e110500080602d007001100f0401c003242d03001c20a04910346c1010500702d04180160881c030000913070041c8905495400c070302400c0f11303554030319001c982c18846004901900400380701d040c0303080128a20307040c428110740b0362501010000140d444000d251749c80c2140c8a0301400b4286940209104040d4030b400e21655090a6111403020714000c0c2d00480140148614014104541d03603490075925a14402c219424405a0142da071079039900300b100850344c45410820080f501c40703900c1c44010801d0724890181800b1150080c1c900315038440d02140c08800340c0807005403000d289956144c00a5112640441750204c4846a000307141c0c1c03400c0c18400102915030188480090144030303401004840c1d054041d1086181e0020300307841d11601c6600d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 196736483 1250 196735233 196735243
    0x1611300705070305070602060108010c0507021e090702010903030b060c0607050c070b0409020415020c03030912031e0a02070603050702030316021006081f05010e0f040507030501050705030105040612170a02 90
    0xc1e00a01c219000401000000100c1c6000e42e51180c0031505160307030b10305140d400e079001d0b40843c50001d1010b004260040c10f190701010035000a009502624821103800700e403442d4800c680f0100140c0d15501d000040c03640510403044a400c0030390382940b82100715041103035100000b620001c100400043c4c440000001480241c01501c000c0401030356499544803510003035001070040250200c070004100e038526000049121200a01800ad1420148498108072606030060284000b0340010030040300214100e503081d800343c08401c01919164031583d02300900e0880940c115605261911007802100c540000a4a0b44401c030700548417420f90252100f00d052419451158101a007441d10110383d026001c5201c101d2a050001c421104080e0640010155903007803107050094a51040070580c9004c0c14844264454082d0085900490381d0740e40f402d0840e00100d030f6910014a0210061106160a005080050a000c1a40d68480708252500400c200b0040a4004880000100303044d0035030080c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 196737733 1250 196736483 196736497
    0xd06320402180c0c030a020714040207050607030e010b123f0304081902062401050412050304051309110a05011209020103150303121103070c110402070803161130 71
    0x56903181c4603406000380da517084900270000c490901080301515030a152090f103401c00e82010052803207464000b010740080091000c030315059502c030214440305841e500c100283e00fa000f4030090081c5003042c0442280c1c6002403a00e52034000103820540254130400c5440034075141c1c1492120b65948483c9000680340c41802c5583c07401c540e1150b424680aa0080303840c500c03c8000004d1103c0400d02c00c103111003c1030758041124041032041c401444110110f001d064002071151040700d00c0c2a840301c0028990713040d1114401d0b100342e00c030259202002010360394542c94400175902500205d0401c0006000c00f000602140ca100da5180e052100b035a2094100c05481c030218030103d0269a12810001c0403842481d0100d010300b4245040202e5440700324044a1048489079a0b000e11140541d44102c2904525111513512640074820600443d002c207000b1401000b03a9681c4440700618200c029151210103807900d940c40d0403181c1c08000000303040e840d43c40c81c4140b080740c2c506c640c0c0071103650f001c0c42e000f0301c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 196738983 1250 196737733 196737757
    0x218060a050a080f010e062811030129091e13020307180512060612031909051c150b060403050102130f21030e0d06320402180c 56
    0x7410000f1801c4001c140c0803020749401c4001d00c1031241030268640c1d142020342c0c41304028440403618080281c0480c2944190202604000c11410303020310801c00940c000b03030094243e082c4030008a481452103070b41d0310485010400c00a1381801441b00015284007940c0d0010100d442140d0a0007080755202c4090034411b0340c5240c811500d030305092000070701c104010480c1c85184104003801040900d03201c0c88440441e0007400040900d80c3c1c8620a021007444075507601c01041c40140990000c01d41078450240c00c440442d55190403080c42c0900b00b140f045c4aa43d203094a000b40240140080b4001d921080c481c940c3c2c2c4840440c0ba0385000c4e010a08910541e8005800c5504c0855800303425110900d980040340c0154568801071a1505e40f50107101000386000d4481c40800400f1400081c002d40f4807000021008180744c00494483c0c484009690b180c110020780110b68000d12002c02d181d800c072407038142c00b000d100500744c0d00e811382c04036400000c1100c21790501c1c0b0f0030200050300e12400d0421903002000360 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 196740233 1250 196738983 196738999
    0x603030c060106200a020d0602161e15020c06010b0a11100605100906050a03180b181009050304030209102c06120307030e0f0301230a02070218060a05 66
    0x260b00000c2c64a0310300c003c00d004c0c0003003510b907140380036100051004c0115002051105004031702d41c2d82c2c00096206500f11001c004004850038007003200240100c088942c0404040418a40e910b8071401408080200703425892062120180c1080005110341c103440051940707507600c810030f81041d22040c103004565016446858811070382d0071181d4001d04201c0340c01380c3d4030001c42c81410000341e43c080d000d070003a00000b880c01d0105411480c4260001c0c200c40790030070a01c0300210a10b03214002e400300200c0301d00c3c4060360741103000501c450041080032407006003136204000050180d0781e160707141d1280b03200282c8500c0c5240045042001c0b072038810700c01012500c8a0201940c010300140b84120802c42059a200200304005038407424140070703035078001c80400061413501072107643c240e0710681c101d02c2d01c6810510103444075209031000d10440940d1040b216644041e18079402e802c4c151000020b04e2001c210b401408003030f00503202c40c00030f00f03440c400f54441c008496403490003003613030340c03c031035002329448641 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 196741483 1250 196740233 196740239
    0x130608030a0c060605060a0819060312030203090d1103041a04090e0f0c0a05010816091512050133020a06180519080a0302090402120406060e07020f0d080603030c0601 73
    0x203208200b895100340018071400d9601ca08202c0702d0f005001000f4003069800b00000c64104460030a05062401400c00041c440c2d125100e0507014254101c1c1000820341c0082801800002081684115803d0346440c00e03100e203c2d08070035522401607101d90920720850802c0d1501100c2c46105881c054400d0950400c0400751000040365903140c4001d4807a8540641c981380303111814a40c00360b4003690b0060711410240d4803120521000b41000803250000c2203040c0002003805203146c1018046000c4542c1c5010b40b04c442160254211030041e480080381d58800d1a00041480f15510b5080c009007049044d11510042c50754140c0c01c1c8100d200000304a40d190000e900c001e4003c0c0d104944640c0e0250702201d0300030305c1e03030076001c1541c68980c000605146401d111110456200750020954080043c002505002c20b0080c03544040805440480d07006444040c28031030300801100301a88007513a80300030000750013510411602d41c8040085001044142c1001443c0368408001b03d55064519034212190b941e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 196742733 1250 196741483 196741487
    0x120f270705030d051e0a1b030c0b0406020c1006150c020307120305070b0601030c021203061c0605012d0501031a030607090501020d0c031d011704150f020403050c130608030a 76
    0x200441409400110100341c0b04610b00c01d810039541d84101b9610740615980804075660840d4080801c11000c1002800448001a00a04802e03014500c079000240e15030300c1c01a02c007802c00440c40c0d444000145030200c20001c244907d02d855000d051981040c98803201d480c004242491581d805c21560340c50b03402074040c00c0507841002070845500034914038045440b46001141910b408400c0c8400680c40105041c49402d2880002c41d00854002c015050540f5a08400d8903424603800d0245c5019070795070010031035403048560111000c0300224205c00c00c0c043c15400c02108258600801c1d0403d075171201d2070382d000a900170800702d0b95074008044517280c3c074141c0002400052107024440c01801110300802803d40246260340340f641c0d26490304010031424045641e40d410099034030328100f00c00b01c42d010b0109041400c026000e030f405603201b140c103a986200d003107050b500c5405628581c00c0c410002000440c101140c4010950021580c45807003081e0410454060039541d0855049800001800c0300615 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 196743983 1250 196742733 196742737
    0x61e07080c15090c040c020f0106080304030b22060b03240405120a0914030307020d03020a0605070504120816060c03060e0610050f0d020f030c120f270705030d05 71
    0x14101c0780c21076820310000312414418200507120400d041e40402c43e0a00c440c0b03401e800618000308144102c401c0b2009950740f540c255400c5601c16aa0b07500f0000e028018052540c00660340020300c40c00d18a1707064580408034110f03020140d000751000755074007801a056903081c84400c1c446032440101c0001100300c910b40200011054808444070b01c03440d5000c109040850059030800c070011f840729861149000d203400400340f0350740c04041c1d1500041210400503030b00d1010f402c030494020303401030440041a203041e9041b1680580385d00248001032004000718007040710f2012646a011000f6915600c0708100b5651204902500800c038500342400c003005140d140c0c1c1304d0004c071180100b03075000d182c03101018070414117000d12101e40007800402032007046160503c010000303500e1451006103000d140c141a03859a0b00b00782c440d5400000001003d00c91621400070894000060660650003800d15020301c0b09520380c0441c400c0324440c0c1d151a0320141c03000503ca43d000519010701500c019101540009102c5c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 196745233 1250 196743983 196743997
    0x1020c0d06201b010b1c0609050f0f060c07020a15031d01050603010b1504090507200d090503030a020601090f0204120f02041404050703020d0807051f0606110c061e0708 74
    0x581c0783c1c0010009000030500565640100c0540600300c8030b0040400c414607011107200564526440383c1030704000600800c100c13116440e03540b01412036400300014050600d83c010700045600f00003800100050380c0c0d881d940100321186140d110500020000d4181c000d8040d400341250344045000846040d008117400551040800300c000300300005002c1c040080030320701d6068910800c10240418007440500c0d9102c16009421810400c14100100a014140709601060302010b070300300780c14007a1a0f54100325894054036084001e1070900d11001d1001f0340e44c03481407181d0544030ba22810301d4038102c41c40d64115800340c0600faa25410080c168100440b000000c50303000c07406503280541149a0a040c91040b0307003e594410040c000709440c50702080b6a601c110001528038180030030030000003600401c04941c0810071030380706030b0340342c0c26051004080b11400e5215009011090382c5011540c1000700d901c510f443c108944060300e85100200140111481c401d5003d4400400158041804140c0024280c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 196746483 1250 196745233 196745257
    0xd15170a0302061014040203040c170a060b0d050619020915031e06030703260d0b0102060903040b0409180204140109061d160314010b0405120c01020c0d0620 69
    0x81a01c1e40d130150b128508481c0700d8a000b020002401002c1880c141c1c00840d00300d0f0042c0302d45545151145a55070740721003000ea40c000641d00c604a41c10401c0100d00403200d5268040380c0e41d02a10b5660f80360540c94001c01014421180e01e049800082854560706807111100064140e0001c0c0384014103020340b540c02681d004004040300c06a01108255110142e44112703c080d0141c54944d00e10303075031000318549001a804880455480c9440050f4002c4007400c0000581040820900c0400b0300281c1040005814800c242d00204418403040010408440c221958400c00041024080e01e21480058200000a502c582041007003200c1c826542c0b182d5050f41d54030b0004000e210703a82e201500500340040c1080140c10b10117000546100d030101034034691540982800b140c01502c154426002d007800b60400022401f01203800d110504082c80004000001c1030004c1c00a0702d01c1c040041c0d41c03045a0b41f0340c28455002c0056a03006c00c441e9400407192a0002d0080400074401e140d507464998101d0500c0744a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 196747733 1250 196746483 196746493
    0x30b01061706030c150a1202031005010305130b010611100905073305180a030302061b0301140d03090e010b03310201082706040c05150d15170a0302 65
    0x241d00d20300400c148000b280c1c001d0a4801010310409421400c0e04501b55040901c03007200300345245011240000c40c461904050010103807410315002404480002d49002d03800144403824000048800c1c07280d905544241c18003401c485003c40c0902c2c80d01100800c0e07100d848c1c0c00d02c454030701080307800925281a52140c0a00c0c0700303480f500d0182407502c580c0908101c0980755000c400c030081c070b41c06030300103228071058821340c8202c03840c030780300460040c41c1d46502c00c6006910000420014002d12100403216901942d400751642d4035003000624103001d81001e03079100d502094180d804240c00350040500900441a5484696a4334101072007250022103803c81442c1c21101d4074090101e507000394906c1412008000d80c1c80216503001100c12000013040d08400300c0c02c03482054500c10b80042c0703510756140d1480050226283c2440e05425040071644800d02503e40745c40044c044442d240151000340d242501c0010390481013407a510320310744651744008980520711800316209400822101202400f94003114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 196748983 1250 196747733 196747741
    0x41b080c160609050708070510080f0703180f120c021f020c090f040506010501092304020c0a0602090a080304050907080c09090106051306021609021b190611120a09020a030b010617 79
    0x304502030305508207400904170ac03002032000b160302525103030800c0c0d8038940028000585d9a03180300c2d00030904015a011413101c1c0340c03101080f01144802c817014460f4549800d0507040b55000c6211064482e0005403213503688042c00d40e009100b0000615014801001001030b400c00740b41c1030801c880c042e01c05941c1c80c080c200001c100c82d4002c54080040302e10061481c003120f40304c80c440680c0c0304504802503500a400300704001b4018030400402034560f0090174010b94a6050002b0044000500d0b403002045030420300c4100f15079a5071f007600580c02055410140d07441d6888040e4075086c0d2003060402540603508100101c1e501d075022015040c04642c10586441407a11088141da40b2031030500014150002e03488103205061594026080c0c9103580c0091107004602203d169090006041c040030401e01d280c08501c061200c64025400c103900d2180d000342c60709641c40803c003070303071140100181403c585501c480000c40d11140ca0100c000c45e0080390561841d615880020300580c0515241400480320780c3c08a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 196750233 1250 196748983 196748989
    0x40f03090605070c051009030804091505040605030607050304060204090903050409050a0603020a060c020d080a030c022b2001050108030306120f0601122f041b080c1606090507080705 80
    0x3d40300940c00c0020f8074030b8030346000100820b182e02c0400c1c920402203000740000000ea02500608050981c0b0307500462800d954003150604134420b0381c4003510175401d00c0002c000684011407460b821103240e1038055565a11418460060710032a40003410691a140e80300050650050240042d120540d505105c25114002904107981d100d00000e0360101e2842010880c03580545a81442c4501c085c00004103038810f503d4000239a0491000c00010070784601104c121240d05200c65185001320502c003103044520310300c08190781f94201c00000b0500141c3d1400c15800b40d0561a00c190518243c402030040c0e42e110300c181a125002552041e00854864180848035070b008146400e000e42e0741720041000360710b003409101002010b080c06580c030204003c040307102e450709030201c58039000c1d14031507421900780d201003484122600405201c07484003c4070701110401d03038001c044541080100c0d03e10398549001041000480c3e0350410000c103407502d00380d00081000004100402215100b0007030318410b6580b5000c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 196751483 1250 196750233 196750237
    0x2250302010905040e1f09050304031b0602030307120c120c120e03070203060a09110901080a030206011401051b10090606050301060605160803070215070305041203151a070605040f03090605 83
    0x117082a240c11100076040c03100400d012044d04581c41d281e0101e4021582c0d01d0703a90861340981c0042e2688050b111460a096140c00c4902c0000d020034401035103189441c000080c0410400c40200d0f9032641c6807000070055070321425008520340e40d041010010f8034180311000d84501016844000707414203065000b01907407401b0041d07685040d0003a018010036030f10f602c0c08200824048030111b604680f080e01110550321b8000005018204010044c0310b0450a410b000e4503000d016800070301210910007450066036400350a54461030301c14420340080552202140d401d02d50000d9503061b20b04c0c5442042c405001c1c07950401c0003281d00650007089055201e240031070b46440f4408080d01160300c14403400c000103a103540110b038005800e2055442000c1001580c01c1c10407002c0e03441c00002510b44042c071060208500540301d06030210305040000d00f41f80e01003140c0583c1d00d4440d016047c00310b0b42d041c1600c0c0c0c4000f0121070207550300803800c0125182624050007c101e207a42c058000409008012500d10b0140742 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 196752733 1250 196751483 196751501
    0x1090504021309020d0612080a0216061d150c0c0a240c05010f110d140105031f110c1c08010e010302090702030702100504140306130809010225030201090504 69
    0x402c001105040441c8000a50700805124804950741c40c000a0030081d20b00078280c51500c210000741e0f44110b140c500920f03290314007100c114060503a00301007210319003080b2052000309151442d072030804000380000394811107814110320f00141c001b522000b4130030701198242502008440c0c01013040d440780d60144400988a1184004000c454107084285000300d259132403403889074001054001e1102044420f5607000c03003461380880408100701084201724003c0b010600400001c0c0b0b4000e42c584000240d1704c149010075500c0526915560b8507440c05244c04c802c100d1040c00c4032007942c80300c10301d111641e2200410203c40261032907070741c14403286118485003812078071200c40403040d0764210303020080d114101410701025480704000b0080140c4445488101070360702e0f130711b840d502d991900242c41c1c0250105404580300307410080802c0100c0d001c19010794205034116841903100c040203401030340780c460b8155582501c44c030383d0144103c02c8001030401000b136034403c1c1d84000c4e020381d0310b00034030056038039082e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 196753983 1250 196752733 196752757
    0xa0f18021201050d05070b0706020d0f0b0d060b01021009050607090e01180b1c0606030b0a020901020a121b0605010f0f120f03021006030506090705060c25030b150109050402 76
    0x301c0100040d02d4084203802d4101d0184058611301e540d01c4444200e01c0d8852101103a46980100d101510940701c5c0c891100c51000c4001c0c1401503584101c0000e48c000d12406c1e00814040e40c40d20f00103000d920030040030403200c1c0d90b402d080180104508081c0d542d1759040311400f00060ba001c10200d000b801948007076040302c400c00c4032180d08400c01c004540141024405183d04480900708585885058903284890540105130004d0f1650643c20222482c2c800205501d0200f8010003d15030f15980c0090b801c41e001e500000c030f04d80c500107400c1044541b007500682d14200c3d8039168001d1030a01c200355005e0360480d0983c0507120b00c1555504102070300c2200512605001400c600c1415011420402086410343e110344161440c41d821504a401140e4003034106403965400320003004507011081086401421045440c9070030642c0d40d54055582d85411040e039400da1500e03009000760100141c40040c00b940e0301420741901c0e4540a04003081101050300b26a0008201c58800145401d2038030880e181c4030100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 196755233 1250 196753983 196754017
    0xd02010c0212032d07030f0b03030f030901020c0d110d0e010906080907050301050a060302010306083708030a0f1410091805160302090a021201090908090a0f1802 71
    0x114000d00e0b4030f400003404501400814240f000c03070244a6400741d0a201000f5040003141e0034040c500401725080300f280600814500300d11740b60203a8000056907080e40981c29116920307640c4c8040c8502a00a81c405002c1d5071146015011205400c0141901182144005c03140307015001301d411030b0011000d0000a0110720302010500c03109101d060200e6019460404640c0e445603078401007070071600200e81900b075095461805200b1581e0501030030004003402d00c000e04039001d5580440401d103690b40481d0000213100352034a010200c00c41001d40e0982c1e00568902d46900d0404003400c0a40050101d014a80b85040ca00040a1400b4030140d4021030440340031042250820384c1007002850a90411300030054001c9060000500c20024030441ca01c50700d902002c103514600c140a03100c04044c01d051a100c0c01440700002c07400103690850b0450702c2400b40805e200c0610b04181308076108405880380c00207000d1a02041c0480d40007070403422101ca29041c41c40d48901d0418000880c052116403a03a25998 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 196756483 1250 196755233 196755253
    0x80402060d150f090c03050609010623210609040f26160b090303090d03020d020403080c0a0c08150609041e050d03050601030e0a0b0c0d0f06080d02010c02 68
    0x15040501050500141c1c071840c100b00c0800800c034960006150300b9074a10f051200040718056440c8200c80e81c00c0a000c5810104005150700740140a40003c000b064420040e2018648060341c2d010203510802c00d0b51140107020384010a0380348200e2412201c8044003041c8a820082c0c0a90b00c10f9800c03002075640440d15a0b52104890720900c003401c2d0744007074248010207400d107407401003c1c140142e1512400d00a82c84c035103da46020014031008842e0001e0003088035814010a4012007035450745801681d81c0442d0140ca0000d00443d0406404844041a00011840c0c0001d001d802c450042c0910b40c03202d80d851207001d40d44c2d01c4040d004444800d091021454a007811070900e50000c0c850319050801282a9a15044c0103e054000741c50a90240703000321807140c0c041c490203800c08030a20702030144050410032260340703280c41d100090051201c0710000b40341c814110140d95210b02441424004640940000c9014100501030044280120240e103100c96005200303292801034250040d140c201c0ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 196757733 1250 196756483 196756489
    0x304061b120b0f03070e0405010b03070510031113060c0c0b13050f04090501240807050d080d09020604080109150b09010b0a03090614160309170901090803070609031806080402 77
    0x81d050b03901e160031400360440b400c1140d4040c8900005030143d180000b0321803901e03090003030a4401944085009030015102440683c5500f0001c00d4055004e04000c215455611544501c0b4440d075042c4000003407454001165a55002110518490080d852060210307152078030303c0d126205113012000c404003550020009400c0c0461324000b44100140002038a03003503a05c0d0349080da04600d18001d00241d01245018680784040000c02c0600381c000c004028050805e03001c61290060f043c0c000d00000c03800f00d901564104650000f03142d2560260010382c540c1d96510640b4064a42d03184101c2c2d441054041c0503041786c001e07219038100c075040200807003d00c3e441c00000b5031642e408600084101030b1185003507004950715000d0300141c1140024420000d140c0129500003c04111400030b003010304040da660f010031b01108402a45e5042400184c4d80e4200460042e584200960f01640fa240000300d80c103c24427102d903000480c0d55000f41c4803c000300c01d140004003a0241103001760004107007034002043c0903003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 196758983 1250 196757733 196757741
    0x1090c0e03060a230a151d040f3002010f110909060310020f04050f011b060b01050d060305030901260c1602030a06050105030f0c010c14071a0304061b12 67
    0x400d030200141e813110104403203441030900c2291105045a2a05c0c4242c041071422803c2000030001ca588803042d90440b1a01200b4911001e04003800e52080b040440052141c1d1b40780e0380c26010105410301e5804142e4805400000f01c004118801551030013070181c01c10103590103100200d01299407114a401d506034100601181c0c007138aa02d4240c45225607030031301d01e0802d20061450040a00101752114a07000401040085000059042021511a01850082968480d480d481d03010300040f5013124240300403140c41c0102c43e004414141040000001d0000c00b00c000c1034000020381e11040052152541130340301d00c1010340c01100700f5400710b001415113001600645030050b129030b420031380c0394078540000749045031034a07003a14115030300c40c01040107140c00c20104a09a11141c05030021510080010740000c2c4010800340c808090880501c5d080391081c846000606002c2003040d00300840001c02c3d6500d600211011030b00d0b80e18001007000010b1007403600410114030b90755004c01d82180961414081c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 196760233 1250 196758983 196759001
    0x40c2111092b06020702041b0c1203021912060e1603020f090a080d021621020f0a080a0b01080102040e01060f02010e0601080a0c0e0103232401090c0e03060a 69
    0x242070354040480c482c2410001c0608014081d030800340e1070b010030b070040004a400400440c1041c012000c0700c0d054460700180d12542d01c0703800162071003021070000e000360003034420f210120700c041200e6000e401005030003000c40040a6805038040250320740764030104624450a58003010b5503120860104c05241c03194008000c58900214031608120015011444800b00c640040a1540045404941540d81001041100d0103807402943c00a45007079800740050030b24924041580081d03401101c04d64682012740a0541c4010706082100d6994017040c1c3c0e03c3e202c83c860102d5480c0107020000803c81c03414025901900c034040d6100b2096480c04205031a8035114540d10000d55484200a1200b200c1c180800342c024105140a03001e02d0b1507526284001114036040041e141c10768000501c0460103c60401c1d2525440361151540340002407102c1d450012003c82380000d0008220403c0085c18400c09054100c80d0550400c4c00281031100c0203641d160b980200e1950103603c0100000c4007481c02d50019448 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 196761483 1250 196760233 196760269
    0x50a090f080a0e0d121e090510090f090902011d0a05010318060e03030702010b011e03020306010908010e010b010f0816050d1d060412080708010e040809040c211109 72
    0x2643d840b110124071440c0d908401952400313103088210600303d03040101000002e52035a024100e42c1200c850141c501c1e00c007401124011140030450010444c01107003060003900003c038158912980d03c0e030505c2c0c003034203002c4030403070024080b14092408881c156a080403403401c000d05240b0b040e410440110024001e5030b545100103c00620141c0200701d881c42009071a1007c500034542e6441c2c0b4010286c08e40d0408405541040f960499401090707842c5078400c441883e00e8540543e0b241ca444004807452812034202080035460416a01c500690550020141c41002e07200c0c03416051040c20141c070107010803611b114140c17007030746485175a0703030300c5400188511440c00c4400105c040d4407008030f0a221071012030290840c1c8c0400c0c280414070484100b0002200307a549020826450205030040c01c4010610a1030100d44006c00402c080248000513036003030000c0034204000d0200c1640004100109550317202100030203403070800302640d54900404817040060f0103000d1070702c2001c03800d00c4440c103440b14800c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 196762589 1106 196761483 196761497
    0xd0b1509091f0302060d0c09050103020405091302030313030b06092a030c0706111206060c1902030f060708181501090905120d0f050a090f080a 63
    0x54061815108040c00311202c07110360b0340380c03503541d00300940c0182d000c608a8200d00d41c42d0310224498145941d000021581c54005500b2071141c1d001e641d4000340e0010001c1e00580c2105048001c2900c0070b003c4a00d06442c000a50820508039082261540080320600c0541e00d0400a0240c1181c450015481c0d0302e03072501d842e12038010404071070148002c00400012600c0200d20f0548800c00e0b0024410321072210302840c0d0707a000740d0141706040c210307071400c00c045215410148261521400b40d01c0082404900d01607440d950201b101004036814811740401489083d0188800742c0280ea1035100e0201d6400c0120f181d251400c0d800107110583e0f4084500aa900e00601d408581140c4d8a6a00019500310905125061841d00c05400b0b50b40d090008841100e802c06501451048000c220204015150f047e4840241c840c5050090880d40000c2042404a89140000c0940f44042d007083d034 = true := by decide +kernel

theorem cover : BRFrame.Cov 196582733 196762589 := by
  have h0 := BRFrame.cov_init 196582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 196582733 ≤ n) (h2 : n < 196762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
