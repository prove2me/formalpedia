-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:49.447614+00:00
-- url     : https://prove2.me/submissions/c55098a1-1821-4c84-a5ab-9cedab17cc05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 553956834 ≤ n < 554136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 553958084 1250 553956834 553956911
    0x32d0405060a050a020f0d050415060608010308090303251506230102190b16020c010f1b020a030803041b1202240408030a0e01031506210e070504 64
    0x16684010f0748800c0044005041c40740c64040c6607941d87c4079000078000251544c0a100078804045e204070500889090108a060310b8018007820300b00c41444050140c3c007011031110070b42d440a0045901d44a20502c0f8029000100407642080004144003564510101071000c0030840451103002c00f03896000710f030410300005c0190140041e00380b4080150441c0101c54505c0440b40c051510f446009100711520b8681d45801c5030b0b125003490038103800c0c0007154414040d030361090343c001c41c2d000c585c01d00a242114440b122480742da0034061001d071000350401a070394000001c1c46600400356001314410f6110000c0080c01540402c1c0c0e98010340902c1c4034210320141c018005280c000602138010082c00c03900420240208071010756500554450030507a0000589800341e143c2c0407034410019070007424100f00140c0039911a84002f111030082c2030070b12070016026074840e82c4001011000580580702403085403400c41c070250700d4401a208031806182440125010a44d100c1116098948100d011055210 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 553959334 1250 553958084 553958101
    0x30301060917010603080a12110703050307080a0219080901051b090402070302010b030109050f0706020718020304030507120e10021912050706060b070c0509041101030b0f06032d040506 81
    0x2d5161140c0c805642e22100003002403c01c002900c50500c160300e540ca080d02220407001c058640c14412090b00c1d0004200c5100000e0300002680e82050b414500807125584013500e040081c401d03542c0d02075038018400111a40c1e568820f210704c1c0b0484410000303002540392081d04840e081003030300b40240d0121040c130a038101e908140d40a040030501920012030320600d00e40100b403c40715040c2043c1c0c1c1076006201c842541d003e04014400052140788002d0000500c0d141070018100801400465040d07000404541171512610507a40540c0d00b014007944001c100b110050022042204502d000740b0722800400985400404e00c841e071507181d0f840d6036900d080f4556580310300b85001608941400360502050002c6055031203400040e0030050503169541d000341c00c21500c0c00204e503010a21803d80003040000154040c0d5441c48029020300300804c050369003400189416120703170942a0080c034080b08000c1803103c0c5842d0025003a0510301d00601081c49200c20403d840400c58003e030907540031201041500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 553960584 1250 553959334 553959359
    0x1150306020d0209043e0d0b01030b060d060f080102070305160501090c032f0607171b0105061206040308010608041b0e0f0121030e04060512100b030303010609 70
    0x1407282c45006180c2036510000030b0440d1900c003c1e040710749001c0060040034aa139907a0030b0011444411001080144803541100daa12078107440f00701454031840001c1559009030040364400000130b0a998448000940e4200240b1452041200f1082031071000620283c042c801c03100d403690195121032522180a01d040701c81c0507045822100c4d50760700c084c007101043c818600c5c18040c42c4100701b0705406422000e1050ba02002141d40314000703d020000612183c1c0d21a000c47d00460303131001c252154603030a641441d140e4007a54016030007111001400586901301980590700c0340354225031102c4416412440d00ba5544000c660041c0842d5842005104050280d050203030f01ca0b11540c461420a08004180b400d1122203a00601080d0b24040074089100505810039024100f5101fa00340b44079a00c9458000c01180080c029040c400008107644058595030003a4001c0c00b8007620007010142881000d50741c80002c48a07403000365141c10300342240703481c0c04000c5a0495042d540c41652480c284805039111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 553961834 1250 553960584 553960597
    0x10180201140c1903080105010905100c0311010e0c1905010c08030c0d1404120c0506011707090c05070201021506060a031a040e0606150f0409020c0307080c06010f080115030602 77
    0x78481c09006000608000f004615060748000c0c0c0441c10400043c42c02071308400c0306030400760520078405001d02150b201c0031004001024280303070218440702e840c1000d5440c81035000210401c2c1d424202691007a00c0000380c00c41111720162010010308102402186465010b1301415000803022804000495500030185400c6251000030303070f02d080c8055004a04481e20340382c0c1900a4002641000144121000b400708400034a00f80013281c80c40720f6560a4444a050013011010400c449200341041c20402108028100003d003c122191200d80050003070b400480c1c0407401403044020864404d025040600d0040e0f40241c00542041c49c1c4441c150050300032005880080311031100c0c0c0c401d003035403180152218006001c01500c9a4241841841a1200300c1d4448030001c140070028503c4140710a0200d504440b9101d80060721007018018103400c500c1100c50180030200080f56000e010f00000c94064100c60100d151901c8556a90840c0c41c02c1ea241074a11001441c03080100300b010070840e8004010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 553963084 1250 553961834 553961867
    0x1a130e1002090a0806100e09010c0c021c080f040801110c070504051b12010504050615030406150b0f0d0b040b010c111c0b16020c0d0809060d020d02090310180201 71
    0x440342c0c13181d01e118075000f0103e5518403100100001001405900d0900f81d0308801c0b07110007030081e41d800100c050715841e0f803100001c1c05000c20a224903c1501640c03603035880740703a01c010004d0303842018007565040c0d90802c4c00780c0c8005500e01042900440e5003d000c41d6480050003010b010210318045c100f000400d0014800004141d41022542c400d181c0d01005005502035005000380e80e5042c102032000b01e9070b005110030301030450354000c0303000c4190090130b4a40c09984904003103034445c500b100c07130352500790726a000c18262400032407100582c0c8512409810305655807170041008000390420002a900810b040c01d0210740103224200200d401200c0d40050440050040f440c8910308402610300020600e000fa65048403520921554482c441c880e40540345a0744018855603001100295048000d141d0081c00341d000011001859252201a110b008a04e48011900e40c64800c3c4c03284040e5000002c4c9901c00d002d0a10618000502d42c800c0040350409203011200e0240e03682c0c01500c611074002803086 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 553964334 1250 553963084 553963099
    0x7050307090e01030311060106180b090307030b0702070311012303100302120f01110c0c0d0f020301021603171b0f0c030d0617010b150315041a130e100209 68
    0x42402d01d08000354021031090b901c0384240040c18803514100481038100d0380410595200103144000001c40d5107042e03440c2e41107225900c200e0100000e14160306640014070148880e4200407a4580204018045a029080c400d92184a40c00115450300f80000820740ca050080e40403035040500d00e0196504c41203529100d03c1580c2c694002401c49a070040304808164019100b4074a02c2000303001e50f000c641d580b64841420310b00c01201054540c52a11030f001c0c05540c814070460140030109081544c0342c2d401030003c5586200c441025002d0042c1828141d0108080d4180d1003070f0040c1007800c2a02c80e0060141007100003031a9560b8400c1603001e0010f040380e5040074410000e2450342440206405004440c0000342285800c00170300c488810f0003c91600da034580403000c4c1950303d80500140b0347c041e015010b5652592070041030740440c0e09041c03046400038908902000f801e9842000380100c0c0c942142c019040e80078400381e84064401004198409800580800700104c0c03850700607110440c1c00030b2148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 553965584 1250 553964334 553964339
    0x51204060b09040b0717010f1202011b05010515010503040c1418010f0501080105060f030a0908220303030e01060807030f05030712020a15020708070201080c0d0e01050f0a0903080705030709 83
    0xd802d101040c0c03003d0f254076100074280180203801c030034084650114080030420941c9401c0520301585c155200b19040500140b400804682c42407415141d030300a407002c0c0440000711400d286008200880754a40c212915403403c075410b40c002c10580e44220761100e40303d40c04500b005c0081b8468a040941c3c5a004040d003d01c0f00010605124054003030206481d00c0c4230811300e0000010aa1101031340f147e80164030030030001030559081c4044075404100890041401c4400d45840c5040e44142c042c1d442c9014200c10070010915500994002124000d5405202820149280c01e003262820701c07075000d042d400014100005941c070740384c80c0b0f80c0030b000c2c07001c0d03a0511886e9114000c01143c402d20b000c00503000001203004100c01c41c540b007281c10f142c5030300440c1413000b546e0720040e4500c540040641841441000251110458400c0710022010903c00380840003802c07064a003c0d040a4176003052504c0008000780108580d442002a159019030780c0c48402d0300c0707228007583c95500107081c400400c50b404901 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 553966834 1250 553965584 553965589
    0x1210c090833010303080a02090a050a090203060114030108100e0a020604060f1112040512210409061406160303151d09150a020c150a05011502010c051204060b 70
    0x202803500c10012000203492000c403120b14022000035101200b420120b00603c04244d020310519407080c403a140040e039440c00440056032010140d80641d502000c100c90101d0b09080a402440c0a40e100381c035004002000d204003000c090009024a102d43d600a054000c3c2100c1d00b5007019282261420564090403c1900070400d04c2c0d00c95006040810fc4941b00410042d5012085071002c5804002800442a00d0808407609101d0f43c4161441070300f02c0160310b103240000380170400340d6240071150b8400c10312000b0b8442d2001d411502c100050380740341004c0025004010540c09204410042a103072802d00c001020f11407801e0320701c0055041559441d500c4a9005188400001608c082200d0024a00002d640c0c000041f5005041300b84580045040542c44038200c8a02900500e1041c000b58070b0307a0040844900d401815030300480d0300b0030804280710394540c483d400603050302c81a400b1403182d0226000180c0c01d0701c481c448050b001640030030000c140d4041400602d03800a1048502240d52540c5600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 553968084 1250 553966834 553966843
    0x3141309060806010312020c0303120c0c060115020d03110301060305040c031506030b070c03091a0c1b100215150d05010e060604050703090b0109090c270b01210c0908 73
    0x510240d2001c0c0052003448032100d900c0c03031b030182a031004041000300c100c040390306c902940700300f00181d0021101048080c25000d044e9483d03030700c3c4001240d000f07603518459003064401e008014009170080303208000306030784640070350102c10000940640c9180d1800c43e00310000c100081040d034240c0e1003440b020000410850a14089500301603007c80c4de03031304500700715a42c02c101415001c00d00c05054030483c0025000700c0b80c071041780c0141da29003c00c0c402c0c50520320514031909039042001c0c06801204000c1145901c04100070708400d0302c524280c2d00c02140c084e41d0f01c600e980b035a1511071232400d0014020a40c805400da0000d0005071110390401c40d980d45481c02e540101503ca812904904201300a604051040700c4d8400082e14051141c41c0e6a0f0b140c1c6203041206024407000307161540b14080520910030301c00b4005020881c54101c5203504e218000030503140d01c1100d045801d041501071a025841100400724040a0000340a0a82c030740d418400000c00040000405209002c00001112407040c0f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 553969334 1250 553968084 553968089
    0x50f090d020607030309020a140f090a0b0301060303091a0c1902040209061801030b0f0d02061b07120302120f0a0507050a060f0e07081209100e0d06020a02010b0d0314130906 76
    0x4074085880146c500c100031b00c050582c0c200d84600300d920784400966603130703001404065003001d9401c8180ea8890000d210050251001e4075601356003481c100004044c0e0001c0d2407001c40f59648055083d24600c103003020382c28403889030602c8159000300c401d8083c0d4184240c18460003440280010714003650f032000310791250080d02281c1441540181102c10300d5030180940b8002c0c00c022106000200d1061002900c1120103081c064012507000c10403003c0c00314620810480c803421102110503d0359260001c20240f00521002c800500840c01e00001203480075065480f1110340d940c80e641041003043e130449030b0f038100e070764182e0312407282c40714100110f24144280143c030340301f03280082101d440c1c000107103181080d00ea0210042e6849891030000807602c52043d55109442103604134211905114111814401e101d00070394041d5400c8161300c02c000c030f158000d0008282d40c0d0003d000703100100702001003010015002502203001c0503908059010440020248107002481c41c070a8140c840510108840054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553970584 1250 553969334 553969337
    0x3021e090c0901030e0a0201140a050705031219060501080411013608162c01060201090b150307090519090501090209090a0c1211130c030605030706050f090d02060703 73
    0xb60798009568580241030040900a00611b140f400d81e03030000b0720f00c04001d000403c4811002c1010100d07076101e5012201ca05070440100c075140d81240040c07884a0200760340402042c06203000030039150205024040c01c03904144c4a9801c15030302c544480c00e010810300706107410050034500602081d4440402c0500d075181440b00c0e140682d20030366107515400d16503017100c18184e0004d0003d070a40d42864404006484c40b000c15010701502c000a907035103894502c800301017084041000803854903415400080002d000b0031080403562201c80320010000e18052106400d80c1000b8001d00a0007095003140ea044401e00d0007089050142c1400d0030708941001320111200e9440d00890003d41c0707032281c800b5400188660180090b00000d50301e01d518115188540100c544503140c0d9801804140e81e1006410b940103011040d440c81050a032100812a4880b0140424541003001c503081c140020b44c00142c51041d03c1d01ea14240726000c1940b85900051141580503c050050500580b0380c0c03400f03002c805109 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 553971834 1250 553970584 553970587
    0x50a1d0c07020d03022d120f0f07060c0e060408100b0a0906080a02031005060a170703060906020d0f0b0609041503050f100c0c02061602190b0c06130b0103021e090c 72
    0x500315041079846806010003400100c0107642e01b14030400b04048450703001c3c40c545690b40b0503c0d0049070909002e5106401c6010402048600038060603410581c3c1d8803007555030341d410000444007048070900660080c1030150340040600044448146d0201200304002131280ca070740c981d10b56440c010780f503040d040300c41300b43c000e80308210460030100440801d012200034240032500d450b03808036485220f184107400031544100b00a86d01c501c0d060010f217001c0c5810020622041445041a601a43c0002c0381a2201c81c030345007441140150724070070300c8615840100b90b10b15240523881000007500820503001d03503107036550740000005442008152103800d1900d0262100180b041c5003002142e0080c6030407000c1c001c042003031b1401a80c90300c1c1220800001c6c01240c1d11404900d0001ca246951020405581c128055030003041601118015000c1902078400312141940c84204980c3d4007184085c0041800000c2c0d00140b00601c2c040d845100c1404100e5410540310b003411000510f4a2010350b41305258850 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 553973084 1250 553971834 553971853
    0xb0f091f050705060c0306030604030f050f3c0a050f04050a150206101d15090106110d021506060715140601080c19180503010603080d06050a1d0c07020d0302 69
    0x6104e8150b0200da2a6800d03801d40c60700001085d19a500200010304100c902c1140c00c2d5510301450070380d1240c000d2010700940310b04991503810301c8404c010003c10341c0403112052548a0350461407000c0240c8902065040c10608400000d5455410800803212000401c0c000490151100180c1000520031000d100701240300e51400641000d201902c05450b40324026030a001e00c0d440d500d00e8103070f03c0d0059140400c40781d55007415015048408021140c0c400c504400015403035038454100040720307642d081520180300d00d64100780e0b903d40c000d08110030000c04840010300b01e0b190420180580c24022020078034000c40103442442110442a421f1000450190034089156840042250320501c8244170901d0445807071003c18000400c0d441035010800803007402411303003007031000501c003c01d000350080c01502c0d100d1400d170300e15402c420380c4c08003100c0c9003070701c00a0700d03141c56140d15007180d034100c0484000804148411607200c600030400041d5031410410318006841c1c0440608403e400b0754082d140410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 553974334 1250 553973084 553973093
    0x1a0601030e0a05031e040909030e01030c210c17040309030b161d040b060d0603060e030403020a12020a1703030f0702011a01030e0a140f10060b0f091f0507 68
    0x80000d801e0455940c00010000700180c1c00004a80314244810060b402010703501110f64120320460f000f0340b0142d414140381c8810140c010144c062154002d0320280b042c0c0c0e80a48048442c00b0345103010300c8400c40800b110b04611241ca60000b07074115100d03d8003601c2c01c1ca03001010301b41107005840490002e5006e040800920543c07400c042d42004038501c94008890340b80300002d2826401000c12410030440701607456065490b50300003a2100400b5040d503403155101c19900009056500c000e440407810501502400d8401100300d03002d482d03004003040700460130500d19948089119008a800c115801d02c04035403032944d003005007412011040155600d2500d041911082c10020b824241968146080c0c0381703ca60a54143c480307214003c0ca00003d000034103020280c68900f030051701600d20418001c90030200313000840c41080c1104d03120304980c181020911440101d91040c42603004610041c01030441e030325481c0004110b2560004c12a051024940b49800c00741c40d4028000404903000240c1d110400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 553975584 1250 553974334 553974341
    0x10030b0a02041a13060c080a08060a05030f0124151809150503010b04140c0f07060c020a020319030206010b090402070203120405040c0c0b0105040203040203030c0304093e03070c1a060103 82
    0xc211514081d054402c240d80c60300400e010b230032039080600070550001030313035911003004441c01024020105c0700c0c910a40c1a00d00d00800b4240207400c4405139245042d600d610f021803244c4201c8161200d035401b4291040d034100d540c45061004002c400303022900000d0b2401190184144031496244200499417a02c400c043c02c59107298501c500680c20071121074820140d1488895201c00c800c0300156503084401c5031b1800611070024004d16403403030540e0604406a00082981215109404a52081d4848040704580700f402d820000c1c01a40000f006020b041c413180c019240d07840c0c000c0d1001d410070040d030307001a09000b00c5484401c100721b800304040113549041c1c0502d040c080e8290421320f40845c102d80310316035688814060a406907030000086411500c6c02c1040f11000303440341d800d9a840d10703251103141e0082d0004050450303c5440f09405034504024640041d142e4a83c1c25211900c84150510203145a4000810a1050160b003541c050042490b101e2a0940d04c0c20f58000e0301121300c3c0460014044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 553976834 1250 553975584 553975589
    0xb040506071115190e07090902090709080a06181509031b02010c3504050315130f02011209050705030f030705210910020c010305060910030b0a02041a13 67
    0x60740700408801c8034034070b084400794101d0759160980800001c0101110f000e03000e1702448a000c2c0c825600006050071155011200c50780c03003251420825103504200f1110b00000b40141e40440c0c00208007100010800c2e40f1030014104054242010741145465144041400000b002d0000c1c1c1c9440c244410507501074105112003408030700740d41015540b500024140781c503410707004104030000d401040410398540c8820f01c4a1030024001010043c07080b03821840da0300503106080c000e00c5440c6501082610220f04588540c01c4030b140c031444007800b82c9617211510b2030004164144044800b1514400e40140644402e090250008002c100e2400090514240600c1007000403500305111540010380c01103900c0e00081a07208000d8201d5080c81c050081500c10642d0042e4081e4000b460b86040716004681c03405040b000f62000c03c020b0b55200d00f030003840780044540048902007140b0520000b5500480c42d0b400c4040708030010709007616002d0410f603040d4404004d500c40c1c840403514501c00c4024110b00d030007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 553978084 1250 553976834 553976867
    0x1e1407091505160606050a0321020601031703041a090c03120f0301060809010b180402031605060316030906020403110907030912110a150c090503060f0a0b0105070b04050607 76
    0x100741401603000b00240101d80850005000c0860524248851604008050800108030300707005a6a45054080140c000c030b2808527680400140000050020480c03034100d030f030800c070078000103808101101e2903540002c4c8119284422446995014050b081c0c200341710300e012200a2801002603403c00d4500f00c0c2d40b03150151081000c12070106c00105400640381110110305204490f625081500c0380500508490250800c2d2981c101000e02d0301511a2203000f00d009400b42c40080c8003c405c9108105058024076401030000c20210b10760000b000600ea1441509140028070407845580e801d050b030340158400c0e00d0301c0307281996484142c40d0900b036071600b1604030b0134204034100c0340c2e58440b0b19641510040005101807400c810b806441c051126101540d44512040220700c001402e110080c81a150380c4400a10340b10401304841c180001c2860041c4010f15042e101076581d0300d0302030003400303641075118100704052040c440004d031070740c8903107000c0d0384200094905072500b940c00a207440c1c1507503072540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 553979334 1250 553978084 553978109
    0x50a0b0306060d020d050f12070c0501050c0d08070903140a050c0126040c05121c031505090c371e18171b0a0f091e140709 54
    0x401c2e6843c91180a0007582c1030796441568070302d6042150a142c3d0100501403030b8000c410703400c2401e00c14107008005040c40341440c1032420b92200700460b568010f00d003000d4038992000360801c0308240615016a880301c420319040c02c0b13880d02c030765901e01030704102c442c42805684046151400c1147c10300c101200141c00f8600f804104110300d185618041900700c40180380380e03011020805200491030308101420f406000104614805204c1d15610100c0b103104044140d040c80c01c903101c0e14468042d603104e40c02c107490000c24003424401003290044002d80319007401c80f0b0802c10000140c854800241c907a0000c2c091202c1c00b0941219011460780070f0700030340e504004220b210344000d912119074140d2204a18a0a0a00340c40c5c00c0c03111204a030015040003150018044550082507000501c0d20b0900c414818000400443c03070060110001c042e0143c400040289441404046010780c800c0e641200c942103881319904035064500103d4420058805d800010700d01041143d6400003115402881b10203100f5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 553980584 1250 553979334 553979341
    0x20304080403060c0201021e03040b100b0a0302031306150f1a040e06030f030315120319080702030904180605150a060c0203031b0604120e030d0c060e10050a0b0306 72
    0x3109445180402001981d5800020306024403d41c15150b615070720002c8900400c0851440c05201d81084034220303001103000300010246207034000c0c3c4104035600b44141609101c0e8602e0141c01941000303041c0010300c140102744801007110f5019070708078035109502098501d401e001c22250b0b2901e00b80c201219150222640611202c1080200c5040700e15084818406031144000a401c080100192a125110101c01c0c030001c0b0005c1004548008011284c1d0152401031001e61503c1e4001c58040e0540c52541c1c00e0300002e00c6004501c0b07964801810310540e454004454005000c03900ca09008880004c1c43c0c45e80e84040080c10b00c54a0382103003440c850043c14080c0c1f0b030005050441103000d08405c02030740c0e411801c2151000c00c1511b000801d0031034040141d0103107500c0c0f56586e0724102c42c00d40d5004044076406014034014080e0901409014000d8420366034814000d403543d0060400460301296113a02940701c0880c1482000307290000c00f100800c00c4e0621391082030650f200322032500c0c480d81044050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 553981834 1250 553980584 553980593
    0x60e06131208070c020d030203071a0601091e12021804060b010e06090906040b0a08010921110c060717031305120a021f090b010803190305010506031311060409140109020304 76
    0x100b03d4130f035038120b9600004d00102d00d8101e0039801a01002080d5102c480d42c034100c40310700d1080c603606c12042a49d41100e450351341c007070340c078000b81c98061035888208400030180440103c4000c00742407140090b142c0b640d618000c3c41d0220640100b25001e0f551240c3c1e43c15142c60640e070100e4018a0f0360f00880307105040110b52800200c0000380941a07500c40d580c0c1d000c1c011416226041600c0042403800000c105c1c0c0f404d00c0c02c0103022520320300241242200b00d04035100c0d14a000c1e4004560441c100340040c441e2000c07e000b41710496000079001c1d01d400381402c94520340c00a2810003144920075440c03450101e103035946800c074980701c00400f004001050900c441749109600080d030460300c140001101101c10f0b01d08900c68001c0407460000340590160f0800819140b00000003040c02082a40c105010005002411000c070340c420300620b0741c0010b0401c0400c5402c40d840c0702c04031807180900c00300004640e00314002000d81d8440ea002c542400c3c4c07100d080c3d0045681e59041180100724420040d859403902e40d41c1d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 553983084 1250 553981834 553981847
    0x9060a0c08071d041503030c0605060a0e0a05070509130e10050712090213060303080f0a0204050120100507020f06090f07051207080a03031b0f050d0207060e0613120807 74
    0xe502803c000c0c0303400e04440759560b908003200810015518104080d00d03418020070a040c0a0416038005007403001182040c1002da0042c1c04846182c1c1800d0b1242c0c840b20b07002005080701400c2c3c481040303c14800111076071764002c0780290780c41d440200010001c0141c1c0702507050030401340b120515289081c003049205030304640e01c9038400404c4140080d0105862000890200904182010a07850010003204054101c09140d000315005038810100d541e82c0740f0101c06030310a5004036800284070a403d05000074403120005840e401e420b060720f00050154021004031035048410304010707445100c0008442c2020303c0903a802840307103c040c0040302c4056031102d0742d860321031042c180100c80507090110924418020000034180c01420354440071043e0070001c0280810481d0404003030104011045042c7c0a208489071807540340c2c030340728201100074021200035003040ca815580187c0b1040070000c2036209122440c802c84000c5c2913035408450070700f030880100c5000310740701042c80440d0040c4021a0382042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 553984334 1250 553983084 553983107
    0x1080402100318080417060112030203040e18010f020405040b0102031306050327100c081b1605030d0504061d06131e111002071212020c060309060a0c0807 68
    0x42c08100c4010031540d40d007003240d0440019100082c00b04011504003616035103003407804032480031110340f40d0700c6502d4862070180c1d0f054001d0160b40200410001d0340b48038820300d230780004002030245401c1800c80406082d20002030700c2130030301940081c052140d4603251190143c101e80a00c0118100042d020b61410051803c2c06000180040400000c01c400f01480700c07850322500000309401d2803024420f5440e80da0407028410b0054a050940100c145171044882c4d61080d4040300210540e4042e001941c01d0507400740400101c4009041c001c007000c10303030400041c1301c091045400003455140134103108040310032254030340120403400c1000c4041030600080c460740000301e0416047e5000c0203880c2170071b8040c00000710513103500c007840034140c140120301354034120080c81a1001100d0118000c0100d03201c000c41d01441443c0c4d195500c1400100d885480b650301440c003e070048404c201e403940009081034100701c40092083d0302c88020059440418001c0d113102894904149096007048040a0304810124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 553985584 1250 553984334 553984337
    0xa06180b0313050a05010902130c08070f030e151024110a0609030c14010225020f04180c05040603082d1306030e030414060c0c0a090209010e0108040210 67
    0x803010621042e112840641900d50200869041903054036003140a8041e080050340f080d12000d50281860742e0b01e00814103c0600781da944d2700c141d0303280002900c400e000b01500ca020941d58049041c7c44203000c12401c90002c018540b09609441c203a079005030f50148903082100b041c910410110042c8154141d4402d426515050160b40a01031002152500040980240585041c44400030a00d0781110080d0121405030119600c003103415450a4244e00c5850726411620b140eaa5407881207000083d44294401e1000704000c0e002040100001c0030364107403480d0300707814000050450301003110560303021006020542d000c1c405203246448040180c01001950001c860001501e400000740c82041400038550701550170780c0b1003214180d1001e4000c424098031001c646800082c501c007000c0002518115000200411814007132201030003025002441001b18511543c6c254000954640202e8400750104040c0182c455204400041030880b8003d40907051000c0e6a05100258842c1142d410540380207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 553986834 1250 553985584 553985587
    0x50c0603150604030303020301080f150c0a02010e0726010501050603070305040206090d05060711120318070f0306091a040201120b0a0b0c030a020715170c160605060a06180b 76
    0x103580841040a4a041c0040c0d40200000740100030180c055020b5410f80e02100110740d6840b1000404a580b108203900086032200c40400183c1d001c0400320003041c0c40040e03031001203001e0042c2141246440c01582002c0e012441d0143c007040e858288007030b1204004140002401554075000108125210141480007059100c1c400207041d903c0e400210782500001034481030a00b0554102243c4480d01a80c0c0480000d804000310100304000140705804000c541001c2880c60316401c11100d4201101c0242295500400300001540e03031203682c00c0c0b0025130040345d002c210643d075487c002c03042150f00350340885081ca548043c80301503680141d402040b254418130020729501021700207001d110032035115440c0d0319000038096201100100c040c15108001c2d030201e500c0161945400d0300e000c550f078114030303000a420102c0013440c1740b0301481032500800d000884038039102d03003035132161444400300d881600c505403103034144581801c210302c0c0301d00200403d1901c501c000d00416005640030700d40f4030410001000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 553988084 1250 553986834 553986841
    0x50609121c060b03040c0302040506040905100b0414070c06050a05130f080409021b070501050403080d0b19060507051002030601050703030b1503090604050c01050a200a05070b1c09050c0603 83
    0x2190b40c01034026003a01c020154880c50545800c5040900d03602040b405241040c020505a0405015201c1aa41e20002800400c242d018008000303005001d01136030b00c103459401c80e040305040c40c4041070007407031380b640da20541c4400d500305002a2030000e041c1c0c9500c249800200601041c2040320404040e0744905100c2011896081c250702e58042d6400080e040c80c400203598054603108101e8401002070384081e54080d40c0d0300c400649150107540310160081c281004403070702c600100d60091a00310402001e5801869840404142000980d005080820000101c88042c01030400c090480da980b0f0890071362451030f08000080090060380e00c02014140c591440c1e140f2581d40b1690b03510803416503603130030741c5034940100a0b80c0d0310482510305841c1401003809400c0e0551080c001c0342c02484603074171244180c8000c4500030f405e10003602c0c5007184501070440c09800041c0244080c0c0d000b002181951a1991300c0f202003102e00c600c103480c05080b0b540c03600608030000b81c004034070100d00c50422900c1d544c4947c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 553989334 1250 553988084 553988137
    0x201051e01060f21090201200606061e07150f0603080910120e07050909010b210c031c030608061311130e010c1d21120309070305060912 60
    0x1300791541c10314000803040e650204001d05684a60886030007680d0300034620901048a064003003400d500300e54039400060024502d8105480103010708100d0a020741c280c8142c1c410704505a4101950813030b04003050f6080000609a03a01908142440403c010452a032541d954034620f0710440d41024043c00506181d59403140c01141d6142d202000b000e0144038942d0890043c94480d45070b0f0040920808040006c501984814403030340d01d40741c601520b08800f030455085008004190301d0a101118400c1604003040c03130324240601c0140c036896101038100718242e0840641902e440b6080341c030301940000e04000710010048481e15109801c00504504186100c2c04920390140288840c06450305110f00800341c01015444030b1200c401541d502079900740792541c40e014903040c10200c00d510040c0740d10100c204000b0303590124003060404045a021030f200016070132981d001115a9441034206074407c20901805010103035104c0d03c0c24001d01410641028902954020058400c041c14414815068030f02d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 553990584 1250 553989334 553989347
    0xc03020903060f072304060e060d0f0902030c0303121302150307020d120c0e0f011b06050603070b03161b060603050606031218060706020d0c0507030201051e01060f 72
    0x140041c00742c4840d0310b00315000e600c50300380607121007000544250702c0700242000d0040c0c01804074040141e4901c1c017403524400319880962007039202c1d4060340401c01500c0c00c0a03e407088075488200444041039944a0307004150600e071464201c50f00075001041807445004040b14899405002c215881401000b0380c00400c201c801002c5c07882800e0400002404203544d00006e036030100702040c0d640c1208280039100340400b17980300402c404000c5041d0205801031890412940e030b01d085818035089603030140b0801d012001e21050102629050317614020300c00d041c00c0c240040c90103024000304e00f500e1810000c5c400d81c503000d4443d42140800c0007003241d540780861154040302c00035801c0041488074686a040c003646600c07041d00d40f144030303100d10000c80440e2880c05054426040c403c7c10080445102941401940c0e40b03c030307904594031942000f100d91407080e1072140304c600000360381d035080c0c464440c2d00e806800c44101a010030a01d0440300c141007400b003d44032074541510303030524101d61810790480069030349 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 553991834 1250 553990584 553990597
    0x14010e0d230301060815150904091704090903231c140a06060e011403151c0303060807061701090e101a0337030c05071d01090c080a0c0302 61
    0x30700c40000000407000c1e8805a614065400da00100b15186821002c000c07404000c4207000c907038218240300340012840d065200d0350a090186540600a98035184222907075440358002513840c1c0e03a01c03054001072503408203240d069540101312a050841500002000f0350207082001445d141503030300006d15505181d0001c40c1001c8105c020107003641040c0000b036010340403e006810018480307988004681d0700c903203c4088021004144946152034082801c4000c0d000410219046081010b1400c4000c2429440029590107590f0014050f824180114105202c1c0d030b101c281084102560000300c04050040181100c0030010001911550300c80e00c10b04041024286884591518000700301240c9200d2480880c100d088095414200401300c01d4076500c100361802001c82c014801b03091141a0200c0e000080c698042e0502c400394001a550b0b40d4902681c0c0e4000752003290000540040c030b00250304001d07000d4051002c0c10b018503449064010701c4090003c001d808040d4031000c0400c03045001794101c901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 553993084 1250 553991834 553991897
    0x90f090207080d020f120c12040330090c0509071205071b060e010c110c0d050307020316064509060806040506060108040308010b0a051c0914010e0d 65
    0x44a00c2201e07898245c0da00105141071405c0d082900080340601c89500310703400c5680c0805003036070301d49031601c044400440c0a2001c0680c4d000c01940001c08100e210750519890080c80b40200e4200030710314010981d4020750340301c903005e80c100d03a00740306040780c206195400444041d50300190b20340d1005001c40d191010100d10000c81d600d03400000081c01a1074000f0700007003031031200030b01c406509034070100d41e0400c000400b00c2c5c0d0b43e0089102c903003041c500071213103021700d40c01401100c2c00c0c501c454001905003104541c0c180420200b403013003040b01c1500304a0b40015051010400c0c000140d03401107006103141c12610034103401001e0f07800c00c46035600c1807600303801802609400300310040d04d62403220b645e00e0094806030b0322880b8180000b58250b20604901b446668542c0d01d100c40e6900c1e001410307003a908070074002010b001040c08940c900d4404501c0107007121160301d4010850305414204103c1400d14045004150390404001c80c1c0444000243c0100a0381d1601d0841d41502c110007595200003640e809402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 553994334 1250 553993084 553993087
    0xc06040312020c091005060f210f13120f2c15030105210a0813030201080901060b04150c0c030317130c0317160b07020d090f090207080d02 61
    0x14803806441c00550500150200d491100480041081c1140b04407051006120000401c0c040d90820034080e250b84814030400304d0414040079964011501c1110504000160040070000361a082481c5660000028000c500d4035103034585840e90300e5940040524240000f40c00400011482040d0003412a00d0310311420000300900701d0801c80306124140c1c454811410b41c0202e9903506a2042103134100d4030020943d0303d856484124400c3d0244001801030303110b0240d45800b50203c0c800384000c095070355040c0c4e02203203014151b10014103428800342c80146148c1c0f60460510581c0c411008035010b84a550030706e10401a01114125034000f03203900000c0c0289802d803000801c03d90031a521b51520800b03800808426620303810003250107919644040c10205000c4400c00c046402104243c2da1001ca01c07259a26044204506030102070b00c123031741210200c40701010441c110754180700d4035034031040030f242405080b49040c100c0c84041e070007406110101540041e100d401c200b1008110345201c40701c0042507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 553995584 1250 553994334 553994339
    0x405070c02090c0a0c120c02090f0907050108090c101205090c12030c0a2d0b0a060b0a0c03030f0f05090a050c010504060816111606030609060e1f090207080c0c120303010306020c0c0604 81
    0x2b03203000c2e4241da581700c1f90702c9080d202107050b40c001c84006100352401c2c4020442c00c0c0d000000c1041c44107002a000c1c09000c140c21000420401d603000d654440c5c400c0390004c003092440c800c00c0c0002d0f0703008110100328640041c00f565054074408920040742c0d41d0096580d0034200c09a42c40c180540340c3c0b0000c00780c0032500303004448080241c1891400d20503ca00c0e402040f606640303407004485849250700c44000500059441000240640c0c009844524400b070000740c09242140d03000107e0303c055074220020f42c06031302c5540800004100041c4590b40a107046414686032200141c1411009422107100f1020344003d525070038480c00500c40680b182d07908880c1a0703410449061b455000a010b40700010741071540c0410021200c0c0a02800c40306000c1c0390310059594003022800281c01d1504030f110f100d000706800600c100d900e002824a540c060380b03020b661451516100340c034040c020000a8042e0f48041ca00d541165004001e9030304403038100b00003680d251a41c032542801c1408141c7d0b0a948901e010801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 553996834 1250 553995584 553995601
    0xb0d0e030c100603061505131104120b0a05010f0f0501120921020c0301060e070804150519060512031e070b040b0603210f0c0c0405070c02090c0a0c120c0209 69
    0xf04490007010304000c80c4c002c612295580c42403078010b058220380e003040043c1d240000d41d485960720b01c5544070a542080d03102e080310100f07041440e0b01a0740e4250307180700f44112078500e44500340c01444011100780b8281e00d049083c096480c02c42c0300c0c10b0305000b054041240341c034003240c026854007980600c0522000c800c09101d001d4001001004200610450b04c804a80303040521642040d0340e0400c504055a81e42c50800720b0311880700410860b5003001c240941080d070f402d240034550003070201000105502d00742c950400110f0b0348a500080c440d00e010000c0200c025400f00440d60030566001c0004500b43c54009004503070700c41d4090080c0042030200411040c0203400c15070178000c000c200c05469010003250208a001d01c2250400540010200040c1040c41c0102c00200b0703501c85504140e603040c41c40c03100050103c403400c80d044808507110030050401c500d811020298040e4221140c3c0e4202500300700d00a100d50300d9460001c1402c0000c400006400b40150522220103600070044040392803d000c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 553998084 1250 553996834 553996841
    0x20c0409080415030203100e06061201030b070f02011a010f3005060d24060f090203090c01090f030308060609040504030c02030f190807080903120705060601090b0d0e030c10 76
    0x7180c1c180d41007000c440403c64400c0c0200d9005450f580e4091010384d04040302e40c0d641c0100600166845001002800c0c111031004030568025401000b20b04e0702c03131500500140071b0158543d01c91045902d022840b41070074072a80700c9500032031402e190001c183d0345c0b85401aa00221024600c5912041c5242418448011484540c40c082c0300b000381070141da2921414003207409200500106908502c0040d4000400000c030070b0b0303c41c00311445020a0256540b1b510205046c182d4224a880540010820400342c004008a00c451142840c0800b0028507051141d20000e07007500005041024000100e038543d5221000e481012000800070070140c2000d1802601403120064124020b00800c40c944c110001c0200380891480c04621440c002c5500e1603a41c0046507004180071a460a0240008000c0703403002c000341c0031300901c1c0d038004a9413518030f42011403910308020012810070080c210b05001014081081e6000c14181c1d6002050b0f00200d080110b0442c080c601050065106001a00141503513541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 553999334 1250 553998084 553998089
    0xc090504060b0a12020907140a0207150927140108030d0509010e100e160b0d0e06061e030703120c0c05040204030b0403080414100903120b150703020c04090804 70
    0xc4080000b00044014080c60b4200e91003440300300c0020b013407400054105a000d5990003002c41ca00118103481460390401c4079040100454016485110203100c103035200d40300d00c0c8102034641001c7e0001490003141d8207211005002c50b40d1075580000466225402c1c076000150301103ea4858089150303101c01c1404d80da6000303621002001802c04011610105042c070400100001c0f403c060012850f200d0003484c09080400629041c03449803001e00c0c3d00c5083e107104242c028101030010166180449840d0005544000390ba1114a803c5201400115569078a440c4c0510403000085c00c0016003000002e070514070300c0e42c800350550b45d0014400601503801040d005a55218a080402c504d0b110010b020883c00b940c0801408044900085008640a01070441d802841100c3e00d001550319040300f24208a60000c803c41000d80b24481c0c07a08154010a078214046041c550070804a02d0a00000302c0c1c040c1c444c1c040780d04106d80040c0a00c1810702c02e10111f04605400341c014090840140b42c03c200962051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 554000584 1250 553999334 553999343
    0x6121614040b1911030f090f1002030304120801050d020f0d0b0c0309010f0e070303080c1312020f0f0f040e0c09090f1501030308011401050c01090605010608010b0702090115020a0c090504 82
    0x500010540fa005034002d25840000400460070b1810000b0400001e52140300301962083d45060705020325511308091000041c11a405103450707040c186005540c0c1c64407001d6440900200e28018007098403081401c0c03404680440b16450280c8464002c01d164904061028104401800c01c000c1030b04540d000450080000e84020012003024041d54000c40300030501403401c5401421042001c81e11500c00d05400c0000d80c0761407840d02441920020900c00c280e882041c18880c02c0454600b98984000901c2100c08180c8140704034142e028005841c0b1040c58626a100d03039518004642e64100402c0030507406500604283d5190400010391940d600703030505036501610031030110800700d4800c1c08080381220780c9910f03448456420010340074045401c940c0b0441c1041002d110b1500c01c1d84090241c2c501c564000c003400107007035051a0009000320816001810601d8003000408014cc545e4203003a1f0460301250080f0300c03ca20010030480c1440402d01010306423400d0810007103242a003580c80070707000b039100c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 554001834 1250 554000584 554000617
    0x7030c0c091517010b0603090714042d0b0a060c02240f0c1009081207030b06090d0c08030c07060f0e0d06052a090103050606121614040b 60
    0x1201401810340d120100481d000b00084502008042d180100b022007000d8000c00105903910340401041c40c03604120341a01182c1c1c8014810031103440386070301000d01c0410941d41440041c00003095804044421003d855a05115001140c0c200c40280e1100701c0c40c1500601210540396a0f040c01081c01060782d406901c140070200e03891032001141c14944d00d41030078418140d8141100c5202004454024020080450080c09002e840c00d4012f0b225004405103d03c8450761a40f4003e40c45e800060001885c5c40c051614003406040903580b40d0056450f8004111441410320390315150200075141998040216840b01181034803105801194080594161350f8511070560a030500c100d5000700a00002900f0418800084c80410324030340150b0352100c0e0300c04155107541494880d41c090218134140c445000300c8003055032011036915000f8143c01200854144d07041c0300070248807002c4000081c3c4490940b030030026640f20384500594041400041c0915500d495564504400682e40c0c004c80b04c12000102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 554003084 1250 554001834 554001839
    0x91e05130510030311010e1e0f0c06090418060f1d0c150a11070f1d0402152a0d0801050306090715030605040e07290a0c0609050307030c0c 61
    0x407441250300c038448125120b14201c1c59518256030107120f000c0c09048035502c407400c2c042261420410100c078080c00d00754001c11a001143d00302c0c280180c60401240c1601b007a10300d0f800c42c0d5110310642d01001021200040c0c40307070a02c4c04c845250305000000078407950802c0c1c5031550b0b403081c1341d10548403c805052616500107140b4511350f00c40a801c0c0c0d220707620007940e1002210740c0d202070380905024003c078100743c0b040c0d006c996003061030444123520450359074040134424881c1400e82c400c5d000b81010883d0340300c00242050740c0001c1c0d01e640d590380c00c018407900200d000b5120008850741b070620b00304074401210b414600501c0c019140c5100391140c0f404115040c00001d424140080d50724031586035400600006814500c4030b001c50124030000300304040c4c880320301041c030740d907a072040c11170ba085000010040c3c545810300880c0c504980b58250745580b03a42c0710441c0e41d802a044100c030031100052918691900c50f92900c20002c10201001a04512002c00c800c0105500801055070903800358228454440d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 554004334 1250 554003084 554003119
    0x4090605090102130f0315150519151409060f130e0a0b011d09100b0a020f010c0c08070303050a1103012c100e0603030d020705100b06040608070c03091e05 68
    0x85c40c81c80024280c000c100008210324195502c642e5903c00d680b5285051207682e2000141134011010402c442205010000c00c803c41c094030101c442c00e210303801c003400040c0e0340c83d44c00c8403d401221880c80c080d0340300207902c488104521045074041c0704a40280c0c40c0d29902d6050482c52080101c0310024400d261103500310180d801016101b64015042072074100b49081d00302480342c082405410b804600d01088000310703441800a0290410b0500381c2d0062024600c40c1c0140303400d55500010000900c12804041c40c00301e11a0000c640d180c64050802081d15158420702e00001c09503408043c842c02d42c0800007007804c402c0baa0741e492010200044040b6900d0040200400500e01903030700c0341c0c02c425095420000000c052038513540c046c4005003602d04100c2e61100100a9074004082100d06030009902c44c2521119071241c1c11011030213a1720f03d8149030030158084c26005018040700c2c244855030001004042c401d50400d0040c1c4001d540030685d0001c03105401103c070445000302846544580d0380c00e030045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 554005584 1250 554004334 554004359
    0x1802070c050d060e1e06010e0421091e0e060a0b1b01090203030307030e0f0a0b01030605131209090b010c02060706020307050f0c0a0b0105030f06010905060409060509010213 76
    0x603001156448034a1401c030401040502d85002101e4a5864040ca00c0c603801d41400300c0d003203500420f21200412100780b00c3c003505011050704410145441e0500344400301e454103101640aa030b098004001c5002e589200b95020002540460822982d0644890280c18070b200c0880c21695484582c7c21141c031044104290030781d00f401090740c0c80e001071040105100f8102d4401440200220001034400c02d0350300400c0c00d40e44202c8046002c80e881740e40000454904001922400b04418041c0105c59295034a8684540b0306100142c150364072140403401100380c4034801c59031140c1c00200220385841502000e0030000d41d0788601004103103010040506540500d516508007907000b001b984c075120181c0c0e03404000b5000035110008010007400002c00d10001320000340300f0060001d00401e2241401d103070a91052605030050390180c1c024902100360180b002440d68151126500701250554a65010500916108801400c1c1506150511900d900103500805c540ea2984041445d102d80303030345000040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 554006834 1250 554005584 554005597
    0x315050601021c03020403080f030108060f090d0f1707030914010e21070212070503010f0c0e0d1e11040501060c081e13030b1e0105031e1e0303011802 66
    0x150b0803030074030f01d41040086601c5010380046401c00504040d12030b1034060b19500007440d005041c03440000180041c00f13041112650219403201c0400052600310403031520381414030081e5080c0403000d40646100c0e0300810740401c80b52065400240240362045008016041c0520309458040a400b40d10360f81103c18002c01c08030340341a10003071100c0351800491950306c050a01c40c16510351000c3c440170005a40f000b04100080403001c000b00041d504240400d821907403074581141d411361a00340c4007491141c012034004548641140c07144921291400c0080c0c01a10f1403c080c040000039030320304010000c204080051180b07043ea0200034607030321410300361040900c916000d0300d40541401021440f0300c42004420080c0031050116041c0300b0205e0040710f14079001e400880d145102d041c01c21810b02c440c5000c0f81100f0401d51880c3d51f4551401020035254101ca45200101041c050303900194401c0802c6a02013295010588012603500340240b1a100d400a0150400710012400d0307080c40c2100c24000d40700c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 554008084 1250 554006834 554006837
    0x607020a0209150a082103010302331b0c0d0b0f090307050d261603020702150403050c10030c1d490c0603020714070f0315050601 57
    0x21020165001c000d5455001080c0036541c03c046207103007000f42c03113022907500184503c0008001c02400d01c0d9030326a5192031034201b030351101c60902c01080075a44405415503c00038541040d900c81c1c40322128544100034420003500580d10020780b102d00d841500e00c2000c500300c000400d5861021041c401c1100400c2c0c01b65019090700308100200d2055401c1c030754000c0c0c0024440040703914041aa0341c8040c1030844043e00c00740441e0340740b079001141002640c2c449800c2c2c9040e09203580782e0315050980000801c035510001b030406038082950800c40d113850300c00301d08242c40401600c0c0c40710707941e1a10503551404c9243c5180502e41c0c603201c04030000d02034040e0b00c81d9002c0c113071288041c1c212842081c0b0030407002d082e089070703015402c9881e010141c1d40e503408603000f801c1030204802071600c074106003000022641c0102c50910254040300000318040502c100c0c19078200b071401603500c00b00b07800e210120400c1c12070058943e02030f103800014030007101c94403003040724461600089104600f5418904a82040f5101030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 554009334 1250 554008084 554008093
    0xf0a0c091401030213031b0609080303060a03060b04020f0c01020d0612080a0f050712021c0516060504030311030f0603060a05060904030c03050c01110904060f03020319060b060a021608060702 84
    0xd096000f074011780410340c0010b803444c149a50704e8455003020400010341204406854005209007070744480c0450141450034021803841c181400481d02002c054480075010a030350740b80c05001c580d09ca0b0100e03031300d0740391000000391110692030244d4000c0d800408a160b985103001c40c0080c140c2003040007044010f401c0f0028905026000c24107481040da101288400c1003802c1004000140140001e01d548851941c01401084d9840e40d5500c4070b01041b54511040c0700c003d0102c0c04120447c2411384d03455a07804013012030b00761154641940900080070b1502c809030710220400c200180700f020795520030842142100e8050f19640d4024040b10030580e001500104008001400310340038010300300380c1c0c910900e011803031b0001e231185c09801c40d0b0300d54007861145000018281e49034641800341501034403203148540c00c4186140c0c0003ea494151000e2008a020010903400501030554042d449451001e0650707581c0e40340ea11002500d40149030181b4405003e91000820f41000c00510f00344542207680041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 554010584 1250 554009334 554009369
    0x90f0103020d0f0609120509100801120303020c070b07080c12090a271b0206060931060f0b12063d0b0406110c0102060705210f0a0c09 59
    0x5660075003003c501078410940b200001400224400422010a070300342d5a80c0d91110041c2e4100b115100482060b0810400120010300c40b82405041c18800d1552504005a40d40f18841040d030420449034807144041c1c0b4080740d41014031002c00f000349010002c0200703036124042a21642c030002e00480d4920f98001050f90f10600203000c810002100703a626503c030800865941c2c420301c0d402c2c1c40740103120714012621803d411503601e03010441e4a41044049a100d101c62400000341201d4444446a0590f1490203a0380001101007440c8424030301a0054018040d001000e24401d004e0241400b1560250384800108103803904081402805aa41440310040c1c1d10750303a0b000d890040e0010281500005020b0205440d45986010044018a407800c2c410341c0b66440c018001e020324140300c4122000b5042810500101d0b80d011030b005078451194100181c8490a41880c55841c1a070941e0b0022241c941d401440130646290700b0081c0b0410004805003c003030442030084440032a00e10a05010f4507500184d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 554011834 1250 554010584 554010593
    0x5060d0509060a020c1c050d0603060b21101d0a08040e01080a02010e0103020306040e07031101030c050a020d0c0c08150405010f020903060624070f030201050105040e300a030b090f0103020d 83
    0x10308032040151400c9414884041c8e9101c0888445d6070080301c10f04c2c1d4990349854607080000d1324645134100d0003c2c89a078403400b07600f01903c40d40740b000c240d949907a44010011098910700300b1352800643c5d403811500d40300c0541c5132418240d8490300417044040400400098120340000d10b108180d035046e55a4606170f290540150040e402c050328442e071064881c807066903040b40c01c11031000190301501c0d80c00303000244c800014084944840e0343d002007080800440700c1c200c0d000101d0504000a84ca0600001e4465081c82d212240c91a00082c0250080d410010311102c03d40e001f55010368001c4c3e00801a18007003240d0f1008909c82d02c154590503401c910002011840c06680e000961122400c900e10707412004940c10710503600030072084428041c100c4450040c0f40d030910549015103420303a020040c4a02d100c030100e030381e035851001e401c0c031881c00400c204042c0c0717108041507a8600b0701d6540311030702c89004a002402038004480081c0c080c11040f000038501d1140100d0080c1200d4001e030100030300d00722a0303c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 554013084 1250 554011834 554011873
    0xc060702100e0f060f04150827030f040905070906031a04230403021b0303030c1804060f0f08010e0d050a0f0e1e1807020c06070c05060d0509060a020c 66
    0x3201d0792203903c048207070f199500d451004242c400c3c4501c0c142d036503071400c00410842c8038031003c101c034082001880c1040040c0c1d602640c0e1400b250341100e0441c00c454200340c5401d10b1840b41ca6100e108a840104000035000140c5c2c12407170055003240ca8081c1c46a40b17482c4220102c8401d00c2000b6108502c029061880c6d0506900201c9801d0b42504030720811204090184581070007038900310010fa101d000300d14a44100800410720b0084100c01451450a001e00200840c2c011608540e40750300c0940510786d50356881c0c0d031290b002404219402074000f541c428040090b822075111b000d13069420010721241000e80420300282d003621a07181c2c02e092207240441101c030803c50620340414001d0341c01140009680c0c10b24618840060100450780c112500000c6c850000d4804081800c100c03c020148561142c01280c2d101f003202007502c01a44402d000e00306540c010290781e024513000680022902038111098009620510030041110007544940c50040308a1085030300f03444079034000801ca00d030810142c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 554014334 1250 554013084 554013107
    0x301060e0d050639030109020d0e010504030221130608070c080f190513051c08120f07090b120421020f100606050d0c0320040302030c06070210 63
    0x34079001d504507556407000d14001c0c0a90f001a004038130314000038440d00f190101046000c0864405000e0001c00543c020031a01060091003159500410041c516405030743c03100c6220074124000740640e050a0030301a4580c0200e42c3c41003c400a48400c0903407038419041141c0100c0300606100d4a5245012000c80c1d2942c8098010b8082020106005010500e22005044402458041241d5400c0c4c00300c5032600c07044100008000740300061103104880300300d0a041c0e008982050310241504520404440125074080500820700100412079000c5c60710f05141e203e00c0b84082801000070f0b515150030640d5040090310a410450303d0411201c845400b00040b9140c12500c10b10b011050501030316803a1444440f02c40703a003001603015442500002c2010043e0141858024000f0024541480002480c0d807140b500c209039040d8440001d00f1003184a07a207c04010411201010a022102240d101d400e5116100136407191003800b220192a01c1c1800403985090b038002c250741045005108203854a00c040b2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 554015584 1250 554014334 554014339
    0xb030603010908030717010f081b04020d060b04030c3f0204110703090e100311120d090e0a0501060c0605070e030d020325050a030813081908130201050301060e 70
    0x9190326000211042d01960054805442c0c11000c8804c84502c501424016446040200f400c094200121627011921203a5020000c44082c0305440180103c1c000c0d01c84c9002c26041a4a0443c0001d04200001c0c060401d40344200c488080075035942e207000040e41140ba41222014216070303246505807078820b08500c142c00084078110644025500003908271041841c0c4e01081a0300002d66000b0107512020b03120240440010801c014201140d84155001190000070700482203180452a141c2c0c03000c01c500347c191150400c0785c24122141c4070060800c4040c7c440c0225603d07508002c90450b150381e0003154161186550380d02c108901907120700c409400c0c064103080a20008510b000f002e80c60912804066101c0c07038008503510100d0040c020408945c000e401c00d03040c00d480340a400064004220303901c0300c40c0c1504e000392031500c0300180150003103410b400048c550100081d03464552411403880744040d940d5501c0e020115900c0d00b206004184c9140c1d0001c0c0020310810040c00745074014035614583c902d02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 554016834 1250 554015584 554015591
    0x201110a2c0402030403050a080703050103030206072313231c110325061704020909030f0304050a031b210210091103070b0408300a090e1e010b03060301 67
    0x5040841c041340d109807401d500190000a180b80b04a811031032507500199a46003c1106600d941c400a4540354050681000c01c001054880d481c01c0d04503039996000100100e080e5a681030f03004801491205a00c101c3c00c2100d0074081003580c3d9040c1080e01c0c0c0119101520804a0b000c2c040407130031040200c82c1088071400843c14000e003032610201b0018080c08540001d034034030b0050400f141d81d000c2046501c650100200545182d513105500700c131098009a042e00c000e000ea07118080064254040c0240e00030a001c00807041009000001a1480300f90b4082c0e207a802030045903c0b0000c1000e10510700140440d41398500d0040d00c040405141a4131044034816510201100c01604041d1041d00b03809491103008003910401914003401420000d29101c2200b918040c51b003c41d00307448201c148520001c950a20007558115070080c50200411b0010002d4540d80b0012004094003044040c016601e541d42c001001607480d0758002c4c6d401d8040200f0b4001000c1a070f01c1c0c02c516030415840109115095500e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 554018084 1250 554016834 554016917
    0x3100c1e050f0f04170705040615020c100c05060903070b15210c0a090b0406051f1d181b04140f040609180326060405060d050d0e010201110a 62
    0x2000c000a031221000c401800c0307028a0102088289d41080d044485c0031411440107420b159000a2140d0303c40d0303c203691401c075241c9403100c181d40c0c050058901428500610041166190012000b004428401e82e07482c00945c076101e4034192015004c080c10313a04184102e9200c9803400a80b030074514550240c000f1651003e22000100ea20016240e10007024261151044165490035003e410301a081c29510645103845949030420000001d01d201400d2000022070a102600c03010300300c0c0381c90380b00906004c202c40800031481d01d4107541207502058003c1d400030b03551601a800002c446c21145202d08820144d030031001001031088000040c0c2c0d501a55807900025040464010088213403030f0514140198090b9090207080b140410314124401400565441140300380351544a801000c1030b2000641ca9a1700e502040f010f90540001808910407511035035021980300c101d41c04005400c3c0c0c02400f8200242c24000c0e028069018441c003c80c0b070744001c0100300c803060318200307450240500c0e14018010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 554019334 1250 554018084 554018099
    0x50a080103080309011e0606030e010e0304051e0411090913170c01020d090c060810061403090f162102100e01020a0807030906030b010804051c0e03100c1e050f0f04 72
    0x806d03c2103000000b41c441e070381000080e0f0148981d10302c3c00d10107030091107401c02481869480e40304d030b40161485422a100d61041c110340d18201400c040c0c00207001003083d04107400c10310740b01d81c001548052090750204002078243c00c1c1c1c010300c1c21800e54000340301700c29402903070f201d134030103410034070400e40c4a66080c09100da20000d54002c401085018040c1140b080f4103040300100b503554014a0301007031825400e0100b002c42d034882e02000d2080e0020200a03140e40b0360125444c10107140e680164203d204050084e200c0c1d88685000404858130940e000c801c500390030503540583d00440070040e5004892405050025004402030b076401d80051058030b04070206640c034110f15030030556040e00001c10b0b06000381301c029051322801c00381354070900381000c1510309580d41568900038414041c0d0121101c0844680d007a00610140c0c0408200406550640ca90f20f0700740740050249008410004a99001c960310540d00050841441829656220f00d050700070640c0f41e0741070740000c0041c48102c0c403c120000b8001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 554020584 1250 554019334 554019371
    0x60406110705120a051e04050312192105070e030d020c060d24030501090b0c030103050c01140405061c0506063103121d0a0506070b060d060c050a030c050a08010308030901 75
    0x2006c1050840d030719242030200781450300c174040c03003200401441080050701c80c200c40308403500031140c0e524104204101502d000082401c0c02110070903080c1c248001e001c4416000498001410000c0d030807605002000c00040303998906a40148de000b0604015902d00c1c5411600316a501b80640030003482146101c6c5599081c081813580240d03203d954403e00312040080c02c5246c513801007059840c2c607040d5415a1207098845174010200c90602480c030745d0340e54101c1c2c1081d040c0e8008080040207203440360a0f4012140c0145ca1050540f1401854180098020f117800415507404120304940080005510b130a9064107403014111355036501d00c20100000000d001d400b42504540c050303034854900549400c08624400e40f019445031060b143c1060910117511588250b4540c90f030004820a8035454540219119030018000034080c0c0d800e1000d0781c6403080e0071000078082c56940d50b070200440f83d0500c104076030602030b008002c400985040010400f080084002d1074000c0041c5000061b04032422171681c05a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 554021834 1250 554020584 554020627
    0xb190305030c061f0e10090501090b0a050d0b01180f11091002060103081c020d060303020307020907030504050309040b0301020d050901060524031303110a05060406110705120a05 78
    0xc0354000100e6944106041c001c09411400c141d1120700118444e2940740400c03121030080c4048080c4140000d10340b07080c00c4410317400030500d45030100038558507440a030b4050210884032701e02602102c0780c00204d40c144502840c4c1104e03005100481e00342d0901d0b004c02620004070001003c41e0352170f20054209030030a4440c1610359580000410780e1001ca00c0207101d1800d80306045181990080001000454402800c844090f01c3c542500901e810a10301e03107500a0082109840156150480100030550000010007182d802142c3d242d100c3e030b40d6060100c042e602c0840d00105190001c3c040e81c403050a168110680e640801000035042c014544c01c101d0854004079003409040c2c5d140c020802142c109040d03038030700e4030041a0b89400c129040b000c40341c4aa1001508100c0b044081c03182c02c0d8140352040c1183d4429101002c190745100c0040c1c01e001e507a580c01924162500b80c0340941c02001007070082d08840880b640440580310300451040032300615009200c0c1d820600c40c0800c4500004803100c0d140440c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 554023084 1250 554021834 554021843
    0x105070507021305061005030714030108060406061505070b1306022802010c09030b0403050f03010e06100f0807030b060903010e010207050105062b0501021b030c0c031c030b1903 78
    0x403140010300401810f20882e900c1c030200580340809108103529145044002e12405042071a82c90704c400a0483d1000c084c00a820b581c2c4401100100305010040359040c0514065841400055180c1c841c0480038010001958049034003008003500194103135800356400049100150b60070f124949444042c0d80c80301409021400300c800e03141c003e0b102e0f4401aa40c041516100030052000c0300b000140c01c40704035000140c0010101c000141c1014480c0c002c803040ca0000442c8142c407565244485104407000303481903031145c0304004c10005504d10035600079681006a54541016441d03032042a00103002800050341c01201c00c118940c1152401d009524217646100e00041e6a4030040c1005800c541c7c000e8821845055940040281070000d07141c40005450302e0100024040c009103031050091042412540e100e900d0350001468a01010000d0068458200107507040d645c400c030300301a1610391820f42000d580180d001c08041c585d01c0b80d40030442c004e10140c8103c108100241104001141e0f83e0b00488 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 554024334 1250 554023084 554023087
    0x1d0a1209051314011a12040f0614010602010b090708010e100305031606050f040f24051003030f020604052a04050f1e0c0405040902010c0b07180e01080a0602130801050705 75
    0x50000401e034943d80100103500d144000c8481210074940d561081d5084000514100801314041c8111a141c0c26000c0782c0c041300070071003d13106506102031783d03900740b02d41805540fa08108401c14200074007158030429640d500d0810583c00c0038000006044e015018103052040488040000351080004114421080c4404005441c080c84c0003030980304002c0c00d2031086a90b5806000c001054940031100190307001c481a03059100c211a08001c0d0310302049032078a400c0c00d060600c42c41c01c0c400300c90340b030581e03000f503a0704500310046400581ea50102038ac2c00a200e40d03c0390074084010551a4000700810b55000440681c6096a50015055481c1540c01c16405080442131060000d02d0490075814640500324151840c5440c0408990f14000c9201c1c1c2d034052030300c400510085a11518010114a920103244091401d00c0100107100502d01c0c500c0006400b65020b001c03c50b405c1d80440300b81200e01c114000d16161405541d42006508501d1101000030303850900410828028007860388582103e0341d400e07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 554025584 1250 554024334 554024351
    0x512070e0a0e10050105250219030b0a0c0e0904110d1b060e030a030e061606090c060e191a0c030408061e090c0103051017010b03011d0a12090513 64
    0x400602c00c258001d038107004c820081c47c406d20341440b64111541040f040c0c1c0218400050001c1002c1500c038003500303030342c940324038902108120b1074540305030140e0881202005120b9880c2d5042d01d15800b5810b51990104d8280001000141207100c0020308805c098024051401c4582d070b00c0300c0500000034640844043d101007030041980c0100c2d41600550118003d14040741f494401030040100c03251203d00034a400641e4031a64003003a00c85003070096000400b000706516906100316140e04500891000400316041210146080c04500e00403214404841a009103048105017450050704c004070b40c692818418401c4004c000e01c0980000e200ca540500158545070159800083d15191a0801340c0c80c41d0042c000c0c0718100081350100c159003800e0001d015105c2040851f00c00c4150344c002284000120241caa040c00117400c0b01104100030340c0244040802c2d488540f24a4170012118800c2307a0105c0c001201044403400c02220010301c40c10003c4003d84c50381e001c034801e400c1060f1910281612042d14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 554026834 1250 554025584 554025601
    0x21605070306051b0315060f0403030e0405010501081b070218040f0311060403050301060f18060c0b010509040f020d0614040309051e090604110c030711120705010512070e0a0e 77
    0x3400d5001c00d41840e0b900400d250141c004104d404050b2510908410000c5c1c00465516800102c9030100c2c51a0729003a15596613140003032024071100c100314055414113000081c9540103a80d072a0080c1000c00400708514500700400784241c11081042c1e9000c4291100701c41c40b944045035640c0100e004c0c02007014001c0a50074007411100742c1800000d220780c000320400021035800001d0f03a056030351500e090003035404c948500b100c40200d41d5102e81290005c0b02000154560441003142546210700c100c601160707a10010480780714021100a004030341c442544500604d04042480c80070fa110710000540080c4203c001e2001c01000c03a0120003081410b601448030349021400403500c24021040d4400107060003001c03404000c00a007160f406552204402a482501201a00c00004044003129213039402c3d4181f02d10392a281000b400d0103003030040e0300310714030502c0403c04000b81c41068640600c0d02d50051a41708040c54010020810040503040850b415034a0010440041001090456080c1852440c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 554028084 1250 554026834 554026841
    0x130b1b070b03040b010302010c03172e0311090c0f120411031b190b19030b18040201080408121302010306051804061d060901021306030c08130204021605070306 70
    0x2000c0d0141c8414000c220000c0e1442501a0640e82d082c42c0c080b48114440c6810f4038440070082020740c1040400781040751390400fa00c80c00003081810a0a01250402841945002016404003034414000300540705001d04025208581211410000f5454039031500c0d604441c40d005115140341c0d0182c0c5d08207000a2150a00c0c940c007030040c04030080c0c02c52020102202d04038103c080c9226014000c02c41080304030300d82c00300b0084010100140c0e143e5403109000c080601007130643c188400840c1c9003091394011402c5c8194081d80355084281c0b400a44c0d102e03a00195041100140100c03049541006080700480548000c240541c1703040c800008855058800582982c555410503402248080341407002c2e1800b114010741c10503007100c00000d045d120b4244000e1000d90002f50000c15106507400d00011680560082510446a8480e500aaa1181e2044003a201d10030104800a200310700480e1325042c0c201801d14015100900043c82d0000c880400c200c000690030040d1030907045002d0070828440a0701 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 554029334 1250 554028084 554028089
    0xc0f01020c1002031303030c050d1d0d21050c0d1a0f030c0102101e050702060415020f03041203060e0a090c08060408070308150a0e04050c01030c02030f130b1b07 71
    0xc500358110b10f00f217030003a103012556803009000c0544840f1824503e0b0700a800711105046100c4090014070b90301280941c07060184440304800f84100c01038146050f10030030f040c006031441d5110300d51000011500b07000161002801c140f4614504000d0403241d60002d00c5080c0006040d00304080ca10b001c0301040018100e88802801d01940140c000c4010710b82e40401d00301e24407208464001042010342090088030708252051444840c80c00301440368690f000916580b107544117018200714080200600800d03070154501030000080e060010030000740b41850b070201d1444041c84d0014615544800c003003c4c6003000c0e10300c68032031740d0380307400c1c14040c86401503000000c0c2c0400c0c0001c0005041c19a240c921522840710040d0401807000e02040c0d10015500c4000800c680007800d00c0500394950460401c1c0b8141900d00721040e00c030700c4803160840e500a000710790791007000d41c014505109100b03010f1041d590280351308244c0e0380b01d1100f02140c8840b0301001360031100000001000d03049100c88510346801001d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 554030584 1250 554029334 554029363
    0xe010e0705010e15090603130b070504030c030308090a0c0b090301110c0303181903081e04050d1206180c0810032103020f12040204111e0f0c0f01020c 66
    0x1014015642c00c40f4119090039070940b5046915280804002102d000704200346512403000020b100b100100303141ca460140c0d00402e0340341107586907400f06461601c21444001c0030b000d0541010404a4011654203031b0045205058540d0001190f82d60703524083d40d600021156540411407000c41e00b024450783c5202640e07054070a10f4182c0907287c2556070300004081c01480f00404c10411440d51042c00802e408007801000c420488819160280c2041c404941101e4800c41a0f0b00407800740000c40c01a0b070045400030060480b0403030690003110070903000900303e4556612144000703450700000c1c4140c8803034a001c0700d0007d61808220002001d90001800c1a03050707001400003071011503140304400c0c948144c1552031008005002d103040e070103405400010855020042050422511000d40e40b074800c51003160200009080c16a4800d460f000e820741d1801c8032803c0540e82007a00484100808c541c0e411074400b20700b060010001a4a8802ca20f00601026500800d5482d0628001c00030819015110b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 554031834 1250 554030584 554030593
    0x2030717010902040315050a060f03050c011b0803180106081f06060809102706091406150418120c060b0a05011202031b030c0403030e060a020c1519030e010e 69
    0x464440344070f54098540d01c6d2158940d904041518080107900003002030030118901d4028036628203010780c903814121881e40c080f45800c9115906a280c14145480150b070100c0360310b065440341900320804503124074450f81959650000407481402c204841c004150050140c040c811180c003400000740da91940c040c005200a44040c003401c001d01040c00381c13103440080000180e102c0452a030b02030840d0041401d42e040c41c1c81c9a159028041250000007e15014202c0d04404000b501642507580ea0222140c3c68064a1001003480e14036181d0801e442e44070941c0000300c000703d55612901200703c4c1d001c402201103030700889400d042150724007070255804401c58560010600d800000703829480d00d000011a056070001c0001caa0148044d01c861024942c98811922481c103a6503180b51341c0d000d40401d40c0405c2d0001d0110301685422421545224050380c06000701c8182101070045121607000036070b103100000d2010180c6294107810300f9130500e103503a402003401007120b800c007800c482c103004030000c69030071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 554033084 1250 554031834 554031839
    0x1b011104141e15070803010b07110f0a0603090f02040f1d06010b040302010804240617010603020f270703050601080726090a0f05061005120c220203071701090204 71
    0x1020251900d032902590f801082c1000c0c206001882e20800b07400503d0002d02000100f6002091000342180c28418940220b6400e1180100205009408820350b403008004000b840024800d80001048034454141c0c2ea180d0f10660b4006000d40361601c08a0340e0302c80c0d840d80308890703206074140c0070b500640200380a41190350400881e40c0580c890350102a040c403810101150070404541c4500802da150342607010421040401c1080107410b0034800c8902d0003242d1070303140135003900600c0f9034000c59600074210301ea640e4107002404983c031f4440c55145064003c26a007207241c8003103c0200d512648203a500040c4510f031040c0050035402010304901c081241e40e444d15182d040362100b100ca4144104c82d4620803036541c1d0f42c0b04914003150054003c2c41d4820445881c0101300000400300d010340b65142c03035400c0d1207403501c00b131001608900c01c154a42d503012500c810110304060205111503c2d10001617030300326141c400d005c0e041c0c3c1c4c000d4440030001344581c0c1400210207901501c81d13001d0845030f10305604d00303403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 554034334 1250 554033084 554033119
    0x3140f040317091002070809030d020a0302010501092714030a09080601060c020325120c0906080102031003060903031419050c0a050901030e0f01050711070503030a0c06021b01110414 80
    0x4480e04c20380d940d240c0c0022070b44103210b035060641c0c5240000408031603031070200c84402900e801070b000c1c0490166003050000302c0e59010b503015444000000c21101d03050120b001c1c41c54140c0e840391b031300240d800303544010a0f21107091080c00100340090440e00e0300d181d66450021030f6464104141c0c0702c0400c100c00c4002e001c00683d001b041c80100032090301420f0415a1b403410480c4400711155200c5101080080070401c20007020564801c00c4681340302c001c000503030340c4203081801e0780700403140c01300c0d400704060b0700303100091265015180c01e500078a00080c040010307055002131007000391507250598100c06c0d2806545045402000c1e4050381c4640c3c00d900f8003103101400340c20303406041c5845050640320050048801010483d01e41c40f044028002d00007818001005449042c000c13101c04118013400e0390200c0c640c20000126814070349070750b075140701003001903c4101c000d4000703125454038008080000032034000240940050460510405035487d464200810b10407001d0003140e0b0301417001000000f0401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 554035584 1250 554034334 554034343
    0x3250801150306030812090c0a09091e0809060c070506030103150e0705090c0711030d1716020601030624060503060a050406052119110111011a040b0103140f04031709 73
    0x140c1c590040e01034140c51380c031f44441c18041c40140312600444096000107030204207030004070009001c0c1801c0000c1340e001d9440d4545688500c00081c1a03500108a000c00504058004001c500392a4081c1d41c2403c0d11500041d00759402030b80290b80021491203840e0b1040d81e24480d040c83c0c441c0c044000c0074110315006c089511232000030070f04c2420100210b1a10280401100c0546000c1e4008003610b11000004502034140e900c0034503490074060b910b000140c1c91001c60001d8654503000b5400a09582c1c4c41c6131740b01d00140c4840121048865030301600000207810713850001000d440e1035111540c0345c0ca00307441848000030003030303120610850030302d0020403503a120120f0f22440a004c2d01682503c80446850080c54840d40919030300c03030204440b941c5024428281c1c0301081003d000d90390798846641c40b032000d600741c0700e03000088509040d2080c0f007140240f615a01c042076625044c103010610701d000201912040d80c04460819520342e0a05c01c1008166010082e6500b5114011800d042418540d401301c0e81c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 554036834 1250 554035584 554035597
    0x13060f052401020f0102070f0c06170606160506040605010314071404020f070c0b0307020c012f0705130f05061203030103080d02120403020c12031e032508011503060308 74
    0x1d5084824068900d43d100303021114510480c40e0081d981c48000b0300e0050484140d016087c1d07004486003e002c19032501c540010825041c074a45903c0046e140e80040001590141403400b000d0140503550000088040c0450341c851401108001260361540c203002d0701c01d214141e880c41417070701701c80d005021051884124142c44507003640c00684a0021513040c40b50b0348a6040041c0c001a100440020381890010065124400c03c0d401d4a040c24201c200569047c40031312014105200310a0308010085440011710400440c2c0008a56880c1d0f0b0711800b16480480b80e06000282c00c0d00d480c00e007213a186541c0543c540100050b141480b0720341c41031a1058036800103000040180030001060411011581c06442b40d030b2104480306401c0e8142441c0103951820159822401050108903443e155031000c000d8509101d81c0a40030f840130039440e07002e00303400e600003401e03c40302e00c030404407030700038a0b05200c24003e160400391140c1d801d80d410400490903c2030701c03400402c10181441404d00010b10300d002502e81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 554038084 1250 554036834 554036881
    0x30c060f0f090a0b1e03060130050c0a020609070501020a030f090b130e0a09051b0105121e09120d0207020103182405090c010c0c030b13060f05 63
    0x80300e400000c030300e01440c03040c014401c0d40030705045004501e10016100418407600302c910080281e519003845c601440c00b003240d4031408106545881100c801c59600303604500e0300311608030325240310040003010450b03800307523000f0340c25040c0400c03d0100190100f203104d4000038200001c000035440d200c0001d6541a2001006040000e138500001c110790040503030102a01000100c241c0342c0c48803103060b10384480f0a104808540d07007032a0124844200511510410702e400c900a490740c410305c011104104c040d91506a810400104121a19440c0540f1403500a111030852020b41603030841b034500c0c050001030409107950300701160f41040c9604200403141c211a0034031001d0713103820316400140d00401580c02d07070882400b141101042041003440b01c1641c0703420f03051042d11000b0b0030440c18108640044031841c0556224034100d1701c256000e030106015042c404c00c950350010b500c941e164400e0f10f1050760400b60f4a000b103031500082125602490301c1220014108124501d0b010802c443d418124004924 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 554039334 1250 554038084 554038087
    0x1713050609060d0c091d15190306020315040e0601051f0c0b130f030e040c0c0206030c030a110a0806040c0813021909151a0a0503011a0d0c0809010b030c060f 69
    0x551503002e2200b580c010000214110324800750340745803049001b0100c807064008080341d41c400480d450300020741d860354200a003160b1112821951248020f40c0050030369005002848521f010a03a81c80c010300707400b0320054000d40215458a014464a804614910400042d50b062051a140e0b4083e0700c5e06d428036005000c0395a152640c0790040c0118404a00203401d008403004400306068211201d51a4040b09807403c12000740700d49402c44540c4030801c0002d50062080010400c5042d201e00a15080a88039000107019402c2c501d0b01e003d540c7c4110b0600d00800c803003404000b000e251500ca011043c10103410240d0301c03464100001001031241c554024841c3c10800c0c0803e40c4a0303480050034000e010b500b8410004031000c04110746c140f8100e841100e240038601122100020400000c1da400344070941c07156411a420202d80002c905021580b04841132414007a00103400102d00403410024215180c89415040401c842c41c25280714010702c500907808240302030456101c980807291005503054200c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 554040584 1250 554039334 554039351
    0xa05011506031e110f030f0618090304030b06030309100207031e0b04030804060f050106030905071a1b030c010c030902210309100203040915150e0d0206070204091713050609060d 78
    0x5001c035000700014010517020200800040e41100140d840c018401281c013103591030b0507030f040c0480300c0200716040b040541090004100042081a00315001900201503d08111045001c2502e0846500e000340c0107910a800400c14404203d4401d0f0a0708452520444010070588034605030782e80107400182005038140c0043c040c0007865106c0b599801600c2401d100d07550b52542c009005d080c030000196450f0003140c9002032143e0f40008090b03040d00f40c007898030303040c118020172a5000d02d54850349031145000c03c1001a4200d8401e22940c1c10894030350328002624003160051000110b62030210350611b4540c1030362504d4000300001900c900c040d04882c0d00300e052203c44803c03411409075074031129006081124600d494180414940f00355241074402414940400400312440c8580d895019000130040704d00c2c1001d0304154006185031400900082200c0800395079a801400c850340502c0700340400420310b0703c80015a907409400401085420900780b00420b030006005124040400038000d545070b415 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 554041834 1250 554040584 554040611
    0x60c1103030912032205060106030f0b091501140304050303070e121c05120108030c0606010512370605010f03020913200706021306090b07150e0a05011506031e 70
    0x250202c8880408a960512401d45010390740d40c7d50a0140c000824207005003101850640e00c03504440c260000d042c3c0da215191078910140107060071000504200b1599211101580ea200055001b184034200840d920302e07110030001c3c4003d0081038158465440003003c00300301e00c3d000440c00d94020b0004440302200b5603250042d141ca1045120210042003810b00005482030b0100151030000c503110192515036462b00011030310392003041010101620b035080400d210721201c00855000506c004801c01c00004201118064540c02c1d0140c40318083d1034240030700a65030310900c50720031320301306080640c105841c240010380b4036142c4c400c0b80342c0212b035180c07441ca0005000356001c05000601c0c2d02140d0b07517100c1900341000030b9844502288144030740c3c1c00e00020710710711039a4100203d8160500050900e03c1c01d40d908105c4080041525888684034504020942414031042c018640b00b030b03000083c054558644103442040c20391000c2e080c10b24202e46680c1c0940007801a41803000140c50000315002c0c400070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 554043084 1250 554041834 554041861
    0x60102160e280e1b0f030717120301080f0c10050909060406030c0e1506070b01091e05011502100c09170703080301030b0603010b090702100b12030304060c110303091203 74
    0xb58600039050403140104450041500d041001100f048070169140400074402580110301225805034844402049189503100106401051100c151103413025907080018580c0c0081c0c0000b1840e41100003c03445c200c508008039141070800741d0b61040aa8034200c00a00700b0b00404104900540103000024015543c1c0d6000c94013031544054050030441d01c03803030342e101250411203501d040807910000388105460504181d03690300703034041c0c07242089a0a02100401a00c643c82c1809100610950100c1c0c06180c0750186a01070180030480113840988042c0080c034041c881016505244d1400d401400416802040101503e03102954080c5020b00c0c101c0b03803482c0542944c009882c8480103c0080100070080000c240904412002480511a10010440d6580701030302d100c005603004500306000158250003646803024000c24060040c0c0c003c0e410f1034117507402100d04503481562903039a00d19071074021286480420810300258110301d07116840311364030b641c02d03207201208002c00700006400b10003095 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 554044334 1250 554043084 554043151
    0x19020a0b100609080a050c010c030516080307020c09040f0b180709022713050604110c0f2a0103110f0d0903081b09040203040206070b0c03060102160e 66
    0x11050302803440e0082048104105a014010000c2c8030b00000140c2c500300012410030f450740100250820070051001900c1c081011113044050040034402d044113048400d50384142640540280381d50f920b08003200a00b0040c8001d040b92140085400703110105640204848440e40d204002801c1a00c44d50001c0981c50304060011405108075100450203a031181c024181005100189100b0000107941155038030822181550300a1038181d04081d1010316a08020b40080c009440041c10002d00318a514079980700010312100da41c080401d180f40f1031000c0003100241c80009484208c040d107524041c5011010004046041644032015921042c92010440e071001c1550500140d0362200890400003910390140d081d40815841000213110001400b540140001e000000794500003904082000940018006a8000005000c1e90000544c0318050a004810201882d501d82c83c6c00c0000a00d0301c4444001c0d0070340c1b003850300b104010444104034015040303403100c004800d1200c820741c400c90b1221581c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 554045584 1250 554044334 554044343
    0x7080f0306061c0b01021614101e0509150f0f030a1d16090c02070b0d0e071701060815070c1403161b030804030b0c070c090606021b0619020a 62
    0x1030390740254407080c3c3e004d00090b030020303000c5d60f40355031410742c0740d1101040610418a0049140d0050380b40c51900441c84030740040c042c00c100044004401ca004104c04280010030f001c6440061a00400d10f0200e0105400c4100000e220f4509112000c45440034055140a086500c4001c40800d1406525411001c0700d000780200c41c02440c4500c0c0140b690b502c4600c00c4812001c0502803020544541c94010a5044107a40d0010301c0c3c07981c079103c94072040ba8401005108081c0e43c660f0151404102803200380000c20380d51180d105402b03c8004100d084900f168400300f140e41c00380700080c3c80a440100344a5105132141050048044181485400c0c3c5c10120051106030000090718050301c134240d0440307511a8011114002d140f4241c480c1090b0541c114000a81051001e020030400a880d24284550146441e01120b040144030340d030b40e412501c001d800040c40141c44110500c030755503042007510380800580540030940c0220901080b0b891080e50702e03400e420a00010107200881c002c002e03103d14241d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 554046834 1250 554045584 554045617
    0x1703040c1e0302040507030e06150a090e0d0906031a060c010216080a090801060305100e070f08071a0909010306020f0f0708040f0e070906080a06051201050403030c0507080f030606 79
    0x4103540340421420b00040744120302d000c0200d000c3d07600c04c0c0305201010b05140010400d03a140c07444104a81403102550355400412032802240d007814a00030904011100001050010b02c3c40304080c11044d65a00000201032402d098403803240c4c54000903000b0503c050340d4a40d6074403030394040c0b940a841070480004440c10894020001c001c850070080103110300e56503403082410b0303c4484031406c0c1d40480c0310240103540850200010300f031480e0700128010010804540c180d41d540d2a80c250502116072240c201d68111000411554528880d080d81030713070490003400e14221506000030f031000d4040c0405403a0942c04200c005a07499001e0440307544000c4900415200d10a40c0303000c0c41c0aa100340245004002401e1001942443c0c04e43c0c4a0b012b40101c2d01c07280411401e100d0300300c44810006020141c16612814005440d464071800514502c000000100b00c5182600740a000e4620755401c42c41002070401c05240400c80721416075199100c1010125540e0301e507880021034500898200030030f6500c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 554048084 1250 554046834 554046869
    0x40b010309141b060c070b090a050a061701062c010e0315180f0a03030e010605060a021e07080d0c06150e101a070f02030a150204140402071703040c 65
    0x80016050840525007404030003110b0031034148146400b800500070134a506c0603c040c01802c0e030110203800141d101070a01d4030079035130700d40004280303c0d510361100021400194001100c50805c00705507000d40000e0415500c0c94940303a207142d5125101c80c02d005056040440d0251043c1e1040203400540000181121803811031442c40d04002c1070241c604104a0b800d01550703201845021407049010b10800015055404450300c1c20f8000d4101c100d0780c600195a210b50225095851202818100c0c60603030080a04464808001000e401d154550009070790001c0d8041004034400070301d82c00300d42034510704130742e00d0f040500d00b00c00a80700e220200400304203403d070045081030780b210100303108488040d220202c0780c1d6640e4505030b2500440320a10412070301000301c2d4020034032002c22995800c1c4054116403c0103100d07140e0094030032140d621001c03c240c0001e400c102c008040da240700e220b15411102181b51030844c1d601c0309510a440b00786446065800f000140c180403052444000030401002c805200d0306 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 554049334 1250 554048084 554048123
    0xe0603010e010e2a0a0b070c080102030a020a1106091009060605030706180906031a06030a15021801110706110f07080105040312050402091b0f120105030f1209040b010309 75
    0x6801000c201565004400c0c0c3c403182c600b04a610180f132003030281c0005c2001d41000c0000303000340c0c015002942c061000820000349020300344010744c07161607899801600c405181400808001a640000c880c0341d00c100240880b1007030114442c6c0209400c000009506403c620300030300502000d9009507410b0140c0c41000034034640110880c5112801c00204510305a2a940f040c8129096070201801701d07004580c1c1c081c40b5029105810760003420040444480b20311aa07181800084184820000c464011610102e0602400c1b507460489100b428640040a400c010312541c070348151290300c00708040389c80d8040048000380f2803460b80e0503000080d1a0b445444030402c074080c0170140d030b00700d001404100d501024442c044c0300e110b001c0c9900a0031001280c0b036840d000140e9800101a84040760300400100d038094005000804c0c0b0080b441824401541c5003e00701802c000003101c26900542040c904604001c1e2032008030f0361a038508a400094500410740100c000f0a0381302002481034074a18102c6407200d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 554050584 1250 554049334 554049343
    0x50703050607080f090d0f0c0b070e09090f12160206070b01031707081c020f0d09122d0905040906150f050a0515070f0b0711010c08010e0603010e010e 66
    0x442c1c06031140b42d0203446400044076024802c54600340c40d0340145017448504c0348110001c409400c164604034906642a40fa1070038013240c1070700d503500414810349042d1110300344044001e80c00100a800b82151000810b00140c407007d000e40c88412445000030402c140615540c00003924607000780525454462500d840c200c1d084080c00305031094296103038110140090700b0f0440d205940d0211225050000300d500c0343c4a00003110b02c100c51321940a00111285180400281c01e2a03400b100c0c0c0070540030b40c41d0900c00c07034644400410a080000b1500c420350b039503003007032a14426411000d00c0d103070298502020454018100f034004c654020709008400040c05815000410f652942c40440c130641aa81c100c1800154664460340e5003203d012041000145070011801000228181d166450040a40e84200000c070700307424111600c0809000740721040350700c04200c160024000c4000c102c1c04450350350182c1300400c144106e841c2c4540500000e4000d89007034100300c0000511000910800389071030750003a1034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 554051834 1250 554050584 554050591
    0x1060801020c280c0302040c031b0c110414011206020415090303020c0108190b010908030d0504150501050a0b031801050702011a09040c050616080310060e0907090b03070306030507030506 82
    0x41c85032451080b509036405040c040e040660144c0300c240c11629550038030014008030407204003071503620390b511415400705c03100909540e843d8ae520200300c008903107803448a104034044010b018610b008840c20280420a18250544040407031120034141240f0b8000068406e981280c1a822044410740355602d07040190442600d100390256000b80640ba170044a00c0c02c41220040c4e0000c07944200034003101d103c1e03804050070340d806240c0f03918566100d20b2035501e982d000c0030003820402d035903404020a220f024996941d0045464009101070352500d00000e00c0f0a000c1e001d503a84e001d500001144865007000944020041d40b04000c5c801480c000a02a000b80f120598005240030311258144c46458801c500920550b4002786510083d401c0c0030501c1002d400c240103070080010303100e8505002c5031b20b0b20302451044201000410916007400d0008082c1c95200c10070f940110300c03503070912420341c0e0400f0f0030700f0540b001f25450310340340c0e900e41400318050096603001a0680c002d583c00801441404111b80c1d11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 554053084 1250 554051834 554051863
    0x1a1212181002061519030c15180b09040b060d0906090c1203090905041b0b090a05060f0306280e01090e06061c060f0e0124060f0e0301060801020c 64
    0x2002403804020380c2c0303c40e0101c451541e04910800c3c44030403842c00150902e2060f0802049885039a2281e0314098a054190003401e014850b80480120003075020750384102e800e52002081540a1501d61440414006c0425080c410b035203a0002290035210402a0351680d400c0c0c00042c0940605424148000c1c0703504038003543c81c0e81c503000c404030b2480d450700c401500b0395034142c0e9102c251514110420300101000f40040312401007402003812510800d21040c0301422100740340c035030b6680c820300410000c10300582c0220301462091000b00103554650302a40e41c00041615007640001c0304803454001d001004000191900034200007154403c40030204c00d046c2d581e00001040b50803002200d20395100e00c00c40d03080b44d21041c1c042c9641d002510120344548030300c0c4541030109401d000600608143c0d80c0b500c285034110f80d51070000e0001b16019940103140d00418000c511082c5090901c0203202d102d032401d180d018410128a0888191001d503c00c0d070042031818003c64450400224290b25038000740300710702 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 554054334 1250 554053084 554053099
    0xe041a030705100c06021315020609060f0f070518030f030c0c06090f0d081c090b070309050d030b0312070c030b01090e03030f040320030310091a121218 67
    0x350504081d12000590301160712913003640c40302642c42c50040d5100700102402034003880000203801c00380c500c9608111010340c015100510700907603100c0c941710b0010103549800403400244480b58055640254008090b0301e050f0f55103c41486018071100000e80e0001c1e054450003040303005001012001c1c0c019240040141e03000f403042e03001007201600420302c0e00380d40301070346044c213030079500d054088002c0c268880d400b09030030229030310140c15022107005040c12100e9110340c01502002001c64006074812101c1c2010000500c40d0f03118a6910058020581c05141d0745000c4030015a03400c10041000f460b2030101c0f280c2e1403c13945003954030a0091b10081780d91403039450000c00d08516500540c40f01c22024001107003076a450007000004034501500a80c28007000e01e90105900d148100c440c41c070b40c40c01000440d40d0b401d165080c00b03541e64090f889080f40c03d2401030345c0302d0004e070b030308413896003170402101c0300c0c102810851358075130504a002601c50880c010010f41c0c1da891402e110460f2080034011507041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 554055584 1250 554054334 554054339
    0x7020c0301051012020a12050604110102151b090a0f0602161d1302090f251d0102030408060709030210031e0f0f02040b1213020109060f0e041a0307 65
    0x14241c0d201510a40b460f4000c0100070300400c10400041d1000034002840720301240d0b0341d500403444a4004030310940c2c50703400003800c020a00040320400b22000c4000e10040429000c200c40c42001620080e107144890b0754001c0c031801d050030100e001d8860040e001032030b24044554035800c4003507840241c40742c10058044c40349107941060004451208460420904a0b001100341c00846407544008180d0f5001103060010140540c940100091140400c0c028410582c20319207100814000d00014070020440c00c0d00034102c9203a03000004607a0303031010440071034245401c000141d095014a0300841c52611904080001c1281d002c0d0700c031802c4078000d540d000d105160340300084055410052540b011001c001a802140fa41c03240d0010701c5c1c0701c903030210004259800c440c0d48004da82c456070110b00f9045001c9120164141c1410849410101c00c0d5844000b60307000ba400600400c016101d40420721240c0c0303010340d04083c001c40141d0481d1500800411940c0d00450b4914103031095031400078024482c83c14007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 554056834 1250 554055584 554055589
    0x170906161707020108011809120201050703050a060f0512150f0f0106090b16062018030705010e10090509130506071103160305070206040b03041e02011d0d12030507020c 74
    0x440d80081d0f010303514184141e08020f0170075122140038900340d0a0035501d84405010803640703080380c000100d2036400401c0714100a5001800e40e1809031910340032900c0c4c07100c2000031100429040c2c0840d0001e0b50000c006100e01000581090b031148820b46408040408000c2104140b03918240f0030810160000803998803480c0c119005100e60152030b0111804101184903418110305000d8101e10403c400301c0c50b610311031103011300ea60b20030840c00c40c414400b040c0c43c8107942d04100781480c10b40c01a8000c0019525050000b0460401090164040c280e0110070708541340c4180403040141c60080c212200f1801e04660b0f6070b041ca02c440000351170038003841012950062050408480300d40303c0ad0300841c20011081c500c85101c0305404021024071101304103440050300e400c40984020818030349541d44038a0581000041a50f000c416244840304500354280144c0e00014034206203145a1203c1c59a0119000031810221007010003500c0030745441940032002d54180c02040c03007500307a582540c184106050a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 554058084 1250 554056834 554056837
    0xf080d02060637060e041e110d0204080c01030f05090d0e0612090607020f030f0409050a2702030c0a030b040b090712062301121709061617 61
    0x40400041c0c21540200e00300d854284400c1c801e481510001030203607450041260312501803207403044405035510808104181d0444c07421a0510b00c150b074148044085d8201d0b240c0080d1310000301803002d50740c908040c0e071010f0000301075540858103510115681e540318040d041d5105842c2d02252300080c04c10645401700c0080c0e00401e8001e000c0c400040241409403a001d80d00d0010350884a07810400604c51846001d10303c000050080a0350b2024189505202400904283c0d0402044100303510030014a203803100300d04100ca04030788070960001000e880e00000344001c0e1220070420074851070075804440c4d822080c01c05442e1b0041c42107080307400c114079000520510701514807020f024105c0c410000340c04a40100d0b20315600417050000d81b03a100d919520034184008142000b076422582d19111140799190918040441c030b40c040912900940c504603130b03100712078810300c0001c01c00701c8400c10050002496805440460000521154a4040c0d60510060701600b0f01002d403020301c0d120701070740300c0940c4800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 554059334 1250 554058084 554058103
    0x190f1406090d030201021c090c0f0e0a050601030b2205010905010f2c100305070605040b0d0c030b031b09060607030807050c0a02030a030f080f060a1202060405040207060203010f08 79
    0x106880d052007425001c000403038007502c2003541507540030480e610740004c07884450300303070404000d2002030038800c141031000100401d5001700c2040a481e941c244428401d030810b940d4000f0580001003015601d00d00100e004e000601f80f0302d074001240000e032034404c071a03040c00d890096000c200300b002242c1c0e85807400b5003034a40a01c41d9901d50300a1034000c0c000038400d0072801d02034140c1ca603007610070380c14294408810410110342505145135050001d00c20050140030741c40c018012032912a05060824080c2000d034460410341a80c840d9890313980992250082c3c2000c111102c0040c10f43d4420a002d0b46515200312500304181d1050002c0030000b101454480c0c259090740d5011340d0741800325684c006050740c2583c001041580720b80b164201e0700006035820025485454865680d00030582800760014103181c0001d0440c01c181011082040920341b904041c00701140c0450302501180c0d6000d001007a024070450b000180c01c940000303210018404560021341c101c49003084c1c45040141c0e0b8507204d81d150540d54 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 554060584 1250 554059334 554059339
    0x1020c010f0302130806040302010e150f0114040e07080c0a0e13110307030b0106020c0406090c021f0209040e0a0521040e0717090a0308070203070203060c0c0c190f14 73
    0x607088654030364880d502514803000d189100d01c003030341e032601016441c1c210308890032030050b9182d90030305e0030740325041c404049100c001c9070480c035003401c10004000c0d903900305008000c10000150201d000c290340e0354000c0210640c00b00700b51031903180c440707c480e900c03414010030307060090070510400108625075540c00b61240703851705200462026181d454003040d8450041a6502d0700c12940040046203810200600070701040c0c00408164504000780816500301d54041d65806181062185640d80c0200e40d07080d052106072080705015000c0740419000b40500f04549030458507000c0c03a6100b40c1c000180004889010320101e9130800e002c0045843d80000c4d4602001905000b0711003000400b00d8511580d40048490801c0b01c04013803d40340480403d08202d80c0c1c03a44580c00035000750305040e084821160009003910180d80b0f84600c90f008280c2d42c1c1000382442034525000110710301c00040a11400c40c002100810300e0fa00e2212642081d0304000640c00303401d62000e00c17550005907c0e2103080508007601e801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 554061834 1250 554060584 554060597
    0x8070b0a0e04021b1002120112020f040926040f082b030b0d03050702130203070c0308180a0f1407180e15010816080a0b010e13082701020c01 62
    0x103510500000e5003105a09130051160451044103206041c49014244540401c0c0141c460b80319040074005244180c1c4440b55501e1001d40d00c002507150300703241c02882e1006590100300c0344150f2618100c1800d2070100300c43c2c0761a034a0140302c55205030344010404c0f1820079403418600c80d00d5000b4a0707241c450803d07610b90304c0e10041900c3c17101e00c01580520040d00005040000d03030618504080740c01a1a0004200e0000d00001031000442c9001c441912400e142850304600751710342507034040d09180340c0340700160900c54882c00140400e0b04c0342c42910030400d03c0c4000e03200064510300d000d410308001c40310100c480306020700100018030b0001a44204640111801140600750702c80c44100601c55282c00707034414042e008a0380f800d40d504e21900750003000301c41c0c02400c00010501d40442014416042015a5003000280c1000320340600c07403150650314407020500158681d09180d05041d148071000508501012a440d0300c40070005800c0c03001c0c6007669084002034101078004903110710041e40d007103011540c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 554063084 1250 554061834 554061857
    0x501060816090e0a020d1a10050d06030501180b07020c0306040b0a2a020d02010204052103070b0c1e12040b0907170606030712080f0a2708070b0a 64
    0x1401e03000c0749101491070a2440c5001d40780d42412803040c1085842e0956940c001418981024413441500d0080b4100748545017071100e0355000aa00310108242d50040100c04912a034015400f644024011070340000204215010041c0c078a64490840310141c441d05594030001e00c1450021a40c0300b5150b00080150010383d42e180c0e1240c0c0542000381c004545243d4030400ea0707114001180c410303c40004c0e058982090300301e0200c0001e28110f085800b1000b10390050004115a442c2c410222454041d03080401e10721110101040f032860041c9034000d0848241102030084200c038180c018030700590302c42d10b8403070410b2541e49280c0041c840c0d50310f01d8182c20360080c0024085811007101a4002c01130105542074299111030b101421540d0440b40d4600e500304100b40251391030b00308440e4000300406541030b8100703401e40d200e51000e40907250100d029290005801c0d40110700c200c8076584400030440e010060311540c07501060002c0143e02510183e031203949804201000a40203952120309940e03228811440c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 554064334 1250 554063084 554063101
    0x105180403050a031b021e071202060d1e0e060f0103050307020922061e06030503070803060f0a0306090209091b1e030d02030c07120201081f05030105070e010e0405010608 75
    0xd0094031080101340c0d40b0401e080003140090340000c91451158020910038040c0f0206807945400540300d030407160700c0301e2010080041c5100f502c858680d0110350b815200c417651542c21018100b001e90344110407403481c075151130384000340c1d2002c00400084022500703266a506042525604203010280c581d51041c844035004bc64400685a03011881c941417000411300b4a00005014545081c1225030984a540101d00f425802c89031400c111401b00050050310f165444a5444e4812084054106800080050456220001c80d014a020054110107523599039003420001440d404030124070815a203004516500400501042030011084000080d103110004000300e41b4070a0144c03452001d8401d004050039501842025034100f2a5006982d851041954076420106103412804004507440302440160368450406030340001c08144114082141290022561884d5803081e5810341c20301e002c0142c0c46600196424260400782c80320343c074a00d054004c100c1074400034002c210000b005180040c1001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 554065584 1250 554064334 554064337
    0x240318020f0a0302041a1c1208040614070e0f0108060114091210021b0d0503040303020d0b10020106050a09090f0f020636030d080601110c120a0209010518040305 71
    0x254014040150150b0f03030340c046420341c0d001082c0f10329960070f0b0b0b149036091400c1143d220703030454030f6410a5800410706076036005a801d41d070031030740300820000100007000c001c000c0d8401700c41c1d0751814440590915005100034035000008074114040c040302d42c3c0d82443c55020f080c1450040384161100c03010741c034040052140c00c1e000b0054a46e0700c0701d07a040054224210a01c80501951b0342034001594801205041c040c1360b01038403a03141115440040740e145001c0d031100680f50400c3d8117103400743c0d40b1006140e142d405001d804c60700c10343c0260480f401880d000d405501c11401c845081c0c5600d00d542d5a82c0c5100c01c1100e244c03c0c005000301c485074051000103101c03d0806070000744000e190300c0c184590003481c2c49512011541c500c0c88495207560842e40c0c0341c1c103007222000080d412002402c456400703240041c0315450107004907050182c84203060a0490060141d2921990b002c0d04241900340e0810200c0e9a5540740b81d01a8000c0b65050000714a03030801070354110130b0308196070341c544035511513541c100c50a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 554066834 1250 554065584 554065609
    0xb03060c0d020d0203010e040b09030309060c07060e1501090f0b031e03130e07020c0609010f0e06160507050f06090924060307030237141324031802 65
    0x18642c200803640710841c0d10f101460203001e5150200e90b00c0c3c40c0518100001700c2000c0c099401542c000e1003006040400080c4003503100b03410b540e40c3c0340c41e82a02d02e00031014114928520b091801900323a000303101100740400034102d506901c4c00380540d07490480900c2c1200c81901540e0b0b013580040417840ca5070a00303200301503481c450320f104a9282505040180c4844203240d002064400580030901c00d2455041040288440040315840c1c0b610000c0c074000303010348800c03441041c144181c0ca50301d0050380c0e07210415954801004500c0410b0780c3c50a20703050380c4540300341c0510b1340f050502a440c4000f505116003610601e041c0946103100700d444030100c088050000e81043d80586503403c020520540310000518061041501c0c0561200700602e03141080905220300c10244402c410b21001c2641d1485198050110041c101000034002e104955003507441010680c200000034580001011390400320010280050319420f21008424401d0844c2a900c60315015a100c4041510130805450450031000302e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 554068084 1250 554066834 554066857
    0x103020c0c060304051b060f030412090b0307030207020306090601290712030f050a1506030207051015080f1212061c0303020307090503012901091208040303030f0b03060c 75
    0x21030075203400005007164000c40302120250010060715030100000d400016001c0d0b400c44600c0d042c0b95513110018814040100082d080c02980b464454000c1d001e410454013402c0e040f0240e41d0b807490841c0010703010b503114003412030280c07207101c0000322800750104005040c1c41d40f01045441c50740c2804204001c1c91103026a201441104200640c0000c5011008450a00311070b100840c6180c825008003044402c014038060305c4070b050010f4035155000b0052010191031186c140140c0b1000700d41069442e183d482551741100618245241035001003001901d07088a003001c04035041ca290940c10744d502e400700101444084c0809102c0c002243e17103030139541076101101400700200803002c0460207a030388507140c0081d000f007a40081071103001603210750042f014040550092000e81080d120300f40c13140180189079500410070980c0088140c1c4101500c400600e420554281c8103900d0b410105c0c1d0301c0c0c5c803620084022070710305000201c00d000540524001a44014054410365a0703030746510340c41d98448400c411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 554069334 1250 554068084 554068093
    0xa03062910080702150a050f0c0304030e151c0608120a170606120411010206060303040807030f0303110a0201050619212901080d02070b040b071109010b07060b0406080c0103020c 78
    0x78141c48040d03170418801d01c3c03c0c4038040342500700700781c002d85129006441d11070310300340c200308110220740c10241405400109507460200e20820f031140710114000c0c010240707030203004c0690781080f0480a0300310344142c92100096540d01000460301c00014811442c06a0215401040754a0b035045004040c0b40d0104000e466585000f4146104102d0100c2c00c6078115440001c2060b40c45003540c1c108042540003805900a42ca86802c0a043d19a105101d2000404480400c454001058440e401400c449036400c2020b9484a843c6000a4060041100d40074025100d29601c0c00c01e2000c9101020111000c0d807160b010503000d1861100784000142c1010f954494440c1d12076549180c1d075004400c151032620401c00100d505141c002410a0003c0300400e0455009000620642050307104480445000c001032594072102c81c80c2c40c21100e910280e40c0c640c405142000080c0c001c106070010001c0758404c002c20445d4900c0b100c10041103480f640074143c92030780310b104811041d501a07401131032024200170444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 554070584 1250 554069334 554069353
    0x3170402010905101806050306012007050a030b0405010f020f070f0201020a08030a0606081303021c020f011e05091204091d010c0e01020708070b25020a03062910080702 74
    0x503800400d00340c14138000580d05441c21403045a00880b82c800350032217242c81461400d045000070600101c12076205544030f4003800d480848501044104024040901035050496407401c10400100c1c080750195042c0d401c000c4503c40001c654401c440c880110b20f400141010482d0710340c01941048103070301302e040d40315025104002c00c9100015522440c0c020b00041802c1d410008020041d180c060000d00d1030b0b04c02a100440020f4011a50003410395400030304407408d030f454000c101c0c07410002c855000060f528240700c030303c0d154000b40e21640c06281000c4051003103886654840b607540c0b40345440720783c0d503090030b1000384150000380c3c0045000b802d084c01d000c0d4164000210072421039423111070001c0468550140305400d940c051125500603c050b0000d411024648400900d2a101c0c88110045c50328120700c00303903001c14246403041d0400da0051b02000b046600c03841e0640090940d5054820212294260391001c01030715003003007001e441e029090300c1c84c001d40b541c0305507604100078010000307502482100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 554071834 1250 554070584 554070589
    0x80f0a0311030d110306100804200d08030405060a05090a020906040506121c0809190b060a0b0315150f0f0705010b1002060a0c140702013b0f0a0303170402010905 71
    0x111308410500840d810f41d02d040210400c041d04000c4101c039024421b88100b0003004c98840300c856018060184880c0030f1540c0c280c4000340c43c03516099401070000e00701009100c24040c0000c0c0c400e1088a054504009603211008083d503210b00d501002540300300d203040060814206a04100e030081070150a01511000b030201040c1408402038030340d0030400c4450795104e42282d2002801d600400c814018004a081c80e4020f02d8040346500c0001e000e04005002182e500c2d101c07212854024001c04052136100d0a00c03081340c26100920b4a0030070301c249151a20748010007200001c0720788000f01410806d02e010400f040078400e5400141c1c003960107542e5a10b81e06003a844983c0140e18007102503001c0c19443c039101c2ca00c0b00c212280d0001c07040412503074210312610b4141b010101c034482502401c1c01a030300009419070084441041149000340715511224190402c10319804a440401c100d40d0b00b04034240d1001807000e14070551002400141c1784040f0684d0100c0903105194103d80180b602001540d02e6802 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 554073084 1250 554071834 554071841
    0xf020906040b120109050c04060e06070803010305010902010f05030930070c09060806130318210302010e03120117010908160501050f0c091c0c1d01080f0a0311030d 72
    0xc0020400400500c103c541c4000c151428098140190100075a00b010101c001c150701440c0600014401541240000c5664440030b44400c1c2d540450800c2c0c0d41d40e140c1c81e00074007038546110100d003c00ca04d58012840e40e400743c42541d12840714000100f0081440140d801c40308211030295942c84090b8074100050218800d000b07140f801d00441411a40514010171841100c200b9406005543c2101040c0802000c0d0503403031184813501454141d8441018141404030f10095034002c00241c41e11b40100e4103003600c07004110341d9940c000e40003000004034a00340c454803407003100e0241003c884030078018481c501e4503080c210b0742005100300000cada1080c20395602c4610f0740114000c60340444c480c0411307802c0190034040c290380417582400c8210300b400c0884183d08240541300c0d80610501805151170282004905400b41d92070b004450300d0034143d0b40780c071840300040080002d54001e4500c20000302e5015400215042e99140303040c020b00b4400b40c90f8404a5080c000d00421301d016010804c0071812f45101c601 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 554074334 1250 554073084 554073089
    0xb060d030c050d0e0907030b06120601050c01060e0105030c060712051e120103150e060402061e1804060807060c03140c010f0e0c010207062f0f0a11010816030f02090604 74
    0x80f07030303c1300e00c1141e0402c02c0071100d80100490100750400046184d90f444100590b0010700c00c1d20b94054894a41c3c80068603503005240c00324046602e4108006660865000813074101e41c010340c140ea001d0500f18041c02114801d0090280c0812002c060034001c0e1072140c80100f01801d0910881100710441030b0f80900035502c807401c3d20500c1001c0c24014400c0c0400c8228107941016505010402070315141a90b80e1a0480148007078496800410300100d8420070200180345a2004903015540d540300e8110390303200c0f02003040c5d0503000b5860460041850f082c0040d10b4802d50303d098541c8244052581c1e0708440d003e030141c070843c00300c64007440140681c8400b400b5030504054400e5000c2484d20a00318046e14001140c1c1800341194000001000700b6600000f0010882500860340c1c802002620412900000429010b02c414458a044691003180200d50220300c03501c20b03408000c4040721071004580f1294180d818080c03240303d1202c00c00c0c005001c0d6100010581115102500f002c0291000803083e402c0766 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 554075584 1250 554074334 554074337
    0xf060a0c05070f030218091009080d0903050d11040503070b03091e0c03010c090609090e071203180603111803120412060f09170703020304050406091e090b060d030c050d 74
    0x800d424021450100381610407111b10a00d14821403803c22042d95440d01d40c0459100410396a4030018140240c0d0030855608030380e058002c4c06101c0e03c0c0d140040c101d0348680b0070212150b10301a1160505201001214100e440050081007081e09105102c2c02d20390015200d08001d11440e5064801d8002a480c1c030a0b640c820b81003e00801f001002c241800d556000500000300000f921091100c2a04400580f065130544000050403201b6880e210b4980183d43d00400030b491074400704542015403103041c0100c40d800c0c0703074900503005030784640076030036141034050035401030390280701c0400448019a0300840305000241141c05080d140d90600a50340d000382c10000c607401c42c83e5070307240502105001d050b00c2c2e012010406c21118107183c8030306040c60600100780c078007010001500000d15100b003043e6005060014020800e00e0b680f00b802100400d841005540e00e000303480390602d104000740c82a224480c0c1c03c0a05440c0d180d8500d01044554080c1e003c0807400c3c0b040141218020540810824810b079219 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 554076834 1250 554075584 554075609
    0x20a0531060603050f060306070c060e10020a17090d03091a0a0b040617060a051905070906090603091110030f0905030c0f161503090213060e150f060a0c0507 69
    0x1e0003001004c1e104020030050b02060100140491500d000440d1640003140d1b1030f2001d0b21030964900003000d040c0b41007150035180b05030321900c2c03580350103680140081903a6889040c0c070b601a652000000d984100c03070002c010b401100051300d40c0d60183d004560003600c620200040d4000c009103602c0491410b650880c0682d0343c8040d481c031203040a1003040058607807100c502035140580a10b455403118010300e000c040c01d4840003c54a0084048041002c25420007003d00c10307881d00001c0117004504034030038a0b00180e810400060031600910840400c50781251007481071140c11401c0c004803858020121081541c4d40c40c500410710080e04c500650b0398480e030007650340c0c6c80000e0a40d0303260004405c01c20080c0d0304512420a805807540c1140c034100c81000407902c4030042d1100050f80242100c1601031340080321001c0d24bc0140103968030280030307540c2281c081810390300c2d03484144070082c40600389250452402c214071600da240400150004800f9460081c116a280da84c0e81820308200b5841558039200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 554078084 1250 554076834 554076839
    0x10f21031403040f0b0f0a06080109050307080a110d21050f04120e0a06052128090816120e212107061b050403020d02031e07081009020a053106 63
    0x123806a0001095400024407040b011a02c41319100e2081d0b000c0100002800520200380602500d1031003036240d5480b080e43d048001c0f2103005004001401750a940c01c5442d051038525158030743c800e00e8000d1401402d10300c1141e90705d668007100040203c20590502c807903121010310306c0e51201c040c1c4000d810685c2d40c845e00c0340e19810549041500000d070007445500204204501c01c424001c0c0f21000055520100c0780048010021030000d01d00c3e00000360860700f001030700707034603c3e50b0b00055903290a1107406a100c01812404040744c40404601c900741e17002d00c4800711880044411601da5010045410a40c1c24078010300d4240303d81d0308601404640f50400106e038100c03d0150300d2003044203400b0022844c856001d80300038000c06600c200d000080c0b14480c10b0244070b0a54038208003c048030607001e645480c2c4000064165991a141e1780700740c10491180360025180c070650b034000c041c3e01c3c55018003c41a02e0782400104001c1031140740e40b5040d4108103404501c6001e10f00f000a000020444000281036030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 554079334 1250 554078084 554078101
    0xd091e1407120305030a09082a0d020706200a0f021e06090405130605090714030c130c0c05070b04180b090601030b0d0209010f21031403040f0b0f 64
    0x15205128400c507085070604011021652112464a80c0e051078415170725552030500000503c400c000203411000c011460781d10204034a80000d600300e6540e104000c460600344543c036a550000842100181c01c049001c0085034041c010342500001c1d407015031022a4000e1020514111026100352401c1000020324401e50610581041144a1a61101504c202401b020580c0c900c83e0400860040d40e441c400100d0000f004160001402d50014040c0701300c1c103020101d1595041c5600030f415041c4c90180c00d0301d19501d0006400405200c0242071903842c42e207280445402040c0e104280c606226038492940000741c010b01145018140c0051015180c6080c0300d00b81d031503101882d84150003d8948440f2034900daa0381d4050350391125003460045004101c400c003281840030306d0000250080b130201c001294014860001c50250b80b00394039203028031030102c0340040ea06071040e000174001c2490204040801d11040004682c032034010407001d4104507807030b910910a04800c40c0c001018500800a000d002d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 554080584 1250 554079334 554079353
    0x6030f1d03040e01080304080304031205160f0b0606041208131701020c0705100c14032a102915070809030f030415030203180102030103051b060304030903080d091e 72
    0x4200e40c5c0019801c5c14200000c2da0b03501c0c0700310301010f05114018218200624400c80840d65035028080d01070103c0c4200d407802400c11461600101d414402c603000042c080d0401c04c0a807130484001c4a900380300c00e8003a071a11143da600514000d01070b003c5428001c81d60803484003034503510f02009000143c4c0e400ba020741c6581003032442d401c814422000e152182010300e60200703443c0c24040e04014041c0b02c03591a99882d82c910f12410489405c3d00059100250325000c0404074148200340c1c9a0a9a0f02c01c10403d110508070b8960f40680f1030000301d00381100c880e4040c8032140000740d0a010f094500512032480b22039141740c2183d00201d80000b80041c4140003030800703010400d0181c0f544401941081d05103c002520f02c10307542d28140805078080002600d14480c3c010900d1000c1100000315a0b958484c2482c0d610381c0c0d0580c03510952401c03521a0700b44242041012a0f100c1c90b00750340c0b0107a001f030841c1d44184441c0e03c000025410a03132104840300c049a1032205241c0405a2410320603180a214500b09195 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 554081834 1250 554080584 554080589
    0x180606010806060702090a06050307060207050301060e04030801150210021c0b180109110d1b090609031509060e0d020c0f011106060123030c040306141006030f1d03040e01 75
    0x40181c0c940501c88261964020380e10490790480e503403081c90f600c002a0f58001d04441d0700881e810701c1480d200064040d000701e40c02e01581c209038024030a0076110480c00041100030b030380c004c000a60380001080170705030ba02c41245601400744103031050f0403104100c80e4141d81004091a0622860b00c00000fa071400c984106841201c065400441085581450301e01c0041c051080460a81d250010300e03008400308000c8a0899542d01d004100310964407207001543c0356010340c1000480c19003800401e40034025441c49088951299400c03007040c0d4009180c03409003010320011520662103005450007440c052000210701100e9030b008041c603100150802c840e5421a800260510040c0c0800c49082c0a0100d900b42c1d12100030700f06801c28640110b01e212001c1c0324404203507500b00d000710a1102000e0040d00800440c0d000d8801844529022a41d4000c03200701940c000c0711007070f8000c0d030400c00540a0b410204c22130640c0c1c100003480030b042c81c98502d4480c015101d0038001e504001414007040c000c50420034003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 554083084 1250 554081834 554081837
    0xf0f1621081501030f0e030c010903030501050d0f03050a09240801061d0904110312181f0309061509090b09070302030604030e0d060e010e1005070504060e030c0918060601 75
    0x942441802d1007400450484614109a1200c00c000d40e40794498110900303800c00303c0d040726030f140743c0101000c3c02045107050031400203003868000100c0e86040c191a03205943c009211000f02c01083e58195056400510b0110500004802c0090100c040991a510645803000340e00315068800d0380041521034140c0040c070a01c03160000448c9644100082c40701428030540d80039082d078a0f036003440c0302c01c40029004c5507498070a0f02c14400f003108094000e400e010482c1c140f602d28180001c0200031b2440345c3d034208030b07900d442c039035040c1d0307101d144642c2107014440c5c0205400191028840c0003541d010a250300f244034090b40702c120340b400700400c1820096004090f0303006016003606590029484160140c8080c082010b440d540740c1042e607800381076841143d40520b042100143e0503039035a01030103440c03010502034010300141c040c2a41d81da0040f14802c03440c641c1c1e464905428420107940240b038038a840c0e0f40621651b40d0305041c81c0c42c0e008005000b00c0d11510220742c0140004031085c5850802400c050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 554084334 1250 554083084 554083097
    0xf120305011202130b0910141c11040605060a020c0117010312050d020c1e06070809100c0e060a090509090a02010f03020d0e010501030b0901060f0b0f0f1621 69
    0x41003a281c0b8070702c2019941200c2503403560404e1001e0720090010b514200340e01c01e801d07406000050031b616103000c0480e2040031081a8035014401000715003080480445d002208984c2145c2c0040c04415808071055001000000e00e40c0c0c440020483e10b0304520200000741c1e2190103c0c400c3c079a00880040300101c01c0c81c01c0c282c2190b041d0385d10b420681c2d480c480e0000a100000c20a401c544410340c058606010080003200d0080a40c40d10a4a01c07001042070461240210030100c1c40161099428512907a10b41004091a203154442500104040c0c0b05140420071400340d54500390352000010000070303400d96031b000f0302c441c1850200652400701404d041c00e541d000c50458401030346c20000c114000c4440c0e05005880300c2c051200000681816000c1d08010f502e440c0001c804c009003581400e010b405003800070000c942d2500030749035a801a0780120184101c05000801c00b0b481e40900600c40c060380364141d181061900b5001c400d04144e14501211805684120980c85c00f4045046020f100624035112 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 554085584 1250 554084334 554084339
    0xc0f060606040501080402030a0b040507140d2012151b12070c0f060c020d0816090509041407060c02040b041b0c060e03070b061021050702010b09040f12030501 70
    0x1e038140708038410507052180300c0000038103540e000e0081c0705550350066071038290740c50b007894030fa510780c07109000740c4116001503030303540c1c4007070415812010b5000d5201c46541880501400a0000510207090f216070102e030300c0ca581c1072200d109103c03030710190550a6041d802c50800c0f901d0020018203480c5140c1c0c2d454014410855607070341e000c41032a00510141014029520b003814031001a01d00c4800c05841642415842c070101603000550007070b030400c00d58075109640c0301d030001121001507c0403020001140d00314140554640110400e030854800e40b1070052401400d41c2440c10311120740d01c0f580118154811400c1541498001c1011f910700403602000040302050129941c2c010b980d01c114100260711440004100450348a01d9507180e0550449440760301d1840c1003130b1204002c0300c0e000c2c01041c000e120060101e001f400020541d0008010341803220302500c26035401450001c02240466486031110714054850014080c06036002c0c1d8492504100903061445007950490b04010070186040c004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 554086834 1250 554085584 554085589
    0x1d010f0e0c04090c031506020c01020d0516380f10060807030b1311040303180f030f050705090f01091b080606070206040b18270a021605070306020c0f0606 68
    0xb141e09807000400006044203018038100d005025500010214408544000c100b0756000101041c05407402d80c00c0310588103820204851602030f00101807040350241040314001002010454a20781051003c5084a01045070054002020400c0028042110700a0190381c00703000c20802c0d40603c407403e4040850b1315042c0001e00402d0020180e10404da503501440040c0c1e034410b84580c44603800c0400038444906a0600090194003a11040303011405110000030140c03000c0c0f101700304488071200840c8040b03242d529038040094844108a425000c2e40c007000c00d0035070b9600c0e0105d01078001011a0091981840f01c400c3c101c40d00400f4a01074504400e40c50212954007001c0307a64010340075603440740c0b91750708c030320114820f4011504a12902900031034032810000072544400361110044443c3c0031145044080c541441d4560030704540c0000104000a0303540089800404001c60159100301c0e0f81207050711040e06000240c1c1003200d2098002404c0c59000f542000102d18064131f10005d090a420690700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 554088084 1250 554086834 554086837
    0x80a02010503071103130305030307030f090f0305070c0e090601140f030703110a0b03090c01020d0813020607020d0f031e301e1e2c01061d010f0e0c 65
    0x2404018200c1384400440b41d0500c256000480c1c8591220682e585030726080d612a04110307100e0000074a0704a03418404002c0780030341c80d034042d00203039409101003150b00c1c1152140d02142080d200da000711003000516507140c60180d0f1043c61444040c08155051040145040c50b00c554841e1095044071001c0c2c209a03800704200d41102d134410176102c083d03a401d03000f003203c0c0c22659120248100c408001c0000303100021610101644090b82070f20100c0c4520502a120500309503a002d8500b44012038800050805d0002441d0950000309003400700c0d440c07070740e5114442c8801401100082c10120407005c44801040110b98202d5a030b08290221509604845a150911034641113043c421840e20403c24101a0700450030003c98600700f105200001540300042e10412103850340b000c5190f098200c4e609d0781441011000c07005050f2340005098040f04020007903c88000304006556902d50003d001100306519682c881c00c000d00f182c156614000440750021f10329403022207002c0c6910100f02d00880e4000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 554089334 1250 554088084 554088091
    0x10501090212070807030e0d020c1023031003080403031d04050903070b0a060305010615020d0207050f010c0302100c170c120c031f061d030c030c040207030e1f0801080a02010503 78
    0xe032013100d5503100c0e00c0c2103001c0c240545200c0c0d541d001c2e08480703100060703011035104681d030000c0e90f41c0440e0210103002150401c2d44403a010282c3c1c8441c050b02001084030030300646c0c00076a01800c096295460351203038803850344580e00480c04105100204500200000d07407665100c00121400c00040c50400701480c1c492181c800d004000c1540c4d0b00004610001d6980000d010b95009002003002d41e0301c03000a400440725085860b005449070301003101d2141d03c0001c115040d0341d0f0241c8180c503224a4030f001510b0300100c0e11012001d40c040c3c072801700c610700e02c20f2041280500a5555007592440040001000094098040d4801001c100500c880321800049800e800c0380b00d42a038980c0d603548a800c111464801e02c0085a10074003011000200c8a0b030283d00c0c00034120703007034481c941e03d11490400c041c2d88840f040d0404d1f0700741c0c003c3c4a49480d07070700d0140e020b05540f501130305019083c00b03804400170710403580711040803200505004164800c0c40d401500a40505020030082251030903a0300040e10034040107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 554090584 1250 554089334 554089337
    0xe030c0402070c0902040f051e10050325120e0f0a11060d0e061509070e01031d1e010507050708040e150306040b0615040303080c130f030602070501050109021207 71
    0x5400070402181982003c001c2c0320b40401107442d16160301814100020078401c2d10301c90200c2c0b20414542c0d440d9400350115650380102868039002919006640a8000410f4040c04044815000072030302c1c0d054620307900d01031555031260b82064040340c208003100c11407080c0802651110881a062980009054003207540000303400e10300b07020341e00015041d40300384000794840c2c03414003461240114002860303e0088003040c6022034540da40000b84040041b080394510006680d00340552400d50280c0d11001d00d07000300e4182d0030450640000d84514041c0d03402d0001902400c0d840403040807034000c0c4030700e9030001101d1500c00c0c5400c02c180c0740e5840300d0046008414080c0c3ea0800481c010010170303090507030780740b0000d0300340c505038640f908110020b144101c5005003c0c500510400c6603030103040c0211025664103442d052001c0d00d80500d0404260084001507070b10380000000803c03580d03088504a00198412000565510799500c0d00e10b0945006038003000a2a006001c140c01c4107400d039084c6a03200c1c074036 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 554091834 1250 554090584 554090587
    0xa05030117010e0a03022d030a0e0402040824070e010c0314130e0411010503010503031b25060201060905010510080703060e090106030b0c091f0915080a0c0e030c0402 73
    0x1d03030441600401a242d0100380720700c02d0042110405801040707949030441d04d00001c2e40c000c2180180000360340c1486200c449a038008020251000340510712102c60144040c000505164072100d14924090781d40903075100301321220750380c0391b804250007501c3e075441030727051400c03034440084540082c2c035203a90018004c05020007900700c0c022a19000c42602c680c94014002c5a40c00c0e56100007030840b94200780c82c00d0b42e0740201c3d980f61443c3c0794021400c9904030f603070142c0110320700b000c0b0744441106100b80980041c0e0304c0c00742034811402020400480070201c40c50341c160901132440c080c0c0c00b9086a18076848080c41a0415004000a40e240c2e503848090b40410309000381c039690b844404900400c05900f040c4d01c0150f0003003e00c5206981540300d103050343e2180f40e00040c01c0d01c3d8803034507035582c0c0102d40150741d1201e20280441d41c2d50b0b440721b00240d80c0f400c240c100000701913140c1e01c6460040d040060410700241203801040030508060186040300307091401e000b40142c482e000429100d41c2108000340c090340c2c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 554093084 1250 554091834 554091869
    0x105091b01140d020a031b0c170f0f0a020c12070f06030e011b02030d0b0114091c080c01150e06030a08030603070b0f0d0c2a020409061404021201020a050301 69
    0x320b42c0b0454440c004000d504550303d82007198080c00070240c0514039109500c48914030b0b030896001d0f129140c46180c0000545210080395414001d8507400480b000d00c480710103001449000c520340000d080d42480d10b4010b091002003540a1216281c40c10554100c9548000e03010000c2515125100c0c007030790940e1501041d44070503900d0701405001c024081c0e59051080014141500d0f030b0200180110010200052080d15070403c01102e118010b2611807046e82030030080345410307281400880e00c071228901200c4400c60319a40b00c01a2a801000030303810140d4484402c0020003132142d100c4006404100c2c5180c0b101d0030300001007070782c48043c41e43c0148480b40000204026580c00c002c2c0b000180003100301035036134070300c91201c6a0f10b40d08484680c5426a0601051420b458065081e40300b060901050399214801d100c035114080103400901070f40c002d681c0710b8000002c01c3c0140519900383c0c0075112074039210309141c4140b00e0300220512030030f40c0300e0b44107100c0c203c00213134070004407811103104110b035040584 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 554094334 1250 554093084 554093117
    0x41b03051e0c0a05121e010602210a0207050a0609030606050a0602190606211a09100203040204021c0209120105070905040504020a091d0f0106032a050907110105091b01 74
    0x300e003003c40c0108406100c00c21503000808680c040c07400d0000002c03005681d0b23031503000340e80d6451510a0f02400c013029041a41003524183c01030b1008944034812100c21540e1034003c0380f6940080d81080b00040e8203590284203001c61402000d0003480c041d9040300c0203600d003150080d00c82c0580c00b110000f0078038581c00c02d024480143c10200c041c05440042401000c0940109001d03010790013000c482d00c030b104201d25065900da00040d03a00c112020b01c080c00703401c205e0130f11450013544014003c980c800d50a000b081c1d16020300c404445c19603142540c0060f501d04903c01000f04602a0708440e2802e40c0c1010200030403240c1c4000b1030021180141d0b404580e81c0c07110700c000392109040760442031249103040b070a003502c812004401c2a2040152041d10480740380d0203616400d0328039501001e0003402100704c030000d5240410309030b00841e00c20071181c903a80a0301c580c002150303544150340c2140050442010781481038800c0c070071a0340101c0c4100003004113542d000141c610885040111605000d9010143c40608 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 554095584 1250 554094334 554094337
    0x309050402130b042d0e0c03040c0b03013201120e01090f06050105181b09010e040c03020a020c060306130b030a060c080411121e010902041b03051e0c0a05 68
    0x201940fa0b0016160f940700e140301074250a803541100c000c400901c02038800e958003031080d10140c4207550403020555540300d181045a41c000391085070381101c12080000e08440241c042c4d400781c20302e42c40c0310401403080a14490300c0c1d1403010a488482380034000807940ca82c0c02c10802000030b201000c0200b80d0006142103e401000d10312001382010190100241c104415130703009905842c8101c64208100100899525060304102c45000d030859203091010358800700c00300684012641403525001c080c2d41d8502003425281040b100c100030076008078824008503014003001c03441040c20b65990341589420070008074040c041c4600d03900e00f0f617034038040c1d0980c80e00d051010409640d0020418080910401d500400a03607040328141d4a00c0d0f20b408501c0c410345444250031089401400c000c6c5901c1c5540400e222041d4548080900c00e590798030940030058032940101001c000c1c031021614946503c8080c050282c410042488000b407030302070b0407001d940f18040102600320702107450060f03c520005106035420b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 554096834 1250 554095584 554095589
    0x3021908010609090203160305100f1b0210050106030207030c060c0203040b03010e0f0f040503030402040b0a150203090307120f060906060315050a0e0304140d02150f03040c0501020604030905040213 87
    0xc1d42069030200d003002081d0028000180300741c049481ca00c00390b80b00801d00020394040204580c11450f0070760140d080c19042a850401d5030720700010f0341443d1206070110030b405901d08201503004246010340c020118400d4a0050150b03040541c070304402030760300420381c0c2c510b030000401c6103a0303803100c581505100308181c074040d15281850341d135256140c981d043c10044085680681c2c2a01c0480000c1030382e0304224074580915444030055095171107550800020701409004030342c00c0301905500140d8050401100c40103441c5a401441ea107400c604281400c00310b0b65040802c01502031070004000510ba0444808900d410010001e0003940c0707490840050079041c0c2c000317880441c582c41000102403c035448580200e00582c000c11001c04021764054482c05103101d820040000e2040d40242410a0041c0201d0248000d2104608a11445401e0080e4100300c00141403c030001c400c100030011414414000342809000800c1c1c14580340d600100181a540110b40c00f843d00807510380781001206094501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 554098084 1250 554096834 554096849
    0x504051317160804080c03010b130e0c031c020f030f0403080f071a06041a03070b0f28110307230a061a130212060415170705120313030219 61
    0x2c01c1d81490410401542050040c50203a000d240c101c0071080c41c0500c9025034405000e49500605400c0e0712454000309030b5a1000ca5060154140d008079564050109114080e1880f00003c0540d03da040001d02d03004800045030000e034010461019010b0f40c2c013083c1d6044036802250260307030701801d5030010128062040010700b540c50348000384161011018103684244801e07541000303109900d0202082c0d00da581704020b0b0301500884000d001d103070120380c000c1200c1d02907404418035000c0c01c0480b0040708014942048040019200380000c0b85502581442002d02090019400c02c01c40352203040c0450f81d5034114041840020001c101502c200340300b6150850740000c020049034182e0703001803c05680648074288640d80d40c1c0074100c4440707c94420313140fa4513000308044200359540001e020040111103c886140c11109000081908800c84c419407024020030180090328039010900001c1d2510f0209030030350f90428003030201249600781d0b0417002c0703c1d012903501c101ca118800b08683c0da080c054003c41c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 554099334 1250 554098084 554098117
    0x601090e0703050f06060315090a0222030203070e1005191d0f0106050c060f040f1e060b040212150a0906080616110613080f030711070504051317 64
    0x101e802c1d0140e0146224401e05080030180d03a403200d0810455210440d80d005a4404076901c9141500b00b1600d400d5005005500040c40d00309102c0900e0f8400401000405c40d81042d1407041c01141001d01c001c200034070120304000d80506000c0c0f150700050209000311801042c20506046003a140b811079480202401031000a004100b0042015004800c80310510301d000d0f840b00000e00148a1000c0f142160700c1c0030082c10032a02e90544c0ca59007070b80090001d803016174102040c00c020071000501110003000340c1c0054500d010203450103000b598100701180744694810310100e65001d510108503540020506981c4000a8495001805c90305064010080c0d4600c2d204022540e00030000f0702a014164085c101240340610040031280c8203503a12203120b081d000500491942d000c50344041d8040c5102d00603503401c003c00c0509004490f0030445680c80001d50b5180c080713140c90414805074000d880c1c02e48040c407203880c00b00a5180300c0030b6422002007100c0c5402d60800400165841904c02d04054841c034070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 554100584 1250 554099334 554099341
    0x27080d0b2407170f0d0e031e120a022a010f0e150603010e1c0915080105120607081302120607020f1c09170c0306070909110f070b0601090e 61
    0x68205401030102224030b04004100c014051240b0b009503031050303c02c4482d017464940f00c61aa100500320182c11020148418009140f071100c0e4a62400415004409041c1e01c604944032070f01e131a0a8050100082144100705240d01080c0400c003c0c0e4000e040c4002c800e0b03c09803024a01401003155611000e801d40c644034a0421601c00412048090449400789882c60f48456080500301c4895000e50700300d50b801803011641581b0802c0c2c0d0404034000c541441d401071a0b696080c400d50041504001000078401c0c40113000d180391000080c034149020b040244150711381444094048100039010710124903a145d07888046690b203803000942d01c0840703000e980d0642000580603541c2c021075091440b0b180186498004141002c8104020610580c1c0d1030030343c014507000c0751200801c1c02c1c408008084c00b0f000c003c1c0c1c0036a1420031025001d10525a1000c040c0c628203000f050807100144104080c6c003100b00003a00c002d0a148081e41e041c1500881c40c026262505001620411003a501c04c418125940080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 554101834 1250 554100584 554100649
    0x60f02030904090c1a130504110d0504060c0f1b03051305060408010e1c02060f0a02040815041e08040e22081206011e1d04020d27080d0b 60
    0x58130100c400300110459601c0c082414040180104518180000750707035542001a0725160700030f05d007aa078080014524142c4a801c83c0010780f84210340070b031089a1202a1104520351000c010a100012850f02200c2001007100500d40b002882c40098100306000c5041c0020624011202c801090000c02c0c0c103503142e07a54000301d4060005405080c1240c000c54024000803042d0380c0b0741703080210b29a405800159110040c2000101000c2d104c0410107900340004980e4400810142004c0c40071181e003071501e0300e4140b4040d8407400103c46601e903840e00b101129000508904151f80c240c401000400c00780b5030710121510605940506030202d0116a80013410a100b0404010a04003064083e0800c0315980c4c640196800d44080495035030b005120146030011500c2801903040d62022000343c445a0b03c1d902d00000c0030707600320001380c140c4180e0300d40804218400020b840540c5807a941c103018034115180e15908010f019204048540d50b441d03644403a090368445044a60740c070301040641c80d0401da51881c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 554103084 1250 554101834 554101853
    0xb0a1e0510050f0f0c010f0e01140130020d17032508010b030405100608070806102402010b0307180506030c031902030a02060a030507090b0f04060f0203090409 70
    0x810380180040c03041101d080348035804641c140c0b004002c0079498041818803a450aa1001c040710203d550f81c3c050b42410040700e4019000d844c9502000031600c40c81d0800306e01407c000c1a408414200f454070440f40c400f904000d03224600c80d800c4000301c001d031121800850355481c000382004201070041c0d01070101c448102c5001e140101800001048a54070503003a8002d80b809214513040424911801008414011001154000c2c071030030544400504480141c8265513240e00000c81e1070b0050300307052001d40d5041044550000781040d00d484464908042c200c0c0d10a000c1d4a003900686a85d01144001c9000b50014109200302904548541e0781d5124403102e1a120449969001810400411020f14000079005411400100a401c54144111280490000a01c8101d8042c0070780c45609000d83d484001404034940c1d43d8078013280e28503144900a0400070103401001c501030b400c1c89520b001700900070071340f02502c4460404907190004141301b40c0c51030186d80b1049034454141410303001000000c90 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 554104334 1250 554103084 554103089
    0x12050a0221100603020d0b0604021c020406171302060f04030b0109020912060403270518040c060f140f0408060a09030806102309060c0303010321020d030b0a1e 70
    0xc054400b000d0000088100756205484065072012400340c4e80c401083c3c20345805604050700074001480c0200d408a100c40b10314520b5900001c0e00d50100c0c00f0859580c0001c228a00c040f8410917135002840d00044103d181c0106807030203805a00c02107400b441011944040b40d001e0b542101b40c1c0201980e40c1d40f00c50010390b020803010381c0140704e50400c100d0682d20024940d80203551680721a81140f120440d09142d84c01e48032900400000f40000026460312805c4c4080340d241600c1e211410a4a0641400003c0d007589501ca5410459180142242590700840e0b100440502c0b1103140d5441d61240c1d0401401d02554014031940d008560a01a0160b0039900a440b401d100e03855120302d650703801003045042c001c1007400c2c1380480d40310701c0485641801d024141a600c2c8001140c241041841c0e03020071015042500d00700007542c0000014414000c42030101015140000d001c2c0c4001800020000e46428040c5040021300d6248c08420282d0745d10314040502414010b6560481419015003074400c819851 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 554105584 1250 554104334 554104399
    0x3160609091b11010f02070b04020a050f03030301140f0a0803070210021603080c010204080307030809060606030606160606031203021209010b0a05091504050c0a0f020d0912050a02 79
    0x40d80c000030001058054680754415100c200350350711000500a6030032a01c41c640394080d55596030281c1001c21103604c0980301080c0280c2074001b46c2d140610501c504d6108540040744105150300054005030350004c01c403815a00c401c483d9a901181d440003141005c0950900310394404100480480c2d80600000075004c0507001720348400c45500924400d03601c9841b1141c40401440040300180f011a2942c00203003070001040f400185400e07521198942150811301c001c0300001c00c000705100d158141008425000a801ca0b400d500e1400c00500050302445108800d0380385605110100c1c0601c41c450b8081c0005603040ba042d500340080a450080080d44480703000706010682030081207035000140b10f0140d61080250440300464140000c00000c280d004003d454411600780c2e180c24261180d020341e501070010000500d8a03805500009403154050080c44000c5601c4003180c84201a4071036a40c0c021138011044000b0802c8180c00d209042900c0d05030080d4000450784007203492001c090125080a1181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 554106834 1250 554105584 554105597
    0x30203041209060e0d1a0108070f0b04060c0b150a08030a09060305060d0f1407030f0c05010206250c0506130201031103070503281a09060d081e0702031606 68
    0x40290a0740ea144075800703010300040c1303d90802040c90900710050071030603004420005450030301302c00400000400340c02540312504402c008010a0500c81650409407282029442c10a0f060a80040c00e0a68865020b440501d030000414035107a85031030003c00750000038200c903400584402105070f0302e40c899441800040c0f580c5100003a01882441201c3c02000000c140c8100c0114544603080e80b00c0c2c99400c1602c1d20031007441c10100301c610410606c4021441910b1441d4904260305052a0101c107660140d8107642194041101d41008001c1c03000104019019540701c2d007140d00d0080302d5180c5a0240181944613010a11007240000c16004080c18800d0303030144030000e00809003148601041d40d204001c0b07107050000c00e40d1100c007101c807400ca00f482d051b0700000413405100000c0903204440041c124012150034440203a00300440c90a500c102c0544801071640d007196a0a1140c3c8541a10803060b4100100080c1e666060001110784003034004003240d0382c1007010005c407030b40d0307202c0d51281001007080c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 554108084 1250 554106834 554106863
    0x61b070f14030c0409030216060809061e18031e03182d150112050105070203090d0303020306063001051503040201031805010e010c0e0f030c010f1e03020304 69
    0x1003503103052940c5440500030b050391030042000d11010b854445406c83c00c0d4000c1c1203403030f071803106d210400c240201030300e5850504504241100c107041100c0a81140e80e0001c05c079000a140c041350490494011924010344040314070344540361400d500038901e038051101d000154480c4003960510156006805668480c021402c030b1302441c0c1c0e512000c01010034507070b4a06040c81d0140c0d105084034807180031800800c0da9130700380e00c08428029042e801d82000c074851b000d0813209414401c003449030703d9202245000462520f00780000103020740712250802010107030000001209500e50f0030944d0707001406c101d806110303c2003522030301480b01d00a00c40c5440d2124001d000084038501650f00f80079050000c02c2242c6161902d0b0011070180c440030140780d039620413002d01080064424402d80440745d08450001070980118500284403411602e4490312810503090310f240300b40d5000c100130b0311450003400c001c0d030303003000704402580d14581c800b0300c8040094504549000f401d0301a0001c62059118440011003240c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 554109334 1250 554108084 554108099
    0x15020d0f18020f010c05031903020c1504020a090908090d0804030201080c070b060d060914030c010b0a151b05070f06030c0c050601090e1203010f0f05091b030402061b070f 75
    0x326182019500034106585118154052017017a144035000303400303591410b40328845001030303180941c18800000345d0000d01e03014003c609205540d201c00d4a55121062030070a9000140c00124600a00802a40c1c4400050401c54040c04440a0500140c46218031006c80c0c00d241442d40c01c5840142d01084805001851041c1003008445441c0d40c80242842c00d5261002484a8541035940072507105a45040500100b125009403071588004500290380d01d80d401000a801d403440711105a01904500405105541c0400d902c5c1114800e1850040d60051014a183e081090140f03000740c52806814000b02303140c2d81c5065010207803246500d080c0701e1001904421521109000000751042d00802e0040c00b02500d590000c2c0e40984240007140c000d601298102ca40340d50007079114661089150104110040384401884000e14085412500b6481c00c85440720070408410000c49501c1e0b40000000d0031555201c0548020041e4440c100c81d10100a883d00b82d503440b103038010350300ca81040c01000074051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 554110584 1250 554109334 554109371
    0x501020f0607050d0213051e03011512060207021903120816051602011814030111070309031b15020c011e090501080a06080307080d0f060509060d15020d0f 68
    0x3440103643c0d4a03d00103100041c600213401080412200030809440080d180c0e03201003084054090a13030707524081c50720303e03002c143c2100e0a00741c0400850000d21420011031212a1107441c00640009000d40d5645241c80014420178421503800e5040c80d40d03807400b00610692040078407028006813030319581c94460305c0051040244004505001600400011001d40c41d1a407092441c54410f06102c8036006600d225100c42d4411070300407111588902002e266145000d0150010403841511514500201d40e00e0041c544602c900019003e1201806942103003000380000714020b1061000300c02c886100014000d4645142c10031541c0000c1580e0301400c100800552100d0030030080b13072551f00300c83d441d0a00541f810b100c01041c0b00c08642c2c0c1c038880090380d000c05100811225100d04403441d9241c080c01c0720182240c84130680a124180340030018003081e140d98012581241c01103850341401d01d1940f41c0000c1d02010a80d89090907400071500400d020307a1070f04917800560085c5030a0101c50b4900b100040350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 554111834 1250 554110584 554110591
    0x406060503071824020c1309020418020d02150f0d0e010e07061e0c08040906030c1703030604110d0905210c070e190504080307120c0207090b010201140906010501020f06 74
    0x3007140c0e0740d010031080300381284a00305070011350055410f10102403000a40d8031202a91443e0450b486145010840c40e03d482030400014004240009086a58011560080c001c22000b03008454200404500c00d10310700a890085200c0d07661155110b400005c5040603000c05d94020b22150300342070020403004400310341c2c00c060340c2042d6144a40c0460304001000003461514101003407101c0800e91070049041c0c540144041d00c906e060104100b45907291000844030543d0007a040011124022070070041c02208403900007500702c5010580411003d00c0ca01c0c0307481941b03c0c6005c410320700202001040404920030303c1801400c2c0d80740c02c681aa0100001c41807082d0307024106a50843c0d41d0510280302c2840070a604810181b4000d0128118425a80101d51096509840d0840003004004600e5440403981e100da0703503182c50038810301d101c00c0d101959072240d40c0150400c55482d4122160541d02c03d50029180038124a8201c0144c03d02c0840366403146001e00442d401030240303401904c061440007510030301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 554113084 1250 554111834 554111849
    0xe0a0e06012703140a0b060105070f0f110627010c0305070f03230d05070903050a0303050a0209030d110607180e04170415030b100f0806060904060605030718 69
    0x403003030711640d4080841c16880b04a05101050580880844d03803074580c00c02074440f1a4001c0c8043d000b641002c1c49600801000b050402504004c18000100c00641d016107955000718840046c907410310f0820302c1d2041c041060f82d002200403030f00c40c5450341e092070301c000e640d0265100420b0300d400600044880302e0b641c00d006800714408004603800610750b0940780094501074601034154400b100644903c0210b0400d44144629008c6500780401c1124072440b038020a250420040041c034541d00c55440c3c1c0040c14001d018983d6440000700c0440d4950125050b910b00142520040340b050349002d846101e54181903400381c41a04001150b00b80190418001c0342240100c913013010345407840880d182c0000030811605040c80c07004880604101c02c01400103044150481380d841012a000181112009800d491182d40c2c074103e50320030719400c1a50281740c1340017840d040c071507a514000880c40390700c5102245504240f600100066050f400b0340030b10300030703002030380c401c00e13040502c20034190909024000c001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 554114334 1250 554113084 554113097
    0x1021c1a1c1403070501110a02240403081b0a0306031109010b0304081e03010e0108060702012901030e03030a0c14030f0f0604090f0507171c03020a020f0105070e0a0e0601 75
    0x11840d84942d4000814810003101d250001980d41d00342541c4000c0400c1c10000e82c0801d003004d074290180411a00000c150358408481000c18884001001007d04068280304d0800085417902c0052452041d500055a884542c2d032190b102000380102a82e120940d01c01301400c058040c0342c504608454100c0d140c020340c480c00d540310303912161340c568000c514450b1380349011041c00c50804a89409036000b08400002000c2e550300d0424000c0c200400141001c086914014104101552151030036614058840c0403540c044100b10040c0d00414002c103242c02188001f000300301c280030040d0409038190801d039660200c16030b00b080c00d18100d400f06491810740840e041c00042c8042c40300880c1c4c80e0303208100520104440a81d610342c14440840ca100c1910280c0010406009201040c241c100307000c049500240305101801040e41d03118400400d0030020507400050203c2d029208100030040710450000820080c00c00401c0034100c0480034607024082c181a40300040c0c042caa42402510900f4187c4910 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 554115584 1250 554114334 554114389
    0x1b01080405071a040e0a0903030b010509010f1d061209010c0507150902010314331c060e1c02010b010503040b0a110c010c20010903120e01021c1a 64
    0x101010040d20443c40c2c006802403000041c41d01e000c006040c024034009200042602a40c00c0040035100000d1a1906000c0300300030080090768000b5202540303005ca46020049200c6611506203160540e15141d5440307440410609825035080c1140c81c00b400942000304031045c980082078a09019806001d041080c40c0c1d1182e103d034004036040700203c980305240000300ca02c140307040d60001890640d410b03685034100301040314082e0748681c600c1c103032180c4601c0a880200020000103145561240c400a01c1e2500002000704101060b080001c01101140030f5902c0110142c21801d060140070454000660808085460350b5004a00b100c0c0155040406040590340c0c103034415015106030447d68040b21800c012a8140c1003084c45040811811a9038000e81400d402d801d03a10381c107400603403668030359244c8042d84c00002c1c0c02403000c407041d010f403081c08680791800e0900381c1c0c024021014a01400b4042d03c0c030b500030000d810f51101c128880400e024405e107060240c00c4c008e0f11004000c611080d515042541c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 554116834 1250 554115584 554115599
    0x2406090e0c0309030f0c10150530070e220308010519031403071703090a0b0405100c17070905061b01020f0d06030218130b06040902030f1b0108040507 66
    0x3183e1020108003201c3c0b803c0d2503c0141040c5902440e400850b039040340d901b111090070742e8010014a6010604001412814003001542407030031591001d01000b0902c00c0c201c0c0303080c210501000700300c1060042e00c010a9444004a400c244100d0340400d040700d0504072444242074600305d14501c15016520012070303a0a05050081c4141e0382a071621404609000001c0042c22942ca50011940c051000e107807138028030315184580d0044c0d8095810b1812043c010403118400004100f42e0094002c1d00c0034816880301e082080c100055000010301c240e003040700b1540da00744c02c610038002d40c4406240840d1950b50b01b00084030344022034080c0c2c1d90311180c10400c00300321000c00c19020104070206000145450424218107003980e111054840702c007501c60340304100350724240980c2250052941201012840c0045042090243c10040100390b10741144c003094007600c0c0c82c1c0c0021222a400360841c1c211040c2500d01c0c90356210000c603442c00b0100c0d880e003802504e520440d946406903903c1070007041087d080181 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 554118084 1250 554116834 554116837
    0x206130b041709120705040608010e0307030e0a08010507020c1804050607051c02040e04021f0504060c0c0308030a15080a38040f03080a050103080304061d012406090e0c 74
    0x1002d02c1c048418808501c1980e50310140d2101418010020201c803443c250504c804e0795001e44c01b035032040e40340c494074603a10075001c81100c0c89030350706103040003084135030300d000a0006846070401c080c1c540c64001003007034035500047c2240d04a0310440e0180c0d0507070301c184038201c501c240845005101d5080384010440b824000d40c040c00a83c1c00071400d2103050305203510110203d8000d50301000d18914494140015400d0961011400390483c3c000d480c4400103109000d403061080e4072a040c1080442c3d004501813103527040b010790140d9400040180d490800b480948043c2c00d00f090403d0700d40003602c000090050001581e9a40664414485031403180c12242024403108091420110340820280005482e0741646d0b01c5482203210311440071140405080041c80c4108c01803040101c1e928010043c0080b2780d0107400c1d079600c60b0340310070041068070340090f1301901c003c02d0500380d149543c240202502ca40036409031a443e114050407205403080d03500e1070204d60050a511810fa60001c0440100e40c0c2d0b40c1c1c4240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 554119334 1250 554118084 554118113
    0xc0c1b01020c1003060e07050309030a0c061e1e02180121110c01060605030f131502040b040e060a03020609100306080a060218030703030e040b0d02130b010206130b04 73
    0x1500c0ea0b0700c2106002c030303038030071201c2d0741e0701001030340c2c462050252044d12110f80b900042e091600c54214684081615541c8c81860618418414825a21020804075802455001caa440540309242c0c0404440030050042010a0302c40400011051385071100588207540c04404041c001c800c450164400640c1c04d544a941d0b81040c40c0c2420008010440840c0158250352601d1000e0031360350101c400e140c500319840341d0000d50801804100307109481c0602032506411041d00e5060100c040041e01d0011002c00c06404604900350020034009100310b4503e0144c02140ea400840100c0755540d0010040041e99500000398442820700001c032250802c200404100061410001005034a0300085c4d45041c00000040354404d40002e4002c00d00d0601c01000d046040e81540107110040c00e45d40d003c0c000130300081c00d06008039990034450629544020140285603005007142005040a440d004045c0c22202e840c41d001d8840e190200740d0780300400c881011080d80144503201f994466984444072000c101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 554120584 1250 554119334 554119337
    0x901150c0210081905070e01050a021608060a0e0f1509030c030408010516020a0b36030a02011103070c0b07030b090a090501061406070b100b0c010e060c0c1b01 70
    0xc0da000d80060315441d615092035505030b1500c62181c540000141c5001d1043c041d5008490b003001d0502c64000e070080180030040c142420115251903501100320703e4040082603c4403808500790000600342c002048060042d69800824042000003441003a40c2d02644010302d01c2035481200070b1492000ea000016801c0350a050650b40707080c50020307546183d5001030300300010360b9649202340900006541c400d280318040a0020303000300c0d1010741f82c2c0c51140d0f00c010005450398800d840514407040c0b5520540141c0811302c04002840100e48503419038075003103440d40784e0266103044181103100c07000d8000c1c0c1e442a030b46aa50f41c01c9001490343d0326100010041d01f08000d05485401c2136085596402e80d461046035560f40004031907140d410b049080d01d406510803c08402c400b0720300005505c80004640e082c0303802071000b01442c0c80f9403968221000c020713480070440a40101d0340c6a6412811b42116056002c460210380d407589a01c541c0c90405d21442c4510340040d030000c070380707503070f00310140a10100c044205 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 554121834 1250 554120584 554120597
    0x6180c10021603082706090411040f0308190203120117100f0207050601061110090f020a081005070e0a031b030c320906120c04061503050a0b090115 65
    0x466402e15241190341d0811a1007482c0818021001c3d03440a0034034103c1000340807005594808280814028400d04c04a2800347d51646851105140010201c500801081c402d000e040d658074203203010290026200b0840c1e420109d07190308409480001a40c01d51001d021781d03808507910b4014510a01301c4c51120a4441c4c3c041c205441422116511804034001002140540c1d50b80e03240c0b44c20b43c1014016041042400b034941c50108000e840040d07110344100d000da81c0020391000354104043c0303c201307500000303501801070f51001ca14400041000002840000d4050160341c4031140f0540d06080025180f5802010744142040403504c1e0052400f0030400e00565100000c1d140d855103011000c041d000100503601c030700c1c4035420701804181032000064011080c4101c2d8030700c49000a45614015100754802d4240c010107200c048014024042d01000080c0100145591045c064111902c008e5052000c031380340c00d001448214aa014860070300c040280303825a540c4c200035032040c94940d807995480402c2103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 554123084 1250 554121834 554121853
    0xb06120a060f1a040c050d02090a080d020c03060a05070203030a09080d11130602010501050a0e1b0c0c0406080d020a1416030b06032e1a0d0303090506180c1002 70
    0x41c50311810b0080101c02c4000719104070f104000240f0512410001c0d801649410120307000030b035101e41a6244030080b010b015030307910000e900041d002d40704c07a081040c05029102c100e03200190001400056600140d05071802561401c640404854040f141800540c01c10400501150015446003481c4ca20504c07000f82048020030b515412203501c100400080480050004040241e42c01404028038240c4001d0040e90f05010108003d6015485105031445103c0042902d042c082c5141401029180f808152541032400010f569110740c00c508030f000c0d5290003c0410144c2c0b0200d1a1000031510360014144045541e45054503c0c0d401c01c0d00303c03924080c40c1d071800c0190402e80034034801980904520140c3d8207100c0201800c00b042c07040b01c1655003405840c201001588003e02c5c003000100807800040054130001d0801d030f05403000580302d6000c54090720481c2010342641c0020368041c00381044403002e40d00c0b202d83d4040c0ca4540481640554014200043c8600d030800c6100840d0340f491060390351403003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 554124334 1250 554123084 554123093
    0x70b060d1a04030806090a0e1c0e060f1309060803122205060a1103040f03080702030f162a1a0d020307021011090a09150305030f0406030b030a0b06120a 67
    0x152003c50004500405202891909555040c0c100d0030040e000c0140e4a00c0c002c401c0d235a5159004145007100c050613a08802c20702401c1741e203201450241020b039a40b00c4082e08c2203890f500441400c009103050110202d241501d0388203400a8442e0040110310342480740c601d050314000020001c1805460380762183c40c94510505400307419610800060000d17040425080d406e035203a6007070381540400b0600420022481202c5456012a0036003000421030702c0b1000304904501c90004002c02c20780d0000b408502c5083d81202c100d6880d03004140c400d007844440701c807020204a0400068481001810003880300106081e0042c0640303056462091034040c0c0c1d49990b009980040b2450400750704601c038001c0030180302d4000d2010344084c29046618264841001503907001150142428040c3c0e02e4507001c17602106085000060340c0c02904482e11185002e0708000b8640c0325000e0721000900740017a0000900300001c04c4584d040e41301c0303881d110642e5003505100c14283e84500300b2005125402040c400305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 554125584 1250 554124334 554124383
    0x903050d09020d02040e030d05012907030e09100503210913060e04080316090e010e060409050f0303070e15070201050f0d090f1a090c0f0303070c08100e03070b060d 72
    0x6c2c0ca865024503214024441c00400700c1d5416400901c018020401c102070040c014001d014003202011100d54513050f0038201241c20340c44501e402d41c0c000030f540c01401040b40081e4940f004803081142180c00441c41d80c100c602e0b0717901418402c0e0906080c03d01240d0418540010b0716008010311250016115aa601c0c03900c901c0314003a1400d50b1000d00000038000401031207076104112032021709040c6012481d01c1e00c880d08a002c1445140045020140801e15030398907600807000342a0841d00300c2c1d00e45403100901944952094845501007058aa0140101d042c8071001d81080d200706c000503418040c1a800540e04c56018076010741070032104012060410102c1e204041423103000320702261000c521460704109401c01c003900d900150389000200f140035200001c5062a02505844184110001c1c101007803650094100060059058803004240c100000854283c05c6001182c00d201c0002690189902ca01c25020058400303a0f00d00000344d564200315090030a5244280e4290510040380c0341d4000d000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 554126834 1250 554125584 554125601
    0x204020d020309061b090613080303070906030e0f150402030703021305100e06031b03100204030b09070f05011e090902120603060c031303110f0106120606090903050d09020d0204 78
    0x103403607001c014080e00782030400000b41d000050b0000c14241c3c002205c1402451700502c41c01c20b2040400017400b240c44482406034074001c050351b4048075200c1c2400034020740042501d02814001070318000083d911600000350038140d043d19440a401a00d100c5a42c0044094005009a825204203000040141c580c0803410f040c450002800241908005c040f042c882a20303135104804001501050011a030340204280d002200f5050310080c2e0349060101080c204080c10031505149480850000f050000070000c0501c00d4200c0019207a034951100042c001d588024000c81d40000c41041d035615942d240300c12607003050a102d0821030710a80d61601b14800f6079100d00126040b101d9004144040b03401d0030041c068000c011040d40604614040b00d9404164030030860140800000020503120a0404d1150740040310403a00240a615291051543c4403900714004640c0581f400d200020b844405205200d01c5a078136036030b09458481c03450070000242c40c00280c140e0780020f80d0407449005a0322449002d41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 554128084 1250 554126834 554126857
    0x4111b161509080106030b0c03091203070e01090b0c06190b03070609080c0906150f0903010e0a0302060702010903021908122a090a0b0c07080d020304091a0108041e020402 75
    0x110140d01030004142d101c055100307524aa0618006200081c4003140156000c151040c1c2c1c65225554850708500d0050000c07030005140c07100005000c0001d511140c40701180200f138071100ca02c0c030f5a4202041041c03182500c0c00119400000200700d10340005071141000280145010070001d12120000b418000c1c298010f50124219900402003001c00707004481d1000012034007a040c502e0540c02040c1050348011641078138010008840400300302600994030b441d20003a000300060341d15070704c0150355114000742c00e40142c41480c00103506907105009640354183d2543c0a8480c1001c2d010761a004e0309044402101c09280900141e0558812001c80d81d03c0380030f40d894983d81c8a221802c01c42048581d080d042c9101c19020044035100382c4403a808a001c5401c80e0a285075520f500021907810300718590031000b0302d401401d08030f500c403aa001000d0030a84d51481d10400144110703001c198441c00003a01d18601050f9480005800f00b801c580c84103000b405040ba581440c040583e001900701e074009004042e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 554129334 1250 554128084 554128109
    0x60518010e0f0912130e090a120e0613090b030105242205160807030207020105040b09150409060305010f0e1506150c070f050406120803220303050a0b04111b16 70
    0xc880200c032402c1b1600022031a01924603120113403600d09904102d0300e00c110920500d1481180350362180d204484050750031035100c030003203910b4132102070107416807d002e14403035820080401c00d50018030720944041640c085000f41958242c81c24040420090200d0080d0b40c1c1101c00c651a540007280125403242600b540081e030f08070801d150241c0030781c10107081c0904051042c820140140d03089002c035401d941c0c12104140c0c617114040001703040fa4601038400140500d0101c0c0005100107660414400e4900c140001c1c40461400c00389401218100d010844c915400741042c01e00500d240d05070306030004405010b0341100b80100341292203d03401499820505da11406c0700300041c0030a0204540600802c881c184082d07403910b404105c01c600030140c0a0030b01d880c0040412800005007003003141007107031841c1176055200c00d801c1c042c0c01040704482645049042a17402226440c052041813042c0401034001c50802291003c20740503c0b240780d008401c244100c182c0021101c0507001c1c0b02e0018280c2e42d2051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 554130584 1250 554129334 554129339
    0xc0809010c0513030b060a050d0302030309070905060a12140d11120a0f080c070b04060902180403140c0c190515190507030e090109060518010e0f091213 67
    0x960848540c40584010840180110740c1c02c24000810001200d4000c401e541c80ca8840200207519100d0b564803046d400a0141c0c0b40d901016004000380d0710034100e000a03241070540c1d030341e81d804c2074803021031386035030301c0042c0700e03010311452040c00b0454000901441302803502c2c40d03000f00b050b40350150250042c404034031400342c0c3c602911030800100000301c440385625800e040440501403c0c0020408200040c000818001a4210302c2c203020349290300d0300030148584505082c02c0501c0100720560090340a02200403c2840000008506500541e410303074a425580b518004641c0b0a501705041e010b5150080d050b503810b131640e50002510003034483c04012081b9520302410003a566030308014198203d5400d20a031800c01a519500c4071009000d428104d0752041545800c440c40410501e00701e901503000d90012410030300c2a8001e005860003582da020100940c1d14010508681c00d00c104840300c4003c0c0001026160f00007800e5070801d101c24200c03401041d104001401e1900103001c162260b01d1503d208 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 554131834 1250 554130584 554130601
    0x905030405030c0103020739030b0a050c09150d110403050d030c0903031b080c060910060501020a170d0608030a020a0309050405011223120d06050105090d060b01120c08 74
    0x2003e00d212001d0a04510380055651041641415000e04004200402d0f9101400d180b40851562000e08451540d0320a00d8603441e250161200c181c2d8a65070042c60040001c2da0344003220121403800000900f074000714104209041d0303065100149000c4060303240c070341c0003075500c200340c000d0005503201d0307005014804041c1c0001012207100071891740400c68045010004650810314078491082000e010301c07102e5085047c110404c3c45030851690306442900104000340c1c00c003207268090390802c0d450034880c0658800049958008180c1c001d4014003080d0b201c14801e451140080c148030380d2120005c0b40d136503603514000d811038000300380030b41c056000a040c40c0700700f661003502c44010380004c0300c080000f941042c014800e44000094024041c618910a4110041c9030540314501400100b0883e00c0001c3c0c0503060140da0742080304100300701c07820101c0115081d0301541c140c81c88a500034064003258401ea8803a01b000d411402c0b0000e040c01211405003442c00007a024003191400181c0f82c8100a0031310010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 554133084 1250 554131834 554131843
    0x16030c060c170411043201051905090a060f060207140315160e120321070203090d0c0506030a020c060a092414090f07060819020319090503040503 64
    0x468004015a1007400040c03507414240980c3c000750000da406183c40d82c0140030400528599100b5a000702e0040403203003505858921504080c5c3c20782c0e0f01181035980e100f09100e808205030250129625a405080c4640d00b0000c2403d07a0100c808400460610303a51510006102940c0c1c2010340183c202c50402e006415608001d8600c0e40b078140c0041542e030309035104290843c0b02c041c00c2310048a90aa2005054a1040805401c0c2600040c622650040c0d482d0541340d403588101c83c2c4608010004030400c14034980301201e01d00c0b411158001d03500c0c11507000100642450803034412a001c1c2c81040c1c00cc56140c8807600a184901d10781000103a444d081c20500500e4610001c20808440b42480348007800100310840e80d43c0c08022004060600050078030684019200c00d030100c04a41c481c250801200d48000103849008200364000d8680f9a9200c1d0400c88001c82c3c1100d40b101e2240411011180070b2119900940d440704044600ca600510346c0d944400c1940c154480582d5079910101d004d100f582380510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 554134334 1250 554133084 554133101
    0x160902090111030a020a080a0e09160f0207051c02120f06040c0b130302240309100507020607080c0708091e12150402100507021c0606062d0516030c06 66
    0x200650420704c03019002940c032140c2e905c1c01040071101160220506000341400e081142c0010101d40302031904c1c054542c26486012901310010300c04d0429134141c81c2c004907030003045d98009001c5c030b00d003009120464083c401559100701e0300030241598410051105011060503000c880b405016142014200750f0300d915519000301054840070094054011b0782c1a1940007220f60681e1440601c0100584c141a5010700c44585040104000108061501c010070300e81d02c0f20702c6c2d0050400c6180c49400089a0307855084440f940402c2406011131182800000680f921074455a807541c60803d8440224000013a8a01c10201c03c10700081c105902e441c002020200840414009012203038221780641003d40780a00081d014007400c4110351440c40c407134000c6a0b80796070064826a21101510305050101c403096000b51003403868140d022500500c00c840c0741c000d58001040c05210714050700041903441d00c8003402c0d40148241001000800d028000240744501e000e40c6810216585030300345002a41c4800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 554135584 1250 554134334 554134367
    0x8061801151d130506090a140106050c010209150c0d110d0518030307031206091107060b0d020913200105040b0d060b1c0c02060f181609020901 63
    0x460060015030003041140042001514108002070036016100c039100102c044040d8120405008010004542e40c00040c0603240607200e01500d41d413050940e4080303486100000381c00f400402d004200c01c134414805071100350507000006140c40011000a0b9920071420902181e00c8004a0300e9136070003409100003072050842c1c1c03e25100c3e440c2d0b12400c0e9a154a0600c013040c040c001d0108828803c4202c0d88110840c141010701100d0f030b0396009040141c040120200c2d654045400c0450100b10600340d07004400240120680341414144a0350b107041c042e04c03250140c43d41011485101c4c40140c0d0b03a40020034015040204100c1c010380c6c0310305200d4030800034400d1410091444a121a180d40d900c201240d00712074041e2506a25010340708003003005070206522401d0003050205a8641040b021060100c501d0f111000c100f00101c420403059845240032203054261860007070000d91680d442038681310301e403020001038980d0141a4010864406182e0304600400ba0713001c141c0b04129600700c0046246800d2a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 554136690 1106 554135584 554135629
    0x9150d060e10150b0703020d030f0e07060503071706090a0905030f0a030b0a1d0612070302040e07050f09010b180a05100309050105060a142404060806 66
    0x20700590a0f9440308071000a00c5824010403140c1c0e00c0c0e8580c01802c14030a41d203005500612a07104401c18070360b21850050030030724090020340c000e807140f92181e94903418001c01c0100036958842c01030031b090f003a52052014603a01c09100640c03080000340301050359001d918085065025a03202d010301070b80d0105118040d207416400ca0800040c0c2a28030a900302c2c3d444000d842c800c200450400d00040340c100200e0042d081016403010ba00940900703c0748199500e030302140848440780040d603601d410410702807050f45404241240341013000c031001c0c0e08035410300c556200144212040c6201c0f06003054402e04a82d160031280800900b002802070507180b4a484024028041e0454103c806528004c005550b81c40c15181681c20313901c03450103130b011550070201809400c1d00f00400350040941c070154145400c4583c0b10051000d042c5039618502d603402c10340140016240c0c2d800c401501740c01c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 553956834 554136690 := by
  have h0 := BRFrame.cov_init 553956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 553956834 ≤ n) (h2 : n < 554136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
