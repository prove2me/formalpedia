-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:09.093214+00:00
-- url     : https://prove2.me/submissions/34c21aad-3899-4049-97af-bab5d4dea5af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 916366906 ≤ n < 916546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 916368156 1250 916366906 916366921
    0xc03060b181c050c011821020108070f020c131b0809100e0a110f0d06060828240e10050601020c0307060e01020a020a0306060609050102210d0609140f 66
    0x3080103074943c1010280c040080004011948440c0b00300702c40704100e01844001c40e1550a030210041070b407200361000c0030a0b00c0b4520007d00036040c0140b4aa09001c401e000c18852a41c01050404a0f800121001c2820070050f2007608010000c544803080c910b2024000d0300e848a0704244002d0188145000311030030031121445150540d01c50b900749126a8000013007540000303d006031078040d10302004203c0019030703584601096002864260589580380c40340c0b0104400c1070280305450340c10032840c21030360b058007510289104203100440000c16001c90140540e081c140030300c1011b0000441c0310024003028031000388690ba00c0018860309401e440c60040460491360000502e018110000740140c906507107401030030389202c1c0d400c00810f4198006c01d003c000040e80c07070610320700146129480010326641816402804001d09810460565010114000e4500080e00c0d103600000e40d095002642c03181f1100c0318402610544c2d0080440c182414000e40c01040d02d5818580708041c0340540d104696a40c1c0c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 916369406 1250 916368156 916368199
    0x50406050d030e0114070f0b041e0206040e1038040608061e0d060609110c280804060e01081b2502181605130501030c03060b18 56
    0x10802004129556050403c0d54001c3c420541820501140b1030b0070b01010b034a480ca40e0444070041120f40111000820042112811417800440c20008081503020a681d0208072184030714007030b42c44031180490000b6900f50460902c40040d1824104c00c8000003040c2c1d0910b54170003100d043c00f2201010140400c0c0642d464003050303504541140c3e40d044503a0f10b6140901c41c080040300210002c07c3c070081c1100c2195114101c0c42d0b00590310500001661a2070300d690035044a05969520111040400c9508a42400000e0403070303900c03050684031250140a40309249840604003402040d0010204000900c90f8000304001024842a210950560340c0c3c03495200800b03441c0b2016041440c01806071030030b010740e604440314000036009a0014038413603540010352520a210940f80051000303800304a08800b0250303060b181e840007410000d04122502c00c3c44155440e05001e5039041541d60003454848034032a410402c000c00018680c280d648000000c241c08000044150901552110342c200c141803240d103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 916370656 1250 916369406 916369429
    0x702060708010b130306020a230c0a0308090f070902120601020d120207030c0c080a0c0b0f0d0e0c12060603121303020402160b01060201050417070c060e04060e0c0405040605 76
    0x507a102402a802d0028110040e0054031600441d00a070360004400101e207403004045180464446034007000001c44804c0c0b07171140001c80500010000e20a004c10814001515280d032a89406c0c250000d81d84e001d0704520700014042035080e640702e03038200020040019401400001c010411070f11181c0d03144c00041e07a460054000560002c0c103038250b105501242d96015000d0070307100b8901120a9055503c4000880c6001c0d080031086402c040a44010080d0003042200200700c00045581015032448030018a80110003000c08003e8440c50300c144050400d2002c1c020441c4000c00d810082404540810f41c1c039201140c05600900c2500d504041a0801100745d60110f4443c0001103423b5065900b400041c9d007000c00050071000416078514000b580300d0b48440e000e0002540001103a19050400304040d41a00c0184c2040c6c02e01009800b0206030403c014209440850802003c800c0074940460020481644005510308041c0d00344601481c950b002041180c034222000e10110b0b0300e54041125101d0203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 916371906 1250 916370656 916370671
    0x5040912050d20091903081c090b09071a040506040b0a0c05030d022214010806030c06161a010e07030509120f1e0a051204021c0f0b070206 61
    0x2541100c01503520078801040101c40d40b0502240040e66080701d01c8400c000e14007654100f52011404602506200b5040c4066070038a1291403646469912491210300c640e881403081c1070301c500005409100641c1100c403050341d0200c10888145000e8400c10307161100c0e4084c400740e00b03013012a0040c0440828040d03405a520082c101440c240c5003014076800e55200000103000e010400015a011600c10f10140040f2001898050390303c024046492500410f83c0d403140d10054500007061107200c2a03038101c000041d5080c01c0104040d1a5140060302d010482c44017182e000b50700080a55184042c030002001003441740a90351407061801002e044004000d000304180c03020701c803000030302091182e006160020640c005480c100b220001d00200b0b540e01000c0307000741c240f4000a0403d07201040184c2d40d120010b05c01d43c0b40d400c0c0555008001d03c82e1040c1c10545048056920118095540780000002611007440240151111a10742213411940840c82615017031a1140003890721350002c034809124201 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 916373156 1250 916371906 916371923
    0x90203060f06091e0406030c1d0601030213050f04060b0c0708060109091101140c0102040f1e03020a061202040b07050c0112090b010b0c0f25080a0b0c09060f180109050409 75
    0xe0b451406005007134401c0805078400c0d01c0c2c4400202081a09049a010780049440c001c3c2614086000d1200000080c10050404d8410065825401c543ca82894196401202c0c01050405903c0000b406410181c014114220780094100810200021150200ca0a80086d0f41040e13a81e03d9080080f42d1903a140508445036031580703140c07030358883c50611081071840303142c2d9070415018915030743c01c90300190800c900e0b4442c0d004050001c007031030003c420210700d0701c640c070064841d045a01182d10030119114800600014143c1e040400101e50192806845241203040e106c5625080c0719650700c1c0c0d03901000307011420721003214500002601034030000702d802c401c4103021640b0b007808080041d40803a00c0d1b0403150041030801038507210240100480302281d4001050103414885082a02d10300c29800801c2641c052407902c000110b0b000031a0742d00941c0e9180356034561401a011032010b00c50744403480400100040c01d11100304a401c0301608002007a62000d60482c0c90b0780900c000c0715a26180505102c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 916374406 1250 916373156 916373179
    0x10f051e070305041206060e2203030e030903030f0409050f0405070b0906122a1305040513020307061214040327120b161716020313090203060f0609 65
    0x4640d000508680380b0a00c0c00c1d0f0b00e0182c1c1c4c2c03480901180701100d411510140c41b02000c02c54906007490154200c045001d200d084401c0c0302240411507807860900505242d02c070301e24003004280520a807010214050b007600e50724038540d400600940c0c818001c0036400e52400c03001c648501d146400ba14800c1e80c1c003100401c0c03110300b04604a00e40360071402240364411070800100c2e81d0b24002410b064007556501d003240c1c01482d070780c00200e0124481915a6000c5407010710502c4290604c01c1c083c07604407441a1000100354171856019514a00e0015019405101d03240e000180c0301d42c011200c400058a00204014800c41d5445d5060360020a0340c1c003800207401540c01c0c40007003441182101f80e950184a940802666504500f015040758003425622080307410104504142c12416481c00c5804e40d1420a405000311070500c0141000500404000403200740410111030081044924103030744100280c45995079840624040d6004461140c0243e0210480418a081020075254000c0b002000c500e07000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 916375656 1250 916374406 916374457
    0x615030c07150507030c14121005090c13080706140a030e0601090c1103031003140a150207110f0907121d0604020102070806040c180e1b010f05 63
    0x5400290000260003030410092002600580e4580041ca940c860007040924005901a00311443c80000b0700510911700c8913580586003080445181642c02d462116030754803184511500001030390415508034100000780424011054007034440d0411070315402c2c181e00d403244032480e1180325520800c4c0200d009080e404104000d030402820550301207180008245042186143c940642a400b194145681c1c20b49940d1150f4409c154201c4d0003403403402176207503050004a22906c2c0c80c6902c0041d10200b1044284100001700b403242c100350a400005234840071101ca01e0020095004103402c8850600c60f002c01086402e11081d000242d80004200810302c0d610040291a81c40b0440c9820300c10381d55820a03201903100f40c01c0c5c2c66030708111840007004c0a28081c400a46010120f03041400745500c070350100000110070380603460640c1c10140b40074403180100a101400303030000d407189595a002d1220003010382902d16102c80c0002e40300b6039611440c1d09142000b40ea6602c90b01e500c030b80c2128581d40c80800328 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 916376906 1250 916375656 916375699
    0x50f0d0203090c0316090b06090a03060504081603080f0921030a02040305100b0a0e13030302090609120a020907140304110a030c0608060a0e010e070c0201090803070f060f0506 77
    0x800e0940c816518a03540c1640000c0c01e200d1442c0c29018600d117849414409045070344100062004155003885c9413289480c00a0340c140d040b4413004010315154000a41080080001c1e10242c82c1c100d40f00d070002c28502d18000d00044400c441c0e26000041600026140303902c00100070310358641c0c00542d11801401c00c180a4070a510041503180c000e40c0030800000000c2e03080116134441c140e60300000131012000e034108207078042160312401c00c554070074040c070070741b4112181c42d420f2a41d8503080051b5902d10041c0821243e01130321170a00d6000c1721441c0021a00a004948950303018801c48024499580350b50055030313184010300300003004442c248000b60000c1e01d451a1074454600003818130350700503900e990380d9a0302910b5402c21800502c008080c03280e2400d01e0b803111000340005900380c00caa0f40c140b200942541d54000c048200300006c054800041da40540d5035503000d81b07042800d903941d40c0041d08200a010749035150480300145014205c480310803161181798012840140f810b41022030361804c0044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 916378156 1250 916376906 916376911
    0x30c0703080709410112020a18030506180d170615160c1401120207060609020309030a090f14060705030d06170f06100b0f0702040207060501080d050f0d0203 69
    0x5000d01902d001c2010840c43c84092541c00e0040784d144101102070319209001000002c00d04036266048240b460756a80058281280038507020005840c1c0351020700840e41c0310028041006000840d00022062002c04600c0502c1154440d41540050340a00c03185960384000004007800103000442429010f0000700700c05030000300c010902584003298400000c0c0c0d9902c8060341d00051010340d800c0d1030403c40c006c110140241030385c6410030300c1303040d03e0800070f86a11032089203819150b900151500030005076a110501400410900310348a181045605030749900001d45240400c0811000052041c0884400002d490088240504429441060006540040108480d9400140114030b02211140710b07110003000100d654402030922118014100310803094040d00766005001040084107000700c02c2d03021503d01e6101184d8504079440b502119004410009600600003d04d2406000c55030704841d0507a180310303094402e40021f01e030080e5803911402c0182403c1d0380c000d1216030302e081001d0b4080e59 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 916379406 1250 916378156 916378171
    0x4050c0d0203010b0303120f0f100e041b030506010f090203100b0310120f0210170c0904020f12150d030e040b040902221109130c21050708070302030c070308 69
    0x3001e0344c03a800001d065030008240c1c035031080d000108100384920340d04181a0040002d07409081c040c249a100c4101c507130618010000440ca0090128007000920b4000b962420503160079919a15140d190441d210303c42070dc100075041040520202c1d8080c164421a805000200210000503191803581481e60304000d01c810b000500f4a400040c0056025000116061256810b0300241003107104004e03800c0529884c540c10044541084100310446d141000c1c1c001403420043c0e901c032006200000d0283c80340040001d808000850f4500d40c06111056a90240840c5074400010340103013410b1040d444d86504000e000100d20018241203401d00780d025006c1054040c02c040f030f061400340c01140320307090040b240c40204002680345400a4200e84940303102e4001000c0041d2515014400040140c0b1003031602401c0e09035140c0741914003e0041810303404084030241c2c50205091500580c0c8001d0800319021404252160002490b442c824800c0701c0c8030350064140a800c2c00742d80d460850340b04c0c20080940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 916380656 1250 916379406 916379411
    0xb0306011a030f040204231906062f0f0307060c020a080307030222170106050319060f0632100507150603081b0c0d030906050a12021c05070804050c0d020301 69
    0x36003580a40701903c2c003440684890380d8002e01344281405564460420002e023818680282072000990203502903900010070303030741610420031080c842c025401485014010621660b54031807034244002c0090a55140107810030010305c12103803c140d031100c8042d103005040386020400280401d009602414a0030b5010603292015005280d14a0b441c5000b81c0080c020b00c3e449495003d20040709014400142400340c0140072450540c40d80450f803e140d1603c0180030544805600c8028180340d4042e10083c4112041314800205d04040660401c12040500340183e1002c10f080c07180d814011000c10120f1481d9540074684031640d240d81a00070500c0b0f03081e0442a07144d52002001c10000805401500041c0c0d03a03000c16459800c44183c9003500c00300e0524016580d01401e50040303504411200d048442d03e0404d2590740d4803004044485070441809002041c0c80401c42800a1002c0d078800100420a0078080040d41c84ea09000e8800000c101d40081560740410714040705824029170132a80caa1001d07001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 916381906 1250 916380656 916380671
    0x30714010c08160602030f15150703030b04060b0c0708150a020a051611031009020f0d030215041b050d0f02150f0c0303270604020108041401050405010b0306011a030f040204 76
    0xf60040911240410765080707402100b0300c010f05003442030300e0b500314071012a00400f0251004c00f080500415861000030217101003a103006040c02070704544110000148100007964440501002a402501e0700da411442000c0012403400000194540c4001100543c001140e94481c05140030358410b01c02c80d010820148a50302501440b034000c0b58889116003001651040000145483d0207240da220600d10350a0108200140e1240c040440134420700b40c035280e040c1c00042c1400d82c9086202d04040c10f400c1e103100c0030401485800c202401030600c401030302d1403100d9901c0042107412011894040c0050040340c01c45001841c2280341092860122000c560500c80d403502941d510f03801c094204070058000208104502c0e0328002c0c00c0180340c1c000e03200c42c60103021484141e076031104000c2000f0305200f020b401180070700001c1107015060b00c42840003030000d843c0c1450454080e100304202640284900400800c0c00b43c0c078804840980e14020300421b003503507958110307074524600160003030780c00a544952 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 916383156 1250 916381906 916381927
    0xc100804080325031b0504050604030f050106081c031503020303120403031b020a02041104060503130c05040c0e030705271b1329041401020f010e010c0e030714010c08 73
    0x3030b071000f00311154900050840c2e0105811128001c041050f6040200410080c403195651100341c4040da038010500104440701c9207411401400550040314485c45621440014501c12142002c001d5403e03a0341406598040034001e000b07640e16000c000e505401c1404941d06020303014060990150191401045041078050240d1880d6507000e2000010380240a120056050600400d240c440c0480c044034036207031500740001c0c01d900002d403001030554102c080740c200f03103e01119030101a0030000e001708107006c00183c3c042c08042d0354040c0540a8007903d080000c00f803900010200030f03132240702c03002c1c03880e203040081311440c50100401306448681c044885481180200703001d017034000740c0c0c1c95071120301d103003002d5240250103003100c41d03000108001c15121480d00c03040d005407030480b000740428840002403000180d0814a000d4480c1102d50300c0c000500b0101801500101c145240300e8842030014000e52007810b4440704140100d084c844509100c2c500c00f94820441150040c1c080c00e00281030012004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916384406 1250 916383156 916383211
    0x3111312060b09011503060e0c1b0304080709050f07090303080705250302010c08090d02070509060f150315040207020a150c05070f1809051f0204050616050c1008040803 74
    0x1c0002400c42c0004440f0317840c450701440380402500856000c0000e514048640c020f5620546444c420260301020721040c4002c010801c0d507002d440848141e8104544403080714000302001c88025010350034007404a50301d94081d006c002c043c0e13501a51003403400d54070000140d4403075102081d440d011580c0c10050100d00a120b803140c1042c6803017a4004200e0340a51b06006100b9000641019600c0d041003100d0103130b00d038000070f4800c121001528403c01c656514400a03040010600301c1ea0380061018003000c10b6034141c00010b61250000d0044c1451140c0701c0c005201c228010258003e410202c0b2401c240302001d080c0150942d400c2041c54821840b210b40d9450f942462010307400070b4502c001e82c140a0000194905100c41440b114030700c00c001082c05601d0b455900d20800c07525600c0030804800c003124401064046401920b005440140d40310b101c500301039031a103140941036030513000e6201c0d4401e880c5040d01255200984c940d0325000350742c4450b2519511540040c00341c80305c20032109820120b14807000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 916385656 1250 916384406 916384409
    0x3070207032604120c061e030f020408030d06060306090603110d060b0d060b04060b09011e050f0c06010305100b2413170d0305160e031006031203111312060b0901 71
    0x382a06426611145060403501c4031682080c030611003034a0b007801011000e00c042460313aa040e8500400d4054080c00d489c0028803a0b03420845d84c0e400009101d42c603002d0740341c0045e400c0b102e1543c0c003000740aa442004204640071400007c0c500f0381c40d06100c030590320b484403112000f24081c0e02e0000322040341740001005152507102c2110340c00e8a42c0301c00706640c6800e1103220000c1030704c48101d030314044480c070000b4032214a4050702c8a00059500e040b901c558480d00680d007441010000e025a1200100d07041c558813072007448200d80310302c00c00150902a02460281600c1c0c940090001c41514041802040c0d500e10b5104d0050301040b007d00c10140258194501c0c0c00080080c00391100c000020a104c0b80c0c00c02c0540e4600c0c105150609051001e20456008035800720b84803880e20124180444000904101c0760400424010b810060044148042000745441016490324100820200c0501c1d030003090056203006c401224907114100660070080605220b107910400303000458450b4180002c2404400317 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 916386906 1250 916385656 916385669
    0xa181511070e040b0103120f050306010f20031c02070314160c0b0c1015090b060408070b09100207080303011208190f030b120a020f030f0304090902100503070207032604 74
    0x61340010010710009041c02e0409058a103060000c00054602c09049888081c0c4081d0401c032a1080d5805c50314071880e05195030908912464544083c02a03e1980e2a08002011080c01d00b400c40c1c40880b8407020310869604980c10303140e6185181845020040329000f030000c90701855011647c40c00011104403681d4050001d0f0b00342941c85401103080d43e86804d85071403003044583c0c50003286a170111543d03460360084400150020806004003001b04460b23010320317842000f0701e100303442003c078542064070301900d82c001c01500c0c500c47c1c15003201005c03652050144500700d04e6800420042c040391000e051103030a41401a80194a000d5003000d5110b1020b0740461844005030300c01e00900b6020381d01d402481801103040b07400036518041011060340350000d00790000c0c46010b403001c076045140c4080c02070075001d003480f00131380f86c07140c1c0c6c0e500491010700070209040f03101c5e10300e0040214041d8042c2040d680686035590080c1091410355440303141c1d042c441155165450410030141c0c5142010f4002040503000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 916388156 1250 916386906 916386923
    0xa05121009050108240a11070f1e08040e0601110d1106011211120a0203060a0515011103090d05010219021005060604080325170a181511070e04 63
    0x2030501d81d44101c0b00182c0200029400410a2408010040560056070030409480ca940d03900d551701000c0050003038031624401190b01080f02400e1240002c080c801450082c150f00e0b403840329a00e40210181140728004180480521043c09040508000164010b00c1030412010030280b400c001803401080c00c5950700007440305403070803d001009200032401001c04100d56802c5540d0790f03a0307980342a440d400d00680940d2035011b001c82c01c0300c1d00300100034010b50003600380c1c5c409090000c0400060042100c0210441d0b201a180c1c20b20795105000e40303000791144801650a01078013404000300350f040c149040c0e6656400380300000c1c0c04208010752085a4881e6001000c40c01c4c54034180310140c8078001d207030701d1080800380000c001d08040070007229042c03540718150001110740c2c0c1c00d4034004126605005416101c8a0702c10b014983d00c29002032982c0c502c20788330706003580b907045014210700d86140213200328a01e0080300030b40d059004440c07489011300f82100352192107417a2002c10600c40802c8505499085 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 916389406 1250 916388156 916388159
    0x803040c05010306060f050702060702041e1103071d01200304060207120803040206130f0306020c0f01060602071404020f18120a120813020904061b020613080a051210 73
    0x301665820040ca420300301800003e1034a1805031910f10040d15a41c00e01200207010f40440d83e0306422140c049a004000b0040c032902c91058040d590540001148018907003500082425406001e503031080f40b0540d588200c4540140002c904001010b080c24184440c4500000c0808800c403504200200000001c1d6251072070403600074034081c003c0d840303100041c0321a1000c1d400701e40c240007165030064060715000d6517429000564094034807250300401902498130408010080729400800c0300130b81080c100d9030080b20388030105080311001d10503c40968828041000302c030f080c001c842c42810400400040c01c081802d000e40d21140d02c81d08100079100078401e0140c62510b8580e00018810713000303000811160440790745603104015050b2118041c4556480007030701c804066066541d025901826002ca1401c1030b181a40181c03c0700c06043c1d1441c00a201815078070b9100041d00b0b44119509a240c9114503016111100c8550140030000c0c00c0080400550345c6d0039415440b100d000e03e41c00f11041c62060b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 916390656 1250 916389406 916389413
    0xc15070e010f0801300c0305070f0501030e0d03050c0702190501090806071b0c03151e020720010e0a0b04032906040c0509032b020303010803070b070318080304 70
    0x1001c090b041e01444010b400602026410301160303400082c602d44444090801081003501202c0502002400340ca10018003104001c400708440044a0010000c6013020792503800541c02d480e84081498059400484807820703843c800c2c1c100980010307c180c030017407800b00d4580114401300d8424100c20f0719618121420400c0396400a8000c1c018460100640b0260400340070043c0212036004011884c0b41c291000e00b000c0c040788070130300402546d006002c6842141d491224002030485880762044880400d01030444a0810b402254190b42c1d100c0c82800e00f41550510640d8660045001c030ba04111217403621503010303240c044007070b409402400001a141d9141d464403030340601199900281d4404206404078080034401300007508848112000706000a40c05e2086460303003d00c1d09040d5040c850407407044c80340b9a03404c0400c1170310400c90180050115000030140c0ea00d00c001c0c03040310011f038010030540e00440c01c030720030ba1a0401d18501d0086516542e2458020744200201c1040d0b90a040010a00040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 916391906 1250 916390656 916390667
    0x50402090a05130f0804090507020c09090c030a150b10080103110d0c0302010507170a3b09040f051b030c040c0f05130b0d060302101704080c15070e01 66
    0x121000c0740d4280103e01c0c104650210b001550407004080c52140003c07002044038510607207000e801114810484e40c41d003154000c1d44c4180f031340020380c041d0944202240302d0210209054036040e0001d8000e20711445940d07142c44c2c12140c00d400740c820781542e5560725004c039aa401d401006074022599510201c0d411400d222501340081240e05102e0003071304030040005402e1107507590443c1c5e0242401900c8111508105500f2410308140b0182d0100c0001c11030781c00c42e003007440072030703000099003940e0a4403d00c02504c842401e110000c4140c12184180380c3d0600346003074a990b40e03009214141e02c826440030b560300c0520b004541300c0c83e20042a680c4d1011b491504041040c200010000c41d4144000710300003201600e43c1258004003400c0110000700351001c1c0250480c0c0030000c010517001c890751401c1c003c01c0080285020f002c102d10a410554405804a11806042c60350459070705a003181601c40f9a01c8004039801806291520701503005d204c6007510b80d48242c180f1404d51912241010070604000610 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 916393156 1250 916391906 916391911
    0x5150a020d03020930070306060f080604080d0b0a1a0715090309141212030403030e070b0a0c031710050306071b0807050f03030a0f14090d0e13060905040209 69
    0x42500c14030844c40c00c0d0b80c50800d05004c05c4051341001c040c0340c41007034040a403003442032018001842907190000c00c0020036401601254010000f4000c541e0f220710b140e035140c80302a039002d000903800f4091003100b05050b51258044c0d10000f0250300340140d59070552010460003512a043c0c3d442c0c04103280045c400c1d401900420b540e20b108042001d40b10139034015107402500e02038507407800c840d00149100c9883d80c00e5461002c0714200c0031601030202400e04041300341d208840c1100028200460aa002940040c0c507000f6621005615801c0c07405440003192403a50442c030035010020741500f04440a05510480741c019604010620034180c1008141807606001600c23103002c00038248016103042d0344403e500005190301c030300413917a5034005013042d42c0303400d080c800c0d284040c0c00004144001080140c4c841c68030301c1000c590a00000b201c4c150703c0481680101d5203030b1040c0e0030035546488254429580d2180c0c1e014020b200e05a035444000070b02044036202c2d04a80c0c030083d6108140415403400102003039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 916394406 1250 916393156 916393183
    0x9010e010507051519060b041e080607051303060f0b0f09010501230909010e0924010509280207050709020301052407020303030a0603021908061f05150a02 68
    0x2460705a20f655410ba803490941500e10814244201285201d001454802d80805610805000b92600d990340100164424440d05d10048901800d80444002c0c0f5040304040b6682c0c20050700003503a8440082d1915400f01c2c07001312107841a45400300018440e480f41c0c003a000748002d000641081e0343c100f84818610303100c0b1640d00c0381e2422001040160f1380034580c00402003024103440031305c00c150704200103240a1441d480b03500002c120000b01d0002011045071348113072009000c50b00590140d8858142500c2555003502007100d10034010b200a040900745250400310010000b15926040703c1d034001030501403000140c825030001860400d0060811040c0050319010004502c0d6501d058009024400c030b040442900f1000300c0b2041180c01034600c02d0307a07840b170307005015203550b45011244c0c140100200e0108a1050442441d40e0141124024509090310105402405543c0303428103203072150b814014203260301c486000000700b055182c40001681610044910720340300c410140740039007030401080491 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 916395656 1250 916394406 916394417
    0x605160b2815140103180f150510060507030e120607300e150705091e13050907030218010e07080705090f01051b0a021c03050717090d0809010e01 64
    0x15a82c10341e0166590450302800703800700c0211060001038000d010094074403500134949902e0241800205044040c0d02da1003a54029600d10f1401524404c54005842c0e204503007220120030b1042d07901420041584600a05104842d1707000480050310640d02160203407030741e03004030040c00308a42c0c01000c200e580940c55100748087c0140400526900d01c001104130000b80e4039030f4205040000c00f801520356140c40c0302285290303490aaa03000d4400d41c002203a140c020402d601d203c111100649082c1c0d64500d1004204810604c90320342c03d9405400058100445e80c06100030000c0140e440e0480000c019459000d605840c0d07150019510020100610080500008008100c07d4640c800200c2d0b0703040600319003072a003006180f8012101406a90b121840500100d401140010000140c00026600c00c95880d20a10f003030210b440445503403140024041351081c0440c000244200f01050050301200301101e041034031940004d54207060f2010240c841c20000201e5645550b8400d00c0c83ca0ba200d801c2c00e00c1e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 916396906 1250 916395656 916395671
    0x20103060b0a030c021e12030a060b03090c0102070501080103081b0115030b0a0f060b2d04060c17181c0203120a02010606020a021e011e110601050a0f0605160b28 71
    0xc0ca03851f0b8243c44491031042c1000070010b44060000d60080029050280b100b54507072504102183c2e81d0481202501e001d8400c041001405600c58034005051300d0f4010051801e00c0c418100050b00041012710b044125500c50140ca0702000f002c110400003180035402d0240e807400d2086040c03040342c9840407829616820f1410500c55007040c0000c48102100304515554003982d14118088601480028411030190000340010ba06501010024a0031700541c00006800c2c00c3c140300800c1481ba070100110102c2d000b240d2008913141601d03141325007280f0031654080380e0982d40e00190030a44143c02509902c030005c1401150641c1c2442840b000d40f2450000f4034000380140c0000390728040007002643c61304482c502411150740b140e0003a0000c824910302070b241015510350003038403e070310003540720446114080002600d4580001034000701c45008003601541d500b80607003118144e1211070300100404030160f0fa04002045800c00c1845681501c0b02003082c1c0f65418030241c421a42c03107000c011101d0901e8603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 916398156 1250 916396906 916396963
    0x906050901110a1d0d0c050120120c1014010e07110a061d0a030207090c03020f070b10030c15200d0f0905120f07060512010909020103060b0a030c02 65
    0x84485200301c6062440650700303030b1025050204290920300740c0101034111210100f1002610001c1580d00c243c803010091012700c1c8020030418101650208958001403034002200582e02c01081440440001d585000d041040b68a060350b640c2003d5482c3c1d4001c010042111568062102c0d421468616280980008290009031b44032141e1401904480d983c841200301e00d4514150340441140c1c1c40240c1f9034042150130702a44030b410301d2144800c003500700900050070034828402c030303400d0201201c801c41c08e100d020703115885640f00061030320380c00000c82e10000c0041020303009440010f0540700010010004000c000416a5a440c4003446000c3e03928086049825808070b081c0d01071f15a24079160304820181071013100c910701c0c1a8442500620181c440c48248500030401e100b0b2450f81000b00c421559546030704803018410034400c10106515130700144a0034802d9081106654014500030408035102c8242c8103003a404500c5c5030010a550f0b0fa00540081d80511400a000c42c5502030300c82200130809 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 916399406 1250 916398156 916398191
    0x4030314040e0915070c05030f1e18100518040b01030b061602040606051c0b010210020a080f011e0314031908010617100b0318100906050901 62
    0x100805015011154038100c09000c02910300509403881440071905001c40410f841d01102610b440301050004d000412143c00703a40d05451840c0c1c060015450710745002c040820981111b01c070942c2142001d002a4118500100a042c0140b000c1f03a9821074144030300c08009104d820041113100780700c03083c031644004803200d080304c4407040d400707841c00300305041c0c1000120f009096004401d94803031000701d111182402820000940c09100307540800110343c540310103a403180215940d144800c1803c00c01811700b081143c01c062403400c0c043c0120713407200f010300c00d0704d0050f40c100f16074107800220b4044c204080501c4524142340108000551500c0d11022042c0280102d42e45000180c4219000e844200969504108890000082240000b80300c0b03130524008100e19000c2c402c060001d00254440b40c0b2900d049820706000d001192149402076181854511131600003d040240d00c481d290303c3c2500f4140148484000d100c81c855001403403000d2460510119100136010302c50903171424100603820608035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 916400656 1250 916399406 916399409
    0x6010e04020d02010c060f0207020f03060127180b07180b09060f070b0a020a09091415010e120717011a01141b0102041505130608060a0305031b0f0d0504 67
    0x1a03520070b5591040340010b85040d844910300400142c0b501c144040c07085810f0740039150341d0f4821920701c000016030310201540d80da02030050780d04641d15680815101a09804039185014200a001c900850035203000080c100c2c5098007545c56140d500c0c01c00040035803040081c4500da207000001801c00c0e09100d03c081d512b00030703054081c3c010b00c0c0004055030318069190540b072400d9030010000b43d85140c00d400d2000a5000081e1801c00705003906000b00307100c1c51a00a00c02150401503c0c0e48903a50b0740309100c2c219008048406061101c00d003200307a500e460704006500e070300000c0c0004242003403501511395654003003140d003001c99914007443ca03900301110300d21030314910a091070311001d5410640d40c403004178414041c0400300d050850355441c81900040d0094821a0b100c40c11b80c0018840d4180240d170b440c810340549401510f20b890041c044030b402140a95006540a030081c100d1a4a07951a645958041e10091500b21402400340b5a400c03020000c03058503400c0c4801070402200b50090140060096 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 916401906 1250 916400656 916400659
    0x30923010f020c0d0c05010201050f0f0c0f090d0309150207050d060509030408030d050f010914071d04240f0b0a0309080d061e0b0307020312040606090501060f1106010e0402 76
    0x111803481d45007807007080311003810302d0014140c0381864143d2a101c00301c10070b24030035640994203010026000180f030210491185082544404082da26141003038542c0d80700c0c0350140e090102c1480418440c1c0c0303c03c0201d81e08203109440b030604032800c194100d600040341881d0582151b01041042c48291104c460603500742e540640c1c01310342600d50911017410b5000340c1d000392025100100c2c05080e41e00c2c0e20380000307025540045021130283d07250b0300640300b0340c2c41362046d20301080070318404150000d20a54414200c1003c000300f400900342c02c0340028050343c0340c0402d415001320980040d0b001540c4198840ba00500ca130745400f049075440c1c0301d0540300300d000340703da01030501da66440701409102055040b50740c0d00c10300c013404004541d10b827160240e0f807204901c4550182065214017048844241c4c0c2102c1c000d5000e0f4000b1030a15880031106440c0d080000c204554454441c20b0016540c1c0da40e001c0e15010b40402c1e140c45c6032903034040d0b00050140c01c030085240c61580c072143c01007040003940007616800c03d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 916403156 1250 916401906 916401917
    0x5010e0f1b0d02191409012628061d070521070b041e03030929040b0306091003030c08030723030108011a0a170f03040602030703092301 60
    0x521002030040c0c900b040000e50401c201034407203a944070300f100040e420399131224002d0200d0501203007400301c2c21009024285180051025050815810072500b816040520381101c0b130b03050031301d84c0000700e0068203a00325490760003102800c1e0401c8224050829621642c41e0301503c004009013440e503032403060b8861280103041c403004040220303001000041400c00c10101300d403007080c4ea44c000850b00e58010304c03440800f05110b1810004030340251115170110b03a01955101b0703401d401c041910007145005112403c0808401d0b4100c50b4005a1001610091074081803007a00c0b0f14004061016110004000350074a040c0c02d081400060740005092200f03c2d080311038562213036100d0b00103032006008041d00e001c9040b00303900f0912440208600560594003030700000e0000d4180c5414651000b92402c042d154840301170803040c480d074008900141d480303d1419040314428412010400c2c1564071039004940145c00000d00e00342855000098a4003c1403a007250310b10700c41100301c40002c20141503005504210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 916404406 1250 916403156 916403203
    0x13060906030c0804021503042d0228030b1503120d0c0c0510090305070209090f070906032001090e010306022502010e01111e0a05011a03030a030c0203070b0a0905010e0f 74
    0x119402703e007e04548051170104540e080011580405050803440344005000c07034644070440c50341c3d515010703460a0729203806d10700756542e040340580c00402c41509000012400c00c1e09681c1004041003200020800741e0ba9051009a0b039010f0710301c010500c00510078000030f044000307603000844004c10011428005500e000a150403282e904c18084040d51120391031052111082010460203120400f6a040f40c0c6034542d50540a020b888252201074041c0d258003080d1a50200401906019500149805000203413940341e04000201d003078100ba508968049640350404814683c42d42582e00c10b0903048003e00342c942d0000707200c0610000c1c19030410a503900c0f20400c030078003081052090001c4004150f205184d07c645161388143e1000f05442075820803102c00402540c40c0070a00d241c0e407000c0c010310301d003008840301607000c0c0000121020440c4001c002100100d00ca0705011800ba141c0c00030042010101400d1050a55602e2031510030741d904404a8502032a0002809291808050041c802102c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 916405656 1250 916404406 916404413
    0x50703090609150f05150111031303080a0e01020115063e060c0909060613090f0203042006031807051513060e0a050d0813060906030c080402150304 65
    0x30422100001c003000e04004126003042850401058420482e860030018510500d00400c203586040d20020441c01d090a0b51141c80c1d40b09000101c490240d4000716490861110344e000309510703140d031050310051000b042c1c244038258001500c150304d540c00d100904c03540c0359031170444401511611170881400411300a01c0c01c00ca42000100400c6486401503060007181c030441c0000e0742044a032144554014070300054880d402c65415200e80c010f020b0491071145d80c0e40703020f114603030740406070700c15044030b88020020320708859010700000001480e90160322420203280503902503091034400c0c090b909000c00301c00f415407200310a9907442a40070300802a800301c0d80c2c07600360808005400054000340d01c114007200c0350500344002d052034000c401a854109580c7e45040301c24a00782070041d0b5201007440000c01607880e040c0d00000c2a82d00540600345070000441e42e20121440540c41100841d00202003040015014031848817910303014184803031545441d40c00121810124642603080c0c003000300106090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 916406906 1250 916405656 916405661
    0xb0310090b130e0c100503040b060d0f05030304030e15031e1005130605150a080103030503061201091101030f0b280807090e010b0a05031e0f0a0c1a1c050703 69
    0x24071220300b0410042449142d8940c0318071000f038855000d400c2441141419070b01c91000c0342e2140d50070504000b00380e102c01d0200001075841c410f0607540860582c014001081042c030095020381d1281d12100141c803001405c1c041107145400d1207603030620080c0300b044101c2141905113045124414403100c0c8590301c280f000d503100c038416040f0356086120b154036000c0d280300550054040c2c540c22038040c06d450421008510a906c100f07649000081c03000801003002074010005035030040e80c0100110002107100328014211855000151070040d40701d1070524481d41c04d44a101c2144002c1041031201c800c240380800c1804020401c003414103034000303d10461708006040248041d14468082d11255650303030002d040540b4002014410035480c140c80b10a043c60800304074011070f40050044c00c0c452000d00d4406c1440c0b00020049001c0c2c3c0650f41c101280340201380a8001020311444050714400d0030070f451428004051125088060410440340da51080180201000c0350458103010403036139102c141c218003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 916408156 1250 916406906 916406929
    0x12030c01060605040f150c1e0f06020d05070f09030b0c0f04060801080c0405010302280306020a021b03060402061209070905010909060b012a11090907030c0b0310090b 73
    0x140d46410340118801e58030400030001c84450742d00c0381c07260030385864a01100070700440c42880418a020f041100141c6c001d200000460034506420511040d83d484020b000711107404c0464155600040e0b20011500320701c12640c2020f280c3c5410440e5030903100d40640f4845542c000034120318030540c001640009030404032a080320425101507141c55844078090400c0350300f80182c010700c0c0588032100c00c0740e05091040604aa4005109103018969103c1c000070701c0f40d4550320104081500c040c00700c0800c22900040207201d20a5000b4190203204e001403030513120308000d03203521a410417004d00000d6a140300c01c1d01d88204080c00c0384041512610720146ca003200c6136000d0500b0b103003030800000d455081c030b5000095160280205001060fa0500115201d9182801b15201c0c2c9018550000160448203401c0e00ca0340c1c13050160002c41c0034150300080072810b0031521100c203540450f07024010411141c1c1c5040050000890042c00c50a24600c0c1041c202203070301515800503500e5041042c40d40e1400000203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 916409406 1250 916408156 916408177
    0x10b03030d050405061e0a0209030307050106080d0e03060f0a020a05070b01080303040213020903060c0f0702060d0e0d0215191d010903180506070b0408090603010b0d05071704021203 80
    0x2a66a040c102220001e04400c45055600c0c0c0500c17000103103540c08440400d1044043c1c6a03498009a80742c1008200940151400c590548410b104450000b00300344a250060f0481000a0041c002041801400030050442c09030180d00078906100901104071501a0801c0548a0258440c0d02c80c0b0401c49043c01281000703440d0000c51400000d440e0004401180281c0c020f0382c0746031002c00b00c00c00c031200760b10500702c000303070550710400009100e240e0b0308025200d04a840c0d00b41c945031a19940000e003442e0002c00340310107443c0c1e450005078200041080616000081d50010f4002800307000c00c9100300000090009840c941882440243c21040b68000d019915241a500416415070442c144c000c0c00403132001c4001c18030100350618000301d80003c3e01c0c22500024805440c5c0415552400c114070005002140c00e41801d01401e100d03540e42001a50203400c41c0e40300303151a005050308003402c0c1ca5000e056a018400c80c074101c24240c10003401041d50058058441d07006150705880414614403c07110ba01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 916410656 1250 916409406 916409413
    0x100e040204110f130e07030515090a0e010f0b040e21090d0f1410180807050c0603190b0d03050f07051f02070c081c120e070303082410050c010b03 64
    0x4c0382c590005004c401c183c81ca80100e0090b965113404c0160103c81003940d4200004000364041a510301d400c1950a0b40140440c001007160107001003403070309440c5d4191113002056290300044950341442e2144186502d01540200180716802c0040c94a0b05002c2e48444030100c0002804070060b20b54039424034400b60303c001408180605d500b0000513060108101d16940d01410f03200100346080c07805030a18611215a01d684030569503610502c982d403107003a00310350038040c4500036404c5035100f4021f148200c00250002124581e01032843c0100c4d14840d020074810704002c01403601199001c000d880c650b4024440c000d684982c01d00b050b6203800d03503002007981154126000319560540c80d4022303180d030900c20340e04c2245460b12220460717240d0f8400130801c02d20140c0c620740072041d980706542002000080790300000e0030a81e2403050b941001c030302d80c20030786c0450080800e20030045c203040c0342e44041140c2428001c405142e031000141c8207010080144040010101c1e41854402080d8051407a450004084 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 916411906 1250 916410656 916410667
    0x21204060504060f15050f01020115081606020106062c0405072106030b06040903110f0d090b0316030218040203090d09060f0824041e05100e040204110f 67
    0x1424048504981c81401d000044d1003410540c0540b075100d03400d50809040c0a030801052112880d50200031504540d00e81100c0421080c2c00403000001c0c180c108060038a00001c50000040c22105a002e40304580c54900c04000f465440140c100007102160301c9109880c05413000b013401c80c07954000c107941c01391919080c0000c1540003040303e840c580c10b0042840011400040c00c0d0202e4085200140405030b00383d00051040c90030703600603003526200e8106543c2e550900e5030740b980b904c140c02e0001c4d0b01c0c43d44002002c038206074229001c0401032000c0b2000c90300d189040140414004c0d0140a14000d06170040b813007081c5c400c6800c07806008442c001e08115164034100010300d80d00c0200e0a09880401c44840d0302044041c4554601003010031203445001c00e81c2c850f03800c019010791180f025907600050000c141105c9a80fa4061140e4000c0ba84410004044280c0d11403021501d010300302c0305d10b45800d040300704401c3d0000c4480c41d5026404a500080c0441761130303075041d50741c840d500304828400c0c3c00050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 916413156 1250 916411906 916411913
    0x1030335061f0c060c0c0c030807060908120708060f01050a031a0d2405040305041517070309140c100813140609060a02091f0c06150e100b160501021204 67
    0x410f10300c26001d00002d000b94002c40909450001a00074050045541c1000c24000315410100809001d44186d00000e600c0e099500c426845401c0501300c07006e090220b0b02400f41150b40200041d130020700031145841189140000078015105104c818414551150100081c0c0004400d0710040c6001c0036101901c040c00034a006a400c0980f00034100c0c5e0004203000c42c00e5000f00600c295486554551110b9141c10f051420380e548069000c2e00d05010040e180e51102e085404010340356014444030b4402045107440c83c540300360040c6c01c051a0311980d03032004e080303220b490350384a00100c0170b200c1d28108091180c90f600c804c01804000e004000e4510b4004084001840350300081c0c0912515140082d15107948901440209a00c5481403080c0d001c1e003030103455120240a106a05403141395030900c0d040304540f0395190410356003040e0105400c0500514100200040080300a500121007408407003440d003404030000080c01926502c40403645104811001c004d0300358102c0307004c1400c00401582d24031b890714 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 916414406 1250 916413156 916413167
    0x180601090305010e21161407080d030203090606030a0201050a0e150f0309071205030a210501081c0e0d030c02120f060610020a02010e09100b1201030335061f 69
    0x90300c05c07524200c1c182040104403040d41941d103040001e0702c030440346417116200d03407004207485081040213004944000414143c10061410000d40503107000d0b03200c2c40c000d0320b510b0030520010103050081d0041584200180c0c0d01c041124400821424941c021810240105a4410f2580c01d070900850380080c0709180e525079032018621858070304003101c0d1050b071511030b02d00f0310680c0e001c40180140c2c0280300c030039101c60140c0c0244c0c100b81301c83c544951041d91466000800d550080e17001501c41d0f000f40352810105010b41c0c1141d0813010803810178a50940c00c803000300c0e8000c6a0f8500186c100994141000f0842d41c0b4000c01500385003544040790b8004031083c0ba1142c07100000d4801900c10407060348100c21050000c141c030201560141c460520a440d904180305802078018041058054003810100341c0c091014003802e2a03080309900442150f045250281002d8030401e18403e0240320300c01c1260312440445888004240d0064031040035488410104a15109401580014456400780301854a6000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 916415656 1250 916414406 916414423
    0x20111100509010e19030504091a1c170f090d05010605060f0301060215010503060f1b0408101103010e01140f04050a052a09060c160b07031805180601090305010e 71
    0x4d4041d40c0038140d000203501200f6402c3c81004001c1001400200000340c0c1ca94864104002c070103070301840520300040011003400c100d4524160003113400541800b48048601401c4036641d684840c1d51600e0107905071580707180592094140700b10003411524040000c01c0d017140000300303405402c17a40c48038124045480203070801d0040c5001403045c141c80321041000350f45564105d8401a024122a46901d8401100500002c0010245403c400016032510b150f8000800041200401500102040d49a000c084c2c5400502307110380392170180014003c98003260030450444581d80c1d0f8855004012001142c80c83c2c042c1412268071520348401c008884816400940c45030b00305015810040d100e1000c60744e41e210a00b02d25802212c014060301903642000c400401502000c5000c0b50180c02e41c0160401071203580d41c2121145c00703008141c4104140c0c020440e464404624581080b116040401050b884144c80c2e109203210040d40780420200e9000702992005103070000000d001c641c26404a603039603220700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 916416906 1250 916415656 916415681
    0xc1b060905010e2a040204050d14162303071409090a0b010f03290a1d03070302030c0d050403080d020306010521011809120806031c030f0c11060402011110050901 71
    0x407a0900400d01d082d101f15130540d54010020780b000d40302c64a0309442c80101010802c1d00d84144000a90f181d002016503600610340b4030081f9a035480464000c5038903403c5140d42d180243e0007000c0a121948140140318900d480c103860003184c50f954004158a000031419000d4800804d0b50004036039071030412502025280603091840100c030203030b410f081501c501c440b81caaa51000940c04100440358503004076030160821480c0d0078420105004860865020f008100c016074030000b0a4018820180b0070981040c0a84c01c06600f00340ca0342d200c2c000f03640318488042000c650b0000019205a00034402d81c1c0038014403101300107030424051003030521800f082c0925a004981c2d44260510444180500c0c0040c690040800300c4600c203d08041d100d4510142c80f1b43c8e03240c0a404116060807484249840c0b442440781c0e03010a1b8644008980800c6580c026030b4039040011030003040b1140480000c1040c5c1084d42842c100d2550824940c0722800c10f4010224000040d007086d05200072440150040e44041c401e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 916418156 1250 916416906 916416973
    0xd03021c060b091806150906040302180615040b04290c0624030703120507080703020105040201120527160306290102070b09011b12030c1b060905010e 66
    0x44c0100319100001e01200e000b03034800440d100301d00072007070a1800f808180c2c2c40901030170309090300caa00182e4014949845140610340c89410040d403890540c42e01c0580030411442d0074074280c00c04520512070300c514012101045002c0c0455880c07048c8081c140381a00301081540c42e1181c4101c2c161a441c0c08065a91103001c0703000301c040f110b61081015610660f84001070061541234915515134601400440c5043e06200042c04124003240440e00140340003881b035400003406260601c009400d12100600000145181000b0020364042c4ac1a0707029000c10100445d45404820070f4070986860b0844107a031601c00c03000b04c00001004040d401c1042e04200e01100095031890070441c25007603045400c8800d0059025120821404010100a000d01881803414000312054010f15040300300314008121011481c03a0502e040380c035803510607540500741c6403030007850b03002d0080740018100001d401c000c0c06065413208041d04000b025840120429200001da5041241e00c484003100015588840580b262 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 916419406 1250 916418156 916418179
    0x403050d0f1d0411133c030308090f07181a0d24110c010f05010f06320310141c0602071a10080703050d03021c060b09 52
    0x140101c95003400b960001032012280c507001c40422024107848031042000040400000308100342010b8450040c118a1520101e407854040c0110202804441981520900b001c1d902e00b050800204031011030740c00d80752405160b241c0b4182c1c203007401c0c4010110622441803c070700142449002000c9140d400100104008554814101407000542d0240443d40000c2420010700001c245116250103600150750403030f03901d43c514107000120b4403c80300d42d050843c008541a40303000000d004610b40c074201c1e40c005018551600450808049442c004e0a040c40b9110114208404000c1403100d2100515504002c41511700b103d80c8410b070740140c40e6290107866080c00401c80207040800490540c0001e452006001006132200109030080d1200f2901241c01704400c40200d0408541820f0045201824807898100105100d0a240c032580c0310b80d075190042d540800c0450000319175016131180382c0c100513a59a56900035456842480a1084d03801460624003017805081da03000b8001c030702c0c0c0c02d450b95407020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 916420656 1250 916419406 916419437
    0xc03060403020f0f03092b06360c0e0a0b13060e010506040e070f270e011a070609020103060f03030206010303080117030313050c030717010b0108041208060f060403050d 74
    0x1d12031b070201e00e078104544080c911240c058007136202c2603514600d10188034210700b55a6020a030f4106c41d003502c1c45580090401d581442c0715502141c88030031010f44548940a580e82c420328203042910542a18500e074500061050140741c100c1842c20000401d81d08440c150601c0c16402000207020341502f9800a00001c40c40b0b044c000708440c151020707a200482c0b203549156084421280100b1103100f0009031104041900c601c0040b140c1050b880040024049824116000120795050303204070301840c0110340c420010740d82c0c54100d58010380c102a01064040150005a010304060f52051a0000218400109041d07002c142c89040e83d10990302c81100d66030780c0040c43c9400c3c0c1110400c49064204102042c1c1141e10154040303400c40c811026501101c640d400005e00300b06056000c1100c0e03120100004200840c284a03510b001c0c071003400c049413603080517102c3d4500f4500d5101e08a0a10a404001c50300355942c0d100c5100c62100700405455a4a40728500191281e11102d074210100310a015446801c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 916421906 1250 916420656 916420663
    0x170631110c060109090804090c05030712110a080c1b1005070302030601141b120a180609060c0602040909032a022805060d0c0f0323090c03060403020f0f 67
    0x1049803000b056180d003030010400007406038001c11a50700d801007100192210700c42c000c0c210810210340b106500d0349001c0e000a0610798040c00768590b154a81440d241c0c0508041e0103a9204a07914909005651f0791044580000c0c802d412140200595424164080c5100081c5150f50341c1c0f942c030410301864490120a809900040e52000d02146500c1403c00030480043c001c0c0c4144200002c6210801107220045030512516803120811904009266012950402004100d2644082e00700f018a89010344c01040c108090040304100410300a07000d0501885405841c040d00b02000e00f040b01e05070307618024108140c644800442c2c00f04800201000c81e1910781d10141c03035a009000c0b801e0080048406c00d1040030380080e03584c84c62104071008100347d11100003511850903103e500103809188401d0140900f85030b180b1030000c0500308a405800c00300c400d07c450748010180d03015a21a81c4941007a50f0410141d0a4010b400d441150708000c1171590005420a20b8001030098948040085895648 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 916423156 1250 916421906 916421917
    0x2c1c050c0705090c1603031a0118060305060d080f0a1b020306061c17040f0b0f0d0f0207061427120901030905060a1b0309020117063111 60
    0xd1903040044108901e04090300b2003507026003200480b40c6000c05005c0c619084900c1d0510a400103956640044000000c0347c10500e203500e0242011a5406880c40c0307005600650b5005941c2090f4440c40407880d592503070f4400b884003a52001040d5240e020310150004035070400d04c40e110000f544884040c1521824a120044040e0054003424291b69844240445000110000000c025003240184c002c0340444c20480211608582010368452030412590f100450540100441c40c104000781501e503d030748004c4a0a1158036400443c4005408524130300a0007604805042c075400c012405191840c840d03011482214007000b20100345c4150346070402404429407004070b469010301d1501990410075405440c1080d414034000c44c03045819520305080400c1581e600302815102c2001030711040784003034142d400c0103c61400b00000802034000901c404000f840340c042e002825004105561240c9001c094582d142d40c13104804614050b140442507900d04505010140ca03000700410b002c0c091404584 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 916424406 1250 916423156 916423177
    0x6140a0608060a05040c0b0a0918230c0d02180a09110d0203091204031202061609060f02101109120309060f0a09051804051504030807032c1c05 63
    0x40707542d070f500445030001e280291041d40d4003508180c0006020040300d00800301d0a01d10b64503000c0a5281490030410f42c586242d840c5416070900440e4580e9200da12448282000c584403400e80c952581c04c81500300d0311034000c4071064140001102051910394241003416048140c500d00b140903520141541214160100030b0780780201040040003142582e0099500b201c0c1107010740c3d0f0b6036107224400e021140d22a40c41190404050302d503d2000d6074042c89010743c4001080c080c105410038480006010407214044d100900a41070840740d43e0b03510030004010390420f17007002081030b4041e0120601007a0041c0b04921300c07602006250301b00c101e9001c419104e01003000352809051440400c568a030740e8002c1e0501c3d404100304034400154a80c0c480100040c90450940444020b040500706136040c00c2000030480c100c007044006100002c0e5002d07052582c0401c0710314000648040b0000c0d80c0c41c0c2c02d01086081c000940102c0020103982901041c0176607030070f1455159060710400c0610598103800b504c0e1000f07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 916425656 1250 916424406 916424413
    0x1020c01080c030c091503070201050601200c06030711010914120f030703090212060f040605130b18010e0f07060206010609140d080d0513030815060d200706140a0608 73
    0x1400741c0c0c082c0b001915071940018100e803031506e00c07013190510307a400450388000103030344820500c100c40d608111103900510721034071405220004540155914460710811501034a4000f00184056104040301055590540000d10503c00307a030510200004120107160414060064095001c0308920200c030b075000c2c0eaa20386903003503541d01d901c10707401000414416a080325440d10038078110b21050140ca84512000500d05840d82064144801140c60042003d480c0848020400c0045081d5131501c1d0f0f0301035945448003401001400900c2d004d0019019908054072072064420304000f0085080340590741d103603007112410f0381d82d03600403110380403944902c0e0000c19000a207035885003419522000c0c4a80980c0c039030b41c40d16200da0f44990072903900701c03010b018440510754008105a0b010105581001210750800b0f05000070b9800211640314541d0442d13626035079600c09443c96003620220005803004000c650b034841d1054280301c03014050340328018507550f11080002d11b0007640b92284e00152100700b00103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 916426906 1250 916425656 916425661
    0xc151d0102210a170a0507020c0109030816022d03060a0612120207180b0111160b13030f0b2e33030b0102070b04050904032007031101020c01080c03 65
    0x1c859203c01060f07820801c12096551242e020f03107400320f000b030340e0080000400e803510b080d0090900c0e4852800904101c846801000400d80c01d6090707425200d00343c050f01c03820300218030019100d00d8030541c045101d100c848592801c0c1d8403890b490358107a0141582642c000d0b548511800301200d40b940500000e84503011103c0011502e5440c04e00d0100903c3d0045030b400b80d44a100c50b944064156a0300e80c0c000b51a9880e1001d1075030f021400121101c0300e000101403c00f40d0050f8000041401d00421040b040c003c20104104031a02d00e00038000d5030041d803c12850714aa040c071030f10b54030301180c548100c1305810310201070311350740290224201420058100b015034204400410701003242d204006801144082050b41c0d100702d40c1d030390118200c85440000340586282e00190030007a540e4001c4860705030900040050381c4401c03d1090b03111341d25107400d600a80510b454001c0b18001411105440d21800794040b0400004a90340c1800c8603003602280c0151040200449200c2d404440f40030002005201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 916428156 1250 916426906 916426963
    0x1302131b080c0c061512010c140f070b01030b06092a07050a0c06050408010608010227031e060103060b0603070c02040506130504050d091d040209040c151d0102 70
    0x1040e070005903a06907645403c418011075071500c8000c0d03070f007028903902e54540d035650fa2401617451140c40326804028410191a0700b001381c080c0d1814195180315040000e00c0740b581d4001e0380c0c21200b000790f0200000100d940c42e4180b175281c1030400c482c0d0501074411400400e03425125050384d81c0c5111207000f04c040d0902c0d80306520300c08940004204542034400c8901d0781c9c3c0083c141074080b501802d2699215500c03949080d84050a44109134000b40c21039104200d958030115501c44242508000300c010710601488200c00310349032102c031601d120001d030402100b5902c000c1d070208909041300d009400c10301c0801d1400702000710358481070f190b25001c5070440341032100600b003a0f0080303540070348020f1100010002d8a2008802c1d41c1c2c04680889580c0c02000d8415800d513041030075000034002c14650310001c98031f030401484000170090f01c0a41304000c0e40c4006400c125006c20140c0241c0000c8000c0e5100014035200545405d0f1a068040c540360201d601404040d4800540d0010b403014405810f04500207240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 916429406 1250 916428156 916428167
    0x60e103602040b1309050c01030605010203031605090a03030f02010c05091f02030d151d09100e0709060803070b0c091c050111031303080a0504081909030b1302131b 72
    0xc0c0803038029403901c0340408190746211100740b5058420402140c21090381c070700542892540591141450728004003844140d0340001a203a2040c04049214070100391403005540c0c90003041e40c01e07039120074150004004c042d404400c0078503070344568000340300c0c0070544c443c1030b54a4040c80c02c5a03074202d005131011412141e00c00c8103003020203445006907490300c41d492500c80140d88041e400013103001a50034041058041e1060985001c098808085201d410082505a21140c10204001e051502d500000b540c03080240021001131440000800010341e4034100c00d81c50b5040000f041e0740d02001140028840841281168070800e0002c28000c420341000c15044000b01c1c200205031100e65803180031240d00803003c00110f01a0110044125032145a0310b001054014014003000605040106000c0001e45120980d100c07a030803d000e8241818210300b0032591400d255001502805103581403200d0f482031401e1548445000740c517640483c24850200b28143e03100040d40e2040c8115183c0034403500c1c1d2088 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 916430656 1250 916429406 916429511
    0x801090b090a021e220806010303021504240e0c040629120c09150c0607200703060b011d09060d08040b040824060a1809060e10 56
    0x40344c401c0504003d601e86018140c103c82400b120001c1c2c15841144000c240c110000024010380c0300400880d0704565000f5140c947d1900102424080000400c0c02c01100384142d40c40360884084600d0018004032012018040158102d0b010b405004840882400c040c042d40081c0c4080407074445808a842c20f40c10008000b181038440868003e0003c0c4600d4462020201c7c01082850130175601d450003c1c003000340d4503103071030190482c1107010014075903a05070110301103600218500308400700340400140c01a0483c84180d080840b80a04000402005240d50000d00c1c461400c0e640c80d062180c803070861209503010389940640c80040400041c10924290000d880c0f1580720b40c4105040507035034410f084503504a9000010b103900311400400744003006001000c103500010f01e079600c103810403002088425030301d40107200848030000f000390a800a541c000c1c0500c5a4040c008006050b040300c4181d49400e0a80c0305072000da404c101c25460f08290040f01d40c40020351b8202401da081e28040364010314810726 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 916431906 1250 916430656 916430677
    0x304030f1106062b0c030b07170613110c10060f0807170a051e06061f030b1216211a19060315060f0614031e090d0801090b090a02 57
    0x1c0b0382c1882000c42c0000b060411040c801c4401505c80f82c114504200080001040f8101300080e4442c148040005003800640080c42030307c8082c5514030008121024280100842920300f074002001c0c4542d240004000244000c5000c0812145458070007064042c1044e100d001e4040d40111010b00032000c0d0301540341c0d181c1e40c0110403911545040e96030217007081506003071a070750316080e1007210b41d500301c09000f1a50702c404100c840550a40002900c0c0400c01401d12145081650300c402d000b400da203804c0b401383d070200d08450413150000c2e8250041c041d00782e8240901029682c0c650700310101e44c854207000c1600c03142c2c48004103140d42c81c981400030207890020034000d90003405446030340c8170b0703c0c0038861507020394000c29410240c40110000030b800c2d9001640311941c100d140344020050540c0c040b00d100d1500080c40c905c240d480c1c85003a41e200d988164580c00502c1d12580005015860000041c806d01e1a030306a12203078050303a61000f0600403603100d10411a0400c4a103070024a0180d2541d009016007481e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 916433156 1250 916431906 916431949
    0x204060e010e0307030210110106120f12090f08030c2107020d08040e010f091a09070f030209090c0306011704021f021f0209011d0d031809050703020304030f110606 72
    0x15a600003420744028034000300042900c55100320f0808e10f0a00500d0042d002c054002d008041007961824005021008060407a000149071a0080c500c54100d11000300311049212590607160310649803260310201900d01d03139205002c00c400c1001e103500e42811b030100d0342c0d410301f904149003500ad01c00a06401c203c00c0310112410080403d001254130344881c080c254902080d5112420030318010210354145100329404101c05116100560b500444160b0041c10751808100c1910314580030f6010780911000150710400000801000c0ca4414019510940e001d80e2500400d40c140741510031002000d0b90060340281c44ca0394203118100b2001c0c80c201024020344102c45508203000303080d507801403901580e403054540008109200d903034060a050005641820f030f14540c0d500240001d080380d041c0517070040c1072045600e521860010a4159500241192101408145441507000f0001e40c41118110003044007000580c10180c800c4c1511601c3c0e840d0b0000400c110344483c410000e0b0f0300190307941c5d24070124 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 916434406 1250 916433156 916433159
    0xe130504080f0c070e0609101a130905060103061a03040305032d0103020f030f030d0902030c09070e010306212d08040302091e0112060b06041403100204060e010e0307 73
    0x1030b2050082654044007400351403c6420010074614098001d006148207558007400d10424581e081002021a07090983c0114040e22a00010b4000d0040b102c010241680d001c00000300120141c02692103490266001c01000d51600d0340c00f1100303825007a58140d000018000a40001c0c0540300440d00448040030302140340120b04001b070000f4000703030390303814000203414010421401d021000c41b401c01000c5016040d05d07940460519684e00071840340381485a01c80740d180081d502e05018250040740003900c154410f00d0314100241607200803940e058002490440001041d44c071805484814808802540d520741945071106140c609285203c0010040107104c0d81546d4100f401c0c1c80d0b61000e118292458036603245004020b5881d2008103487c000a640d040c0400c98840c922240c1819943c0803825900c40c0411414000c0050024001c00b60700101d0018020900a2165840d00c0880c5411030842c0c24501d0302090800c244e014a01c43c00c000b08441348910f44056002c1d141a1100c0200502110340b540d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 916435656 1250 916434406 916434427
    0x1005060901080723150d050105040b180c191d0d0c050904020f0909070305010509152205060711010c0201270501110a0e03060114030a03030507031b0f0f0e13050408 72
    0x5e0402101341a0b0b49130000d1640a5809180201030041800711800c114140c400c0d80070070b40c00307a500502e9484241800300010441030045064650009410296012140119101400c0d10101d00d50f5008420080c0130310084501d4560039900d1450351140d03003031091501d4a814002c000c03030090812a0b0000600503801e0b43c80d1a46d00640d8171030390291009029031413450900070300711035019018585642054039030f48044d1042c0444150000141c5070b02c014080d01c1c02c2d85403040d4045811008100303001c0c0d01d041c006000e03400303500d0802c10340051008025400240506908840d0b1803241029455414444100100108454040c49034051000031581658404044183e42c1c04220800041440800710303c1440c02c0c200610750140c00e0603000740c008241000300195445205000040401d0344400014411900c250031103403080100d4070740403030071000205d0050329002a40214400241441d40160449445242840351820700a403030340070700885003026000a010020000c0c0c446a00c208840d07010b1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 916436906 1250 916435656 916435669
    0xf0c04090b010e37080604020607080c03130e0915012106020705032a060406020331030f03060f18060806010f090c0e03031902120c1005060901080723 66
    0x5202a013544138044582d400560b12400d00c41c0707900c41c001102d5841042c820740e000050165045901222442c1c2c8460b074a2400091034400d44031036153364000490b140d0310240d1070043d0501034625200743d2100d240d072001340007540ca0118a4010083c041c1c0f580040064012208401d0306541141c03462155052407511740704c0c2664040e0f08101e03001d51000071040c0c441c02090401c0e0b00105182c80c40c20081078402ca025554480000d407001d4000b543c0000851080944448034290240d485030280c410740002d101d555591143e16042607000c5590181c00c4000300e4440e1080106a804019000391601c0c00d05001000307000710600b107074407602c1c1e8402c004155030400708603603402804c0102c2ea0105c5103040c01043d03003d0b43c00840ca00002d0007038501c4028500d69011041d07034204c41d41a0008400b010080c00100e00c0c006400d114010300c04000910005484030110b40100c40000b90032040c0b0958a0741c00602c00840400d210f10025504103c0d0240082e08551120101c160700e940103200c038900442000804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 916438156 1250 916436906 916436929
    0x50402130b010e0a0f051009060906031a0a0605071104020a0f0c060e070e0403030c0c080f090d060f02071b08031209071a0d0b1005030a0e03120a0902090f0c04090b010e 74
    0x44454280c0c03010082d500d40307102c05c7d1200d191a45001c0e01031030b203030400142103c1068024001416203c10744100d0740d10091901c2c2040100040c002429a03540d228058420340c46240d00340c900104080401050303040c00e0080750001542da6403800350b0300c010306408644aa001c5c107000c035000760712101d4940b6002401c00c00c0700701422010401c5881801d02d0b10703002c0c0844440032445010301990610210100751503809540d0481180c0c2d50003030ba19078426001030380000d080200145a1403820315803041c0c2c0300035903002c0c000c018490b49200e00c2100040c0c00041c0114203d1143d02c0b007987c42044400c00c002204501a508504110129502c042d1208030303406c1c40d038901000b64814510042041c0740c40304d0003800b8040710b020302602c07094142910200c0042c082e220041c80c1001e02c50b10389202c090301c584100b04542c81c3c1140301d05880f0b101d0814045580140c080010264480e02da1340010a9100040307400c418028044410450b15246c41c0c0121540035042c280b14a0b4184022243c0c407a076540c51300360b00c442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 916439406 1250 916438156 916438169
    0xc1501081e0c040c17010e190c052b05070210060e0402030d18081506010f1b020f12160f0b0a052a030309060702061f12081309050108060a050402130b010e0a 69
    0x1506440c01401d0000700d090018942200c003810b00c0070021042e5086021900030180702c11044502f010001500540e00c408012040d176501c0c03519040007455a070105500800b00c0322603000b80a01651550507880700320040d2030103503044d04840c8400c0c210a001d1603c0441410003091111200d5503601481400d08070f01c201083c4540288404010380f40d1390140460b88181030030700b4100d00281080211010186481324001e015400da41f17941500c035922a5028441c8603550340450311140300c40344405040e002c0c03601c945c15030719820400100740103103618155007828445079211400c002c0700940548001c000c05103441c110712510701c00e115000205200661003004000c0003022a810074a000a180000003008928141007032100e080811200b000300c40120f0f030140324250410605414201c2041c41820030018a0044690f800141c441081d00b14a0484501c1c030300b0344410b0350f00c05d10300344155101241c00035400003818110786c0c84010194440090200e0614103000300b04000d90114484000390382024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 916440656 1250 916439406 916439429
    0xf0615030a0207051005071d130608011a09060108190b0604080d120501080c0d0c0902190914180714030718080a0b010b0d020c1501081e0c040c1701 65
    0x18400c2c050201710000101403024000c103e945410310005022601c100c2401002a142e071074088929a47c082024180c400f203200204141992200124028111060700c0d00768200c0070301070711240d40b130080700c03c40c86541c040c1c6903c002c17035481d400000c400c1d2111503920540380e0754609569885413a0342020b00060030260008250407000a6809084070210f480d005641908190040c00507201c0418074001301c0c80c0036038800e01034210501d031000e01480c2a4001c104864400f040d0000a001e4400100f0703040002a00d940030500d40b42d0040030243c01c15180c0941d08403200000003010f000400b843c043d4043c001d0701d41417449004c5007011244a5005464060000301600c1031050040c2001e1105030080c000c920003051030601079078030402d0703a60301441010a41e001c08070b1890300c0039100d5011102030340281c0003510428041c44545900303c140031b0240344040c2c811108840c1002c80405980f400c00c141107001850701141410400000e080004000c5042005505080c044450301814203800380100c900503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 916441906 1250 916440656 916440667
    0x140f04120812161d060a0c030e0d03080609010602030a080628030b18210318160f0503030705100513020d0b16020604081e040b070c06180803030f0615030a02 69
    0x10490040c6001261039000c0f038209052103550360108607810300401d03040520f2104843c3c2812780b40140c01c00762503a0018811541c850030503034840c038542d2203643c0c00c545180d180d98945004a0742c4e80141841c060201b9081c5020a002e4508110484022000b030000c141a03010b0385010216040c8082c2e0084508022a50922041c04405846000b02c141004001d00b40c0c2c0b41400c00c0403003500481452601204000800300300c803d1a81d0420800d070b04c0c051021100c03030408550642c1c00c400442e01c030b00010411900303000b1034035140201c00c446100c0c1c1c0103c0280005180c0121a000521010b88a80424a01c43c034a160068032004503007031405e4040d0703c0e890313514074010141c402847c0440c10b25004541015041000050b04141500d0070036040500c050102151105035041611a0703170411404c0c45400b282500c1002000407482d8203032180c503620301c01240510340500091101c203005500054005000060010305004c01e01503100314000e140042ca00c2100303500c1010b80d80305840c0104400d0700017a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 916443156 1250 916441906 916441951
    0xd02190f031a15070602070203070e160305130201032c010204090614130e120711030d09081e010204050d120306060e1c1a16140f04120812 61
    0x3451411a1089464260482c039500020b40090012114a0748224002c42c00c0002e00105505403000307139601800f12800b040d00c030548036030704100403514201d510281108280b04140b080c050b01d80075811000c01583c182c51a0340c015030140c207008410b10050045010031001c800c47c102040e00d02203d501000503039903410500140d0070b4810700d41200202d9406490307008503e413516104040204444103002802020f0f5020300d5003001f40d41c018180228201060b004140040541502426181241100c14500d01201d0940e000c034810f04ca00b0b011500141ca107107440150210010700c4e180081c1c000145025210000600b4001c030341c99007501c02c580700c0500e0014041d0544102c4001d04210700700400c0c01504100080c50114080040c80c00d00c120210f88002001981009240c5141d00350411407000d251900c01e4040c903014400301c0400090380c0c0740718032031900700400c00c07164050268565541b0349800c15a8044401c0080b983c229003c15082142035544400d00103903130b000e01018442154501c1c070703a05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 916444406 1250 916443156 916443161
    0x501201209010c0207030210031b0302090f0103050103152406051306083102040915060b070503161a01140a0b0a02070302091008160501180602060c0d02190f03 70
    0x4001403910303031400d02c08018094000800c2c41c03c1b2a8101c174a01d00c04640c5147c202c018140b445c2003864061801c1e02c940c1d540d650150090500314105480031104084184011020b5403000e100c0904201c50300c400b28640d18000d07411481c00220741c6241c101120441d109841131102c8071380d0250000642c040303010254414049011001803100c1d00d81102281851502c3c0d00003990642c5060030000310010806145581c2000b0100c2001d4006008200500c1141000c0898040d9614038820031403500e14081010b144c040d041d10b8481d82c01030011400c01c141d02d526038103102490135056400b07109074584491507214411340c142c0070700094920003840303a49080512003901c40a40041d005094107000b5a40310550000703854088940456080203030391180c1204c0d030131581a50b0003110680c001c00018003407015545c4044011141b003a43c4a07090419011160341510900c1d0281e200117800c100049419201107001815062804000061030120072160207040d03520490800c0e03000c00c60190b40b0030b84d601e8251 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 916445656 1250 916444406 916444411
    0x4060608090d050a17150306010b04030f140f061f0506121501030e0d0e15030c0307050f0d0e06060f030303010b04050108040804030c03030507140309090f0405012012 73
    0x5042a0106041c000740315900c96501404500c00c0100108201c401c0902c10700640c9106012a10040c8440c1000da020a468440348008107010703200d0a0000112610352904403000caa4020501840810590f51000c0d007140000010030300351712410013440041101807120600501c1002c03200650410135145040035824564015840b0380e00521101d40d003180c801041c254441520500e000b0a10100801600204044044080588642c541100c000c1d41c0091150f60146000c5800f460344200c1201c1c8003209100450b4100301c01081131002c0751030180a00b001e01003103903900300f046040402c868107000450b0241c1d07100241960000d000d0242c24140000c000b0b240f20401d5007d503155604011380d035100f84c400c80c42468100500344001500344a4100d040d80d014640c072107014080716550b400c000f001e07604904029155819402200039040703200208403180c101028000880c181d488140d030101c3d160005200f03642d1952202c4d10000101c510050801c0020741c994121503e402d43c602104e00e212400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 916446906 1250 916445656 916445669
    0x120f0706060f2328030b070c0506240d080706021303020906011404150e100302040f09020a021b0607050616020f0a0b130305040b0a0207180c0918060503070e060406 72
    0x103018441102d031101c04c0c00e40752440407456130b43c0920f403850303042594440d40d9601c042c0c00c10a058060008281d4408992440d141c024011038116444985c081506030718a8070f814030070768a5200743c0c1c18150801d400204802401074010741c3c2000c01c1c54481c401664024910b1600300d070074441c001e10031854041d002c40d81040013032a01d16101000c03400c2030240342c80f6600802c6206881040b40c401510300c40d9080301d01c0710b4809041e5801040341000060083d401600619440d0030b8085004070700d07000c5520948030400d2044d8020414020348450242c14020100085500304004004060200f5020071041340500903d03002a403900e00351603030090500000380340042942d0024149c58003c2590385003e50b0f002000840e01c9000900e0030315003590705100b17650140c2c5003070502080c0080000e4010a039001154001c400c0e081d00c21441c41016000c8403100c594800210307a8200040c4070315000304260780324412000703800160302600c5100084c0b074641c02e079100003c2c9461a0081010504003030250380014100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 916448156 1250 916446906 916446959
    0xc021201050f0609060301110c060601030612050303190615020a02010f090812031807080c0a09020403032304050301022b0b01020a030c0218040b090f060603120f0706060f 75
    0x4105060108450b00948014412000e03c40400c01da41c0e000c0d07002d00768000d400740b103445d44d034070a4584040d00c4000032030340140801d1800b00b001540d203a26268400220394000081d40c035607558000402c401c400004e401c001030703a58550021414104034091b0b550b00007201d40090040390744520006141e40c1c05002140e00b013100c03d66040090010029612143c200019907140d100c0e525149a4041400b03036100e5442e161044040015400101103044406080300f03880301d100d0300f0307120055401a03216512004002500c000480c040c2e41d000142c0b1140301c500030000c41c5180c0b030340c4c0d40300007400e98103c90030b80300280245c0361001c2e440d2090380c1d1140140c4003030340d4024411840c1400021303413141100e220280034031030005205021581ca0048a00b607068110415643c203040c2402d0281041d03804a6030180e007032041c108480b04090000401c00d00c1590024028101d001110010190700c0d0003c09040749004403e00c12140061014001c0d207010b406103d105909503860720b511040b121258000440e031045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 916449406 1250 916448156 916448161
    0x807030b120a0606080f0d0822150b0d031706180106030c1b0305040302280b040302330f07080a1809020306060405010c050a020d1203061e050409081204030c02120105 73
    0x90001ca42132103c087d5078200001142d55128000090112040124100c0e400c0c41c130030b0404002400c401c40d03420460750541003002c60100310611102408201018002c140e641d40405820742104840da03911060140c4019148840200f05e142c005030280c200c0f0000c0303070b102d02458440d2540100340001031040281140f10a45042e00e0207804c501c542e000c0680521000030f05404d012450380a13040364548445102c07130441e555214401c00980250108911a8021010740503440c031889040290f0340740c0321550031a4407180071101410b41d51110001c3e0074070b00801e01c003120101e18120050f01c185a040e480780d40c152151543c0e6600c0b4030000b038000e490104d206005000c51500d4200a4500741d030400e00349000e0030f0304503052140c0f80040c0094002e60201c002006a01003000c003407200701140101c0d803011701525440301a040541038042c0b641104405c440b02041066251036002600340343d0240c01c082d480c00300c1840548111980890f000e0740030600703004008003142800c604420071603000000030800e90 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 916450656 1250 916449406 916449433
    0x10906050906060f09100306111608030406060b130e0a0f0e07170604050d05031506220f1a130518010321020a030f02010b0402130e0708160807030b120a060608 70
    0x1b62018000504641d80c0c43d14034200d50803100f003c640b50a056280100c0d0b44100c6841c204600c1d40c011101180c0c0d0074104840081c0c072001c2081500c940404010200d014182452000074002c003000307003400e24807030721403444840041e510720540a400429401a040c064204006000100752412a05025500040030000030031030210f04195501002d25110750f40f0703140d0180b0540c01165842007140c0c41200001c181c04c00c0c0743c4100300400c68040c4100c034541000c2e13950f101710a0071240c03403044c0749134050b42ea0841404030780040010004110f0315400201115120310214225009034064144052010030051007800440080c01c0d00e025620080d08504030000d0400940f5107031864001428010903001e0711401500030f4000710001000900115251005002c0c01c13041002d09100f900c155040c15400f090403d4441c68080d41b0401c54591012540981284c0403142048000d03d0340040643d80c0c402c901860703503814410b02c130808a5400600d42840e01381440b5003100c850340e029045c294040039802c00307003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 916451906 1250 916450656 916450681
    0xd090605060d0b1605040504050a020a03050603030a09060c0204090605010602060121020a0524032403010b01020304061206030605190b0d02010e0409080906030a0e1b01051b010906050906060f09 85
    0x40411341041c1030100070411020303915406039070081030f07000d400d280c1000b482e041e00f540982100c400070795040c8041c2d1900001d06880340f041c1040d81700051510034041c440540240d0f038202c0744900c0680001107026507504d80701e085800a800c1080180c2080c00100a042d011682c841e140c0d2101458202c1c40c0c030040e50002c1c82d00c11071803143c1c41c001c43c0910300b0100c2c8141c0c07a90341b11402d0b414a0303c0e12952407410085c940c012845a140a09030f991140707040c0801c5040511801802c890182c00440c5400c1c241901940c03140c00c00420520f1154503008040700241190103142e00980da0100000844418004603905541e640589203009002812510300941c2e0300c00c150044011043e60b0001d401c28181c03d01c564144180550107030850700000038084492090f0340485907060b10340c800d941a81145450390170150340d45810082c0000c0b42440fa89620700b4040d014920001415400060342d10101ea4030b0100761882156107400b6900000c04004250400d0f141020004008a542e50300500d86001c0c0d2680 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 916453156 1250 916451906 916451911
    0x606040902010201090f051c020715030504050712030c030809060402030703021c0f081b0712231f050c0406020a0803090c03030403150b0402030c120901020d020d090605060d0b 77
    0x865611140c4a10959001707612043c6215082880030140c40704a050450392640603070300841c0114080104905c00510202d56201070742c440d1418810345070300d034603002c6024200c05001910360307000e03070400010307071480c4044d00a001c00d102c3d8230744003581c29850030090041e003001010700559030010010000141e40c0821a8410743e07504843e100d18400030310b0007c0040c0c81c5194401001174420039203030390034421003070041d105a521491091030101071140c0c1e042d03140c00c0701d8480c540d0641645241d140014401e800d00c03100314409100100f0701120a060b800d8500210304011415100702d403031645101003014010aa40304c0e510f91003135031a00d4641080296106039a42016040c90030200215540300c0041c000808007080090407240c803952641000000b1480c840166000c46240019009441c181802502d00c903040011113581080c201c0c444d0391354580c00041424070555400c01500c2c002a2141c800b402e001882c1000c005003907070052500e50102c98020b001c141c071440f02882040300165141c0210355 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 916454406 1250 916453156 916453159
    0xa020f0d0f1b03030b0307060e10030c140a0302190e011106061c0c0b0a081e06090a090606090e1f110f070c032915010207140f06071101120605030606 66
    0x2d21110781d082c2240107142d444406603060040d2203002600c140c0c4200740021010701102c288a8481440030b01f9001c07075082c85001d002081c00c003c03171a0920703c464005003d00030007030b04015103040d04c09034004010500d0700c89020041102c002c4a0b06480d64404034041d202e103c81d070020a030a042c41c0000071f00f4050408080100041040022004c0042c080c40400003840510241500c400c2c442c24043c00021003114601c80841c0061002c01803d0171448d281401203c01074600109500d50104001c050070030b441d82500c134903894180c0000d4a52480c170440e00d154001c00040c2c411600b034106899500800c1208000c1c80703504060510413008008812224400765007180a40d403070303005203031881c0d8040242d031000d030100442c000303040b840220f2503008041c2e14940d400c0035a40c0d591001c500b10050b484c00d046150040c5d002917018880343c6164118a520b140004009003210101a40094815407101108540d2841092030041c80b558100040c041000a14002840401e0402c00404d548440040006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 916455656 1250 916454406 916454447
    0x1d1b0702010e0301060807240e09060f0307062003030f01090e0a060501060c06052208090114030a230c0708300603060a02070507030f0302070b0a020f0d0f 68
    0x540840e0700940e60702c007100b000074000303000365a5100d00a9840c0e61051080103045400642480f0b0000c2030055603080c403829035100c8540c92907409003800740141c4010310311070700046500c6002e00955020070641000b800641c0e10600d804030107000810f0780b4000c1d10b5035031490b13910610901a9141c48480d1040c113582542c1c80020b054500c48140c02d00d41611501c025000514080001c035000b5800a81d4041080c0200414421910f0b92049400c1d503030a103296103501d0306c0c01c1c21244000101050010722400d44145012024a007401c8100d4042d940280c40070503840c0d9880025200d00e480044a0399030308503000d070000c4881c1ca460020070b5018441d00100500d03420380002d1008a07050280915500c14086403244240d00295a0852480b084181c5030703076100703118441c0040c1d4026100e00844691a500c80054240c8034910f40c4c403030449203100c802c22819801b03000c4010030000400800381401c9602c5600804160002c0303043e40c1d040c4059118920100098445000c1c041078000d201442402c4e001c1207078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 916456906 1250 916455656 916455667
    0x9030b090a0b0702070f0b19140904021621020303070807021e0a15022b0204051518030601031a10091806060e150d031b0b011d1b 57
    0x35141481003004000340403100c00b07014800c801d030307001402d0401d9a003095001484107458890205043c00b8550442d41c1c9805100c0000c81500e00c41d80d6494400303400c0b800725500b09030040300000d080c0e81105c0c10401001742051190b0007448135a40205c3c00c0c40c00010b90600001c400080004c0d00c9100041a460510000710003042000703108104c110b141c0d02601480044800000940b6034440c18203400a5074440c41002e5000841c103401d10844000d24640b02c4000921150000c00102100c030b00c500c072800e455401e00002406455401d81c1c1400854120042c80d941d0a1103403105031100100311609000764004801400018520710070a084070301311601410640e82c9100b04070b412164641c001c228402c0c14820103080002c4c1d5055002240c0d0300c140c0b03060121540380d54000c000010101e560008100a501802600c0d080c01301c07003100f40601a14144091504044407544404500c0d4011580000b4085c0100300b5140e09500c005d071040088010310483e0f08100092895a408030310400b282d078000003c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 916458156 1250 916456906 916456921
    0x305070815131208041e03120e010b0306161803030305040b01120f151b08070f030207080a18090501120317070c03080c0702181b0c03030a1508011416030c09030b 71
    0x11903c040441b060315403002200900d0004c107007001d109600403031103081c0401d2800f03500040c004d556001d1000750040429580301c9410250305c00c00f500340344003845000141030300032845036021751010398000e45000c540c0341054603100c5103450050b88441c251102d603041000000310541210905690007a031030668228a0003005002411f001868415055614078602900764229801c00d118801e1902c503500256902c2d0025003d034450030000404402040080700c210130b010720040852504001800d811042c1ca400019007120001e0708032009041d0703401509420181d11020300714041401210708a071030b043c0b401d0043c103110a125802002d2000b80b20008120f4654901900e140c035400404640c4d00c0d52603070000c4142d103d4281e0b000c411398940b10514658041040c000c481c42104102c00441c69039584080178401049005041da1030217084440014032480c00b40101602010840714482c013a042840c0ca05841c1009c1000e02c4040c50305151885400680080c002800c89800c10b0494035566aaa04d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 916459406 1250 916458156 916458173
    0x14090105100b040f03030305190c0c0201081302090105060726120c04060e21010c1e140a050913020703030e0714060a1115040c031401050f0a0b0406030507081513120804 74
    0x3d0170344020b80cac41d05001e603c079254444103d10102c6d000ba01c591450740c6036441388501c5c124880700c0c042d401010480040140c1d0a14000034032159010b0049801d07004101c0c010700001c1b41d00c1031a88088644007140b0302c142d1039400c482c0c00e600b04c1488680140352926200001e0010002c0b840d01c0c038440c10f880b030700714000c0f0071b030a800012000284100070080070b5020880a03102c8201025807440725441a94041c03041d50003012070240b01c0244c0e840c11404e20f1038800c4d00300d4139075010181c2c082d0012103401d038980349032401e4005002c41d90700c01d84002c110703560b450811902e0300405900008080d17402e4801d42c4402d40f1040e04542483c441440c0100c2003541007003229150949800544007054132000030801488143d00700d15054902c41c81c1c1c640020072107074014a00340e4000380c9059401001100c0800c1d0800c000c0e40c4a030040032006000400c90640d2926258102003441d4803221071a00070900307120010780500b9400f5070010b03450002620007490746e02c4e16825520402c0001041c455a000401c2c103200b00301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 916460656 1250 916459406 916459441
    0x3030b0a0317070c09050103020105091e0306070906030c0810050607110a0f0305070b0f030f1f0f0f0602120a03050c0f03010303120509210a0314090105100b040f03030305 75
    0x940141c41c260a9142c220748290300240069904080d0980701181800450041c6812213405030345c0c650404c03115404009551201d64800302d1034001452220030039880521559110b008a51111000c441c036061024094030400201882000140820403e44100e040100003c1e0360054030007a4848540b49440071000010b503403030b5988045050800608441d4100080c4183c1c1d1050007611450340d9518100300d0303a4028002012040d06080c03001503c3e120b0180101d40d070240034604040c031412484a0305c0381d0320711102c0e040082d40400308030040c00341803411140c04c0002e00d5244020540c2203c1d00d80500414018070f08078108254071540810a42e0440c581074584000d1310544155503941e680c81c010b070a46941c1500300540c0c0d81040d0001e0115200420020540800d003250b980076074200040450007a0300c00e0612030145a9685110207010034a041158407449c0400c000140f40d00b0147e8000e135200c886907020b004003030420001030011940c0c0100755003c0342e9060501007100e48179461402e04203240d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 916461906 1250 916460656 916460663
    0x20f15071403100f0b07081c0609020a020d030c05070b2205030d022d0d09080c0a0b091002040b0406081e0916090b10080402060408160e0a1803030b0a03 67
    0x202c14008100100c1001c0390449860480d0b8150f5165645c0718200c0c40c2c059610090700d0038005001a00303c40b00e8175801444100d502d1030000a145485900c2c1c0c8007240c110b0074807600103030b0100e1b02c54a2a96050303c950201c1481d136041903414000181d581d01410f420007001c5c09008040c00c1a05002d54010309101003000d40c0c008280ca890f44d032803550b00e0000303401c1202d204c0d49241d00d00c0f040550321310320b144a454003107018151080c076040d4082c0704507010f481d05c01004c40c2c150100304100562004248600800d180c41105108042e04150588074039000c0c0f403a0102010758070400c0304001d20200c4600f21402c4504504110318030303644184860359843e101e284440d07851400f203001c02c445000302040503050340030358544d9440d1503038079501e0240882d01c800c0540c503088403107048544a41e600803003caa504c41d1004207254502601d42d07920038103246d00390700c40345585600c0402c103004c8404080350b401d5120301030380e60070080f11014005480c01200c0c442e102a05040c2d81c0c03034201c0e10390380387e1001150140d0f40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 916463156 1250 916461906 916461947
    0x20c0d030b0f030f0a061406010c0f0f02040204090c021b092404020f120703140604110408151603050601090b0708130807090f06050a05040b0d05240601020f1507 71
    0x100104c500341c0754030303a4200842d00740d0f241422000a865450443c81d0091106030f43d803040c242c88517621003c800304160307020f44003081d445c0d02140040e46c450004001030b28130b5000c0802d02c801c40d454042d250580700c5c4820213448031000d144003020340f10082c42540c896009400003c3c5628684000400c0d10755104a082d0828000509d100e0030425200c01454011a4104400500d550b42a01201240c00820320b00308100c803481c0202e8014500303508403000130b01404002a1906035038107089494640314000c2204030906404c2000400d81c041c80151202e0381040c14180224908140000c1c08100c881c0156800fa010210340c0ca41840b02010a588c011600c1b240055001c1d52100d5150b03907036903054490181000c0c02d094042d08006083d0080c102118001341240c1c0003641800104000340035042c0c207142c0c00c040c0700e614040c04540b013046450900da00564048220740216806090203803001071415041d54004038600040d0107000488800d010a05030b085c1c4070548804030111010f00c010600401040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 916464406 1250 916463156 916463173
    0xe01030803371407080402131a120708060c030c041503090204020a020a120207211a0106170606040e15040209030f0601090f0c0504090e030712031b03020c0d030b0f03 73
    0x201540545043c0840c02c0c0350192940c1c400c001224540f400b298004e400c4140c0046804c10f060701d54025100311000d401c0704100c105400740120f90000c40e08480720f92540e201c0c000422a00d00144041500072180c0b0342000d15620740b04000c2c4100d44076a1061061a2601010801c540f074400d0340903d02213540100155070766001884025900c2c01d186100783c954003070111805100d5400001c100c0c0890f036051a4400080d080748014002c40c00c0a108240c0310381405500c0701c05001c4e843c0034514041c210300d8980d118a403005116030000c282000300828016441000700b4081581d212034166442076410403031841c070362403440105001e4018900a90380610401c000800801404924181a103c1e40c010400c0f84851082403001503682c0f01c00c2a00101e8002c1206000303210b40780d00010318900b40d00d403c90b4078000e05660f6004100010f003049900203a907030706160f9181351180103080c040d01d410f850154103001038410b0558498090800e413070305041da110140381d0325440b083c500c109c03804c0c4014156441c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 916465656 1250 916464406 916464511
    0x80a1101141e06041e0b13020307050d050723070606030b010807090f0c14030a091707110901051e0a030503180a06080c092701030c06090e01030803 65
    0x7544266501d8030b51000000051600d0070700d0b00c6075801d070782e454141e50386422020b002403000500b030340500c181d00003162110120014515000843c02800d4694401d40da8600407130528003101c001070714180400406a0303004407100e0303812074040c0d450b00b98401101d550340c2052601301c0c02040303250700c01404004a2070001030301030800710b80f2008030b0f402c6003000e00062032066031085c1100c00017800140800d8900d002d042c80c1440070405998007215511001a18501a8807801310310641905d100800c500c0000d000800c01c5070005040c1601c6006450308243c40d41481c0010350b41800044030b120035000b4110822070b0a95800c0b05d0b100013940c002096a0707a40912046101c021107060814a000e0a661032002032241c0c4901045481803601075903503400e201c00b8808001c0c14401c00c4002030b048840c00d0920b2803031440000605030086114003d1754220031314000d00a08880303025481424410144401040440c00be40102ca9101001540e20b81c80540b103410340300d040082c1540620750300e00144000c0202da = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 916466906 1250 916465656 916465681
    0x313060e012703030503061201020d0b100c11090703020708031501320f04090c0e190f030813120606031109091509072d12080a110114 59
    0x28100a0741c91401012840308000400d01e020580c2c0e00403509107031010400300344124051500020020700035610000d000c03043e00c1c20b80e00080c40401100da1b0ba0741441c0f0052a03d0b2a19004a200c1c3d814844000c5c050b9844100c400c00240200318040e6120b1400110310b24400d03411103468039804480c00391641804003040500e4032800a20034082500d840800108001040b07503a114407842c8540411f4291500c08480d9280d000070071055400c1c8001c2c480440c40ba80d2600810f144e504159458940c0103111300308004084480d8040c03a1078201000c0b505009104512594074243c0c2c2c0c0240e080c078ed0742c0c048282d50410140042d030107070903220203417081d8108008403074100c903040301e028202030b40ca103c00303c40800c500741c8425506203001e544004521100540020f60311644176900c00140e0300210355510110010290100658902c58403084281c01505049038200024004480074000032942d82d40d690700e054420407a5600c18441035502c0e42801da103007508000c0340d4405285294400d8103106450151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 916468156 1250 916466906 916466927
    0x2060108010605010207050319030c0b1311011b030e0a0306060605130b0a080423010203090a0b090f0c060d0b03011e0e061909080c0303040506071403100611031306 72
    0x80c41d50030310000044562001606005459004002d4407002c5070043c10942e03032019002c411014446182c590901003030030390115601c581c00c42c0b01240c10401003807620403003c5c020040650b051126000010000d4503190040c40d100701d0381400c107680940c0d481c078001440600c041d40300800c82d6060400c00b0400551000260126102c00d841c858900c40d11414100d0140c045d50811a0000e21420300140224406840c400f000c400782241c0318181c0c211006c500c43c26070344116100100355102e0070b055420806080b41d69980701c0004000f901b42d15240c990000d44642d0f00346040d510400c03000c500d9135040c1e03003e80c0c0b04944106c40100204210f19505c065517981044260921008a14001c4012650000400c90318800d43d52401d400341c1d0021500980c1d1700420b8200030030b039113004060040b40c04c40c01d003c000070b502446c020f0380244064603150300d004100003c4100c1c81200ba100500a2248690040e01040203540850904024843c001c085480c50350080c420f0701040000b4031900010166048840140d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 916469406 1250 916468156 916468169
    0xa1115270709361b080c09060103090b010f170a0213050403090e040b040c09140610030e061807060f170402220e0c060403030e040b0613080318010e0f091f0303020601 73
    0x640002c0e01e680d001460681d180318505151b00444d03c05411458003e43d4554030603014100050140841d840c0c42402c050b098028812040d55180180202d40c007004e0300041e031102010003002d001c4203607400714080c020b105030900803e913201c2c004a0100b600a0114501400034010050b14600c1d1074182070b1800101a84c1c02d54800720080d40c041907012050050310048500700d00c0c0150300f9241e52042c84540c5022000850405513120480e8012102c1440704a000742e0910042002d604007400303040e400c101c61070b4440014401e00c9000d400c0515008a000704c1581c0e440012600c003543c0d01c0c004100440700700d10148540c40030501e01b964666007158001a06200e49404072083c1c04810320600c0023074440d90001a000c00d070907040c5c4d010103203080c0e0009a080000a4100b074203080400da0b81e000d00700c01c10380080c095508080f600d209088160701619800e02000d02e0203c00080b494404241081d0f0807000c003038025000440015400c4100c030400589110f4030447d41e0700307440c0d96418004d480c0c2c0020300412 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 916470656 1250 916469406 916469423
    0x60c110d0807170405060402120f030f1b0705330403060c1e0903170d020307050d0510120f050a02032a09040302030f0a111527070936 59
    0xa0050743c003104a041c49280d1140082c0f10325115602000740f441181100503a00384030b890708515242d80c0c24400342c000c0544030b14085458a10100003100103100351954800c0c603500282040040740d0710b51ba4044480c480d01402c1c8071801c0d224031a00c14400c114200801c0d00284001000410070050f9880b22503062165a562250f03109240002c140c50b4048182d4000042e54824051020030350f170380d4100303680210106583d4a8003c80440c18402c0c0d810444141c008a000440e1ba07010260943c01005c1d8441c4207038022441007070401036140301c1e10f9903035070025108040d0201920100311341081a94940342c1c004046031810b10302103005000c40300300f001617040747c50350341458800345060603004d05008980c56000b0311300382004030362019156003009a0b0103040007180300113000812001c0c010003000700a81e4090710410b180c1800c20054900c0e20f11350700342c4445018004108075203030208070241525880c0c1404619a00a81600002d812b4501d0034244800e46c004100c8142000c1f0124007400d2901c101010b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 916471906 1250 916470656 916470677
    0x6081c0e0a0e0a18210909050108031603050702030115050f01030b031002090d080d0c030506091905090c12280503180612070e040e1207060c110d0807 66
    0xd000000300300340318641040c100389011400d048507a4102280900202c1003008002135070351103d00c0012003880c0100ba80300c07001005402501c0d40102d1000140003c0e50040c0201d500d0520f002d0303524410340680f50b0b03100311541c1c3d141040620660807920941c4c0c0081c001c1c0007440522401c60311040082c454580309a5800e4000d89407035010b03003c2d0707600c4048024040c20a02c2c0b4060032800296001c4e51010380d001c1f4038071103180002044007001d0301429184090001d480000d00300090225200500000d00c03801411040181c007501290103400c0c903007551200410305803030342c004561408901c04c2e007003580880b0306c0034410300c41c038800260000306104484071215059100d0900b048041403885014000f07030410044000c44651448248480c00d0005d86003501d0005040c844500c0e550050b2540c8000622800001d01180741c03070b00036031402004103c05003a80100165004045100b407400c000c0420340c440030b404d14480d016102e00c141c03903c0035406440700349100c40c00082400d4011110040802c1d10f5651 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 916473156 1250 916471906 916471909
    0x290a0c120e03180f0901080102030f07030605090412050d0c27260c040f140f0108030406082502060f011409010b1602060c0f121305090a06081c0e 64
    0x54a09a40c4603001940c0760829410a5010f6103800c016180e40140d061081e60304d15441d03551119008080802c001a1241429080c4049288000c1c1c102c404042c201a01803106030f6031000c4403034005902920700003950000041c241c0d41c50081211089040b071414542c8010182c025910800c0c45102c941c41d0341c049100c070303e50785a002480307000e81120301d0702582c0c0c607030041800040220b0940301880119254100c4980c0020305803003882e070104616903140c1c0040e110740300042030344035007041003246242000d6060550f800d64900a40c03140004000c1c42c100451342d11f10300709818080d03c2c49202403010300880c5da440065502c10051303071195040041c007000001d19038808001c24038132400040c4802d07281c0e4600141c0042941046c1e03000400107c00704040c00040c0d49800050000c0c502c0b4101400d0303401401d5400c5810a6842041d66080200c10407a050101030301901100075140100c5210203d034841c8481c40c40101515001566644150500d1182020716141d11021000c890303500c0c00c212200200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 916474406 1250 916473156 916473161
    0x5090a1505030103120318110f031c05130b0d05100f0303020703080306130614150306100c17030a060905090a0b0c090d02222403290a0c12 61
    0x682400155042c001070001480405400804030388078640851211420f84aa4160904050046508004010503a0100e0510f42108401c09004401800582060310b2490004111112280303042043c0064002e004403890700140020b132010411054a90001d940c400008100680d286001c001d000400059000e2035038004005407949540645903652456a84484a400242096501c032091244642201040b846450020080c04c100d504c054488141070154007907151000c0ca03520ba40c10400c010035034880e03813100c0300345880f58903000001c2c40f001c2c20054146c0c0c1054426080a00c400030503c2120049500204280c0c0e602402c10040764031102401541c442611a004140c280598005612903107004c001e0007100703a002c1c0101c0c40c540380035800103001d1810202e1410f01e502e41c01c8502100c4104510a408900500c041050000144d0000038015800184002020096501076110f20701c910f0000b00e0416501055215002c1d040c842206400f902d29a031110b40000c1059040300d0302c222950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 916475656 1250 916474406 916474439
    0xa0906060305060a0605030610181404060b100528170717060604051e0109051c110121021c05090a12050406050a08060301180317010b0403080f03060103150605090a 72
    0x500030040450ac1d00c1c1e4070030b200724803103120078040c16070f28049042c250880c4007505200d980701e201c0000741c42420310b0800c001f0340100c004950070030a080c0152407031070b4118195502d800d1284035000c00c40d8071415800300c484800c044c030780c0902c019002c0e050010203034006081201155001700300e0b18180d80c40001f0711841e80500e04c0f81c82d03404544070f00e07034407401c110101112810040614000221030746900200c0c10700c2400f01c0441086d80c070b000c843d5209021005080c1d0343c624a0920342030300c200c0f680c4070100c4c0b8400040d501651007164002034905900c103240c4004c01400304040c00510680c074000185035100c10308004161842c000c45d00001c1c01d22841354040f207003520295220340d0304243e50440b044410b180d000706056003540da68003140e4071250811a40200441c03180c2d540041504512811080034a010b1b0710260410200784414400941a0810b50b490190740956450300d035a160b4004802601c05407003150030b000e0f00300c0c40110b0b20961100080c10222001d44403154803580d280103924000950 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 916476906 1250 916475656 916475671
    0x501020118110117090703031b08091e040f1d0c0a14060714030912010e0601030f06182105040e010e09030d1a210a0b0a0906060305060a06050306 64
    0x3880c0c00c000015420712940b4603580010314040e15014640c49070822800010f40340c43c5440d074080c00f010401c051b440501c590030161685031b0100c601041d07940d808003501500c150300d8401c10865031640c0b0301ea400502d0030060b000b0024001d100240941851000406017807410544170b40e841c1400589145000a044181b55006014001c3d0b8605d0a0449d030142840c0c942070662145080010001082030590310b9070880001744091661500180c0402455070310456405035540d06004403c2844100030825504403500701c5040e29a642c0d41e850000c0042199028420402d0015540c00090009841d03a09010359074250760107404200b00c480070b9a290044d4418111641001c000601c11300c004900d130190071026250032242401d0b0012590015150858175080211003035001e00c0046243c1020f5107941e0b03c500010544043c102c0115140e229030150340003a0220403040041000c00301c4e0f50b4403e030f4016030003d03020440c60f5220310b40291500801c0d03c10300ca4036820310001041508d40401d000e8040d01d03d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 916478156 1250 916476906 916476941
    0x9180a200d021f0207051e03010b03070e0703020906072003010513020f061803071203080604050411151605010b4b120618031c090203030717030405010605010201 71
    0x203007044001e883c03003420440450242d10400100c80e00c41d010521054100d00034042a4000390805050031143c3d6150010721a41c0f104208000444c984a10503800c4100c40c50050f03580d44c107400c0451118403a1241c0108600da41d00b0403040e2010303040409100c80c0700200c000b4009515101041d001d80c4007e1003019511000301d0351040010300c0c0c008018050940c2e42000ea1b0914240540043c0c01c00b00154080001d018840d000d480070180e103c17008681c08402110200300608194546183d004040d18100e40074160020754944445001e109079080c00302c09818140442190b440c0142c06040001507460003042c00051a000105401c0c0341c103044081d110b64240c80001001c03010300001c68004006000b41c103180b03124500c60f511601220104006004c00910203800e02c8072032034041c1c002c2c0601000c0b69400902000c070f404100030b14040781002d0995004504000d0034000a41035200b580f900510b00a8450109820045242e0146110306e00400080000580d01c3c40103a098034400c4400c003401a6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 916479406 1250 916478156 916478179
    0x20c0907025b06170c15030f1e07030213080a02090c0d0608031315080708130203011e05012c0c07150e160812070209180a200d02 57
    0x81840e032000441500d0a007080240e1100310403682d080715659003000d681c400c43d4144500280c202080b600824000c16560101030780402c06445249020141c0400800350032400800c6090414401c6540c035107950003204042ca0404400c0036009500c10008103a41d0718200c6800208884c000c141c0c2c1103580e030003500c1080965035003005030010b984401d80d0707000040c1d40d500022801e800c08101900150444031030040303005040942180034030359a5211041000440c40030008015804880542c1100c0381d602440d501c4541ca01c006400340070308294921900e1310352000869129920341105048030b08580e00451010752048842c20110040d401c408030900001c0041100b81401070007c140c4140075000400d61085500c5170b220903542d103440d0300441603000034508a400c000c2c2203584002089220010112104050000c44090288480107445104080c00044196002c484025498801c1109a0b43d50740210f14202490009148001020040c14a100a50ad08181160000c259001002c580c00780 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 916480656 1250 916479406 916479523
    0xc0315010e0c0c010c0e0a0527130b101409071b06020708031f1e09050709030b07050a120b0f0d0302030d0f0209031006030308070f020c090702 63
    0x858080c00860b51500100f00444009400b88070308008401c040e0f8418540c00d0100741007102450841d04001d1103004003984907984440000508400260501d000541959901d0349406040d0b24034a40030704121159420400e04440000c03410080e10411080b50700b003401e01c0c200348609410304940107008641002460803600e01070b074030100d500501c1003e000d4a0680c1c95a00c81c00f140c4c200b03850b00910403813402e0000d05602c1c2a02000300240c2014601150f000081c19109200c034081d52040c502c0043d078442c003144049200c4e0742400040d5410031400c40090502100040c01d55002c030b40000c00042500d011201000420b020741551004018912440806030300c003041441c46d1066001c40030340c481084a12180c00c0c40e4010000887c480c02c00c01a181c00f82c0f80141402c0081030440220210303c0d00c0340c18070001c0d401106249d00100c19140200880c0600c0102741d1501e41340303003c1c040d03001080b8010003000c60360001701d00d0245800071000e21850310621624074191072800b0b0b807400409501c40b2088400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 916481906 1250 916480656 916480679
    0x2210705062514160605070206060301180204021308030f12090c090c032701090201120912080c2a0f0c0604151b06020a0801081504080c0c030f010e0c031501 69
    0x2141c640010f038074074100a0401303080c8014103000302110380da5259000c2016003901030003001d91105058009000520790300e0140d2101e0f80014600030311079175000c605050b11804c03400761031001c0c191100403a5034880c44c00400740c000740c200701300d0b900400520701c0005041500c0801d0b020540240500f0803a160740f10411031011a42008115060144031141403d01742c0c84942c51550344040888000a084012800014880110002c0030028503003401e100c00001040101032132607140700307403a00340455119124003e485120300340e0f820581d40a200e0340e06c1d060310b10034050f81c1c2556580741d040300d003101100054151101e507644101e961000062200b00301d49043c03240e6420001e04c0c1ca14200c00000c40400901040703850102c0c0503140e0a9011580d0000b064100002d6030140400100504400c18440300c3c640d100003004100514000001c109502d80382000c022401444000030251030203411801c02260080c503806400a030207100c2d21500304909d0030f000c41c4c00240d80c4100420400300d0ba0034540603885 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 916483156 1250 916481906 916481927
    0x60f0306060702090709061709060c1b030304080a0e030607020c061305030604110102072301050703050f120610032007030207051203030a05070e130c022107050625 72
    0x100301c1010031030040181e640b60b00f1284a0344194803180c2d086410640024681c0c80851454103144a0083c2803003200d04000030703a039500004014545503507489100e910307021012145141442c610011090001f0003c00074081c12200d0125500d414003144e005040580c0d0344400d41c0c2d5800075802047d4081514144035008021807000d085040782d0f0b81d90703590003191501000b2030b010340388280c1d42c0004010f81d69043c091080184500100b0407099218840c1d41c02884080740402414800002903260405018030140d030071113a0b00030001034440b560740c0b83c1591001401c4900e68410f00c10425110760680c02441801e42c06070189100d56001d108010154003554800c10041c2c003035218003080001e05a40d02082e0040981a005c00b55071242441c41086050380e2000d03203a14103201750340401500c1a16482500799403101016408038070510088070603402d00045010b1f0340e0581d03003107112507030340c42d021000102640c40c858002c40700243d0300d00e448615802c08580050500c8600c00e80a003002d140310704d05161 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 916484406 1250 916483156 916483159
    0xf01090311010f1b0f021302070b1609031502030402210304060324060203070b0a11070b1023010206100e04020907030216060902030607020c150d020f0a03061a09060f0306 75
    0x207907039041c0d551090f0307101241d80101c582103003017041d0388110301700792a0001c0b50722941c00095007045801e99450903661002080d1059000844010700225445165080011f503045651103581d0751240012102a41c01190244d0203585451528550001010716a403610648507000e10b003030a09000c0c084020b8140e02d00c3d00c100c907812980c201d131654000040300c000102016001181d03242c00754644480901002850166420301d000241c071861759111040380c0c2d005601240040140c0d071030300c0741a44c1c1c1d007540790010106031100d80205804900b020005004d80312003602101c410790b4401c110110420500d00076125104074900c042001030410012298002c5d1580c00c0c09400e00c0c09001c0c030440004001c140035035400e501e5070f00000644c2014004103030403480d244040c00e0642a000040340d2480745c856201942c02d200000d10a1221545a0641e15000c40d50129150381c1c1041c40c10041c0503101502844401070001c05030f428102c818001100d41c0c9000240010b402c003810051072500035000103000c4d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 916485656 1250 916484406 916484417
    0x35031201121110021c051b0102031008010b0a03020103050402040f1b17091213030807210f0807081512160b1305013c02120901020a0f02031507020c0f01090311010f 72
    0x1a000780b5201600f10903a1f400c0700011f88030701e807000d0403440070100d039408100143d24103130f40c3e1b1590b80c40d20003090058a40a007004182030700c0c0c0c1e1001c1070007024081c0714007000c2442c0582c10150b031142c08104025408055903000400f041d449203400030090240e420441c103030310180400c1040403000015007a078000400b03c00c2e0203a950b98440c020140c2c0204000c413140c0110b4400c0c3e41e43c44000724041c025080b4649001000810741c0380780070b4040c080282c604424031400e04002401800801060705100d80d000c2d006404003044001d00700d984440b085102032011040324008a081d60720001910300c170609a204030301000d443c1a0042d650b80781c09503a45618403690703075441c90316181010203000701074049046032681d520114600034108040440300034207140040108500d00daa0021300c40d5051900402c0788802441380d03200017850300b035031146a1036810f05240d0070080324503000303c1c80d400d0800d8140e40c00d8080e0b1011900441d5050880c3c04000c1c9080a98444030b0074a51240601e15040006400d11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 916486906 1250 916485656 916485667
    0x9050d02100918020c070e060102030304030c060608120306090106030c0813031b080a0306050102071d0a0603050109380a050702010905120c010635031201121110021c05 74
    0x510304040f03401c14190f841140c0000348104008000c0001500070030f4403039068449410460300007511f81c84080e00c05020020141d5001040c040f055000c98020240302e0112680c403030b10400e01c4051900b046440903c61440301000250903406030203901c040c61940da0b038417069540c600c1c180304070082c03a041c801d808000f40c00042001c004640a0302005050090000d00d441c0d40413041c000781074402503048181150840141000031045000128101c1c107105628181c4544c1e4281c0980014819907002810640c2410244411b2195101c81b8109900710180c24030600002c450700d4050001894280700605c01c0c203540003c92030060355100c150484e240d4400403d546246448161508103001150030501e140003810741d00c015400d114000061800c030300f00c18009940b400f44412200c004610f0100c2c103c1d01081c80c1d180c0100c00b0b05c101e461800704800400c000303585401d480a8800c440600880380181c960305000840e01c1c0c01c0c084400850a142d0040408245208842186c04002c48108040c00800d008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 916488156 1250 916486906 916486919
    0x20a06180815011e0807090b0102010e0312040b090a0209070e0f0d0c2105030702011b0606030804140909070501030b03030d050f060f0a03080a08100305101b09050d021009 75
    0xea003188201030301c1d041c0042d410514411381d8841c403144068943c00291204200c510703070105807402100d1216800040b07030021000103070b0242664141001d4103000c0081d040d04040542e40c80c01c0e0090b4016051004141d903401d50559407078036100c00182d8070881c0a030001c2d074031500c121144035140301c010709403c480907242c401050320104803500440740f2042685080c8026400000d100c110f15401d031141003c414803d480745901c07407140c504040e0402503458011013140882c0c08128194903400101008019a6801d00c9211070300203000308c103a08004010f05058518190098034000ca900750098a6030034541001900207100b0300c01082d130140414410000d00114a220341c500c00c3d03c00e01d18244051070300d80c0800960700c002c131500912601421f08180045403d610940b6803158050800c2c40d801e803500030304204107142d2584024800e1142600d0b02402d40c44a0b04116400c401300c1ca0400314024550390260f6041c1e11a001300d0760819100c010f407601524101a100c40311501505000e000940c4828 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 916489406 1250 916488156 916488163
    0xf1d0d0c03080d0b090907050d080703030b03070f030b130b0a0506121f11040308070605060301110d0c0212031b072d0507050603070f03200a030903030b0d020a061808 73
    0x40d4081c001d59138101c03154041c10103031041580080c014003c0d000c900d0800000910450301500050280d05001c104542054000e901103022850000d044034a21991044110b03659019400700712100758100340819164007160342c1600f82d2a0f4048107900240c2d032001134841c0209001404507600401c000f40008a0980c01e05c014030415000c45080aa402080c2d0030b0201901e074002500b00d4102c00400080000c01d4110382031701ea82c1076000703034046426180c403030009000d40a50035541d040041d002800464841c0a80e00c42e1882055a4095071540800ca048180c50b40c00103c4230365020803c3d508080351080c50200040c60301d01c0c8915a000d51108408061610104085402d01030041e00c6800c80c4042c0501081440d0050404443c01c41c42c519101c02c0c014032003072207104900149502e44403107490803405618200440b01d82144569254405804014041c069100064008c00d02d003401d94451409c1210043c0344440d0041c1104203c02e10740b140c2120070346041c040480c01c1e40250b25002c60004000d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 916490656 1250 916489406 916489417
    0x1a040b1303150e070e0402030604020d14122107020c06071e121202070302150711011a040b060f0f030711030d090201031a090117010f110a0f1d0d0c0308 67
    0x101c0c4001810f5508a81c010b1800702c0340e400c071451032415041004016500040c8903580a0b80c151810f071b0030402280fa121070002801100c60102d8000c41c440d0b160480030302005070442400045543d4940180402e980c8081c103001d465030700041c2c2200b09941048d0820400901c4150300c46c0c0c2d01a490007002a04400304403004280c21140f0041e02090300134415440540140c02c180c5a103401c43c5030042c9564042c1d907600c078110241003400105000604141e0113203025141c001d081c18001d00c4480c5d40112441e02d85000300c414184210b140118020aa08040b42a00c8a20907407400c0949031000c17045400b4030035000104113004205800d10110001581403015000012148030081001c110610014040d03455002e00681c021494040d5002180d94148105045a10140540403014103c40c41135014200316400c901d24a030034402d1090300c03c0407000081c55410025640c1072460104283d0899071131b4480300c2c4180c160386d2070800000389850300240b0028203034450f0420302d214980c2e0f0303035880880c0c0c1c020f03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 916491906 1250 916490656 916490693
    0x5090c0303370c06090c150e0a06091a091f08060a050d08120c0c07080c091609140604031205031b030601090303030f0609090f05071a040b1303 63
    0x1004460910104020a0b042050400025a1005081d200c00801c4074403d80009041c4a8981905030240032070124001d01410718501904001030280d00003601182a014a083c000c9042d40c50006a441c8200703059410303258445443e07060020b481d91403000d00d030001141582e01000000c0024502c615140d62000041110345459210749800b2081100140040c2e00c658040c10000d03e1090001c2c041404403403a44840c82c41aa4494030fa8142581290041c0c1451412a120304078011440e0040000d0b00d0f40d814070100c80e6000b02c3e0352101c3c40e103401501d803c038205021400117070382405400c6008031000e10007000035144d40d00785540d03030322a6075812040000c448007254002081c0301107801c01c56010703500c006012a00074558108000001c142000c584405010140ea842918444100c01e42207600200101c0b0007d10501c40c150520f00c00d0340710807c0d0100c865100304040060002d01c0196060704000032003410030f08061a080f20074003594840e00c2010415400c0c2140400000c00c031001001040d2034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 916493156 1250 916491906 916491937
    0x60b0306130519080a030e070509150f0f0109210206040609060f0309080d1e0c02070806180d0c0f060606020c04060506044208040b220605090c0303 65
    0x218100103042100c09540a088200c0011600c0f0201ea190411a580e4414074600010100103030030805007802c1e01600800c3e0b01552600a0242002c1e0904074100c55280032030b80f0344128152481004800c0c51400120303804a01d00d060100892b1000b410440020f103c10f8848a04075580369001415503401742c1c01c00c60220300303010402d2140c2980001c0d06010343c0c0d458102007060b0952070716194004d0050f00c00c0030540c1034460001000320340c815600d441c4280c0032041c003485032800c0404082d4a403101401035403d940301d080b00181490700708001071056414164060f00d882c116030a000c4a10300d42c0524142c5601c4001c40341100060030341d1194000a248a50281600c10054010042591760b41c0c1c0c45640b203954203001c00d00c5601050302e01400701c207011505510f20058203500030006194008190501c0da41a160320640c11500720141e135102d01c0c46030802c0c217a941d0b601d164201c0c0c00981d4142d500540c0361005941c20025905a1001e07030000d41603411200b00e4041e01001a20795840048420340004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 916494406 1250 916493156 916493191
    0x1507020307060e03070510020a02011d06090c0a0f15050f0d0501150c080d0507020f0601080105010603140403020d211107050f01020306010c060b130501090504150c050a0804060b0306 80
    0x6018440c0043c04050701000e5403601d20f0a4582e10740d100c00304140d500e1825030004100d41814001d5109403030008241c01c01120100d502d20207107440b044100c659070548d0150030003400701860420605c01c1a10040c1c1084000c0e2420440044240d02d08048484203201c410880c035125040c840d409080c4d800e40102000c1600e42c100b80900c1d0300004030364220014423403c500420f000031500003e8801580d0b00303540c0041c0c1c542d2200342c100d01d0200090550096401008008a40c05006400841c16180c4503101070200c04410700b100401c6c04d4080f100640181c12810484410920070240344802c28038055405107040c2d0a807401100722440300154011221002520a00300100dd100010b00071100c0c5000314154503080002900300c14110100910081c0e85012002190750342e1940b80d110034400c1c81c1c04000d190b854404500040c00180c0d030942e0120361440036a444d1f50914091000000490303aa55400c010010600340d80215020700700310b4105848020243c00340c0c804009842c400c403421000555a003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 916495656 1250 916494406 916494413
    0x312070b1008060705040501080925080c0f01050904050711010e0706021b01170a0905070b181e040207050f0a06050601111b0105071e05010b010e061303060e1507020307 74
    0x18085038881c00b002d400c802c0c100510640c019041d42c0c2114028280540c060740c03224201810090052400d01800c01c11500040c130138028000960165613884c011642103402070410022110500c142090020b00c1c20006401c3d82d0400b074110581090717080c103064103d01422107880c0c2c02d44619503229101c540c414941004602ea042004080001ca00d203130072002000c003500000c120a510000d00f006014020010401d00ba010b075014410340d03504403095911050701d030042da42d40e0b50b0104e5009040019604c4c45c1c84900c0c5083c0c1d82120b0325100348044c2c814098224824403010790231905066a4502400c1c0401c0e0003214140454803a080c45107a000503103140c000e001406410030a00f4503174080d4010310503075001d400c6401028002c0305013400c3c49502e0ba5001c1c83c104081c148400a46c441c00c0c0030030492201004030540042084540988801c0d0703004094a06000b400c0c05440c0202508030f00369002000401c226a01c4072080f9403504003580c4e840190412003081112003600c02400503400081c00340f046c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 916496906 1250 916495656 916495681
    0xb0301060504021305101403100f0905090606040509070909051e060907051e030f0d0f02011404060f06030b0403050d06060302030c031501020f12180a08031204020312070b 75
    0x7070401200c1c01c40c1401071016144103104c107180607035401180c1c88103000159500031000001c404800ca40307044c5d40c0745032100e0300321166030740c41c03050345594800f0241c040f400c8441d5001d00d0b8485d1800c0310003004a40d40c1d00080001910020300082c9450150762804500c05481c0c1c0602e42085019200400410005100070780042c1d050f00c0114a10303400c400d00303100c011100802d85a0403181c0843f81220f09c8640260540e25100d2070180316541440381002105180da0041504000b0056540b91201d900d465180c0a074203030703040880240301e0220741070002400900c9940c8081042c40c00c1502c0081c00310340702d0780c4905204c00c040d501503000c81d90210344104042d919004600140002e45000c1d4114102024580d1080c000078008100000d106507940f07103207074400c1000c0300903805110b044a110258071200b40c0060341c800d00c031100c1e03483c08801c80500e0b181032480c05038048401b0500110715006010050390039411025004070b030b0502031905080048080c3d900134250b014080c0c94074940d24107104219084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 916498156 1250 916496906 916496909
    0x1002010e0d030c0f0e040f020307120509012c1606050403051006060e1e0a0b121501050a080408091011010c030908090609030c0409060b1002030408060c0a050d0f0b030106 75
    0x4050030311480f2441181c1c8985404500003103030610240e032194000002c0c014160303e0802201e07443c03000c001c100300300d50300c489144003400130403604004e540c803500c90090a94002211400401340f4000c99415402c0d400380144806111040969005041c510020f42e02c0044a0344500d000910105060090100030f12505002200c0c1030780810911b80b030400040e15103440c10350040c0c4503d1420001c010380009044544401c5940188051252030b211460050550003c8a407a2400150080094101101400440107091058492a041100c0b900040b50700c00c2000704210b514907402d10400c40300352a0055948404c14941d00c50310980d134006080c0c0c0d0b00b120f038107002120070182040e85800105118001711900c0c0750040c2c901507511010a00802e203008810140c0a0300640341c803003a071003030100c5035100c0300c80168200c846007603c00050070102c0c2e9074025805015504d811102c0410049072480f00103040b88030440c00d100d410041c10384021012104401e0300380705003940742c00108281e440c01780309550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 916499406 1250 916498156 916498183
    0x10061d010906061d01021e062a12040c08060709151b08090a080a0f020a15020c09220c0f0f0f05090a150b04090f020a0509041a1002010e 60
    0x50501d8043c0080021010b000c060240c440c16002c4a44141d1081c0030201c02031001d9114801400d0180700020356035607045841409204c000d140550507110000440782000100c03c030102c1c18000c40507900180e1580280c41110500c45c1c0c51400941c02c0b505010880c49039406403584004c01e0b140c0709254004441524409040000088441c46030012040b035001c801504220b00e41d0320f540e00c05c00811102c844a1708070490714450150181c00700861080300400140c400d0361042c400c0c0383e0355018100c00d0025034043c040035810140240b10241880400f079070f8000016462210030144007000c0c015a0b2007445400c0c0c5e0422140c030014011818440d0559009201000f1340c000c000340f5008803c0052280c80c0982c0c1d02c110040000306108000301c0d0800000c0c810120252142c45988200c11080d80d482485540460381c1810400c800c04c800e5442a11640055a1180ea25010f0a881004020080300805600b00102d200c0ca40320340307484e010044038810203182c00009090f10507005052400c880703450001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 916500656 1250 916499406 916499411
    0x9120c11040b030a171c090204180213090f0212030a0306060801050d080d0209060f12010e0408030402240a030c0216121506050d0602040e1e01060e010210061d0109 72
    0xb4040c5403800100644465001082c0d0704d40c80040110203442441404032021035081d011051510150b03040c0d0040c0281d0744203c0301045085100e600c120700d401c001c080d02a601140040d1150424801c1c0d030400081c0e50f10803030604c0703903124040d800121401881702e21480c0590011580042c0c1582520400c0041c00c80e50500481c65898070300020000d0b055114000d20146002c0743c405da0011164040e50500c0c3c00003004161594028080540c07940c0000c620185e0b02d05403c400080c864100c614824002c503041007640f459030b030742d0f03400348003040100710300c42c0034050410304070800682c056402503c801c5540c0d075400701e041050300c9002807814488400c020f0301c00050319010014241090048843c440e80b00050660001460703481c0340090003a980034541140035854560b0820415900800c26503a441c40700f400b054443c01c00f40c44c3c6000c1d11510380c006008590005214507800380c02003420320601441203524009040401c141603c1c8668044941c0d441c42d44080d4500886103d07400d03001d4000701204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 916501906 1250 916500656 916500671
    0x4030e1f03150b03011707080703050f15010e06011103120114040c021b0f19030f03090e0601021203131703060901230f13090b160c170a0309120c1104 66
    0x280a01340700611402001440152100e03060110902c0f41c0c80040241805454210b580c1e42071441e02e83ca5403034005c00d164019120b00302e070001c1c08451070318145c4400b41c100e514507603521801501c14110340950903810740b0051003000101c14010340e03002c1c042c040e85104071002c01d03580001d000c160380502020406540000c2c0442154281c02c41c0d0010381000704a491402101401d0081040c940c011008021801d04801c004824424030403000c50f03400d442a65101030700c550351050041585004e0fa07809005801c441242080c09500d00041c42e00f02c08224102d01400942e035448081070100301104101c2c2840100400840e807a010105500609200c3c204c050480c9424600c25040040c150301c0034800d00664500006c9500c034003050201192803c6010400c041e201e0401c140511821101c420019401201d91101e1a20031071825421651040200c06218441300c80d400b811f80115280c102010740d40c103004001728624009003901ea0f0107a8032480c04010761401e11062481a90b081d81e8001d40c2855003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 916503156 1250 916501906 916501919
    0x150f04060302030c190503030a0324150f020322030501062108030a0f02031312050a0210110f040308180117010b03090a02061908010909031704030e1f0315 68
    0x1204d850340002101d40b0b98818800aa21a41190315a00703c90f8041c400810700d484a20f4040d80048401811215459500c002c0082664903405a038040e00c08129041003100d50301f28050380b8240796004843c01500d00b40402c030264014604945040e104102050f50000c01c01d01c0f40070310940300a080b000194840180003448100c4d11622203000c02410341c030340000000d802c0201580504000207000700305543d01c2c140340c07061f60007413680d4007801d88040c114007596000d4607018000701c401040d810380190a07114a44900d160091452241041c0405010048800e0442c40c05005001071071080d41d40544403868285030f200490303022840c06051010703c11020001c420a1300700541128103020b20702c0e0b0f5070340c0c403a0540c0d0308266000304000d4104e00c000c603c62010700c40701e4a6000924030540e640d2100c503030b40c861141302691a14203003d80400e280460010321560702c80b81e9240d22038080c3c01c21703a400029010200f0b007806c6a03102181c07184040504032803d1750b5072500410388841c902410076030440b414480c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 916504406 1250 916503156 916503163
    0xe010e071d040f02030a1404030219030311070501020a090803040f0504020a0329040c020606090402012a0809331308030d24030c0302090c12150f0406030203 69
    0x4290406026489101c003510301803860081140140140050045203204404240030350001d03201106c00790300f011a4044c030040900c854500ca2505503005040ca8402a42c5501c0303900141c072410340805441c0c0c0d0707000940c010245c0c024030301e042c403a1000503611180100000c11100c180d03046080d050b041008100700c1c0c0e1840c00850341c10382e00f040341e0040c0c1e00c414030001030700200400c40d0210b60b00100f80b47c10514548440c500c80c3c051080a842c24440c18142181c100c1c0c4030340c01107c106074815074038004180954401c078400c440d0217138090290740c10800d56007070640c80d00050990403944214002000704031410000307005600d0391001d070791900184c005509030301000d41c5c481040d22003001010404480074003c0005000080200c4000d8a13074414082118101400c0301100428060540c4081c0d00405181c4400b0201260782081d541c40d00141507078200300781000090300000005c1824040d401c62103800c14030703c42c050201f5061404601c0352100a1201701c541c03455105204900c1c02c0e800300090788022 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 916505656 1250 916504406 916504411
    0xe030702012d120209040905011a060f0301092705030702041a03060718090609150b1321060c0206040c060807141308060705070b010506090a060c0212060c040905010e010e 75
    0x1403d106180035a40c80d50100240202440e655002d410000c3d07003400c0c002e043d03000c03102c0c40869108000c85031304802d05000c42880ba060301860040c0c410801004640c1c200d0307214001c0c1c4101107070074038103550021641c01c2040d4040720341030366035030000610795046244c240b084a909000711800729081403008000a074540e0002070500d010701c40780c41511040d40c11050003400242c0300141040021a0715050706800905040308000c42c00300021402003403600444e0b05803a80c031000208212070b43c500340381d8081030281e0070850b014000d0310b220070010006090341c0100184c680b4981e008240c2450142001040030003a64452000c0c00004800d0050031940704000d00b0403c5a0340c8402c9566400401d00c04101440035030000c46180100010302140729400001001203600522400340b00d0b0b45c851040201a01c01c4903c030581c000240305003040340d02d00401c0f1402525000401903a10701d03010845442c1004000c50b0051142280042c0034040c2082c2d5105d21800340000e0b20f08050350f5030508010300c5000002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 916506906 1250 916505656 916505747
    0x1050901030525050406141306050c0a150903021b1c020d1b0501020d050f07110d020d0c081501030f0305030c0c0d0507030f080403080f090c03010e03070201 69
    0x80c0d800046202c04001e825030321070403c0c42c0b400300c0c54501c00e00c00140582c1141c010000010707a0070a05500280c084002c1d15000110405420040c6181074820795140d404034204c0b955a009a03010f44d4040756569694288031804c205010422060030302e00203041200d840c49540c0c00780c200c0c034080d46081d141d8a0340907440307014003c0c3c0c50b2142059400040e2481c1105407008011020038107048a0f9081c1981156044a0084e007c8510200d9201011b9803e809641c10201c0050760a0003400d02081c0c060300c80c01452074024080000309030440d0041103d450507543d01b5070714202c41da0001c2204140c20000503074030000e4103e00040e2541542c1e82c98084000c100006070030001c012000c290100b00d540200c4580342081003c5071444e06a01002421503085a42c2c01d07008107920b040403103a40c134080c0c08020300c1694166205800c40d9100a00310500d450045e01c2c41e01c0b40c2c0b0a04800704a5034a0034860960080501c00040d91941805e1000500401c904074420b900345610102c0f82d00c04265003007610041012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 916508156 1250 916506906 916506911
    0x8090406151e02070e18010608071a03070c05030a020d021b09191434170907080f030304140a02030d0809190b0a0c0201060f03140703241a0105090103 66
    0x5160202d03e44a42900141702c100e02c0003003401000e415181720341c07200e115900c009021003aa200c0d1107a072140e49511039908100c0080d001c3c4107000e031001c0020359111249041403404000c0e13a0b02d9036032441c0c01007070700a0096842002c3c5403031210340410090b0501000c4c0c005080d248600000480d10341400681032000b02e10207125a400110520b0700304190b010b40304841d031030b60740c82c0880c0100c0f1000407403e4040c501c500c0c401d014580150350a0551450b500c42500c40040410761045107451868009010107a40c0c01484170102e060074060107121322500810000b10744a0074a0f040141ca010711038440c0024590120b0319610041e00d01080c06c5401c00c000c0c0c10711440964823504044e0510002080003900521030710b46c0c110801c4040300380c03140610140503042002081101042c3d00300c540d00c3c05000e60208028200b00b002030880c01545c420f003420101661542030783d960f91580ca40300e500182c8015000d0141a650180c00c0700d00c621074110700010442030030788680c4c0002030203030f11030703070301881e04254 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 916509406 1250 916508156 916508207
    0xb0d060b190c06090b0f0703060815060108070909150905090a2a050a03030305041101090302150d090803160f09030818033a020a1e140a0809040615 65
    0x11076000b0802d09412200850750351901000301b0390b5203a0101c940c500841d00d860320128040d20006541c049642c000e400e8101191105001940ca40100030003110820004940110381904e070380c0034a010000312403001c840c186040c03601d414240d440080c615015940b00c10400c0c80402e07040320010100c1c401c0a1000b00c80000002010b128140300e9030041038020f41440703c004109513042d400b40c0d08c034600a40e1529660b2140c0d4004450000e014070001e50b10050504c0540d05900e240402007c1c0045103c81c00039115a040c2d5825110780c0003119054428030300e0f0002015100c3e00510079880c9288a0b190105189007140e4500b01c09004041051144c1100c0140420558408020004031001161200e20ba8440f00c1205c202442000b407079503440c1440100c0030030002d0b40c000a0510101ca0303120040500195800400c4440380c4d403c400309942100d014000321454003001d00c6640801b5025080c025034840e007600c20b0000b600d0150380101c9151126a5000900b56402041440c101d82c5100b0508c4404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 916510656 1250 916509406 916509413
    0xf060f0b091312120e1011030f06271003110105030910020901050f0c0d09080c01020604120201090b0106091d1618050a0b04030c0504050633040b0d060b190c 69
    0x1d4113080751007502c481c075040050010840c00109082840d010319424802034a10148134035040c001500e1107041041810301251080c41c0101003e800280000d440c20a0704406620040c0c04400c1a00c030700440080f0000c082c0240038420059040f081000e00b171071461424045400c41d81c41441c1090000c400e6130101d031155040e84103004075840c80c441e08190644400c2c100c0039480d03c5400140190380450400342d00000d5102000c0f5412824900580141929aa817500c03000c0e0b502200c03101f0203045550714401e0314005038840459a000c0c2100e81e5a000c507060510503002101c0c0c1c01c001070054611100010001409080d051040d0076642a150244070003511401d01485e4803440d8000c41d0740048401004a01220300c40090002c0300d002c2c034104520207654109003c200c0e9000d4455603004030030004c2141c68826900742c1c440d120800d03051a22002c0d0052903034181540c0041d00003030746445000409007400e10090083c03802610242040c0d40c070744a2143c144845a40b4141ca0030024084940400800d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 916511906 1250 916510656 916510667
    0x603100c0509150c010b0a060c29070207080d020a0b0103020f1801090e190f17040b07030c02030c0306070207170319090303260f040f0f060f0b091312 66
    0x10b035100541640f101c0c00f84840f00311107a8001101d180c0e0300c0d620f00300344c45031a8a08103041400700c0e655a01c40b401450b4560700c880580300e404400a0010112801c140c002404000e20542d00c01c203220390103003252500b018589070609080300072210856120b40448004103843c0c03850786044070790454407101149030381c00c00300c1e10145246141c920091001000020342203442e800001400b0b40010648003002c030340d200a802601e160306030203420000c054441c4030028100031480e22601d07111100d1281070554810b000509544100c90407000102c0c0c03140c60300b0460408110031202d00108402824143c41c01e001c2c002d42c1e031201d5214107020801c80303601c0e015805506000b22501420389034200300c090080c150700035081410724402200011114000340105210440c000704160804094041c16a04c1d0382c0c9507003c3d92000940255a50546004041e00144110503565141c0303101b104080f403038020449031030341100e407440c0950b07008188040410442070244120706940b5603001e0600880600c45820480c1c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 916513156 1250 916511906 916511917
    0x7030209032a120c1002212107020312010e1603020d090f1a1f0506070c0801090f0b132301090b0906100b071112031e0301080709050603100c05 63
    0x4100003081d122404440d0041034444c03140c82c0550303580d142e610180303c3c05c9a03a805400390095441d10f030303d9441800c030010f002c000e01c0744081c1c9024103842c4a12152511940781300a456074400340c1d0001031200c0d001041c05040d09d00401101c200e000840c80c1101a400b56418540007850030503030b00040240304000340b94800c0510300d0b04a866040490814a4501d11806540c8a00da12110304107000454410140c036250f0001d800301e0420844092601703042c80640d4011040444201340407000100700e4102c00d10a4061032801072500303290320400380c05e11070034084008c6e0620180e01c40390362841c400b00c0c84c01909002c0382c1000d003046102a02c07072050904d004000e0080004d24061124052003500100064418003403404200c0801c1c000703903102800149440341c400c0041c840116201024464500355a44881c42000c038015240307040e21881440b6110b5421000340b000405001c070040c40a480c0401c1010b000d013071a510200424200000020343c1d811588242c10181d9031500d1580c0b620503c168140d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 916514406 1250 916513156 916513159
    0x90f0d02121b040e01020309190305042d080106140f030304030b0f04060501060206010e130311030a231e130806070806010f020c01050301060509040603050a1a07030209032a 76
    0x20014551814100c0026280c030142c24402d80c10901002c002c040b0610880e801040c00398001c2c90304400038180360200500f2007034241c00380b1505120006041d4035103281780c0ca08101100503800115865040240304010507080301c54547c1c507254080c4000c0c0d0012481407408041280e0200b000121000081d2451085800061140d005201803011038248207103024059441600107000582c5c813505c00f01c0c0d50300000d10511110448590108905072074120340806414064030305500101214004103240d98040b404c840b0000e02c10001c5002e0560089440c1140d200c6100c0c019490195082c044201594288803520602d910014422425140110038440109000306c10b84a451a200320040c2c0040703812030b03070f0501080300300c40210880d074400f252603401a04161201d90440e400d03e40e04131101e401205180fa0029510305020001c41c0c1c0030480c528803a44a542e04401144001c0300f07034080044098110000c1c1401480100441e941c0031503640c80b00d6039011070001c1c010100180f10301c02da460568100c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 916515656 1250 916514406 916514413
    0x220606030503091318120e2e0302030105030c011107090f050a1103061525150b030609030706090f141606050a050306040e07080609160506090f0d0212 66
    0x300304900800074000840c0c04072211210084058007a6056803524110b020b00b492031003800030001403104004e002c0142e0300f858049881412500800c480000b40b510500e41558000e00043d4811180c0d401914110494074003036042d54036120200783c1d251000c0c040302c1e06101004410074000c030020050b5a00074400c0d0541449044a001e102c00002d10080d600c6450403403d000079a01c2d84111081200e0103020003800f0f182c8032051840d00300d0059004522025a46034410490028465001481012071030041c0b80d090290780c5c6200400302260100f152076406a0000b40402560140c0807003680c415640088d004150000f05140503403059801d040010023204810f00f450003150f100055241d131403000d44410601c459280c07481510b280c0540408040001e00810005105080903007101c00200681821101049c0e240c081090074000c0c00c0740d10140550100e64000666129280c1e2980107140c16110507242060780c80204900d50f081b00b400c44c1c00307018180c500c0011515a2403080040c00030460a4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 916516906 1250 916515656 916515659
    0xa0e281509061b0e1224060a050108011a07080d0f020705060a0203010f050409080c030705030703180303080106035108031204080d06090c0810030b220606 68
    0x112401405800010780b4020700d456803146101007a40034002e01d0340c0a40d140c040c0941c41c1e180c20085204c00e03c4c1030442407801076045402141200801d0310503101455442e50207549810b2040c0105031469601a81c100601c1000410030465511003408050195940e1030384d40b20410f0400300c449126074201035179903918000314509240b259901602983e441a4155a071540304d440b01e0805a0000380108100d00b000302008100d646000e9122021032442442c6141c1001c40d014003c038110b400202095466820028001c0e0805034050055251481766111100d485070450710001d203170544c1401484207141c0ea5417440c04460200c074003803c4031094411560300d07290301040800101425140c3d4910790044c0d0340c111400601228100c08010386003440020b6003403a615107440c01c13102d0005003054500c07001c00c00000403101c80e1360042d48090300b0380640104100c805a94000d1680000030a02c810a440a0405000045420401c02e812208480c00c49844449104e0b06d0340d00c00a4240c001442249460310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 916518156 1250 916516906 916516943
    0x160210110f060601020607030b03151f0608010312030e15070203040609051c110a0b1204031413050f0a0b03150901150203030c07030e0612010e0a0e28 66
    0x254180000104001d5030041082401071650b80c1e00c0075104240560006030000f00340c50310070f6109c4121250020115200d510b10303031003001c03d0b00d001552007201c1010340d44500c1d641c2c0132030040c905005044030702d4541c441c1c0d80340d5111a112840c10404040800d034440c00e1100000703108005850142809070001c1200d4104010041d40d268441c3c8940004503880c1c24000885241c0310007980c1c0c641d06c0081180101c40c0702c5030754580c5d0080c014136000358080410301020802c0c44000014080301c402c070034030302d04141c103090601919106034040002c81c1c1c808100003844840d14001140d0084031419100041c00460000000da402d29868108040c81c44010040004100f144100c0c1c1c10100d0007610061816622941c846420700400381989001d40e0007040440c01c101600310042c01080e000340387c10360aa105030000100703964840c0201001c44000305e00140102901e60175025000412070384100006c030b840304150344d1103400c0c814254010200c5982103d440002040d100e00c411948015103441040c001030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 916519406 1250 916518156 916518167
    0x91422050d1206150210050106020c0d0b090114070e0316030312050601140703030515010e0306041202010b15091e0d030c1401021902100203190b0111010e0321040215160210 76
    0x1b422280c0c2a810040002140b6001040c0d452250b00c01921030701803840d840c1c80303603a800d2502a2144802c0c0d9a207031902104c403409004614003903001690f51500b8210083c00301881c1980f401c0682d0859143c2450402c00250400b161f5109d240c1c00d80c50100703881d0ba8000041c0c0c1c4016158682e20640440018010201035150303100500c5280248110200d81c0078035401140d00120b00b404050305548104041004699200e0b424000b810252001161705131203000883c0d40740d03021032401c2c0c0e03078a0800b1400521903d44586072840c21801c0300d5500d03005032524400031b0003040f0012070103400d01004020090502003507180c0e0b0302a0035904c0000b503607210a50203007580380c1d4110345000d00042c000c50b10040b52100c040d000300d80c020300041022100c0c40604141d100c008103000d01140d41031102c0a0340c4180a035100303016900c000c01c1524055500c4104000f415000040020302d50071050481c2d40c204001039580690b0b0031058070100d24225210440b2810100401a007841d020f5444a081d0281104281c0e020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 916520656 1250 916519406 916519423
    0x60b0f031014010b0a0203030f0a0b0303130905060306160c05101b08090f0a062a030203180309060f0304030c061109010318120f0504091422050d12061502 68
    0x90311003030403a80d071000c400999001e00c5c488280140c10400120310428900310340d85401c1008988006100c0d0540d03800240340d0340c00050325904041d00c1c0e030000c0040c010f01d0720032603a102d88260040d000c0c52414010300c2c4100c0081c69185424440340608500601908000c0010030540f26a001c00085003c0c1d0704600c122009030b0101d40010300c64034002047c4100201d1103907005002d000090098940075a5840040d00380c000748540000480b419040d0103545041c6030f4840705c2240c0d140140e42c0c0c213003205200e01c00078904442c00310a0f801000b00c0c4100d9100c04045912440c603040110707480e81c40e18a0103c0c1c0105071901c001d8003007070610300541d0b6913000f414004d19201c1c5007620104002d181c1c0d01c010180042c9460005031100c520010341e054218081c1c26201000d0801e890401c0c60310341c0755915801203520300003801313081e00ba696040110402851644009505810110702040089503480c2c82e652442d032a030301000c00018141c030240c403882540041c80a803030f444540001d2a01c1140f4029602d1540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 916521906 1250 916520656 916520681
    0xf090402030114240f0711061c1b0c060b01210501090b040b100e12030a03140c0301081f0b040906021c150603020309030c19050d0f0c060b0f0310 64
    0x6601240903a07080f150011300350384070544031160600c0420904034420350040c540c1030b900302d4804c00103a0496a1564000c25194150413070074611059400800e0044407006204019268040300103a08400d4201c607401e90750f6588041d022448000707070b00041703444440030800d10a000481c144168280d00c1d4980140b810f0302c80381c4004101641c0c8038404c00054a02c6504c040c0d41126180708170900c0c02e4411081c040ca81031015001c25020724151841c145142e00c404000000682d4516540100402910403950481303402c4240c0e0342954105000075480718124803501c036649605081a0101440c150005c5407161001801044110558101600a540107034070075002a02c520b030645084903468822041882264040100c5140c1061816070081d4800341003013001d071000340111000c00c3e0b000c0100e02d20781142c4808001d0002c0052a045181c0040d90541a00b40302d0707030900343c484ca50f078403d07403010b03c490f000040400c0d0920040e004ca011001c545039010707018050440600780c542c6880c2c100341c0e00d5215 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 916523156 1250 916521906 916521919
    0x60206090d030203010b040512121b1207030e09070c123b010309030e120309210a1e0b07020d0f080103051213090606030507030c11060105060f090402030114 69
    0x1c2004034200e210901900d0700290703007808140320606103401d141c1c580c4080d08003141c036240c020701c004c0341c903507008840e8441c0c0701c416a400b668511281403001460004d030080a1034141320499501405807040101441d009003e0800024141440b450b00780e420181c10440c000c01883d26868020034800c240d840001107544400b40c8083c0070300d6031100a12520070180007115a0500c0800110050541e80c20f06608100300316490141075a61503501c80304061000008560313400c42d400034080009041010704010562410002580460101e241c044103507002081c1092451000410203141821343c002070902020035080041d86600040c420a9070003164580007100e4a44513407c5403181000d0000400c40d800214003500417142c031001914040f0000c485121015031100c0021044031015441000003d1315502403003100c681520034098200203d2502c2a80c054810440f90740e560410300c80c0e50b0254400150f10480041680241d50715040700500555581d6541d40642aa900e0700080c2c251145a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 916524406 1250 916523156 916523173
    0x5010606080f0f010303030b030307080c010606030b0618010807030e0a060e07051203041806081006051806090f060f0411121006080112020609211216020906120706020609 75
    0x4529a202c01e00c42c44503520540e025a09642d001c4000e0405d160004d50984000d10141c000100f80030301500303141600d00c0002558606d03001009050303130a8010480c0c0030350b5042082980382080c3d00401d03c0301900a0030251070503140d44804500800060203041901d010b080307061810010150440c10011000c20100c030442510f65082101c1000b0384100081c41743e00800040100d400780b928603c604850281c000151507603075558107410301080860707001202d136403078030140320070302d0450a110031140300122102900c2c548030300424403d00015005a00c920616400646107658030a1030800a60020b80107220500c600c0c0640c800c01c0e04068990325110541c00c001507408040c41034204206d6030706585002c901e920b088a01c02c280c0d202108280e801040c05c01c83e0800c980c0340c1c841030703450b01038408144007044001c24281a00744001041e5089110364200890540150038070820303014203070101c0301c980d5141c0b59040014400402c4c1d0400040360b001c0d14000191458000c80c0781ca00c60b50102003640d6814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 916525656 1250 916524406 916524421
    0x3070f260c0a050d141204060f020109110915040c09030201030e0a020130140105130c0e040b0d050f030a021b090117010216050313140a0b0304021305040501060608 72
    0x1015540105500400c980740200501d00c0e03d85a040c1006026480f0030140124144009003003074110140a900c980c6d0010b020401c95601100c0034041e00c43e240300030000244280d4410302425004c00c01c55104040807008641000001c2c456110103081c024801c02c9034400041c1c01600c40140e40c402030740840d1904d0004420308401180700711b403559050b90342c14103001a83d40d025101000403000a9450800000c100c00006550321806070038001c0c0c60204800c81d85418200a140d554004d003110115050422585802d50010000c03881c29804440c049995405200130820a0880f0074000e08a44100074034414142030110060208600650035118203540300c4410302000d400e0502820780000b4540010030400c00d1010a0709448a0580c0015103011047e80c0202445015420151070715000000c0d000c00b216021030101c4002c1110000e0390300140e185000047e10350b5014400c110690300c2c004001400c40d030755132104007103582c2280f808200744d0405041003802420395025410102e95081c000c05c2c440b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 916526906 1250 916525656 916525663
    0x30606080f01060305041a010303210212150d0b0f010911070c0302061303050d0906021e030d0e031e0d0501090204080c041d031209010f020301150e03070f26 69
    0xc1d10702140300845503403802004078010b041c0100242c0350b20f080c04102a01445494820350f0086010b83d5401158403201c4140d912564101802c02211510401c070444640b81c0701c110007907112010145100940b0a0380000c21403040041d074004001641d45801c00c60282882400e0a0603100719900811034aa8005918241846082c60151420304410070070001890008020580101d10305d0000c03800a81e2aa50949401c08980d0210003040880342e00f40300d0283d04210030396440b50544024219100034080d0280c4910503405071225007515245513100ca03040420446130046e20109444401c0340f0360302019084c1d5000011035000c204e080000018410a480c0252000d03582c0940c040c0000304140b40410008002c1520901c460603603901130720125140a10203029001004030400c51640f9084202c24215034410f400f0140c007a02c184010300c00b004003031060b4240c0b0007242c2130100644070003400007460010b40303038404104000044c50114007008614407006c1a03005182c0c0340c405195043d82c0c0d4684 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 916528156 1250 916526906 916526911
    0xc080d0906060915050d060c140703020102090301050f01051c050a08030106020607030b03010b0603071107090f090303360305040807120b241512090a140307020a090c030b0d03030c03060608 83
    0x140305200c031071100d0200d03405238018504812181040b00c0390f0707210f501040400390000c0c0030550261f540821509540d05080c0035035544811140050340f2a5130502000400641000001c90b1001c20b010501e1804c0010070081c80085941046007180c40f90380d62000255508001c0799000002401c1c40909101070405003d000f024603002043d40d400e598825504984008504601c850790340b01d1103400091440300c074442c500b000d0020b02c0000c00c509225050190030346031546c2a42248424551007440b00003950315a0718000d441841003c21096114241180e0a0055410002d607902658000044885020364103841c42485020419040d03130b204005285040e002c183e0200d00c140aa5881072041c1c940004c0649000ba19281c42030700300140c01c401c00c100c02104551807a0f50f60b0140c000c407405d006800d40300d402100d40600003140342405030f0340419005005c0e48101c88c451500c410b0f03180b014501071340040342c1006c80540f00700525203203410001c02030420468943c01081ca0b00c03801155041c0b08041680c0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 916529406 1250 916528156 916528159
    0x62105092d12160c1401090e040503030609071206080c010f02030a0f050c0a05060f100f060c03030209011709160602010e070308090f1512060d0f02010c080d090606091505 75
    0x14407042c1806032410350307002c031007110554290180e030040002d030405210406404002040110300b00380310005400800da58015000b200c8070101000001000042100e03446003003940c2681d0661a001d60503503454007054002c030495400d1003004a40b810001800380000f1500741e0fa40d1801015006041c0d0701ea00c41e600040780080c54100ca801035050094004001040c20201103030030800840d07c0b1503003012030540c3c40c0020b0990351014402e100d45c100300004040c0ca020104c1d110154580400540950580348006091640205445500d0b07800740b42c110540b0f2880c0c620b040c215140002110b912469414520045d5042c011400b060031817052086030101140c184c0181030150442d10f5201c925002403880070740c080c03000320900308552104040354419565000741207466007100c19416031000b070010b00c554020480c00000f0400305894083c03081e00c83e0340a080004909066040c51600d601c03901440ca02003d08040c10642000b1056000e00e0844606107020003040300038141c6403429910b14403030300303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 916530656 1250 916529406 916529413
    0x9030f0a050111250c0b1c0f050108060f100321030510080307080d0213031511070c0e070309120e0f092e0f09022104020a062105092d 59
    0x40000c1c021220007801c10303038050404181c0c4546c1d20750b51030545030b101044844a030f58020f28160b8280400340230300074140d81740358418440d80d030500104a80d46d06000b00910780310f040030700c08514504075040a140207103801c101d000f0300030300b452a44c1e0030022074441c0ca82d0340002d181500140700c401d00c41c80b080d025030b241c03003010b0b501c2e00e00c4603141d0520700d410408207448616401c2003804124061242403800441c03080031024060900149803c0480340340c94840940b04a040140d40d00143c402c151420036200410746040c0c440d00c0310b003c1180145603c3d04000d008402851502d045960000782403040303940d00b169060300213070280c030910200c03031002d9800c80c0c025040e0f0001e000b98840685400d111040051b0002031041c3d0355900c15241404050b80000e1b07809500040d0100320384d070f064041a03001150000240c029051a07804100da40041c0d02c44c0320104441d0200002d01d5441680c4020168210342105214170304040c00c0c5280c03109031159421100c62111002221a140310300072100e54001581e028 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 916531906 1250 916530656 916530697
    0x60301090c150908061f0906050919090f030324120f0512030708010e06090412110a0803180606010c0507260a060c11070e01050609040209030f0a050111 67
    0x40b188100302c66002070240034049101003045a02000958420042d0200c0011940c4902a6480010900c0d0b00301622040c108801800355456942641d90040002c03604c0c0e800160f00a800080280490007005007050941c41c9400141035150304840c480010928080030403440780800b807600100644117001c00d00000340040d03004075441c5001851094010f40648101c00d02108054415034022100400842c4d44500140318480390011030030390002c81660440c00e94245a02c038548601107c59150081240040150707161407014800041d00700c0c2c0c003400441d01c030300340407103070604040d0580d1004480d4410400001c2d89503201e12000d03001c0039001006132564074100401228400aa454110000802000120a013503002c0224210003030103607000207045180034000402c40c8061805c41c000e03a1744142410701050391040c20650446200300c4006650320300600c08580a4024080c0199045c020584001e54a85000c164005480c0c07103203008010081c9007010300080c500034089413080c05c0d043c103040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 916533156 1250 916531906 916531919
    0x27061009091509171b0d0c08030f10080706051207020109150b060702060708070302160b0409021b01060f031209120605040212061509060301200a051e0a08060301090c 73
    0x1d0004207010f889180d00800ea050458156980085000c919548202c408417504000521103248984180d25103c00e2002054032096210301000e4150003070040c0749000302c1c9800c03c41e0030381c0d54010018403040d02c1010350f590340050405c2d00895041241b00000300e00003400da0b07106108629100b61700400700b54991140314112001420f600c41100e40200381002050090713501c00e406800103500c00d8910550b41d817810b28009050150202d0b032003e103416465400d01c41d02074004c0603141954080c850042c1c44031040c403060000398a4080040c0c0a5500c0c0030000305401720041d0441003980c4c000d20032000714050380c1c04222580041d52140c03001c000301002d80d0f4030000303020340c00c801c0e0010300040c00d034440100100340803410204152071100d0300444441c0c00d985141400c80c20719920403011002041108810358102c20415000184060519400681034403a00e0103001921405007100e00522002d05c40c060a0a22590202c80b60102103500d1400240c600d2805018440d000c03584500b030092120b15084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 916534406 1250 916533156 916533161
    0x1080a150212010e243a050d08010e040c0b030402010c0b0f0105041802100c02030a060903030c0e03011e02131701140708150108270610090915 63
    0x140386580c603000c00842c81c0d1080c0201c2d5290181403603000e0803000e03040980707241c02e450805000b08188403441021101440c3e803242c82141d08550300c01d125010140451104001c0755051856200c01285080300002c00c0c481c00140e511364071b0085c3d849485c10382e40c881d2600c094088003200e0040022039004001c0c00b020414602641e006813040c18000301c5202d4a41e03400001c2401124180c030b1311030170b11004100c0741c038150180c525210003a101c0380c10340400c6a00499840142014003c0c01d1000305000c80d021500c04029401015400110403c00460946002009010346000401c00100221a900102e1506100b90a02c0b14410a030542d00300c1103540301e050182d0400c2d04500031942d038210700019000c003107105020344081c00000004501d0b80b01c60705503550700030103802001040190010000303c040004c5280c030340e440d42400c01044c03584d551100c0c07104030881180907241c4040020100d418a41001036503600859065451416140d1921903901c12110120310180201e000408841d000d10501ea = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 916535656 1250 916534406 916534433
    0x40308090f03031605091002010c030606030c0c110616030504030b0c0c0a033609050f011a03090102192f030a0305090a0209010f17070f0905090c19081501080a 70
    0x341000790400004400046d401e900c407d03201d1015035180c146030103a0031760521a0b000500140c0c14208501c8181c5900103180c0c5610301c400421500341500c00340d18680c3c8050603103030780b24156111820707130318510f14000344a5017280c4412160703100110082a50051000141e508191000c3e0090103190099242240d1402e04041050f03003140e0340300308603c1051454a000c1141028501c10320b10000d1914800c5011074200410204542e030300c00005006ca12002e101100c0d01c010144506500ca4549642c1ccd103009215040501c05030a03150441400e0300c036000702401440a100c03039907800c1c0740d661030a06460f182000c00e2181e141901704005410541d8044e5001d660000e82c10000c803501c5009590202e0b0480800b88c020542c482040d400070041d40794003814640680712000301508041d89011010080ca036004e0003280034a6417140009850608100260304601c44010f140d41100148004042c0d440c00700d50140c45400d00501c003036188460b002c03000250407600440014071481126454405003004034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 916536906 1250 916535656 916535701
    0xd03080c13030b0c070b0f010b30010e1e092a04020a2d020309040504060e01090b060f0118050d0f05120306120a02090601050906040506040e040308090f0303 69
    0xa903402002207035540400c6132055519100880e03035419141000c0d0580070004006880142d00d00005100201284081c0c80309001303000b042005c03a98000050f9814034120341c0448003101900800000c0046421408134026070402c034a020700b4489014600940d55011103090401e5800520701800b07440070031100e9245004c910807112883e9801c00d00140076a40090400030014032030b5031b00c25145a800e501304c0707000e01c2e00c40c00d06982034101c1e821001c0c0d203e0040b902d4891050b5941c1e00000e0a0050a401c003515610301e04000700100190744c0344c0074000710401e41d825030042d04803100c0a5929402084803003207031501c041441044501d0202007001394004039500301c1e0003128404544c400224108921000f00001c2042d05840c0d2a180040c04000610300150b00020b5014555841c007503256080c0c2603070011020704c2d00540d00d5a0b80d00101d00103108650145c1c0d0411000a0009841d039148160a8040c0c0c0c400e036540740481c0c94a524050361009219004195a0020004500c0184001198038949020f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 916538156 1250 916536906 916536937
    0x309030c0a0602090f01020d0903030f14070303050405061b040b072a181a0f0f03070b0d0b06070203030d09020d1202100509030a020a06020c030d05010f030506060d03080c 75
    0x100620460514004507000c40c0d20603008102e40c09203141c2129042c010300d40030301c020f00c18184880c4006140b424a480302070b06104903100000050303482841c508400d184c0801c1459130340d1040d89801401480c040341c058406014420100e00c10003015405131034200e82d00d08040382020705004d03407880e8036845450b0071500c00c3d05405d001c40c0703000b000780101812054404040a625440c0003260340d400c10081c000402c0941c03170005080802020000506d003a9441507070791782420030100e1b0120b02040c2c5050003003a07140c890301c2c00020300c2542550060484440da41c0d014401d070340f1000140a1140580300c0000c1d8150018060340070450420346c440c40040c0d0001b8548441441e0342d07165200d801c54135046500068001403d003080303007070b40380c01001e03000001c1500070f503c0d040900c80002e443e00c01810000784034640002c0c006030701040800c10f42d101500201410841940d403054a425008014442110b443c000d01000941d5440c0550030180383d00d416466074443c2e550b440610a03400d034042c10f0214018035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 916539406 1250 916538156 916538167
    0x18080a200909060103060605040b101d03010516030e030403020105070b0c071e050c032802040608070b0903121303301218050a02090c120403050711031b06030903 71
    0x90380d40700c00901640c080b0002d03040075411803d004c000d503a038640103140154188610f40f181600c890000c808600e01603c2e0a00c070304809500500d0881c0300901710242d0642c03c01e02401406402003010100c040d4641e00c0c20414440d24079156a180e0249200c0a40411401e20080c4041550b202d507440c3c0c01001d100d10245013021a070340303941c520060310320040140314240302880c041000c1003002c0d0394040c4c0210001c0c0f1030000f24920000302c60404d5040307820001540340350401113490700d802500144c00e500c810b58002e65240c00e25540117411078a40d581c440d205441040030841800700403164000ea401b40110b84080c295103c200158551006a2103625030050110f1200030089100d4541ea100d940e94031418a0301d091034000036600e4100480e513440480020207400134900049011030b240d8180c2e2446659600c07030085160500a1510301088102410200300c10154001700070010540320f9981c1c180840180420700d903a850413100c51900c2c030710804084840600c0d101d4042c50784003c44004403071504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 916540656 1250 916539406 916539409
    0xa020a090e0a060603063603030b030c090112050607080709060f1103030f0f010b0405010219051e06060a06052713020f13050904080d0e16120318080a20 67
    0x6403600c1c1e20580b030300c50756072208411887c01100244e11010380001c04400b07054024812510804050348010207065803203440401d0360f20140811840110000c01c200c403590381d250007010307071048001c01c1140c07140070380000100d0701d41c003400c540c5000c1c56041e03480050340c6040c00c0050b035009200034022018040c010305410050001040110320a154440040e500307400c2100c0304102c0e060040e0003003000050140000d2185981c0065151904002401409110b04140c2802418100c000c0144502c1d444103c98002c01000002241d5015060603124188840e40d208000c0706d06020313804501c0c5500256030030b00441c40050358403006d030448004203045003400c1070b03407491001ca910500003003054110101d01110142c2c04101c001000b04070035251044940f41659401300f203840b40c9035441c08019640d22000751610000c10000c1009461610400070781d6842d41c2c403203515100348400450009003d0326105440c4820360381040111494540140f0078803e0740c0d036400e02e069200401c01e0041151001c1d4050aa = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 916541906 1250 916540656 916540661
    0x513090c1b120207090b0102150c04090203010806071106010509010312021c0e0112180f06090c030303050a0e0706080a0c0e03010f02070b090d08060f030307061b030b030a020a090e0a06 81
    0x440c0b1504165111a44080300641464415070046180c01c0c507001405142e40d0700032074014000c070746859071310301035980300520090b80703018503041071030000d02c0440045520040050828022020791722451408880c0c240415a204402d018842c0c21501380801000000c8142091001e40580740c0180d42d24142e6408500f0403744054158200040e81c0950300d00362035070042d0345640c0d07065a4800c14450101c80041a907211200490018180c00d140000501030010359800105031035840305400c00b11968a090060141c02c058681101403450a17445012507100002d0b01c0c01261082d4440850555404005400405441002e44103000ca20458002c0700d9800b03218004256140e64070060710340171581440040ba0100130041c400743d41c8451001900d09406c00c9036a94020b0088071940d40d910844d001007070a50107032002c014002401d114200340906000400138210f4985981c00b0401c484450040503513030f03180c00b038001c2c2d04051000c400340031002c140e41103c0c1c5003410302c40458281c0143c5c1c3d61b03103804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 916543156 1250 916541906 916541957
    0x60604050111010212040b011a04080d0f090812042309012d080d02010e12030411040608061503120702180a0e0715020607030e0312040203120c0705030d0513090c 71
    0x2445800f40b030049c8466240c1c2c90180100890a00f801c80c00c040c181040c0744e64410700071b4031183c241700703620f05400f9845101d0340c03180018100c114203695443c1e980c1d940c59a1a41c20501a01c000d561105104000100c1140090110010000c3c0002c4a0741d181800382154941541c24807240707424a02580150031840a00b07071402849a01d0080c140b040c0e21810080c00c40340b941805080941155070080c50070900d19050300d0300960480031075407145000d900020000c05840d8804240c0340650010401e0304000810941d901c0c55094090342e92840c0d0082c8540318500c103800009501982416034108001c2c00e070b840031030b84096a0071001400210f10b44000b440c10206a02143c81a044800c56010f200d42c1400307415089580c0742400c0c02180302e00d4649540b01d004005031202501b50090010b003d540e41001080004403619180039a60bc10307a180480e00c0e004180070300b501a00c1400a1801480d110305c088403000c0c0a0300f003040010505100c1c2c00006030490112510402805560112400f000d280d1000c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 916544406 1250 916543156 916543163
    0x1e15040f03051c171905010801051f0602030d02160203070314010609050c0706150e0903040504050f15240a0302070b1b03150409050d11100506060405011101021204 72
    0x18891441c500d0168500800d083e442160b010b08088400342298100d0a903980318880c1c01140c0701950348142500e4510300c9074544020b555814240000380c04c085c1036101c1401603e66503003850854080d01c000040c90350082c456400141c1c401c20031402d07411441c0d805400310412486120303035041243d40003e80782c81c0381074001780d4150403c0c078000d08050a0901c9250018400d0b04014070051400070f40040c1c1c64003030b00368003810301c540b151802001414586080340c080c129403260100e65007440c0200d90b03600d41143c081c041c000c601c2d00c0045600804c41c0f5098501c1101c1c2d07041c94000d1891a60140303d002c0740c036003102c40c04241e01c816103400c80a505501400441013555001a22030800341480c812404002e0f050302d0030f0980300b55001c03400000803400c40303a00602c3c503280c004894201f400460004c044410015006008100010004951041d030700121740d845175048a0950214548110856000f9504550300840820040240b54001c1e20818200f20f902d4000508103200164180840001104c1c00c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 916545656 1250 916544406 916544429
    0x80a110708070b06090f100b0703030b15030703061e15050f0f12010b070b070305070224040b09071419120b100902210907180203150f1e1504 62
    0x3003113030304050010507885802e400d40340529003404c4003c0d000300d40c020b000f000340032100002c52105041c040e40000c01090703000b41401c0d086103c580d0304001035420a5444500090419500041c51880c004920401401031414622034500d401c2110030400e0702c5540f410148a001e003c80e554601c4800f000d040400b16403243c0c16500d2000055603502031034141c105080002d401d010102c0820181c9121070350050355030900080507250482c040c2c0c90001494031542400e6521207030300740c0c00d840c02c4040500451040035200b03403e403240c460068542d4681d0042e446c2000c01481500c500340b8200440108a495507689001c0131521010030b4440d42070100c2d815608201c1d04c0041c8a1503041d0110400010400b40d43d0450a11803a4802d4200c41c0500c403c001e001120f03040c0c0401d114000500021000b004c07403002403a8040e60f60000b007400782d08111112245d40c8512201002c035410440d104400442004242586905c0c1c410b0a9a1034440c100c1040c5d9040700c0d12204410b117110f0041e00400260020b081d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 916546762 1106 916545656 916545661
    0x15062a01110a110c0f1c0606050409110108010504052404230906010506131707090c0504051912171204060e0c040c080a110708070b 58
    0x81454101002800710b1040d0b410400000000c80f016050703c1900d42900c00300305405003808030042c1c03c03e01c0b000210b0340441d00d034001c1524862080b8000030b4142d0b01c45002c038048481c504000c65400402410081c00c540e0405070305801400d040b03d003405a45400500b6192502c10f0380c10205008e100c00c2120080c0f9540c6403c072441102003500303c2210030b01c003a4090298040c0517a500011409a0800400c0ca030a00c4ca0441d1317174000d00404007800051611419141d050318045480c5402d0192540115081a160041052420721503840540356170501007046002c081c0000d010711315000010742000780c1d00329480c110040e680c202c001d110490540316826000b5202e198092030380303080c01100f04810001141d00c10155083d85c2012621011700c031340107000440740c0600041000c282c68100241603d00c3d9600428403580a010f9540c2c1002d48550794521160000d44049031b0202e508000c = true := by decide +kernel

theorem cover : BRFrame.Cov 916366906 916546762 := by
  have h0 := BRFrame.cov_init 916366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 916366906 ≤ n) (h2 : n < 916546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
