-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1656
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:04:56.823101+00:00
-- url     : https://prove2.me/submissions/012641a8-b683-4f8d-8b88-557387963903

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 297661870 ≤ n < 297841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 297663120 1250 297661870 297661879
    0x703090e0622051506040608090727020706020f030a050604050f0c07020f1c0503190201020f07021c170c07090b030309130b1f0e040507050a030209040b040e031b0a0302100b 76
    0x242c0408100c5c00c0e072081d408900001d480c6414010340010501854000340001d41884080341c1a90070306401c441541c04000e4140c43e130000b42d00c010404540c041c1c03900d400d20814015180e140600040d0081c0030101e031090710079840d050015072141d402844040c050f16201c055a4103100190b030902198056404045031722851417001814a000c08200d82c101441c42440619142d2004546841c1c01442c03101894041d640180700c5920080b48440a0740c031990b80464601840c0b181c0451140050460944041c4c258910a003050200012007030041034001c1c000000c441a00d80d80d84100c0c41103c10840e1034550582040018005034641201040c071940c404d0000020b60341d900d240054400884503600c400c3c000c0156002ca81c0b1a50404041c002c00c2c04140c0d0140310b5032401e13240060452054551280903d640410403c20f0381d2950b0780402428080038008104410300b00003540d50320740100c041c60408880003420310400000121b40e04091a901d50000e100f80c200f10340c443c60282580d14030840c0c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 297664370 1250 297663120 297663151
    0xc06021e1f06080f1c020c0f10051b0102040501140910271e06080f0601052208070317070b0c3406060503031614120703090e062205 58
    0x88800600c216401c130f40780c1380010015005040e050035018080075191000395007141c1403082c0d05881c0d0760030100590100f142c91480d002103520003500c1038004e0824190030100f0304080144c246d01d0540c010000d88100341c0380c001c091901542080102d100ba803800076001402d240e0311045450081d40c00d0007013071044562004148083e000e007046204020390003d8200c903c0000c0104a8192401c005030251529241400c0245086ca0100c280c000d0042e1044c0e0400000007032000c502d444090b0703480345001200071000724107980c0d0100960b440301180401d4508012910402c01022141e20880c0e9185a01c024507a50554a03072a0135040c90b00902001c0c90000078020181d60a60130100c05003404907110400041346107258186807044640036085280258020040c24008080111124002d2544180e090400d0240c0300942d500308080d00001a066040200c7c01c0e008064200340c2c11816500c005990544d01c0d030341c0d80104402404107003a20881d01c1541c00e9240400116a0403441d0300112000c0351061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 297665620 1250 297664370 297664379
    0x702030a05060a0b010e040204030209270106060203070605090d020a11010c0f1b0608150d060603050703080406030f1b0c0c03020a08070314060609161701030c06021e1f06 75
    0x10542d0464006000e16901c0300360b03001940e00020104003509040c1c0d800c5003024250b41c003050071020f014001c030f80440c0081e241c00507003080c0054035842c0b0100f9080280022030361500042d5032a0040b01c01110a541003000143c500300c00064122002c2c1225030041141d507a090300e41000b0701201640b0f080c100203580080501040301c803080c0180c820303c00c110b0f440034205050303c2d11000307010a401c9001005a8030003404003140c18003200c285034480c2255585001d00032494880001c1005910060043c05a14400400e001241c0d020380200c4940762001d1000d40002100c4000311764980022002c000b210500c00ca071014400e5a4003180d15111348021442291660005041001140e00080c1a540200401e000304580c44440c885040c00303100c000e103000d0800c9400540020740060096105242141c00403100c0c81c450101a9103d8118420299195071079040c04040040d0a000e80401340c440e0a81d80b43c1c00a1100030a0007003103c0c0c0c00c000d0162205030048100b850b2001d400044811340d06c5510110703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 297666870 1250 297665620 297665623
    0x9010608010203010e041a010b1b03120106081f030507030f0624090e0c0a0308090d06050f0711030c07090b041d01020307030b011110110c03030702072402030d020702030a05 76
    0x6000c1c1c41040e0920640d0306c2c2c640303400c011007258942141c040115400040007002c152000307903841c01c0c40b1301501c1c024000c40d030702c43c01c0d00e1401401550b084030503030600005500c58004072180c1c026000c0a40b510b035200b442e10f20b4002a8000b900c00200103070720100081012402d00c1d19020540d41c400d01e004110503210442c4a40c020298510007001c2c944a044200300162a5101d14900031410002801d0210a4400000d0b010f07400c61001512602c1d00040c842d211707903a8170406030302d1070b41e1000701003140d418401c142d603a020f8400c0b00c0b4040840c0030640010701c054070010668045c005880000e009842c06c1c090201c0240030310003003d642194a81e0002c0f407919071100f044031007144640000685901c0e01013401015a081d011905050000d101d42250102c2d00200d0b207440e1041152001084013800c80404070030034800d0b2002c4c0c40b440e010100c10300c13145640c08640d4508442c122005c0c5403005800790780303260500c800d58642ca40980d004020747c003002e602d95009403075150300007010317204650015180e25 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 297668120 1250 297666870 297666877
    0xb0301050411100e01020c150c1522111002010e030703181410080c04091802090c031501030e0f0708030d0f020a0806092505070303240b03090106080102 67
    0x85a51610305652803030301d030520300f28407000c11085107480381c429000080041d45903510140e0343c90040c680a2407074103140d080754045950401e412030450714a41703050056900d003007400b500c80c043d81a0400d410315900d07020701c038074a40030581c000c803000c02c0c0c1e43c0030b0404104c20801c0030110601595241d14070031300404405d002401c0042c0c02a202c501c2d05032407041c40415840e010f504071802c0420a050782c030400c0c1e03c03818082da030700403c1824240120384503583c0101d110301503588820747d11030074550110390031400810400c0603607100752604541525034216001d81d0b40401c60703c480e4041110700c20780d400740d0705c42d42180350014034410a0b500c0b000c500400103810080310b5001840301c0e50001410040b4650607205c1c0d96112900f4110860501c1e040c81e1005000c060702404030707407146051030046801101603a2003404003642054014030400758008011b80181c01020040c0d000c40d103040c4030300301547d8001c82400e905150f441141c01216040030001103258101500e1805d5541d84c0303080106800e00e091006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 297669370 1250 297668120 297668123
    0xf0909070e090328050906130906031a060307140f040605100305040308090c0d062c010606090b0f032701151703130b0a1103031306060e1b0304060b03010504 69
    0x5580d589451004c01441d9032550340e0010020994900c1d00300e140ca52050603208203100458a07140d4803040c418100310003001642029001e2403030000000b0801c4050142d8060044800e02d02e036905541e40410140ca540c0984155021505201d294003071524111012005440307000f8400100719880d4000b141d4500b2854003c4804250344406120503d80c0054806901604e58001845450007001c04241d04003000c2d00002c3c1070b180ca6803006001c05d481658103001e0750038200e882d4102e1058010001c1e028200f10700c10000415030780c1da40490907141d40e40c1120110214100e5503482c2d5140e9001881000c1541058140320028808100000910030b00030360301d20361001c02800c10024200034002c4507111102401103e07a9100b00301c5c1c1850525285440012140c03c0f10300720b52680707111181a10500709042141704113000000802281921f10b40c50241c0450007940c0410103282c0f100c2a003061484150b80c0743c64400460003543c0e91603c00900110340c801e00c070381d502050110012001c20300f51003007030f0740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 297670620 1250 297669370 297669373
    0xe180f09060907081b280312030903051806040b0d0b0f060315010c050f010207080309060702030a020307080d0b10020309040e010c090302191a130509060f0909070e09 73
    0xa000c5a8081003148540154040c8050025a45040e00392030b07031042c80c1c05070b4482e040f5280c035400301d081e41c1d14002c8807000d0800e04040007000540c00098940d1007200d0008403010f211034140b40f10350324824401c00d0911685600c0e06d0740360050b07400084410002030844c15502c407104101c00300700400031802070000030404000102c0c0780f0417136508002110880e0b84042e4090030050081082c14410041d03c00e2070624203003800b80442480e800e0281c01e2000c107140395840742d8000030f44c1e41e00b004807040080d40f14464a40a44059840d981d000300d1300d030b129140d0301000685c424840030010070125402407507685440038000900c42004000f180714084414240e0000da0808071307000150703062a01484039550021002040300480000020340104081d0002034003d01541d042025403400551581001c2c05d0708607002c4102c42e111075544400b540c841c401140120504134800981d03410304a000d64051000144040f868400b80000e01403085c0300207040300090721a80340d000030200e0718032401c6402020704a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 297671870 1250 297670620 297670651
    0x60f110f07060210270b060a09050c0702010e0a05010212031008070303030204230915030a050a0f0c120309331805120a14150f01061e0e010e18 63
    0x5007640222241000c0d20200041c1c2203051114981071780380c0410095a1100c480c80c42505e5041c04106e00d251140c00c000d0300c0a18103414484216445000307400120700c01d03a1480c20180703c00d4184841d080e020b2140e0b501680c04101c469214000e40300c040c2d54004500542c03041d000e561500458900a41035005601080c0d00180c10320001a0340130b96600b01000c1c02200790300441f18003003c00c1d07000400404aa040406049000300140c3d0305202e8083c066030401d0885101242c1804c00381005200c011046840213903651300020755181c08030b8880100c03600f684030419031030328020308040c1d0003884260b0142d00080c02a400c02c0003030f11621011102d9170f6641c0c3c900c0090801c1c566040d4000542c0e0b004a8030601ea0312050341c50031038000410340c0c002c9900800d00160181d15103070a82c45c180400c1050b88003c818441040102048483c2c41812510156a403003504124500345c012080012000302000528100c290040c80d40550b00012400e900984918552550761203401c10a44050350712181025610 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 297673120 1250 297671870 297671893
    0x12150302030c101b06020d0c031a190f0b0301090518060a0b010c0203100506010801120209010b0904110a0512060612040f21020307050114060d1e0c0b070507080106060f110f070602 79
    0x500c608c0001c1e400505040000303000c6080440041c000313502000380314000d02da103e060041060b407400802403140300002540d10b5110104801e480d0400d0045040103464280020380d04051a0f10402c401e02e6400c001c1c20817519003540c21406811011141c606024140d603160303005883c10000792249440e0342000081c10b0500500041c42800182e008210805074104a000565100311000b8111201c1051441e81c50092102280c00b4003002402448501c40100304120100d403c800140303501140c0702d030004081c0d0740d04010010302c3d01618100900d1050554001030018076900401e54089010391425184c0381400c00c61506030180489071f08005800110b04071003000b009010f114000c441c040f018803514944400030454580134a8009450a81c0140307010320402d8031402044801078101881e00c052076103d107000c05176648000c100b00e801b4801c80b0700020360030034103101e10820390714190b81d03d83d02c0310366124040b144031841c01c80e40c140501803049115101c40d010007100e0f000b08000d401038450701000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 297674370 1250 297673120 297673147
    0x619020a0215040b18030703020406060f08071d120a0618050708070308090d030315030308060f040501141e040e070503060109020c060601050a17040312150302030c101b0602 76
    0x1c402050b0500380c06000612a60140d0804e40d5600100b2280c01c001d1000c01070300181c548030311580041c1d081031a181c404115a42d1002c03481e01c5540072a00d8840c820780ba0340030111640300c26040140341001441d440c1d050a07160000d14000301140c0c074012142d00017186c1c5c88100c2184c2d07244440c5d007185e8120f0200c0d80704002080c8803030f030014407500010705541032440d101c00c6200d2284110b01d9103d40d0321081217108240c0254410031003101003070102e641950300c038940901100400d491140c4a080e03518003640e041e141a0140e54141c541c2e03200e5102038160990b06021014080c4001d561020034940d2401d2980c0d2200d00c540d47c40b00342c94000610881c2d15102c1818106403040c0c00c00f050f0b0b98010800e10410782c7c000034503030341c00a03428a4900e039540688102120070810710f0f00b2100c180c40111041c0320034180d10009031840304111210030400ea19100e900059880c0d4070b40700007074144e002000c5c83d500340d241c0700454004402c000c0c00c110700340d80b415442080805e0314500044842607800718064818041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 297675620 1250 297674370 297674389
    0x31e0415152c150d05060106020d0305160207140f06070b04140d0207030201051e0d0b040c0e090402060c030708040902130905010308070605071b030207050f0102010203100308090619020a02 83
    0x842c03407000550444403042c981c4046200400c001c04100a50041100503103440fa2102000394100055468558640d01c0081d260466600403200081c1000040307a80c02e103a602d10342e1b0351483c0a40081490918050040000000034505550b200c4a9a040403003683c49001c01440910b04c11110109135250501e001e9403440c80c1a01565030a40c0200c08002c03103160006044010341ea02400c0c800d4076400c1c110b8000e9050b6691b81c40ba43d01d0701801060003440b000403030b08041590401100c052000c900e812200702c5180010403c0580d001d0400d4010030094102240200f100200000640e8940055501c070348810b644943e000c1705403180d0008404424280c403c000c0300103003c0120003481300307515588640015010740e65001d0806503844010804044c059694030038040b043d10341c0c1c4415200d0a040107511604180724082c0039464840489980e5131061003200d1052041c01c07810300c05c0a04517202e520903034001004081c1c2100d0300304030300751080710080450300364030748190700801c01c0940c13902c1032110b18103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 297676870 1250 297675620 297675659
    0x509150108070306020906090d0609170a0212071a010806100815060906010903141f020a09030f0c0504021201030615210519050f12031e041515 63
    0x16586801401407820100d001400c0329009030025846a1444001402c01d102d4600741c0796120007524064410403189030011140c9502540c01159164085c00d07c1306081c0c4a032f000d00f280182c0181c2c1c0200d4440281c0400b401e20f0502988030030116268018440d0900f56007a001510950301800c204001e418117401000058560300000d8141074007000c0f01d1080184000e131259205101040002d01143d1007074400c0e000a6821041e80020088400215900ca0589401cae0480c0d40c0000c03007203501c4481141c0201e60483d0900e80c2c4a0f41010b2a60706e804200c00e02e10401203c110602510014a599440c00540340c1c10070410380c0c01042e0352452804008813281071251a1620360100020009648a4210180c00e0800301602c901e01224516009052490003a1201d1840782c07815018418060001100c01054010804440351000f10019203001400f084503002003802d070011140d4045840801c0c81500b2520841b14900c2440584031144103941c01c6110040e10304094080c03c00240036581944c0c40e2a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 297678120 1250 297676870 297676903
    0x30501051c03050a03180f0804060e09010e06190b040e01060915020c04020309150a02031e090a03050a031407021c050406080105040b010c20041a010c03110f0706030509 74
    0x1c1da00d9030003400501600d0701030130906540741c03100c1560100c030b80400c8490a90100801d0488003541c60404101d07001400b0700f8000500014550400c0e003000d10b441c0703041e95240701155841d40e5a1404001804180c1e5100c0d43c182100e050000410801000140000d062184064001036050450013810300000360300c41854810740c800501e42081d000300b80440728003403c0d200035949030341e0850704518024100d41c640480034480400c0101a2042c0c0e070255000d00b1000e0400d14031620802c0c540d00b210002503031600040d400c04000d810000340074100400da551154140450b8500700c1007000c2c1a40c0b0000c03140d40c0c01681100443c09039141c101c1403000001880c0b030400c60304180c00c0c100c006003880c0050103654015075940c512082c050f07014001105071a64003030980c03620034881203980c909a1005184407401242001c100051000488030361008140069540c42100d05c49502c049501d00c0d04441850302900601c00400e503410382c2405410050900c03618041350908101100d20300c0c0c900760700c0a00303035103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 297679370 1250 297678120 297678169
    0xa120e0105030f060904020102011503060f0e0d080c0c01060509010303080709060513090905070b160605061c06020928030506011e0e0c090604030f06180c150504120303050105 77
    0x7081c2c3c0751401d904074a003501c00314001d640d580b00603401014030b01041c00038000e181100004000c21600441180201840148040c00c0f1600c4040e59a0098000c11000301c1ea034440010340c940303502405005d5904d501c200109400e130b500e00105080c4003081e003003500041c0b250f00402200380e4100c00c0840003001c6901d040e520f480b410002051149103a4003c2d1800c03c0d4a444e603c40c1885000c0090300c02500030107400c540d90300c0b031107072607010381c44000d02c02155080e051000140a5141ca0000291960071600350a0748880741c60380c0f40f0000f5449200e505a11080398050004c0f07525214490032000e064203012031f10f1460075410414030303245d0140d010020401a43c840c00354210a4a04004211900249510229102c5424204c12401941d51894000030007040000510541100c414101d41c0030300c40800036501d803034903000c603e540c6030a809450030303600724000c1140e80004c401042c0403106615126007800d44500900d11084207400c0b064001a0301d80740140035034600410100201c03003c03040000c55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 297680620 1250 297679370 297679381
    0xb0a020c0f07061b06140109050702211602120a060c12061401050304050f01020c100e0a1a090109050109060c09120b01140a0302040c0807080c0f030f09010b030a120e010503 76
    0x1000c01a00751044402c205450710308100f0542d13406c030b40030608650840413900d40c4c640840304018101100c44038010700c100304609686840780300b0b0940d0388281e40034aa80c648103150850012290050390201e8110001c618080c960300b60500c0140c450900c0307082d0204141c2c68006000f041c804650310031201d11850315808011040411103841c081503001c0c240907459641d541449070902c1c50b80781901800794000111884101000325150003519141c0504001d8503031806180c6070344d01c010050040142d4141c1440b10301440d418240164084074030000070030004510358a4074207640c40301d507045880070f84403d41c1c80b19254101607050058561100100300754400b81e00e900b40d00c840103201d54092045941d050104640300d5250040156030054000e012220350340c28010311420342141d25800199a1001080c41c031140001145c8041700b041c040e5a00b9038840003240c6e0810000540b040c0301c19903984a600c50151400c0c8591100b15000c1c01084001c00389030200a080d42c4040341046040100800800a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 297681870 1250 297680620 297680627
    0x120103030e0a12020907050705070e01030c09020c0307061a030a030e09070c1e17040303020a060c110a1b031b080601080a030c0b06031f0204050312040305030708030c070b0a020c0f0706 81
    0x142c18580461704102103403210364061b90103118944024042e800740040c041b0721841c0001001d412a4802c0b1081201d40c1c0c0c1d1045224201d0241078100d0445820400202c4042605a0010901e40301c413544002c00600e007260000c6d00d0726950440847c08564030f499541c1040c030700340ea0403950011003401e069071241c0032f56486848600741034005946188041c02141c040c80a120003145140c140340000580d00c503100c0c24040c5d9078030302c0c1d50030440c1d01038184600407954600c117100c0c150209904100504621043d56a005d02c400f00c5071043d00b0082102c0700000001c1076050040c000f003035402c201441a07a6040264850900e8816001480c2c1c0d6440311072400b00007a40442c11940302908401100043d8172040006401c2645004d03019001480c099088181c1c00b503c0d0f4028030031904114103d80410320880781601090160b48000381280e002440041c010076100030056500440d036959552801100b40e8480303e0710403064405c5402c080d8007051b0704000c3d50080103002034003c41040100f106034600794008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 297683120 1250 297681870 297681899
    0xc0c05040b060a1b02131a0301140a1a0a0906080601060e0904082a0106061106090d080606040803040e040b0a091212020c0114091203071b17120103030e0a 68
    0x880400100c003a01c03014000300c1200120004c0da0041000003144503280358913000c2d0140ca1241001803080f0884c111042c41e05104003402a80b0908903048940d940e8189a001840700c18065005684044800c1d84590f41c1c4589030806020550000280d046c140103802e840c00c84d058211900b0302c8180318400c4803d541e0001e059a020742e100250320b0b6a10740390483e031079001c1c491500c0900880805004030340301e2081900b002065030080d87d14124000420644907580c2d110507a003000c11500728615a6003140c1c81035550660101d00581903c4c6010703560008580b41d644140c0c0080d1001d5112000c0c00100030100100c25082501820188040100c0740c80e040c942078410080303034041c85840c0d1401c8521940d16010b6504d10905c480003088000082000c8000448045502c4021405141c51980c00a02c5120650707004070b2503a624a0710f0781c50b0b40340d2000740c3c45490348010307503031980300d824056070100108006200300042004500955459490003030200d0034001d0141e803150b40750640c02c0c00b41c100d101060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 297684370 1250 297683120 297683137
    0x60c0a0c0609020a09020a080603011b050f03040314030f0708060409050309220e010b0406060c03051b0c04020f091002030906161b08071a030f01290a0c0c05040b06 72
    0x603142d103441c0300203412110f00ba071000c800030340086800e048180c0c11210790791060310306600a10143e03064010359a02c0000f05080d40005c24000d000b41000d410b0b03c40040c59100d4440d003000e251309030220707103514600d07001118010b82d540321400400003805c1d171002216801600a5a0901190340039540329030b00c1c0e000702d45456005d41841105548400c0c0302141d210110020303da010403121000442043c064031585410354010307414001d0004d140c83c81240c00c607240d01c1d01030b5180c40c204071540040b01001541611a6503007031041150b80300c819645c52006015000803101c8141c0d0b51410302061251140e2840003050544d0800d20120441d03840f0002240c2400d500f154180a03d00030500e00916038410070105181c4946190001003600344002687c142030300c04000202070555021107003149103200031501040d0324140341c4010000031945809540341d416000b0680e0f0003808100d542012160021204840010451103020b014040030b0307260036019060a4600b4009040c200f80400c0b160f2046214 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 297685620 1250 297684370 297684383
    0xc09060d0305070312050c0706150b03011503091712072c010513060203040602120414060304020612040308061002010905060c0a091d060a0e0712020c07050409050303010305060c0a0c 80
    0x5443c1d04051040d62840700d8170342544000c03c06030500f038800f140325800a603012140c4514244000c00c441d0300e25600001282c0760303240303803031718503801c19000302403080c030040d40711051603102c404800c006681402c4480c40340081070161038603100203440a40030500058495000c0c080c01e9a174030300258241c90750b13070100c1000e125400300f41d82e2038580040320740e0700c0360003004030102d113454001140740e9501000a10442d0007507802c580343c03004034010b0080d40b403055200311001e0351564140da81803070078204003543e4031030f0006010742d090040d040c0c040c40d04000700702e40c11000904000c040024034a0b04641100000380144020480b156050781c0c1c80756103c9014004a19080c4003141c600d2b41035106941590140103d091440300c081c007040701466003e5816560548940d681c010049400f82001030030030712a940d00e580b119034a000501da4000254412450710b0f08074010307041e022629031524080c2c180c60f0745c0300340e00840c5c0d40e624500b041424031001074003200b60008104040310301e480d80300b000c01c1c03c0150049e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 297686870 1250 297685620 297685627
    0x41d0a060e0c0307080a0c0e01081b010e0402030f04031b0f0f020303090303070303060510051c0f0b1026060d080307020106090f0509011a0307031106040906080f0c09060d0305 77
    0x521040c0b901e088000d1850303151240795004503d1410104422581521522010074420b8440c103480410160900a8944640c0408590301600d10b1544903240d00c2c44041c10201e02c41c24030000070506a900c21508550259100c0007400101684108010800707881c0003c45401a541607640c55003c40030322101901d01074825031030304255581841200d06503035006080b00d0383c6041514018010741194401d075403044404800d040c54082c0541e048540303000002401e1f0701e6001410712820001c10503461440c80d03540c0d60b042a2042512188000d8800c0840ca80b1200d42d403415423000484000043c0c00400841c540748400e011142c4c944c11500010326912480035a2680c1e10ba0108900410716684100c5070681000040c0c803000342154030031805441c042009000d02001c200c26182d910203035071030381c0d6050b42c481c00c0d04101250704581c0c511030b800002044d041c07405543e241140c02b900d0ba2500406c3c680e0304441c400c06a4076404110100fa0b004055030050710502e0481d0000ea9125101e10010b0180078001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 297688120 1250 297686870 297686891
    0xf0c0e060d080f12190c1403011502010b12280b0402011d03060a050f0709080606060d090501020c072904050108070201090b0709050a140d0210020f060a0b041d0a06 72
    0x10040e03c101041220072410300b860042c090b2a949455440c0b100d0f04186000b00c41c0000c0c0c2c7c031504141c543e5111b1950080d04e5a4a003072403403d440702d44815008119565414890180c1e030b184010000240502c01c01000e0700d880a42260794500b5201c15001f00070420041359100089290300310036070140d02400c082c0c0241d030301c1c50342d10f12104180a14a0364940100420880070440b1680428015940c0a00303060243e41d0340c1d0416103c03507200340181e0788103a0090000078594a40140202402c2607044004210440c076642c805003680c2141071401d640c0e420451061081e0b03198180360004841d0701d2280080f408441c410403011610403402080d0412118000240140e0b000750080c09909910050620040c5440c1c0801004041c16009035441151402d10000e400440030380541c0c000040100100c26080c40c6908002600d040100000b01f0b500643c41c5d08052200244142c034410348000c2e1001c103c445205040208603807194607030303080e1040020105a40fa0300c0020300c003100e103a40f1550004154441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 297689370 1250 297688120 297688147
    0x406020d030e071e0f24080402090411031f06080c0604032a0315091202010e1b1807050705010b040c0806131107031e020a030c06110d090f0c0e060d08 66
    0x59400c444060303a159000000d100c2080d4503000f00040342d1003039800c00ca901695040350030f0781f415100a503100c10030b04081004610800c0b25070200c800000c0c00ca910f60384440c0d4215500001e40205940342c00e94072142009800c0d8144040100e00008070ba0080c0743c10300b1940c0f03104c10202d0000390f00280d48404030345482e0b014541e080e248040c503001803c40e00343c41402100072000e0902e048040302c1900440300c041c00624014001ca5042c0d440340005444888028069004010360045602d60b1010b664544141d1215101c203481d07004601c15a41d0030358485a0b410003500b942c1c040e001d414012403616280c1000c0c50f50020a194003e441100c0b0a114241700c00b603c08040c0c10184180309d0304c010b000031984c00305a001507104100342d0716103a82a0354401c034400309903101c504155003e00410301d20f0000000040050303210024440b0071968550801c49172034a501e00b03c1e074502e2400c88010740000420000d02c0104034407140100401c039601580d500e03280e0081159142c9403000109061404903400d00c030b1204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 297690620 1250 297689370 297689429
    0xf070903020a0e150402040b04030201052124010807210b030d0215090102040312050c01061e090e0607050406030906090b2a09100f02011b050406020d030e07 69
    0x1001800c12a10343d465041006103000142c552005007082004d0405850515009039011a80d8402d0920308042c50350300155480d41c48403030344405108000303611038511249516840d00589961200503202401740300d80842c0c0401c1c001032541400000420081640d900c507040c4828540000102e076060803000d04180b02030000c185100b90b06010f50030528080340d500060900c00c030004c040e603000841d1103c0800e030b0308030302c11804003400705003100000380813540c042c4004142c0c01e0440c1c00000303503565584580c000c250b80c82804440000802c11400c1111002c18001c044900c084180a00034608002002902d6481a880b0b0041450344410587c01031200341da01c41c81d12940c00c01540d105134a00444120308011524201d0b640c0c2007100c0d01084c5801c180c60056450020010f00146101c0300c1640d0186c038114115008101199200c9842e580c503c18102e2200062442d20340700c03507403102e040c034101a007042615102a01090301e031a1590850150001e990b508031444034244005810390704850403460314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 297691870 1250 297690620 297690623
    0x40314071703031803130b0c070f030803070309080c01020705010504020f010e0904110613080309030f120427020a0e0a090b09040f2a06030c031a1225030c050a0605030f070903 77
    0x29451b01c0000c1c540030311070300030000c8907a00ca0030b4034403103a02c900c1c20745401e081382d001c050030070030050001403095800ba038068410031340260440341c1440c003404000d5080e0380c842030044a141e5185d409020031424800b00078410010242003d400850b000e00c0032956407a401000608030140554500d80940ca0b5102100e5041d502c4c011504402034031000110350300d0f8005a41c2ca0300070b200c0d221140e00140c4010542d054001d50784a0244e00d46450b00d038070789000181242d00505550030300003444d00b404005100800084e02070fa101c103050800624104103120110703034484100c0798180200301e0355903074030505101c0e032040d8000c5542c500123031242040c0d108003c4400110350300c04030341541001188100c143c0c44040394020f5030280204584050124240c035510280c01d48000558030032031106140c00904008585d0a4004582551311040d66a45901502104003d00403103858003d005100003241540c02400054800321040c614100000340280310003040c07130750ac0070300c254041041d861007160743c00000c0d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 297693120 1250 297691870 297691897
    0x1050105121c0e0d0c15030e0d120b101d0909070b0315041401090e031c0b0f0604140406120b06010f11150a0c031e11090402040314071703031803 64
    0x1903c46182c22800c1403c0c5d4003903501c10300081c0c03c41e0b440441c840d0003050b90820f006c8026008174004040c003aa50208021400e0ba5416203c1000751441e0325800c00c0b8616a400568a040805030a01300942c01e01c000081244c0c01407400c4410040d00000c00a45c00d001c5030321107041203070b4a41e2901e01c2c120050181034a580d601a0802c132413060490400041141030701c440440400603900e20b5101d4039968400c031425107658030400c00038802510200c0d40405440c3c0c00117403c2c0c54030075852000203240c0750700a0304010304003070003681e0910f014103082c81444040c00440c1b8030100140d5280d25190080b10b0010f207500e04011a150803011503502c42c9030180c25452841d0110342c04d50084c02070f041e88025080710304003070341403901c5e0300003010740d01c41d024140c403450762901410071a140780c080c0d14000d8265000349061001040005001684172480148010350080b848001700e10080802c09080800b107903c018900150304c070b403050102101000310ba4101d40380c801506000e0726004406070440c0281c0c069880301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 297694370 1250 297693120 297693139
    0x2d070809121b1c060204030c0e09010506010c03050a050c07180c050405030c12030c030a020a11010804030f1d06030907060f1d1e06030a0b0301060501050a0903060c03110a02070801050105121c0e 85
    0x7000119423003001614140703480c41a141e96280440d0707080381d80032140b66000900c03032404035000c0b0780038800801055640e444e100b03107402070b1142410300c0c101242d440200e218094418030800c44174144030340544680350b80f0300702e40b03040c0c035150010780e881c480018194480e00c8041800e610141d020402c4400c07603010442903c1d2203660520307001c1e4490f0170011058562600401403103009603c1356103018400c0da455211000800c14086c01200c1011604444511640a14000c4001566040302840c41380078030768010442e0391304041000f00517407604071880b002d1200ea040101e151f42040381d240b00d0701100550300c083e4103086840b15440134400340707041a40c1000f4004280900d0078190f4001c00341d00706007600203002440d507a4004650b80d2084101000c00506030304000d20008103642c0111060201c64540400c1d616001c01301d1054a41c0105040d20247c0e100200800a15000380a01801880c049814070400020500820386440c03003450100000c05850303120201080c01005000c402d031101500d040d15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 297695620 1250 297694370 297694373
    0x902090702030a0e04090f151811130e07140607380112023003030109050703020702060a05070611160209090a082d070809121b1c06020403 61
    0x1180c0d84190f985000040008205442d035051500401015030361000c03000c0e561040b640c030307007503408480032000b14001d503142c0c580c0c0b40d00032654010844843c1e00801200404c1305000040201c0e8006c4038496400550510240d8901c1c1c6d200801c200b01241c00710700103404034810080009005215411000700704e00c0b6101c0681140c020540c03115151200e90900b040e6400c110100c400b00440400d20600039007044e01c0550800500f0120358200c10001006d102c5101e200c602306000000e100421a1141c0710343c40840104030411303850080b00e800803564102107140c800d14bd00440c016200300c8424405001001801e01300300906c4c0d51089000b415500a440c0c0c4413036140451262100c51006c090788900b03034040210301c03241c00c0414a815002c2c3c1c405045450700245c02400b039160300115909001803602c1504014500d03200c1030042c03100a109101c031944d5104104100013510200429480c0c5a034000d172184103908800340100c62410f8800c4030b00a800604261006004024103036000344070a001040000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 297696870 1250 297695620 297695623
    0x6030509010c0e060301090213080a0602030f160c02040e1c0f03061d0a09020d08030a0c0305130f030e030106120605010807060c080a0f0c061a030d052703010902090702 74
    0x14000c4480340000e00600031410302c111450303a0948421980304004000400038500c2c10790082c80038202d00720780202043c0ea02c011540c108440c10030306848140c1c00001300203000c03808040e007542c084084495058581c00d640e034020300c81c3d028500000d0041d81d5904200300c03409000c2044120742e1161940e0201001c1c41c0180040006000180b480046030070700e02d0120b6140807004c80c4449201c4040d512044680c1d482619002800d00c0b45016a002501c2d404040c0121350703540000d602c625004400441d060040c118000e040710b10040981c08000f610b2480500090012800c50303440907058946039221001200000e13006203047e900c207000c40c0400c6900e4204228803a00708d14122080d2000b503665850380c130350040e1000d601005000f40208010851070b1040c901540f08500c1101d0705180050740000a0f640da4002c5a03406000b10340309180c1d41100d01098501088104100116403803e80d044c503000c00c41c0030100300c2031a031000f101000c2621203445680c500354000e00e08aa0020220406800d046401a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 297698120 1250 297696870 297696881
    0x4090b040207020d050f010e010209150a180b0c0705011b060c0201060f24080108031b010f050916090b01020717030d090317090703080d18020a0b09090906060108010b0309070308040603 81
    0x1806d4079406d08060310f80b041018070903101c0400f8041d0040f2010311411a413982da0341d1049001400b4000480c42e8910112403554242d405003494003c0d85640b406401c100d1450160035a10184c100511808041c03512040c00d0240c100c803d41c40304010540d2046580282e000d407182d60060f4031340045288000607500c008511a0300d41d42c0701c0a002c4101030078900421034140000340a43c650fa98800c01400041d244043c40225988990304000500c8410900700102039403c1964401c9030350f80030481c001e1070803a2000100d002040702000030801400d080c00080d49032102481001380c44240c0c8200721100c29011b0046900d108420702041100200b01e141c064521004403480500c004103020009812900c0040c04000750ba400001540c01c1c2b9811003901e4018250744403000101c19032044003180140c481c9201c084c0a418200112034440041409005512500505e0801d1380e9002c40280300341643c1000c3c1d06415aa9642d0382e0756036030741d01d4101c414581042a48018184000020005440b69069008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 297699370 1250 297698120 297698143
    0x120403170325021b090f0609190501150e01090509010510110610031a060d150b12010204180b060a03050619060e150a09051c0204050c130e01060504090b040207020d05 73
    0x20304c1c0640c0690003400504030084420b204444400c0c00859294a001031400741e1021000c041809260816440030040e07031001c0e407001c0d0306030b03101c030240c01c0449800c100c5001e480d641c00e103001091145004e0000c5d16600f010300c6046c2c011036034480441801c0d4410555180325220744001c542c110705103100c00303081c0780f405480151200050901c003400c50302440144503010b500010716078a2400403544580000035003030721990010320707035803010064113865104030b101609482c10f0005850f18685110004058800d0300c1d0070f4009460f141003c5850359070642583ca80318007030728000aa95803560080b420301c2c4211903d0019000c0801000141e803a0700201c40900030000b507452099803001014002150302540d09580041945a001801030b420400320042e14071300401d45030719412030300c1d40105045402c10f455800031940e000400710703086d030780d4000b91800501c00c0310100e045a41c508403006210703002c0d030b024135403584d610350392102c0150799980c06440595400800340c0d01e035030a21f1301c1c20075956030b0214003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 297700620 1250 297699370 297699403
    0x15060702271e0403030c20010501030b150a030818060d0c02010f020304020d021002030d0906060510050403050d1d0a12020f03190206130b04080f12040317032502 71
    0x30280c200315880d40c0c0c5000803025000480e43c59540d030580c007502c1034003014010050340210b440c88a110b140203081840061600000c2c1650450811451460b8020000c0d4000340009000d050182c5540300c1d07440440b0303001031120344c850000e0810a1030900e0540c44a513405580422000000c00b0954803581055216400801084452400b428103900007120060360003c44482481c0144c141901c0e080c11a64040c03050720f00d8003140308240b0044501e11203081c0e5142e503030340300c05000906060000003003405850600c0c070b01b071030300e1941c5159030741c40901080810001e114100c802250500c040184900304001d0110f6042ea407a504550400b00300c01c071041c3e105041c2c00b581d00549003008100d0040c0f000d2800700441030700c5a50b80030701600340d202458010b4004c0b18a0000240110f42038040d0000e402d140d009406001000403001d4609008c0c55405950480304200c02c0001403604988821402d1141c5056500e81d51018406038120550585001c40d0102c00003000030140d46c08251100185407158 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 297701870 1250 297700620 297700699
    0xb04080f0d020c0906041d030a11010b031c1803080f0903010b01090311011b0812010f0816091a0301240801050f060d0510090b010501200615060702 65
    0x101240d490464480f401d411202d03043c08a0000d0906802482844000b61400311790320341c0300c006540c5540d005c03540f2500002c01803640a071a1800a000d80340a810044008020745d00203d018007040502c52042c81050000706500301e1480303080042003400441c0c2105101e41c540500c1440303e085903208201461082d440c010b103030b5800350b020f05601e405482c1c12017200142440703648015510083c10403090341c0882d100c408d8590001e00c2850007484010310410440c00c1552400a0015202d6a103822035065500540d1001206003e22406103040304c444020101d850b2820484000d683d52040d9892034165092030380b0180001d4400da03089040c0c03d004a404401c07207981d0055282200d90544030042c16020b0400420b00e90b1500f81e420003100703801201540e64401400044504940b6241c0040700c1c5c000822004104035070700844406102c5003001040c0005511000b64151108801060304501c41c0300d042070b600c0d26440c1d020903036250540c05008460029075502e100c841ca114003910001c40c490200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 297703120 1250 297701870 297701893
    0x906080115021e03220608071103180a090f0b01020c04110f09011b0302010b01020c010c030f080c1b03040302040605120d080a0207080d050f09010e0c090901060b04080f 74
    0x50051144441d2940680003030503001c1080d540c000e4103080081254801400f510600c010480c1c1c28000e641e403140141188a480c203100509581c000600300d4060018500c20600c07a60000b10803111a541a0001240c08401803070024105103c29040310b000c2c1860101010382d01c0300154040c1035428800d8007111206142e070f80c2003009075480650403840048040c00030726000c0b50b2801c0582000c8905050154500d141442c44101240d004081640183e46910b1307a00b8040d6014030144220108c01e1800c4240403482c1d880c040d240b01e040703850b100e0803c84500700003800ad8082405803002c3d40170340e1305000c80090318a44c410365250400e02041e03225030f2400100282921340b0000c1954001d1b8140098281e10340fa0240641e8121f0b0002c051064050b02000400009108000181101d21842c8000103223407c0417152002c510000910880003a80b4008809500a50002c0c9003a508041144c0021030303a40c9000455016040940c0081e800b5640070801050381c0c000410042c3c040103504044680c10040c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 297704370 1250 297703120 297703139
    0x60604090903121d0c3106030618120306050918011103010f0f2c090c150a08060915040902191d0903090d060f09020a0902130b0f03070c020114070309060801 69
    0x160f05000904890070b010309101d090000c40d14200703910310700b2400035051b03923a41c4420041e1010100000e8400080302448020882185014141079070342e40303020007c83c0c2c104004500312901c040c022061042c40032120f844041d0094000b0b20100809884c800c0d22940e441081a030000050300a00342c109502c080080740f107000c6074900700036944107016503289104152803008203084029001100c54090014900590345944501027011a0035010760359481c00e010384020200717803000c0e29081c864007103403080c060312440c00500c2c0c4861003001c44001914090a100103030703031040001108810407860101c000783d8041440c07030480b0400352204100b40680c1e110040c0a480e0310414079160b511440c05004040030a07001d500c510300e1002e10b460001424001900000c55505255208100740c0d13400003402c03d400c10000350a0001090045844c504080b1161041042408010285010840643c100c4402c0da88a07280c030340c1d054220b11510320342c0c0700440d0500074030040c054051000803c45020001915110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 297705620 1250 297704370 297704389
    0x3010801060602060f040b070908060708070801050d0302061501050706050910230c162001020c0301020c0c130b1305060918030307110c030f030d0f0203060604090903121d0c 76
    0x2804c0032071701e85643d41d0b079403400320506010b0180b01c00c00075100f8011034003c108201c1140100314a46600a0034a00407034010151301d8141c0250340151481c10780600001d40016076580c00015282001000b0405c00c40102d8580c0a00d0001401441c00e08060000929000c0ba150028a20545062062a400c204a0401c00000000310f082ca0500040001d00c05a4080c0140008080c0b00c5c940c0c012031006500c0d11588521910f003a48036501310310720800110360301080032a40c03550003035009500707042000081613111081644000e015820444404003509116406401c1c54440245018400110180990700911080300c03111300408810001c20884c0c84007213072040d10151540011403031a070325000304a03988840e044699a843c8603c03009000e45940a00c80142e203584140003c50310303081380710054000c0e03960311081c0300c41d09403041050150a4450f041224281c60240401241d109030500e000c07a80300c8414550266200c2c50008107080344141c83c003070301d070504140208980744001001c00f000040035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 297706870 1250 297705620 297705631
    0x30e1213090507020a3918090c0302150a030f090c0605090a0509180124032a0603060806070e090703180209090a0b011203050f0c0102090d080301080106060206 70
    0xc640340100320304295504599408601c0f481510f003d4151a5154031004650303c420182d210f40601402041141541106610400e11016213a80341e2401e8031080b1301900c0ea07038886207080d03210146107083c411100074400c02540d000d00b403452010444855590745400503440800001c0c24110740c1980d0b910140524080d064000208081480c80c041c0d00341d500707501c0310400a07001645480009081eaa4500000b44241501c00f80c40b4040c041e110300c400d00315845070050074940803000c018400c1170401020110181c81d480f00c00d034050045d54010b0a0f14440e03040544080425405e9400320311745506030850800c48528100f201c1032511881026695210000d5003103810030100d90000f070240b4400d401000da007041d6090381c04244c20b11500400c03100d0004030354200d5070b40e102e091903c007004003c17100b1030f0040c00d0715110004401d14503038000700588654070190386448800302e441031135480294125003034644001e01e03c1294544500d024002d9030802d22a401055107044000540140080340075413181 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 297708120 1250 297706870 297706897
    0x702010207020a09050403111b040f02190c0f0b16030c02030901120203061c050a030f0f020304051311030703060603050601050414042c061501111f0b060a030e12 71
    0x5081c02c00c4c07034000f04030081050301009020048222090001c1c00b0054200301e030703010040d6400d50b40c00300b804241d441021522070360031720410100030001c286043c241d40f43e030660318115290700c0160a02c04003180b00e062000c0c00c1025140140a4411819a00001071848a840903c160566480103a0b1240100310b10b09001c1103100b2030a16100c0d5140d402954030000080442a0b9140c094039143e840802d039610440d020303801950f000341416004a0482c6800c0300a181038004450f10510094980c0181d04ca034900a410401c1c40209071013031500404031000501d0a165100e186c00b01d40100500403c5c420040420310707000c007044075944250b00712400da03041b62118901d407a00702c10601004203006001e401005280407071103913100c007003a03164419403000c01c00103040030f0810a50b019400568219014107202d00080754041e184030200d103094042c451081c80000c050000c0030300c1c0010f01001d10001d6030001d000940d0382440d98050f03125182881741c0c10210b49000c2283c2d540340400e441441041d9000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 297709370 1250 297708120 297708139
    0x3020f060f0f010515030633031014010903080705012d1a01090b0717031911070201140703090f0b04090506030601030f02121612020f0f2b02090106080f070201020702 73
    0xaa0811810410a0010250450103230324510040201d05030710704600183c442030000148119226410305990140076450342c0070207103105050000e04036090611004241e00400b00e031682c1031050079881820520f401c05481c40c080e6100030a15a28200ca01051446103484c150300c0400c4041581115012018107071641752b00c0324145090801d00d50811102101c0141d150740502600c0c044645c0558010003ca240000200381c01c400548240d0740e0010060744c105c0014407030b036800b60380e020503400d0100f021005020b07500c038080e09040b280920550042012044259800584c404205004204580800300f00308003a4551008164540c002031102420b00056100c081d80946440d17480544400010360448a9801c4400c400c020050403983c8401130281c20110480b00390b00f0441e80c083d40705142251380010f0901c140000034034250060030100201e241c41c2c070540e04074030300748084800e10f01e13002800308245607540c400086c40500100e60200d05800000d001c02e08060050082c7c6041950007001070b102c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 297710620 1250 297709370 297709381
    0x20010c030e0d0c0302061b1c090203070b03070c0201110309030a0b0a0b0d0c030821070c020909010510031b03080d06330e0604150807090f0e06090403020f060f0f01051503 75
    0x1100101f031030147d24900010442006034820701995543e8103c0642c4010aa05110380105810031005a1000840c038030300700100101240d02c02000e080203a42400c01d00c4208501c1c80300a032131070042070182601445502944024491003085251040c0900501070020021810600945080d003050052042000d007a0a000040c0004080c04c2d00034403141c0d03085100f0000d020322030b038a6441640ca680120b03001c0346030355007541020316500350701c030040400a001d107051003d1210440e50765448042e290000000461428001034030313082e0000e581100281e61154a101c40d050003c0c840b502c6000e04c00c14544c102c07201a0f0381208003592039076003595240c1211102414068034200e540400e0070390300c032500b00030100e40449440c0c0f47c0c44511b4245d40d64601149031529001d04100c1e1a07030000710000d840e81c079041240109140805078040826581e048181c0c44614060f403900350104200c840600502d000c200000c5a18a181881400f070003540490356642d400510451035a24070300c10300001c0c0200000382 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 297711870 1250 297710620 297710641
    0x6081501030b0918120a080a0c0201020408030f0912010e06040609020415090207030305010807081009050a02120616080f0403081b1c06050f1020010c030e0d0c030206 73
    0x111002010704020428218650004142d0f41084500c100040110802a6041c0300200544644150300b0314240d4500a19071002400c6183c0c02410180360944803104103258a1013901990010304141d02260740761405e0203280350480d00880c0400703000c6d01e21284182078002c81409030352400d2500d180030b0582c81c0c4039034981c040a04208001640c1003500d4100407144042e02c046004010007002e040161580c9151400509840c01030784900309031380c00b06005000c440c001080c406004000b11500089107002e0340b502d02d04021580d1006075200c04c03070a4202070f01003008601c1c188100d80d0f0703200800311501c0352401660054000c1c0d9403581c519105c4800100040c1c024828942c001c281c021240c842494482415409070344004202d0380b02c40820705641c210a0398901503500039020032110022107503080800b08520400c0300d0001800c00901d8018074400221a080222400c00c03080000d100c2c00c200403030054040d019000311b00c202d1388109280c00700c1241c0305804c0c542c00301d60305074060030755920b4010012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 297713120 1250 297711870 297711901
    0x1b050901120614090a0e1005060f1e010c1406040c081213030f02010c020405090c0a0b07210519090f060e0f090a0e0304080610080703050c060d0603020d0b060f0a0608 73
    0x80b01d09903550443e88080701402c01c41147e410f400c0d9003000c03a452404c03005120304000742c80901e9010304003460358040201409008200041428a13283c601251141071580714140c519400d414103001c4d0206100502880c224a0300548554404807081d40b061400802c3c0c0510502c412403a40080070081400080c04219a82072120300502d00000980b40540018080324810f42c0c006420b58001250341c045404c00300084002400800c40060400310310f900d07488004400c001403c1403a84003900008181e03030066080c0c9006c04844400900400410303040a8451080e0b0700840b00442100c150009450703200e042100b4007000050080d28480e45d0060610075200c0b40907144d01034007910360741380c040c0d000f8081000e84000c045920043c0007605203440c00313070604d0000780c00442064001210070f201003600091031503503100c402d44926a031401d022801d84024143c540000390700c410147d00390800e20450107501800f41d40126411f0002500b2801040390020080c0b01f10804200c940002980011030344046 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 297714370 1250 297713120 297713131
    0x70f12020f1c05010501060f171803210a0c1e12240b03040c12020607020405040b162c0406050612011802090120011b05090112061409 59
    0x1a1074500001c00004000c1038800d10400382c44285804080e06010090240500500c038900300132580d080b4401c001445a50058522003004201e41c000c07901880d0044183da56030048103069030f03141d10680b0340c0d00182000b0515008032510b2030a010070b80d0034403a4440c181d040c24030742d240d24030300072181400c200520201c00021070622040035000e50780b041d1b07503004000e0000094156129034041c0b141c003550588407a9000811910780a104200002e50784e031210805131440f0300407107412018036200282852080c528025041820a4203010400c01c011101c40e00620f1401d41c51060b0b10000a405c40301d039001110604c0c0c0030380030324803440c0b0540800c800003080248003502c00310791151144081081548000803a6203580c05c2d280040202c0700035030072210101a0000001d51601510200080c02c1700c0c041080704c0110800c0c20341d100414031003584590354404410f40c803200b0008000801401d80c1e009540d005011504850360030488440c0751003480142d80303044440b4006000702c1014010a034200900b03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 297715620 1250 297714370 297714379
    0x904060b0307090c110303040b060d080c16090c08060a0918080703020304030215090d03080a090b012301020708100914150103030e1012050c0909010315060602070f1202 74
    0x403004541e840a010400107030152001c00300c1d59000b5401c00820184803030101c8140c50304207000b81302c0098405003010740c201008840f20310781e541035410a0345061007080c41c0e990b1644250b242c0c007001e202c40d411380c0004a41c0104000c01c01000c1401081da0040c20071a020380d40b02e8802d00040c052901658011541d04002c0841d00408203403e50750010729520890068000d070303001082c01c10451810003a901c100140141c0030754188021840403420100400d030f801406d012017034000801c41c0c18690b0010381d41c280c01c40c031049503550755440000042000c2d5000042e0b5000401d90f2000b0301d5000041a001302e5009000500c540300000768480300500131401c2c00c903600b48a102294003080e60422030042000014803044400754914900a08008613414141e801104500020030343d041c0c000451074905c035408000440d8a036512403080074240b1131000496444071800c8004000d0122140c0520039000914108205e1641c6580090b83d540c0c0c0c00784240032030240000c40a2088016214031003e02e180f0181 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 297716870 1250 297715620 297715631
    0x90102190f3b0a0b0708030712050f0103020a120506010306151e05040606030b010806010c060f020708091327030909020301090b010210060807050105070f02040905030c0c0f010c02090406 82
    0x15212a42c412045025010079180300d00c0c0c440d140c12100c1c405500c054219140e001c850300d440031105982c0500d80d0060075011011000803071310341c0150140200c0912207081005203190009446840c0d11081c04203a0103100002d40205010100000200985070000020036041e03203103540391030142400c9050b1500b0000324850014440044114a00380258444000d07540395082c03800744003c4903650362080c42018100202d00c07800381d0b00591300603000042882c0862600d1000c0c20140041e040c400302c6140308038030008000080c460000050400c01100301c0d014044a00c1580b03500d8140c4031440c0c5082a041018081510500d880c03d50950751035201c1d0034240c81403a41c0301045000c0360000d9011a17125074580c4403030910740da4180450f5603026100c40342001400d00740b070440c0d5030310350040c020103041c420000345210600082c0c80c00041c4941c1c0c0100140044010b41c80c25584980084d5080d1580e8031905610796490319119000d002a25810781d580540e040003602080b0308004003410039540c256880 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 297718120 1250 297716870 297716897
    0x3060b0411070f051b0a030803151002070311060408120304030c020301050a0e1c1d010e03010c020109020a09051909020d0f111908060402042a17090102190f 69
    0x30340001c90054000340319a91213070070002c0c10b1420400c9004800d02606800041c15542c0f010200162500207411984a68464031044090146900c07250b60200590302030807407451b40002c5c03500a4920804030800c3c414100011300c07815000b24024080715130080750f0b580100c480f00c8c40c080c40e4018000e15141d020380c140380d008203086800c00d8602d400c401c0d03120110030021706402c0101c41d0250b240103949100d00d40c00503400400d40040444040381004248ac128501d07a88215101a040340000b00200702e110142580a8000d080c000c00407401294220000144601e6520410303214200840070601c1000000c100d401c0100395000d000ca80c007120b880300710f001041880c4808501188a0100d8001c1c613400c0e0300810000b80ca00340401e81ea10185c005060007a201c01090040d04107505460220700c0511105003203032040c0290003101c1c0c01c0200c03625155441c95001b42c4140d024402c1301001c0140c0e4071a450302c54281e01c07609481c0701c00603129020318842548141000c00c0c4001462400c15000700c0c21 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 297719370 1250 297718120 297718151
    0x305070603022104081206030a0f020f01020a081c060501050403050a0221060a06060206151c0201020a170316171302150a0c0204050601111509030912101407050403060b04 75
    0x9540645408001080f80351b100c11120000c60b0f00014120020100055259907009440002d003000a0241228003e00001640200400701c0581d174480071036911140b0042543c06444070342000c141c512420a980003070b8550261080310141c80c0c103c405025003816680074029060402003887c003016122990246050710140082c9009640c7c40c500410b0740e5207000402843c2c518041d04240c0051980070800c02c4a40d5a100e40c0f1200000d002c104540346541c40c00182e0600300911009028820444000c00c520f8206030000c0d40706018005052000303205404c130860702d0380e07003018206141f050701001041081700c1c81d0101890540c402404505080c0345c001a100054000c2000070010450f94041c5604520f418010980d2091083c0f03170410400c014a20301d80d9407140f00c039502c0d00d40340340c1c281c001c40c510b120300b030003142c101c0040503000450307041410132490355500d5801e0340680d0962078540300b55410700c4242c0750140640480c3e45d8070f03410a425130701d03210300524080100795401955400b100310303020b44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 297720620 1250 297719370 297719437
    0x50c0703080a0f0801091811041409151e010501030203040213020406020a1703060105090d0312060b0a180806150f03070b130e04150504140601080706020c0a030507060302 75
    0x2256540229003405800141c03904c03a040e0041d500d202e05110310850030fa8aa01040d00c0c18541040c0303114201b50b0301402003002011301e03100f540071540300301007081441040018210500d0900c081014010350300c00d0740d0904081c81000c03100140a00c000c004000d590322903000341d50803c2c0000c10740b40c624903a4561003002c03030b44642c2c048405070f04003c0c1084180240e500386d281e54040c1e203a100a02d14540080002d20a1140050b081e101d004e16400c490241446003060340c00340d44000750704100084e21840c0d0340301359400502d40540003c00c1840e0400701d40d802100500100c500800091a00da01e510290098007011152402d402001440365070800399001c02840340240070301c0c01c020365640f20622114141c01015000902c503d0744140901001880d002080381401364003620000c1d0b6a00e0310302d0413112021200310f2242c020300c0b802d070020510003808200e01080350856021581e00100e0740c41400070044c05844040d0440d04200c4040140c1e9001e40c0003420100e404c507002110001000101608106 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 297721870 1250 297720620 297720637
    0x11030316050120090d06090c030b01090204090b04021305061c02030a0e1203070c0204020904090501050405060609061017360105070801180e030903011a0316080706050c070308 77
    0x291550004012070f880191400c80c0040007956407854102c070040414002c46032404014081c40c0d82d5000b031000d00410000c3e200c0510743c040e44884c13455944e128002c01030740190058602075898151060b034070740707094400c0b10f07041e030443c905d50180c0d14505170410503250000544140807041d0142c0703200048ad810b20056100b0001e510002440d18019404186801c02d1655001e400450401c14440c845401c808540d04456045502680e25149103010034040c14040000420960800302444200200401c4051080d942a6091a9107030703102000c000d0980401d40382c940201d0315a507000580d510503118039551000344002c6020300c407009500c1e02d039411009524111034000492502c40b40f00c440c280217050b080300180c42c0440e01941040c0c54a0b00168091082d21407c60fa0b8881050042d60180180e991180c0000c0c001c2114084a00050f0110f6004016440c403d004aa100380c54688000107114250740302c0c00000c1c400303641064400e50340c50307102a0300c545c0144240c110000006002e01d00034200e85 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 297723120 1250 297721870 297721873
    0xf031e080114030708070b0315060304080315061603110c12100e01050f06100201060b310b030609040501140414010c030b15130302061602011116031103031605 70
    0x250b00d803144040030140c004000d18469040381c1410031a12400245201c162810b00750b0ba141d51342c1351111005601c80d030142d0400e4209070080104001d210418014601c1303183c203000201d5a640801342008443d10400c100240c01103c0c45160102080c454a0003e48030799240781141c0c0c541074040001035140c0210300c000d08059010115081000d80035005200850311410028407240c00c09080b9a003e05a000b00010f00501d200017001c1e041500c01d40091004005998009a0309c1a12050141d0701c048260094001d02c0c1800c90381c0c0900d810b06a0154040b106e22898181c03c0d6110103040003456180600700342d41543d00e41c2130100303c03000d009035844c0c0a18410820b0f051001010300303503035080d180c4803010082030501e000707281c100d551102144481803001d146040b40c0d0714440030718800d58909490300040d40100c0c0104e0020002c46a00340e051001138000d89504480c00c02400300c070342d500c101c1065030740104519076004100007104140e0231980d4446c010150b0341003440505100f11012400c05055a26 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 297724370 1250 297723120 297723137
    0x31b0c07090b030d020607081306150e0106090b1303030503100b16231002030a0204090e01020d140106051602060702030a0525050117100503101406040e0a0f031e 71
    0xf85410070001010031000e0010b8103280c504184040c10200c4000c1a1510445078020392004000565100500321010380c1801c9038a10780343d0204070300b141d009004400c08103115420200d6009259401ea80e0a1100c00c2440402030b8199907003140d507900b001c4c1121081d900200c0010a00d801401c01030b004070200c0070607031140c0301c8044c105200d94000c0d080e0058820310324481c08409000004c83e50b0b0640e41c0c0b054201507601e4546a210740001d00c1340350310505095243c81084c40e00d03003006400500320484001424007141c15404e411503102c0c0028890710000c50008c20590390040c0c0048860404680006d0440e03050140a0b004241455070b032a2040300e1a41054007420420252840810b56100c280821f00300394030704043c001ba00c42d09100e100e0072030046c110400510902e440c2001e22010340710107011f07504400c80c0c41c4142000740c460b1003503181c02082e9280c00568141850b100c1d044050f1150340040181a00e00e1301c0342000282454003e4003044500030444480403e4090b84603034007990344d9241140e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 297725620 1250 297724370 297724391
    0xa05061f1a040f06030f0b04142403190611030601120c031b18061115040203210c0601050d0309060804050c04051006030e0607050406110f0106031101180b031b0c0709 73
    0x44420754619a82316903e0102c0002c00c0e10b0074103460582c4a0754036406403e201039100700b0000076005c8640c860b681441501800d0010b8406154a81a42403140000307010005180e01f05c81e401d804100c80c1e0500107660075200c407100c85010341101000122078100000d045c3c03c041025003a0082c28011800402c00ca100010041400141c0820040110340b5008032245030584100b6159100043c018034822890000705055503000e00c072003a404d400d200702c00c404035803184800b419079400240c04551b80f401103100004040c00c01840f4084525810355460392087e041c25826a40140702400c20f84071482443d0001030107407614421b02c0e0046003d560040502c0d490403000030705071203034204800c40a8010009002c136130751b04082954162030842c02d081510762001000c441c40c0903001d0750380b0000d941c2044000030901405090600445c80c0a030380340068080c01c8403900503682d20a115041c50014200001039150203040500e07400404134070591440c2c1040703c86068906100707030700a4280c880cbd03503034002207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 297726870 1250 297725620 297725651
    0x11060d15140f0109050f0f0a0806090a030f0908030a08091c0e100504260f0109080405181003030f050714060f070c05100f0209030a050a05061f1a040f0603 68
    0x40750b44824a0011905402c1002107516151941d00306402520720803150107455a80c180808060001c410841d211450302c0641e4558230700e0011010f801064210840d544424400d400a9040e1030503040110310b80082448200c0c0c80582c0101000706c207014008010030901540007406032a1142c956486003500c0c501020002c49080030f507071036010711104100403c110008a0b80156035103031004000801140c1280c0410b0924020800c994110352806910358100320b0240050819a071b0269a0031507140419203504610348820b80c0d0703a00e1000411501040000c3c80395503903840425091600d00e0030b1850599451840b00303551585a8440c0c1c100104201c0302000d440d02507a0b020245262450008469482c0c09480300c0058110b02d101d19125901e0366000c0c02e03a5012203045840c05012101c074030701c07282005601c0d0050b62600719001d009000c08036041912200700e02d81040034803a0030210a0f842c1c803295003462170f65420395900c41d803410300c0006148840c81000304000c003000c1d24049645c960444440d0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 297728120 1250 297726870 297726889
    0xc0201021212010b160b040b04050111090906040506210a0605151305103506060109381305010f090302011d060a0906031811060d1514 59
    0x400d2400c20501c200c8410700b4980308054111020f0940c03903980c4540c2910350103414020100054883c881c11000d03c000c1005000d40360b4070542c000c10080bc903480030350041c80c6280c8165240c1c190b0004600307011600903d41648110741051005152621a40318000e4140c100b610040c0c06410f035070800b5805e801806054012645e0055080740f61402030500304001803076921030442d07e011010340da4400601d558030b01c50507a5000c0c00403819085020b02c800c0b0003810a000c9108010040880c07404c1072100190b40000380301d406018140c6510603850304141040c1480d103403504118003481b0a000b5a08080c03103144880300d41303d49070304071400e9480c007881d08081601800c1e0303403102d0f04011910080c000101e5004007804152942440c0c80d03a10740ea050a03210120505825805501c507200180d8030031b20303942040d01a0700b12007554905100400e444258102868640000034280499450007907016140c408000e06c9e0300d0485101c0040c004032203000c006007611881d004540c0b840e48070300c1980f0951402000d44c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 297729370 1250 297728120 297728143
    0x15160201050615040303140f16050115051e01020c0d03030615020f0a11030a05011109150403260d060905060a0b1e09010203270909060c09060d0e010c0c020102 70
    0x464000d12a00000e16451307105510000d000c01100c450b000c0c01c040c9480c801c44422008600d165600c9503004800c03003012024002d0116103561a10059070383c010711030501001185c17802003542c42402c403029074140011110712803050443c01182a119680d80e600c04607420b401303000f80d800140d81400d0018400c680b4010286d00070566003e02c0100f10307420400541d4151040d40301008180043d00e0001003840d2100c0100d0046c059402e02001100705610880505210502112006254921500d40c1030301d07480b0b9800050280c00c040b0f0f80c00b4241101d2414142040340050440600d0010810000700440b08181c102d2a0090740751018071025107404e0309541c0140a80c004000e00e01034019440e0a50800108441000710030040f5400a031a030080c810381d5140c942c840000c600704580b03c1c0303844003441c1280070442d1040c2480c8001c071b024464009001c5214142807801c03a07281c48403500400c0030542050743c070750f1801d82d104c50815076090001c0c0a51140360b102c0d80c886200c0c01c0c03558400039042c02e055191 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 297730620 1250 297729370 297729379
    0xe090114040b040305130b070506040605240603070c080c010e07060806030c090705040f1404110c03070b06040b0604080a0b091903110a080a020703050706020607090e0603151602010506 81
    0x1484042844203031100e40250389402c046699201101b060240541181e0042c050030101094a4092220104880d4401c601c034000030032640d0303901e4108807458190415144003007403c480c4c031b0b1092814084000c5800501c00d003460705100140c0d55517805154400101c19030a65102c0c040307421048800c124a40182034281005601e40c54510302095680c0d1980e85580e104070211000714090a0041040301c000c2d08941c04107200e503e0b03e4104140c030261040382030034011b0b4a04040c0a40f4508210142c074502e01c00e03a40958900380061f03c44a405c14405858a40d1050ba600d01510417550341d00010002084e0450141a201800e401c1007001c3e514014841c01036a00070005100500050304200c140b4103a040c1000101c8170b202040c0c161411032200d4005081c0c00c40000c1ca48002c0d6000203903031041700c2c80783c2c0c00c0760f144649500c000c07a250039081e81c6030004946090401d10a80301e190a18a0307201c100601290181201d40050700f03080c900959a107010705c851042014038095080c010954420340544 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 297731870 1250 297730620 297730661
    0x804060306090b09151f021510032109050a030606060e010c1502070816030306081006030b011719060b0a120206040b030405161d15090403180803040e0901 68
    0x8081451000e0007000e170008100e01c8200c840755035480f1307000038102120b40c4110b00d52484289030041d6840c40800a00400c50725a080002c04507410740d015038099075032000301c00c40001e01d4900b08080c0b048400f48898140410103002003800d4a5800c268002913006407000f00d2103910f0001c0281c0b01c2000c01000d181000049914000414034035100b1000407041c1d41401070790341c4180e040c801e2450181d2080c015201d55040c5c0d0550615a1580060341611410002d4425005154803503204442d0ba6100080004a6413801017100d8410303590ba103420500000300350f82c075042802900248400c1e03032140481c2c607030340c2c0c0390350009041c1400d00c40310000e00b82085000784035101d41d4000030002d028520030040017541c0040000c00f001000c0c4454142d550360f480b0f00714881c0d521500c990306003880f01d080802c450b802c441d00240031078004070b48803408050094006040e40d259510111204a825010128108000c041c00241c521042000b0002000c1c1000c61100311b00b018104e090a4880c40b004220714602c265 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 297733120 1250 297731870 297731891
    0x32401030207052a04290306090c09060a030b040c06031a09010902030c0417060405010513020f100203040b0f0301030501060b1309090c0512010203090f0d020c01030509010b090103080406030609 85
    0xa10000e00780550030001020f150041881a60007013110340d8903401c40c3c180041075080c85d0030b40142c10220090708000038108035078142419500c2104417102d10040e84070716001501c138108000110f070022400703400c0c6c0c0b01c03007616511a0103801906030740071280b14004120400000790305100d07580480c1d082000c02c01c0e2581c10b88002404405040c085c1025150f8000081010f414040d005c4a00510f1800e411010324603031841415268441107405581e5542054001009220580c003a130301d00c7c5038010450b84007003d07104144010303610407607440400c2d4481040003191035a030200c050510004013010503070f601e40c114541182900d0081d4441300d20070405000d042e402c001c2d1181d6800981c1c929207400240c1504a080c0340241c5005544007541029900040d5040950190000c5104508900483d007408038840c10707641d510b001c0340c80c40700d0058100c0d000081d07096220740c0040380c111040e40000b1510456100001d000048280e20803103c1032000034042003d04c0e0980145d50081c02a030100300b1402c881c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 297734370 1250 297733120 297733123
    0x6050408120c0c0d080c07020d030908060106030b06042102030105012601060308040b0307141606240b0a020309040c0c0c090c020307060e011404061a040203130204150b03240103020705 81
    0xc04d42c20303c2c00d0280410001d0408140382c4207442040c1c2d0010718a203118030701418080d081949600400b9000e001e00400424114000e00640b600c0c194081d1800d03240c603140980742c202180f00100d15100c01540c2c04080c0c80540c0d0240100c9000e000148201041140038500400d034803041b4141000c9542d04042c01080817403040c5095034210b810782d2031a07643e241e485190450b103c0e000018205c100e1400861080210391240c50090300c110f02c20700007004061b130581802d1591442d8010071200107002d0640a1003506504006440841c466004803801c0449020002d010fa4116000c03810010f203240381940140a18500c429000381030b4000d081080191120009407030f0701c41c009014190303035140c01c443c2440603400d500800c00441a515188003504003450008003038070b00048030202c0f455454062180c40d02e017510071280210062006510441059401e01002d4541c41380088868401c050000038a00c1c004401184184044501c1030b41c9807407044041c44614141900c101e04040c03040c0300d034100280c1d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 297735620 1250 297734370 297734383
    0x14090105010f26060f030a15110c0703050a0203010b0603010f140607051c1d0102030d0f06030b0705070224030403030f0615030e06070305041a04060906050408120c0c 73
    0x2030038039080d000c22400041c19184000f9070450554000341800c1440d040c80300ea0710030140036040031626403141c8900c842c00c040c0d0702c851411010f00412001c480301035070203040342c0c406201c030344044500c0b9050500e200750311401c01045920540b901d4001105280441c42c080c854040801005c03502030b4210750525180080c41d151302c0c064034801400420340841c4540e50703101991140380d070003c11541c00405a05402402e8480f92144074007244a40c00400c3c2e40c00c480e0200d225035000d040c0e00031404e00020f100c1c034401600c1140343c280d0059640700404004540c80c0c82071148510311940b111661108184103001c070f034280543c00c40d001c1103802d13141c08541040140407030350025010b24012034900f92000d04007008040b0b81c1e003d840001c5480c0080350540b03400d600101039901d142400e84020b039540000a8081d00e4046400a1407020100c550380851540b07110080d42041c024000015a940300303507241030071500705403015111040046509d0440e0b202e0344c0d03506980420840051810946100f00c5103030740e01d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 297736870 1250 297735620 297735629
    0x608090a11030319031b02071508040206040302030d02061005030102040b0405131d07091109010207030305070c0b040330080a0207020d08030f1f05061606020d05091006140901 77
    0x74800015030356901001511121910503002105102e410701c80036004000c0401640d075001d401c2c142510029001148480884040d091030038002d8211100480741c2100c02042280c0c040400d00022000d40c50030025902408000d800410844c2040c0140a4003000c155001c24032a07801040107000300c8400c1c400b82c40491314150f49103041311404008503800380c08200486450080080035503045040c00242c544104c524644040000c140141c401810a03c01c9011082c091b80c410102007001902c03800003464454040c051580a00e6203612483c3c0d0541d0156000341d6500d8a00f5602401909000c038070151441c0d00c80718144d070b040314038203405030210310300070705001c0d40c5a80425541e00b5500c0340200480143e500c00c00d11543d03450410400c0100c00c100b551202c82040807410413100d540d456041440665500426150504d0410700ca040500b80c4c558004035001902130010210548a6020317560040e007100015061102050705000304855039613000074881e220249020f41c80b9140d01e0041c3d0f0658 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 297738120 1250 297736870 297736883
    0x10801090f030e010e042a0806030a02120f060c0d0608150c031b03010b18030d0e13060801020c070305010b270408041a0a080106050715051504090b100608090a 70
    0x21040380006072024955134060641003800e10254029001d00703c00e5001000300202c04420741c1c48100711f011504940200c1e212901944052101009840e26101c0b000072240082e04580440b46155822402c0160aa0300c0200084000c94030228031032080c0664405004040b008165112200e401c41084e80c002501c2442000e03070010110b840c14081181d443c3d0019560380d440c1d9605d5940d0328201c502944801c0354482d00c80c80c0c003170410015140200c0c11300c01d4061569a02200791404500b0011201c04451700803103401d81d10500003030040c100780003800304548200044c0044603c1d500744582540d020b010064460801c01e00e0020028410305031981e030068079009180c94aa41d1468113540b203225030b4000362540103103100105100140c5c2c0008191002565580b65000e9907140c4082e6110b00500c02d004004104107080c05001d41c0090f070103554040320b1041c00c5402c10b543d1a003c9000c4444405003640c0880307880080014400790006150300400d010b140c0103440345003046a0545420800c030004050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 297739370 1250 297738120 297738137
    0xc091905060a0911090f101e0302090d05060f22140106050a030f060c1704030e1818010e07080d050304050312010e01030303180b011401110a0501060e010801090f03 72
    0x7540c66030342900000e00005607041051480c0ba0440c50100d4000601c140e100d403801d5050036104d030501661000000c0d07100c0c1c43d121820b01705d1051a12404001e0500032041540c2400f00c69500e64500489000840c00f900103800716041900e0084840e90004126203241002d0321040d0001f0403150807405409600700b4003400c51703d0040d03d680c44c0900b502e548515404000030a01006024615030071a800901c80c3d8010000e402c1c80c40402e5400465150092804111700c3c00040e000c03074094254003004500081004810010030510b04150300010345003080005800ca41c440e08480003403040c107540100240081c500709152035052552104000d21603010410080041400c000c02001a1441001003203201c0c035856855681014144000348810f60000e8100f18560901c0c41c00c1c0c2070404030013900400210403581c00c0c101180507848641910604104004e1207918418100b03002c001c507103034807660000c24503620305016a43d15880c1038100b031100341d150690300000102580d0340d54200e507a1500b032040d503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 297740620 1250 297739370 297739381
    0x8090106082808030109050105210a080c100509010507120e0303040615090f0f0501091802190e10060e1002100b0109120303050f01090902130b0303070503070f03020c091905 76
    0x8500303841402c0140700e58070200010943c00426007150341a140c042d140b41451500c03103800c00043c80003400c6205d589030019051100480c0d000300050842d0a4500219071141c80500c0700702085890841d09480d5a954403018003c00d20f504c1040d00d10001c2403800709002c490f0384949059103030310010b0310090620b551403c85081d0a42c20f041b10b98000c01e5803800400c101c403040b052442c064a44612440030080c902000400c0c01c410b0342c4555182501c03002c84a041005156003800008016000c184006a0642d8000940240791000942c4118048103109810514141018103c5d68007903880c64800c0001e441d443c40c2407940000e904003140c4d403214000c03c41003000c40040e1200c40194010194642d074000c1c0f201d0915801d600010f000389454090060140c0c0e036911458100d4100040c02984082c03c141c69000064079508903180124004050380c1c07800003d40c2c1c0d107e24551140b442182c1e91001100f2141c10b054061110509040341a1040720440c40e0803088040c2d42a0010036844050b070780da501095 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 297741870 1250 297740620 297740683
    0x20a020c04050a14340f0f020f120705010b01080105010f0302090d0b040311060a020903030f09030111190206130b060409031101020c0f011109091b0f0304030f0809010608 75
    0x44c016240782010510b0803d041002010601c60b4054205100340d4142c1c9240100848044c8100d618a91348103144480465000c4541082d0010003004511851004034182902441200130610491240c0c41e9076000038500329094072200030020b41400025030041000d0b0740c00c0350f1030340d03007040311440c00694442d416000206d205c0e2651a024060030b40d0002004101038101ca0340420082e491000c41d0000e0380d07514000d40c160310414400540681080c07144928152a24014080c100c40050021070400040909421281c0081284162082c80306c4941c404094050000a40116003250440b42a4010362504003a1207400740907103018076a00c9045006040c82240c1c1045030f103171b00400a6507110210842d446e62001c0c0b00030354a845510302202000060340710400c81e8a080c0d0043e00000450f030b519407450b10f07080b46195206008510030003590800701c1009000b144103501c82d84a0003000513124074010940302d8020b100100c168075241041c002982c00007501c61410712a00c03121a90078190140b00c6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 297743120 1250 297741870 297741881
    0x304030c0f0b010b0307110d02210f0a0201020a110c09040206090409021008060307050d0209040602090102100e0d03050705120417090418050d02030708040b0d1d0a0312020a020c04050a 81
    0x18225000b000c00205042a0003030046000d00205d503100104208007401081c0c0b6282c0b0182090302583c01111021580405214101008030b410048a4201050301c41c0340ea00c00c0c0d109455010060350f001410100468101c8410244012410010304883e040034020500c10480a0b0020303114100204120203a81d5075904060002c0b940603040c03801c102d00c1ca9030042c4c00c541c01502c075540301c1d0283c000082054100050b1805000303400500c0750341c49031101e44070000258000300003035046000c0c00c2c0c50220800914001d03410320001850080c11400c1944600808460002d4505402c0000c1001a0044031541c501256002900200000030102c00800580c10f140b00302850741d60001d081c110050400c0031060071070762105014900341c0c0c1d6240d00361182240c0b20b215007030300141000010b10080c030041410a001d00743e5a5441c40000442c2d004060512420396209035542640f0741c4005282004c041d0710180c0e4854907640c03200c09609000c00210081c0d154903000c00c0700380c082c1c1e070744000250041300150080e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 297744370 1250 297743120 297743123
    0x11a0c0d030911030a030914030102091305040227161d040c0e04060b0706060b070503030a0c091a03071416060504080d020a020a30230a0207080709020f0304030c0f 72
    0x1100c1c17514825281c050200111442203000703c0c08101c00c90740e514241030080b01c1c1030040090454a00b0b00c44110f404000700b00c058000d980000403c81080c100329072050b600080201c5581d005e100524000014106440b000c440080c204600b03030b500300710381203440c0c009591001002c413804036080351021022100700840040b5507600c1401c0c10800a107254150000b84805402200c05210143d210180c2c410148a1440001d140358000c00c00610700b200540c3c8071800c0f200062400280c419500e40040c0c000c00007414060580d410000184801b050304203901d086070304c29480f0405e00b015890f4202401c04686a20083c02c42e83d03d4000140c01c00200c2400c4a499080d002411912030500080003551045148001c8848010308900007403400307a00c100c419940880c03010480d4107049580002c41d60032a650a1840f038180c0e080e0b020444c8031f1340b0800600301001c1c041d8010002c0c00c0c07a111030107103001c10343d5000d00582c1e481003001c034250301c8000e0201d0b0392080e050b08210790794000d103203414021606c4a210 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 297745620 1250 297744370 297744373
    0xe0105040f1113051512060907270e06010c02150d0e030a051909050901050618030a12171b07050a08040b0a0e2205071214011a0c0d03091103 62
    0x88000030344050b400d01c1c1c0191340094441c521040b030100241041e0f403040340907200b002c00308100062400d103019030007594499803d00c2c01038040c200314903100220f04900d08038408000040b0909002031244030105a501203070919002480c0395260f008146054030840c00840300340400904800e1103129600711003c0d00c5215409c60b0f5950110102c010227a800007500f0040d5600b083c841162500d228200d440d0544000800180c000d9180604014441d400716401d00701007513107120030040039601804003040c1140251441c03400302084810050502c4400000c089414100744140040303102c0f696511041385803942c0f0000d17078455082c1429407a00f03480000017410a40d0002c0c0110b07880f1134560140c0b080003410344510626044000401c464940d031440c50f200c032011180540303281d441d05074100580148007420b10381d030105450014401a034a49861540002d40c40c48010001d00309400000d0094084150023641071110b407111881d1200a02c0d501d08081548076500002401105945400c05040040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 297746870 1250 297745620 297745627
    0x305070c080c240a0b090903040b0306040906150f1208070f03090b0706140105060a0c02010f03020c030403060504050f01090c030809031c0c120504060203070212030403020301050117010b03070e0105040f11 90
    0x3d00f0b4212010044680048080c2494801600c034140000e91b1760003840708070041c50403d4180244403c41340c00003011503900a07120300018000c81c0c064403c2107100e0441c002440c248a08100c10820000c6141e80b01c0f5140c110005880c0300411400420b85a02541c42111003942074040c0c14111940c181e143c0025150300400107401042008586c0008040b0b0550182a005681e071a01044118081e08a6420109240303a070b00700c00640c8a0074800000b1041410014106986020b54902e9900107400841e41030b43e45000344130074801d040203041e000070386640c001d01010f02c03503903034402030005907101c000c220441c003240c000030641e8248102d41501c20502010101c01c0c0f0020030040150820750000d4802255107d02c03c0c210903c00d8044500f6603540e90011031510880e0f81c03c0c40440c0241c0d4050400500040c4008001a50b0030b002d0b1354003d110820001e0802c2044140c29803c40392282040c9110307074030154003042103c203015141c1c3d04480c0c0c02c0f100003036406d01840c90b19014102c6e4a084800000000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 297748120 1250 297746870 297746923
    0xb1305120a06150f060f02160b0c10020702210f010f050f1e0115030f05091e061003031202070b0c0a170603030304140307061107020f010305070c080c 66
    0x801c040300720301602c0d05000c805000356040320424400e0180040c0c05656043c01d00c00c142c01040520070320701061044603400c500f0028109018109900440e00b081d00000f028403240da0304004101040d09002000c5103445510fa0004220403010501d441d02c24030b642c9102c00d428102400b03201c982042c010000d029a465481c80c0070020b000444922a03154031150104031419005c245808048200c03c4a1a14590902c01e2148250420780648400c050300d81c42003011480c2940602c0e805032a5800042c0364101000d01250134040400c0301c2034a10354045402c00c245044240b1146040b01d0b01404c000e0301c9040c040c1c0ea5140644103d10020700400c1c014024440054020f400800400c40d080e82c82e40301c00d2060409000e0703204e00a6445a40c507510034004600032400842e045140e12851008492070241d0543d00d010642d2248102d000c02c2c1e2202080080070b509289a4020100d03009180820007440e0009021308640c11080016003510800f04820182c04000c0103840c038401041e1a2613a1001c0e143c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 297749370 1250 297748120 297748123
    0x40c0314010b18060f01080c040308040b0301060807050c1f18030206010503061003050604020f04061d0105030d03020304020112050415020c2b020303070507170d02070204050115090b130512 83
    0x30a1a654040c0008240c0b07042c103d03480b54005800307128000d00c00c01c0880000401120103030806001240b603000e04000010010b094840100010701508a81c00e442e0344c54880041c280c000002c2c040300c01d00000b0810040b0034003000c202200311a162008000407d0f440b046a0700081c01034030310f07030208a142d440b520824142c00046160486030110704840705995001455050843c0b50300c0020182d81c401c501042c01403414400040f40e400f405440011070320740d51300001e1103c01594611403007142d46c1a0060000381010300014404440508040d40ba40c2050340c0001c100095030106048450340d504041030401c0f940d0758001e10000b004000c20f548410701924401c6e10340c1100d243c107941c0740f80d407922401c1c6a102c288107103c548807202d4002d507096a844000540e0380c2c1e130002c0011504021452414254855a14003410f044c60301501d0040c3c940000f84148821100d040e08018904000c1c1c1c104a064107034480450340c140c0d50003144640d26801d0a151041c1c7c2d09009810050703120107130348200b0104040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 297750620 1250 297749370 297749381
    0x507080406020a110f060a110c1008040b0105013b0301020a0909060906120201140c1603051e0606040c05070b0c0c1219031805070e0109060509010b070b040c031401 72
    0x5135100001840012040203c0550f5500c84103802c1542800b080c0080340c000c43e48101c1548191080d00c10740052440010409400b030300c84000490f032920284030a000400081d24003401007820304810589070280424003090510b00300c4e400103e1a20070f84808811407907552030103400098000d5465081041c3c015264000034010600c2403880c0c03003030000b03094500d4020f80f001c0740c80c8c45940c4032144215400449104040d4084c140340a1010054008030150400035000b00604265211013074a0030b42ca8030300d0030004608071080100480b0310380700e01c2e0901d0100301183c004504990001d05142000b80c02e8403240117400e03014041c210b42104000b0391765500c030300900b01d10110000703580d034a052032418440e0074003c00620611080711030303440d01700c2e4502a52242041030801800034400b0b246903566a0714000b22500000c00064681004000301c007000e0040a000c0e2030304440342030317041d8145071917888280240000906040b0070b07140800c043c0122000d0701c0c0c0180d50080c0318921244001c2045901038039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 297751870 1250 297750620 297750623
    0x40321023f04020109030c08030a0e0103152108030112020f03070b0a0c02060c1f0507030608030316030e03030c190503040305031305030415020601050306060604150f0507080406020a 80
    0xe03240c240c9421001a0038800d4010144240030030600c169400850078000104100d041c00a01c0e040480403482400801c001400e00304029550b9113502440104910000e102950500d410008004600d882c07061440c0d05903071500d150410b0855101c80c5035484151110000340c8144400000460401c414600d20301c0b0150098030440c0001d82d2110616a944029114014103038100b03015000c5c0c03103440340007829103182c0020309241c2001f4220000070f06042c0c0d0340159031803032106110003000000a0b4000c0785d50146480c1001c216007032505440f26101e00c40248000d4007000410004e1a06900030b41c40700010300840300450740c07030340781020808400707a01c400c00e010400c80201d00300d0b42c4803e01c203208403403040d039066454909580710b14130b001c00c00502e4a58100e50310b010520022412000000d40c88030342c500300d0360007480e1070351500c0141402e290b0060306680c014582088244465074180c04404c2e040307086482e010f540c010700a0021203540c0900100180003100004001802270340c000395151086 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 297753120 1250 297751870 297751897
    0x7050a1a0708010e09031306030f15080a020105031e0f01030c0b040f090216150b190302030d0c0303140a050f0610120c03060308030c12010603090203060f04032102 72
    0x40d2110100c100e0300340458940d80019030600041c0604468400450b80040301e040c102c90600c2552035201810135040d0300514006995030552850312108ea005403039442c8102c04400c00c6070703420301138195250f108a80c00641844000404a500080c40c50108490f070b40c02c0c1400524a800e003103280d40c400020a10095412072244003012070318100300c4088504036291035101070466460325400d0780103500b080c081c480240f40503000810204003900c0340030b40b5082c902000003038001840c0d82008058903141061103054040c13000103100689002485120420140c1001c4001c5026890200d0141140243c0081091420414420032601980005006599485030503042e540e0714405c1c480024829080c1100081e050700c840d00d44004203500c9805501d500d481e020410503180d444208007030340165807892801c080091744060081c0c0c281c40700c0380034020030710301404204503540010f5500c0c040a01b200d0740d071454040103d803c042c0a240c1c03001000448840466058803011a020001d401800c80c0b100c52 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 297754370 1250 297753120 297753143
    0xc0e03060a1a01080c13090e010c05040807090b060f0a02101a010e04110c0106030f060c02030f1207050d0e01050601021b0102101a060c0706090b040506030703110d0207050a 76
    0x20350300a0281c1c00744100c2e24841c500c4544401801100c0e00e5070050040c0b0020701003044240440c10300f143c0c140340a001901404640a00300c1d600450844000c440584104501400144034202000c500300d0708941d6002c002083c43c1050300c0011f42e0900c11a8000c100510723002504003810f90f00400e08024585500d8020044010a5401d02c54a600c5044070240041c001c00a6202c0b00c2ca0164402900c0e118503804040c1003c0000c07070310500b1034216820941340303810400c11800800c000341c015240c140e80c0c54405103060410205030400c0074007910304a00b00a210b95030024801d02d21030010340d80304603940181480004103280c1c075a4020203096031450f0050040c80070020800300c054400a1741004181d006005c24081c1d03924046c010211314044030070300c5076092030700810b07a5107000281c01288050006040c03401d2810700c010b03050a0165006070000031050104009955407181640e038403100500380803c010001c8244500180f245214114516101007051814040001091151107102d202003154 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 297755620 1250 297754370 297754381
    0x2031b03090a0e1b040b070b040c050d050303060a060201060f090f0b0409060f0e0c03030d0f150312120c050702060309070f082d0d1b0c060512060d030e1905040c0e0306 74
    0x56510a86c084d08000304820001d1100250414025640c8503008088500055403280002040c00028240545480d4004070621802d40380c11040c000c000c1c0110300081141c24600705501d16051024803d5046055883e00030019803882d80d00034900c16040284100000585407400a0007130640015203102d05103004082c80c007031200000d07402941903000303000b903080410301810a005000c00ca01d0720b0341c00c680c0b61110309aa8404440e10140910f02c103483c401c81d01c041110f401803d14113072652100030307281040c140444458016007120b04458041d40ca25585e0ba03a859403091402d5010f0b07224039020a035101000407035210118510004403040c00043d5940e04a0803000494440c03a42e0315580d043e0410701c0e602c1180e40c0074200b5000c10071540071010140080544440300200c0b0389070302030000300b41c2c0020b20700b0741d41c4e4200032040d0b80f03c2030440d403260b40c3c072a00d5200104190082d6142c103001c0d42e148000d41480c5940c03110f0803001460010320901902400c0c00000300902c002d01c1c0c07030500034801c6601090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 297756870 1250 297755620 297755671
    0x1020c010c0306081c1209060b03010207060203190903080a091a04050f1b0a09020c070e07020304060e011e0e01030e070803070308240907050d020d060e0c0a02031b03090a0e 76
    0x125000c201d9460034000100f402042005040041f012560103595030400300507500e080c0041c02c0c0d9940600c00050b201e1030982e22040380860036117000c12880340b5050b140000250000c08098009400ca00c0003c0c801c845c92038089400e03030f1540040340080b42e5000030441080030028030845848107020944410501070741d0180900000d040856a2010003160240311800066014112110068003119013150740c91901510b0020107a0b414801070b0800079043c4081a08000898560082841c00740140101d64410418003004041a40c5c00c10218800003c8035038800e40003240c41003048010383e401d141e5103101700c5a0302d900010049001c9404007001800103558220130100c0901c1581d03400300d8280040c020091086c0e0b00411000c02d2103400d112042303c40c0d091f03201030160030201d400e00040703041c10426084000b505c01401c1c1001c2103010016100116804000c0d0f03444507202c9524100c000007000c500c6401c3d4000d5048242c0c1010401e40c0000700502e00100c2c8500569a000c3d41c3da696410085421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 297758120 1250 297756870 297756913
    0x91314030f0403020f010203040302060304060e060c030105130507030615270b0d0b0301060b030f07030b030303070e04230f0a060906030c0302060702010908030301180506060a02120c01020c010c030608 88
    0x11101d034642840700300b004d4102000000540481441501e10f81501c80c0c2c001100c50304282d4090b108203945012480180c3c50030400b01da04039a60b520b50a003150b161500250030500e064040950031612200031803483e900030307000400506454140700030220403109000304060002002800449078044012050711080302c10101038492004915181c000807001e140003a00144050a0b015960b4250014080d2000d50195000c3c102c400e42003400c505000304024142c82000e4202ea00c01d0b00100140544190484071440243d80103640200c0c2107802c1242070081007081040c861a43c002003802c010f00308140da07406909c900c020703a0302000420344071001070048030424000200160019401032001d0310b010005084064414503007500342c262120b10f00c81c115002070340244460788581d002901c1d610602d00920350302000982d0045d0400a49042c0203540b442880780e10360010000154800fa601001e40485070038600000090041c3c0c0c94040d0003c00408480c82001031a002d1240210399801041c0100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 297759370 1250 297758120 297758137
    0x602220510020d05030c0f03070e01030c020d05090d0501230f07020303010b0f030a150906090b06030f06091e0124020a050c0402090607020a0801020706061205120d060509131403 78
    0x400b0b048005076070030b80d0554009008000400024024542402c7d442c030011072041025603101800d0382103103000502520100200a010740d0492500703842c000c2d41c840706840c600b400403503421648c2026030801c1c9005100305034800700c952a25540d00d141041400003014000c40103002c10502d1555020000c0ba2680001c1c005d002004c01d041010b0724030409890301454010a00d8840020000c030440400724200403e584200b440540314441040444864840c10705504c0b8107840caa4550319080c9001c02c80c0c444001c0c010bd1140400c140824540d220007100c0016035081584000029616489269a1048849441c1c0010084010080021480443c2c070042d29940400100500b03004801000040d4003d083ca1035008602803003030b400981d40703a482820042c5028000160350b142c0d10300300941500c0c0203801580064452006410000c0c100040d08006280c420701c5c4541c49800b107480100203021140e201b1070f8071120050034030007442c288444180445110300b0548104c0b0603a00300068607402400310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 297760620 1250 297759370 297759373
    0xb1c0302060408091206090609010509011107120e120a0213020a0c1101050903011a0405070f0f0c1509150b01090f06081008010e0d090f030804120c03060222051002 72
    0x80b0300080d030f03102c1c00f602071000300810044ea00200b41c10054541070085486003020380c0000305201514030280305580d08078141e0002880000340e41d082400e528444d851000f89010320a0401040080c420040c0303004102e0000c00c2c230100f00408800003941c03050341602c280d205506841c200e01a05100b4400c840d03035941d4688480003200401d8031414420824004040d041c84020000807020303580a200d11940607a600d40144808101e4000f0300040718001088034003808250800c0407511078000040c1120180140f814180c4469a45810850004100303024a807d81c1040b180c5401c110f450420546047c2041d41c1c1040440b000c40d00446615842c0e1148801010741d410041c0500c40c42002a9a40560a00da610000340d40c0c80c1102400c4881070340300b0021540200318441c58240d40701d005080204001c1c12401c2156081d40c43d40b284a00c01e03407041c0c04001c0b0440c5904020005412110710042d600030408544500182e011103214804800c4c0200b100520704401054070320f010b03013034180e4680e107950 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 297761870 1250 297760620 297760633
    0x50601050306090c2b0606020c060406051c0605130b010e1813060b191d09060c092d01090905041502090303190504050109090506130b1201050a0b1c0302 67
    0x4001c4e9180f58400d020602d40041d28103069114007003603030b800415100c011743c00000c00c2c510f403400080c140b000a0034140e11411007003004029003036210007920450f9035580b107481c01c507102d5070059000401d8154001c0d50454021201500584102c0c0d01c906035892080e2640b6035801811001c00107034000c8440c40c103801a6041000c01c0071481000300c0e8450540c440c14001a5410040b400918075250361180d8420702080d07508188580ca210901104a40c0107802d410201800d088040e540c407017100800c081054107010428900d1980c03059902c0c2c04290440300e00c81080740c1c1c500c0b812801c1c1c036200000d083c04161003030000111100f462080c14811a086084407070b81c14a4000500701a41c8207058680e4103100c00e001c900e0440e107200d2b9a000300b4007416100c0e0341d5110b1a020000d08a0381e40350b485540c80c1c0b0701d840104400b40d11100580120903006990005240900c80000b5000d1a141c3c2052151980b0f01820018108465400403462040403910142c014004601d01c40001d00d0a06000b4016000315 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 297763120 1250 297761870 297761881
    0x70b090109031218150614010c03021c0512040506060a080f0c0d110a0608151021021e04050a0b040f0b0c12030c03180607050a20011b0305060105030609 67
    0x26403210b9403040030900d44003110b04e46138498001001c044442030405503920300080202011000804a5105007801c01401c000c045813800303501c0b0380800a085401156030446201140d01c9002210040c0d001c4003941041400c09043c00740d40c07040103c605074000c401e121408184158002070389000d0b00c0305140107241c0040c3c14414032000c03080f0f0000844540a00c05441040c030b41d100c4c2d0380030010f8501680d07000420301d0890545030b00d10190b00c1046001c2c20200c4108035081d6440013000982c10b0b07001d04000d400603c1d1540c884000d100345c4418009418004028002403484507005108450381141c10003072550301c50301c0300d81c0d81f8451880b4014030207001030010044405442c000d0012291400c0a9801110b0450002c00c0c05600850300751140310400420807401212800070320045901410040106141100029115100e240c1485050003d102e4589492031b40d00341d00c1d894180c0e00034ac02030040100c039100c4c1103104518194244003181c10400021410b521a0302600d21618009003640156100d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 297764370 1250 297763120 297763157
    0xb0a020901081b180a090603120801050105031306020318010c030c172206090c090605120d020706030b030a120e15030c09010c081e031006090302130203090f070b070b09010903 77
    0x42a1304541208821400050318046071007107400543c020200300301d880c03040e00402020014140c00c83c505000302481440443c220350452801e14035030206006a4035184c0c81402008005413403e034240300e40c20b00c492071003400e074140c00110303c2c080c1584850000e080701d050f40101c2100308440000034032000c1600e140444c05000340701485a03005180000b503496a9443d00c0c400102d1682185501d6511001c2c01c0000b41403d0f000c120b100c0c401d5030040c0960400c0d00c1c40080d01c6001520500b820542c40380303600301d5a40d41c00c2c000f6a000503400000d03540c0780e1407081d0f005002114200c440a1140c014900340182050150040342d104410000d0100c1c13420304041e0042d070720050b04070800d40741b8142c2400042c0002440c0c41245610f071090281c0c864580c50072691111410000350044810043c5941007040180c407500d031880d41c1031303505150141c0c40f6030740c00d01410f14000c0741000d140c3c02032040300c03c0040c00d0725501c4000c0c207038240104103c0450356190040b803401c0e035510100003030001e00707030203001c6c008401d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 297765620 1250 297764370 297764407
    0x4080a0315030602070506151c02060a11031207020d17130f0b0f060f0f06090d170406030f061d040b0c0910181208030c160b0a020901081b 61
    0x840d8101e52250688039194402242c10440741100c141d0300120900500c9191040307111880f400c201c8010601103140002c0c4029041c0c8003d0090007407201040e20145070303004d00051085c0c040300000312920392020361101c02d01140280d46c00700c050300a000d40c3d4850140318a02c07568004031941c5040700252108040d01000d00c200e11400c0c2e5100c4110411100081c00b10102c49004035004a000c1d00b903418607104002d1181c501c07c19140c81000540014502d6458200030703650107d000326401c4c25020120b003004d0300103081e00451101c54000014001c0741c5103030140d05c1074500c0300c2c0c09142040003940352036150710400c02258404100c1000000000d00080480b0051a1301600f5504042e04021400000c01d0404282800741d03400b00b0030304400f10f50b03800c400c0b1642500500c86169080c5142c0415119040244409004011248000500311007503540c504a00c56515901c505010440e1038800300d100025084249130030300184d90540800c035a540c84400045101c084040120b24100414014130028032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 297766870 1250 297765620 297765641
    0xe070309080c0606030d021b01030b0406030501020313110405040807060504051006060509150a0504210503041205210f1b0601030c150305070912150e100e0604080a03 73
    0x548500344840081c0c140e4001d0414a02c004009050b5410200201800c004002c015081194008076031001c0c069141600160024021700b00000c4403500000071402520442e0405401e40d030001043c000003041c020020244c050254400c0c0c3c80800c07100c02004103584c01a1005044a00709214020215005038400380d04036200c0c0d0b00703c50102c26101d00d034400fa500603912010110300c000c03c02000794145040106451058011000d00e0404000d102a20318007803030292040d000602600c0c2005090408806489150001d04580e200c0303694004042070035905c880204c1d07007400742d400d6048040006210804d0030020410070582014208025019950003e406d940204115051030600c06d07002031094501a5010b030341c01c0007009041015a2503000c0300c20010008140c40e000030007660a901008640030b0300c0006030315901140082c00c1c0714200c5c900850b00800228a031021204800c2000914402c41c1050300394144102c2c002d1000d055294901107901601d00c0c02c04000e24010644260b000c5241039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 297768120 1250 297766870 297766877
    0xc050c12161a0706023702010c030612030c080c03030c0403030f0c0308010e15090f0702060f010f06030c03060b2107020102120a050c041a0a0201050c0a3c030f1a09010e07 75
    0x1880c05414110740c1d4064403061034182100350044071b1545a081c040c0119149060034244112840c04204007800d0035400005020040c1044404080040d4a400c544201c50701c0c1003103d0f102e080170b0303410440c0c0d5172180c40118040340130180b24044070b9005e9140050111b03019181e124482e880d0480444000e00000d2400c04d4403881170a806c43c1c4d40d42d2719140d2074091003c0c0241e415842c0b8040401038684403006c0c101c00a84002080100441d40c0f0031251380e000e403020703440e02140d0180008000d9000c2d280c144c009020b4400042a10140007400d0381d0300b105c0700d55949a00300303056110300606038201e100e4030542411501660f4000b46c03880303e058001c60340100050a105142c030780d1f610b0200307e04030542e0b52000024040080c0e540e000035030902600340c01100d020122841d0440c1c021000e0444001c07502c0c01c0c1410b450307032920460105944c403c03022142003881c80200e2141403c40000b4018440300d844000c54600d04040c501c403010010200a941e002c01426804131039017004103100006100512100c00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 297769370 1250 297768120 297768157
    0x30515060705060a0609090b07050d02070c030f03090e010605090f030309210f030313060c02150a02040e090c0a060513050402040b0703080a0b01020d0c050c12161a070602 75
    0x2603210388008040c0d450140c00648118145001d98038180d5005d0342c44200c0d02820411010040703802011000c0d0800c0e182d00f0442c0c1c0d546181c032004000780c0180e031005000800c1038100042071002050202103258030035514020829160b1000c909003110071b0242c2c800154051003403900c1c600b402040c004655000408407030034003401c0030000301c1843c2e04508110b00029031460031002100708000b030782800b44004010314190b20342600300c019400840400900041d03141c4da5a412464001e00600e180403036080410030091404a29a80295119200b8401d0500004c4001420500c0104a80211240041190038000d140100c1165a030f080b40d4a581c020034070303010000900c0d03903d40c030080c801804000d00c0070f600d038545400c0103007080d9001031015446504241c8680c00036a070114498502d0109801c100002c00d01c10b081c601d01e0b01c1d030740001141e0403800c119040b00c98003600146400b22041307a410300d000f640b515040355000d15512080410b031410401d002c40c000096058014016900145140d0300a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 297770620 1250 297769370 297769411
    0x4081528140106030c0207080c0906010305190504061d0f0303010302063402090f13080a0302040b0c010506040c050a090b0a0c020301020d1a0a1206051b310e070305 72
    0x1107405080e07100c00c0103e952030381070081c0d00b40c041c011100188851405882d40c1c005482c041601030b40001c02c12070405940300c0c00035902030038202e2562541120241d04004a24203854400010b28450ba01029141c400c80362445080d0f000044c02c441d032880700c9000d9030542e4a107500f4404e04c2c1d005241d41c0300012614242d6001c0400f40f888000901c0550580c5d003132000841030062001c484d4015200c00165102c3d80c0c10400c1840300140c0799122164081c0442c0ea0300e600c5008100c0c024010b03504840ca0250700040c210040d007038150000360040904460401c20900006002d4a8900c1030309542ca02242035408200001606000540140d180c10f040000c0d004200c0e500103402c80e0b000c240400c06075550f5100c0408120000c00311520010800c2c0c8a802210341411000070101034240f100078613898036031000822101c0141c1034244007000c0f00503450786503c0ca00e5103032800d0700c48400910740c3c3e48920310001094080c6200310041159490100c0621075281c42404078050f2900034207042c0f400504460300d51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 297771870 1250 297770620 297770651
    0x190c0b090c0307180e0a150515101101020c070306020c060604020405012c09041407050a05011b17041502010b030309010804030c1b06030b0a050a0b030609100302030a030504081528 79
    0x72591040000c0750300c0c074080c000160220780001d08407600200324440d03510069114801080d005455074144051a22f0600e100345001e80b050f121188a1405008400010802990058a42000100290744442c0c0d59001800124043c1d0710030349000074900c0c2d402055a80c0382d40c50300d580320700b0b130001200d01146003800418143d8400b5078003100c148105170f0400c820380e032042c000341c40607050846020411600d880002410400c0981c40901c112506000382820400c043c1c3d40c62103074140d0113030410b496542e44c1078a03c1188004a08034000342d401c141d0704420519012040b1500e80304140c4807006103480ea41c80c04c4861141c079100c22190f100f92100c0c42d40c0808800c0203641c00402a569020841c69240b2091103220700255001c01c0c05812116014424070030700006882c1e101300260b41c0d51005544002800042c460241c0c00a9058010b072590300041c19800802401a03c41800484400c183c211440c0d080d0384100300e414210001c040e425564210804111400030914401c8000c90048201074040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 297773120 1250 297771870 297771883
    0x1103090a230102040b0d18020604180b030106150f020705012102160803010504061208031f09060602010c08010b0903071412160e06060f040b030c190c0b090c0307180e 73
    0x302c04005000c01d00301b45403100c500926079090f41c0e0029040c20b811181d80851024000c40c0100010400030900803841d450443c0e21031704482c1c00041c0244809661501c02a650102110301200010144e17540500501c3c00002c10901b1118181e4031001c06000e08081d0007007200c41b40c802420034540800040c1a640c0c042c41407006128002c015440d03482d4503140802c1308039442030b8080c0720400b101181600100c0c4500c2c040e207038402d2042c080c21220515800c55605001e41035040424250301d44200402d40c02d90550190450030900c1d1200c422a9880341040c1d182c60044031415940b5502020050012904440918800303d40103095055900400c4000c1411b1151610020380350b010500c0080011a1000c0b207110b400c01c0c0141c4400d85400d04140a80c1000e200b0380c000d800888400102265102d04042d0450781c00400212040c0300049020000511100032900f00307940d003002502c00f0030003140000ca201603c6000c000d004007617040c6480c0300e211902c0707000016030f00350541d5038800032016081030080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 297774370 1250 297773120 297773129
    0x60324070315030b07120b270a0b0d03030501030c050a05030d030b1516050607080f04030c0203100f020c0606010e060409090807050a1511040f0b031008030a0c0302011103090a23010204 81
    0x1016101003000d500c0904560b1f14600d220301c501941c561740840444200041ca112443d403c03000c80d0703550b41d0014000080c26006800e20f41140c140c4a4000034140c2c9503100c181070702e11407940d454185940c0c83c00c01c407181180d4001ca0707038540c11191200201300c0c02a88039a141d94806001c0c1d0301480301d26001c81c0d03110741080000c40080d691203070f5034404006041c003002d5400140ca0a01d4030305401e09400a40044034000c10007002d00c4010003c0c2c00542d40d00304032004040c00c010380d0600006140b80d00c801c0183d04031011400f920301c50500420041c0d03008450340c2800380300190a0f1030404d842c3c0810721000d806800c40940e1480800c000700004500b080c0301d080040c40c0502d20140301540c120b140d803c00c580207051207902c4484180300c1481416000d0141c10100e0701c0541c011902c07604c0e4607041c1850207841c1c0d03001c0710b0f142c030002508000c09030b0440441140d560003030700200503c50f17002040e008203100880342541075802c19214080059000c490801f4072005001040300e1414900e85070701d0883e0b02a800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 297775620 1250 297774370 297774377
    0x20609060c15071722080a030209060a03140f070815060d0c0c021801030507060c0201180608060f091005041107050d0c020a0902070221030918060324070315030b07 72
    0x4c18035281480c040e10f1340e41028094584240040c43e03105080d400c0400d60400400c402000200200100d20036010348681100c018005a628004003001400070281c0007250000305040f030f4006032111b1400b0656030300c103a000d92240c1165548001c00030722082612030307807254800c01c20702059907905c50174464005a001c0640b10003005003403500400c90046d012141d07041c5c90200440051002500100d1040100d0b44d140c14001032481071880180d0300300f0341007083c5c3e841d1030300304940005915900950050040c0c8060b40c1c0c40e030b03518824106000021074106c48041ea800b840070300030441814540e1240c0408070100103c0303030810a02d42d13543c604084100c04004005580c4214400a610703110b600000107190042c02145001d4150340440c0786824500e48003c140340c0c0d1807d81c240030403030500c02c545000a00070a001c0c940040c0d4803070500100b00c1500c1d00e40c06845240002c04100030440101c0c002e03502c41c00c58682080d9940c20040380a000c4604500420540d00980040080c810340113913401103c2685 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 297776870 1250 297775620 297775637
    0x30a0e07031202010b09100b0a0327031101090506010e1506030906070813052e090b01030b06032b050d0c031b14070605040807080304050f011503020609060c1507 71
    0x780090a640c170702e8496604c100c010a05014103040d80496603001c0750492150141c0720203019405500500c90060f40d01c00c3c000c0481000c11400300322501c0d00309007910070340f02c802e001c40d603000c80c4608856030f6071401030040d804900144002a00e0040607503100c40a404114003442401010a903560010b0310b01034100c0d840b035010310841603000b0360389a0b489032540c0c620001d41c044940b41c0a54500c05e6119410818558841c40c03444450540540303000305041107414403e003206403910441e15402440b007a0303828240f42011952b940f0300450050300c0f001214040000d03880c05000ea940c1501d034500c448501b4400108601c1c5000006400340d155090960b407000500040707181661035404072502440c100300310f0b950110780d600d014401c2c25591703200d0300014001100d960b5843c140c1002e00c180803024026441c040108001c005001442140c41200807000340f0a2040c80b15845420749050b0200075841b04050003450007074280328020f80b40120403d0708480440b4507400c0e11802001050b04c0080c005a4a40e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 297778120 1250 297776870 297776903
    0x60f070f0b1b07032705120a0308150a06050f090d03200a050d05090a08011404020118270f05040302070807060516080901230306120a0f0206030a0e0703 67
    0x1485480201e90040002c0d510f482d4103070b0307401403042c0080c030034420400c0408208001c40c1c07092081040d028003806131014001080e9018280c0c1d6482d89220100c000405403400160b280800014201c1d40040140c1103081d1380c1e050650603603050b00455400c01d4030751411b008581e00c0f03507079144020400b9806900c1e40d909119000310903007460600c00c4103145556100400040005130001070000043c0c3c841d1a007140c81e00100000614146200d5100e14055070074003481c40010800c0d03029280c083c41c401d889101803451210640101c1e01880e11441821400c1030414404041d0000c0b400303d41c82d0140d0500145240c0180100e104441083e142900180d0100000780640341c01001820043d202904105040c100314001e07014170a4003941d0700402e2800040b0380f10400d42d0190074180c20341c18120b04102602107015200f0794054200b1a01741d0312403250203200d50711b00703403001c40c512081036000940905041005c5d001e103e5150710140405c0c0c03415075180b00b818002a0305002c0c08019600c0385080481c06a80d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297779370 1250 297778120 297778141
    0xd02101412041a060a06181206020406020616091203270302100203090306010515040f060c0c0e09030a0e0f060f0d0e06060d060e0c0604090212090105070e060f070f0b 73
    0x4490301c25480301d070003c00d0200d40d5440c69050001c4404504c2d003108080c100505150300c0c107009038403000034244603900e410f04200c459005403041e20103a07821260281d4900502403c0e1401416010020880d446014050484ca04502c064900e010341080c115030003111094182c5040c0c1e0408450620340c0b41c403018021443c140404080182041c401141001100000030303850340e0061190034441c420450310502542a014240c1700100251800010426581e003800b0302007115641c012200700e411440040744400c10b4032001401600254011410001201c03025100c01d4090715221b60700ca14401100002c9548050003021b000130343c00e440e15140c00d482e000110550764150748164064100c1e400b000300079241c44c8010080d40c0d0700480c0c00701d03046c1c884001c81e41c20f01e02c2e050707030b03450b00f22000003400b2658110540044c118400c54900c00c1c41d01e6900c5894403030882d0b10565040c8001900210041d01c01d24116000d4822401c60040c07452400161303070348122000714000350488240c20f40d10200720490700c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 297780620 1250 297779370 297779393
    0x2701080f0c0a08270a03022a060d0f11130801020a050a0804080c070f051201050c031609080123010f030b06010c050c03060c03090106080c0d0210141204 67
    0x31551a00c12250612808011003402901070310000c00101100041c1400202d804000c02c0184494400c0c1c40e00004070b010f552292103c1406601501c140a4001650016a030b00742a0018004094100aa007020f04100d02e80c0c4c00303010400d103020b450f5020b044214074180b00700c82803003100d0415540d4685170b240c084111041c880e8010340942c0d20510440a2480e0820211000240c1c140f801000a43c3c86161500c924040c42c401c414051258200106140c400040c0c542c00f40e450441c1d090540400b580741141c240d402c00c07517603101d90110500100e040040d054075982d981a0450070111a900e407200540c600b1524030300c80075400a801301c0701c10108400300c032150314050310006409118040c10740d00c0309041c50101504690400c030a100300030b418042c0c00d00c145000381400a0950b591410300d00c50119003030300140c400307030f045505c1c01c000000d03004400102e012071204042e04903000e04106030200513000d080d207002802440400c00c220658000914002c1514400d114400c204600740380c1866107400d071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 297781870 1250 297780620 297780631
    0x6020f0106050a060e0d120201020a08090a0c06080709030510050a1b0c02060d0b060a0c0605070e0310020a02030408060907062a060b062208011404021f0203270108 72
    0x24074052003404640c644901030401d99401d0308200c0c01c00c6034540086419250b0400c0c1c0548841d90342024000c0713483d411740042c06000580e039a000e2240e221384180c0bd8440c61010300c0100b47c1250000c2c108905c50240b040c0c01d1348500e05041ca0320f442c079540c1e03c1c1c2c80e00f040e004a83c806800381c0c0d55401c1000c800176038464030b0b0710b0501c03201c407130301d5032101c601030241003207000c0000680319a001040c6041c1003059a0441401e0781000743c40151240768103030002c0c0100402031001c90300a414803000030341591041c44844507112000340249500d45014110798004d502140044045000400c000b1480403410490305000e05034600003030000900e0044014280b00711801001c0c900a00340e0700c40c1c541c070f043c40b0041e10501c2d80c00c101d00080d041c5e900d83c002a00b9110710b0f488602a4454803008802d4400341020380011541c81030000e102d591a40c140f0b04a5402003203c000b0f51040744100288412003461804000600340c5004407458035210f00064500e407901400440070104c0603003040012543d204d20350300d8001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 297783120 1250 297781870 297781873
    0x507090501080d080c0d2d0e030a0302030a0902030628020f03070f0e21100507020a080a0207050a09020403050f01051b07050102160b0907060e0a03020f0d140706020f 73
    0x194140a82c1d141c0703071a64054500100301d0302d2400700d44004004d60460300c1081041904111130087c00340c001102884552048000c2ca25580d4600014085405048543d0368410041c5107040316042c0154001d40000c0c0800c403a05598070a50401a141044014043c220410320150251001c000441d4600086604d240d407482c0180035011403000820240c4e508000b590516810400030250200e86880303006000690065880b01512010750f040040303440182101815a405190090201310507103005850309030060b4401e4400c4004030b40c8407c003801024209105640e5400e0713442c0c00180e00c1e1006504208420f960000d010020440c040000140d000061002840715281c00301041d603078030b1119000207400c4139001070a0001c0040030740c11a080c60041421171101c030012414801c2003540101c85400c124401e01c00040303540da00540305540d505c10020159070300d88e811942842840701d400c0900c82d801404d00c01502c4002880e000e16840300c210410020004c85280040080c5030101c4032020b4102d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 297784370 1250 297783120 297783131
    0x1060810060806070507020321090111011107240f140a0504030824040509030c0f0312130618030c06060b04050117070e0a140f091311030c04020412050709 68
    0x9000b10f0b2030b59000d402810310980340e24003400400d0415400c03624400c200e0300c059580135081081c503000303002c4026080e0b81da0490828032448040c2200c2c43c109003403003004810b0240d5000108011151900c6400c00c524070840c00b0340b02100a0240e85039215149516502d900e03285080f01001043c00768040c01d020300034400307030510380c4029140f1a0301030030308140c01141300c08118201c151480c21b80b10618014200300310524007441031a440350020b1156144c14000c15100314000000042078540340d4001e4851291035072100004440140307421402158a10346801c403585024107035080c000e104a000307403184440703194540f0f411350840d90b2a4100b588001001e01c002e10840c0d80c080c100090600140001d90382540b100181560f45985c0c07020029070140c0c1414000c20522001fa9503440400c400391250100b1404a4080203100c24085030090300c01e164100020020607059000c1d40380040006c0c0a84281c0484040440e0617032f40143c1056100c000c51200702c40810208221031801041098803c014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 297785620 1250 297784370 297784379
    0x23010e10060e120c03070303090512031c0c090504021605010507030614060702190b040e070e0f04090606170102120105030102181203040914180a0305041221020106081006 75
    0x4107510114200d0043c3c90340c200c09000d110341080440d01c81d440040403626495580d16004103048140d0107024000d04c216000c01102d5400002519021a02c02d030754101c101c5010300e440001031007222440c00800030460380001d10364850b44010702c244100713010000342c0f60030756040c4903094980203415441050711301001013003403072041c2c0c0e19101c0d50380085803c550340707400c1800007480314955101840100d00525500042007900e000042c070803500d00100007041941e804030183e070200f4004a0003278004000c5541c13410329107400c0c2c0c0319581142c401c0304001a02500e411588108032101031002003260360020300d000d0f280b1a504406801008100d00030741c038003004a001c00d0035020300442da0500808121480300c1a40030203009070b8000d440a0a0100101400d0002c0d003406000140c901c440c00c0c17250100071005481c07000c1060010b40e901516001e26251400062116100013098151014030000c0701ca440311409075032406000070100d80c00030901500345100c140c24041d000c241a005580350100410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 297786870 1250 297785620 297785627
    0x42102030606060d02040f24080c12070302120705040906050d20130504030504090605090f18010603050a05010b0315150108070512070c050d031a040e0123010e1006 72
    0x1548803005582c80364442d0f91000c1090041e00030380c7c0080310040d04410000c03940000c1c130000c11516114448800c2c05000e0070300030aa400311030075142c01c008440100070301c6804a00c41d90000d1703002951454010b00c1c04800002a11848a00381c42c00c60004900003410815010309000c1d00300504030854100c045240c40344d864a502040008000229541c90040c00350196501c20050700203d0306040f0500040c9840d02e001030007607100d4081d041915241c00d81c08106400d0080000d40f14070f5013a00f400c80306898400d0007080d80d1840130b40300440d41d034841c00007100090051081e41e803070b135210b000042240c5d601d10b070826040c00406503401e1401c510890030080c2b0440e5802403030004c21000c0c2400f03480d9848400d012555403160718002c0c29441c01980c10700c50803c0d403240c4000105809401656031100c0800310032015643c807410b001020f02c6420313807803030794500c0d080d03125448990503c3d000248989104800f03000d242d002113400b4442006030030041140d103581c1d142c016801895045000c1a43e8142240607 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 297788120 1250 297786870 297786883
    0x1501090e06060d031103070305031b0c1e1906020d0f0c050a0f030b0a080c0a090515190503060709081011030c0d110c0a15020a021c03091704210203 65
    0x580325460f031942d0b40b070915014030b2502c0321043c080700950b0368900850402401d541e0068402601208103024901d81c5001004250343d116503603500500540c45107903a0341e44440d160f00180b01c84c2ca0080c440018031008058030607405a62103004c015840e9100aa0358030b045030f2907191003006041c200320113588001e500c0400c8401d5110141010104800c003640c08034000d0075444000340c2c0110102c0400b046005000408110f00c020480e481d0301d0154850b6840ca003954001d84907245501841c00c605a210300c1e12079148172402c0d82e02054101042d55a800181c980701090741d902c804180403890074082003800340985c032030032541d18be000e201f40c0c244001d200d0082d101c0104080c862080c0030403513008110103900149020f2080c480317155203030f51800c90080c2c0c41e008201d000b12044c0304d07803601020300740c50f1328025102ca0240741e4002e0300d81c004000c1c1d040e001c0038125500b0764040543d030341702c20000a01580b40310a2000d000c076440980f9141000c0003503001514102c521020101001e10701c3e0010307600003901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 297789370 1250 297788120 297788131
    0x80c0604030b0406061206020702030c18010524070c030c0e040b04060506040209040f020a02010b0a03230307200906031c0311040911030402010311040e0133021501090e06 75
    0x52004a950f581440c07001411180c000c40b00c1e104d1404c50120900c4407607006808424000c4042d0340310701041e901007240701d003001a01c0c1d81804480c1c0b801003106140030101c1080f041428400c5900360450400702c0540c543c020a8222a842e641c12020700c03c0c00140b00e210405411040446559030a00e502d400c0b00c20b0000920062080341c031000000c2c41c1c1d07211a0181d80348554040d005210000760617903400c010307400502d034050040d8a0724000240c1407400c6029641100d0700140750110500c0d0004035031008000c4c4900080152204006d00c4001801041035030441b0042d00c542e40e0001d8811104012601c2c0c000b03800c1303611a50000010f42e0101d908010200e5a43c81d003400d0001d590700d580c1d00703c1039042c0500d40c4a019010700d005171070070820300303000001d52159100740d8080040600121060100307000303074000c0780514086540184001b4580540ca100b81c070703c0c0038000c5c041086048603018681d540c0303403003190016000300c030800c0740c192030180c1541c0c0941402d12091000710f0540e05107994030f0000411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 297790620 1250 297789370 297789383
    0x606050303070b0c0307032d050907061416140f0111071e020f030d080f09030705070306051e0a0b01080709050315040807051e0d0507020a0501110c030124080c060403 73
    0x12882660003036120501400640c00318801c1d00342300c403401040382d15102c14050f69250401c000101d41040c04900c01080e01d20310f44030f000c1b001e42c2c40c05054500350000020351303084034481c44881001c07500350ba6049091411400040c050100c5c0700c103101d070942d4020280021030f040700340803980000305210100c03441c16a103403401a07604140c03800081c3e150880321095503014051405041c24041d030000c01e484c41201ca004015280da16940c20060352031045070000b82c903e07040560b00b80000b035142d81155802054103501e05115280809290044800546441e9103880c0e81722000255542c00107603050780068207082920034146400042520303100c840106503003d480a10010342000202000c2c2d940060304002100d00354081592103010a07025081000307014403e0f26000008140300310210343d182c0d64003900704031b01c00c0c1c0f0b014011341360b1100c0502841d0042c000c4420001550300d013441445056003252106124550707948080c600c0c408050f41018005400031150000ca640b2400101c800b100d51001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 297791870 1250 297790620 297790627
    0x90501300c03110102011e090506090c030d0f020705040f14130b1302030f030a0e0102120711010c0515042a051c021801030309181b12060e130606050303070b0c 70
    0xc0040b030060070003400d07081c0841d400000081f4640301c154054640b4038410401c55145484130150983e41c0c81c00410302c950706a100c0d280c40343c2e0b00c038460902c404041c00076004031425070382c0b600002801d548034600d9209000b5580e640100756000c00000c0d0700d4100540000707540c2c41e0100c54030781c1055113000a280c1c0806104003440074046450030001401207902c16015030740c40321040340d8000c1c81d800d04902c042d0300612078a440c10300d400444508854555500184030300d0441d0003c001034601c200402d00a645502801400c0140700041001407403203684215100f041d881509660004401e03d0800d910140c1d0241d04000d02c0700d40c0760070800f038910b5450300758440480c035500d10010784034010070056400074120603400001015040040d9030241e681a10070000d4150800d14500c046801c90a01d0600c00041103000c60181401482502d00d0102303003070710210380252211031448141d04103480c250000080001000305200c6170784992400f4141c02c4019505e440c1480e15a9120100c0285c00309080d0030380003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 297793120 1250 297791870 297791903
    0x51c0e0d11010311041d041406101509051e0907050a08060f0409150c120524150f1e04030f2d08030601030c02060603071e090501300c03 60
    0x13009440050544440d8a0710408a01c604003114550948045650034103090b04030822880c08241e66101701a80c1e0154003410380f400d0003294800d4519a10201030240311000807880da100c210005800d000711000320441148254280820b0b010001d0204003000800d00c6021021a4042e0040fa0030100448a803070144001000040080443e8000200020000110080c84201c1a0007410030311105860345a00b2081218505080e074030704443d007a5803040c40002c100c8602c20452001c5100030000b038110070180109c1d2400180540c03012004c8586244081810000c804180e00d221140900850300c41e401c087c1380d0b9503290750102c5603132401030105241031803413052207070120a41100c41590002d888038440315070134249c19982c01950b520740001e040140401807180000b40c12401950080e00500742c0c0c034a054249004180381107002550580d041c2c900040c190254040e050107090109011040480040c1e400705400621801c0c5841d4001c182e8800408100141c0381c0d54200c0c3e400c4403415021034643c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 297794370 1250 297793120 297793151
    0x60d0e152e0b21010504020301150804051002041d06100e01050d0902040c080f06040603050601060c081e1207021c050c0f0d030204080106050402030912070c03051c0e0d110103 77
    0x1030303000144034030700208000e15401e00781d80c0301e60300d003940d03410034003d540c0d890b00240803d0380f01c00d000340c2016810040303503044024844d14540358001d0040f4191100f0740c0c09141c180080e40e00a900c04120a15401c2c542103001340901400c5400c0002241e400701c03c0c000b001d4019100d5810038900341d040c0500890303e540c48410b1500101d440360340c000c108004c14800400080c264920541d44240860b1685c00021080e09040c803a903030640c1e41040040c40d40340c1c64850202c86007008094100d8002409100c00d160b035083c4400f0030510040b50582d41511080c0189004400000003483d00d01150b008000900d1081451000c49407080c509183c141d80d1404441000d515004100d0002d626601c14103c1048409500d50f0241040e514048000c0c8040780d07072382003040164041901c20f800541c0040116003100030010006102d11846411030604480d901d4807010305001c110301020900e81c40341c10241c40356544c060304298819104440307401b030440d45915482d500324880c0d80c280307041c10390350034454121548 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 297795620 1250 297794370 297794461
    0x90f0d0c0e041a070f080c0901050d05040f020118030b040b0414031b011b09090906090203030304060f0f06030807032d0e030c0a051e010905060d0e15 66
    0x6200010440e0900f071030b00d50b15070a51001c552110240007404a00e072644580a15240051281d40c0c0e000a529107044114181c0d001c00c0509041c0b00d000c100e941002e505070702447d80300d030340158410151402c8500025003020042c0011818640c810b00b000d01c002450001c0c3c2503003007a04480c50219070355952510380440e61a030f1603a5050b034840403440e07025010881a0f001489000080240b10030202d5090900c092028050440d002c42c444140c1449074203056400110200c2c011000410745910b10380220f801c543c82910183c13212901ca8400d01d020390a80d008074849142c0302201040581d2658542c5100303401403101c01000c2000741c42900c02c0220f121400781801c1d03051803801440100c0640c60240001822984641c003e008000c1c1045940c5080c4055108032400a802c402c5050100301c00f01088408510300c850501c0308540c0045507540703420000d41140d5600e00c034001013900281040780d00d07184c0345070400c926408600b002c0018812050340e6030002134404541c800038001070145182d02d03524 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 297796870 1250 297795620 297795629
    0x6030e0304090c022d0d110706030b0d020402130609140109030303090c090c0509120f060c210a050411090402100c060914010501061404080703030503040201020c0904081b0102090f0d0c 81
    0xc4288003420421010417000800d410020482d00b11800c0c1c60350560fa1822590340d16001e036003060b102001194041c1d00080384404008080d400d0f800c0341075000500700c1c0c00185510a0020015a0500242d5040510035002d400002c0b1004103003417010000828004403404018201070b1265020703410000302403509006061b5041083c001002030a030014110f4209050f814400d64000640001d01500841c0c0b40c4084411300c805401503030390307200c010385e0142d110704100d0300c201c03000e5807500c941007960503680c0d4050070100f5400301702401c1c1420072249a8030752408982c812103442d400e1100680e12551441460906420314102c0501e15003024001000f007804060102c400c0224144044807040d0701c0103040e18110b80740c0b606048a40c8040d40303080c0c025401010307010713449104144042801400515030040c8140f048513138100861010406901c002d807002c441c0c1207008556169001e4101c66404c45c000030507002142086030100000d02114007890519000305039040c040c00038840f004100f44044d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 297798120 1250 297796870 297796903
    0x1312020409140c2e0809030408010203250e21010e0a05010c0801080d0905010309142a030d09030b07020c0607260c0d0e030f070f03060606030e0304090c02 68
    0x1c040340744400da142d42c000511144501c2d0b141100909841c4002901c2841111074507000030604d001c0782064a884501500b68013461200b4800001d03070380024002075101b00c146a04403119040c82c8007049040610b49003c0d2414061071100281c2c051b19a0441020b20f030700e2158056250b1a031b45076245004003104411a419800388a640f807003801415007004100d900c580d510a210f0340e81e101081501c07503462100328800108071000c1002158400d0f0017072020740e03015400100710b00305003105131441c16644541a01c11000e200081e0010010703011500b10364140c01350050401210f000d01d000307004800b1350000404090300e1002042e403c40c0300308008010311300b000d050700e551100603007040075039800400a07800c01c3d0201680039900000500c0c05454626450b0b400800200382c55071000c0e80e0345103c8002c400c1c2c0512407447c01426604041290390b000b4582c26003148010741c21800c1001c1581d401350070a50500d81820815210050b00204980403941050740c0040c014008003000c80c2400408224001350 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 297799370 1250 297798120 297798143
    0x3011104031103010b060304030309150912110d320a2d0c06051e011215020403022101020d1505041d031b100203040b09121312020409 59
    0x41919001030007542c2c021012461503194540070035017070f01e101d198103941042c818030208001901a03045800300d070740714198680d0401c0ca9103588000325441e41c441941d600075081701e640540d80e007110ba44d0894903c094003420301c00c2071020020340030041b4403c40164048002080070300003500c0012140001d0640840035a4900300c00100030300400040010b803000007159582004030303501100c00d2904040352074440c13410141840d29060001c1c0801041e0810760001d60140000c055000c420b02c90191076401c0c0c4151040200d03040c01c191246903402c2c0000f40b80d20400023400582c0d1080b81c03e507404600c16444138104022085100d01900810180688060901c526203040f4411815580261402900c0400101c44a151221404460100f4007a03958008000e40104038002c107000210202541c070807a14804041000c0408a0344100c80a540c3c5403003240c02d00c501d416050100308900003090541a0400c001204400d00a62075441020020440e814180085490b2500001c5c021a0480a0b840c81e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 297800620 1250 297799370 297799391
    0x91801050f010e091f0915080f03030f010e09030c0d08151818031e0403060b03190b0c09060c07091b020709020d11070f02010e18010e270f06010b030c09010311090301 73
    0x191f1140d05d000d40d01c128000c00820b61038122000058a206003040b55401c007003a46440c11709000400094a80e042c1c6000410000c402c5610800010583e054284d58500103403810544241240019115591003005150002102140081c80c85030b000400c1c070402d800e01e10000d015540c40c1d0312508410b02001d151221281144071864400b600860b070050b0381c28043c10304000c003055114903041c56a8100303030190100d030501241c641000c240d8841c00780706007546001800c1001603c0e039000a1041c026690200303031305010b00d425901640002090150710315554009285020b504c0d00c600380a0f6510b00b0380e0100303810449203000d82100a250041241e0f196803507199040204100184c550103078045440780c0c00600d0301d8101014a144d804060802c40c00e50759080007407621000201500c02c100483d51250324610042c3c00d42d20036611405103030020207848421550960412105078411021808180108005490394030100c0d9540002442d0001d40707100028001310307250192541030b0ba01076190411901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 297801870 1250 297800620 297800651
    0x304140103180b0702160806041b260f0303010806071b0807031211040b0a0503090c04020c0601031a040b01140102070b0301080d02061501051e091801050f010e091f09 73
    0x2805501315900b6144000140352209000c104107216080c403e601c050005804950181c003d851005800095030103042d0b6200ca020f4a4810707101801b0540c01c0004040c09a03a100801804883d04a510042c40c10b561400300c1103910f03050002e20b554248441c83c0c41d10302e60720103420328445286600c904ca0700c5d15400581401400405079044da150740310303d0003c82c8101c3c400703042c00b92401c42c0d0004440340c2c41d00040000450b0307160405809c1c1c9020784510707242e26103280d5031070010300940c1d003891004141641c550b0400c80c2c070400a00d07550110000600341803001003450b00c02c01e103066454406c00c680041c00102c0c0100d203411466806402112004000461603090100e0303e501010550b900311601030b2510b821884840d0344220001b80400c00802142a50050485850007024040100c184c188418240440c20000326400317021421100203005021900c0c01000d0301c02001000e180a41c03060503120049402c0400180c00c1da000c0641112007542e203184503071181c0001e404203404c24440148400d0525 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 297803120 1250 297801870 297801893
    0x31605060c03160f1407030b06040914070902190503040201090512031209030d200301060e011119030f0c0b04030e041d0f150c031f0b0703210608030414010318 70
    0x221a40400b0085c1120750050028541003a2034210902c4111621004100002840b45840031103039211000740c07070305155805015007001440c0a90015030b0b0f44a0180d1075196038945030f034608052000902c10301001d40d90004500c000d4410a4400e000200341c07800030985103008440501d501e41340303c50100005500084060402c44c9400901804003140e114080702074022040000c1c1420702c030500040001d0f80c8190f22907070701900d040c104007860020042c1281d06165107215010220354840c0030b6030b010540e1243310004032400614003a00103800e56503400711140f8000e00050b007009000c0c0c0900405a85aa01805040240c05c071805252424011041c0e107804050041152a00a004a00c0351050303034580114807a02d85181c4240c40c5a640c0c40003041e40cc030101e40511500a44502c0c0819682802e800800b4454000c2e1281c0c001d4040390390700d80c1180d540100046001034100b000400035014004203036001c0e51250042d00d1103100c0fa13940101d00502504a059403540c482c6041071f8180180d14242 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 297804370 1250 297803120 297803123
    0x70c081207110f03070803040204090c050303070c0e01050f1309030e120601031203090519050309041424030705150910050c12040e0c0c0f060702031305031605060c03160f 75
    0x584000b0100490f01540343d0080c01c07005002d01c50104000b4005281c44c1e408070146501c2520382078005a00c130b0011a1568001420407038452080e502c3c1489074904201c00c2c03600400c0121000b6880214803004940001e501c4148052a41d441c0e9004200701401002c155040230030145c003016941003071801c21030781c0303020178442650043d178041241c1c52958400e0284000780c41c0c000c0c000b440440f40d110b00c06104040035000541c1e060000b0300c002407580d41e031805500c0802000c1e08004609041c041c0690041a040002d4801e4050140480c1d00540e00d001c0341590031210115452041c2982025010fa8075104610005a0041800e030600d64955001000b5000d5992407030308684c4140b007151500e0b11540304a01841d40202004000200781801c00130040403044815800d407200102e000030407906e03005c002d488000250b000881e00141032179000d220000108811401454040c2c0c01400c441c10301c9255009070750107010b0001e174440108400300112142048560510010400b103420880d0f001e003a613220 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 297805620 1250 297804370 297804373
    0x1504050a0f0608160b0703020f1002031501020f0601140d0f06020304031403092e1406011b08030f1b040f0e090f100b03070519080609030f03070c08120711 68
    0x2030118643c0c5001919068021411202c0d101407418084000d2a54103d10422401c5104140c5050303951041406104d0035003107203820160b228100041e00e0400792180c0281c29045500c07a484098003060700150b01c1d81114078461002d40405040004203c080210103400380401d1b001038028000c0204590007903100724000da445040180082c1c0e0f40c040c00d84410340d240102e0354460340ca0310519408000d099164181038019004029900c40031880031340d005400050214880c200402146503044441c0d03408030702c2c1074105030580201e40e45d1041c10078080545141e0071134800070001000c0c010890b4841450b050907a0744141c40d1aa200184818190380d030180146c9082504045204d4120000b07800c9001c007651030280081c4060031240b400181541780c01c06905100700d01002038a600c41c12542900502c0f2440d4000000341031075101803504002901d45c0409510410044414901e070a081e81c1d0445014071f400b000b41e0145090008281c05410b1251034078903241014805015001f02c0281c001140000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 297806870 1250 297805620 297805631
    0x30708030a09050a06050915160b070e0402070b15010c05103c15090c020f06060604120803090a08030c130e010b0702040216050607120b0a03020105040501081504050a0f 74
    0x10284000f11004c0d00c05d94000c90814814080a450b1010541c4a50710520038801c0c01d0441140c03906003048122070b01540d4481c1d8810500c1410380e440444101e2400c0140c07820b614009a540c2c0f126940000201270003440303544410700e00441d81c2728402070b84400b6080380850b51041c10031001c21005105011074409200001c16012070110010115094020300c5100e00d041d09507107041c00c1e540500003061520030140300703240022032981050b1190101490040e4014488021805111898181c001e84440c1c407071902400708000a031010b0007004030280d44100115181e843c1c03007207080d240040784c4c0c2c0014446071000c0100401f000e024000b5201903224121296125959000c1e010744000c028014500c00d8201040440050b0400340c005141c5220f41d1410701d80c00340716644a2604200d01074680e580001c1340d09600001c0400140215040c804d001c441c48001036203554006081446944076503070502c0044d100044e032050006182d841c42d01701c040e01c18400c52a155001000030303d1240004008545002c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 297808120 1250 297806870 297806879
    0x723030a0e090c031f03050d030b030106290c010b0406140102100c050417070e150a1410030c1b03261005041104080a030302070209061c0201120b030708030a09 70
    0xc070003032801406000411031968031080754003d03e0705d801500602d089403011000200095041169610340c10340ba607000900c200200d002c040c20b40e00660b004001280100303118000700c0300031003081900110400715166803420f0400318603024149081d00b0542c003a1825600240c004070b0900071504041c030903429111030b140c41002500032540803543d184000360040c4820f0007460b0301c03240c49001c0348150404035204280d8605a0401c1c0100440d044000c00b04101018242070070b00c40c0d50303503002d03062000d000b00040101034003003001c0c2c11440e248101055200c803401c0301c0d042c3c02096004844001c0800c0000600424103000c0c00007950300c03042059450101039801250200b8800d41d902440c08085644e00c40c2d40b0b00010031020702074401c001000070004110000d800b990401414074070351f201f0b450168943c1c0042c0108681d8110080100340101707038000924101e01c4500121314100c80d82420807080220808034800c0041410b40c0c8899018401c1c1d12010803144000000b502c00d0380019640c1e1800c2036260b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 297809370 1250 297808120 297808129
    0x90c05010810030209130204020d0b040c09060215060111010c0e0102160509040b0601140a090602191104050405031306110106050109080a0602071106040b0706060b03011a0723030a0e 80
    0xc8034030300d0142019241c24801480c5c800702103038100c0310000075940001c80a0700010100c3e03100852a10f462a500d07510800281800e0250340b8080107503040101c025481c1510103519032543c80c0f01d0308401c0a05c2000074415a000e40150b21342450114000c101c41e64050030702428032001d803804cc9016200303070f400c00094035a10064003070640d100901001710b95210740c1d40c0d00702c1000e0702400c034605001491003c0c0741e00d03465001c00350100c1d14155840a6400e450400083d0820510f80390100c4038007032041c0c5880210b040100180c01201055400150b42d44d00c03410a0b60860040c0320211181511904000803000d1f4800381c502020350352103008021803a591401998901d10740d101e410342c143c0104040b0710201e00350f903000d402001c0c02104806a4001c200b0001159071340300f0b40000144040118840b4240b141c2841102d01401240441c103245504011411f604180190482080c082d000500c40080041002d2800c44407201d100780b00700d489c07600c800050b07280d800c44094600001c00ea944025841d251 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 297810620 1250 297809370 297809387
    0xd23040615150503060609060a0804140a031b05124611070e010314010f0605010207180b06030709030b07091404020a1b0303020c0f0f07060c03090f09090c0501 70
    0x10b000c078000e108499980002d0300c181d00000c040030f601003004d10540e5159107940005260301e1109070b80355482440e040ca0841e0b0340003950080541c1a0b4000285500001d070054500391015603901400401c20000385445884e01c810b20517a58144c1e4804605a0b85000c4410700341003040c028095030040c241d10089807403a03914810005039864070030308000d110445006d20a54450041e540c42903c0c4059180d054039807402200f0781c801c544051800801180014082c03203032050380040200140051480d010000799546c0c4c82d4089c0100f40e01d8000315142035803400d584118007809000d44030300e031640f50121003c2c240d01e00c94403040d10b421201500107a080762180101c00d050ba08042e4450a0407c000b0703061100035040880c041c814440c2d0f84c80183e00c03800c6140146030711644259005130380d07480700079000d60400d03d2036464a034842e4000b409a510100001c40c45509941c15442c0c08a84101c0394102110141c429034010a5100c004580200b0494841d820a004180c01a00342c0200281c1d604011200700d45d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 297811870 1250 297810620 297810629
    0x11d0307020907051606020412060c0f020714180a02130608040b01120c0b031501110114010b070c0b0414040b060304080313020102011e050a0506090412050d23040615 73
    0x30b03041c000040145000d040684501c0c10b20801162800381c05945a608a0b0300c540c00c00403d15810300c601c0000c100d00780c010444030200500d0300c1280600300d00c1000e55113191602402058814107038840f4942e03100c0c4858940c2c1003010b034200b00306606040007484002d503c01c00c41113a41001044001c2a614041c05100c1d0146500c81200175183c1c1c039102550b5015107500300221601c2c4082d0f0760001e5035445070009035009490740001d2954441011001410f0f03040d10341a090083d0741820020304845001800315170444010074900d540c0c440307252030310644504c02754110315007443c404100400e58000f1441d000d142c4901c152410400106918200240760200325801040d00500300001058480d0319107a41c40401d1040c000420038845c24080d400e260b8080c04031a0942551301c10820041804502420742c10480030741da6610f1324202520780c501c1d600ea800c001303c014844002104103c01c4542c2d44000c1050020140c140d240002081004000340401c0c0da040e07c0707050074078240d100d10511001164003102c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 297813120 1250 297811870 297811879
    0x61407030608030a03090201031404051b1c060b030703050114090d0503010e040f03030608010c030b0310140408130519170609030a12020f030f07090806040503070f0221011d030702 79
    0x1e013510340480142200000403410141c56842810035590314500700c9000d0361007223025080c00154501c0c50000c0e5a041800c4601c14840105080b0984001204a06089420440104d04a1140c84c042454121107031f00040c0950300e01110383c3c40004102d413956000e10101000c8e944407121003075080711507000078001c0480d0090038034007190002e00c2714102100c015100381000310f8990b0766800c05600b10b4000c014200c02080d103e40e200c11803442c0078002c0501280d0f65003000c201d0300310703001030880c4902e0340184014049000003c02c001c03c8201d03507118400034000207101407000e60400040e5203c109162280c0418003280040a10b001032000c0740031442007030404002c6040103c52201295800c1041410f14500c90b400c01c036003014415454011442010b0046041d0705508000ba0f004050802660203030038180c01941c02e12002680110448608540103c030000301166180000ba8041074580024403148491320200b19000c40d06420484000f8040e49595040c40c0108641c04d44a11401c003009522 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 297814370 1250 297813120 297813127
    0xf01050108150403022a0307060203040806040b040f0605150a050f101d03010e0f0c010810050904032a03020c010207030c090509160303020c150f0901080a110706140703060803 77
    0x141d0740400c000c0e54428000d05c1280c1c4c0e031020400a609011852084138030a1203d003000000b182c1c00d0400100c0010015031000350f140c00d00d807040031902c03920040d200a2002e80020085814031080580b0101403c0d080301d0200298241041c001101c03070f010100c968003030540044002a1490020780d070190045c00039100b608081e140200807280c3c040c02d00707081d121240050042000e2610248500800700440100034125500805612851b00e020044414100f20701c140800444070044203580f01262002d541140b4581c54a140c01c2c0e48210a800e00340700111070101030858004a48031140c81c040b0300980030350b0300108018004a84903040c501020f400c8100d0401e00f001880080d41c415640400900141c6801285d0701001c81410103469101360f005034450118910640307444040fa00040c41c180320290702d0441d02680c400058082c50081c01e051010050000d0500d4049402c038298803100d4040e020b07501e951900e84100101441035960002d001c03404001201e85001e031003000b081d0f07520340d4011401e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 297815620 1250 297814370 297814393
    0x61205030d0509071a0d050906010b04170703060c210614012607020706020606010201052202150c0d12020f121f0f0602010b04110d0218060d050402030f01050108 71
    0x2821010f02120740600c80c0e0f2000081034046405410410004e100300e081d51455042a030105903070740540802595002280104248081c0700c08881c1154100801074040303002840d24941000c0050b40090006c5003040746a030421a03012504050b43c00641140300040340c511041f250032500386000e0802c80c0401d007442c10040c0d40c007403044184d144402d801c10bd10859100d8400ca14130354425240c010140c1d0004005104040c1c0501c0130a51181007840208a24030340900c84400165507442c98000130109098170405548500b510382c04803041c0d00301101c0c0d8a18103542d80c0c503540c8041682120010b0010b90015041910900803244008440b4215034100f010310442000079401c040d1019101d1740e50350740040910100100380500424001d00401b0340945010740190a40d8540419988150301c2c20304582180d4410201741d415072056101e005856400c4030715412095062192413541c000c602055043e405c0c0f171940c05c410b102d548280c0c15201264241c1d13500e5800c4e102d080c06160200d4021505406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 297816870 1250 297815620 297815647
    0xc0c050705060c100207060c020601090e0d11030c120c01060909020a1a070506040615320301062403200909220f030906050f1b010605031f06120503 65
    0x883c00c09408290f40c03c0200300e03461070b030490340a5082100c2c400c0d114546c070341c447d580600029004119080c010310402c042c00d000342c3d1b10b0b039410002d00424044007100c0402858800c100380c4510104400441c3c061248242c490f1100c4d41000a488040d0341c200100443c2c202c0c00742c041c242c40c066025210701c0c4040d080840e8100c0c01240c0c003548040d107090030320407140840c03001c001050081d80500d41c0010044076640030810300f8840c81d041055440c0c2420045102d950b1030340c025448a240607005052200103d10000380500120350219190500f045105108800050400c0c3c5250f00c0f80e84042000054051000140809207095543c4540051024110300d080410060354408801e070a9500741659070700c011810303100c2940007959403200e1080068100f40d0801c5902e40a090b680c01c2c980e0030400540c1401419204801fa0051036804110310051208000d41000004d009c0c0101650019001049100306141c01c28500075182410f20307100044020001c04501012074210f4003941c0f82400c50543e54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 297818120 1250 297816870 297816877
    0xe0717011203020a050a08180609030c12120c0609062a0c0a020604080105090c06030606090d1112060703150f060305070903050111070b0c120105090c0403081207030c0c05070506 78
    0xb5029070290316407620000f242844440e038550f119440c1d640d00e50000c80991488074003510201d038000c071402c010065507607a000072940a040422075140102c0c0006002e41c9082104051150310070b0000400c05030805007001c1400d600c11240007044030680e60310b4807001e020968030790007000043c200032240d0030116042c00c4000c003102c00c1d4080441d96512020350106041e60301c1a0700005440c2d541d0300601c040d07140c081c41504071a41c0115202c6066003018400264240b0815880e144140034030320040301080029003500f40890030040c0444144221145100c0d1505000c40d0501c002924192840c5030071703035007000c01d0300a1310914010503098034240312040c0d0080c6000303031a02c0c091240c2e501c00040020310074014500400d4803001c88903182c10341031030129403c001c05091040c0c0c0b4079040c00041e0300c00c00c0c0400030504441d01240d5408407500d580c0c038540842d2185420181002c20000341400c50300c6419043d49005030810b40d41000b84150300c8008070391440f0042130003400c6402414041000d40783c6800603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 297819370 1250 297818120 297818123
    0x30c0703031401120201080a27050a051002070b07110303041e022805090c030f0c070b0f04030f1d010f0212030a09020f0a0b07061503021002070e07170112 68
    0x15a2180300a502c04618026803000041c8034070140390b00c0865920400315034004038100b60a00162828511048080c40ca500241110500c014480810300004100c1c0440c01e0381c005043d81d1034035003103d1040b0003039480508140c4a80c6140c1000c610300e035204403802c40b229960071000c0c40c01c60300d60780e80b19041070000c3c096404c42e10028545000140e039569054000340c83d60000900c083c0c2940c150320a01520b900d500880c801d01442e010041500050011030394050320300d12a0300c90903581d60500e580a40154030001d4050900002082030403c01d902c1000e00842c0252510380e0206046441100d400e0000201d0200c0c024640e05a00c3c140d50060b1b5100b4501c4940340141c80c1e080c2082ca5145459030812203088022607150359015065080c103044c1c00b90514029942141554103080c80c0309154401d080c00104840d940302c0c0c0301035000861003a00c2010396401040c1600420803c00001c0d0b5500705405210101e164000128085501800c2030274001c200034040d0364410783c071b004061022034483d17010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 297820620 1250 297819370 297819377
    0x40e1e0c0304061b0306060206090304061d0d081306020601170a020409020a08120405040606050c0721020907020d030f0c0e010c0528050106090b06030c03100302090106121a0105030c0703 82
    0xa248200d6030208044182034029903030014510b440e10700009e140a4001e1f0203031000360420001408450790280c60207610f80300441e0f600c001002190042048400286000f400589021821462990560f4030410440790076070700320b540c240d80b152220301c600900c0d4100003140c0c1c0e204404a0006007016045044041c0c0010701584501c2d54074480c4500307068903001c44a0303c07110005824000c91a00d40704000140c02d0b81d00d407440c2007000d410034143d41c03803843d4060340810112898541003c4080b0640b5000d5007170780a040c130b01440c1048000a0354601c0729404007804a81010b00a2024000c28882c4c000481e0b00340e550205144d11040054409030030142040d101c034014600c0c01d221010145410000348840d038540c0c5881c000c1182000f608540341c43d00880651070502c0d01d0700600d031307032818240c9401540c121030540e500d40b940900181c0501080e4030007074000301800000107400740c0094940009800b400b4040c400786103444540740c0505121504035002c100188045428030009001410102c0d12a05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 297821870 1250 297820620 297820631
    0xc0f03091315051e0418080403031d03010c050d18050304180b0612182b11060709050a1406040603240f03060608030309280c0b040e1e0c030406 63
    0x45811899024001000d030304d06114624102d0403e8801c0c8609207080141c4058040c1d820b640e00b1940d441a88000303001c010480c04440b07076002c0ca006210080310300c000e00800c22402601b50260064100142050241d81380c40403010b034600c442c12444031420b90001c040d624142c1401c1000700400a00420356a520b5a02c421044035a2985030003810215080000703e100b514040311405880b1601642c842d0a9800042180a1003100c0300510307002e076056070791281a00c00248a08032500d003810010035019209a0042c0400590412004020385d1802e54240d40182e80b50980360b18240e424544c9507400c014104000c01500d03100727034815100d00006c0000b41c0400490880c0c2c10b007004440c2d03004039514a4842c1e6003041080070a100f9040280203c0003d1401c600c0d101c0c90240e1200144503001d1244005000380c0b1400410820b0700c00845507006207080a030984401072888103030054000c0740110849400451356071000007203002c001070903800d101c4445558986850f40e0030340000d80f0480c1c0789601d55 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 297823120 1250 297821870 297821879
    0x6020d02120907080c011103191202030f01061404050906150702030a08040e07092105160609031407051c060f09050307021014120c0405040c02030c0f03091315 70
    0x11061030188494100800e03001e81070881039821708505d00f5003103041c09000640080c158002100780c0da09211080388075040b115000b507041c0c903644085e03e182100d0711300c00010019229210710308141030710390555880301843d28009141c0103074800c5000300c40c0d110041c00300207200342c80d2428200040700d06070650755080000300e41c046841c1480750101119001000b0034140b00312039100c2041d039444902440d10042e4189007014550701c3d09601d0f000002c0450501e9085401c0c410104050820000b44082c14031649035554402490384083d40001c0f681491403182202a00b0800200541030f5840103010f00221241940315041d8000c00c910100c0d100ca407242800d200d59100707417041c40c2c089400341001d035958804500c104800302007188000c000703020b0310980104c14590b6920603a46004c40e8502c0b19101c0d0340380e040e141c144500403030740003e0780242041041e6809650120107010707000d400c0c0046950030111070600f291240155070116412880741c002c1041e00081917084003603010342c403140c200e0582da140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 297824370 1250 297823120 297823147
    0xd05060a150c0308060a0b040306200a030606350a0905060106031d0f0709020a090e090304150e09070c0201030e060103030806130501120b061c120801060c020d06020d02 74
    0x380c0d030070001040c40350900c0824075420820096200f0422504a030300c10303050007511076881c0074900000e405155541400042070700c805105c24002d65a81c941c041e1100000d110041c0504201e0165100142d0841401c40c020040c9901000c0103030322070031031001c88844d80001001e142000a081c0300107252030300780c84e0020410601540d4040d0026550102d109404080320801d45d105050b0a980c1d0340d40100c0d0045105000171668a09440c6c440e00c015135140e41d0140d0031130304060f0755001401803891883c24800340e00800002003080b80c51801004002100f04002031341c550708040d00342c2c2d0304800b408002482d81ca01c1110840602c074070504002607401d04058030280381110980046020800610034440e291600d07074400c0720000c0b4110001d215030740c1000c4004031a404040002041a640c41020070469a603d03a41054600703103451160703000980314240b4404070701913034180d0008100500004108144100d0214020340e401502d52041c203205961280c00035400811000e48266003845a14259400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 297825620 1250 297824370 297824399
    0x302030d0915110a0207090513050601080d030b01411903110c0709020705191a0105010801030f0209190608031209150a02030415020a1709060108030d05060a 69
    0x6484140c1c030814403900c10a04032140226142e00350070f4240b0051010a90015a120aa0311041c81c0820142c403904d58881000c84240c00c01082c6025600020840500002d1810f05180c0542c0d410b00049284100665081800d949a000c15804015094512012100d8100243c00603540304942c1d00d40002c4000c0901c0c4c22184095220080354541c01910039814000c0b0810340380c014030b03001d2810310f58044296458165200f003540d400d130046120000c5c1b07c070610021050000000c20003100780814a40020064421060442c4459840d0008203441d403240040c641640d500c624803c2e24a00319400300042118014a4030140c90b698882d402c100074564011100107000702002941c07581e15804000e0300c0590020309850544c0d2181c41440c2d0503401c90903056402800400d0010b940340c546080400c20720700d070480000303161400000c001260960044c2010701082070341411807510b40704d503050350b4bc5541c400e1164a007503600074000550840126488660070440003881c0600701a0b41c0e003d00c021011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 297826870 1250 297825620 297825623
    0x100f1b0303051b1c050c040b030403080118020f040605070c091104060201050f070219060f02070b0406140403020303180f0d020114070806010207060e060913050115050702030a0f0302030d09 83
    0x949034018000300245406410f646480c0c0300e43c40500300121550342d405003c100110340a94141c030344010a505e0a407403012039000e4002c02000c550759140038200034003030784c40a2154402c1c08240e46140c41861002d8400c1d01c0300101d1215486180501d040d8080380c494000d0181589d40c046004e83c001048074991181072130718404401030548552510700040c3c2142e400030600ca01106a2804000b1000d80c046142e080e0140050486030480000707082ca100200803d084170203017144002601c030144a412030a2a1041c0d101e03250a120071f0b11010f1880d154074400755801000342c0e000b8404142c509003160b8103000903040784070840d550840b07082c030414030f086d8440c02804050b0755107000001051111f00d4801d6401640e5051102290600000003507580b4602e224074010408080c0030b0361156030712082200c131040740c0100496400d00b038074900800142020303c03980702d111203c2200d4140e201c0c082c1d01580c9a5940007005415400f03415190001c82045125040342140410440c5060110641c402c415885 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 297828120 1250 297826870 297826877
    0x5042d0308010621062c040f0305031003170717070210111002040b031008070612050c0409050403031505031605300102120705070f11030c03030714010609060302100f1b03 75
    0x3045003506c22641c203a0000005040360040100300404075a5200c0c0c1c03060419031528010343d5955443c45030709164030a0b85c00007042d00031501894850900310b44050301d03685014408e4208000240342c402c069912a260000350040f9800c3d095550150103944075040000c142c2c01503410081000010b1002ca13801904100340c0680048203002c074001c01c003600c9a01501c0820000c1c804c1034100300000e0205401700d40400c280c20340301d01c00518000160000d40700200700740a4144900c1c1030038038019000c1c10b10118040b10700e03911405c1c0015036180004403614650080f63328200040d08250510440001c20b0070082c0707140c1c01408040340c44a041312180d555049510b0001a114100341a4820307100e80b02800010400205001c1040481c0b4100d004015450f0b020045204650720000071038107148007509415030502001c20741506020301c0c44040c0742c203404c2c610001c00c201c503124244c0104442140c04040e4001e0480c04294400501502d6014a94002030810308030031109901854002c1c50b420100301d000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 297829370 1250 297828120 297828149
    0x302061009060e040b0402011704030c0501140c07080d06031b0315021806032a0c070e04120c080d061203080f04150c0c050105042d030801062106 64
    0x1046840c6400102030110904240070007450f0012a60b1503240141029192400b00d00228017168018030a480c1642d001503028030091400d810302410300b03118036009403000c0d400d08415158a40200c01920320911400e03415500b064016142c1110a8110b00051140ea86d9a02c1020001c6141003024011200381ca00000c500b1504502e44809180a148030004400780144001c00201e507002d100440000019039901d03840b035031641301c2c2a69015240e802800440011502c081d80c00309810000c282c184000708c00c40e803640d9514440103540b40011a00a803007684140f40000407240b044817031080d000c0c0181c03402d90901d2401c54009003140d803031341d11210305001305081150406802102d0305a120460a101c0100d901c0c150303c0c0e60f6079a81d000103080d154250354841d003001c024000c0003450382094002d0000c000915181c80c158660004181c40c000031018159440720b41803509030290401d0b560f2646e00d80c41c10381d10301403084da5020100000c4111400300340c0c01070500c1c00300b14401d5400a00315120350080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 297830620 1250 297829370 297829381
    0x8060601020f0c030307023001050601110c060702060a14040b07060608030a17130f0c030b0f070f0302030a0b040f0b090a0b091501030b06040609030507050d0b1609050409030206 78
    0xd000b6164000400681201220060f0b582e4007109171107032250182c5d229080101c03c0030400e42c60035100685403200b2240c00c0325034801d0117030550041384168421707280e20262076180c002450355800024221940810100710170001424040050f04800b10a828000c03d204420b41d901000c03500030b40c1020741e180c08080782c014240811402000001c0c050107003e140b400d00d0b5650000c000c1c90303010b951504c0040088021801d070384607110b00c98904540010340030b4039107491442e00540f0410544001c1d10184081404a10013040c00f0841901800042d08c490140c0701c005c2000350065080200500c000540d5030881c0e2599844074006c0c080e525000000c0090680462410071010f08406020a0348040c54060724401c1501c451840035006000c268a240a445550340102d000d42020501c607900300308003060000f91075401990307031003d40b132254040e2030025855809204070050070700401340c141c40c1040c001c0381210314030661280c21010149003041507161100040360555550580072001a80148200302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 297831870 1250 297830620 297830623
    0x131205010f0203160309050c04060902030901051021030c0b010b0a080c090f0103021602040603050a0c080a02010507020f03160f21030816170a0902130501060f0f090f0806060102 78
    0x20704481c0c000204504504245250680001000c40c0c03110a050b59401d1705002c1c041c080140110040000344140010354541d41100c0c085e4109480d506920341c240310100760101100ca8008081d40d99140c1c04026180c1c001814150104d81400140c0601203001d220038007050000d5185800f030400841e00c1555032203c1c00004102c0c8000030101c25400c8002d0040c900e45a41d801c901030079948003460007507116221151100092054148002c1d40149845c400000300000410f282d18100e00a400f0b40b0302142c2e840342115118200064000d00050f010048440144be041e02d0040113018050112002c41e850603281c40c0c107001c001c2d00001c5001c0b0310000c1c00c2020314000c800d02c00c4103018480605206030760a56025210540203020b00b482002140b5000080303501c102d01c084100780217400d812480b4202069400001c0c4081002603000e0070b01d0b06901c021070b601c5400344a0484403039546590445514403021a2006c1a03c01e0110401c00d0603000007d03820307221980c3d10040e010368405000715042035000079 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 297833120 1250 297831870 297831881
    0x1021611011805041d1e300315040903030b03070807051e0616031205131203050702100219110706090603021308010e0606090c0c060411010513120501 66
    0x80341004500c01200150b00200070000d4100d41d01541c2c0803c0100702e004c032040b007004491032070104030700c2103e818021180c4d9210b180c078912013007082a10040c221242c49950380b840803401c00084504400046200c1c001d514008540c440d41d108110001c07401d40000190a48800c420150002600c0711b142c481070b0301e424400030005150790002000e120b440c180c00302c2c00d400c80070507148103c84c4d20400d0388e10007a00c0d18000c607880c80c4062000d40601201e01e01c2c0240608000c140643e45603860080094000e032690101489695040710030103118040b828800c50144c1401844070b02103000d241c0d050040d20100f40054110b5400710b903c2034003001e00750744d401010740b05980d4045005521800c010070506400035441000e5460614001d40d6854400c8014070030a0001d500c020040c3d840c040403902805408102d2502680b022181c40d4081d849540c5107001c10301400d9aa000c09421a10101d40001d400201818800406041c000d007041000300c080c0c621048160700040d41044017400c0c580400c40d003071054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 297834370 1250 297833120 297833153
    0x30e0a0803181009030b0411040b0a0602010e010f180210031107050307021f120b19030b07110304050a06030218030a0b040b06031903050c070e0a061406120c07060e010216 75
    0x218030304d03520b107444015075418041e202410759210411000f2081d2116049840b1854005e0401101e41ea40d9031340c028020504460528901e5117090780d8280d06101a02600d8440312201d0003241010040ba000c00260b49141d82000b028507540d00c141c0740000741e025001d031482c240a40091038a8500c1030041c050100c445004403502c59800800c040380c402d4106107565034000000c01300060031117950000c00d10903450350420740030103a60030100104102d404000e06201c1c070100c0d503d82110003031205c81d6680d030740100c1c005c40d94003909a603001e1000e94440e40c050490a1400c2d6082e90801e8010700109080c001004000d0300e0350000c0e24204818400c0400c000c40d0060400d800070004a4149210300031460b0104d10001c1c100b04d000241e550001c441000324001400043c041640c140c1004143d000c01804030b0302c60201d140719241c84a104a1500505568040e6400340560855070350315246030700075510440d401c42d61540d41d07418400300b101091000c4c11b070f8000c0c0e458031140749911505081324904801e030b08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 297835620 1250 297834370 297834377
    0x51e01142109010e15091501180e0309060f0304030807080903030c1605070f0510020a0519051207030903030e040219031503140a0311070b0304030e0a08031810 70
    0x90552034000c14403039010801e810701c544058a0b440c9046002d8800c40819050510884448903440310f070940c10240264000400c8a202925440070861010030901c500c000035003190600307148241298000201c401c5440c815603152109010009030701340c01043d480c80050001208201c101600003110607048402802c005549191000d200c50341c9105c01041181d941d8400b14038402c05e401a04d40568440ba40001a01c503081d45174407040f9220030203880b0b840d02c244075040c0e91801c0c02d4008200946415080409000500403c000c14405018001d5003120706204e641c0743c54200c141030b5005040744074031075540e030304000b469810014140f1460110261280303104100814403550807181c04040038085080110b14401034800241d030007881507101900340c0b2038403040094038040c08518000c02c140b01c3d03240d81d00140610506155150581d0103081d60380d580c01c00101c0d021a014610508a62134010504009651603641c2c2ca415078010b02d004114a00c00e180b01220b031303403528858068400e8410315 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 297836870 1250 297835620 297835627
    0x80a09081c0e09100b07030504170616030b03070e06030a17040915051804030e03070303020c040f020a021b04020f0c0105150303190e0a0302060307050d06080c0a030318051e0114 78
    0x21409101c04d07089200b1540c50100005002c0308141c019000e54004103014800d0220000e5044201500c40b44125002c1c0b03101d00384403908a00c070324000e00c22440c0000c400380003090a5410002c00021540c00a0005541071154803204070014880400e105401e450741d900041d241c0b46000000ca0550b260f034902c0b04d400f81c1e8006018011611002004a1281c800701590500358881c1e0a0581f0301190180030203805014940c0044103158000a00c050040810b550030844041000c50000c101c1c01092041c40060700120680c0d03821442044d260700340140000d00061030120f40303407841922540a44a00d0f200342c0d448004018915090300c1c483e0b0140350003600a540303814040600040e9185c498027002c414403541c0d2420740c4640d122102e80c1006168003a1215039a8100002c010302641c1011030025400fa040200c0824242c0c00401e03254007000014144038803040c02d60b5400c0d0344003400740300e407494000d03420000060741da0358104200d000c400744943e01c1140b01c003c02000505481042a55592144042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 297838120 1250 297836870 297836881
    0x50f0c01080403050a0f03110c07031a090a0312140412021606021f0b030105010b121005010e090a02071b1d16110703050a1a060405040f080a09081c0e09 67
    0x4aa03580300f4030340742220045c00c03501401c0e40104840300748c3c0d0303200d5400807400059505001414806590083c1905403010300c1d02c03c490171009204031603000303042d00000701e00300c0000d00441e0fa90350003ea01f9440804c598000c007840d00d02400e81158180e030300300514030700d071000250180a8a500b0a04203407800702242d0a110010795610110520400350f00c8031918000e00700b801542c04000c420000900900a07075950795204a40c035002209501c190f00046400300355802c00329210b04044500c181c440c82d04a02c000c100f0006211001800800d6140e0208214000500c80c2c011040d20a0308901034180340c03906000c12007104440c403907690b158052000381400007840340700c00d020348000c00c6890012503000410b411710341020104da100500340e125444040041252031203880d544080140150503965403068100403d440003580c020b025400750040101c0800c01c654000c20b008403142c18080c803482e40c0c0790000361030b008109400407220b080b164900b4600e194003201e10f565549044818103031a0030039 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 297839370 1250 297838120 297838127
    0x60509010e01140904020309010c0f0c050a08160605040f1424040201050c151e191104080a060e150103081c0609020a020c0f30030412050f0c01080403 66
    0x2001c100d8140805021002e40b16260502203030261039028000303549900303000302102e01801080d10200301140740000001a602e1007071041c0700741e158001000f00105081e61f295980140d0018040b608003101d070500e418089402405950f01461003107038074804100c0503013022f455255041d80c17140030f1900074074084004800500100c101c08002d500843e40d1645403840140c4080c444c0074241e03038160180c1160b00a202d030035800140d214014021106103029140c03042c020301c03650708440c018258416420005661071095009000041819020500d00340d10760b040c4030305e40b00c03000318101d5000d500d880e03003402086401e0002030382e21a1042d811900a505550b65003849000392710f10a001404607501090f0250080e0b08010001c1400005c00c55460f071030b40390000c1d100e1100c0000c1500911010b000380d03941d42020302c030344a03840413039044090030a0300d202d980224200c0007403083c6d10b581c070040c003002c260786100040800000e8490790040603502c01c3c800070030381065952444581849020000c201c0803980 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 297840620 1250 297839370 297839387
    0x5030a2102120c0d0923060904020702030a0c030308010806010f060c0203100f091401050601020309010f030f0c0509040e1203010b07110301050a0b09010605120406020901110a0606091149090201080106050901 91
    0x1c0882d00c10b81c03603013002300c0418001e018442d80698184107025924040c012180c103003809490013540c03480300903a02c0310320322580e500080c440d00f010904880c00411060b481144404465480103064403203500e00310b1195019520000c01c3d4181c042d59500d50041009011101006501d4024001780200d00e4000c0011752603000e90481181031052076144803204c240310364490258441d641030104140700303602c0300040007504056101401103151600742c07200f20100184030310b808150600b80520390ba0801071031a071117411242040b103c1249800021035942d500303000e43c80c40341b0115000060190414001c2040c0f100701a0b001206028041001c64140c01d05d041d40c0d02e0380282c101c03001682d07480700382c40100c2c5c0543c1e0030b00c1d00070140d0041520400070440c454004d02d04603006c69009020421201c08400c400e481030140c6406448070360004000c00c040c007080340401195003444800d010303a00114030001c1c06d041c0079849156003641c0b034244000315030300710341030a000d40807505c3e0090a1820800c0040d01c00300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 297841726 1106 297840620 297840689
    0xf170106030902101e051b030313120c0302030f18030f010e2a120f1207020102071409131502120a0605030a2102120c0d09 54
    0x10300c10030040c100c0090594107401d07900c001c0d84043e10691f100c0c4503d02c4611030001030f0488030340010320240d44108441205450808002c0c03400c507412020900390101804440145c440205e51b0000982d10b0a070040300640d542c030b04c1305402c840b0b000d400900312607503d403059011118180006401442510034410126405c982034800800754503074024900d0504145601c2842040d450100307074141081c1c150f03505451040c04032003041410001c01002040c4103040c0000d54000f1540e0405c034400c014402a89251615081080000c002100182001210360244020301040c02854a541c0d1040c00e44208110351303a54800204001c007900c1100c4c590305040c90711000042c44d04000c98110042130b800b085050004140c0c050600400030348000c0c0f0303800c500c502c04d66101480c200c9802000051440c900400180003103407001090b007441a00030102001c41c0c205281c172207180d808004803030714 = true := by decide +kernel

theorem cover : BRFrame.Cov 297661870 297841726 := by
  have h0 := BRFrame.cov_init 297661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 297661870 ≤ n) (h2 : n < 297841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
