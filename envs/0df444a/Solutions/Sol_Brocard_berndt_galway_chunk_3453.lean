-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3453
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:30.81984+00:00
-- url     : https://prove2.me/submissions/e76e1b8d-eece-4516-bcba-e9765e8a7bdf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 620863309 ≤ n < 621043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 620864559 1250 620863309 620863343
    0x302010f06060c0f020a080a11040506010c120809011103090f010c0302041508060f0d0c06021513110a0b0a1808010e12070c080303040c14010c1e0501022104 69
    0x4000c0344100d41107551180701e156851348881400c0300394114200e07030111050900051000041c044502e4480c091040c0500c42c079a11424042605e800416260400c20400034000004810862910a041c10b6140c5000c03182d0f1001c0c4504c0c0104003014406017031500200420594250004040a0000d10200280201000d4413401d13401ea00681c0101ca80710074060f172000f08141d214200e12176200c503009103030b0010700f011030001c950500d02039003040d02e02800d075400a00206070108201812200c102411009528283c1c1100c0401e40003460001c01080031004031150a03500c0002440107004805402603aa442480303000d080300004805440030348004801c001030100b8184035000880084101410b201d54140404658640c00044204d0350008888001700f80004100040c2d4800c91007000400c20003820092055441e41d5004013490400403581484030004405401198080d915100224100032541c90b1490280c043c00c88443c0c070198000e1181c480c941c0b00c12421501440c0900e01c500e070103505070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 620865809 1250 620864559 620864561
    0x50f0a080d0c080f070302071106070606051903020603010e091e1b0a0e01030b180d050d0614030c0423091b060705060f07030212150a17060a23070c0302010f 69
    0x1213070942100e0050200184034035009800501c50300c1e104110b20400c00010310005a102e401c444802e540095031100180003a041c02e40c00c070000450901e031241512880c5d82c4c0044e620788414084d18a060030441c01180c400c5804019680d04015031021308075410350040c02a0340d4551540c000508000e14610340b02440c2d0a00c0c0d200d8409540c40a540581140c1c01d548414210301c81c0a00031810103110140302c09100301092003520482c0401d0b60f81c85640302a258004000e5410b10742194107001300903031400c5810368001542c240c06403410f46c0c0108030b04c094002503a0081903125103540d80c00b2100301c04c1000e10400480d0703030584c45009203014070a91010701c003480010301881030014803076032180002c1030a40002d900034a611140510700035142070300740c047c0320f54008015900041e080407108071400701860308401c150060003080d20883c00c5404138a80c0b0707950b5030001604180c2c850f80d8840b224282050740e4803228000b00b420681803056420305802c001c02c881c86441082c2c0040d481c2aa06008405003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 620867059 1250 620865809 620865811
    0x4080136110402090121050405101b03090206040b0708030402210d1107090c02060906090d0509130603140a0302120405010806010e040e0f0d201207050f0a080d0c08 72
    0x200400007280c111406001c002e5011080e0070b41444200e40140003082511b8900a45100c2c0c900c80103d654109441e29600d00a40c50344064400c5080142403580f807100c4100e045c60025075481d0200303443c0c4013400810054411034101d00c812080001d034a00038042050000c5000700c0c0300ba9000381c030614600340c2d03100c40d1121500c0707480207907040141403028071481044130030040400c800c180c484403666814a0411191080c10724409078004008000b20a8414081c180d400700a810145ca401045100000c0c0b6074880c1180c0148030300d0207501241d0b500c402e03e03803148002d158800300c42c4100d51007141c0328a0340c422082c00300310018440c200d11a03140d8465442518210f4406844000d0700741c030380c1e00054514080800c215600140c1d5801c00c5003000c54200481034551409030043d00b506504113400409208070a03c100181020110030882c103520009040c0018000d40702109458050a15107079040c07441c81c00c1d4054192150325951020701c0545002083c1040144004000045e07030841d05841610f8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 620868309 1250 620867059 620867063
    0x909020a140607080a020f06101d010b04090f020910030e06010f080c0603040201120614032e0b150304050709050f0f010905090f070b0901090f180b040204080136 71
    0x10007030002d4400200c03984c028000c0c040d01070058039000c0344442c00c698030300502190344060650031130900700a5000b100b80680300490940c241e403e01513051059000c2c4d0340c8200d205000c0d0340e656a03080e20364030f0032850741698124400205450125600900002d000e410020b0b141c0342d0300e008410001856000c4003031400100c1e1108006416010a0394040080c1604010803d80c14031944000c80d20b010b040f80e00c22403000c0d15030700442c1c0f60740d00540c0302854501402801d03461940a055030825415039082da01d460031010301041d010880d80c80100106a031100c1c1100f010b0181d0201106100800a000c10080c003510305544003040070b50355820100301041c0050701c040c0729149400c0014054030107544c01c840c0e442400c2404031845100c55402c107a2502c2426071002c0404000440d88a505692118003880246084c5c81005192401d205032401d0680c0300111400300140e035800c4036080c0e0349864058400410084008000e9285504100392031440b40464881c5803aa5034a9004100100c0519165180d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 620869559 1250 620868309 620868319
    0x50a0516081f1a040f0906110a0203090f0d020a0605220e27030a120f0b0a1512020c250605160501020904060b0a030b0405040f02011d06040909020a14 66
    0x1500c64060b14001c183c45540b40200052122411980741c45501032031115458031035000420906505104084034102e00700780c110102c08204440a590303002054401401049603011018600040041e49178120440c0003034110030510000501d4035000170103040d910840043c1600f81000300742c8503440c002381d58011000c4000700b1002182c20b2085420b0b44d2101060241c020000e01010821402d02c0c6401100940001403614664002c807600f06008030180c2031000c0d0301c2800911040d0001411011050181160720724100513035211303036882002820300400d01c1c030701c00715903884205482c130f500d40c2d40c1940c1120354602d8601000341e441c0d02119030082252425030320581404884c0c0ca450045e450f444105445640d02070240000381da40300d201d030400500044070026615088110046e0a590f02a44418800c510700b00800020032294103000c0007181c5d0900c0d000040780d007441004070034102d68920080c5c010801040104021015078840802940211549520305136924250713030039007801e241d40756000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 620870809 1250 620869559 620869603
    0x6050403231b0307050a32060d0605121f0f0906020d05010302011101020408072105150105031e12091f050909070302070f02100c050a051608 62
    0x801d403032a00c5200318003444079800100303621040000740741460b02490502c01c00440003040d07416140802c010300040009440c520b40f201d291401e1441284480f0002415480007003d03018007210a090f40145e261200401040c0c540e021518498001c0000d402014080d80d96092020503421000407403202e0b080940342043c801032001856000078244102c5001040c5490351040c0e00041d000303001400590810760b800041c0781d0b04d14000100300a0080f20980e00a910400007030003a0312001c68004299654421010f082c00e05144500d0300e20138003294080c0c4280590721042c80c8407052202c81c64100c0d48220100e030405248880b1030813202c0e00200700f000169102d1807468004c0406803000d0460184001c0c6050380348014120004261100811180300058000601450034030b0226403440e0000001e01d02182040a00c1c0c2e14443d40010b85130300a88220b5483c48800c0c01c0314400c00c2160303a007651042c15076028014a01e4002c1ea16000d04000c0c424099131450b001c260f0400004001030041c0d0000e8a006003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 620872059 1250 620870809 620870813
    0x10504110c0c100203040909081e070f02010e010e04020d0f0c053c0c030306031e06070804050304091a090105100203041505090d05150a0209010e130608010c05040f0f06050403 77
    0x2140f1010601d006600040c8000296034481d032044541c0c65000d01d4a5507926004d126200d2859a00c19190882030035040c0034071004240c1404a118106a0a0904040d054141e500507215007400d554030a50050000400383c240e20039541001000006840b0b00388288040c40c41c0036612801044d0040401e02c5c8140300d03040b0308240c43d250a80c0e41560305117140c2e40b508c60318031100d0000d90041c00403003170380d600000030b0054030304081200c0001000c90070500041600c05103800c0ea1608030160080d4204000100441e040c07160a0084500420090f0810002c3c0c45080111401c2c01d040d401c5218460144800000344030704001d15840d03071051075503011314940346c280600c0e107401c0f0440880b0350040100038000030031039440c0e024600e80c05c6805803000302050000e21009044c151401000701c03e80500501c550045070344c210302d6000540104541c0d0104075040b10108900402c0e107a4040b0031f06600707101480051a800900400517940b0403c80038a51175107a141211035a9482c1c0b08a1000980030401040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 620873309 1250 620872059 620872069
    0x10f020415210e0601030308160503010512070f080c0906120d0f09050306070806030d092303010f020f0c0d0c08030c07110901091509060f0512070902030f010504110c0c 74
    0x81c429042c03060321200c04107401d1030500720b0300c0034440044980c0c041c030300500525402014071584007140c181814282000b40390010014001032040601810300140c05240c40c0030140070400103405000c2c03615004950b2205101d0791500606030590091450001084850034100028107050f54510000c1c200924941000c0b16205002c150350010414116000300b403e644c00d00c1500d015182d50341d1036001c0760400d903007014188129a00d05201317108030300000f042480d440078a4040d0031180d0350100c814911032900440d015001503110801c03024130002d902e6071151841c8000d088a00d190100320740300500748500a4406e1080884050100103040c8006802d030b0507031200522041e803150301003550381010f44021800301142a04110441610740e2000d10214551002d078030018211042e046c000545022070b440c005428074003c5c640581d000405030064808200100d00080c424144210747d04c2c50415003000c9501c40c00c0c01010710450a1051480c18152075001b5240106020006411442140c004000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 620874559 1250 620873309 620873327
    0xb07030b150406051e0f07150c0e0603061203030a0606030e03030f010306020f0904050405010504030806030d121505030a050309010801051005030a0c091806031403120406020306040204120311010f020415 89
    0xc803440d0185c400c5544841d001a024004c0c409222800645400c22442d00c00000c490450207080f0107841c25010031000c1d1f6208480c05000241550007030703a203840e260042030728428141c138946203a210000602200003010380c41141112410340d02045140e10345101e054807440152460703003041c1c0a101c014070102c0e0b4940d00410030000341501d110b2030005000c000c02e05441d0103d80c141ca072070b55100108800d268001034415403200044002d081101c2e0104400f4000707108001450540c9552030441d44508050601010081c0070018201c401204c2c03c0c4c9041d41e0790750312062206000030641e02c0001141c2c108104c81c0e81032001035489050031070796035580c4500105840c2803860204180100c000071884c46440d6001d6119600040100d2030074198100030300e403040c90040810484e841002a41c1d03155081200460b0000e501c180c0243e0ba9480d00d0001902a0140f50071501c041070400c1e041c0740406401510b503d08403c044002030002410b40b030303425005c901841c40f8045006181028280d9402c0c031070046c031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 620875809 1250 620874559 620874577
    0x172407031112010b03070929070c08060906041b0510030c0909110d05090a050c0d0f02030d080a050a0923010908070c06080c090604060c140a0b07030b15040605 70
    0x1a42c02e268103051212030401003030740403500c00715000051142c4079a000d81000082d0150040742c0c1d00074150302c54180d080c0700e42140b8074002e440c004503042c410411503078080e40003000030a044880b141800714046407148003d0782c00700c441c81c3d49405c03807409150f0003000b21801c40394028107051414071641b0042d005482803002010800030504804244a00c1c20721031000c14100d00d810082d201d00419520300300300c3c0d4016003d03046c16482200e528000480020b405226460f003501c42013482d20052a20001707140301000025454000c043d030b03494070380b41c1c031041c41441b464100c8070a201a8440e00c4204046940a9801030540d8440000222108140323000880349040c47c20000218100f10b51030b00b84040d085500210744240b41c02c0740420200341d2051041e40c120802000da40c5c40d0070460760000e480380c4598495801407000240c10380090200c071f50411000e0322014002d944a0744881d151004400340111400c00c04079141400f2641705041c012084040c19295042d2586040e0411209541d41e410a80d41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 620877059 1250 620875809 620875841
    0x708070e0709030b2232010b06030c16050106060302071e0201020a0602033c070921110d11120d140c010b1002010c020c090f16051317240703 62
    0x2c000c001584015600e00780c0f46e0401c0ca86910320364aa0300e10082000010308098040c1e050030355651265840204590300800000b0152303075200c080d21103d1011080102c4007600952a083d00001e1442c2c1540040c1400d521685a14880a002d0020b1084040d10382202a0044c1c0c004c0d82c010300010540d5000710780102c01d2044204901c940c1c4050708580031054815001c008450b0524540948a149a926040401c6003050541c290034821030b11040c1c101180140550313201c150341041030054106540032081c0c0050200c01041070a82001039240c1041c0050340d0140241081a071461f003c08148801649401c0da185000310820700c40b01c2c50300307030410340da80b02d07035556030300700f0103180f0b0341e541382c24451551a80d0004588c4172038158020781003580f06004103005240c4002001922950343e0750302070788520100001202501086011269802225100e002c030441d40440454041c5a07a1240c58100014804480465003140a4204040f000b0080c0a0455198a001c00c600b54003030340068821019580d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 620878309 1250 620877059 620877121
    0xb0601030e0a0c05090705030702210d110c0f0102090105091201060f03031101060503030315010c030c060e0f0c06160228170f0106180902120708070e0709030b 70
    0x80305810540c001c1d80031181c180380c183c0e04000c141040c1d081a60b200700c0710304200d403d41c07400070307000383d02d590002d1448115202c40307492420005c0081000d80e6142c5900c1c1e82c2c00c01181858101417211940300342080c01803845410b2100303e50243c140200c41220790180c0d9540d0400c58440180851020403000058141d500c95101040c9680241e00e494000d60107592080c41040100b5089400c403115a00624000c0d0410003c00544040d0803074103001c40803083ca405228800d040c20212541e051060009000c1803c0070985100705200080c0502080c0c0c0f5a001d55410001c0f200c200440e038800c04202c0401d400820010101524040004480490380c042c2c0384012200280140713014207107190070802d0041d68000900309180340800c005580c2c000580000c0110b113040500d10b0303151046914088040c503481d0301a03c001c40d129424020301d048491004c940c4625190921031b0b440b50218007070040e4040c50b2100242219100d60a64800c0380d800940c65150707078035034040c0c01e074aa580b0101c4c80358440c03901107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 620879559 1250 620878309 620878331
    0x9091104090b0412090308030f1e0403021b010302090d06020901110109061a0d020d080d0b0a0e1b03360303090609210f18030a080d0501090c0c0b060103 67
    0x200401501c01d2144558541c249400d00e02244402d10f110140401c21a140a083c8001001070003103d0b0050401c185400440d82c0703050840d1440381c000e2003030f080d140d04104180000c00d900003c060342d1855000120851b1108888011012030041703401d52680606400440700201e59558020320401d10306162102c1030300300614050342902c0404004645e041d5960451803000800c0d6007100400c00003c8400780500c10a0b500007270060302c0c0664015103190000185590300072050703806210100300140400d40019610301c1d401000306c0d400ca07000200d802c0c601c1401440c2c2080c000440b4401e01614441d642950010142c0d45201003402c109070070400401101003020440800c06035100c0d00c0c84900518013860004d9120782003c440140036a080c00c1001200d841c0850002c0030b9582ca00c00c80c1942948a103002c00c10701c0543c01410350280c0c3c1600811072900305201c00c0764018500000c090720140302c0342e641d80724040c04a030351400c0100000740110344484d0000d6101e00b030b03071600940140f5000c19223100d14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 620880809 1250 620879559 620879561
    0x1401091805060708150108061e0f0a03060504050106080a08120601021e0303161407240903020709180b060105032707091b020a080a0c05010c030c12050601020709091104 74
    0xe070340d00c0380482c05903010070030103408500b00804c00b1790003842c1c801d106007004004500a00091041d841c070010b16071050001d241c43d519514140c2000042604031020303502e0401d80000d000035038050f60b96508000340410302590001d1074401041d80030440c5464400301900d030000703c100242045045005034400d00c00c031040121640382c200141e0703502540e981d0801985050300c000000c850401070100661103080c400d9852402e85403c0e1b60403000c1e00f0942c40405012515022540400b92450b501d032481c200103255000850409448900740c0810140800581c03a107400440c5441c000c00e408a008002200c9500c100c01031904003d21003100011503403051100c00c80690f10103640815a880300c2000c01c0350920b140a0410781000c0301170465201031a1601c025101c0b8901080901008000104a202c152007035203900b00c40c0750010000c01091402000040140020000c1400024080e00241070075189510625008410580080030f84520341204400648440030058646c19500300c61121075880c0c2d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 620882059 1250 620880809 620880811
    0x40f0f0512070c06030c2a05030c06040609030906020c060318010b0312250507030b061c1118100501030507051e04061103130306090807050d020604030201050901140109180506 77
    0x400c00101c000f042c20050000e00f100c501003410003c000000604030707100800c0604040100d007200c910304400c1c0701076080031f03840c510a840e1000664400e13402044184040d40e40140c00452003176907107403803141c1da40f45d04a80da400702203200e0358480401c001040c801c604100c0340341d0452200030b00109074945214000b07400c00b990020f90003032010001403141040b098000c000365040d01d602c882041c0d00c4080b520350301e03138503011404024400c01e4030802141460f035942004041c240f0041011046805440c03600b02d58494001545900800213a070b01d420140645072400c0d481a190450308a07005480c003401140038090182c01d00003401001c00c03950100c2840040e516030300410054500e544e491030003900500c154902c01800d440c64100b404810200700340381e41004e0490343c02580204401c0040d01740072440b4402e22200410504c00c81a8480c9102d40106000c1d100342e0107a0020082c03582e404021718243c42090280d000301500100050043e034034280e00104061105081e842c01007051a6078071494010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 620883309 1250 620882059 620882063
    0x1c0821010b031e061f2a030203040306020a05130f050a060f02100504110301020a1d0a03080a2604110f060301050f13022b0b0103020909010e060409200414040f0f051207 74
    0x1b540740700701c0101c406001842c1c104419a403074400e240075800e4170001e441e80030f2800006e19103600003801020052142042c0c9811031021090b10425960722a10403100307030510b20501e80a80d0001100041480c000e01501040000b160081d04407103905e05122802000002c00c01c40300c00b00c1c4850781400c242c409101511844d12340c1d40b41c1d2500507298032050186244c401104601c10f4203000c0017400060800400d07280c2140f01c030f0a090340c0300a210244603031512403184005202c00c001c80308103c02d010b0051030007001d2520954504d109800c80006210581c84240a0190400e05105402c0709030f0a105100c600610003182d40141001c00c0c0e071035125001242500c01318214020280441c21180581c800c490815009090451411805401184002c44140308052400050100180e05904e9503001000100e81c0401c4540e000c0c202c9903402102c00d082c0c510b155010f5880c00242241c040081e100850013a908041d400d0a001820394840180806281044030103006050584072842081c90180080e68 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 620884559 1250 620883309 620883317
    0xc050f1c06061a130f0305120a02030412080403121d0f04020702060705071503140115020a0b0405070f05031b10180303230a09051c0821010b031e061f 66
    0x40d50031500d100c0c4c9000a03401860390250074032000c100240000810501044071419016250701f8480d001f623046021b41e510541042c100000c440c010400745c8030042098a210744128030300c40d803041c80d00b02c1303840d014900c1e411220300100c0c0d030810040c0740c0a980c0303ca4402e00108054604002a404130307100e030b080918101ca82d54042003050018041321a080e803109940c51034100301d5414500c4501840c1070045c851080c0c00045a501c400c1400d1091160b591026000140c03801c1e10f003020319265690344038070b02c502c00104d10360740c101156a01d0049449038009d07140c0702203c401401043e04102151017086c2d08071091140b8007200c4200c400e05009880000d502030b4803928141c0500d0306c03031000c45039035940e90301030400300800480c0c400710740142107002998000d681d410004140100013001c3c518000340e02804804022130400b441d040c00d203580840700c41030138141d40b04690380e0708a90107407800143c0350b42c2080c1c0742c4c031600c204000d604980803d6000800507e0110f00d0072810050b01e0b800c10400403421b0000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 620885809 1250 620884559 620884567
    0x12230402030d02061302040b0604081606020601090c050315060c0601031401180b0f0c1c06030c05010504060522050901030303020306031614040f020d05070504030c050f1c06061a 78
    0xd0701d4180b00451034040caa00140c41c480c540108182e40c0003100d2007009116940d00d04900c3c0954031a80141d03005056002c0c210358904040000b82d01040c10b81d442118018400c80c8000b00d07140a55008141081001d42c450500b1030715241c1405494450801c0841d130804028010a0741c20780041004600950281500310390f1582242a8942559440a0500f03102c03a28132101e0000690070707000680c0d10010500800086460b10078125502d031184080042c0d5291300c0407008800500c4560014040b6440f5030300303040c0031540d2030f001514180124480c11000c01c1040c440c00340c2d5240840d8034200d20303a0380c100142078071548403000512142c1b000e0304142c0000c0e6000c020001d030350030b00304140701407081c2e15000641d46e42e203040f4580c03072444401c4441c01d0007552601407860a21740c0c0c0d80c05480541c02d0118081c002454007000c020020740180c170040c0d64011002c82d0018150402b104075441c10740c4060310490a541c5822401f20059181710360807100156100c10000350700d01c1c42c01c1c0400003d000d2600184d56 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 620887059 1250 620885809 620885813
    0x90a080f04150503100e04051218010806030607050f070c050303030c0a0e04090b13110d0503070309060e01020c040216050703150e060c03070f02070b1219020c0706122304 75
    0xc0d0000c1038a02c4040c08400c000f0701c0000441500c4020445603d00040c81c116a9a40740c078606000b1100d900000d450340200d11481d44025508441c024250280e03540301c000c7c0c2d01c0b2010150b03511415140080031450802080303042d400007000405005000d24004c2001070342e1200030a240d0341c81103904108440303004c00d520fa8010382c40900446200030444007441000a240c0340d00311181c4028005810186528060a003001408a10b0610400d0001c109000070150303810719941740d6100180880c0041d03d8001c011500c00d01880c0600854441a401444030303901c0c003414030000b0751000c1141e041c50f041190140c2c001a4040000c50059882010208445207500601c041580d5881152010030b40014080051003600d0f4000c0e81d134030000d1441c1c0004448951007041c4c3c1400a235400106003e500001c68a00f2030000044243c001d502d00f0a0450b188500e000c5d10358101c2c043c4010400d00c54200c82c0d010464a441201c44844001c489100024100d0380c0e200c101600500d20099509101c81c02010442 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 620888309 1250 620887059 620887079
    0x21070c0c030c3308070e120a061401031e14011503060c050f22050d060c020c04060b0d0e0f0109030c150501030c09050705040b16020301062903090a080f04 68
    0x4005508880c4002401e841003c07121070042e0400019400c2009410000f0319442c030074007210f00000009032080985002039036145880d00c40110f000e8990a080c07013a00e8110942100003c5d0403a80c00c1040342d2006015030340684403295000b481a84c8507001602e00340f214900a20a00c03400b8035845009800851a40c41c0400c283e079140d0032a0424400c0911504030803440c10012113500c0060624042e440d4100c803080110884a507800468102080b1145001085a07582c0004c20001440c2c0032960401503d04c10030056500d540500c00340e10f071003449801c540092030340000005220b42d4003500d4a2900e0801210301f16521950260002401e038000c2e038051207500d2180520000700c0c000c0070b20a541c15600c80c1c0104400c50b109100c41a40e03034030001405144118113640142c8a080801940c41d40e0691032111440c401e0107003603100754a00003000410180c510010843c20320200a0184c3d511811112809603401c000c100c92118001c4448110008034024001d003013400e5514a00c03a143c82c10302a1240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 620889559 1250 620888309 620888339
    0x30f09140a0c05010908030d09080c1641041419060e2e18060314150703090c05030d1e0323091005040c081221070c0c030c 54
    0x203041c002a05e0b418404100c021084410f000d0074454045040c5e1014a0800114860083c1498190050f0300001e21181d200d41210740486188039031030072240c024242040402d4550403903261220810741001c04000040d0f00e40e04da0450b4000780f00240901e0031b11220042d00c00c04503800c040011400307000400c0c841c02071050101070304510011401d00d01c1c0040c00c090500c0b00081003107102c0e061180c0100c1012410407200b6002e400800781510701c0242020310000039007503500085824110580000900c418001000c003509007587e60b0092668a40b02d60950042c03e4620050702d042041b00d40204e20360301d0801900c221034035503582d10280e424111810480701c45441000000f018240300d01c051808520f044e05905803a81250ba47c8076684481d11003e142212410007940380b5410002000240100301c100700c0e00b182e002e1026155856041180d2821510a0994203000c000080c06a0440d03248206070050340499582008001784025886210795004e00c8c1d8011542c1c4d10b0310042c14042c0560504c440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 620890809 1250 620889559 620889569
    0x4020705060705031e010e041e0503041e0b0702010206041112060c1315050423130f0606030b1810030515100b07020916090f080c040b0a1203030f09140a0c 68
    0x2170103007541000d55410a02501500103050850035100c041180d020030500703134021640c04000c0726502c039951703c0348210342c081e02c1c0280c0742d61102454000401000d040210340c5010b5050b030203054550740b29902c0c0003c0325540300a07103402489100c25505441e10401031540621a5000c68680703d141400c3c88002c0240c0b140c1004e41d003003428900480d041504181a00d06540c9180034001d440350411490380e121080d034801d0607620070680c0d103009041c0850740d400f0282d1814111014020940c0300e1509505407280c050399503400000c0382c401260100e9292a072039030030001004407100c83c107036030341c031114039000c2c241d0410940e42d1000c6092040001c0d00801c000000d110a040c16410455150000390300340000a1417a090701c00500c4181601c144180741e08409442500b0f0030340300c1c0d162681c0003165602c041c825202d0050380f42003004125480e200381840c0c100d130001c8081c030390741060710f650403000b030006401c1c81000f080d19200c10500180810881041d08107006000b0401c0400300d05048804014541c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 620892059 1250 620890809 620890861
    0x37050601030b0c090931030c03020106081f0e0703080a0513090c0509010f0e030d050705060a1a13090f120e040b030c120708010c0806030607030e0703110402070506070503 75
    0x990402c5d44032000d20642c040c5012040f4410f0702e198080c6010105038200d8a0b0750a221404041820550859043c0144074001e43c000c010740d07070f1105015591021003004244a500a0107100c200428458219526800d041019140056620365608240c0d8000d4400100450000b055a070074024420354000d004003100c600510154020340c4000d041c03841540e80d4141000500e8003100c03a41d5002d11150b0307100d56409401c891004506200042441d040410200c880b40205070200f43d80c0800d9000307845c1980b540c00001d00100ca8140d04201420211000600265444900007404203031041c00c036003903ca00408443c50960002d0000802c6c051130011150701c250300d865090072958130009554403100b0025229007414450b11444d440c900507855201101d03a60038007013215144c90b440000107000b5103040d030403540d00d6103034002c0c00d1703050307600c45403032500716a01504080002c559a100440302080300500b0061034041e50340c803520f0038060210b07004004940000140520420f4540d4584c000000e4038113 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 620893309 1250 620892059 620892067
    0xf07171c0b09011a070b07051305040501050f0d14061617100308030c0706020f040501030e07081c0c2108072a060b090103030e0307060f0237050601030b0c 68
    0x140b8410010701807154803d400006011500b1103441c1241d983c90341210003000036181c0034000500c1d9034001c0381460755240e818500041d090820380140d6040c1c560050140074611601014042504000801520321b48810a404981401d090040304d0040f040038519400e48240510080c048090010b80c0001001e4181308209240b0301452044040e2075100c0c5074142e583c0c5034103018281d5030062803c0500180d01c001100c2002c100500014800c4550a80f418082e100d4076100740d0b40c98040520030b0741480d4129150100102080c1c049400500c0154105030301e140055441e025500c410322951403408515111440041a401245140d07000c95a4030340118405100403500d40a481c890f040005050b0350703201c04404100c1503401240007808060408916980e50b420010840341200540500a0288d044085251881005800700601c00e44c7c0040901028419444421030409a900400348107410100c4030300c1044c44108248480c081c50080c0241e5043d800c080d42140d40180501c0d6641c14104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 620894559 1250 620893309 620893331
    0x917030301031b080d14040f0f08060f1612061802120f060d0305070609081911011104050f0f04050a0c020709090b070c0305130303050c1902150f07171c 67
    0xd4000300d07440d0b4510380107078450002d2003646d8290040b50080441c0b2240b0050110f10300e54412444d1003260884000c0b00c0300740d00ca403003500384c4801c3c0070b81da0400348101c285030b004c0c05c1e54001c0d0710044000340e1980e00002c040d540c6141d1420302c5000c0c030346074440340c2d5000600da0000040a01c8015040309070700c15510034505110300040d413210b0a40341c00400348900810800c1c01e200941d07011014064120240704c0d0b4035a0741182080315966541d02102c08a506585109642d600501c101456090201e607600d19040c100f50400c01410f445103100d6034402c10540300d403e6980c486e405010300071b01c520720000c200116444d002a04148030b0350450384540f03190110035000725150840a42c2c2204590916030780044c210f04040741d80380701300303004801c2c90500302d14000201070380075004254442283e01640d2081c40003035850300c1590001c00c0080e501240718240101030700014401400602017101e50a80f42098503550040c142c0d034588229410080041210522191030102c1c021004030020000c009103440b072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 620895809 1250 620894559 620894563
    0x4180230070909050d11251a09031c17091912020106120b040332070204050f09060f061309050706140a120908040b13050f03030405060d020a0917030301031b08 70
    0x217507c0140030200601a1441208181c0b0000c0014200521401d4a0034002e0300400d400782d0701c0004664007921410182d211b0000004050464580311a666104c110b010311118204100006e000704080f4002c0210008400c0d4040c1000c01040d88616805101c2880002c0041d08640b0507500004035040103281e1030000801c17030164103501644c18244405d0f80c0c09003000e00c030354131600183c40e036484508a00c6a65100c100500291600c03e208440600c82555544040d0a41c2042038409030010703070006000c210070070400500b080d071102c0098201d900e400303a0300f174454050300d4400c0400d84160b003240717a05005450340030760038040c0300f2400f0390390b5898001100750042203800c20100200e407255a072400a003c000b006c0040f10001e04411001c03e0b00c3c0d01564071304201900c900d200c3d081c4240236000440301c9900f00803007907030704a400c01032690b4140610300c3c141c8000395028044c2081045072220021072a654040d010100d4181e0410055403a9070461030102035501005d010008144001e000c104401140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 620897059 1250 620895809 620895823
    0xc0905100602250b0f03010e0c0f0a0e0102030d11040305010f05040837030f0e190b04020402040801090812070306050a06110a15090204180230070909050d11 69
    0xb0960411520a041c0d03a0f00360703802610798200d501e00c11000280040900e0400b80550f0581c0c1c210b00e62450a41c4402c8160b134083e110310700038a11080e205102c500d100c5406200c8603101810b0600540b46091802c03141361084403036420040416500c04601841840800d21451141c8140709904010b1400c154640c078000e800f0311005810600141c946c0714114215203000d05480c10004061030f00d40002a40d0040c019128a20722046c4941c680740d2001803819000030580c245c0c0c101c5100c100c02141307868503442400741d4001c000380d80040d02000001500942441a04861406a0100c5840700c120f01c0090aa500002d4001800c05040080500040d521a2102801c451440c1400d1204000c040c14a50800d080014007a110101c00745628040b182107801039801c151081f01c08100d400c2e0108118940c0086440c0c010b5041202c40445068082c0200c2c0ca0800f0080c2d600d0f181c00b01014002985881d0103000e4002a50050f1103c0c000e4040040401030203544540508054907203162182049a456203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 620898309 1250 620897059 620897083
    0xe061e011a04030611071e0b0106051e040801050f0a0603230a060504110312070818010c0506041b090e100f0603061107301d09040c0905100602 63
    0x8180e0030100030307030071100100c400031a44403105010742c01032840300f11106c1d00841410ba5130002c1003ca03210100e51a20003c000c0c680d40604c81c1c0c003550342860403c80e0150070000020301626140d24145005c40f85142c0a00002d18010b400882d00d803500c117925001c42034018000d40c110b142084070510000350324002210444198a00740415140062841840c1a00d022000751200c2e05d0842480148149014801500d0340150100c07100d10700b00c2060f4504500c90340c0030103800c004052002050b8111500c1d070b50031b0703800414900480a0003050b210982404001c0d00e04585020484130112104141c181541c40200120a02002000d411440240d2920380140b0344d96281c5550780440080a482030307015002464011302d04200c0b001040320503484560061400307440b000f000c4036a42c0b44050488107280701200c2101010200100c6000041d02c40b141d144503180e101210b40c40d40340c82c494813041340e1541305900075040e1144492518180301c0454dc0c2c082c0400515142d401c80922009400050b07241e01c0d11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 620899559 1250 620898309 620898329
    0x110d0e01080601140313020f010f02033702030331022407060204080606030c100c020307231003052703041706150a0509010303032a030e061e01 63
    0x103590b180040325507451818042007400d03404824449602c440301d400e000001d109950903a10034854000540d92090107122110040e4010041c5040c110320301f0554860a04a40d1281d09622036143c940301724124084143c0001a4408002c00008002c103c0c1c120840455208404c400e9103074075604490400e00a110180c0640c2d42d010807d030110383c01c2002890714900c90000d6680740c0083d840d018001e9881480fa01c1054410300e004a800c2c3e1030081a02c023041b0500401000038480301400954865032503503004c1e81d250241d03000c0000c00c000c010800c9582d00c5200c01010a101c0104002c1040c880c00b00b05441041629090400428034207018070080036864815100f0305501605030f0092130352250b90064a44691800c401071803c82002480354040c04800d406810901180d03006d000c0d0020191190961120070704004201080c080d600044000121107402c8540b486150491504d440302c418904002980c0d030502019008005d001d8583c00000c132440b80c1c851280702d45170412441e01e0600440041c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 620900809 1250 620899559 620899561
    0x605010e150a1e02250b120405100624020a0302030901050904110a0834080c19120e190602090a0305100906230a180f060507110d0e0108 60
    0x14a002d081c001c0300d0000030004046008800c3c0600940380c00c000010161703164500e01710b80c0c0049010505140903541a00c004600b0300881c900e413400c03c550040c01c1660789004042c42110b940740c10340294405000e00340e8941c0304900d00e440740745005240742c16002045400c88005440080d07400301c100c41000800b443c200d03071910301017000640204151f0303500040380301e80020b014580e180c0220301644a20142c5103100c0c94035528a42c82c4141000b8541000c4000c207200d0643c4040318062841c903504030044000030341c100171480c0e21454480c0c41c2d400140c80861a070380c903284d00c403000ba07001e0612103030f8804001d0501420008842d0443c0f000144006040d50b40100304640c041c1c45564419000f0741d00a03044803a5105806801002800c110200b035807480d041c01284c0c00b0111003001c080c035204148180075015540c81c11003190003000700b082c0743c14040c144041c80b500400c404120316000203019220010b1a400c201e40058403044080711701010070f0b0031060303013800000e4210a480407640000c0c01e010040e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 620902059 1250 620900809 620900827
    0x90a0504050c0f07112409130914010b0f030a031713080307270b0714010f060303050c0f070608191107030c1104020913150812030702010605010e15 65
    0x2a4021007108455041000c140b00d070030b001a481840e02c402e01c007500c0200071002c01000d029064420400121b00217841004041000e00b04811401c01e030f036030702003c0002d4480c8641d44900741d5143d240441c4900f070f91544a030569604d08040c401124400440c02070600001170f0380e001d003020365500350725188411504006404100d40e800440c4600b03900403000c80e50b91800010141641821b14003c0034078802024070003461121400c141c0701030300c0710401c01c2401c002103643d640c0010384904c2b9054801d952a242030300c090055130b020704009035110f6180c5070380b2342c0800000140781071a0003c10240c10303480118104800f582046896070031404c0107980c0200070348a80805c2024041c2807088529044000480f03905141c2e0244c0140582407281003556410b00b55031041105901400910b90760000301c0711600807100c140c5e41e0000c42040019a00c4168480c0e45480d80d50505501032140f9a81c050000704011103da8284a8100038045c24240074041000d4003010170840d0044a4494120344400540400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 620903309 1250 620902059 620902081
    0x209030d0c1b060f09050306070519020c03070b0901080c07021f0221040302100206091209030f0706110f03030103030804032d0914060315040b191415090a050405 71
    0x10011102d940100401c9a54040042c911030190141e84002500c1c0f180118103490041a40c038000d02d029584d9a0074403144060b6512010000380f01a41588079011b40050786440c2031207940b004104108096880d20484000502507290090003c4903c1320200200c5005070358203c661180c040c2c2d04a88000c0206006509a01e002217020300c44803034002841e042035410606400030802d4034801d50b442505c040c11054180d94600e401e44c0c1c6a8000c0d04414090303100c07107400002500011380001c00312520030740800303d554245981a0058000103500c08582000e2000400c402d01201032500001c0d0300c1c40d1701d07588000b4619000a00000d080200821451160b609004510b24a03080700e0385214021803040314000d400c020980c030803000c90f01143d440803040c528181c01520303c00d0710407446071001100005e0401c0000d081003000319600004983c0300d800300c05101c0350340002500d841790418910000820811016082400c00c40c01d85000403c107050150700d842081a040b030b5400c0e100401d0507103c10a00d03003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 620904559 1250 620903309 620903333
    0x111030f130905090a14010e0705011107090203090a050f061605210f15030c0a0b0f040e1306140c1602040209060c0604060b011404152a03030605040209030d0c 70
    0x143c2440f00744802403001007413603c1154407400890035440c3e024034001d400d954503000103040942140740200030b0340d40503540403001541080b007a50102e50302c500c0f540701260406d482c0da8200350b20040110040250030091208050a680c00034031162800d81480081015048202d9080140204001c22404040001208500d036858100c0415140c503000d1201c8000c1c0c01c492100c10a02144411030b11410082801c5050703480140106a1071410408129801d42c07080b0714288503100c003000700140c094100103105005400704800f5100380c020341d050807029140640480f08a02920f0010b1120b40d840000c12102700341d80c40c0c080c4d1140034015000182c001e000d103c05558000200217030f004a00d9401107001440349105e18802c0086241c62001154101d455034401030008204001c20702c000349403105100915001d514103145407001050242e4a40003841107400030401d0b03000010002c02d40c05000d0003001d010281c0e0308608010410000030b9961500382d01030018081480d00400a0004084201c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 620905809 1250 620904559 620904569
    0xf01200901051207030c030b24070c0306060e090f1501031506031b180b0d1e051005010306050f070906050d1503081902150f090c090f070e0111030f13 66
    0x1c10154501000080c010781ba000d80c0f4103001078039100b04491036140910f1000d5516941410300ca0501c0e624042100303090348400401e0f102c140e8034200000000c1d40a010f00c00c0038104140503507285092402030035181c1400101000c0013078001c584c040f482c05d40723043d00300350449400140c100d0000b511103288200034461500050180794400c40032a681030341c0228214100c2e804aea041e40590f25403165000c040b200c1c8242080e0b807201034206d486000c10039804c1302841e510400c0f80d22815840f00c507500c40e1711b01aa841c1c0c100800b252954010810300c003042c891181d102c6164200340f0802c1c90280401010003240b4000d002c00c2c040046101228181203038007000036808407414040000703847e810040c4460300300d038003d244002c04001d1100c082e144040380c80a8242c40400581c440c81e00d800c0c100502c1c501005020040d42d1080400048295660030042030080362688142441810301c201e0041200081c005581d050040c580014984080000200e4104103000c1d00303140e4952103100d0310880c0c0300e80b0316400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 620907059 1250 620905809 620905837
    0x1b1b01060602010e1b090106050708120a0911030a0c0603110d0515040b0a031709011b03171f090f0e0d020c01121103070e03010e030c0604050f0120090105 68
    0x1240d1142c05501c81c803030078001101210481c041101e6111000c81da4003440c15082108000108100340c029809001203600c02c0c0034850801c4070b000c0e40303080f294104441007003819481350300c48001d003c1c1100c4448225a000c1d005021202c0158031601c614214903c5018100365854103800b02955402040c4c038850150300c0001c0c011810204051345508190728a075a100750711304103140b280346c60000a48000c803a03210207140d001d030854880d6079440b900700c9400360b03060103a180f0010312032044052191400e180f2a40f6000c00b0900d0110380d40b2041040200294800440c40c12070000113001100540111040840041007400c01c03a0440e0003e800030100c01d046a01c1401d01070405260041030000d10042e013030717a910580027813088400c2c0503502240703141050f0030010000b050341c0c24414103d0035900c031809070001c40d12000d07140c0f8187c80d50f4080b102c075540603041181400704004090016008218424000b480f070502c0f1741c42c0b03da081440704289440e801400041b0414030742d0184040d13502d681c5038071301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 620908309 1250 620907059 620907071
    0x70c0b06190b090a060513031205090904030c11010201020a210b10090305160612020a02121614010506060417070834030b01150c170705151b1b01 64
    0x1407008881d000f801c4528841c00020402158251040085d510700d004030249482001d031840e1946013142d198a0791440c10030408000758122a15403042e01c40c0140d110f542c0b4000010124240910341e101c0310300c1c3c1141164010054180800c0d40070040103241100c2d44404d0551281c010564401400c046802680080c644941c01e0115904488800101c0e0f004805954410a40107000050513039103001d1400803c510310110528001254080c01d440d8500740102c0c1c8003460800d04064041e001207110034400c101440d10300003004102c03540f64a1503e941c01c000d0100d03061500c0003075564000e9015034644103590324080e08600b001000110000c20b005030980d442a0041c00680000700d400540c3c031082581c07221007109099455039503c0d03040702c0c1c000281c100940d08181000f040030144043d4042003020307884103000072404540c0c0200702502c01c2280f0355a102628074215017088240c003140d40c641e16690082040500750403042201103400c1c8803115948040b510007000204640b01303800e20310303503103041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 620909559 1250 620908309 620908319
    0x220c0201140f0903120c090a081b040203011404050606070b090d0e03030715051b0f031f030506070c021810081006030809060c01020702130c080a05070c0b0619 70
    0x9070200c1c0d0707110704000a11545940320806900c52002c2501d20f84141d0303000304018801d800c0200c4980ba004922560074515000c10f01c00010140091034200340055000300c4000d03003240ca00400128100c00080d2802c1d070035580f5011890000d07011074081c040c0104c5e02c4000194050355404201c4000072781c480403036003032828145407055035020000e844602081c1c410080320120314001080d2582260b001d12103405100124041001812004d09079400300c588100c03650f101c1448400260121150146d4003544034035044040c9a40e400c0582205d1004c01c5001105201094010600702d030700c02200d08044000703406d0351000c07494128026443c8a8000c0c2c0240521074107000300e09170101241c1c1240100c0d03c9078601649120708032299480010300e6074400700043e03a154108800a031044000c050001810a40242c000c0b8124003480a804040c00d035803803c0d00e500d82d40d0080380b9507400044113103040240c0e1400180c05085900c2000004e450702e200341d0009001c03503803401102c40f01d0b080c540d11211884e80d030351 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 620910809 1250 620909559 620909561
    0xa051005070b0f0609150a050a06033c020c030f0304060506090a0219030b0f040903090e0a150302010c230a0204110a1403130b0c030414011a220c0201 66
    0x161001c544040b03403440400d140c9124504510700901c00207003400c50a40b9405d03082052606850346140e04410201000101a0384c0e10f01298001c001d01e031004100303c80c0c0e66142d003003088400c0307040c10401403e00d200500f034903414400401502c0850180180c1d0342c007244514031710711700424003188080c0d6400420042013040c240c02850003a841a11b0303000040c0c8031204505e0903401850001d0203000c0c8080900303010181b10390040305002ea000b501c0c0300f9007111003e0109045c0e91698000341c002c00d0031410b04001080c03005131129480304496204122014181c3c03406901d01701c1c5440080e0410601008510500c11010b0880b214654030320005089140c0003c05242c9501007030f4020380c4164605804004885e1a031001c44042240550311950036815001024095400103056070b82030400e00b6001000082d401c01e03030280540c00700103d15403649003515040220401d1004418150303410401d105200200442140380303200000c0b182000c81201c20003600146403201600802c1207400c0030a5101e140e501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 620912059 1250 620910809 620910817
    0x4060521010306290127050303030406020712020312011401210c14030c090d0327030c0501170a0506032103070305180307021507060c110609010c0c0f020a051005 71
    0x24192103034a0b40e8041244e0781e040c142064186002c6070300c03040701c001d0b1000039441c00c0042c0d000b000a12071000c0c0c1c07244042481c2d90421241103031240c2d8006241030a118120b035010900381240c1c4020740c6001890700c640810104184601e80003558070707075103080003030380039007519400c040c3c005040c09032181540e8041e4000c0c0c1280d0740c1030008900c25020b50010b005258003228410306103c1280c5280130240b2043c880d040710070301010380c100100450100c000c44500340c44907005000c03500c400400b1a04504283c107800c48158019410b020001c0c1c003400345030354a0001194401d410440c001100d69803640800d0401a02d09001c10880c1e080280030a2003000e01c101450003541227a074108840e82c0c400d1407580785004804901d01c0142d0081c480f1000514080c44440e421450710402c8234186142d0f5500c0d40181c8031904c8046022a812100040c1000c0082201d03e6011517001d009004c2109025030283c0a035442d0440540107002c456811000e549546061302c00909010304040c10088a01c1c40040203500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 620913309 1250 620912059 620912081
    0x30c010906060b07030912032003030a050c1206010c080405100306090b01090305030706020f04030204050108060402010e030d0c020114220311011e08040c090203010603090b0609040804060521010306 87
    0x450070780701141040c2070740300f40d844085d03141d02c81c0d422040c184006020081c07006030381102080441100300d400c1aa80c01049001003890350015500c03402c060540d2016103030000d00000e5519014050b60b076042c840c030b035580c54101200f82007840c410841802c1020f0300740318940020340c008010000c5401001e038154464000c450141c0010004034108200440307840c1002d02c0041c0c0142d2040c800b10022031240e070300034110485041e0300686819900c0d40454141c4100340d10040d42d541090040100f956040f1440f9001040d0484c05400000c0e11004050305400c500f400180c1000100001a041c20b1b131464200c0d40c54001c40d00c4402c031038810000c072127029245079000859210700d80c9100000203500030050500020701c5400b4900000c07440003011220a20014401d0350028030740940090600514801140600030320385d0082036203452400d0540c445440941007a000c0c3d683c410030000401c0c03141d4181c505540382480d1032981c036010044d03c42601011a00c1100601e414600000204140c83d4003244c00c5003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 620914559 1250 620913309 620913311
    0x14011506020f0a080406200d03050a1a061e07060216050f0303091005072c15090303030c0703111c12021303060b0406080a0f020306090604030e06070f0203030c010906 73
    0x181c0e0030000251103c6950308010110710050005101440c0180b400380100715507101c03032079940303105060f0503441c0c17800c0114000d02007599075082c0302d5092014001d42c0101d40300542c16003000651440031580e94412424100c1400816007030429402c000c40040704c40c0d59800c4641952030b990000c1c404025003410880c00c8036903110fa803110100d07120b404030a607482013804001500458400f0000000500340082171102045441400c10010b4035905040e47c10618000380003010003200324052054400c42c0030711000d0312810078000310b800c03541e000003100e900c0034840c900d2685403c00d0b440d0030358466003001e4075036046014000c580c804001c00408815018070480c0e5607120f000c07180b50f062008a11680e480c00c480003080820501c085449034010140c0d0b4400076000080c160b039101030850030001890011108151190a00d50551030208030361900403810102800560904e55400350058000c2c1280f24040d0b080481c0350824012441007150792150003400b0f490342c4101c4010b22500914040500721801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 620915809 1250 620914559 620914573
    0xe0a0b010c03081501050403050604050c0109081b0f010309080708090102100501053003040f080d0e01051c02090604030506190b01020c121612121b0f1401150602 71
    0x10350300c2501c19034980d54140e107405519403100302c8079849200c0007004072414000104400000aa01003041c0c41c803680c02107000d040060003403000103052500300c0c2d100110540c018034002d030950103120841c11050302c040310902150204080141e0180800407030140c0496000300d080d10900c5040d100904903032009a00399160109a5101c460455100b1b02404e40c0005201c07070401302031655018030210b9406017400c3c0d142084244451285160b002d9004001045030055040000b40380400c0046804030007401d02000c000900340008005028001008204080003004c444680c6500d45c1215072080c0042c06803940c554480c20903c1c0d4801042d580c6103400e10140c0f00b40c440e0902c0922803011040c10503405803021001100c02c00580c040e04954400c0503010b0a034190004003443e0590100604e00080c10403e0702c03409081550705900c00341481c500380a03821007280000c0820b03084401305182d020f0404840d042d01030814801c500c1c500521803902e5031a10710040070f4001400da4100444a003a400c55483c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 620917059 1250 620915809 620915831
    0x120e0c040e03181f030509011104080a0b0c0322060b0301020f220308031506090a080703031e0c0f050a0b07030f1104080d050a0c05150f22080a0e0a0e0a 67
    0x2c038403008482000a820184c0340ca64805220381c1106410458200001c10442404801d03800180d00c01d60242095600c990030340d40c100b0540250103584104139210340c034118a4176640500e03000c4078040e4004d8280d0854070440f0100512a03001c2c42010030046c008548842050002040f20b0740502d4008a030079440d460741d0886459140c2d00c0c0c10540c2c0c2e00241e00d6046481703a080d111444450317a2015a4010020f00c481021500c0b0680d06038004d000d01e00050400350f285040240c218009802051190700c850700c0025100e54002c4c1220241a42c400c14080c00780e204e90501e01e041c607100720401054003480c1806d01c00401c2c0c0c10341202c1090b8946800c1000880d641d00e8159002e0b104034862050590083c000403d02680100041d0000407036a0920342004403083d5030382070801060104a10b0508003580c1800744d20740c030400d4001d601800e03901401c1a414140780d044d8005908540000b01607d5002900c1d070b608510600001c3c4da0324201404080400d40c40d0701c1011a180c40032a00701c01d0036490240c500403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 620918309 1250 620917059 620917069
    0x40507061e0c150605060d2004080d0e27060a060c050c120f0a080705070603060506031906120302010e0609060f150f0d060c021b01120e0c040e0318 65
    0x306516554590040c8100b00755951010f0204407204146a9a55001c000a0036101d10700149143e18500300000351100c0b2606191019404011a81071490000c0c0020302a4481c005000c050859490500004401d0076200040da541c1d0020303040f40b000307445280d043c40c41021904000c2d004500c1200c8090a554541d407003201c40c8128050007404a81c44000391000e035082c14005100c484482ca002d944220400140c031030b26200480754201d4018900080a105000701448644090450ba1a080c488980b410001a03443c0c00003070000442c3da04403148640c100c0955500940003090100030041e4912200d0034041c0c02000c01c009004203500444001130032050002c511036201d50081c0e03441d80380a0f21040e00800790840b4800d800d5070401c40000104406580c0c8005030310303501c0e1241501064000e08488021308100d01032044840380b03041e180405c18940c3c1c1280803038110040354100006c10408460043e441c160700f1110b89500070b40351030607059042c0d8004c0f00600628203d038290390381002c0c015041c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 620919559 1250 620918309 620918357
    0x306091104050c0d0b0a05030114040b0f06061207030f1a0a09020306032512140f0c09060d020a0e011e080d02030a0c11120c03100e0a030c1a04050706 66
    0x3e26620400c0001c40240c644aa00c941c0c031441c00580952401d0391603901103402c444900124101a0700c1c400200820011042000f0303a00003e025000c601d036040034000b18116020310720168501180328000503281a100c1d9000301c0081c042c10801380708108a0100070340c2c544c00507117901c40c080e080700e84003c12034070f9050084078028070019004044451151600c1481800c4100940c0c844180910000407a4004221402340d0280107200f28005000200c84580c90084400808025a080900c0c3d4219942e20603240d5640014140c40381850318103180300142c0010815080f046076601e03141c00118102c101402c10000c1c1c014491000384803641c94091050f52444c1c039820f0040107900800c000d403c107620820046012034410501540301d98214000a244a800780080441075404118901098501000001c0202200315020801c00c40e0721900309440e07088441d0054144401c590744102041142c0000e09880b490603804030005080510302283ca802e298885da400141d030b02c8504040802442c207210b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 620920809 1250 620919559 620919571
    0x3051201140f0102070510140432090412050306040f02030c0702010e1c020d240f0507050a12020a0207052e0503280b19030c0b16080919030609110405 66
    0x100c11101f4007140407500c81d5660304040c209404248400244284c0d103442e25050307000c408000018110401381c100b0600100c890050b80704004120070721020401c5000740850500241c5402a52a550400454068031508102e4a101440041044480e185510281c56000e100b60385002181182c141000042c9101c001140c0c94203200410700b42c01031402803408041c180c0b00700d1400d01c0c0689503107410005031007003070070f829841034440c10b850a001e01c4600c1910340c4129541442401c0c041524401070654100e1460f100c03405500185003a00d450081180000820b0002e0101004841c95003042c15410000002003d43c0e86085c82c99005007402081501e00c039402481c9490040344060350000491501d540c05400d9950b650713403c403001e07a00c1d040400032959520017080d40c1064658900039203008185c1d4810034844100303102071844209210622000181c0040b0b00d1500c0f031040800055071405040104090043d03411000410011b0581001c0303510340c0102c8140c2c0d08101080140415103078101c5903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 620922059 1250 620920809 620920819
    0x180b24090a0c030906140f09030c0d030b030a0c1d0105030a0b0708150303031e100510123b0c010807111e070f090b06030705030403051201140f01020705 67
    0x80460445902c03030040c828051074045400c80301901c4201c100c2d0030036484101c1911289007044803070301554480c1500308000000070340c40c00c10b40b8000b0304d440c1d06010900c5020182c9a024411880c0c0d01000084602c58118083c100c0d0240c0d215208201c103e44041d81030512010b0900009043c50080381307048846800c4064121039039102c003800c440d2208010125106265040c0d009101da0301c0400155103d5040003040c44036a2445540200181400400d50701443c01802e0042c0203648607020082041c0f0054103245100030654814034020308543c0b0105005815100702041c17004a00c100a022540b29442c00d03000301c9600c110308140c403800140c48041c0420083c00c081800b140c07080300080701d03550169056034001c02844090701c1c4030340c002c4440b0300b20a9010b40c81c00d1100038801842e1200620300c4c100b0800414090360082010b0b400020801d006000022001405043c010401c6488185610703215000c03641e110389041e40c00340d040034543c601503181711000041c40d50000984030266980142 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 620923309 1250 620922059 620922061
    0x30201021203060d140c120a15091707050313050f0d080f0c060a06051c030807080709090f090302010f090804050f120709050103021507030e1003180b2409 68
    0x1c1c0c145100c0c0d10141086800a40040030360000c181000641c0100c1e5080c0301c040c100842411b020840d0601c408100c030030f6141c11003d005000500c0410b1011002100c0800200f540042811300c00c0c8907001e51096600c001c0000950340702042800300091182542d0110113031000da403101c1c1400032842480170100d410901c00c407074440c0410610409440c00868a00c13240345000f00420031541400004d46554942d60b40b6141c0c10f110610b4441e03400200900085e011a020400c01e4400524441000d4045010301520001240c1060310401c0441d002d42001007007803080c1c51120100c00300a004000c401d50046d4600300c4c107070418103034901640e03034440e0300007200c5414181403004100f0615a10f8150940c84010110039010704e500c140501401004000b100241070740c03560040c400070401d42c0a0301040081c08102c1da0b00000e0b0041c0ca110721414095070000740c1c07092280d1060340201400f820211400d140481d03442c0800107403412042c400c0e45418030aa0030b10700c1c4c144407a81d0f501800e082c96540103074004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 620924559 1250 620923309 620923333
    0x140c0d090809040c080402040b0303071a0411060318060c04061d061b15150d140a05010615031b02070b130905010303030c110d02060601051c050a020301031b03020102 73
    0x240003000c58074052207480e4542580000000c0c00c50340e648519a000c20b00398000c00c000d525084c070031006040c01c240c02540c64078201d60f644249088080c00100302c0000000081000d00c0800304451b802c00300045d000c190349091010711110b0344031440104000da44288400540484000801d840440d007050311109000c0c0c0d451170107114000512200c0c90381000c3d05101c05081388818002c40c0c0041c010000107080e14601c481070b00703104d08800a01102004007000700340c807504d80f2003501c04404c0c180c02c413031a11503030340750f20003040d0800f90525805040380d802c0010103d00600c0820403000c2c3c801d0386880400605c18810840e83c1079041e02c1c840c1c00c0158121107010025620800c004100d0b0700d80c05418207001c991110074074000c0750401e80003a00002e507658074007501d6582007000d5400340f1640f07400405801d403034824000c0d42c40700014121810060085400b41c640e00032007042c0548002410003c1c007a80c40d042d401c2c0b0000b0f400904c420307525010103981010007002891160803d0329010782c0502242074200e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 620925809 1250 620924559 620924561
    0x3010b090316030b06060f1e07031b0b04020d02010c140d110f1e0703060204080106060905040b03060117150a0507090614030601030213050d03090608090304050a180b1f0201140c0d 79
    0x7c0e41c0d44082003082120740006649410f2014904052000060300d0340c0640c20020b21080d0030030b001c0c21000614451542c040f5040712100c0e54003d5041741d40c0f808443c03070352004a42842c2c480000502d22501c10302c040580e200042440010aa51966400071019944a03511341c1c07682c00c0d12050441e60401c0a00c4111804da14180c03880030401c0c20215440141d4070368515040f6445540104210f035074803002071004070741c450881002424200c070144855000a0002500d98a061085412101c2d80081c10b648021080c040ca204d1945034000c60486803810102e00c0d8041e21085405900181c00b5546c00701c0d1203409240c4110749200d0200d0403a04550355000158001d610845132800e0340d44040800140540d5400030300b8588521a9550798605803801001074004c80300a0704824032a0000e001c180a00d031070303625149048a658040042d0032000d200207440c010045404006c1d0010280c40044180d80b0318400d9414503045c1a500030012101005414a040e49040e20810b0f040d1200300b0030030340c500e495 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 620927059 1250 620925809 620925817
    0x4050609120c060a1211090102100e07090f0203180d020303070806030c060408010b0924040f06050604080601210308041112030309011508010203060105270603010b090316030b0606 79
    0x1c1c0c9402c46520901c1c040c00280700c1c2d00304512080c00155140700301020080c00d4002c80350341c82c1c80a004242000c2103800080c0d2128056191508a16a03841c000407020b0420421100140741c15801044109400380009001c1d510807980c84c50300303001e0680f40210451002551602070307110f641c040c60560f211031a044502107005403005030f152042c104c8a0900d076541a008100800103500000f890003844400d00005940041007020500d09142c5000d40054480041d8040c1c2c580c1103c00080190140115000415081e0804c540050f00443c0c046291000080c0d19070584544200c0d03c4a40d6501402d40503045898620050010310312f5000310340001c01c0e00040e5408000018981901a44252207503861034000325140c402c40ea445580c3c15600041400416003e401550020752440c138184001a05500c0340309210b010742500c9031801800c0e440305605080e00814002c040301c0d60b07560740b46031000c04c6030001c21005103c0e00504848802d000300002420701100e501c60300303194403030390b0303601c104195500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 620928309 1250 620927059 620927089
    0x112030302090907080a0b090405100f09051501030320070314010e060a061406042103020a05070b07060e150106080a060801090f0b010f06090b13031e0b09010204050609 74
    0x50240605801039803901c02c0c4902c1104d00360b490002600c0d060005e0016a40303040c06050082090101b0310022070408500e07040e115003051004180c4100002d182d0000741300200014046000302e042d01844130224204d494120381c02982c0758240058215458016413a0306044104594410041040003c21002e00c803020000300e40f0000454940c020012401d0403012520058442e646070002d200c101d540900040b14004181c484a041504151000c205064527100340c02184841034101300405108100d280f030101c0c0e000c0c0c10380c1c441706d950703181c0302c0c869410083d0304491803418000c4c810041000000c4680e1181e4424035106456441d01d1000e0320450700c06040c0b545515140e510215410200340110703aa160321581c002c09003008036041c000c00042040c0c022032110038800e64100030340c60b4003840034015190100040c07980d07070040403801d140780c40407680000c1c0031a120171015141030204034210342c0c503540100490030103651030302c010500300d01c16400f407580d01c00300c107200e000d140e0b0812914150f41c0305e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 620929559 1250 620928309 620928311
    0x7060908040b030f010501020d052d190e030705010c0f0b0c09030f061603020705061b21040c0f08030406110a2a0603050402090a0e101e0e1501120303 66
    0x30781c640d002c4020b1035004483c031131503018141c0c00421603960b04101290a10026240817400c1160030010f08aca1940400351445044244040c695a000d080c2c1080380e00c3d40409070041c02044029050240841807940c00c964403d004c4c0c4240000c095001d0b244541b00c003a4030800280204403142e4490b10541c40c003408425003901e00b40714003041601d0402c09420141a41801440e051030302000d2502c0405003e281030f0101801072000c1c0c40000d01c0002c0050304030b2141d40304403503e203810400301001406248490b96103800d04e102e40340c4080050107800c9014500445020555075141c0c900f0710030ba85550f1044007201c0c0d10802007000424454130301082580401c1b01910a07130421a01e8549461403801c4180c4501c140300300ca004000320000306000300801c1c0600b0240131600d0030ba00080c42c004070040c495903003180c445040300c01a210501111aa02005031420040180c4040313040c451030084101000c0441d1070141e20034078610002400a640c0c150310030b44241503a00f0540c641c140c0030743c6900118145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 620930809 1250 620929559 620929567
    0xc070f080c2104030203060a0e0607111c0c02032103011401021501080c011209020105040612020c01050103080409060f05030304060e0114030a0b040c11151f0e0406110f07060908 78
    0x707150b0305501081c01c041c00d0707070450316203040d40105424404090580c040c1d00d440e1500320b40b4003140200d0400d03403226032410a0000400e0f914002402c0940150800000c0390304656010101034104a244548034001da0450300f4400380051000c0001c0c28400e110740950205000400c18071400c01e81401301400184160340105550070540c582420080c0c01c00c01442e00002c00139942d55a02c800802c8011503068028011040303103400107000c5118070f002d18010805206000305506a60342c040b80c0c1d1050300302000300038540c2c0d00e04100c0c01c01e802c18000d030419181086400160044204104000e44500034095860300d440d00f40280e900682100149043c03041d56044402c3d0034a40c900554411969042d010924130710040c100000c5812040e030090500804030030380f8501d118005081c0000c0011040400f6694840e203a8404002c980c1510440c80c54074074400c04110b211007883d40034012441100c06201003103424419111902030340b0b18940c2c81d40e90034040d4802140407a08120081d50190443d50f02d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 620932059 1250 620930809 620930833
    0xf040518060a06090c180608060a050d03030e0c0315130303140a0c02071520010617010f05010f03030f0c060f0c0225050622080a050f060c070f080c 65
    0x7080811120b00314581e82e114401c001c60039240c05101d07600c1c1180c1c64801c0942d5420084040c160f00140a1401007008101c0007800076207428103540702800000300442d01b620100e01d4003c0180812601c1501c29006010b4407000608000450150000340390700d50210980c1c904101d05c203010b0f151481a01015140c01b1564211900014480c0c003804041e0008541103a410201030304d043d500d07a1000440da05940303043d010459000c55421070070441c1110400b80782101102c0c0502620080d000108848403040d00300b0359500055109140204401d4000e01c166030340c4001151000f5402c0c8000f4022559510403070064510034404910124429800003030340807015282103081b50845403050025a1014903010f0f0021079001454a40e001d2001c0126005c03810440820800c4c010703600102442d80400d00030001d00a01a4880405810a401180d40a803900e06060759201d0b900340803094980034820200d240003110900b2202c20940051640100c1d46859695001070f500004442c0390324042d20107103482d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 620933309 1250 620932059 620932063
    0x5071109090d090605040605030a0c0e040e030714010603170d0905070b0426031b150c070209070c080f070f0c08010204090c033303081611030303060f040518 69
    0x102401d1a08001d01140710078036005000c110b01c2d90032410034403d05000401c043e5a0200c22079034440460f51000c00c2d18002c20360306680060b04036594550280c10104818483d100000240a0721801000d01950404820303040e2401c07108203010181c16000000004d06841202c1402003411041031140016540d15640b41c860500d622a0402c0e481d62200090802030151070305040751521280030b280b003041c184440c843c107549105041d490f61503161401c3ca4240e0b05c410074071910f402102001d5825034507152911621680790b01950702281300c3d81201c80030940152040041c0312410742d101c50f4451418400000041e107541254400311880340c242420b48000450219030a00204030304000981c940d400c00700158152481c00c5080820940f91140602c80355081741c2182400000d040c0b00c903298008160b922660781d40c0c00c3c1d0409412600001400c042050013039001c080c22500552032400b0041040c410103440f0720099804039403007a400c05c1401c080d0701d01030b480030f50001c0450540c4450502c48a030418 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 620934559 1250 620933309 620933311
    0xa03030f05160f2a050f030322060f17010612060b0a21140103020907030204170a05060106140d27140c06070803010314120d05070f0503010b070305071109 68
    0x5801d40701c0c540f01e46042020450b03064101500c591141403a00d00d084800076114507080c8141c5114503000341c46420591414012140d0b07112184080c0d8840d02c40c4040c2c400a24501c0d846030030001342402c41000c1e0b1240c07254104101300da00e02501c04a0326441c249045511b00100c000c07070350340d070707551a080026800103180c000c01300b604080d16204604c0c402c6106180c285500041d02d0341041d070601459501a26246102c2da066030360444900758030340c8500b00c04a00a005d981c000c01004d804520b0000c1c2150b00c00030b082c80c43c0780c0c8110120303109a1b0325090115035005144801d04030046c018040e514102d00150080da022000e4104032405031190703004403001040406400b45d80e01c0780341e94004262600280f1070390380300010030b0300c5d40b520344042035403000c009200c14030000d00921901050451918800c2c4550381000100010f2035446002241c00c00e40104ac040d240403000c80c6000400c00c00341405034003601c0c12110205c00c00c0341003140c240c60a81c2d447d442400b007212020404805410031b80c1d1121402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 620935809 1250 620934559 620934563
    0x307170703110d150b0903070b030a142502030f0706020702030a470708040609050304061d0109061d030102040b0415020d020604120c1e03080a1a0a03030f0516 70
    0x1141d04486074443c03007069212174010800c546020028900c00d82c4000481200301c4444030201e6940340d61760301c2c0281c0200112031040e134003000c840f0284001d96900540206003428821130241150858078001c0e039907841094000d408042d01400240b0105200e640640092400a020342c2d8441203d903031084e91140c0c200200b0051230f900758143c1803d50700d40c0312045000070400009800003001045800c00f00200080441c0c080100d508009003c000907504862150b99004040b83d0b01c0e46c0c2ca60340050101c00f0442079042c0e210030140c151107070b950b1140150f481128110344514046143c50045e0030094a5034414864040d90208030004158500800801c01800801d426804e92044c90750002d0034031051209080071980074105100125a002d00343d040032180c2c40c01d00c00c400c0b00d01841c001b903241440d001e00e240c110040307069803010705d42c000448034407881c040441040900300e030440d42441d80710312245040c3c100e4030014043c00024015004600c2e4045941000c0e0b0500c0c828031800b8448025180301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 620937059 1250 620935809 620935811
    0xa060c060212010f1503020c15130c0b07060c02061510090812041502060408030609130b04030c0c0501110303041104320106080103020607110625050f030307170703110d 74
    0xc0190700c403602c02500141d00b4914040d490120500070322a40c0701408420300c0a89c0e2121404100c04145a07242d5410803035005600300249640d0314142110340e00183c0c81515528100505c54a0036407002c1030803841446204001000c4042c598107005c00c2d642e510911009100c015400420791810800c02d001d00703034400f070070020fa5540c14030404524030351815405500f55440001800000b4880c40140c0ba1b0008003550721a21035500c0103102819190083c50180c40d20a00c1c00501050543c002a400c40c92802100c0e05854680e4400c011a205c2c0b001841410f8241c2084c008600001c22405003d155100020320220385400303d5000b640041d40340354905400106200306061000541c0d666442c01004107082051080d85550003041240c42078107801002e8460151140400355509000da40815005a10f074640d0741164004d0107468181100080d0b407648119000240d0035000003084074420742240e0b54506028040300d184207040c0a000e40080249030b124916520b696480070094504980c0b4010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 620938309 1250 620937059 620937089
    0xe0f03040807080303060d0314070804030614010807061706190e0702060606070201050d230a02091302070305070b0c1e0a0e0409030203160206070209070309021e0a060c06021201 78
    0x1001442c0039030355405284580c0080c410803000e6034913030000741003ca40506124201c0840c0d005c04007200e200c0d12100600c0203e011802000344107a56204600c0301000d02405203c0ea40c0701c40c010340d070701d5003c1e214000c00110002c0034a0b000c04072068071660041000340004c0100c0c5d0b82c13940d90f07030401c0009800c11569510070b00200000b495040107840c1c0c00032030540f121494103a654000901510504a98040107916501004a18500035200d00d00b00400c034414800c003800c20084c01d074040c0d171007022902d204244420030075030301d08040d20031180c0b860b505480d40c9103007020b0b0b551001642c45008100c030702003400a001500f000c0700302c1403003507000b0507009440c03d82e122846500600b000640c0c02d0201d00a514040c405000650004129400d101000040440310a01c41c8005034481c8281000203421002c00e400344203c06030540c2120328428400c6031520311038010320718101041d140390000340758450307041d50003002814001c82c4068030640c020040540340191103030a06200660070b91120711690300b040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 620939559 1250 620938309 620938319
    0x33040e100c030e1005070c0f050f061005011805130507110102190f02030a08040b130804090b03071d0a0207060902030a0f05160315050919030806093402010e0f0304 72
    0x1106882d40780c0c0f07051408212509081c000101f10a030240c0e401488041d528100005109040041c0350041500e042213810519200910410b41181032064501265211822035011003a00740d842e0b0a50b54007034075881c02c0040900c1d00c0c0700500307000740c054414041c3c540b40606107500d085c0010055803485c0b4058000300c50391510000e0403503031520348020454205011195180b540048c4268009800000d81206a201ca07025042c80c6000204010a820740010300060701040680002442c19803c40680d4482a40c51050b00c480052120400440a100341c000402c00d9143c1d50203401c2240c0100000540e440d6641e01280ca80040140140c0740382c107100c9400d01c108202040314607612002c5522003001d00e0700e550303940300700b1807034862089041074ac5480000d1000700d010422a07900406184266040a28504001e4202c0d44c0c01e4400c24041d45c18840055204800c0e00502400001845440c2e211514100304a0610030a111040000c554a035001c489110004003c12510740880b040610340e924542 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 620940809 1250 620939559 620939563
    0x91509060304030c0b06180703090201090b040602062202011b0609060e1507110c090408120123030106050f090a09060606120b03061b160501110333040e100c030e 71
    0x20706d12840360701c1c0899040c0c45108140c1201e5000011418081a03c507128070051b512030480d0b4002100015001c10001115a400a10f0a0040c6410042c0c80b41e40200361800485c040d03d42d0340c019020400d800d400041071845d250340c44031501c0c0240000141441941ea60205840401d0b102c0a01030303000801801c40002041030f1290070040346d08107200802030020000751101d005000b160b00c20f0b400c100000d414000240100c43c280c440440340541e1540c0c41e40022081840444809007076245510030070351a40c10148922402c0e52001880340a0b40e160701d008021951500406454030151104071010009546020703004c040c1c042074460641d21445680a14101c802888aaa1103a0f00140c1448823468889904207824054800100c0e0307990034400b12081880091030f00100158604110210380c0180707000694040c80003a1180300d5002c210303650500384d410020344520708003440740030816980d20b859032080080c0c80c03088007611100751180c03107482d08071480007143da400f082c1c0b00c01e2280050001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 620942059 1250 620940809 620940811
    0x6181803090504020a030908120f010f1a0a120f050604150f4113051005041802150901081e010603110d0513030f030c05091509060304030c0b 62
    0x10550014400025500e00a110a000d80304032806281d00080802d151446034010403521900004655580d004c440c11450315800b00308c81601c4203200d25400400c03080d006402c1d0b00d04485241803000e80d5542121001e03034541c2d0180702d282c0103028000140d140c20b400c0c04d000c0c44980c2c180e420400039407403514005000580b11800742c4c21155036214401400308041c0c030706420058601401da0540546e1324a0303c82c99402442c40c1900000c031192903002010245500e09071402c0c05c505480d0074201282c059280c8003503d0099a03c01c038207076080182404141400d0b405170141d030010444603000341c4244e0f000302e81001030070a11078290301c1000440030400c0d40c00c03540c401c0d00b001084451003800707222250070504608042c040c0302c04140e01d800003810f00c05034000550390101040d01080180341004242401c012510030f10444c00715803090b1500048a02904c0f6554140601d6101c43e45080007140c1040700f10700c420003441202c84002d003c6c0c0ca1403030700c13528041d6105601c60b4842d5081004107007012094668 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 620943309 1250 620942059 620942081
    0x606021b010806010c330207021c0203150f04060b010e010c1b090c0806040b0a030218100902030112030e030115030f050f0303070c170a120207060b0306070f0e03010c090618090618 79
    0x20040152314011388680e210388200720522501e49034071071150b2000030b090101014211032031410140520110480c02e0410038052031180908004040c217000054852200141c00035021442092280c00400e00c54000360f80850700391140b00c804581c58101c1442101c0345071302c4c6000003c40910400445061510415402c80390480d400030070240f5503400160400d803480311003141d04640c14081440d245503042d520015002c81130056440390703191402c1c004020541c00e001e50000d03c08110022007800c0621848000700300340f0862500850454035480744c0100d414804484600c0f608090002180d4140081c600942050b0f40d09e160101c1c2ca41044655450082c2d502d0410040410415054540028484c80027046101c0702503120f900300d080140007855000c2005406000d103d0410000c2c50340428503d501000030b072101d0309907024000c00d1500b20365028800304045040d0359011b1041c00c0c0180c0c80c0b07088e44080e02d800c0c2c0f407a407901c445040080e40c000e6404400075503100c50191841410304d001d0a03218007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620944559 1250 620943309 620943311
    0x109030b3c0c13090606030905010b0406210510050711060a2306030c0409050c1c1502070c0f0e0a1109030601061b0507030c090606021b010806010c33 66
    0x156100d07000340e00c032030290800540140020f29000c000368405042c000401854508211740307565000c01502509400800310b0306035103480e20682c01b5143c00e100703403000e4412903003640d54040c00c41c2a0021450788074090540d020b11440d521000c07400c41034003d09209100b0342c1c0d030b940d248414a5400c00d01e0484060a81001d044c00c100486030f050040105004403040c00800140103601c850b00424200101000c045030014145280f11043c041e0014036201900810b8036040c0301604420b058007200042517800800340100c00c44908039206c8603030040c01405020380c000303200c0c0a60398160040c014503d81d201d00615240841004000540c510a0708049003030049124a0100d050001944a2405006034828071400045880c2e0380251040807202c000d5100c01243c011030b84905080c4034680740b5100d001540c07400c0190108400c0d00c0840c41240c8180224040c5111082a4005440044005140300d04101102d0604408181e540e06020411512a1071451520365090400403034900c002031030400003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 620945809 1250 620944559 620944651
    0x206060d030f030c0e040c020f07050d0f0f03050f07050604021806101202130807030c060908030d0533040c030527070f03080a081308030f060109030b 66
    0x301e6084800590007990038034001480e090074590030781c0c80a6100501640040c03500740005922900040c02020303086a410440d40c07805d40c3c803001c001030b00d00d107070034000e240b1101c05a5020000e10f80d04186034805100f802c000342403a005024801d5241c000745000d950310b03481542800f00350f0030f05803c2c203134a10514001d80d191500c0d01d500465588101c1d01059010003c540304454004030f1981c1c140e0382c800c0c80f04884002c0c0c05a0f5001e03001d540c0c824502003a02d0b000e2004200192040c0039107c1441160f01d00c0010710704040e035040e0b000f0010075009122080c40d150b01840d50450000042d03100154880401d20180308103440740034001150305020001c0d09051810043c01801d4802c2104031815040c1015502c1c24000c0100c0e45c00e040ca1100d5000104d18180050301108125014015280c2c01840d9a542030240d503550454507102c000410010f059902c042020600780e0781d480b403109030311000605202003d1940c0b40e44071045000300b11000001703011083c10010b05c0e40b00400c0d038040d80030b003041101045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 620947059 1250 620945809 620945813
    0xb0708030c0703020a050106090605180906060105070609080412060b030703020a09090503190f17012301030e0d09170c100e0d050a1b06020f0a0602030c040b0d0207030206060d 77
    0x521001d02110380e01c400101e114410035208000786030200754003a00a02580e50707030b021000050721950188621520004010001c140e40c9081c1c0148250034000003801c4ca174441400650360781e8840030007940c086d82c855000307102140c0d00e240108014499608040c441c201c10382000e804075116a01200e102c1d80001508101695400e0134540c1910210040020a550b45183c1a8558443c0c0008a050065490b05000d000b640150007401c049074203885040215242400c940310340d180c00d020b10001001400425004500c006040c94416201810009014500d0200040c9046c281d00c051030006140080c0034000b100c81a584200f0403408000140380010b050000030f015200e28240c06010044110400c0c1c0265441640d481800380e002803e0751640c608d07500300a14a00901c3c03180740100d0180300800100715200040c0c0340d1110401e100a400340c081c0701c3da6410042e500281045114440c00d0001080c250b4039240101800b039801d02c401030340c80c806890041c0c202580106903d10841e402c01d20303100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 620948309 1250 620947059 620947073
    0x8030705060f060a0801090b220f0809060f18040c031e05060613030602210c070210180b071103010b0d0b04031704150b10021203090a0611130b07 64
    0x2400a42d41d0261014030f07650800030490481d410f0340003e11035801c000108041c048555441c40c0100c0483d039995041500304401c1140c9071101c003000a1444281c601450701092110300030744446840144500c1c58240ca0480c14080d9401c2112203540d4402240030301e01407803074103100d041390b03048540c10203011000201c40d0115955001c041e2010030503440300c00207401070341d45000701c0389404101710050614a46a05210009420400e241022040d4040ca19170611243c0c044132481140a1500107181400795400e000406007004a59400d0000b1140e03185440c2c0c40505504000d0030820341d0346a10742070b040c00e000150f4a00a07010f24080c0c1d04d07025060465844145080200640080183c07541c0d44403450201d90041c103c41481c1411803035442030204011428040b0030b000382e8203110a11411000100300248600c0074030340741001d60700c81007240c20440d41100155a005000c4002da590740300098517840c06036a420040984250310006200c0f5040e407580d04000050701c0c500780c13194102010340d6a054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 620949559 1250 620948309 620948311
    0x703021509150129130909200306060a030602070c0e150103050f07090312020309041104051815040c020a0206042606040c09110d0e03090112090b0a05040c09050f01050a0803070506 79
    0x100c2000800a05c042140300ca051030358004044a0324100003a0340ea50811310403510b403e0000e42001000030404101d980f40000300540141da00800b02c80c5210714550b660002944203900446d800411150300040b4042c490800d01d108101c28440c3c3d0012480482c001000c890009040d0b40c0b08c035002600340042c40d5400840341c0140e0768040c0c20410082d41400c01030740746005011080764014244404c0d00a0103050300080e0080300d4081d64401d0010034155505100e04004036080c00c11004100c051507954a07054106140321012801900d0700e48131143c01065042d4065082070710300b040c01e0035003110f03481c94440c030400d07507801c260f03001e04450b04050740c3d81c02c000c40e100d2084550942c1c0783d000021080340d900040300e031000c03002c00c070820031101c0c00580300d83c503a048080c009000c21407024848403401d5481c040d01000c0f5038003481d41003003943d844945c413004050242051724178021955010500c001c4a05c01c10340143d41502e9500b210350301d00410880e004584d90018201c50b0018018100011400101d903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 620950809 1250 620949559 620949629
    0x1403090706110a080f0d0f140714090901140f0d030c02130b060d0f053103030605100201090b0c0403021e12011a040506040e100207030215091501 64
    0x1042c80d01c02003004280b03005000c0c8805401441c0000d0450300392403140b00202403c1240b80c0301400114609446071048400262129040c0300c801700001d40c501740b00d03584d038090010010000e40e040146d128007080e1000401d0700542c04000040c4c08100312483c102c0454844120112100059407a040c7c0d0300511404682e0402809403189250700900380c0300075084800a20701c0030340701e2030311070a900c482d00c5e0180c0030030800c0142c07191034030010990142d030244020950b41a11940500002200c2c0c80c402100610807109800b010307070310b040c04140c030f50300e49a0460031a0720036070001c1240d4040d42044120400060400344050304100030800040e1034495005034660501d0b0b4540d2865120440803c02200000900c540694682440390060103000c800c1e00c3c031b6803c0203550801031a036034002403204071800340307a880d002a44440d40107807080203141c0003001c06901c248182c070007540e110311480c540840306a0340300c200350b00032020006002445a441d28018120140491000b050110b100d07100c8000140304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 620952059 1250 620950809 620950817
    0xf050f04060b1b03071a0f0709060c03321809130f0201030b03070801060305011505030a020904322505010e0d140c0102100603080315040906110a1403090706 69
    0x10f060819020300aa6201c20b4004000b03002d154105061031809420440c1c40320061050203001c00c14540c130480308031090358959220501c0c10b202070781f0282c41580b20b0600401c070760301c50072032201c0c040141180060b002164510010b40c072078212140c42e2801064190200703005604c010200701149074110f8200585980001c04806165607500040300078050682d4460b070184200e140018803854158080b90480740580020409800724002058078801244600703945507014644c28009490400d40194115219050b45440101d0f810b030303907081c032485907159840103d100701401200d5000901c1800031550360b64020900c00f180722135180b00f9245031400343c1410002c5116030410700d500c4d0751080000c610b40140c081c8094410600c0101d42d503410244546005000e01c00c08049000c00d180501000d0b01c0c1d10001480c1184c1c0c403240c0384901d501014080c542e00a07100c1c20050081340041c41440e81000b03a8003581c0350f031085403100103011900000c0b4024002c038400c004000100102007003030000da92040c0b070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 620953309 1250 620952059 620952097
    0x20d09290c0d0201022820030c1c02010608120a030c110604030504140d2f03120d0e150c030a0f0e15011406030a05070315090e1005041a0c040f0f050f04060b 69
    0x11f501c1e6005001048e003140c801c80c170003001d4171036180000424108495009101b0242c40e11060794442d03280300b44003c1c900c001809103490040c007a8000050001c0d00c0d1606000e0381e04c003412114032380300301550280c010520010b428401c2c0c007102d200460585c2c030250350410003118240c1e1002d2a414030005400d0580004c4c1000481c0020303103140400d007042c1d000b000c8407185156414044299032041201e40842ca2400720b01c404541d502054651412040e5030701d4032200d585504000e400e541c4002d044d441c0c07035a0785d06005011170006101d90007403112180c0042060310300f500c5c00070b8040315068000c603600e1070303550100c848a5910310341100e41c00b0034100f00106a546440c60142c0180c24103040811500303044690201d01100598492503e2103400000c42d0181c9140341c14201c104e51003550054040c102087c401d6420f0078460f6a51038000280703050751440c2c140d84041000c03000f0310380c0c1c0245200d0420008200a5454a0300b0031035001c203803c450070004280317030400708060f0784035441404030900f01c0b2070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 620954559 1250 620953309 620953367
    0x120305150105030a090809100e031902012c0d1203050106020f121c051f061b03030e0a050708211809130204050c0901020d09290c0d02010228 62
    0x10f030586a140307c010b41403100100c40d411010700f5140030503031f91030300a10501520720505400c0b80f480200158040e141c0502c08401c460f114507100e42c0c200044a4542003030751070392907076841e44030b040e0035940d0040f90b0070011000c00d0306005081ea20184d0101045600886043c5141c16010800b20310743c011041c101903880e20000c41d4600a12225401684110b14001c1000110101e54600303079040d52000e858410450f40b603c0b4141c500108609008000c0da84012486002900a6004480c1548601c049402c03040c3c403540c03034615200081d00304a885401c403044540300c07108400c01640101406106c1d580c20304c084080c070944651940c4078110f1240681c00d002c2510f00ca0090100401d40350098404e000f00d20b80301c0c1d0501455440501440d005202e0034151000562140309076401354ac070b40400d0005a091417090051090b0000000116020310400503417140c4502041007407600c0d0013540000d41c483c01e100c0e03c900c40d07807c146c2103000d003280200e00342c803c20303550700c03010b0081e401d004d22041840100c624 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 620955809 1250 620954559 620954573
    0x901050405030a0f090e0405030406110304030c0306052502010b0102010b12030711130e070f090b1e041103040c030b181906020c010903181e030209150d120305150105030a09 76
    0x6c1e440926040782d04c1061005106002c00100155140b907100c075492045820030203596440355110141480705010000e1000507459000140c12500c410801d0341c1502009041481c18440c103200d07440540e41d101c010707000c83c0d40c0a000d001012241120340c0e061071001c19015644030310075980003c2040030050140082c0d9076828683c038490101c1c0c4441080841d900e078a8590b51080b00f030155182280d4080d0000450256500410110a0010305811a2540e890305510038025602c0c0c04035500a403600034903038544101101a502c140e019500c86a1894514207010000c032402a00f41007104040903002c4840400000d008000c90034115104503516245003800002800754030721984a650038080038105140d848549200b040c020f449641c0c5030a0303951113500b80c5244404940e80300d44a0107603010005443e000d000e165000100b00224100c82c0444800039260001c400c82c21100384505000c5210000d81c0742c440c4035484814031500d40d40500c600c0e00040c2c940c0c00002c3c0a00c0300c02d910307100c05404002003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 620957059 1250 620955809 620955827
    0x1d0325061103010f0905060a080a14071d061813030f230901021c0c02040f021e0a030c020d090e070309141b030d05040509101203030b090901050405030a0f 68
    0x200408940c0b2541c50b41016080d503e80c6104001c0c00d41e0601000ca0036501c0c008200f40200c405000090104002e2561110369054250721080524000d1110008810944898000040449455041c01440d00600308502000c2844202015078030b1103041003410360f48441d6081400740c050030041d10700c0d01d800b00c080350a0b1196a904410300b84584220f400718250740c101421004d4400d80079030f02c4281d1501006c02040c5040c40f4a040041c0b102110107015045c0340e41301032603444510710054581741c00c4565104030701c504a0084c0341c04c07c03c00240343c00030b03032f078148102c07aa9124244013074030111200243c024006106805540601041d2801007420140070b90300000a0652007604100c4840ea04d00100351540300c02486902c800c07403441808502482c01160b01780000040e6100d441c07c05042c8400d0141d42c3c200241448010114100049141c49a450381110300e207119543c00708020780100240321414802808a1503541e0400c0c0070301002482c0401520301c680d00901c2c10000078112580c0c11914025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 620958309 1250 620957059 620957081
    0x4180b04020a0f021b01080c0901050c1603050709050603060601030c02010b041b11070b0d05061305090105101203140a12110a0801060f0c02010c02221d032506 70
    0x120000c0c010301541c3d0003a0240d5000039554003524900c941300400d901909900c09112800591050006118a903207100988003510061510500307001c0c00114075494480040c0044030038080700ca2003002004810003001e03000d841d00c0e010900c400d09044020940d5160701a007000c1c1415220350321811400c2c800d521000b20020020402c0c0501c00d400d000c00304210303c8424807400040c0f0b8030b0504a142400010301c08044403005a42c02d840c01c03442130111001890050310744c42c0e100c81e00d00202c0d028070203d8050180130707618900000a460921042e0f079002c0c07600384c2c0d0004c0780801410f041036000c29000076800d40d84507107429005984d14000c8804440307000c40c031101105400e242054402d050098a07018204034a06500c40030001c2e600d4000036650ba103c00e607049000074103e103140e000194850307a01c00b80210310250107140d201010780740d00350350201c1060515140503590342c42d91500e211150306407803407040c000002d14a4104608102154410000810741500e580c0d81c40301010003800364840380b01d8507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 620959559 1250 620958309 620958311
    0xb040606050d11042d06090b060f070b060f030604030f080601140315150703050d05071803080a0504033003060f060503220f05010c030b0904030c140f01021201120804180b04 76
    0x8610b10401707009090700e004407010301c1e150400ca80664100042114034030a42d200940d42401100d03500c605160380020301954111210038201c51054500f0003c10707000c3c501c6034842c264440441c510040585400a181d541080561490240080029803caa801080708140d02920781c1e080400304003c80c40701e105400102a0025240c001d0503440b0f0050b2003184102c2d01c080c412622104c50840b298183c80c2c42c101d417800e420a204100050700300c3d0007413118082d5410003070f041554a40f6002c90b000860a41c01c1c24012100c44101d142c40c04440320b40428412504040007002d08102160f045103803030340a0302c000e20800202241f0303500010485494403000880741980708107058035001c0c0c005c01d00c040c0304464075070901c42c1c44484503020740140040b90002400c40e103160740d40c0d600d045528400c4410180c5090080100310500d0f170300b003404000d0035060103200241c0d48032811010000304420581c0201240c2d0401d264080014000c0750844003100c0d0301100041100d251580200b0003050300004d1180e2207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 620960809 1250 620959559 620959631
    0x6040303080a20120a09020901061b231e0318010203040e16260408030703020706111b1204060f090801050106030603140303060f12190b040606050d1104 67
    0x803000f141c004001241080ca1056181e45038110030a040d113421890096202010070014400c1d103101c0c00c0105151481032070f500180030b1040c1c98400c00b84080c489510342c012a4103003802e83d519010080480e00d090884008400004034026658490080c140e10241d8030340304c13040c60700702030388200143c401420500c0c603402c0c1d071401c0250b00d8102d040084074018010031441c905110503004042c07002807051510790031001c0595501d50f85c0304125032005215806144e421700c03d0a01041840c03068801803540181010f07620b0180741803450035400a1003403c0c00c0c9a00c000c218950001001003507034100c400360304280c007101c0041d039429181c2080e140c000c0c1d0407542c44d183c0001182540354001e20101ca00070412142c1001c400e400c05516480100d444c80c3d0003000303054444610b0704250070405c44514000041d2042c6c52040ca00d1180310204084041d211a0082000c1c00705001c441d1044000030300c42101d80306210b6040355903003444d01503103541c01449141d0303039440c4601041e048441c8582e540c000d06070480305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 620962059 1250 620960809 620960861
    0x17060913060e030406020118030203040b030a0f0e06090f070f05101707020102070201090b250503040503010920030606090f090c1314010b0f160501020c031903051506040303080a 78
    0x10b2030f0054400e0300010760034160600b000814020644034109e03010303400f8510301400c1c400076425591014001030002552084010070b100b07458401c0d41217842c245400b070081d509080b5441c80c90202071200410241d04401002c008884040423001c003125801d40e80035194848111043c2c0f2140200302c1e802d03d880b890681080000b0307a041d801058468402d0300c0c0c02c545180c40ba20b88180c1d60040810001c0c150700b0b88452024004140c06883d18000d1103081282d2078151150b020a082d00c3c45a1400c85400110507a21800c0f510b40303403221149101e0607001000f1620300080000c0141002802215210b20007901180b18038000340501d480300307000504407080091030170012000030140d104500780c0d000485000490943d0603c400c55114450300f80c401824101800344a403a01554000d08840b159800c02c00d0007103c49043c03015010158080010802da400988005800e6a400170080d6401c160a24180d403c070307170b0350348094a041d203403d0719141c58a584da002020008002c41d22082c4450403090f0000a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 620963309 1250 620962059 620962063
    0xb040314040f0509183a08010512010912020d0905060708040b0705070503012d15180902090c120a02040b0d0b01112d010e03090118090e160617060913060e 68
    0x403c840c1e4035206e610354112a04800b030080b885258072180004c0c8600010840780c03030010f03c0190b2070400007000046d100340c2541c8400c80720304561071600242e080741da40c441035150403c121b43c00030803003500d45a02e80301d45a0f880b00100d100394020b00c2d0700403e000c900c42040c00300402040b409460007800030803d4095031703100760019120042c07046041c10024080d03107850a929001e80758a541e032030242c810025081c4800034100c40c0071f0155031003807159200d0b4840301503602c1011083c010f00b00c003070110390b46849024611880340c200a00d803484650041104100380d00c120404c030f850b0b40c0e481e8140006d68007403400c0102e800310301c0d1071468416441020f002c0c0801d02c201a1124480b4500081251800302754901032a007601c0c02000302c044036070001c0c003c400c80f950158803844100800568003c01d03031030f12141694119840c40b15050b14690203001c00c2408103240d408460090302850410131711003800d00241c02d510300d40003000b0500136081c25010509601c085850500020b501103001e01100307100b280c0c85a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 620964559 1250 620963309 620963353
    0x70804060c032a020307061d12030c09010c081207021b030d2129030c06280201062112050403080f0c10090b040314040f050918 56
    0x1440e51854240240c281034068070660b090b149141c0114040441d030a10040702072090442d8080c19400100030040009403144107200c0c280100d10948651034011120f058178080e21144480d03030b4036400f041401011412102a140900c0007480e00a4421410f0301d442d0340d4500130200b0000601296109007c0041d80104139021800c141e452400c140c3d216520070160381c1d5410801810119441080b0580342840700b00341445e86443c943e10210301031505000c00b401410003a5030b0b030003241000150340d000501e807d020081c00f068080303070064180140c0100c0a420004e480c4090f04080400140c4084880d0003900000d00405643c2060000040b0346100120508200d610841b403114030006840c011314042d4007a501501d42040d411401c1c00480550400c055103d045606524400c5a450b02039402d100d00428a45a01c5500001c116080c02d260140812202e010702e0040d50b1010300c004c0c0101c2c40d0351043c1d0030460b81c0c01c0b1030305200343e03e80388100c108540388007080b204103000341c40600c559040038042607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 620965809 1250 620964559 620964563
    0x3040e040503040f1d0a1112090a050a05060f0901020a0e0d020a030c14030601121703180a141902011b0305090406121202060402011707110723180a020a1106070804 72
    0x8060b96a03080c40f0442100c0002c7d03070310500031701c042c440700c4440c2140d103d602e07500101c2030f01100c07081321458440e01e1800340f840604440c0d079071000080255070800720000c42d07000180d0300b0007581440714840000e0980b00400c40c5441c01054202c003614150b41d507541203640150b40106030051125201ca0f9075011040210003003501138800c220000036505410314442c1003464112060480d6241d40003a50718040d4405040c1585490010007455041041440740700342a0344107441201300301002c19480b1703041811200ca1001119558661040942d030400b0307000020310b080041c0b6000f42100d034502507e050261a0295800c54500040840e41c540210b403c41e801a0141d5030708503500d5040942241d451800300c038000e0006041c060006d02d5410904503507a0010000c4c03c02d00380c1e03419a40e0146150000d40e60046104d411901c00300600c0940d040c03650740140005031210319034034107480b411030010000580300c5004264006000e244030740c410041550003950070010740340035040030440200801c4041d542 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 620967059 1250 620965809 620965859
    0xc1b0806060a0b030105031209030319030b040b042a090803040b09010e0a3210080403030510030201020303190204170f060711150a1e05011508010803040e040503040f 73
    0x400f1525603828411303a070494070001c000300740c03280408410603c1604509900c03501444180555181488100d5415003a100540d4000582e00911030400c020b94845030a0702e4000c074604415480c1d402c2c0b00281c00c51904007242d0900c0020841014216280f600c0d5512006948c00003250100b401803140b4000e0900000c01d03a02d038041d800d0039008102940701d04e40b0074860302100e10342c021500c80c03990340b50402100480f80041080da0355010046500c20074092200030000d00003c0410082640521909800020a450503426181503500107503403488090000c1070301500c175103104100065160100c82c0586011103104040a00b040139103562a061203201509c1ca010303920010704002c0c0700b03d046100440180c40180303442480c840c80740b04e180c01e0180030460200c1d11561000d2028069400c03900c2c1c03490701180c0c0000d080d07251809035200c6801ca240c1c12410003a11500400682c40300106840c141c50b03100908201c00c0d2141d140851442c441c617400030708004945d0030f0001d40a403400c40140302009000c21 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 620968309 1250 620967059 620967079
    0x20114270918250504180506181b0a17100b04050c04030209040c171b06032502031306031a010e0913030306180c0212030411010c1b080606 61
    0x102d450001508611544240c0c1d2042d00e01c61540315400144410740c100d40e050358200c581e240d901150646d4281d01c41448641000541e50741040800c0040030f5000c4825024001c04000c1000240d0720307905210004059400c0300c50680744142d40d1801c028000b003a000c5aa030901074095451143c403000500c4032120382c82c0c42c0501040103420240280b6124940e0783c4100c600d0103045508011400101070030076503252410a0380460f014070040034401075a4441d20003041a05c0907611460104c0c4d5203d8a26401294144144002c24440c1055861081008403100105056490040303103140100c800c03200401914400000d003950301030b480307419040c140361804014143c2201c0103649001c06000d4441e045036401002406941c1d680241080b403c3c030928020640d03d6542000180c121002d65803541d0715941d0712404296036804010303010354500b00d0241c0394294641511041c0b681200342c0c0105043c80006451041000040c100c0581d05220380c0b03100c800101d40303800046a42ea1000c54540d4040d02c6240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 620969559 1250 620968309 620968321
    0x7050c100911011d0f01110f010c0905101b060b030f030316110c010801060f0309050106030803060a0509010f090c0c02120c011404030b160c020a061214090a0201142709 74
    0x4c3c0d481406101c000d020405031242c070500440d605410003a9a5029000b003000700c014442c4280230300380038170300c89a0740d03040150f080004104100b01002044e41c14444a1030010649100414407144030036009038000484951501c04a070421a1803603042016000c000100280c44007449100c005500c003a907a2030400d040501c140a5440114800035404188024010080d1510400c4070030903001d00d5107400710f00441d490b030f03515007506d401d0b4008656001e000f00c20400c0300d06156080344000c2400710341c0c01130030303501d03145000c01d030850329000d458446610f07500d1068032103003d910590801640134110b4200e119401c90300c1c5449071a80b141e56800140004062400240504c2c1560242d80d04003003080c5035a100c1c503c00f90340000d0846c144001784010060000701503541e400d9120003c0545483d261404104000b01c101190319a102c00304a1104070b4060001c5403034001440329140740d080c02c00040030b0700603015114950060001001d109408107054680c0c41904803006083c070241a03a00112a07202c0c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 620970809 1250 620969559 620969597
    0xa11030f121501170907050d030309050c030303060109030816021c05101b0e1201111921051f08071701020703300f02041e060807050c10091101 63
    0x410f40050b044001461480069011094100e103208040322600c45da10000b050311901d000e0002c0c0c1c08a50b0f0b0300c2a4a040c84010320503224044812000b55185203410303000600311441c0ba0002600343c410104540b00b014100703150f900c542c0ca070010108490344102414100c056040f203001101c243c02010b1a0036030303064040c0182c2408941c01c0258000c40d001542003190010003010f221a40070ba1200c40a0641d50000c0c030a0100034030324880c6243d5034106403180118113003034500c100380422a00c0d100d01208411340090303080d410744403840e0206043d22000e8a02140c007107500f44800f01c0c8910712030001041500020000c0c01c030760034000080c00300e03401080981d00f00d004c1d00f08064046003000700800120503145161440d41d01c000d00744488c0c21140804800304442e518074217061141e50000c1c00348203481c0900b0b0404e0110468850400009062180c0242500005003114090110104e070300c6c890740c442031091803141944103100300300000013400c01480f00c0c0c0000100078041242075207400b80c51065 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 620972059 1250 620970809 620970841
    0x1e030c0303131101020c0609100c141c11071809021f0e060301050612090a060203090a2a0905100e04051027030e0406031a09060a0b090604020a11030f12 67
    0x40280f40b141405041018802700e952240810f5040107a14030888000450310075043c10f1803022103005060300301c00300e43d000c440e000081140303c062000d04000c405061000055140554000d001800143d0300d1440701c080250180702c6001750712034a43c0303110b100d40c02c4c0e0170000418400c6480e0345d07030b210b055000c80c03d0111a02c002e000341c070341020003089031884d0308414070100358110144000315810b60300d0b5500c0f102e04170b1308140d41115064102905a070280580043c41d260520940c0c11200031000b060707192101d0b00c0720644681002542c590700082c3c1c0e40b413103007551030b0003c081c40310307010071103290600c1d1860305d4007100c1852201d0246000781d040c0d0000742c1451000168180d12070006002000b03620149d42c000c4484a0140d4019180d40d400310006940c2e02d50b0812054000142d00c209003810160707241480c600a0042c401a85080c250402a94501c203030540c11000035540142d0b00c81c48040b00300c0c2c96070082d0003200c04522000030080407100303132076004211408102040c50308603150400080188a8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 620973309 1250 620972059 620972083
    0x90b0a2f0616032c070b13032906010f110f16060507020a060305342a0803100f0618050d0f0206030604092003010e0f1e030c030313110102 61
    0x5420b19981c1c0030b07483d030310403154007448480300726802646d450440000035803000d80201000d10380b5460030410048054000354241480c0d804800c120140c0c04044516000000c001c0c03410416a2201100d849000b81c42c80003020b203828054400c04400007600681d9100c000c55a44280c5461074030002c0e003684550240d072394181e4020003e800c200c0c82c144e0210080c0101404224a0a024002c04a01c81d100d4100903800b003032a400c030800c3d00c80f02c000c9000c0e02c4405018040c1c0814103503001960324100082c00480482e0394000c51716912a00c0c2c184101c010078043c0d403c031103405c240412000c110325400203110b90b503083e80e101c0701081d0141c4407070600c680e8455040c0010304051750340c4212401031030410090744c0c0c0f000000e0400501182c035034580c5100302c408001c1507052000c0300080c0c80c00505081c081c0002604552000340301050041d80307101e541d005201400025040101000c5420300c80c00d00450b5042113100d41225140c0c00c200c00b4440c200ba500c020115944816020b4543d415400480d402070958 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 620974559 1250 620973309 620973341
    0xc02060a17090a23030405030a0f0209060405010f051e030708060117031c0506061903020417031e0703090915062601230a090509010c090b0a2f061603 66
    0x1220f244400107000a020213030b900742e03010502c00401c0e10381701000400a414000d4181c0001d0500c00d00500c81d040c90701074a0140100e0621005204032582c1e080c6000c210b42090301c03418040c09034651114682d41c403c2060907890300820000007003001e000070f41d01e8180c4a601300d01159180b044803103a82e0341d1003050115a0301c55403460000310074440d258086640704802512082c03512556284007252028a00440804640c1c0800c00384081c21034102e0312210140a8001586841d40d0807050030b16100da0501c035800805000980101011700c00d00c6444000c160f07022052221034013148910b48864081c1c059040001c103119101411804801455400240c1e00c0307a525800c3d03402e05034109580031309100040142649040c4203880c1d500c0710340c0d0b04801843d0801000503d802c0411656080d02c0101591a04101080c0010b000c20b041320821a1082102420300d01c056926404115222000c3e5440c000024503000d2198000c4000c0810b52030320842150704900310f441c18a180540843d100490405222 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 620975809 1250 620974559 620974583
    0xd0c05060105101403040b070201050c0f030c03060402040b040e160801060c030e2b1a0c031302030109060c0c060606110304180e1e010c02061e070c02060a17090a 71
    0x9810400f402c803240c0340c40c92408010310b000e00000294140c0c81902c0c102d50301d41d1888204104141c0c20302c03401d0b800c6030320582900d01d48403600350450354500002d0b00391b1602a40c008042006995180e044030b000302800f07050580c54581e1000c1c18407072917800725881840080254811480d10703200d036050a0503560301e80c541035101c0c01191400c9450500c60064a42c0100895200e0024402c000307180381c4a6044950704004407000030f290040080b180032680700170b4020b8a10900560190020070f07241d025001c001e0191090000d40006400b6040e91000034001e24540040002207a5002d2032013703045000b142c080c416140d680004440c0545c6080801c2c99640050000307100058a80401c4a02401402c0010580c21081d95503142085880704049401c007030110b400ca50504401c0c0292000d9801d140040c29103450044841740746081c3c0c200b00b610100c44003500103030446001c0c81c0141051600a00000c3e1244e81c9810301412071000252050300b81d14401000565841001902c00e4155900c800d9813401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 620977059 1250 620975809 620975819
    0x9030f0f1e0c171602150f0301170123041119061107090e06010f060305010b0d091e030302030108070e010b070b0601020f06070c0c060201181b0306020313050d0c050601 74
    0x290505095080311810450080101c92880c400081e080c144e46890442c2030742c08980c1304020310980029007180744204140311401e0102ca107031080c1d07811910301548a4601c400c00030040c900510300300089102d0100480c0018426420340340080d0322582c41804a0b4211401000030082000c10500510b01c80b103c62500a10080744a1000b100c1002094402c0b1041c003030b2201e80340c9007544e541c4da5580f5142d6111030010089800296003200003048641010040c41d41013081c030080501c0340f50041210b4681300d425150801c44400c1001684000b086101d4030010320a03d0010080d41c402e200740c03c10340c0710b08903012840010004406040f0b654150126182000581c1c50803040c600050500341940202c82501010744414400544604241d5455201c189014500017540200980288046a24058610700c4038101d00c42880da4058200c034000f4002ca100c1c40c0f1007400b1181603000100079500220034031103081c540c4044142c48602c5541514640499941c0458801c203100c1c6020b48294458001040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 620978309 1250 620977059 620977067
    0x3090c040605041e0f11120402280e060a030b0a1b030b03031e0912030702100f0219060e0a1b1401080f0402040605060703020615120a030e060d09030f0f1e 68
    0x4841507040c02c001c02c251b00c02004c50000354101e85e11280f240c1003013800300700841c6010060081c0251040d0803070381101013044003016401c605806014990020100482c03090380c1d03080f0b00301009540c4081e901c60030781791081805c1c01034489a2031030844038100c0140b801c0f00902038000c40380b04078009070003542040c1d0703141c00e4000250003100c0756520707808040104040c2a110781604102c000509001190368030020300c103002810340b05041031000c0103400450fa050b11030b80070901c2e142e41a48800c2041640707080d4180034004007622040141a8450400c0c1c134800c001086420003012032018081418655550603810242e440c0c032140301c2d0004940c10300241c120300a600246070441d001410005d41d0b140c4403004945640e0003e00c003580945d105004001b03007450042c141c6a24110140e0714038948828400703e495458a45400040a10510000042030340e01d80307100b40c070070316000c0390b106120400c054100500213040a101660001c0e500000c00300300280644000b803215204003990058040340488202c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 620979559 1250 620978309 620978321
    0x18090414300d090c03051b240d0b040e07060801090b0616030c0803040b06040b18060d051609060812031302041a09040b09010e0a0b011203120203090c040605041e 71
    0x100200e640e001c0c103c0100700c50351990360140d0f00c07a00c02404d40c0748a400500840780b08480c48070344503c211855100c0042102c3c003800401900800c00181c035807082d40c1c40100a00100000c0d1a04107242a6024280840c002002d03000c403210341e01d81b00c2991740c036100c0c2c0034141c0d88001f100a411440410240c0710f49150910100c0c1c0842c0a442d02181e180415075030a001380c1d00584054458001e14401c0c400549040d1140072070700c0e40d00303c07906414903291010803180e640000701640d100d404c454003040300703000050041c15100448084807030f2542e912042c1c8803004281030300400034079100320130741116400b1400d0205d038010708010742c10a1410b06a603013004042c0500e20b2001c4030039040e03c1a01e01142e103680800324003862103800d80008501e1f0040702c940c00c58200c0e4038104681d901c8504440041902e4a800d14151004810b181c140724900e0f06003a83c02c070b00c28401e07102c0351510000800c0400400843c8000d05094102d070140001c6655a0822056481c1c0c051820244001550100d5007242c00398444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 620980809 1250 620979559 620979577
    0x2031501081807080a02040b09060d0303020d1e0905160605031605040b0a03060608130c2606180d0507050d030b041805060603010f020712051809041430 67
    0x10b000000d404404581086181d078040d50700c0c0d50081102004520340385c01411a40345094a0301c0080789045000601c2107a41244090203250380001c21030301c6004290820200702080e001c40e00c0e00c40d0004000c242c001e082640c400c1c0c403140036040300112005104980a02224495038696065841d0701c0324504210b52003080550901c1420003000820714906e801401c0300081607100011510b06e0281d0203040c1002c01400001031443d0180c40e080003400c0301d900801603481c03a18036490040c045030701c1e040c5400c16591000c02907110302d204020300040d00e8907081c0c0c0643c42d6a0b069800810700c611040d80e69000d0300c6402011508071613a07040303d50b4031907400b01521580080c80403e91042e032001082c2d440c40400c20079150360300154208151410240070314040c00c005000e0440c50a21740b0f0705c48000e42c0b20400d1103d02001130002d61180781541001c00700c0320148004104200314205407a2403a136000310b840c1410404d004040005400303001410f0003071021000d5000d56001000c40c0d41c10035000b98001111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 620982059 1250 620980809 620980831
    0xc031203020d051317130b090402040e1906050607080313050721060b090105011b1a010902040303080f0402010e0f1f030b130c0903020906040b030f07050f040203150108 74
    0x705464141c0280569070281000c0d20b07000440100900741000901c110100741c903504281000b0700e400c12560009184211103c40703044a443e852301c0c00014000c0d01c507591100381308084c0a41801f181d04900f41902d510030106000401c20156640d080c003030507018208026240348000c7c0001641c040d850b082d041215032060050351103454a039012004c040c2d44404a111816400700c01c244100100b038400c44201840c208c4401600751725110000f0705102214620281c0406809400030400108202d0181c0340203a0280340912580c41700350900007500144801c1d0005400b43c404640c50001110156028540603507905e0301a10260f028481400c00703203001c03190030131890102c440c558900040015607142003075402250f44211101000784950103c0200e040c40e0303140908038409140c20854030401c903903050b44d0030440c81da1000d0006008000902801e50140946160303801071641c00300705101603800844404181000000500080b80001c03141c050030600d650480007210340c002c0e0783e01c0b503201c00e080c07030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 620983309 1250 620982059 620982067
    0xe0105070f060905101d1908040b0a2d08010e090304050d0b0115052d0c0312070807090302030307060b120709090b010b0c2d010c09051206040c03120302 67
    0x341c1d03001150030f203541c00c0d1603582283c40c030070240d104140104d600800c8082c00710703600f4a00d00441d0310b4032800080182140058001c810380c0410040c0010340d0001c2c401000f020303444000f40d481c0505080c294568800c00d0090004040040c40360400e04c54242203003560301c02240b0780c01c00c1040050040b000c0e1241009100601001071140c0e02c1c031840d108150b100300040304280d450840300441254001240d003050000c180000c04419a00b030391070052103443c1d140402c1340c01d96160707102c00862080380c210448a0000040d0f40ca101203140c0c45041c0500b21079035418007942c1d2001070485040e1480d010095040c1c208100301d2004c03c00076040401041402046084c4107181c84081900c0c24055610030889182c0740c070980010300c100c200081d801442805412417604100c0041d0a403501c82410003485c02d500c00140d00c0c181e03070038059124100151100d00030484000440701c081c0180b403003442694864044040d250000400c041105400341f0f500021744410786042d0b58800c1d5001c035030b0400360020035500f48 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 620984559 1250 620983309 620983313
    0x227060c010606050414040e0a1e0c090515090915060307050a030b01080606031209010807171005091501020604080f070206030f150a08070527280c0e0105070f 70
    0x80700b00b100030016520350582e40c601d0502c884040003a1030203403034403031460060300c2c0200072404140441c0e0070b54010105010103203100c000f5002210760740000761840b00c2d40d10010442000e5944502d000348003458041c0444104441003100103001122420426003040c0d5005440c000740504950b0022801002d66078080d40313900100f07800c00b195520940d08507100c2001000b4024040c8485504440207070050040c61504c80c2c02c1850038482e80101904001c1c5401c00100308030b100f10307185052144103440b43d0419040400c6864002d4000e4064948101081008664910414442c5500e002010703009003490303503101d84844840340c000c0802c040302041c040001000603030340c15000f1440754040103400003060030301c84801d00d0420f9021040d103018254003882803104101c001068011110704440c2c0c021a40d031210740c4501c11005409045880204400920140c6081e000e0981600210214841c0d41c08110f0f040e03890a642c683c2c0c80b000d01151346184952400d52141c0d009040f414010405004006156 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 620985809 1250 620984559 620984561
    0x5030d0c02120310030b0a0209210307060504030e0f0a1d270601030308011202150903030c06010909120f0e1509060c0c09060f011e1b031107090227060c01 68
    0x1c440344a20f01c10051818006c200d030030031440b5041908850110b050200c5400400c0c1ca01400c1d642540d0841c60904010040340c60070021558860b40c4400e0a1225051074a0050004a400104103126075500741c0f40c0f110b242042442482114407209030078071039808080040d12103000140041c0044402002e940c034201c1421902e0301c1010445100a1909601d9401d004080c6003041c2c10004204240070213420140c1e0b18811440b9407610312099603030381ca5510780c001038a140308004800146001c2c1c140002412001fa9000126050048010340503452204e1812a040d003c011801c1001c5904844403030355031b0078985065088040b034000d0143c0341c03c0c489400a4810b42003031840350f5807035114840098450a00c1f290a642003c001d94001c2d152180f400700107090b614004030340004138240c43d80c0d0f04e000ca81c4502541d0f104000d40c1c0c1520360300d01806050041910500300191616032282007800141401944200c031040394103405001d15003a000c00c0d401c081107040303550455005100340702c0801e8850003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 620987059 1250 620985809 620985811
    0x30608070f06020d0302030402030c220f0b030c0f011704110d0602090a050f13090f02060c030301060212070f080a090b0d150515030103021909050708040311070305030d0c021203 78
    0x70032104402480c074248009182c902e82c1c851030000c2500510034000141c030009280101c8641c221850030102d4507902544040050a10300c0801c030718105107440c204a01642d000404d49501501a18080718100f01841992010642030034001050b280011445050302c03290a50002e12680b090140c0001400000d020001d40690a94002c2d0340010740e8900c52411003800001010306a40d46180030300d1401c001000808111013a00b0616181d0461204014140700c4c407082ca81d03030062015884001d4600346036900c2d003090281c0001740c410000b1030381c5203151401c141c80300359501050f440b903144c102d56904007994010368940c0e4144030380300c800400c1e1819280050000c01c2001c00d0005403414003a001d1403036028159220502480c1010b00c0e01d0341c142190400c59056039010750303642414000c001e01800c0500d050f5030010001a10702014040465842803210f40514040d503600d82d01c00400c00003a90701c401c114480149950701c1000891040f10203900211028005801601c0e42c03c2003901000c2c42e9644 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 620988309 1250 620987059 620987069
    0xf2415041b08060307030b01150309200306010b04030807030f0512090607020c0109151b080f1e0c07030b101205070f060807050f0711030d090e0106050a0e040b0103060807 75
    0x2107044070240e6140c0c84210070703521503812001442800c2c0b85881b01ea00644040c01682090003200700d05100d80c502942007100c1c525070010200b030010184504071080302c06004001e034400d001c0c8030000940860140c0c281d074152600a2207941c84c000080d070b800e403808101d081c07101e010b1140501401880420704403c0500c44c5280c200a080300e40b4000f20004d0405108442c4681448102c00d0240400003a0000030b0101081e41c4c203000000701152065031034034046066008140d0700c40010300065910051303000e4443c9084100107180041c9106488640a006545640b00580d00c01201040859401840c42d504003804500d070410082d02d8011401c0c10204608040d501603114210401c030110382140e00c280100840e2801500c6d904120400074044c1c4980704c4500e0800b80c01107403a80608c90400d215a483d400014202d9504803030320304000d00700d000305100c0c0c80780d05015074000003030441c0114100c9401030025a514030081c2484002c000041084860321410540e0710702d40851a00e41c100702e4000500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 620989559 1250 620988309 620988341
    0x2f090406240f140d15050907020715030612171317060a050702070e090313060f0908030a1202030907031a0406200a030207240e0f241504 60
    0x4414040181c02d5110741607400c400c0000d20000307075501611110540b02c420715140b901180203e050244581d88540c190400f45d13108040e4414461a01d400164880c1121060402a40300414040080d001c03140c2c01d204010180c01c43d035503841d0004484101c0c2140c10400384019500384500c2c1c03015907000345a01d070030581c0c0780c107164182056803c0d4100074159004020f22070a003c3c0307140655000f51102000d11030f80320360713054404c045000c20b003060040d5000d402404680c0c3c00c1a6035220070040c4800e440d1108080421030015000c1036003000407044a400f036407140c807800d4200d9180843e010080d0300041403a51980640c80003c00000c1210203801c025204a8144000318202814071030b0890759800360b155480c035207010710f4200900700d81d801d0b01c0403c226410010b03101c407460b040c4000d08455405054400a95881004000e0205a032044c05040c00075011210107512501e00e0355034460b106c2d0940400c411481404440c0083e4800140313911902440415031015800c4010a054a0040034a88048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 620990809 1250 620989559 620989619
    0x120c061508011a1c0302010207060f0b0916202103041e030c0206090f0907050406110c280e130b090105060f131d0304092f090406 57
    0x12007424003aa80e103440c00d960f84440904076600015140950004540b0003504913044040305140c003c2d4151401c164010f0000d102e071241c1304c0d408030010100d210041d445140c106010808610421402d410907803010345480e10300a1002000c0070541140300b842200701c0c40b03000b0540348020700f82210342c0000700c1020301c619100c0c1802c3c6444800c034608684c20030007583d8501c40000105c5d5108803610b92040d01500e034290784031440c102140d0304200c140c03441600140400103000d0000d03401001441101d1550ba00c14804560880e4401c2d00c981c1d0a80505500072111201c402d0f240c040b00e4086041c5901140c10b551002d0b036924040d0440120803204485100100044001441120050b02d41d110110900030040c034948800000d516807142c1d400d4900901021400544020003644420000c20300100c0c0355003081100e1117440d540341d119008200e1060304103090355078104401d52420361181070401540c5ca60086a40660700c00e80c124202680d4001c1e2210030000341c1000388004040b0000115100140c2c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 620992059 1250 620990809 620990819
    0x90301020f09031e12030618070e040b0303040302180601230c120c0a030305040503130e061801182c15060a05010509121c0507050d080103030507120c0615 68
    0x18042c00254a0074a04000c2540c100340903400710711721403a203003d03194803034507616550049900c004540100d84606400c2c80c040c090320940000c20b6600010003201d0030b00c003446c1404281074a038001c9201c000d4124403000b031902c40b0000a04e11582d44140c0601d000700c01420712001142405a08001412001c0d0b0b00003034000c10b200d0140119104150100c04d41490811240005903035000c44140181c10140d9940120302000002d00854100007840440c41903a15221007040c68030440c251092807013070b101041c001010115000c10141201d0301d8078031180f822030203c54240003030a41c0e00d8000400402c0700303811507940d2040d611800c6840701c550700100f105c81480c0d0036101c4a0680588a140300e4400413104000c1070380c7c414100d8040350402d403100d03050703807204001051501c495406a16140221070f11320891003680003000d0828503019400312a10307100d860030103464920080c040540002c0c0c0030042000440e40300e0301c00ca03c9180f490300d482a542403c40e15480708580000071140c0c3d681e2885082000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 620993309 1250 620992059 620992063
    0x20301031b050a030309050607110901091401080a020603040f0609050a080403060e15011806120609020907030b03060c0315030f0618010b1c0f080d1d03070f030e06090301020f0903 79
    0x1418050310850f044900b10303100034003002c126104203440788100180c20010001403900817051a034000e82440b0b02540c40380d40e400c0c041d00880342500380302c0801000006101c10300007808240540c01419841c0386440c1e079211201141081e0340103485803621480b103040003810400074400d205008400264845080d803408206803604003544c0f020f42d03805105501502c184034070003a411100b05541404811000c013080070090702d01c9a2200000d88103040c814420310040e0b400450046100b1035605c0180c0e954213400760220340d241210960168091070008204584003801150008202100c00760400d8050380028030304400309030800c40c0750f005041404208071680e1842441550000003d0003a5444000070481e81803848488628140c0c42018903c20300c082c1503114002150001003c039529080143e034280074100040e400c07460414289501c1808200c0030041c0c600055004000c1c000c0703c03171031351000c0341c0d489072682d9456880941004218501eaa00340300500f0b1340c8200100240e160b443c0001098 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 620994559 1250 620993309 620993363
    0x708031e07020f1b010c080c030702030c060f0f0912030c15130f2003030301120218010e1302011101020705011a0d020105030123100c0605060105090f0405060d0602030103 75
    0x1c103560025041070000c080205843c409050f41840c042c003110019801200e500c40311a0018080d179000092040c00c2c0c940c00b00041ca9140e00940c220b401c1107010340d042c401c143c03141da2400070386440b040c013400e2203600c2e11800409070a803000b80003109c1c1c283c80f40300043c01c551140015082a60183e10400c01400565035031030340c841500d05402422468949036058030b041c44480c020040300390381400440001c03d80154070f000300b40250450f0384a68641d000001600828201640301340301ca24a42e04050100203c402e06a800720a403290403900d40b441300a0b07210181000882c1400342040035142080c8003440641982f50140c0008600700c41c1c00060940d90351140031441c0d0003426040442c9000d40d81000413241110f84940006402e6031010074010101d820711100241e0118600c4140c0801951103040c030400680640c0e010400e81d01d030312005546902c54040142e82183d040c051750b00c51840e080c0d10480d408800900140c01441c410764440301242d02c240c10440e541007161090720541b080044201d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 620995809 1250 620994559 620994571
    0x240221060127060507140111070506092a040902030313091b08180109020315070f08010303020714030a0c0f3020040c09150504290708031e 61
    0x2000d84056020b50400e8140190041201340040040c4200c104900c0240b03c01d40d54848100070405c110395408403030525405041d00351100e2040e0000301e0390b5880040741407201c903841c02100060102c4151101a44980048255a40a0360700d94122000d40c41c00e1004207045000b5402503000079042c05040030403107580380350800311f00d0320140300201c0041e0440c032519008082c4c0c12007580b000302e10fa080340b400342007200c2000f9014000c11845030134152410050700c0c00b0301c19507140c90114184da6502101c20313a40900c009001603000f640d0810800e43d80c2c044205101c0380c05820b6903802600c6885a000482695211030000340907900c0410010072a40c9226464200c941201a40041c42c01d40b9040302460000000e402504203200d406945011481203030704c4600090270902c2180340b04040540449014481c500201d26102c401a13030083c0b00701d04850a4480400038401c04c2e280c3e00032428101c02c802a11500941e0302002410b01007000600550710600c030b5030b0000c0d0101c030000726018132100409842 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 620997059 1250 620995809 620995847
    0xc020309190509040b0910060902070c0905060a1502030f0301120b0705040f031b0810050412020708031902250503240414011803030b0f030a2402210601 67
    0xa005690f01c1100164019030000003540090319121241130400100c1680110003074640301c40003c6926054026000304c6000300c180c9804255114030b20820303580120382c2150f10500c1031034281300448589107419010002441240d00f44150300c01216440c0e0b000780c03c03410320101d0710030b00f400400c1601c54209a0107201d070b2a10342c0c10989000b24010050900f4000140712480382039800c15800c9288042c00c0c02022001e00b100c14241e4002442d100601f802c0c0d0341620303083d040b801c2c108111400003030301c2c00c2103a4854000f141380180c941c4921052110410280c0110300036034140b00e070140007541180000c00d180e44000810107180400305854030b10794a000c040003030750505000c000070300c0104100c0d81c0b2030b801174104420100702074202401488144a04d108008000c1d0005042c1941580062000c4006036031040007c8074200c1010741d5581007050013001103418040204040c1e805903240303204180e45100250402c01c090700000b1500d0708148104000c20340c03142c100245580d201814031000026406 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 620998309 1250 620997059 620997109
    0x5060d050415061e0b161202031204110a0501210b18012c040807120309020406090b040e0309063001090507020d0e061602150703051903060501021f0905010c020309 72
    0x70f50380313403241e001b084081e000051960006600900030310071a00c2450750000150300c1d602e80792414000c007031404004070740282c09450001c40e280d4010140f0380d41c098240040e40a070f2222a1000c2000f030310780103900342c3c0c00c07441c00980c11000b034140030f062038043d040042c80e54506c102c50100e80c1c00355081c40507642003545000d4060001154400c2c3c0bc480545401501806c98843c80360070560282c411044000e402620300742c000034500c076496000b8208402c003120207218440c0b012088655a00803039083c02da1041c42088004008030a84511040024000188001c0880f54581e003180d1a0000d901c41c50459072503130100f00c80c003581409400b8074030f42d05051440000080c2008952240900c1041c2c1c11740392401800c0300203558074024410b007206640e280d00e5a40c0c041382c2c0b40060840e040003400e65100c40d07141754003520a41c0280595810f407034042e4010041e2501c01e22444c01d00107041113841011030381c0c070300150700819000e004800c1c0301d020310340003160380d03941c8c2505000c0780103810f4a1882208840038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 620999559 1250 620998309 620998327
    0x20c07030b0f09190308010303030e03121807050102010203100e100801141012120509010c170c060c3a150e060117010b070309150806010e0a05060d050415061e0b 71
    0x1103003541034a4151030000340210100cbc02e03041c0f0318482c440c081c2900444d90010004400260000f120003094510140e448003945c0d070f0300580c00c0c0d00056030303166104041054280b2101048040b00e0ba48200180e00c50b001c4140d40e040c1580c21103010540340381000d11000100040e4210114000e001001402c90925550720207895115540d44000749100403c14000b070050800d80c842d581d048015600014403100e81d60407202c40b40d445a00490031071860b4007524000441e40805401a03030759440b0b01d143d000961038800407024a8641c88400041c6100c1224112200800c0251003030448108020300004501400d0100b082015407000b0705603070400c1180d03828042c083c1e403181c103220304507500c0703510030340c2c803241d15183c20384a120141c0c06c00d000010070025021006a40b00c2c281d140140c40a0702c17000c55039501d000a03c902c01c2410f00500d50401c40821800c02c402c2421380c4800d5100b070140901c020550100801c00081d10415170200084521107511025040c0c07100e11184014913600e4001c070303c0c0070441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 621000809 1250 620999559 620999567
    0x1c0201051b010608120c06132003011103010b1315050904090503120f0709080703240e0313030506090303091c030e0115060e0a0e0109020c07030b0f091903 68
    0x441000150400032110300301c41075025045400a06980d5040c1c500d500e903952134100940d000344105403210710900c80850784055080528860030351704400c0b0b072401070400b02c6c1013442d00a00214a03580541d6a0f40d107101514085a01840c041c1c0350360040d0b1076560f030301011007060402103608141800c40c8069003a444041d041400c03501c2a040580e804640c002460a000b801c6004090b10808005118020403044500d0300d01885c0c4541903544405d00e4179a261480e080d0f81c0c850b2170000500c0f00c1201c1641400000840300c0c02d0101d800c0003000481c4001c205400ba5040d40c2240214626000066070103208000c4140107031940403030b044c4011400c5160444000c0d81d02d0301541c004031002c00030302c04091403452080d0080d0081811550003401685405038081120008620803900011b4103850703001500c2c50011440390442d03041401c003800c944d007032805910080d1f005211510b5248031380100000000e00c407410303a41c421444500c101c056490f2007881103082c1001544071188601711025200006500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 621002059 1250 621000809 621000817
    0x30a20090c04050d1a04030309020a08030c12030603030706090632070f26060a090516030c41040305193207090608030d0b0105120a0603021c020105 65
    0x1200c0710584090380b41041a5011703041e401e10840c00740c854041100307158040d0086d0b042c075403095409441e40c664884009840307014204218400e600032403a111000004074001c0d540100700101600d02e043c105c0e5540100301c031003201c17045603e0350712503101c040080341a89980c0300034031034042141d010103052100008000c0c1e000740a001800340130016051000e00c503041c10001c2c83c507604007441000c43c5409039001d00190484035644116001500070070030031480d0041d02c3c01105044850040094900e40c01d8014000010442040041c1070698030310071225903413040c0d8040403a41c0c00030012035200c413806000e41c00701d00b11018500420441000012000500d0101442c1c820440c0241079419140504008609141002c101c005190315500304416150f882c000e6503801c902120320541c2d80700c48442c1650741502c92080341c0d400074460704074040581c3d0055000d40030141751503403400d00300511030303070700140c05031540c011840e82d5480500c2181003003c46003000c20386456520603902e0391940000c2a61007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 621003309 1250 621002059 621002069
    0xc0f0506040306020d09020d05071503020a0c12021207080301050a0503010e191509030201050702010509070602190515010f06020f010615051e0c010f150f0501110c030a20090c04 78
    0x42d0008801681d001705038132054201d0781c0104004c000b602c0302e081c501e0b40c0340a2801201100351a140900d5034050080c0700304c480c0d01d030054940010f0031110b500d5141c62a0580c500e007001303502130b2100d10100d00c55090003c141551207111465102d5040c6020f00012102e00c0c0c1015000e80e1502c80c00c000c0180f07000900004011070a0040381d0b900a541c5001c14030310b041c641041d0142400c0150b04020513406401880c800d42d503540c020451951200c87d0280c3d2102c8510131680940c0000780224202e18850324100001c901034400c40b4204044801d0300ca41d0340ca02680451350103500d0501c02e0001366814003180c007403411180020300520303003000c00115490840301000c030103000001039619545001d40e0303c0d012007080300a1942c0d485102c00201c03913010340008014212100c1c40c0480056091103810342440076101c61001941c03460342018019903401000d20107100084c46843c12080240d074041000c1040d5030300c1150030240900f0249008410b656841941c1807248400d4010440c060300c000054408644c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 621004559 1250 621003309 621003311
    0x60c03250306050301020a0908010b01030912120b10020a1b140f031603060f060504062603040e13140f0a03030c05040302090f041205040b07020405220f0c0f0506040306 74
    0x100c8a601a801400254412501940003042c0c5801345904100910102c03500b940003403084081da0b04c01102141c0e60f41710000c114803000c0d0b40800c5914450480c400407450040000507040e4040400204140c041d0b00718080146d00008803074003080300c0f103a00200701c41c0c40c68902582e480d044c941111200800c81000303d01a82c4100743e40c1845660801520071000143c00400f443d10fa01c0c2d06000010303000d000a2680c050f07007894000180c078102882400111000802000c0c054180701361100030800e00002412400d100a2001048000010b26440e0196100050250300d2084500e8203407030340410080c1d54507403500160341510070902c01154190340e09134985000122408005000d50303850095400180d086410401000031490501c0c0d4001c0c001c0340a074100040c1980e802d4811501031080e8000d002c510003050101500600301030300480e421810762151443c03400d56102c02918603e60400e070588107641908640c4081c801c44c111524003404038541d07094001402c00010805034491440024151 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 621005809 1250 621004559 621004621
    0xa020c011d0904060f05070509010221130602011b051219020c1213090b060d021c0207031d0a080c0d08130807090c03050f01030b070908030d0e060c03 66
    0x501070110011141d000500c10384860034103040040040071103c0d41502c000e45001c010a4400780a41d0a68494010590042000511400400e500050444000c1c445140305000805011010000c10740150107e07500000d207450007289000007800d09040c0910a02a0802911400041981e0403690004164024000000720545d05d50000c1c490310145007128015140c1800c06c484a9130010f29001005d60002580d01e52a05c4105003221004da1030706074008010803c481d030200e40f50300030700740352140e440070074401707600310f04821040e60b21031b00088001903501ca1041c2c200174640c00f45044182c1c0143d804004032070034080321a83c1c400304a19464072500102194104101d810b03011240340c0215101152251692500b0722641e842e4280182119541065404c031b0b0068402d00c9a00d206000c00070071102c56920b180c651071210700d0040c1c0301108200700e00201090541d020002003000c40621400007a881180e00d024905040000d0007410f01e800c41003040c803295108080c25814030b140441851481 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 621007059 1250 621005809 621005837
    0x5240a06030b0a0c0c0b090a11060f1e090a03110108090c1c020f0406030b04140303061c03180f05031b030606101b06020715020913020a030b0a0906080d050a020c01 72
    0x241521101c0300810340d5aa013410800707c0280885c103100041e200701580c0f0814180003003000450300504007071350110301040c00000c44040c080030900807041c1604070403524080c15003000ca1a0746009400687c1d900c004507103c1822940d003ca4910392000705040a0141c4074181e60000b00442d402d00f0586190007800401b003010342d52048850750074504000c0041102d10b40c0c0f46010f18920a0481d02512021040c082c220508240402228854200100380166010400c441050007159002c015410401031251544004030307c00045c0f0042c00580d50703100034003482d040406140503c296015801c0071030000402d1078a8070000ac260384c11241c102e801c903548001443e403ca4060285c288100d00d82d8000e030841c401408415801041464090000450140340c490b812105070701c24a401c840d0041d407002c181e5100c0421a0b406800c030120946404104070004400003030b581c2d1b801d50004c041040da01c034001c11510404121900e0010001e080c4903041c0316100c0006500c070800d82040c1c0307050144a41e000c1034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 621008309 1250 621007059 621007067
    0xa18030806151c110304050601050d0f060c020115060203090f060d0902100809010f1e110409063215070807060513030f05090d15060305240a06030b0a0c 67
    0x403141d614842c042d49600401661031111921800d541d10300343d00c0e00342c6200d504200344d400c0780e00c6150014024011646070800380408200300c0c0106075000420020703039400181e414000e44148026076400801c0b030f8200340300303505d07a210a280c0c00300043d54802c00924001c0d40318413071840c0300d09508a82031615400784200303240c0648124038000354094200c28902500b550040b101e54050016880200810540041500100c50f5a02c0d640a80003004d442c030401e01c0c0c401c0c1e400501c940041d560900c0e04090383c49010005865564021081514002140001d2000b91000b02c106280001700b030212805003600120b02ca50049507904941030070001145000d005100c8111707241d403640800304105618080080790910b404042048001031842c078003c208140c4035400303440040d803000b40f901105100d150358a94600e0000743c41d40b0340c8980c4440000020842c11b11031401c8403420b4032610488104241132001100e40c1c020041c074111468a20188042034259003e6a44005455000100c107828100c05503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 621009559 1250 621008309 621008329
    0x702030109061e050105100801050d020d020913021212030105010c0c0f0f24052d040f030c0e13020907031d010204180e0c010e13050a0209090a18030806 67
    0x60002810f005000540780c60014070f58099040b402801c1010380d03203032010400d20b442071080000c006400f140050040e440c1c4421910811840101001d00709581640400c401c1682210111000c5448640e400c0560a101101c0c0310140d034008090400d444035000203814030700043c080c5604102075080c0b0706c41008818048034014004c48019554955920402100d0070308050007103030070203103040e50250303524031485001444024143d196142010811559003007011030b040c1c102c07001000d490015405d0f0400fa000200701501d4422030f24480141503040040003805c2c50343c480d11940411b81c01700040d01031204007100306035034110389035411611800000c4024146c80d511292031010700004030345044005500400c1110380b0701d914240e102c03100c0d0070084201d80010151150a801204042505600c206420110180018503091031420707101400c1e01101d804540600d2080c2d4001400180c51a03c40e01c050742c00783c1340b100b042c445052015203000d801491044000c06008080000c11566603480c00c0035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 621010809 1250 621009559 621009563
    0x3050f1207030b0d120810030c090e01051f030f0321060f0503120730030902030105060916080a020405040f02041a16080708070204061e05040614060702030109 70
    0x10036240c8200000380d4440c090291080000309141c14045070f40c2d41405146440303c640c01044404043c118281c0a490300103000740b0688900e400004080009907041101030f010300f82c01d100015441040250311400c41c0c00280c0400104038100c2c5074100b8140048030000d003640da022032410358a407294903040d610280c00700d100d19981100e850a03000b0a4800354008021038107004000846240d448061588652003c041300224080400ca114089a020f0014203051003590407554070050403135460100700c0428500980c000390311001060154a400d00aa580081040320542d00300d09052503001c043c41e1b0490000303c24000540d00145186d000c59042d28001c000c0074005008500c2d1242c0c60074001c2d4014001c2c000e1607064020f101d2001c4882c0015903222858029551040c6c248688070005603411400080f903400074104050001600d941c0150030081070800548000850a21400603d00049811280c01a4601801004103c140751080c0300300580940c0d09564501e050300100740540990900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 621012059 1250 621010809 621010837
    0x1805011e2d020d0e1005160e0f0d050d0c06050708060d0b0601090e0a0f1508150c1e030402010f03050c0306100c06051f0f080303061c0b0f0a0e060402090f040305 71
    0x4c0b01000d07400108000041011400003003001d9a01d1035491080d0141c00c284160003e41c2c100b080c0a00360900f10074a25404400901c41b07040c0210959441e403501002d0506400098900c1c130301c070010080507008841d003201c810705140d215841d141e0701185c80003480d68006007084d00000042105079005505030700242000301d480781c1d901e142205200c40500300f0403821440b0507240408000b00860740c80000790541d101003001d0075403151340c422a400d804030050255030040c0d81c1044201d010643c3c4185004d4202410118030340c4030b107000e00015103c0350704505030900f894180300811201c45548001c4950000d41110180301ca2082001c045030408441c0300010915842d0000b80414642c0780680140c0142c0015030b590440723a00c46d00d8001d4038001c1d901c10000690300a0002c6029450f0043c2103015611240c10502c0d09911030751a1000f06110940c1c156107180c50b0302c030a000903880c40740140c01d000e20b0404c004010300d0030f1690215411000040409070300d0086040420105031140085900366450404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 621013309 1250 621012059 621012071
    0x211d040b0d03110709050f04020613090c02070608070203071a1e0a020414030f030a030f0b0d0b19060506041a1b06010519030302060f060102011805011e2d020d 70
    0x50301900c40365003058850f00034814444005028039150007040c0c400d41c48007003c00266291395080c885a50480328a40803450b020b96400302e0329a4003841140b000d0030156000b80419894480050003594002c0d0004045402c100301d5030740810040201c9601d0340a81009104203582c41040312040c4034010041c0d800314243c940103100c00c8480c0e40d000741054444528418010340320b94810140d96003140300000315a5002400078005c040d01940c000f038590403c034000401c0d4440c2300b00000d00d1482c020002203032001c1d000c005006141c805906030389845514010100309560501000411900681c03049062072181d01c2d0800c80b19012540c107a58150008024071640041e051001c5501c0785401d00030300303020313401103c860b0710020200f498210840c1c0e016000f0b4403003a101d03088606803002000780b2103415903484880005110040030005601c0d903000380d000085c01088c0d80f540e038005810740051400068180110151114280391100030840c0a210b0040f403401030900030301c806401050051514189420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 621014559 1250 621013309 621013313
    0x10081c1101060e0a050105121b0f06030f1023121005010f0312030506011205130b010807081e030307052b0504020306340504080613211d040b0d 63
    0x151259005207407503001071095a07200d906108c1c21060384911008250700202c0b0901065851656528407071701c2c00b60034103891a4000001c40d020f50700035940b08030b259031321204006480c0740c0d000061010b0719142c03422091120500f660307a8441f03021080304a00c6101d14110030b0002e1b85041012200402540d4814001036a43d8002e500110842d44426501c1d0581000c00c44925886031140780e102e4607050f11840c582c603051003020030092000400c4100785c50310f0b070408000420010b0080e54003c1105000a041090500f002282095041040314050040020191441c00d00100607a5403242607464426140e45014060401c507400c0c080800c58400c64009101e90000d02c4d64000314451402a0200c0781c00ba201d0a6240d0310760b000740c081010581018000c3c5c41004c030145a40800300d00d904d4544503003450784031203104d810950306032034922003183c108445d0303410402c01100c0005c642d184030080750344a0340306007c06440c10809150f0040728140c1604056200d54a0354007100d00c80c0c0c8090f002c030001e10154 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 621015809 1250 621014559 621014579
    0x160b1b07170a0219030f0b0403030f0e010509010c0203040f0623071b06111519020d050417120622020310090e0118061a2710081c110106 60
    0x2038042c1d000341c880960700c0b0340142d030307520440080740d40c01206d64514511700d4603000c00d42c81b80a8002c400b09074036840304280c011501e016180c1c1c0c1442c0803000250301d0400e8000b0383d085400302035501c000c1d90410b00c010044000c12026903402c40b45103041441120550614503448402030789002340c40700b81d0202c0c0300018001181c83c2200b44042d458480340c040354aa40b811344103051401c140d149558040e0701541d141c2c0001c40c80107a00300c920718030081820050500c41c4420b80e0400306155074207030340d50b02c100701c2071000220900d241da18012001c1403a248851b00e02051400c0020601405000c6a06044a56102c07003034440702c40c05503e9108548074140342d881c28001489900c51854850709002079840e501c88188034950381d204240c4880c428910a6651308406407100d45402145986021154407968850518101c04822001c1e454a00c04001400d17143c40340402a19a2104401c412011300c00c021001800703205080b9a020324112011410a04954080410046094650070402c000038100c086c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 621017059 1250 621015809 621015823
    0x62015090304060219050d03090201030b18040606051005070303090f0f0302060601020c010912110d1b1e0509040b0406060b04080a020a090e2503061805160b1b0717 72
    0x704d07429281d80040000c14900d511140c51805416a000f008006d40381d1400381d0703c41002c80d4818100440c0350006000041c0b061960645542c04522442c8104001c000700d502c5520041c2104681e204207800d25202c0040450107486c00c001c06250b500c9444105201036171004c040c4880e48091001e03200700c5949002034403a1020750780c0c24050301c20b184081c415980941290700549008040c40a444102e9440702c0780c2d0740608800c5203400117054151100403e0307910101e0400c03104000f07500800580f80410800c441742d06107954801c41c04403400140180c1c3c6e1030141c40c64106403c2085082682c0740c80c20800000d010560052011010000d00052290300210716407034124001c5a803052250358880448003a941d1030030b5101810b800041c62074000183e070751074021415902044e9140515141e5a07031208030354043c1d804139100344586038000104441080202ca850b641511001d04192804104074298051300055101350401c441c1d0404051074108000e40c01082e602c1807a00d06102090360007600c40d00303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 621018309 1250 621017059 621017069
    0x309090504082106240408030f030f010605130311040f05092d0613050a0c140a050613060e03240702070b0a092306031005030c0307062015090304 64
    0x9002400c5003e4041c03a9100113100d140058100701c1142c0c0e03000c041084c1d24a070a000c1d88440b02e4144000f203007001c0100094510924141400f40d5282402c00d1854240c0324141d010008000040140740c9025900c0c002c2a0201eaa00070ba002c4c40c603985060018010b009442482100c1038541020064528030014144c1e00c800c820300201d45c40c0c100303407100310001c20b48840034021080c0d0000010580300111448d1006041340918140c0301d4801c2180d941120307a0907a5070220a03440034030040800300e441c014030100014501124031030320303020b4541004030382546988110b009220401002030020746080c03182a80c040d0b0310700399080e02e00580708100454880d042c0d4900e40140300d20100400d001890004441c4035048a8440c0d100152070900c4c3c07103081926848007400400040d40d81801c0c9a02c444014501560314003d00c59545824241490700d00f6900303210b083e01c41d9102c030004000d2280c02c5010900005c40c1c0502484407031141c1002c031450040416800c03800da101c440100810107a002c00a041998 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 621019559 1250 621018309 621018337
    0x1090308270d021f020313030305131d0703051008030c030c01050c34080a0804030e0a060c02041503050a0b16091d0714180a0b0f16030909050408 64
    0x71050800d200015001180c000e402003210000500103030580280c1065061081c411a0315000e1a0140355000101030351044000c02c80c04204800c500c054510b210002e02034050540d81d0f403c0d2203044120704107001901e030034103041d40c4401055505415500200c0074180607011699140070f6410701c25540ea02000c80d0403007952038107011030300c0c444a4004503403500038100d02c0781607800c04442c08600e14910350165412000a03d0b00b2003000540d02a02803c500b1003541c0b120300582c070345810054840143c0c004054490300e8450824000d290700440b0140c0d04580640d40020300100703e0701c1da0500740b4850303000904240300740801c8004020044400602c07912030701c01d902d07508048680d0190707902200c50040c07101d4070000345001c0d011403045031500c1382d218400f81b40c10000c1e01c0943c00070300c84541c0081c0704440d891424505400341d41c100007481c0c600509132520420b24007581044c0700d00c2240199180d40741c03000d011580c51030034984181161b2000e0150010100003504003850840c07550b50002030310f07010380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 621020809 1250 621019559 621019627
    0x6011116061205060d030f0e0a0609080d09150f0203090a09020405190b0307081909110102010c050408060c0c100f0f05060303090d060f060f03050d020606030703050a06050601090308 80
    0xc807010f0060724041c03000646540c4a5180d10b80e000d40c0d129040301c00f03171001c110040855220304d51780e541040e4010081c0b0f03220000c140341487d1140d0b09100400051070103200408004000300c4070311031000000c004551805541c420411001207085104950101e548001481e001091882055000700211001240d505200e0b04004c138600301e10035810700c1220200841880000c00c0c040c010340c441948240421081e442049005540c642186c0c0c21580584044e0090b05940c00305580921074403101c0301c16820080e0034245031075440ca6451800400b000c40307080d004142003100c401d0400c0104400d031240340f800d000202100380008020203001c8154251141400c01040150071f0210840309554409014080340308450b880b2100500105c038040c1c00700c079a664030006500c00d50b604580300694801c00c090020320004040081c6800c8018044922a030020601000002d00014800c41444d80c0441d0104441d034400780180d410346010340c005054031600103a90f016070301c5402c0081c00503590b1440c46c03140c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 621022059 1250 621020809 621020837
    0x916022401080c01170a050406140a0b04050a1404110105041d0907050d0b0604050907050d050f2b03090521130902032412030703020f06220303050601111606 69
    0x82ca20345005e03d044000c4500441c58040ca82e4001543c01405200702284a54a180a440302c6d140704840c80803040b5903030b03058404c01c1c0c5054018107400072200c030024002024001c020307012289015000900c400e0440780d80c90111390045003590001c080814540030700690249000790784250403208000d142c020ba520119442c82e055102a00e00394100340422026994001400000c0401400584003403249a20026441d40d5081100c503034580309030040d290f18081403082510340003101030703d482d8600741c3c6240d08400d0440a400840f25405a18000c5215404c0c0e061590506856071010108460040c503500c030020b100e031000300b54142c40c002d145c084c0305595071990b1040307004c00d403000f112035886218516140036079038081a003100e0b4000d0005522002282c4500d14652207910301300d0141c0c1204900000c40325041c04000c0e80309201c00d40030700403204c400c0702110520000c03040c0181030566603800b084d480d0b4400d4001900d04d07001c03601218940d0f00b80044d6081d00e90464424400000c42c150010b40e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 621023309 1250 621022059 621022067
    0xa030906021f020d0603150212060a05030a0b0c12011d0a0c05031303030213090e0601060201050754080102070203031e071a060406090203060916022401080c01 70
    0x22503000d000102d0721241814440b0001a50040e014030300e09684400010002c2140710b50800b000e80e050b0407006035500581000c0200f265030080c0303440d1266007106070800c041c1d1808100103000c9031b400110707200941d41c1d00000f00858010000d1070741c42c1149920002c110b005c8100760920b008102004003076840d03940c020344001981c0d0380c980c0140000344113001040350003011012155a1511070b040c054100194044214268007080e03105019058840302d468007803080900081c1d015001d01d1009100501d004100681301a04c1ca4080c0b1840b240e124284c500b28004180141c00c1a04959844070059000e2204103e0070400d4400c98072003c0224034000695004140b00319491241e0142c0618146518442115803400790440d6480c6154802c11141c000910340c00098035030240d4105030360205007448418042101c1d8541c011240c014410428132000340d69084540340d0225034042e21a80010030307904200c0c1004003c040c41403030808483c4000700000c1d404181c003416100b03000215a804000000112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 621024559 1250 621023309 621023323
    0x6030b0c0702100f03020d0f0204050f0d080f0f0405040f0b01110d090513271a0601051902032a0c0102070b030103060b01020717010f05060a1508190c020a03090602 72
    0x95104000c5510220392071301070706502d010144281401402c104c000700000c400c2d80d41c20240160b215034006014000d900c0d1590074682c2c17000055840c0c1103a00300300d41e12245184101e2449042c1c40d28046140900261311008460250102400a00802100306280c102408034503401301d0220304070b842004800f400c001013980341c00e101341c2e580000051900c0180aa6034940a02c00062140c60746441c065250322007400f07520400758084080d071724081a0400b6805105644d42a07404001c19809100880e0307405400d450030140c0710400c4000c0c450340d00c54180d1941c421440c2c001141131710b0a68002850440d20403103c03107041d400c8191100d18155000498545c0750301c7c01074040c0e941041c0014004074459501c90f200841c4c041c011685696101c400481d505800b0b0185460169102d851050496816002d81768000000341d0341503800320704000b44000d0640e5440507401c00c004000740001c024007095650010000032004040001d941002c5009450321801e085c20f4010402444000407039510010382e00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 621025809 1250 621024559 621024563
    0x9011e020c04021c0608070614090609040b0f0a09090b01080105010303200a05030d0207110a05101101060308180108150f0d030e1002011a0609090406020a090b030a06030b0c07 77
    0x50000341c00d034001080002d4001c50781c0d0f100c0e503120b018007078600d5070f10511032032000c3d144001c000d01e6403900c0c2020003051010b0000c044003001009202c000f4a0b80c6901040c0d270070f02d8404540c00f26048407044007154640501c64170866010540240010782090198403e005070b40c02100e01ca40c540e80c98005050990380d0078130004000404184492800c0d46000c0044000812031005441c90f0b141141c44152454200f00c1c00d5813180da40c009071000800024094103003200314140c6070b104a017440c100010740d01d60700014800d005e00009010700c808880302903105202540e400707e41c02c1d07200d8082a21500b441860140c400740458035a00204822505800c00812000300080c00414500b078450203124040c881210124140300f4401c4144040b82e8451180101c1020700307074000241724200345502d01302e01e5007904036980500002c0283c2c280c00c1e12404031a0358081c0d0041000741e0b030389001c0b42c011207604425500c5030300b81d001c0100c00d02c0f03549011a0041802c49000d0041115a41c4820040c04540c0c0316171400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 621027059 1250 621025809 621025813
    0x10051009080c0114120c0901110a03020703120306080102070c0f0608100918021e09060d0803010e130f030206091b060901200f060f09010c080a0911040f0209011e02 72
    0x1d004081e40c40b0b007032604c43e98060a80c1450034404184a41410740d48141d488103400d0302e010039000019603201007030a40d0205131f00028901110140c501075110f03009400050200c0e590b80b01e0b8035211078000e8205500900005000b156581c0e143c4c284021005403038011250210300e5039074001490340c0f062000c40d014001085c40c0e880c2043c034000700342d001410302682190000c440c40d440036015079140780c0003285c48100d8022441145e10010104408a00c1c0180030a00c121000d11802c030200d4118404d8078103680b8250070340e03180c54941849144000b004494020407040400c81d4400030143d010503c00d000d14502405c40d800e14100d0040d840344a1481307041c1903003002050201d80060340c801d1511003d400c00940d0b071160741c0590a03403e2070610824055a50a03a80200203000c0b20001600703a00c0e9101400400030008542c00d00c0005280d00d00140808540b50344800c86030003480050070401c404060300500810505030903582d0b54001e500a10700c001c0c003062984c2010107a0030b0b0a511300e02c00112480d40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 621028309 1250 621027059 621027073
    0xe010212070516030303090b01060206090309060304110307181b0e0f040f06080d08060f090403080c0c030301030614100e070c030c06060e06030d26041a1005100908 72
    0x8280c09180c000e072409403002d2081e092958201c0014584100c042c5000340e9011510034030605000b0300845069104404550100080019002c004030a031744000c04100d5a896a948460404406210303600650a80c5030054a800044c0148110410b00864840f448207100301d008901101c0350700400d40300705001090001400120701d10708034070724100064000b03000184000703c01050300112032003504460705d01e901c0b5514400605410400455100364102c40d070303070840390074a004909100d070054402810b10481802107100c58028500b41c6071000501c1c0b003140c4e125a504d041c42d0000d4964124120510400403001c00c2c1507441c8032407400b042d180c0b050300040c0581c07a800003c440104499005900b084049498030380059218081d0100900302d01015858904115080501300300b120843c80c014441c0c4400c103180c0a0310500d0344900020f03402c00500942e59681d0611080c01c1c610b400711301b1100d1184408000c00c0690311501c010503250203881900d9054010f03182500c100e0040e001d90304103944212 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 621029559 1250 621028309 621028333
    0x10903180b0f07031b030f0201060e010311040203131703061507020d03050310030204020403260313031b02030f0d091d0a050403090b0a02030406030b0402070807060e0309032b0e0102 80
    0x40000c1c200284240791514400320040c82140c600341740044110009080c0000352650b0547c24012400600000c10018050754510754a084c4140d081d208824040c1e41c001c00080e5040185a070b440c0e1280c0d4115035581420340703022070991a154400c441d11131203034a60260017075007450b140094400705d40c2d01a1409507840203944056406070802400d500390103882142c040010f07162030001c2d00055100d02000282916030460035421290411120a46c42c0e00910070403d12800c2500704017451901801c00240519130850702c03045a4614241c0650980701c3c0b5148040e0305000000c480c21b102c20a6550001e490361076003800e0280f08421845604203031400700200d0b50400003507011f140c0040c441d003407207496181c0d1008103c1054216112040c0541c1003c18104481c0b5010301524248400c05c940441c0341c0009503684c0c01c03207401200c1c0041d00b020b503a54800100b2031810001c9031032510008088850f03081c10030142c0e200024440340501000c000742d040880150f8050701c004541140c058019040088040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 621030809 1250 621029559 621029587
    0x160c0609020a120b0a18030912050c0405160809031918030f05031315050d02070c080105010801090203011803080c0a050f0f300711010e010608010903180b 68
    0x1030300041e070303125002120008a48400e0654010658894080d6103500c0c038003401044100d0710a1020034400700040e80711000000c0d0320081400035100012080e11201125040c610320301102c203046190090300d840107000e882c1c0140080b81c0c0041301c20380d9624845640c0d148101d600c81c01695080c1e44540b030100000c4c0d000d18024290a240401d0321a0300c101e415075261600d4444450559041c0c5803034100080d0801c420030740810940c01b41c550301030281a4405440b5005100348a9410a0402250f000c1201c40130808030000007401405200004d101e156190031183c1d000b0202400124422b41c60300d29400c0c0744403040181f42600740e8254941c032416a0303a0f24006511544518609010400e0801c5220b0b02c41000d800a1312811411503200381d2549020520503020848080c0140310841c034207032003414001c0c10390302d9260307001c01c1070300d4400501d90b400742c1c0340ca015121800034900c0075420240d01250050055000d9200b203402956070301d40124410040419410441c0900000010100203070400ad00ea0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 621032059 1250 621030809 621030821
    0x1207020c04050424270305091003090c060206011a28080105210604060b060c03070c060e01111c1808030a141e1b010519271106041d040209160c06 64
    0x241056454442d240001800a40b003d508100c040bd40e40d80d020014050904004c038003600721400240402c0d4100310300001510074028a01c84803590002c1c114a04040c1000034003407c9155034407500c12400300c0720010700250002d0096a0107040c0300b44d0507020340c02650f07801e51280003202e4080d10b0540c545031a0040a4011104010b4004c5810007502c06607880400050403031501942a001c602410300000400e51406251001d04019203144480c00075400811044c0103a0000d00f003d018041c01d41e1026500031140071201140c07034129110000315500c001c00205050400c50ba11a0300d103400340c030224011402001c8080303820b41f1804a80350340101d00c0c070000b0142085948015070a078161a030700c050a44204460000000e10004084e0017461350f1401225801160ba00400c90136008415400710125002c0101820308104000d24030700c03d440750400c4034064510081c1d0406c0c0c100c541170910a00c600c2c1914224050754960002448a40c0c1e410302550380541c0503982c90707920079159103490000d4a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 621033309 1250 621032059 621032063
    0x609010201151517070215040c0801092006040f0e150d030f03050601020c030a030503041403040e0103030e010305130303230a230103081207020c0405042427 69
    0x903030b40c000d26100d0340400860b01c00030003a8100c3c40307650014001000b00075003200da403280c3e100009407061081094001c00d045181c150500c1c0b5015451743c50b820b02e810300f44c1d03c680c4241465442c000300d0f1018404040e030701c0b00c060708440543c003180200362003c0c415244528421030081c5405145d0505c00c0030040c40407660012061001d011264489030000340c0c0d0100c0c1c0d00c0b002c40205074400c0c41c062059070140101d562040742400601a4402d480000c05c3d100c40d00004001c040040001c0000c0410082c41c10b4110124064001c5030340711a15240c100e0b002c01d4083c08190080754810040c40310f150700c03902500c1c0c03240400b0340b109496072036990f4054019103401500c07000070f10014451228946c2030b455025118103070420011500440700010506080385a41c4480604405500180041001042143c555040c08030441c41c5540c0c5001d822820100369801c000e0b88223080805010600081d0003000c4042011403400d4941e207000c0300300c40e40448070200b0509181c224008504800524a1041d0b480b9181c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 621034559 1250 621033309 621033311
    0x9011802040801020d060303260c16061a150f0a0309060f050f150303070209070503190603031716090501030e01020f0f0c06070c1a04030e090a1b030c0903020609010201 74
    0x6a20ba50700c803400c2ea0001801449400d0303071600c080040c1640114044000d000b1401c10f00c0c0c19040502032400313103520051460305038140c0082c46844003000c500d100794640e0f810020802c0080c0380d000140089140721780150b80308003101e021031a0700c1e400318011144c3c0318103400310440c41c0110910050300a0010324205550700c41c0c0c0ca0314241402445030160910440315040d4500092412000303680c00014203000d20350203607200380b08640040c2c4035503141940080d421700b4100d031256a507000c046201e03010304120043c0f01d4242500001007640041900d0000500c0394082281a40c03078920904800761114111400a120040100200d5009501110303221650200244c9010b41d4020040000e600114000780c0e200d0001130914031a140c18000c13250090100c0c43c050211103503586030704581250201444040081c654040360815000b0365207030b10703028406041d18038186418180d01d0020f0100c641c1c031020b19650202074040c42c5100317115849121800f5100c80507820705680a002c1c103604002d0060f8155 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 621035809 1250 621034559 621034567
    0x20108070e091510091d0402150408010e0615030d14041d01030204110a0203030f06041416020709050709030b0a0204080a05030d0c081b0903120c070807050f09011802 73
    0x30703102c100d6101e200b040c0e040d6404250b1080b05060000c15001d0b55140010062071306000e0260b10140c4c1615401500c0e01185d00580b030b02c0313038000a0101c405000507004505070015000600c1141908424450030142c01500c00135924202c2408051001d889002d130300d078200383c40382d10400d8003c04210001e02c5100740740c541099104d40b0091503000c41000e03140301c00b005000c01042140750a006501315107460213030950810f07455440180d80d03404060301512070741c0300800005005464035807100b80c1e442d6404402c0102c40c02c00d0070b11503140c00d9403014641d0050151074000310b6402c180d401280e00906a55403903c5e041c500e10b803a42e116000d801781c81d0486eaa502040001031600c803c1103090349407801440030b1a51a0500c0e068513003101ca0310b60314034060040c01c00c04c02c00e01203610200444a800741c600071568400904001a041112005030150314140104020100000002c0e01d07006845000c1d00700c486980d05c400810200c280e41c0400117601038201c9005001c1c003013084642c05c003c0b6840c400d0240c20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 621037059 1250 621035809 621035837
    0x131211010513030b042a170a032a0203070902030f09120d02180a0b190306050604171c0809070501020f0c0103020702010c0f050d0f0503070e190504020c0102181c02010807 75
    0x21b2010000343e540045200c01800340240340c180b01d5021002558100100206030f1259801f50000d1604415160340c002d4014101002160305a030200b40258010280d80d1426150707a039410094005440c00d007500d44121001405401c00004d404640004d88a506420588041d0380f51002e035005000031404207040c0c24a0f0310840e00c80c140200098508010320f90b8480c060b580d0010403040e1300351501000c26091890400094540c1c0040b0340558120545000d0b0052100040d82e01c0c2941c41403030340e0500d07003181c0c016004a45d8000340a602460402040e95801079950004907560300040c0d0b04032040da0001d402d07071842176004c1ea008000452040c1000310300c28030a601c0708400c0108031a070aa45c0b6800200340030004c03640c080e60180d050b0615040c10780c01e40c00c1c040e50080c8903805d5801030341e00949040321070100e8004441c144100901004000303564422840310800d02079080038040151000703003510414140d01d04041c83c050b000a07820b41041e10526580c00440c0c8078400070b0078020074070100d060b400c20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 621038309 1250 621037059 621037103
    0x60d05010e0403082a1e19020d020102070302070b091c03020f011401030b1906050a121403040e0a050a02120405030c1b060717131211010513030b04 65
    0xc000c0060385100c040a1401d802c000d01001c400a0501c0350925105402c010204c0c211500c080303821a46184454488a21b003103130f40c2c10040e8003164186000c0c1e010030070040241038201d054000703030a0742e420341e0400b000300b07001030b8240c2c00b444c50001c0c0546c024440c103110f180c203c400580181000240401401c0c0380b1400c03000300203c034100059005030020018581d8106090040a12900c0304c2081070701d4642c9181c4880c201d540c80901a20a0403407402240440c203035050300031102503c001401044500d40c0c1d110a1715040c01901c0c4101c600030885101c0c1c0c102d00c0d00120030764080352191300c542203807990f0340580b140080400400c290841d0381c2c2402415030941c9030310591441b403803050000f180c0e01c00c2c00242183c0350403003038181912a032469010141180e142c9209656415070310483e119074540c062410a08540a64401e10b005020841b000080343d40300c00c068940c82c0d030b00610b080030f00f041c42c0000445031071044c0f484001071504007002c108005908261020361250043c0144142500402c0c0d07000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 621039559 1250 621038309 621038311
    0x72106060608220305030a050603010603050105100305120c0c0111070306020d020d0f0b06160f0506070917010506031203040609020a091d0303101202060f0f1305012c060d05 76
    0x180003400003410807040e02650700d0003070054600d02c02d003070380030440f9a0f5004109100040280ea269600c500101d000d41d2070035000080550f622a000f8006840c2124012408100c107200c2a182032045901c0903060001d9001100c52900c416400791860f06024001910b0b240c011b811400414862181c0010102d800c0388050070041005c4100941e503401c00c0141c000c1501e149417100b0861a1824042d1890ba42d504000c407440794607200d04240310304845007007a42e0345100302c0002408500840080090f11548079120106072801d120b06401d40d504090800c074200d03181216800c2d010351041880c0368201c070180c0c001d16800382c400d2401049003031807940070418034007031075010020842c0c54070360700e034400211101240d480940400095081d49449458a07031100e0b0507200780d01c1400b070002c003c0d40554682c181100c000020900d01c0030742c0d800c4582c00500d80d41d4000c2d9030100400c1641023020441c0e600c9034141400c80c0c885040c1c14410844040802c026008013114181e9120700100104144800140505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 621040809 1250 621039559 621039569
    0xc120901020301032a050405100b040305010b090f0903041e15020d0207050418120306031403040501090e0705120c0903011118010912060e0a020409060b010f03020a0207210606 77
    0x582ca03545946426480a0710300c54020101000140700c03031000341481c500100072030340e00701c0b8017150726241c0d041601422203040c1c020a041e6100094040305000c0305420429044009480d00301d042d0703031500c0c4644200141520003031595001003108100c2c405030100e69840c600c28042441000e5a80e9a58907586400c20150920241c0c0280207461111074040c8038040080c4001d6400380075081c00007000f403004102540700200643c4200070072240c090700c20380c080780155074400c81040e06984041010f030381d40d8029114103400107810000209103a1000b140c0c03140500b419031206424601d058012011400f0010003604144030148180d0002d50f409026880020480720030b450799400640c0540301d43c00d031001020030305008042408000d00640803500902c129007001c0f000030400c41d0103a096045c00307841803000c0d40c0942030441342d60512403194040c0114020903242c599600340ca00340182d069024100c5540c0243c1c001364001c2066910708030682d96940c50006400c031540c205665100201e4143d07800c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 621042059 1250 621040809 621040811
    0x9010e04050906040c080d0e01200607080121110105071403041e0503010606020c1c0c0e0601080f0c0a0e0604050901030302010b0111070b0706110c011a03100e150c120901 75
    0xd20085c4080c000402000e4090070020340005000c0c141d0240101102944c454108130040c1d40300340403a00400038450360354003d01c042c0c414a081806008011030b001303000d100340400f0080b0b007200084400b0007220145d00e51014040e0a1403803014015030300c5e6000365406881c00700000019221400051000344082c2095500398001c0c41c180c06000000200c2c2c6d5003095001e68544001404140e800244409040380c0c00c4548003015079401c0c5035617045980800d00280305455420340850782c1078400d4000e80c800c04007030780d841216aa0301d248203403101c0d00c01e546000350800208550010a482280b021040801c050000da19190b690008119041c009a10a40050359910b001d07020640c0d2001004500c50318020040841c541888407104451041c20001003410ba078442c070404076030303104805a0b0540340301d082c000c2005900100d608940d90221703e034202d1090213216174551011110b44514040300403200002e00d110840c200c4070540c41c110241c170030b500c2c042060120702c60181c00001954031522400300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 621043165 1106 621042059 621042061
    0xb18010b0d23010e0307120c150507020102040305060c0903300a030f020a12050a061a0304050a020d0c030b13150903270f120309030809010e04050906 66
    0x1d440c401c0ba5090118070700b51900c0c080042d1003480e01402c803440d842400e40d81c0c11107942c124028000c002c003890210300310f00c07500d0f2503101c0ca0740003440d4000140303065142e4894600d030036002c48840c007113220001350380c0105007414484080c140c1025101d090341c86000000044c4010303807003584c642c600e00001c1013456005200380c1012104504400c011550781c1001c1400400d0b140024500503071045c10b0102007001040c1c544200411a101644842d0804028800d41111030707201510a40d040c1c4912000440542d403220107200b1103501c5007410540f881c2c03562508540f80607005251058000700d42241d5404101c2c41c04861311460101d01002441d040c940c0340540340c1c814030100c400504110512080d40343c1600e005182c4c04c1c1c44480c812992101d6039a1900190654210302c010001003040c08200009907550014125000e13050400b074096001d208046030441714101d80100c0300354400c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 620863309 621043165 := by
  have h0 := BRFrame.cov_init 620863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 620863309 ≤ n) (h2 : n < 621043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
