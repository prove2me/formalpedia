-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5455
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:11.401132+00:00
-- url     : https://prove2.me/submissions/5432ce33-f51b-4a77-88cb-cdc008ded2a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 980935251 ≤ n < 981115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 980936501 1250 980935251 980935253
    0x206040b0a030b0108070c03080c03090f06010f030b0105030723041d0a0b1e010e0612100609050c030f0f0403140c0c0f03070b031b070b070309060b0f180c07050109 72
    0x83c043d02102d01c1d01151462002035255403144940080ca0354055455481507120125010815030010707040e0705250051590005010b44204070080c02450100c00082000f459810440701511040e0013113403080d08000d02c00c1010300c0031600c055600da0364254104801d10410340003e0001c0900c45141800e4068104908001c66000308070042d030207010b042c445080341d9850035200f201100304149041034030b602c480107210500145408642c4428080d040710404014509482c0c0b0308a004518886038640f00d80f411b110040b4a40a0140c00c101c0f01048075056040c42580c0c1c00c20b80d50700504000c28040f070f410005040c54499602d40c181d040b002040d46a43e40c5c860200300761101041c1c4146405901a00402281e50400003140c0301190960300d085401c41d100d410751403c1100790580000b01c00c000600110b008524005100340c05000b02d86c400003542e2980c1d290140507507103031800c064411505050f002c3c03003c1d2a03052100d885003200086013221590341d0351900046008951002d0400d43c60b142c0200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 980937751 1250 980936501 980936507
    0x1612031b0b0114150307050d1a0306010e01030c080a020a03060515120a0203150717092406032401150c0c06090501020f1b0d23030315040509070b070206040b0a 70
    0x1142402c1c103981c4003142220b000071304000d62005540000c0010410007000d400070f021030384030584803403902091512005510001030318000f020f800c203050b02d5640000400401801c83d00040c01000001c01a24a41c0c1854000590f1300c2518030002d000c41d0f840c4d00005003507460003841060442030080100200140214a1555641880c10304030300034030603900e55030464002814410f1203038100f40e580716607507074400c0b15049204c0c2016100b1841c0340700c7e01c40b82101d81c18843c00031108034180d041443c1da0614190301014940100e0982c00a0080078861200003802081c40805056440b89540583e059072841c0017100c0348903c0d02000341900311420f0000c01c0c095030001a80080b200700b6401c403424a042403610a8948100303407040c40484078051b03411080390801c60340404015015000325500c080f12024007200782030320056202020341000040141c2071a001d2402c440003d0166402c008901e82042c130556070720760b140100700c1d440c3e0000c5080811035640d58100c401914035900c0036601c840c0d081c040a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 980939001 1250 980937751 980937779
    0x1e060f06030f020319090323030f071b1421031b0322020d12031b021f050606090d1a0a0e0c1e1905031612031b0b01 51
    0x84000241030101002c2040c540b03000b40d9000311100c0000c085150f40307404102d0010000d45a0480612003c500c4603542c1980400030030203c2c1c03e003294a0f07070392890b140710710321703070785440105684180088004503800ca0366058111010541d4003042410b4524803000c04a8504400030340c640701081c5488104c0440b000c2810040d5008110f050a11006000611a0701849d4002210f20643d42c0300e010480c3c00303081010102c8102502e001800c40e0380441d000e6164006411103200c04003003c20389074050303000f0300d80308105081e207000e40c40d10203040c2c0d90009541a20301200392062091401d91100e001c80c01a41d5480101e4a00c0d240c001c00c10031400c0c3c8107152100b2440b0140c0c4101c044403c640b00000d421880d14010203204103101c002903c81c00c150f003005c100c0481403072061346504d0700e01032245204a4880c12051009000d581340008042840c00003014582450882c03c1e00c3e02c0d054403003040000c0040300d08006a415454100340407400050380c2440404103907014003a2003401c0080c00003520724000100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 980940251 1250 980939001 980939009
    0x30204090f020f2b05010e1008300d020301030507150c034a0f18160302071505061002150619030f121206060806041e060f 54
    0x140000c0c0081c118210490280000000d10000c04200004094544c04001104c1070300f038001c00050103180011003821210240c100d000040000001d01c15084203240405006100c060018110f40000a00200405514061442c0302c0034a01c4200c0c0c52080c0183c00366540350941d18030464403583d4909081782d881c04c0f02d200d21500c480c403003012280300601c2010f15680c510307090707102d0568000c200300502d286240c00034003225410b40009048094006400400c2844030b1080f40c803220590b1100042042c010355041c0c036940714004011020070079104600201d58809100a081c0f000c01c85013400a50291185840c000c00400704840600b810040d50b0380014020f603025101c0c00351200a8040c281d07500c017440c40300702100b90009800500c4924040d501c20201c4483c4d080328209071541c03503542083c84000c054007215040c0c0703400c060b48401a480a8800c9817034040034424011280351800161010f000501260701580d2504c4038019a06612500b112090345041c008204080d9110760400c0c0c11061801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 980941501 1250 980940251 980940269
    0x15091505072705031507051303050d02070504051b0a1e0314010608091e01320609010f03080711031b030609011509021b03040e0a0b0a120f02030c10030204 68
    0x2d031002c484070350102c1035003d40e00050020111445203420111400300d00400745010010100296030340b00c5400c0149100a52192000f403000e802ca28001a060000700d0700300c2802107180104100d0f40c005000141d0300c01e1244280d015035500340402c0125244446402d0000d1203141c11004000c00d19403552060800500180703001c2026601c94804035007110064070b0740c07074440d4401004141008100b0140d20300103038259000080c0c0d000e50030118045080c540805810800e10301c01c058008003681031501d0b6000340111904100e0358140880144841040d0102400c540000304034401003082070454002000700c020212010040400c10140d087c10a038102c440c001c4c00f400c0c021840101e0140101400d42c40c0c42e1200e5018130703003402031100081d00040129600c00c2d907104a2100912020701c0200054440f4003d110301510300325916500340c40c0442900341c011200c40c801000340380d9030030520035011356002401c008012903034000a490305c100d4081c2c2c0c552001c000c500d0050303120341603801001100e179211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 980942751 1250 980941501 980941547
    0x3020a0c031a06011407060c1107060e0301060807031509231b10020d08060a032109060c03080408070c030209010b070b06040b0a031b120c060e0307031509150507 71
    0x103801120380440031100741d0000717903041c0304038000110307a80c202e43c0c42e65815140c821441801c0000c0e1a181000c0c40d4030050105103c2c4d07010b980300d801d0038020100030741610002040304600c0e40c2e407424940d607071085035201070503580d030240c0c41040705034548012400c504020301c20703c401d54040100c1d00c0c2d8081c02d01c10300241170804140f04050401d008400039010305900982510100b1307400a941c0044c005002030340c00240303104003000040807950760340311922710a507203074450314090940506503089641000c42805038240c6d04900282e0310481482d4015400a0305949804c01c52604450b0802d090700f00135846401c0e1400499080a1000034100050281381141c0c40386e240c440c180403ca841c43d41c00f42e82c00a50607501800801d00a54104a41d0740f22141c2c141100c03540da15080841302c0b0740d04c000702c92003140c40310104020b40d8001c2c040c1c0090801200070300195861f41d580e0f04008880004042105a10352181e0028040e0355a04003100d01002070007407141d464080303030003408881a600d8002031003042c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 980944001 1250 980942751 980942761
    0x2d040509060106030c1b0c0503060a02040f090b180103060b15210c041d1e060a050415050d08190c0f0204020d0605130e010e03090f0d03020a0c031a 65
    0x580591400303015004050401c99003041811030140c2a21441082440254901d0074000294119900f450034021005411001c2c00e113030030541000c0026241c2015240107110074403a00b14904191021168450400901c0380c40207004100e02c40c02c1c441c07941041020351700000041c4a50f0341c00c10544198211404400c0154007000b100850064006044078214500540e03503601c01c2c01046590441ca1032684642440c1ea540800c1c01503842091100211200740014405190801c40c00303080c0595001d0300038106880c20901203040c2d80030911806219540b00e68154400c4c4c1d011114076409400d0141c031582d15a0001d04020100740e0165800c24880701640400c40b00b480c1c0300340c00d8200f54580c000b0404100e0106070b0200f1002c1d400c0300d21410b6a0903510500081d1503034402d40300c03042d440550340010501d80303901d80340b060071505001c941c088541c00030042c0b107050b541e4806441106071003c55142c2c240c60320b6800d0880c07510300150740082000c990964080144508040d0242c036462094034412803590310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 980945251 1250 980944001 980944009
    0xc020709151404090807050a20030604171b071a1c09020303090a15080a0501121b0b0a1101053312100c02060f0601050a1d2d 55
    0x61845a4074503014621010700603241c030041c2071002050002c3c0701080c1a440380d10384100c5503201e000c0c200e445501c4281100100011114403c1d24802d8080354a20414100c001007a102c01000348010309440030642e400c1020304c201d01c2030300c000000c0b542210b490110340501082c1d41d01090700881000e84081009070341943c1804088840755044910410805240001000050054580120303030500003440390034096140c00e100c480c02000c140303d02c900d50700480e1102502100c4e000e02642d0180d410030005025200000c2c4480700400c0c1e0190120000c0041d04010a10310b04940d00401c140ba8400185ca4514aa008440c0c0701c071455800c000300f01680ba9040c408150001d1091091090101e11420043c0d00200b00582c45110b03201410000041d8058005281000d550342500c1c8581d0380e8070841040d03e1541040416807140284076403070b03c2400c00c07500180181c0580d4001000b0040a00761a401e101c3e00c203030b8541820300c4041e260528204000003500003031101c40040701e401d00c860703440090785460 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 980946501 1250 980945251 980945261
    0x405090c031e2706011401050c0a0210050a120504170715060e010501180f061407241512020420070b01030308060301093801080102030a05070f0e01031e050a0c020709 73
    0x18407054480061038494019203450300207880c0d4800c0c42c05038070400002f581310341080180444966a580c0e82d02d00d001d1001412008011031040c188a03d8401000700241c2c0110800c1e805c10281510962500b44915155810034001d04045c40914201000003912a0000c40c09d14181c0300240ca074001900325011400c08180000e11818400040b030300c0c0104200c602804071403441400d04140030340b5204054544607001c40d0751101e4140fa40030f40b038505900703000c0c40d84a00d00d00f641a000050a8162400300380e502c101c803001101070301c5190740d4980000e03015214080b140c0354043c8800190b40354402401c06141248003440140e02140e0104002034581c074040c407801c40d06544c4480031100c160040c10740882c94803013840c40c0494844203559444103147d22510102d008284000026030b0b030740f9186040d02e065400c0600343c1014013800c0044209000d07000100d402c0716603001e18000803104d41c0300b801030f000e00761048458901700d031501050096604c12600402c01131182502100c400d540e4074074090007100c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 980947751 1250 980946501 980946509
    0x13020d06141e070c02061b06071803051b0f0a080105060415060c1506120807050f0a080f1c020307030902010206070206010f09240605030f0109020405090c031e270601 73
    0x5a00b4000148210b014056106180c0c0c0042c041c41e0501390740198102500000000b00400c5500c400d0030410b80a500032440c810b01040d22034400a0149590786665581250744101c40c2c140d69080383c2041c140e12102001084110018083c1e90015030300d480d80c0380240f601399038090060f810040b420004440380110402100e4060fa5040f030700000c00d03121000c5a03242e41a0000040351100070000d861090500900d4846000383c0d00207542b4034040ca0321030b107802e400f201041800c0c2c0000c141d00010600140542c0c003d12000c005c1c4560f070b00200040c505600850950505e0380e83e2010041c400c0f1268541d002061982c400e0f000c44400c0d03140d020301680e548409220310550035507594014050140f441d0040d4040d1080ca40320800d80c41e8020b480ba44074031070306401c50400500c000c001c000d50754110000480c010891014114505400c1c08003050040000078203042005800202281c50310300c0b0010003044a03044608600f01a0503d0000b000700c05a40d49104190b948c01d46e100b40059610103e519030480b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 980949001 1250 980947751 980947801
    0x1e0c0a0e01110106080d0513170a0f05070504110c0105060f1302070314070f0308070810090504050a06050c0301170f0307240905030d05160f050313020d0614 69
    0x405984001150502d20242c944122552134400005081100304054214203070713035860b0b00e03803600190840310704484116804886161030840c1020550300c00403403001d00098100c05d1403a1a20080d0502501d40f110a07400076800902c0d01560480316101c400160a61040110003480180c03100020407500c80040031100354041041c643c18024600140c0c010142c052081c00c01d082d218485209a211540015809031015a40702d03988104055100c0c2c850b603489540c5041584071820600c100e507902403094028151130940d07a0b4007280900104001a0f6100303a8006814082413800825201d442d030002e1180c13156119445041449034040440c8000c504400c1900541c10404191980c18a440741307001d0501588010000d0950018100d0082c940003074000d100455a560015a2840448000501d081c04034152a80700710b2149a020003030340c0c01c0ca691860301507200d1700e481030ba90b01b103d000c0e240025404900c03c4080402c10016810120101050000181e56995075400b0101400035010080641e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 980950251 1250 980949001 980949017
    0xf0105060a1d060603190504080d05160207151707020a020a231e030f06010630110c16030b180307030804060b0a030b04150c0f051803061e0c0a 63
    0x1c2c4c01c101000e194070101c42142c3c040d10385000c3c000081140c0341614103a842e4100042c040000804500600c0d8120301c024045141d000d03000c2c000203444421a001d041240d100c0c044000120300d00c6049580074000d030480700411941061900650b4500900f60101c1c01030340012000110364000c1d00b0305441c20403100000d9010440200b0400010703100300240403010300d4510010600fa51000c00268422444d000000c01565060140c00303840d00c0c6500100c4044141d208100c050810ba844900d08030151031044081340c0e09000c55040e0069002d0500030800d144a54a400300c04116102c5030103084034081d0480f00074546511107040342e9600901c10b007030316a40c410001400002d2140c9907040e80603002e040002898001300d000103040403203661040e640381071810240070502c54180f413a0310384610301032070400400764032040c09000980340651030000d0203000f0030074050554984c1051524030400400340c42551800400358122200303944c03850080004008000351900040600722100b03554240c440d03030700d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 980951501 1250 980950251 980950261
    0x30f05090f1525060b0405040206090d0f021c0b0912070f08091c061b0f140706050c040f1703070b0a0e060907060e03160e06030703050f0105060a1d 65
    0x24540d1500305480c510b180070410050401c03591101007a0f02002d82e0a00380c511245410802d00b0380380d1200e01a071103280750209020041c2d50750011030b1440070702500c1d8400c054101e4100b40741240c5a50740e000e900100c00b44048140030250701145407920788958020001600d505c003406583e40c020105c0801d2045003000354401141c0026004c4901510420b2a24a072400c10408103148281c03100c042500c4400310740d00c180800c6000d0255216500044116400d80c1000a0380101b02c01e1901203075005200144c03000f126421400000c8079862a0055400c0c0301e00d08103003890f003140d40c1c8144a280421042004040349a070324240740030104040b468015410b054081c0c440110504005d007034100c000d40e07540000180321100b40715480c40b843e0040003500b145031500501421422100d4076070351080c1c1100300184103880f1824041401e81c0c2d000410214076684100101c1c1c40d040319074101610034440d846022443c40380c150407041c0b0800068031000d10165940340c030f0940e0400140c00060460090f440050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 980952751 1250 980951501 980951509
    0x90f01050405030a300e07090c0302040905220b0705040305011109030f07030c0b030c0d090f0201030b0a05090a20040806190504050c0d1509030323040206040605031f12030f05090f 79
    0x440c0744060301a103062623501d02c20807045908603c9002c010030780128040088900c907110b1158002080451044024140800078095814400c002032030b00c1220341c042600c0034801d0064074007469008008104070303006041c1c0075020b50081c98469101c1d200c0c0c0d6001c0003003031001040501c1201c3c1e00180100c4a28284a01019107800c01000d00e0b03541c0c4014051000c000525004544080d4003c070305001c5005050f00004056446403042140245c00304041041103807240715249500c110300c1040084c2031180c0d401d221801520350b00700043d28620108010885883c00f152003806002400ca1110407464a11080c03815a64203e401800d030390000d2008603a0360030807040406400f842800990600c101500d29001281d81d4041c0a80000f40d603003884400701d01d003890a0030009207000c2d0840c0310740c0c603250340000d1944c0300394000c0b9020040c000c004501d40620100e07100319800141885548420b846113448500c0034004103040d030004a0300d54501c50001d014000f04c43d904040903128208503e03140c1c00b80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 980954001 1250 980952751 980952761
    0x10c02030304151107030503090601060e0109170328030c0810051e031e01061217070f0b0103120f031a240c030405190506090405090f01050405030a30 66
    0x2181c001078454400c4c082e008400801495424441c3c0c81d0f41d9101d040c000c074807515000050b0008001c0c401c0d24400c0724016032b0446400800c48540c111101750000c2680101c0b400c50084035034031264280380d00400c92944541b60000e00480c03a140e60104020390b03460900715136051050340ca88800c9045800306100a00b4112140710250400840301e400c95103003280840e10317101c115001c00010082c02c4081d8540301c0b0080c05070340001c00e41059110422803081d2113010315800043d10189144100240c0503040001e40c00d69046016000190040113603501d05005016000d5030840c030000942c542e00c900715050280c03040c0c510815241c494101074400001c21700034102c64050b0050b0102c044800350501710010070004101140000015584442c0f501d0240b01800c0004030004610300702d400d005000a445a03802d0fa81d60901c1110042002d4884000b55070a01090706002c1d6015400c0100304414808004010103c000281d541c90b031030b542c1141005a140e820050b0304000d06051040030460401081d080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 980955251 1250 980954001 980954033
    0x70b07020f0a030203040501090503060103231906090209011d011514130501090f0b0f0304110d03020717070f03060b030319020703030306090b01230f160c0503010c02030304 76
    0x45510412001d0402071500010410071001640700090502c86568000201e0000380002d40c0146002e504560310303040070000b20000240948013810100000716001c00100c82d004c0e00c0e1a0700c0321117070320341d0b030600d00042e01280006034051007850000141c0503694071030042c0b03a00302e031900c0608541d0900554100e4500070229000810141112020300325001000074602c540081e40380700f524910784400540f40038099440001036600c00d08003044000740c0f0303a003198400c6920003404e0f60380307568900d40200003c102d503030969000b0075550007203800c01d40c000407044140d50805a1680030050801100c3e50741e50001d020f10038020040c44010070005020744c00c040e8041c2e1000381680c4c10b011140c41c105555003403112172500103038080039040040c5909485618082e29114a0070300140c003000c1c1c000b030040784906d900660307010807104014000c403002e40140c0781174010300c161455803000300052156100c81da006003a21040101400042c003468144241c005030072070742c0c01442c155681d41d2545003000d6820741c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 980956501 1250 980955251 980955253
    0x120305060a081c120f0609060b030c19050d060b0309070f05030d2109080301031208060901030b07090e010b09010909050105010c030804050c090109140603010b03120d1b170a05060105070b0702 84
    0x21001c04e010301540100003c0614241d00010b501e0b140881e0401500d200b6403121003004002c20500442203980005c071088201c0c2c2c0203044201c802030007000c4030340384201001c009245240000100301540010011400b420050b000c5802d50703902d40004508000342841550390590051f2105071005014164540e691843c2d080800100447c007051201603442030b040448040d800080140100001c000c3c0d09034010785c80b8030b44041140340a0000c0b444001040c000503014031148000240749902c105a41c0d400341a4024004103156510600848030b500000380d114041150300101140c82c1c40345100d52412110144d4482c901425107450660b85010b0150069565014642002c1c90a4903030441c41c500030101da003c005242c04503050354100000003c0c0009120303074108034420700691340025030010407141c0004080c0c1c1c0d501c111030600b0010000c044c40340d000449100e101400e4140c000615030300d9455480e03880c80865a40440e140d040b075400301e840300d020078401d014200100f00080c580d039030701c410540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 980957751 1250 980956501 980956517
    0x9050405090d2f0706170709080d140c0d02211819090c080618070c021207080a050a030f080118110408031c0f1a0607050a0807120305060a081c 63
    0x946204e0070580107810100106d2601030025095511125806030b00030303800d180c0306015a050490440c5c90742e596400d4003003000b4440f20342180d56800002264a07035081c01c02120f4003d00600c80c081e4460401d038804410ba960700d0518082c0d502150400c913003c80170f8156103001d001e140982000158120400c0507802c40300c040c08003190003200c0c0e201b011401c2990752140140c0380b81c10380c100007250312958107641e0002c2c400f00901014070740220300c090030503504070b17841381441c4049492a486c0020680c04071040c2d10a0580c400d080c07100105a50001c24020307914070701c1d032040d0346406540a032021301c03440710760305040300607211494455446213428a0510b05010705e402c0c0c0c0c8182c444e145401803a03103481d40010b64402511a09250b10030311440c60415501071004c1c0c01424160340c4840d500b044400e000f540001001c00030000e040c421580000c0e4009000350700c2d40b440341880c03001661040100b40c0030a03e8240400c0302c42c40c052050fa0704680c14440201203460b04038030030700e00811260850b042881015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 980959001 1250 980957751 980957837
    0x90506041e0b0a0e0105100b07030806060f040b04090b060721050f1804062705090a051507020c040513030315170c2404170c06070309050405090d 64
    0x18000321806243c0c401c00100b0b104542c011348500b12034029001801b0040c101101b0003050b180d0b20140d8038829007604200405546240100d1038520454000f2400e1174400600481e00250600181090301c017034050070004d04a01d40c045c030a20b4448ca00018200b9046860b940c0b80e0941c0c240d81700d80c003960442c0b0f440340c104110801803020f40d030008070408100034030002d01c03d00f0502b0f00b841094010310b08010505903070501c2151051861084680c19002d4a40700d80c006003160004101840d1762540c03220032180c1001012409661810f0241c92041c014000c01c8001480d901d00741c05564061b1a1082e4405181005580d081e402030000034000c5452a0700080005580c0800801c1c800d0380c0039415020b0081e145804041100d110781080201e081c0141c503010040c2140058820303103054034070401d00760b41d1949106200b185084480d4140960219001640c6030415134072041c0c942c11908240c5040c843c5407144d101172074a41c042800040002640203e00300184841c107100c1d0300d0034151a041400c150305c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 980960251 1250 980959001 980959013
    0x12110301020a0807110703170a0e0a030b06090906040308010506070f140303102102010c080c0307061a030c15090a0f0909030905011404090903032304021201090506041e 74
    0x210401050100380f2a008120b1281d40101c2c44c000494140b4000c1c041003801c40d6120502e18010745146c16100c0404600507520300d0058000310300e074110082ca0701e0080c030380c0c030301d80404104030448001d4050100c20011500c0d000c0e0014070103000b640d058498801c1030f82800c00b81b0010307800101042c1c17030b0f2001d90441035001c144d4080481040d420b001d0003440d41c03031900480d2459100d000382c0c42020382c0c41615248a000c80345401800444590900c0c0030b90910480f070030038901e07502446242c00442e004c00501002081615401131000c140d038208120100100c60040645403110301c081690030511786164056505125001014081401000e42895030745507040c01594140d940c00038442d040d0307502e203d00113064001c0d210500800c400d1030100002c05417481d0b00000c0340954411180c10039100c8500c03c0c105400380d0040d040070b000c0b9010310100c400d00311980c103c0704c0c401520141d0080d007000d64405203c079810f00a410700e880c1c1000c001d1215072529075a005021410441c00240303008009031900010300b07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 980961501 1250 980960251 980960257
    0xa08010e060d02040c0f030c020a051510031407060215070e041e0903080604050f0709090c12020a0f080a060b0708030402130903020d0e01051303060f0b04150f1e1211030102 76
    0x40146d076078103140c41841d14054106c0b80d4071100b0310259448400301c4d10008400140300e00be15003041d02418200d4903194030405188905800c0140701d4500c1d02c1d142246010000781110442e40a5804c07209404425006d04502c4001900d44600050301d04040310010308107900004d01420f00c5100c0c0f420448421024141100c0c403c1004400040c440400e001140c5003a0103080e4208402c4401c581003814104405003140341180b01300003036551108900043c540c0185550000b0040105c422340d994242d0910081801004000f4000801d40c4000850941d02c668410030060304c1802000600c0c20358152141c140b0340d00014002ca030f015050400001c0c60354180c1c011038601c907110f900184007440c0c801a002c0d006074206800c1a040107000c3c0040c258183d034072260002200d03003100002406003007115046024189040d20540c209003440c00301210001401d00f07840c1101e505902c0d030301c0f03040e8540404120710040543d6038400d0004070301041c80003c00c030314042c01c4014860003106014003423460100303007aa0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 980962751 1250 980961501 980961521
    0x6080a090f0c15030b06030c031807150e04050f01140d061e02030f090a0b0708040f02090903031f03080f090d1a041509150c1709060115050a08010e060d0204 69
    0x43e14010035034845805002d10420300030102c0e465415881c2c121400071060000501d21040c41c01140e0540d4030080081c04150041c10744890940d11118a404c0050507000320000240c0c061440c0400044a403044100b40c18141c4500d0811000180c2c040c07420407001034520301d000e403802070f80e4030400c0416410081c030500a4860942e00940c40b03107040c009074910500006e0014407550000e2103210005480115500d40c0410a8142010700ea00c45081550f6018000c2c50000d400040307101c1071003040e040001c043c0d8440c0107090840301ea0301c0c440480758421b00180d031100502001090203c84042e0b4403031005420812005080c2c1e2801107d00d0302d451156000140722408140c88101c02d1005125040c1d5860702c111400300d030300340036080b40d030703961203074204600d2100710105030b51389058400031072148003590383d02c001c420421102c1d030800c22845902c07040203105503000410703190060f054075400703942590400c5940e82c5448165a00c0c2002404190f0700040055500c49007080017000140d56600c140c0d107442c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 980964001 1250 980962751 980962769
    0x81308011802030c030d0206070c06060e070e0406060c020102100f24060f09061b03021e1501150921020402160b070912020d0f0c120c090606080a090f0c 67
    0x20500d0b8014942042e440804d824043d40125180f0b032107481d000070ba200c3d08440381c2d203020704210000307040c00303001850710750000ca1040508509012406a00051030039115100b00c4040121566800c016a248807550a009026802403103420410202e1580040561458a100803c100b001c01c0443e40380f00c43c1e01052344400c080c0c105024045070f0350003110749001003800d00342020755a08050014058218082004d5002d0b5104500b00d002c0501c01e1142c0c25120b4481e13082c00346040fa2448089840700c00f0300384170480c0c001c420400019a1054054481d1094010761613180e01c80d400c205c5000c2044288140b090001d004250000d00141c69501c020640b076004141c0411210f00e0700c2c5460030402c4805041c00040028801042c0100c400404802c3d4803d94115070416080a007460040140b100380e01002c0c201e140d0040d80001c00040c0700e195641701b83e11420349610001d03210b0b21038070b04440c014004c440000f43c564001842001080d03116a050f41d01407440782e003580545d03982d1501c0380841e0750040480f03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 980965251 1250 980964001 980964041
    0x302030706110906040302040b0307030b0703200403080901050a2d1206080715090f0906050a15020604110d0f060c1103041523070b070e030d020a08130801 68
    0x5110079442101094060405468a4400d10000240f218000c5000180c8940c1e51090f41c07003080d540801000c40110750040c140c1c03000d031401d248007900402e0a0307403450388603070600115038005050700800c81e0300f0340364840b80b95030401025030011202034020304800c40521070001c60296218070328031078000d9480f00b114450002c00c90008001060510f802e07144003442418020103005080c4007155074400c4e2143c1105e00340d04c1c2108000115840c2c00203501c07416428000840c08203e50345281c01c802c0a4400079a0f1800e030141c4d03920740c3d0030f01501a150f103140040c0c00000101c0c002035050b820303402c0c62001c0100100850718081c1c440c070b0103050081c8000c40307405e41e981c448090171980120401400c003001c00f0155051500e45000c540740c40346100a8403082040e0b080300300800700a050a030685d502410000d06441d680185801400c000d8151100408034044800b43ca0b0186000a02003031328040c5c80e405001c80d40000d80e01c0c5d00325a004001c40c026541511180400e041a003442400c01c803080c605514a8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 980966501 1250 980965251 980965253
    0x2c01030602130503012f090a0f0603140c120703020702060a0f02070602070b1e0f0c07081e0c040c0e042c07030c0b0a0c120302130b03011d0c130303020307 68
    0x8094034640d1006001c3c0e41045040d0f0400c0009408030005014a19074442c0f03825089281c549480c803512940941c02002450046101a00e275581c55082c0c561580b400c1025a65a41c07007141c82c10360484a51502803420880344a444400d08142508250766041c054200300305a0b00003600d40e0442c0601000087c41340c5490a4440c1e41003101100508181c0090a465070801400030407504c540000702e070607200304241c10303001d803080f4504491519010480240e2650302c00c000c0143c44184501c254081440762104440030704020303501c5000e110040134020441820700c041031001600c03000001c50180310348000302c2c1910b81c54078015880900d6444100000c1604021001024840300e5041429994080641400001c240da0510350a035074031407030501c1e1580f5907110215105001c80f08003d2038005503843e000400c030303016000b82c48200b107513010440080e515819084003a000910803400c2d6000d0800e1440c00c030340110414a40c001d1003030304625281881a840709040746078581d04c1100113900006400c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 980967751 1250 980966501 980966527
    0xa0b1305061204020a090501140603040f1e050d0f09060305090709050c0c1207032a0804090b0f04110906130321080f24010302120c0d06080a020a2c01030602 69
    0x40140404550802095040ca89e074140150f480204c407500030440000810280002c1c030309501100b9501540d40741180c0c0d00540008043e00e200380c070484040c0b061382c40e904c0c400e074040c01d4000c240106079a1108002450000b0840140001420b00c603c02d016a09010038450924024035202d0a0300120702c503a158058040c0300d2500850041080d4941c00500550000030350100c1c0ea003410b05040710005000350007034040380c050380c0c0c64501c004056040024000941aa494010081c2030108880300541d044184c0140405c0d262020b68810311140300300982ca590703140c040c0140c61070441c801154195180caaa84000d040c5220441c601c10651803211741c290b40550040c08554803082d0104048460b00f0440720f4910b0f080600141407a1400744280289284d03442517040d1012941d81140a41203410b1180d1041400d03070280303e207801080e00b00304d0046103403080002c00e902c4050340034114200d114508503052240783d48800da00b07128628040310340200c4004002d10103010b14090b040040e6501d05c1d1911740 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 980969001 1250 980967751 980967769
    0x25030e0102190f08031012151b12050c09060711030c060c0c1c20120a08041e080f01020424050304020f120132060a0b130506120402 58
    0xda1402c84a4001c9000211594103410031258004071305500c0c0c1e210000b03d40090f00c1d854108046842d1100004000d000317861055004c5126120380c2088a0202c100b602c4541d24072200c101303400700c0c5400187c0300e104003855010319440400a01c610341060b00345c00000d503580e80500c00c107607500000e4220b07440d01407a05103e800700c0100d04460300c521700101038000701c0d15640301d80181c610030b203500350074500c400b00301c000b4140740340da80078130b4116881001c00781340c40410b03c605100500808480b250078080220005070154082c0d0042c500c0750404c1e241c40c01d900000c1041c4058210204141d800005204104012040d0010820400035880364109003442d49140450401410b080d01240e048190194020341140e8000344c0640c2c02e83c6449001c00041860440e02d80101015980f0385aa050b04020002c0c11802d5507801c210800c00205100b104c0000554105480d0f03680d00c801b100e20b08005204140008040c160310105569000320b94580000f400c80c1c02164254022500d980100004c601d0003480c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 980970251 1250 980969001 980969023
    0x611040806270d03140a1b0c0c030804030f03080718030f3305090c0d080310050901181107020f0d0606080601090e0d0c0c0501030b060c010603050f1b090c25030e0102 73
    0x208002d011840c0144c007410040701c7d88803009010696421000b030014072510700c4082c40c0c1103914281d0b55a602d140c08d41d0a096821800c0e0001142c00b000304060a00c5900140c408101d6182000400c1d030842e00c8043c00300410314811500210700f0011074503e400002d0b0b5a92a02c640800c402a0311b207a50039152041d901c0017488280ea039004007a80c1c01c15176030f4606156221a800129540d12641c1d80d031005d907080c469540003254009a0b60000140d041040d80c0748a00c8841c0e4440184000c90014900c001d0383d00801c00d0081d8403000100c00e408071424003110314140e250103148081100c0d03a03074a0359070307003407003000e810101445454040480b0179043c2000704410b00082c61510001c40d8070640c0300e10301406002c3c05010b04160f11000c0c60f50040d0f80c0c0710150380c000e203150b03802000490f5403480c04983d51800c01942e087c00f40208003e040156010420402d008030002d00390301010364480c150040c05030f021151440002280003140d01e08400d010001c19901d81c404e440d110f00d41507500001900c1c051041c0c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 980971501 1250 980970251 980970271
    0x60504111213051e10140a0c1409101b03081b0c0606092a0406080c04030b04170c1b040501090c09090e0a1e0611040806270d0314 57
    0xc0c0c2c40001840010448104c03e60080c01e410040929243c190825101140512060303040c00c0d0007442010030100c05902442556208221180c8818420355014444911380c200740c800c24002154603052649010480c150a031a06100082c18100c240c1c5081102c0721044e40000d1008080100143c04502009014050380003194148981090b4055440760001c203424080c0a0a0020500015180c10302c0c0c1c1c111110400500001078002603840044d4002c4c3c80f400000988880c0841c0000b00404211415a9001081c003030165a071b6440d00101c1604012013800030231010405c10340b100c00180894246111200040d08aa01407041040141e03074068200070305840ca00070413121040c6d007200ea00422650303901404590790205a0840c0e0400300d501c04007508180f8803040420350040200c1d004841c0921400c010803040300d940c2c01001030350046000c0c580300c0b075100b4008181c120100c505003e240d101d01590401000386a112460704140c030041400022903114008050310062040d12103900201c014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 980972751 1250 980971501 980971531
    0x19060509150d03120f020309011d1504030e0a0603020a0e03010c0c1b0e01061809020405150904060801021b19020102060105060d060902041805130320010605041112 72
    0x200300ca265020020051080710b2200311001014060314020b0400d41d0391400c1040381021110f00392010f51700841d4241100e501c0c00041001001d40c03140c070004044903540c0240002040d20070007542801c0b0250054041c41654035604100ba510b0485000290555640150b1034606242001d0010420068120300c43e90600e580b0814a41c1e2001950329061782000740310b03104a00390401d0b5100204240c0080f0040c904800021a810303420880300c42c103000c1d103400e18064440e0b886030010220b000d13a000320799000300081d0b80320b03000541000140030703035120061000a419984120035030032644443c02c4501003c02d1450300f071402c007030706004042e40201c0f0035200000e81c14181e40001e40300e10050050510840c40450704c0b550b0455250322040c040c1001d07003c02c55a8a40f1000e9030100c2070041a4000d070340d40d00301000600d283c170a04000780d51555041e11548851055206001c020fa030600b400e10100b9907a480e0001015656402850703654070b8001100d9603246038130f540181d4219402400c01c00f0030200c0c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 980974001 1250 980972751 980972761
    0x7031b0821031317070c030c0b03090309040b06090d1101140c191406250f0207180f020315030111180105070309050316081627021219060509 62
    0x48040b03036071103a503003a254035103503019151180410081e040b4200c00d0f00808200070080000c044d1260b0b0549000c2c85503a0341955480e59076001c0d61004035140070f07458000b80648565414035401001c405040281001e003443c43c0320020807604601c035402070b43d003201242c0550906507003201c030f8598101180d0860902d048901790740c03556070340481041c400041000c030010005211078200800f07010350790f043c02d490103410000c8404242c8121402c4508410b5215981c075840c042c085d0070600b400e0f200c6c540252180c1490005c503c07416142da1580c41c07907800d03150020140740c403440b440203610962180c10a003100640341010301d0308440b101504201e01000400c440c0301d07118034500640c000823a09282195541c10750b458212120221030784125098070071604440b014003445a03224041d1000c06080303440b8030303003a14500f6a020040707200b0b081c060410580304001d1565140444807a848a20303402514107800186200c642280489a030304014401c5114841103a849006c0d010040004889003601404e06c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 980975251 1250 980974001 980974063
    0xf11040b06161e0506010b03060315060d232508060103051005061908030304060b010906050d02030903041509091422060902031b0a0e04030f1107031b08 67
    0x62000041d001c0040740050284000344018101d43c0183c4c454142c80c80c80d42c0d41c15005513260402d6074100c1c420b0080d0450920001c00c0308209078481d40000b840ba0144807840d4982c140310314985130710ba0043c5c50350100c00e03130001c11040100e8842c0c41c444409405000c10f503100110b44268094120b400b064100100400c0800c00010380b0310508107441c40700240781d40304c4400142d180d44540301c41c01150120040c1c0000c1441010024501c114000e0700c00703116400d0f8400046401e030289005040208d20280700a07656a041070703010303551014040c400c480c0f4140d00d616113844400308901e40c43e000039804220a011980076800303151000c0d4074041c10003040d8185680c15000300542d140e001e041c03a8461100200500025400c40b046458026069079100d04410f2507250401e541042c0d0540075403c241d400149000d03c080761b00348a141c056441a01b0080803400440b0000740b400e000000a1007a4500070010a112070566a180005000b200800f80e280c4813040741000d00740b40d8003440c03444604120441c0500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 980976501 1250 980975251 980975287
    0x315010501050a020c150d0e161e261e0601030f03020312010f1406190804170f0307031d1b0d0b01030b04260406030b010c0f11040b06 59
    0x2100b401e0258a40d40300c1a4200c1c0b522164614283d40700c0341c0074680824070107000d0700030f021040403c80d0138001020000781442e0350b1501d111080d20b07480e403802e17001c0144400031000d22841c2c8141d0f805d40341c0703443d0307aa01465202d60640c80ca08011500c1d10052110031030001c11400d000d584070380c003070010f200c002030140d15201c020500c0007802e092448804d0008241c4244116411000801c41d500e41550715644030380d40e440028002c0c442030161901c0d2090540c581071040d545041d8a450170500c0701401c01400b04c490300380c00361084440c0e480c00e4442140c00c104100283c0a940a0008030700d860f450007070720040541e003948034400b1081d038508034411a003a501280c20502e061040202d4601d01c8450b0001ca80e2070020070038003806010414001004021200b00c456001e540101d40c1c2d413142c1c100013840300e11854240d60718504007040810007040124000d80081c030a41c80c0504044207454100d0b15074651000490300112464040d0414a0a007864284600861210309036071035402e1907940070302c80c10099 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 980977751 1250 980976501 980976509
    0x30309060e04020403080a020d030c090b0714011e0504031812060507020f030c100f0618200c01050405062211130618110f040302240c0c030606031501 66
    0x111144950114a40b5603404480046900124071075442d440308100949131180b4407501d000003030811809038040c61117401c0e0b0405980c0c08140c124500300d51555440800c9502d820f11403400d540b111840000404008060b0043d0007180c000810340e4649881d00805070580a03181c904032078045401800044d54420b403014450380c0c0502d0004a44d250928140e28281c044d40da03d07100c91200180001302200301040f010030b0b0071a0301c0e00a00001620070784e12415140b0760b006084001420000d1004c64601a0b00321141c40000e0031143d4801c00d03482415119168061a00d07886c2d217a464809110400004204869200440903104081381c200155501c00fa5a1000000b401d41d44038000b02e11490340d200090441c000002c83ca0030042566110700b20140160303001d100802e12407900038480d072842041021640301802d01c210746850281107508014002040341c00c2c100349030001d1104030800300004001402c110f50307420001c3c5030b15a4400c1c209490300c00000c00d503a0080d04040801c0703030b17042010390140b030640f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 980979001 1250 980977751 980977757
    0xe011211090402031507111b060910030906090602031806070522170f07090608070e0a0b04050c090f1e12030706090c050406081c050f21010905090703030906 69
    0x5510b90380006807502c0385915400181141d6202441400f5030008400318040c04c9086c10340e01d100c50f0b00728001c0f241031804c100711900b2010820144082c1e10380903441c0c1014004909000031031140c40e8a5590444003803960446c1c1c07195000081c000d003400c14408500710703130204200a00d00d80c0343c12035006109000700c42c1d000351001045c08541c41c40190743c00e4003401030240101401645048400c6c0c00d80d44481c1598030361403a02452130003007101c1816016401c1038901c20b030000c00410f89402880e20801000503d00c400c025070f51043c95000390351700c0c040c06000d0420704411648600c090400c001141c40d01c0444d003449000c81a07911030a82800505200d0302c140c046131002600888051030714294450071000409080c5460010010080c810044034242c6106440c104081303a00c83c004550b84100007004203001e00d1810088000341071050b0020101500342003100c5040c444822008d980c04130764002c1041c0450301060061115041c2480341c1c1d41d00c413290381c0060080600e140c41c0900404e4940c001e150030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 980980251 1250 980979001 980979019
    0x9030b060315150108091504030c11030607032909060609010e0d060606030c08092508010e010f0b0604030b0f04050109020d050a020a0b04140f041b02070e011211 71
    0x195800344840e00d40e00b0b00c0034015110340d10700941da80c208605060a1039003c03842440106404940000e408401d0640c50103d9082d0781e00c0e6500c045e00d03100e0ad0385000b03c540280052080c0c600340c40521556000b01d040317840200301d0201000c1014200c0100026071041c07207001150f01ca030207079940d01c4201c0d080304099501c999294104401242ca8826070002c091704071090036807070810809980e014a0480f0400d94040290360070824048850361400e41d01095035611100707040002d2004880026400803e042080100c10395a02c0160f09540003092075100d0369640301515241c0712500d020310f0604400480d19203181c1421965404480c0c0c5000e89a8801107552a0000741004400d40c007900b64190010048c4894800754030740349035a6400403000328007030300c4500c000003140001035003a581a11442144d2840c10b00c04202840b010800901250381e0094840d000e4046900003003806403281c01641d800b61501d207003445e060821251060303011a0701d400c2c44100b240081a0380c00040514044116507401c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 980981501 1250 980980251 980980261
    0x30a03021804050c030411030c09070e0109080717100b1f0207031703011514040614040e01030503041a16320f010f02160f050f011503020a0e040309030b 67
    0x1041d40c04a20704035400500d000c081c4070003112040081c6100f184621501e0280c054040d06158a0320381503a54030390008020004502000c0c080d03078a45110740d406260040007070b5070307607120700785001c00720340c050100d0341181d00c126038811000b8000c5032415010141c0c1480618900e001090030031131002e1074818103600c451a007100b414424802040110740010042e0340d40e5144460304003040c4d10038812448070b0306600701c164203154045d28a00c0041820314100358101464042c00356000070110081c00301c005420007000c6441c40715254400c0c0a14020380056071210706150114071900790781c05440079001d0061010030350540045010300813655101030b45e40c403c0246018603008a40401c05d00d10420901034103204041c4d1000144441c121012400034030420750885034050482c801c2d600344004104401044801041d6100c41242e05607201d0030484441c3d4010030340860031588510222409c0c1060b004040007945403815860000d080d1011107102d250902d541d001c0d04841941c03200400403c61040021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 980982751 1250 980981501 980981527
    0x180605120c09090f10140a0b0120190f05250b1602061c06060e0303030f041707061506050c03161104110d0614060d020d06050406030b0415020a02030a0302 68
    0x2c0d081d410a04a6820300c40c00d0703507610080c00d5000c2d01c6c0c0b6446441317000047d210704110b0061559000042c0c4421105005050407a50400c40c0c0848040151207080e25024142c3c44002d55030340440e0190f0310000b940a0303103280060521446c4002d81c64400e00380e01c2d108114205450a140840382140700603503441a0032503d848003094000000380d401440817810001c28800b03501c5001c0f959040d0b9204101903030b12904182c80ba0349440c240c8a805038024000a440348101c44030302d540090195110003008800781c0078040c01d5610007c0211403454558003103400b8120380c0c1c4554000f419072801c1c0070307060100d5101801c0d5a4002d01412000e580c09180c44c0d20240828181181070184014000f804002500c5d0068000f99010305040e10340c00380f030040009014170640c060300e0207001000304894a0800c00039214000f03504200c0360307811003a40e1034074009220782c0d036440340f01e004600c15501040135103002d0604c031101c55025140070140500400490022581c04803c42c0d04286070340c100107880d0f0340082154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 980984001 1250 980982751 980982763
    0x403021e0715031505040c021b06040b04030c030b1509160e032a0607020603131401060e090105070c110d08071505190902030d0c08070c180605120c0909 67
    0x640203051446508602070783d450b0700020b0703405003076504a1581c00c1e900d10501c01190002c80c10700c401030700111410444840c0100e0340d20701900e0300416150519031100c48080c06035006600813617403a00e0415041042240030740c0e8141d070140100e03104a0780f1a0348000414400c940003014901500010310350444650300500422603134034405003c448900c101da403084d050000d04010703000c0c210300c88c4102c0c8142925201c0f0440342d07140c5e030140c0300d1411511000850504081c05080c103c40001d103100c884c0070080c109101340e40013840b82824241807800c1402186003112000741c424000c100d60215010041081640302d00c503590001c0d50007110201850410070030360300860030020021034440e019200c011100380c2040c3e0040003035400300440408082482800c0390703a1140e0081d01030300b03c1506000554029920303440114007902c415071400c0c100f907540140e5140365810074004c080c040b031003095416116200348805494142c0d0400081680c2864090750f40007807141803442042020001707000d07840248a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 980985251 1250 980984001 980984009
    0x90307050d020d020f0c060711010c1e0b0a0203090604110103020c0118050d0906080126010207050607080901061206020a020c091602060f0c07030f050c030a08100b030403021e07 78
    0x16903210a528100080d1611a00100d51006100d010044200c617640031600b0350a00c3c82c002d101603c1c01445a0360b03002c1c403078401840036040c41098090b001c041440c29003580c00d82104030145060303ea1042c81c18039103504d0301030402600c280c41070081101c00d403800140b9980098012075218103055840004030040d214031180b15140f5400c0c80720b034102c000280c5243c1c0341c000744a04113484204991000450f030280e2240704640014202400400508d03000748001c0c401801041d044600d015a296541030982e8840b1508548584c0460200130840e90301121031500240c090340280702c40c03850100d1620001c1c0254030060301403507002602805031402080401c0d05100050020461454190100d401306100500351401600821000031000307aa00c00e1814404e10400d82414142440c9490441d6060306202d000024008204410940181e0801c00781511840907070794000c840c500101d611420903d00e07405442d0329141401484002034010801c042c040203880c52004c90400c82070354991600c540c6070b03c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 980986501 1250 980985251 980985253
    0x203071b17040e0115030b06222301020610061d04022b0c0305040c030f021908101b02070b1e0307030b030c0a08030409020d0e061003170304110909030705 68
    0x64002030034850f0080c901d040303a01c0c0052186191a00d0301069041d00c2d006030210344d120208000c005110500c2492404007100d100c4250091180c6400c05642010350785a501e400130111812505600d40e03041040d1a0f00c04080c05c09075280b14030b4a000035144000c030300d10f8024101c0000c0e80981542d01c1e141c2c103a4241c400c2c0d0b80c1c2c2d00316420b1802d42d001e4400f1801400c042c6800c50410fa80c840d03102d0f0290080031b000f0360b401040040554615240d0760107800440e541285e02042c5a0000c5d8001e024003442c40000d440e0900160200d01c00700604a011030350007100d500c0700c0d10981c00e41c10307000707503004201c039811a100c50484950728800d120401a0074204002002410032022051220304c07641a440300c0c01f2400b0a0f400c40d21009005010014100314510800300c0786d910801060001c89003507000381c00d03420f03801d86003c14000c0e1080c07011800c104046620520240c2c3e028810828000b040c16407108012202c42c0452640c00d15840340c072402c55126144078000c1d8035540104096000400c21561680c3c0c0141c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 980987751 1250 980986501 980986507
    0x40b0d030903030906170a0902060705010f1a04090c05040c090914071419030e01090c0e0718060f182705010f061b1e061e0203071b17 59
    0x115001e0160389032400300b0b0b00054404000491080c0c041c842c4070916466103042c90a030380d0790b40c9072407030042d017010b5100b2a0070407800c4c0030342e10016100b4056030000110540c1c010910480b466450385080003424040e030b1040e418850388502007031103010140140d80341070750041080481010300b0740d1007103080c0d03010300042880c020541c2140400d4407002070041880380d4a1518015200132071500070301030382c020800c44c02ca141600f10f801d03078080d9000d540c00c80d040600208034444a03840756012800e481e40078414142e140010040304940c81036003000040a444100341c0c495084c0900100102c0810300e80900340543e0720789090a0028480c0c4000c000e10002c10300114561030300c00c40412010800101d00c450720309020020444401c1d00c2001d006490607030341c40340c50000541402450061101c1d000307480d604501500b4042042001311030b42030a500840c400314010340c10502802804040e55800d420107031051040c803146951140300000041c4411001041da0000d030704200300215510304810241c48400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 980989001 1250 980987751 980987753
    0xf160e070c1b0513090506190e0304030503030a0507090e04110a030c09021b0c130b0a03020301060b030403020d08010608011707081f0515150c03090301020f090f0111030a030b040b0d 80
    0x5002c030600b070354002c0d58060300010070f0004003000e45200d110001c1c032070f4001200280d9819101c40071124884004840030950340004492181180c0c4607800954050304000100f101510080c05031540103102c0d49003e1003030515010b05c802d807880000d8802450080003268240d681c2d1351300070503031000e1354200c40641e480540e1554007800030341c403208440021106960040002d08404141c0d813202c20300240c51140110800074401e0300410030380c0d0a80c1d40c80525284040003580317091041001400c9003600f09036503410903050180c039000b010b01c2d00c001001210801400780f0340c2d00203080703811151044562914010540111410b1583d242c02c1a0a948101c1140307809685100c800d80c500000e9144041080f6280c1ca503030305002d250f8a04030260824140008050b5280e95180107021404514003549d0521003103c0c0002d099a000070304220712001c02003241c207404d185c280740740014100c0074242400701c15550b81401d40c07030b801050394034401c0c50350701c44503401c49842d144c01400c0385120041c1403d1008241e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 980990251 1250 980989001 980989043
    0xd050f0d09080c1807030b04090c0602060402120703080a050a0318210e0f010f020a0605100e180a060b041103090f01050c0c0a0809040605040203090a050f160e070c 72
    0x850700c500d124610450040f801c2d41c1c02e181d407243c3e01d000740188090007550354545007540505242c01c60103401540e031301074030310110707904d001070801508443c0d0152046013000e00400c040a401e000442c141c58029410070000079070484122043c40d102800d01c0303521052600c0b0250001c0c100d16401294040410800c10100030601030340340604440004180c00081c0e45c400115100ca503018100d5402c00e2260300a09040e6019040e464003840080c81100d0781c164440d92544150707070b02580d60038141d98054005200030707401c001c5c6407984407446010f070410300c010a20606945e01140030340604400d0f42c0c1d000c0e00780d1584490700315404803460705001565a00300f4050b400d80c0d0b1a052010900c0d10752034100402c07288000d10080b02d01002426004001c0900107480700d0041e40d110030003e550080e40d583c00020f164a907400654860507102c00540210581802d185042022040703042c529600040c42140403000d9913006174054404d10f24090500703a40d028402e5480165000d0042c001d20300c483c44140101c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 980991501 1250 980990251 980990267
    0x3020f031005040e070602071206090c0824060105120c09061809010801090302030703052503020c011706010c061109030105100f0807061e0309170901031103010b0301050d050f0d 78
    0xb0b4103440030842c0c4d2480390b81491300c40d401401b400005130000c07201004002c10b2000303d840c51602030f5400244480c2c10b5540c040c107401e000d0f4001601500310444030340c0c00750242d81c01b01c0c840c1c0300c81c12543c0300c0c64640b220000f001d604c50f80b00e000c404083c010740030444607070600b000d448040ca070203081c45a8030703000c030100030440b03160340000319214195620000c2900c150600450a076151b05400039030404846075402e4490741c22101d103140c6101349030002c400c4005101000340c148180690080d1041e581c00000052000c0302d100c80c100760199409080c84803e07688114400121904498002000d403c1301524048038442c000e449a410740c00e0074203001440422424000441f0411064004450340d248800b980320415803007444046640c05100e04036101240104180310851032a0009000030355940d404005200100c41110305403000c01c1c81d240c103503014412844410b0f055030455065615243c01400c0c03c1c441401224010540c6d5441031b0104001040500b4a00c0c01c00410388510216960008003210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 980992751 1250 980991501 980991509
    0x30c0702040f0e0a0b04062a120c0e0613030605010b09031c020a030c05150a0203070329100228060f091a060f030f030903160e0109050703020f0310 65
    0x2440e010b80c01030001c00a11800f40d1100700754020340718000030350311142580a802001070f904940c80301c228a10381e03011a0f065401e00d800c4e2540c00415070340c260200038640f51344401090001031401d480548007541044000c184070a0880701141e40d681c1100c03181b81c031420283d000801613420200042408110080601030340f01d010740868100d142c0003100c88079288500341310840941c0101902d000440e00c684030120825004400b12480e5852003e4000600d4038221075010782c1650100601c03803100d51501400c803403d8001c0300c04070308805444002c01c442443e05000288205040318806684c60700030700451401404580100c0c420034071010903040c1d42c0014000441e061443e04000e07050b0801d076880350501c15604400410350b030240e80c1d03681800d9000060401c980c0990980c1c880303074542d0f070300f0014000c2d10404040070b5a00e0780110820303d40750200b05c10000c50b2049004a040c820b8015a0340081c0c110380f10f00c42c0c0801c107070b181d40102740e00903c2200c94003500b50200008001a0381001d41c4840111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 980994001 1250 980992751 980992759
    0x90a0f0902031e0c181206150310090827122b0c021003062c15060706020a0519081006030b03121b030a0906090e152103030c0702 57
    0x40940c1c82d10f100c01d541100e035814903080601c5000480c8030b65250705038640801601020710400a04c061514040084900c480e00400510820304c00307040a0000702040c5034801418070515402d50340c0c0240900400070b6103a1418040c020b034080780300701d22003450050040074182006082c10614155210b100e550b20499000c4410003643c564849145d0320702400c1407903680c0702d0303c00282e81d03403c0020242024117440304050316060041307580b90081d16040118290602e014507020521100b4403803011740107103606001030708101201202d807940011078880f2a4407600060341c0e00c22901056600340680d080412000e81c81d01011260302d40c200b40d00380c2c003450f0742e4221480055a079200c2181641c1207041c3d11070f0560040c103441c2c5044411403029122003c40c0001821403014103104151940e04610280d400050080c0401c1200c1c54008096102404824000311003d281045400540b1801030100c54004c080d503174060315024801d0308d001c4401035040c6055070707900d04041007160f00c50b8001d6281a485 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 980995251 1250 980994001 980994031
    0x21020301020409050c0703030c1803061e050109140108030301080a2a030c1d10060c030e04050408031905060a12050c10020601050a050d0f0602091f08071d090606090a0f090203 77
    0x346004040c040ac54880140e100e58000342141c0c1d82e0701c080c0c0003103078041180031142c03103040802c5070184c00703501e0280c041d00f080080c5126621495400841041e030040302c003034004000600c0f10540120300d004611723400054140706484442c00e1806591168010401c60f83c00005020080203104800301003200d100940f01c00c0080600144649402d80940340c12100d080414403c000d0680540c1401d48a103003e41007003000311074800c001c14140e81d400c950803110050000200002c517100d090b01d0003441c1401c4c5a01300700c0b0380340c04004070340301140c24000da082a40310003d00c0d9080050410002c90b0400011f170411818501c421000380d983c0400f03000c3d1034418400c280300030880d0300b4144100000103801c0a0502e1100c521511028000d601101c41c180c1c1181e010910028501c20b90040f01d81ca9203e1603441c0040c034a050039008080c01900c00c000c0034044403c100e1600e407540c0f503600302ea070000030072194142d440101500044e0450301941c0320301107034241c542c0001040c1d1110b80c060f6114007008081604 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 980996501 1250 980995251 980995271
    0x1104230a09022808060306011517150319080d020310050d060603031b0b160302040b0714100209090610110106090b1504060504120204060f08010504061521020301020409050c070303 79
    0x114280c04840c85d41c0c01d64003040040081c804102607a485500780740c00c014008400c4050310002c9240225030845041d408000444c00e5420100465a200700c55420300d240c0a8800e6540c4400c0d0b841520355445242d034010020519109040c40450001e000c010074060b4100520300e404801783c1690710060740131030180d00403c014898488090355110f41d2102f141c444a5943d502c00b01c080b03044116010702059824800400c5045a4100502c5464065070030110000344404850f4a020120800da0590074018064060103403200c2554a0f000001122007080402a418041764402c50300086440302d03600305000020780b0180f81e441250000c00c240c0725680e20720408a01d14183e40b0451040d00009001004108124402d464403094001e20052011481598501c045030945a56402190f240e0f5564002d100c01c011543c0b0940d0000905c1d0069030b100b031480d0028506944100840503d44401c01000d00411540d003903045401520151000300f006040446806503030b0740000d0030440c00301b850301d1107070b10f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 980997751 1250 980996501 980996507
    0x10e06041403281e081201030618110d030c0b010f030302060603060411091302090403120c1103040b0d090f05030304150b0f150c010c0806041104230a090228 69
    0x140f60480b035405182e140e4000d0355924956820701c03040702c031140303440250500006841c00c4014009034120000e411219415800c1040072501700010703c050700d0010002401c000b502c06180c84d800340004840c8078078401e02e00c0c1400e0782c4090190400801844000001003a1440c8a230404c83c1540e0003a8202c0395240da0350000e040d50b444040d5005094031801c06405540f03403603e20040b6910805009183d1001c44c4940d0114400341000d0741c085005c40c100e5004905a41141d1280382c09101b614600403021103078010440d80c40f40320354012440703454000111500d03c501d0f550845800e169201c051450740f40b410303003040394503034009071811111180c080180c507005401c3c5008440f0304a5000b003082c0c039620341d12410013092040041c0140c2d000502400255403449083c440d2168104030340c0c0700d42842d8030340601040202da80741d074000c3d00030300405e0000b4010046604808959541500c0c1c81810035081400003c02155079940014482400060303482c010111401c041001d80c5601d800c40c940c808140c500036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 980999001 1250 980997751 980997793
    0x20d0203040b07021c050303070207230a0e070c20010f090e0a180221060915160203041a090910141009090e07030528030509010e06041403 61
    0x2040028240b0080000d440c0910380918080451702038241075107403556030b190640d003084038101c0158201c0c2400f0400c0d100107090800f0102e02c0c000303598050b074101c01c0c00954080030b02e0040007401550700d0009649940a040141036050700807a007841505004038044011a0b0300c101540d00040d81c80592078003050203400302c81c044d1440300c0f1040c2500d540741c4031480300030400f08015000e0146e0235445080036072144103c0310303030744403010000d4007815000455461400302d01501e0071407540d01c241d40c00481c1820038062241c00c8080f92101c4041c109180c401240703540501d400c1140f0181e19105042410001030004010b08002603845d158107a880440b10b80d052a0580310381989808500050800e0345486580c0524040d45400c1940341d41b81c80d000c0e680200c5130f40c0110f80d0060350003040c00303105210741044002d089072200802403081c1004c1a04c0140e60350180c44009083c44804600050780fa8041c401d100303d4008060306094440b5565103003c0540c80c40c3c0080c0e207000e8000e2204d039074807011404c10302d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 981000251 1250 980999001 980999009
    0xa0c0c02180630070803090a17100c181a09060d271406040201090b07060e03120103110d0506180106090905030307110a020d140328020d020304 63
    0xc00a241a401d0039005004500820403076114003400e83d06040d041422002001800d41e4451004041002250a9280c19015003250020360b100340300031003c658541d084001551400c01a05981e1030b0500d04403454421070011010384142441c0001c41c4060380021842a4041410000480c10381c0c6d4400000441101c50464692a075041001e00300c0750801d10007c1c2a442d8811000146650104800382c8071000481c1c0e20a02501100d100c81c001d00c01e22030700e034008040c00a805004036042990002c0c000009038403501c0c02c240340200f0003000784041079010300c0324030217180145da541d00428028084124001d020071140d182c1444d44108460904251441e91154030100500e6640c03150046c150a04900c0120b01030030f1341d200c820101d14030420b400f4001000744200001c5031a07041207c0083d11420402010080756404044158007590340e6010070000c0c181c01580c402c5402e40080605802e601ca080030001d16105200a000141d080400d00c130180c01c8070f1542619203488000104980724800e0f882 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 981001501 1250 981000251 981000259
    0x4030203060103170c0706020f0106051503010302090c1c0912080906010b0c070305100b041d060a09021813060c050405010905040c180603050603060a09030f0305100506040b030a0c0c02 81
    0x10700005004007414504050003984003400d00180344440d17490486c254110070016040b6405002218000f40075002c0640000c94401c04042c410501c039158a0005110191003065080c0209001350b1030103045400002d050000c1c801004001c034225006491b03050421104941d140c0c01541e04a1307c5082e146011742e00e03100180c601a460705e0102d0b805a0001c000d808640c1c0158440000014010803403075442c0e40d6078a5021529035078010400c002c50f4445140e0150300800407114070803c80010610300d5010001400014013000740d4000300d01f5101c0000c440c0b403c0c0300300d801c0034015007007241302e00404403920912003801b003000c1c0403400300e460f80558030441c0d001c2040b00c03400748140d20309a0040741848000745407010b02c0c1030011040784401d0080c0c0d0f004034003103a61030060201030b040a1002e194003050201060006083d180c1e0020403007480045803400301559680840e1005009400040060000800c0980c0351a101c0c0c602d0b0466a00035150010030500e40880320a8880c011849114481c1d0024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 981002751 1250 981001501 981001513
    0x61806060e0d05190311010e060109150608071206050607030503090c0f1008040807060204120318061b1703180c0405040503041e1e0e060904080f0903070b03070305061504030203 78
    0x811001c500e0201141203040c04100721012070054024230410b45880460001018294549040e0404407003a58102c00c51006030480180302c801d400c11460f0f90000316514081c2c0200c54941d00b14001424190000c5602030030001d0b81c44140740c1c0c0440503502071a10b00055075604003030081040303a0b9074910002c40e50401113242280c0c064a00403843d40da4040e0040c0b2001d8540195580c400d412644a42c110b0011080100003103801c3c035600c1049000c00d44491000c10380007a00f402030107003180034204040055a11110442c00c00c010040d0783d40901c3d4510650119141d0070040d880003c04854003100c4240d61140c101c030000c061526018060285410801440c90704c0c0c00d05034110407240c000c101001038130100c00c0000500da20400e0b0014040c3e403903c4203400c10301d401c0c0700103c841600d01902d8a44540d0416007031001042500c070440328a01110070388103590b2001100071904203000c5a1003e880010080200417040e038040d000148100c9046482c400a1103130310041495a016a0001a41542c028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 981004001 1250 981002751 981002773
    0x20a0902250c03170705030904180b0907180204031a06010908071d011401080a0b2b060b060a0e0607060b030d0f02060603030406050702060d061806060e0d05 69
    0x5580208900342040000364010045006800201c04126030219a03284502e0800c01c00d001c0c0d0300d00480080001c40c9030b0b4500c1c020040c0c65043e900d00810074902d118643c0c4440103a007006c50051100e40050f4005450703119443c2c505149525980a0f10681c692903540140c0c001c01611603100f11010750707901040040c00480f0009071220f1841d40148028140800b1442c0031442580c10071034507000b00b411621204100251100210300404181e012801d44c1c45d0a011002183e80c1204041d540306c2c0c1040c01c00100490b041e40040d0214042100300c05111107003040c442006500c0d411107140e01c0d03001e40313400d009140904051100520841440300e00148070001d10380b005150100040c40410700807203000c16407000ca04002030506440c881068041032000041c03107075454061140d90f6000104a001c0d6040c2407070441c024100d8420424024415a80018141d1a8140943c412405404000610009085020300c40d40003000740b0300903500400c1c4400036007029440c151540c401d0303240d8010b0241c50400a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 981005251 1250 981004001 981004019
    0x180b0306060c0601032603150d2301151d0403120f020a021e0601260304090e0f0f0105070c0b0a0f020a120516020a0308091c090302010813020a 63
    0x2000e8006544070300200b00101d41c402c420015180a0360140f020704070304080c10f03030031071007025002891312007121014010480003140744441036509010544009500f41d803686030802e82001005010604142040002c9080003015481401c11550b04854040d80035111604e1000005001c00e81462252541c1e00040c0082c2c8111a40400d115407a04040740c0d000c4800528003c0c0d81105021000680c0200a1410100e083d07003010b01800c3e0b00c510242170554100010361404031510403180d90f04411804903090512010012500203180d4040200214414043d0a03030711780f81041c1c4010458031810400e06124041071142c140600c040d6250b1028609003540c5d1b03003601b9031005040b107008964a584030060400a0700040c4001045980c90460a000c1040000d0480f2406419030f550250006401034003940c002500080072601800c009415946480e01c40703280c402e4410601032003c9500304120703406a004072041060300d02c01d0301e41c041d490790703031000307020303a0014090000e980b00c524114100b041c3e500b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 981006501 1250 981005251 981005257
    0x32a23180f031b10030204030b040f030810030c06030209032103181b010c06090611130902190c140a030c1202030c0a030503090c06030405060a183c0309080d180b 71
    0x4c1c031402c0150406a407900d440c240e4002c103d4060760031ba10040a4201050b9102540c07039070110845c4401282142951102d44442d170082c018079080c1540001c4c82030480e6020070180d203400031604d181c0d520b4070b4101000c0c594503810589401240070251381c0c00d1042d040c2c0115110508a125040c080400e02c0d10400460750010164000d58406070303907070713105000f05075140110714121901450307140d80d45070440100c01c040c0d10183d0059090301c0c414091001c5907800d00310000050062131412100341c0000d810844840c1100e0001e54000340303d408100002c0503080040c03880580c0c0581e5140460440c0c0ca041640c0328032a04608840c26000358000200203030040e0095034001754910110707490300140c1070200700180d1090714260b850703500810400c9100242030003052484001a03000403018196030340d4084142041c000c07541c80c0a03901e40d10b003022040c19410344c031b00390326001c445491492401d0b06001d0101c1146019444450080c6201c5001545c003800b940c6c51f050850f0030441c03404501d051040011a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 981007751 1250 981006501 981006529
    0x60108060d061406031006060c06050604151d07030c051b0304092d0b060403081606050403050a08010509060d11120f0d032a23180f031b 60
    0x10a80200760300440c405215030b038003401c0401c001ea506410320760101450318039201c101101113030621000388181540300c0c585202d00e590261000c03072652074010005e0b000d00050911105a00610400003411099400c1940440c1d0305480704062562207940b01141692801030031030022400420007014520641550192100c0340798050b0380c1080e445070b6501040c1c591902c1515103082d041d04030805405204900182d80c2c680c02c000402440f1411004126a8007651001401040c408101916100c0e000a03500754400c7e407140c010072a6103032919012701175402041d480400120040c0010a16003041160f990003041e0003807903426000219079841e034414811800f00c50300100e0f103101e680710b00103040000302800c1d00302d6400741101c04c1d403401c001421181030070007808907403401084840302c868940007030481d109098034001401003200030300031807810200343e4002d41d041400900304804030040344071400a020115041001174581c402090769075946466192140344180e601c0b0a40c910700084004414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 981009001 1250 981007751 981007759
    0x117060406030b10231c050f03030f0f090a110409060b030a03030e0f0a021e012d1205090303131b031101030b030f0703151515030c020307050606010806 67
    0x2d480343d4406020b0201502c01030402c072081c0500b0320113903000d0083c00610030920701c1c080048160560015803d20840d2100340342220625a080040c04420302098101405003000c481d030300d003428110400120411181c103900009004081030314000c000c42c440c80810703042242c89100e00703a00410000100f6814804403201075641030400d2050b1000d0100c9600280252400118003a0421110703040050210152030940c1101d0043c60040e40c0d40b5494500040d5070041222000500400580e6100d500c40b1003c01d1404480e0350300034200c0c01142c00c0400d0800d866035141108000550130700162a0280c3d45000c00340c100b07000040c0141d0447c41c0e0140403500030803070361481c0e003008803054003482600e070000c1c0d5056498024103182540c06000e6540100c1b0b003170f0000c1c034000040040c0c082d110700003800000c01e015542200c0d10982c20035a001320410354502185c0029455032000030100382070f1280314060110f0b0030140d545030060300201c243c40d12a6000405040140e880d00011540754030010400d42d48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 981010251 1250 981009001 981009011
    0x705040216061409301c02270d0f02060c010212090f010c0906120b01021c030b030c06040b030403112b140301080d03020304050a051f0e010b01170604 66
    0x70492500821141c48450443c1d00300e281482d00c80d90f4103050040350800c200c00071501141c2e600390101004d25841802e4036480c02d0300d443d02000c2460300c001d41d00b420140070600218221203941c014100c0380c01100084c00788040508040414050200d012960140285c40000310b10b4000d4105503000f0819040600c0c001450650307112118000d0941c2030780d107031005a00098050502c404248290180e603911030030301400761482c002c0f0041100d20310142da8407010343c5500c4246040e900130086e11810f414200100035480640203001001041000d103550301c41c0c40380418854090525030210382c15146401c151900d0b46c1d8442d101501c8081c64041400281c0c410040d00b081510b0320041442460651108a1a081c040980004126480b40208035214110030001000010000600041181c4290401588a50f118108113082c60199403000d0250f00980140012444801c484c04580721000c035802c0006140c0c1840c0c0030700b01e8106071010b502060800d000810212081c510700b07948501f0090000c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 981011501 1250 981010251 981010253
    0x6020d060e041a090102071709011e02030c0c0f10050703050f0301030b06130e03160f060c02070501091a0403110f031c0f1d06031f0b1b0a02030705040216 68
    0x100d0720070110740030b84140c0044030503081400b00305002c080e0405850b00c002c0d800d1108540f03132174901a019828000c803121000031442c1c86030b4001c288a96480c1500c1c251075410843c0c0643c0a5241e500c00807100100e0300541c15140a00d18100ca0050a0103070042c110b00c11150001c2c0054410f54400c070429030078410b0520001800f44100d034000c0d40658445d00205a49003010410700111030342d07000e44005800c4c01e00501c40c00c4e6200000548588003111070f4050103070501800e0a403040e17001040044d0031182050034058000340c0000308282203501c00e988078801c0b0359807515211840710b0800c00c0c040c1d4000c5c04210400100b928155451520703100140910201e0140a0000340f13840428441d003210242d43e10316080a5640080e02618022190b04241414221410b028201007014a0f401e502c00d15001c0041640c0014004c240405201a07000c11103070140c513503c501c141904040c039107012424410020303107031b80c80d40070420250003036010f40181212400c110800000e500500c2e455004020340008202c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 981012751 1250 981011501 981011519
    0x15040306093807020c1f1b0b18061911040506190e01090503060f07020f0f070e06060a1b0501020d09061401120b0c071115030f1803040306020d06 64
    0x18400000c00c1444140984510b01c1c500740040000e0405056420490507124291107512401c40350080d8020762111111404031305803101c2400303040303284617809001101003c000420314124004e4072035030092064034100f28031496807580e08a840b450901440340c085c50743c0301000d800600c07080704008110703402c064a54021a400ba04601c6462042007909840300d4103290304060303482044034007031070901802030a00d0046a41c810010300484003203500c440025007070034070034000442601c072080e0584a040d41c04080c55551100a800b55003120302040e008118039182c1081281c05041580c4c40d00140b82a120642c0408061b443d44140d41e555020040100c540f0407a2180c1035034203106030340c00111900b22007034504074404141c002c0d442428540d9403140124801240ba640d00c0a200c918035640c90503545004030f50040c40d50000c0b170f0056070080130340f0b080f0311040018500c201880100e00ea45551001d8541c0c4900007101034040442c0c00810040c0007043d201d07001088000740030080454043e0b9194090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 981014001 1250 981012751 981012803
    0x5010b121018150b040b040b0310030f051c02030702010c061503140717010c0c0215210702010c0801050f120307050d050426030405040513022d1504030609 68
    0x42d688940e81c80403640c1d02000f01c0750f5090040d0440125080c14030b410003a500340513102c0c90099a2150501000240900c2c1003496500c1c01b650380642c10280a9816260556540c41c40e44c0350980b1103c000307466204000c5c8000165020103405079140c1a4004403506ca004c000c00310854092040884c412010000c00d81d4000040a081d02000003801e40703c0c075004000c3c444107a565041c84190741410b001103461b80d44180c0350111103804840d5004074001c500b82188840c4030390801c80f01180749500c00d9490260713082c20244c0c0300e40c1958000f070041c0722801c4e4003261440300074010690700440b00d450031125814140590243d078041c4070100c1e4030740300c00754585619000180245800040002509015040821002d0500103800b00118000e00300c2060b4526217070702482c000c03207010310342c0c130400a0030001c0003e40140085d9000382040c1c071044014290038442c0750020300045106070180d4000211030401042405041c4151420303242001d041da80c4400117024000b005490b0040082d203401c400740108030b0a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 981015251 1250 981014001 981014039
    0x230c030d020c0418020a060315090608010506010e0613060503090a05010905281104050c0f270a030b01090504030507050610092003130215040608040b060405010b1210 73
    0x801142d01410304101c155007980c0c00d43c2010071282059a070060326801402c0003691043d0a02003140c64001c15001443d07426a400020180d0404400140004040d4011801003d00780d03504d0360103501c10303404d11210b4030540544034544000400c0400200c2e108001554000c2107500594031106480e8880c2c5094481d0365000340c41d29004070485440071002000309003030b030062641c80c40110154a4982c00405298980c0e00c900681e211030004102d40c81c003208035500c00c142c0065507a100e00740221131650394182209280d1250a0700c43c100105d5280094a81d42126806844e801060307003800302c0c07031002d0700015104906104c010302115001443c20311030b852103408480b81d42400d55140a4408003610340070310f24007081009010082c240e018100c400c03254840d514040e01b0105412502c017088140d4440b4420b00e40c80c0c20080740c003190712640f2141040c002c5000d0030f9609130648803d01008100c400a100340403505404200c00502c2d1419020300940c080d407103c8014000707594030f16070b48083d030225040d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 981016501 1250 981015251 981015253
    0x11a0d200403060b2704030f09030f0b06010e030c2b17120f060d12140a0504050a0e090a03080a1e020307020120030c07110d230109230c030d02 63
    0x81344207650601c408819110a5000d20f005600c00605000400303411000c0c00160410036205400c40d134560060380340c3c00043d94455a41d503009812030418a5002030309840c0c1c02c0c0004c1c03550224445078900040c2c2c0f465060f40050403402070508007910450203038250035407081c4c00040b4000c0340020413043c1c0f00c115002c2055861007035071907011003081c45050400a094042640c01d08003400500c2d1904604030048662044500e043e540c05c4c2c043c29500e80c440e0303841003c0d0950001600020380c65105018000300c6205441300b04105445581210b840c0e07a0460b4088502e40c4948002c2e004070780b007140e0242d0490503034403000680741681e142c91100801004070244040c0d4000007070020240e8244180b244001da00b00c20301d0706405480550002600c00603019424a55000c602c031410320580b61313200c02140400034201010002e40d4644103a4501c0f0400d101d0101000e1a8465480071006005049800341c1c420402c2007100b04c1131007a0407402540080c0c1e00003e1055546a82d503a07182000346108150490b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981017751 1250 981016501 981016511
    0x160e0906010b07050718020d0c021e06010e0a051b0408031312030c030819051003030306080304080c01030f1b030905060604110306090901090f0c0806011a0d20040306 73
    0x108014542081a84034000c5010200030600104501140f19030030340f0580f400200b680800207103d4400b0703000c0c0c401d0380e080380e5240c0400d0b205500d0700003440d500c4910110240b020f848154510040d165a0240b044061810000002a07400d0403a503102c01d51182c056103511200c201d02064421064020381c2000000da840011b03084d03103050151a01e88000e060303003090001c540d2000d0b90010300e107018140c3c5c02000d100742440411060388560700d507e04407841c20001080b040ca0031485150080d06a448154040792a28502203020b07840441120207071243d10000b401c404020500440080580d00c007103492181e55051866a80c24101c06850307070011403a5404124031015080c450b0500381c0141c90b03540328615110004002600003030903298002c1048407880350680d68080704a02402c07441c4c1d001010303807000120076020020701d26583c40954081c3c1044a44aa032250036101044407000c100d0361080d03100f80480c5502100e55085072601070f031071030707105136102c0401c861106c905d401c190000c03a4950389503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 981019001 1250 981017751 981017761
    0x601200102120c0705030a0c0804050d05011406091014180a02190201061505131205030a0e010305010e161806050c010b0d02010804020607030c080315040e06090618160e 74
    0x40b600c0e0030050061859181542e280c3e80c0a070713a480394030aa4007e1141e007403e804144121501594000c240c0a0a10085c6121f83d00e800707402400140e0172000b800c030581020a01500b81004074501c00d110403900c1081d002d042000400010341c1290440d584000c01403108081002c05480140c019a070010002d621b682c042e083c1129100c503286e1000003160316000c020810050030040800c03185070f440c01c01e250b0355040c07100c1c100c506c01d240c0c1d0005001c0c1c2c44860304a000300a400001484140c0441ea16060b6000b000801107095640c2841210300038280040440c807c0412041004100d030100d003000d948040408100e0100d034a8142e00a401084010581c14842c500c00c0c003030800f00c210300300e480340403211455001800c443c4006d04040c0c050790000c6914030800d0b00a8003a07075039031034011000da516498003516050341c1a00002041c1d01450601c0c01c0c400324845c001079400d00861540020340341c80d0390f42068504200c0010401c944c3e95110343c84c00030360000103110300c05002d09000c4050340128541 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 981020251 1250 981019001 981019027
    0x41e08090d0b01053313030204020406020706120506060403110303131512020f16080c030f0d0c020d0c032312040b06061314040f051e010503190b0601200102 69
    0x61500038008082040c10311285214101001c101d400c3c0c17140c11351034060f94846000600450380009411920004010400540000b150000c6a20b02d907910703030a1400100c558015120260380c1141c01920501007070000850603000320700b4000c0080c0407281020b52a0940710320310400c43d4055034210030400e01398802154010740c00c043c07100c48030700c0540c6401284031000d49503103d00307650100c00b1507625101d9020003101e04102d4a40c264070400303d030748960005941c1c40040e0311040100d1035091a0600900c0380340c0c004a03c0c981600540d8684400303100090310203450305501000c3c0491b0341080300003840c41000780300004d000891010007000c54945014030b02850507010280c411403048401b4018407181d5416041d819055841401a91010700d03036180110700905160314a0003c2c49003403804200c80d19040211601c0480c04040d07810003e44d907120180b54030f07614085c0140da16540382810714004141d1800c40c1c0c0d40c00100615104070200d2046140c900712403074046240000342d40008110840c09a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 981021501 1250 981020251 981020269
    0x111804050c09030714040e0d080702010c090503030724020f091819022116030515210a050a0f1b050901091e0c210203041e08090d0b0105 60
    0x1d49020742480d081c180c0b80040da8512043c42040c1541c071400c0341c5c646180d04c031500150265001c0f0720440b49029804003000c0e044070f9045540000540c6000080d80c3c0c1d6910815000d0201c2e140900a18a403c0c00781e215140c40c600c14107000e480442150a246005805902c028008400040041c5444111107000c00c011801d50a14000046003424140031030719800219071400452000380050396600480d1070000412840b04400c51200390301d40800000340c28040845041c41c182d07990801165a07804000408c64201300d10503030300000807014622b144101180154845040402161504946076581e00d01e011105041150009585100070007003002c00031140c0d079410107400c1402c80d0349090030702007400c4100503c5031007012500c076680012030a080d01110303c4540b101140074450503a0040300944000c01801020b24500034081c140e41171200070344242c900955024240404203c21810042c2410707480b0002503407013102c00c200c001100d40c1e07200105000d152240051180c158984810002689 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 981022751 1250 981021501 981021511
    0xe0301090b0109060e0f101211040606080609070201051012050c360903070b150916022b050f0412060b0f0301090308160c0203070b030a1b02031206010311180405 71
    0x251541d0301f807003401122103407440c060303a0026032805044030316400c041007203080c03424071150480e150081c0030550560081030244501000e940c80003003901c44040480c2200c10465103040e500702200018850440192180ba00c2c15006d0011588407951036400505502c1d0101500381100212002c0c1b9150803403003050034000c4c022450042a81840e00041c1c460300e0f841803000042c81302e0002c01c0003414041c122503452600000190001c91185001e01800401c0d01140d0b00580262081003061103040381d50038140803545200c80d0104285001050054420740c001d01c103155a1110706100c04240328682600c03402409004900110b640c8184909201054840000441c080d074100880f004c0441d4112801c80c0c2c0150946e21008180508800c5c201e078014a0240e0003507041c06410000500c1d40300c06000345010301e040c0c1100b00819524000c02520305880d4411141c0580c009000781004600350520300d0f40d00400604010540c142204040d64199026000320a005a800901440f040c01c0c948146580702c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 981024001 1250 981022751 981022771
    0x605030d0c02040b06040806041101032007021e0603070302130603112a0f060103050c06120a0b0a030c0e1f0b0702220905071a190e0301090b0109060e 66
    0x3003a8040402010400c4550002e40204d869014031a01d907110758040b1002407d07642c007554080e050600d418116200e840f18424002824006025917000c0303480c800c1c1c1d40407850042c410b031078000e56909014101213a4614000038030011000184103132a07013802144942c00c650350060355420300840b4840c020009420000c1003518002403001030100d0300e0b040341d40d605054004002102c3e0711428016149040780040c219038080c180704000d8905000800758160703842041600c48190150003400424010800410310090b031090100f9200e0140f603003c42203034640030707041d224220f440c0d44582041e009240d10060010400070300b0482c01d20799041000311030f0480d0261035207120780340c074050306007a00030140041d1161000582c0307030701104d0780144400c0110340c204200384011925420015156030040c400c00760402c50103c801d00c0d072a060842180c0000345018a003652a080810342103444100e406002c2d90103668079000383c40031801540406000340240807020403013900340382a020f0b04c040040d00c12565 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 981025251 1250 981024001 981024013
    0x91e0c0809060c030132130b130e0a031b0203120304051005090c13021201151101020c1504050a170c0f010b10030203071704060204050916021c121e060503 68
    0xd0304010610311070400250b40e05004c1807510310b014001800c44a0120307136401f6108100451034600035401900a4900403210440c0b10100c2c02c00c0701c1c003655410007203007015030807408401c0c00007030040d070350380c00302903400d00c1c41801e140801e9002c44d01d080020114001c5401c00070041000300300c820032620301d00792081c000c24082c070700b0b100340842d03035421052680074030642d001c00040340030800550540c1c150f51107804c140700307095a51b000c0d448004405c40c000380000650071206234650000500840300340b0500305008006004040780f002d100c80c1b01c090411a1507019003400500491070007480c610407203503801d00791035940420080d817a10341500f10300700303007040d0f414452255820b03611040b05280c258030906001da40c0742e440c40b070100c645013021140070808141c418140424026654058011f03200140c2d95041c0c50744404040c00c0c00782140440c11b000590084000f82c20400900101c800702c400381d4108940031040c1c58480c0c1c81604c0700c01d504510688000c50740202c0049540c09010020a0b0507030141107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 981026501 1250 981025251 981025259
    0x1605030c010905270c0d0b0303041223010f15061403040816140c03010b1203030403230d05090d050a050a03050907030c1211030c0604091e0c0809060c0301 68
    0x100040181c8501407040000d22404600f40300040024000031340d08540c1a851841c0c0f100d6040104d401a218405040f494406614076604001088500f0b0303625100504021603400c1c0d0701c11080c81e1107014140a4020452040d0440340424055940d080ca2103803000310f0007808a0010b0f61f0160200d622003800c120900b5a40304009501004030790300503030880d14650340c603000d82440502d10100400c00400c02034541e10550041c00000c9800011104110000c0c01001801300c100300410b4401241c81c0400d800c2007000c1000a4001c10130003c0d401c11000c404000790211001803106608101000000c80b038845e8100034281900740446d502125180c00e0a9040c5115401d004115025000c5042c080c07594440214001d42010401803000b1030b4814034018009885030102c403c2c0c484412011200161010038038903091802045603901082e000d0003030350071700385400d00c010041c0202c00c120361072014a500c1c8101840407a8003510143c5c44013500c0304051420f0118401d86001001000010b420380140010300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 981027751 1250 981026501 981026507
    0x1e060913110409170a1b0c0509040309090e030a03050a0e0c09221211070b180607080a0201050115020303040c0b0306040f1d011427030c030403051605030c01 69
    0x301886822654041207041d18201140090500c0f0202070504000c0342140c03900700036a000102005400e90b614020140c5c5054244e41b000a4031980062000c0c054010a20203410000f0321180e2141c0280307400c41a113030340d81141e01c3c101c520541421140c1d8200246e0800100d0305030240d00d800022452003044071004c160403507074560720707546041446211000c0200f929480d00120344600f040088e044a40d14440310b10b0401404c0302c03000c030404007207850704581c00b03041e11002ca23401040351125608035141071a80c150f0320390031160085a2039403018080c00803502180b2501c1c0a03100400280c0c0000609504100720520b14518103068142194402c00c10030000650140004040701c00c0ca00015403030b41c030f600300082c0250582890300410245440c040c000c41410321039106410b0102c0000030010070700c1c200c0e410b400206085985000383c000801c0c1c0e4141800b8214004505c099403a42920300784826903131460306541c010b510079219540300c0300f01004448108040000200021001404072441041c00a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 981029001 1250 981027751 981027781
    0x20f070f0504050417210106081003080f0d020f0405090f04170304020d120201140105040207050c09040f05070b0301231311130b0d050109020f19090902031e0609 71
    0x14020b035100c0700840d0800034105482c1000543c200f01e407903150408142103402d1440030041c2e000c4000e11510001074910b004060b0705002d80d04000180d02d84c14196210f82241d0360002140c80c080500400481c2046400c51005c0d045800410640c1a9110f24101c100034a0f0200a084100c44100c1002030200040d0f65050201e0f010158001480c1c5907940c50000402a82305500041c00020380c3c0347c602d0518036810b61184192017100d42044015036240c0090104a02508070000c00c240e110f07150404d42454107102e03943c4d000c0e1051281250080b450350364141407074030580c801040d010000c001407143da02c48024240081c01c0030090b001001841d00002514803054022a245aa5840304000d1030304070030b04216480c07400382c06080a80140c0d03642c1e00d0100ca074030040710f0b00621172a040012400a503d4000c030b0360644140c10342039041c041f0758031b2660400f40112603000c00380840d421001030b2504070341c00950f01c58400700c2003101d80c1c0c110080840e4150700004001c28815400d880c10846d591100002c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 981030251 1250 981029001 981029009
    0x306100c0614090c0a151205041b030c0812130302063414071a161509140a0b0a0f09060e0a03180b0304060c0219030f020f070f 56
    0x5841101140c1c2000401805103941c18036407150502d04120710311400007061150482e0076648000942c3e6608003d604a0320881c03040400078806141d90b08020040d60001500139004000c610480c400740303010f50180020a03401200e400da0f40c5142000044070034000c2c001d40c0549861002e181c020180c9000002c00c1641c0002480f420307004c549480504c89004c001222655000c07950080b44000800800712a01203000c01c4034640c402204603505140041075580c02c41c0e111540ca266002010008000140c2004050710800d4260f00a04800710304015420314462401000000c0c52a80b14204550306080d10315420141360b0000b445540060242c20030079902000a02c000113111442c006100e000d091901d002404541c20200e401c1d00028000c90707a8030003076109458403a18122141074680781c40400e84131b64134082e04140001804100b00760000301c2c207030038144181d03031461103140f0b402c540b001c101170021b4001545a00b00c81860315010000d40c00040b50340c100801c5c03068a01859446066410f000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 981031501 1250 981030251 981030257
    0x106020303280e12090a0603062301350702030703091712030a0204060801120804090504060b09091006060504081906090506012405120a0c110a03170903030610 70
    0x1091088140c0550f000d010200002c40603105000300c4c012080c01c081e003108145612031036580c1000201c01d0b00038422007040b40d0302007078180300c1165006a641d20095940d0003460600c02030502d00704401c030000490303011055034507581c8404401c00001024199a00400410035944208180b10209400040b40e030204d40100520b801d80000f114610b0381000080d001c3d04554034404814010849265000f81081d00c5155540000c1a81c8c1c54244400c940c4410b94080d051034410001402192241d4110070340c0607009a401050540d42078000c1408100d04903034201d229000300e81d02950380f40f100e01802006152a1502c0c504107424035185a0b04e070010000f80054099403080d40d01c040210315000741110581203400d0342c0c12983d6036880d002641e15284040f41d82c0014007000c0c0c0c1e4449014400740d410100d1b9001240555940f07500b483c000800015800f40240400c074986a51440c404110540556120307544000100154050b150b4050340084c02a492a0304180704210301c9880b41c6201c5003024810346 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 981032751 1250 981031501 981031561
    0x11040506030f0106170607020c060319060b1819080c011101200301290313020307030503030108030a0306080d0e0d1401020a0e030c0f0901050409080d1b080106020303 73
    0x400080e01c1c100300d8090042c1994200b15000500c07001076108442e02950001c01d84210ba41d8154080741c603420300d82c1d20303d03a11600a20104803025052a4140d41102403101d002854580380d141818030381d0040c50420b41c921103da2901d006070b00b010301d2010b03140340c1e81c6000302c541d9504080e240764807141038081c0141088000110144490001d4000401c9090f548114401c40007007010b0400040d40300f4003c0c05900200c03602c210302100f80185107a40e0070004841c10f14255107425038886500071819005a03458410800701101040e0240000e500034102c00004565800f014203000c0c0644030030b0303030001283c0d030030213000c407003446030446890144524112801c5a0f054030310302e400c400c0ea107940418008150f101180740f00c0c045401c90940c251400c001c038210340040000074104100001041c2c115a0002c000c0c0004005904042c3c00c841c468903c500c0200d4100100207540394100d030146450a1a080c0c0d81075400c8000c07030341102c03900d809040584082c5185140082c01c3e02910070340f106003502c20440b10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 981034001 1250 981032751 981032761
    0xf01140d0b04021317060906090c120115082d0706050306271b090d03030b0a0b0d14010e010e0c030403200d1d0f0609040612080a0219110405 62
    0x507411950303000030100401d2035050f1515640302015034a03070b41c905c2542c45404085201302d800016070a100d0a0b10900074060840780b10107214241e9100440c650880d0340342c80e20340c140074000d02e19410141003580001d162030741031812a004104801d444000071154201c64244c401c100100b0740d042910500e092090b44c035280c0e900800c11525914042215100700009515413124011414034010a0700100b128442880c03c866482c483c07081550a5500400c2c00e15601c0000340240c02400620070001c2403540401d980740301c80e28065101c42010121036584804102840d044401d0103805001d00018100440d030414408095080e030140c61801071000c044001020503205201c15504040c20203004220400070030000b680d07a0001d02c41c0c4901141840d840c40c01d50841d4285139480c01c4400a1107005103510280070701803c0c0d40150f07103054210781c03500e4021681c00307600b225040b5080c1c0320701c04455031050745003070003800c0a0a102d40107050101c2c01076400003050061480c00c038002d208540c00103590b161 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 981035251 1250 981034001 981034009
    0xd0c05070905070c301b11040213090b15040f17010f0e011a1207060c080f0a020706030513020a0510020106080d03090614010b040b0c240103020f01140d0b 68
    0x2d02080180203010115841d01c2400745481c0d4201034456040c0b503000c2c11151508155060300f4408080c00383e2241c06c0190390301040c4444a50780388144054001071030200e8805425000903960f070045100703e500d50081800d01d00f072521440050b801038940140c00c10381400c0d400c2c40725242511a49080b0040d000c0100c21282c8290b20800980c44814000c0020515201490303018119401c0e9640741c9000603a41c5c41000c0c00c007203041c1d91001e1644006445500e003082800c1d520b04200403015520790345c0c05d00210b00f000b00088000c1840d8040c9800422001d442c1000040c2643d0008114000801d070400c03044006032241300c0c440003516401c5440208a00b4034100803401000075034082400c0b07125045601100d590183d0080700c0080c01154284000b180c040d60b09201050288900007078000c0c00c01080000c000b05401030303d1041141c90030340b09020304039940c0464004100c44003c1d030101c800e500410840c0b44c00c42e2400707103010013801d040e00e0a0021426800490042141c80c2c001103880d8010343d2240c3d9031b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 981036501 1250 981035251 981035267
    0x120610030b06151c0f0c03060501030e011406040c1b032118060c02030d05010b2a0303041118040b1024051e040312080c0c06040f02010c02030102030411030d0c0507090507 75
    0x5c1c0300d07030410400c500f0700e000501a2145104132404249400c080a60b400010b008842c0e02045601804045464480c1800010030214480c01c040041da88003a0012042e0000aa05054025078030181e40409030000440c0410003032000030482490618414498032803074201000d108c0d000400091500315051080c1d040d440388060900c0154901000410f84800d080041d005841c02c0418080c03502c1400b01050350310f0390030742042281903442400000d00054550741c0c61a2500c102900940040324071004400c0f048509940c101c032142c000c28104000780c46001e01d040c0040002e05d20a000004110003080d0f030487e940001c6c68100600000c600d0034814240c00c800d00341107808003d450f40e07507980741054400c6070702541094000416400c0401c0301c504098060300d02c51030611000c1d240f141c440355201240c2c2010b14a04134140081c003812000940d400b031001c2d5209901900074903400520041c00c0605003241c0f28003010501800800c85408a6000500881610000b40c40003443c1e403610074003946c00306 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 981037751 1250 981036501 981036521
    0x81c050309071a040803030f0a0b1c17040e0a0b03010f0b06090d050102041206060317040513020705010908070605061f0504060503180a080a0e04020715050402120610030b06151c 78
    0x48000400e1001c2c000010382002c0c450709c68000c040080d1103441e41001024800d507913000304004411101400895040c001c04c00a22813450042450301e662000514102038040b0360801011f592504908500d041c2070082411420103e001008000340700c900140f09401280382060003207115440d980200306c025411580070f82030040001e54098003900c0d100b0041d006900045407511101c0000d901c0e07100e41e0006560030b1780d41c028a00c20210044070310b24030007900302c00429039641d900d551700e62011410200080943c240252000324652400200340040301c65000b04450100864249120205610200383ca0a9a910345452666600c074280110356000101e02044818040c45c840c0c0000c100070310307004262407030031500c03040700101042d010030040380030b5260083c00c0d040090901081c0380001d50720039944503100814540c0c3d00c4a041602c54079101040390025140c60781c0345400d105120307100010302ea020404840700c51295841102035881d5000710054502411841c41000c050314038141c101001b45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 981039001 1250 981037751 981037753
    0x90905060406050415081605030d11070306050709080606030c0f0d032001020403031d061c0222080c0303070807030e031c1701060318020f06040e01081c050309071a0408 74
    0x320400c040c4456070b40150b44140031b41c40c0306070049815044081c8142104039039000f40a0000e9680100c41a070b0f0105001941110314001c5060103c00640e01d403007814050100c039503035440010b06005159150040240c000d41c481d81c8810580841655108801c20205134280c4681d00041240c0c5000d81c0c1c0844280e95072400d0002085030082c18140540c0130b8021a8000d0742d6600c80200541d5155400d84404000140c010108000030949090403101c2c0500104e05800010f140c00100e41c204c041081c480c003a0916600f20100e03003000a0b0608100d02d10400c0400c4028503d44991a9941250f0b0f208000008003401140d40c07094959580511034148200d581c3c1011700051004050000d000c4041910040b00d90140c840000c940b0030320a20400861820162803516150055020040f00c0000364000390b5214400b004082070100c04201c02d42c0c02041200010810305100b8407159402c450780c410010300300039050041200d0140009804801c0314100705401846e07490381315204900d8130036600008a5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 981040251 1250 981039001 981039011
    0x1b020301050a052e030303021c0e0a020103050603010c082a07030203090a1a0304060b130609020c010c08190b0607020a0e09120f1b01090209240a060909050604060504 73
    0x1034944070f0340100b441105004503480c1100b1120100c040c1030500c07500b00390b41e801c003250401c1c8002806a402090442c01400600752408245814141620065880240c40d5048020741008650700350140640080c4c0850080c44082d00c041380090850500070f1001c98020200c0e0030303044501414842901942c0203400c401030b510303852410087e559502c05080103004050070400062044041050201c11001c1d1220640c55070b11283c44000103800d420000700da03c021005144540000c592180a0042121a0300940c0b1074000c11800750071a0440091203042c00b0030001000045034040010810310009140000703149035125010450b40d015458009400c040e4140c0301080340c4900c249034a108407002ca0459008804200c00740c0d02a00a82858004043c0b09002c05040c003e2005001e11400003400b0000030380c0c12090b0001045048180d0394900c031690161000784043c441d0f08841901e0342003e580c0f1100c0c040c0340101c010180c561610075542e04554030000300300c042e5140d03003001000b00030003402804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 981041501 1250 981040251 981040261
    0xd060b030709030506060a051804020f0a0618050d0201090e1005060d06171218130f05071b050706030507050c0106061115130206030403020a0c140a06020615011b02030105 75
    0x140701c41d010030b413424480c0400244030341c80d01599103820f952025052400e01c400c40c810f541400c0b40e0151080703a00c13540c1032000019548801c04444014141030742ca81300501781c00c40e407000032402072350031040c046c03d204844840540d0300100c0350021146445542da03c42d907103070710180791441201e4000a901c1000000c5181010303986400c10310607a10044107200107820380c0d801140e030b6245010008a103000040c000d4041e1101d56800180c0c40b580007502d0000507140070701c070980846103c0702d1070103101580c1e41c5c103220340d02d030344000c0207541c200401c8503030750041d82c598940d0b1796a8a41031254404054488001903885407084042d2002b18811340700a000c82a180d1002400b20460309a00008038420b00320f4603111502d012807024058500d102c44085a28940d4080c132255905c01402a015441950807160000303940c00030040c01450818094010554075104126220249074400402c55011205214080300d44600c0d1000003502424007030310007c0030416001102a10a101070b5055180408000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 981042751 1250 981041501 981041507
    0x81e010602031e0a2309040906051501080f010936200f040504060207020a0e04150903022517010212061819020d1805011508030f0d060b0307 62
    0x2a8030b0340306000a9011010000f0000d02c2c5002d074004610001c0c2c0410001364007440704038950303400724109482403840e0082c10004034086c0d03403d5400403528a5614810041c84000a64400e50391035002d2905001da410a40301501c3d14403418014440c40c50394403040178035240c503415400c840351041c1e00e507003104504100314840b00d01c44200c001501c0707170096207800102c50b81148241c000c203500e00a00c11100c1d1207416044c4001850000c008075001d0781d003040700300c0160b078a5001d00001081c0713643c000059403405280260f82c4410f16a115001c6d10f040043e0341e00043d030040741d551542e20130341c41d0b81e54a40410302854640b1040b240d002c00b841040c030340c000da013440c03e040d002040490348600e808607140d1520750500c0f03000040711090000002150001c1030f025500394031113a01030702ca440d07805400c1c240d105003803504807024200c039403030701484c440c60300001c2040a0040205040c003811030500301d9031410b10526101d00c80c407841c412910b00b00060001200703c10f9031009025241400d81d0503100d2418002c06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 981044001 1250 981042751 981042757
    0xa0603020c0c0301020c0703060e1914010b041e0b1504090f061410050a0302040b0f09030f070528080607020609190f0b130b0f060a080f0607081e01060203 68
    0x10922809062812202c6050500880380340031240c6000f8402036107036407105d00007841006043c228900884246103c0c17041c0f5203140717022581c05050074004009415040a0844954111039409070b41804204451012500092052201c0900300410074007440c10008660105403044d01c08521b5021030089103044075540010300341043d160081040d0340d182c620a00c1c0990003000700d50340c0030459548070004c0500c117001070910b0001ca0700f0052b0a050702c960710706919030850040041220000b10b1001990301e8100294407800c0d4001015040740e60803d00401e040c0056040740c0c521010f6440c86c40c2002c0392075901c00c500241100000d03a007440c149504029224203003034901813294420842ca20090b4103e1025860b0056400b1641e00700301502555005403414000308480308421a810380b05002c22440d020041c8114100d450900a529200d010000d404003150021007071948244c014514102e00042c099070810b0541c144041150381d20351451442c1e1007041c4584000840d52000007030401d0b000000303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 981045251 1250 981044001 981044017
    0x21002010203160e030304060e010918020d0f2a170907050102070509090c0f0105160b07091a040e22050f06070e030a03120e070608100b09060a030b010e0a060302 71
    0x103600c00c0b100100c00321100740e40f01c41d044d0703451b4004110800102c1c0c0241c030741c4c25412206040a460322581e601d038141c040750038015881980342e00003400381c420104900c1007800d00c103100007003004000b490f070710401c40e08c0282070240d424078120404200c2c2001c0c021507607a00d1021030450481006e10384030711010303150316082c42006c0c058421a2000f050300d107882e2035000d10840f0180c000b800c000f162403003089042811000014103100d030030031016401003203014683e80200d0255282c10a03a0038001c41c003c2401403642d10030070f09401082c050384c1e000d5588004940c215004c0d444005203030344441c4d49001810700710118060040300c2c1d40004034204000810b009212000000546100d583c03455015150155065499a45500481c199100190090000c08400c1401d054001000d820034009289085007640002010412400030040c0d110940d07803500001c0c0c811178811901700f400700404140a8000d00841c4805d041d260104002e05034070503035040c03081840080403c60078594400000d1300075803160403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 981046501 1250 981045251 981045271
    0x3120d06090c050f07120c0b0109020306030c0307140d022815020705010f121401120606120f030809010e0601091b02160612060e072106030b040b070507021002010203 73
    0x20200405500500076130b600c5102900c4010b14080032130392510461707405060010140311007520501c000c80d0f0103c40907800b03002c00000050b5241449410940b8100000404c2446035000000c1031208601e00c40201980c00e6003035965184038412480080d64070200150003c00c6003103d010959210f0710a040c00400322418078110381c5400d171500000300d807034500f280036030340c04101e022580010040c4110b0000c42410a49000050101d41700f1105014070b00080e842180303110310625803102031005501c1184024a8a02003001e8510050354520700103c0760f0707800260030f2081c0303031000640704c4500b900078011000304103080e95095a103602070b0304001c15075000010341d641c140c1c030464507002d40001040424004e041a1506040e07250190403112407030005204200140c44440015400309074124981c000c00880c0c403a00301060403c1c486125507115426503c00440c14074a0400208001048213508075810400c0102240d0340e5500c182d441d4812044003c0d0403060148001c1c1d1344642c1036015501801da200307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 981047751 1250 981046501 981046511
    0xc04021204260a05030c09121e0102031618030501050405010c141c050c071a0601020d02071208131509051f02100e0f03040602010f0b01050a020c0f03120d0609 70
    0x8103a640b52098900501d048400b04101c01c00340c160085000d0340c2c1c800c1d00440d000f031800341464042011410700322642c04040c0d20035030001e9101101540e04512102c4524000c500318549901205034507142c9041c603209014514a2000143d40f0105440340616000700091005e4202440c0480c0200130401c829400100c04201101c0c02c035286008440010390481c2d115942e05808060f0b4200a0030043e009940342d01c0e00300070fa10001144c10040595100c160503490f445860002c0019040c10f844648800071500907100034804100600240c1314403581000c4c03526102c80803120340b44070001c1250080142081000950769000303a10101c0001075450542d02d81d047c190380030030117031030641e6603404c0c01000d60450810104840d8603a4000c407010004c450132070703155141c0700c1001c41c2154001d810a90041c0d45904241001c00d03140d01400403068801e18020303290045c0148002e46071400a000fa42c130840c02d202468590f5582000814101d01e104680142c0e0f440541200303000500c56841103000c514109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 981049001 1250 981047751 981047783
    0x13060e0109060c0201120605040c0201050103050d030b03070608040c030602041517070207090b0303090a03141504020f21160503010f1515050f03040b040605090715030b01020c04021204 81
    0x2401d060084400d50740310b0302d890b41150f90041d0303441d00c20078080b880b8103a40c90340001036554407402113440102c203079000000d240d4150300b4240d0814850a5610040c90304014040507151000074089007110781074645500c441d01d4914007113190f02d400d0303070010709458008940810f5841c000c0c80389180305281d41d19400c1d08044070803601c01e01842d0483c5c0100c0960001081001a00c0c43c64100c100d4261000b001d49103409605000101c1144a540040d281e0540004440903000c604104400d180451914030240e140750541c00140804540f1002134058264490080c00d025040f0340b0040b101d02c1075074241c42402c2d000150015401e480e9125192003907003041c4800c8c14503042c03881350002c00300d0030405a1292606000c0504110700d207000100c02000b204000503804014a070b8080c60140e44154005821820141410020341d03001400f408456040072104010b4500070715020040c50030941408100460050700503400c00602520450704640001003007250809490542403042c0e03c80c0940e400c504401d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 981050251 1250 981049001 981049007
    0x1314070c050606010e06040e0c09090a050103020306070c0f020a031101140f0717070602070c090e01020306010e100318050f0d110a080d0225030801060c20030c030313060e01 76
    0x31480000c0d046400000228a0ba0351049480038031302180075095030300d002c0c0d07140e0300351001e00d80480f20a2915070b0085404117003454000165500100d21420a0259505603000070340c4410300039010b04140f2501a51407002c2202da1404a411701d6001044048007582e80d003851401c10307a03040320b8140002e080c2500040141d40007016035068001900c9114144207590303840c8009504042088a103103c01808090002001e60000380700c15403140c003596054a24100d42c0100303941c40da049022840c1d00500420801d664081d524408020085480e04d400600741182540104a40200d0a41d50408001c1620a000c0700145c0c010000c01401d0413030783d002213407010888030026006007400b281e4004003d85400315021401510f0b601900307610051400360f0741060340000c1c00c02c80d90110144602410508203150f00315070303124014022410010030042d0940c0e110099602010b807a5071329410b00100c10546500e00300302d981030f805809811242d807131003401508500780302503109002c0020220b994020f01c9500c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 981051501 1250 981050251 981050267
    0xe09010935090102011416091a12180a11030d02010908040b0c0c0d030c051c050717090411120601020a0209071101110406053403081302131407 63
    0x1201d485100e07501d0220340701400c03070303503000b101036038119922401c85902001c00503107491302511a1240708040300b0301901e4058a41e28071503003d03205100b494190040c0084900b82142d241240d08104035506541c3e1083d01c40c00c0c1c000913281c420043c4944c000420809c442c40700301000100b42142103441e00140c0440c22400c0e114a080c0080c1155810b01c010080212800080c000310b48043c010f0310202011580410619140e000d0143c000a640441010a1100920a070355a04042824602c1e420100060103041ba100b08000100802c40c444072649681c2440d00940c2c8070358400800074410f482407403000c0030241d044008890850f4104002140b41507000141102000794090005040c0e82e1b01d940041d1240c000c400307140c444c99500c814560000d802408020809400181c507a00c0e2940c4108550880c12400c0c442d0030034100792a03030400301c0e0504640c100200b55580c1854441225614503c03110520034020000030b4014520300d0703094201d090140c00001c08003159a14495180d6160710040756840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 981052751 1250 981051501 981051563
    0x60b0a06050a0c0c03050d12140606041203020316080c1207050c06090d050601150e010e0604090b010c3509090714041806060906140d0906060e090109 66
    0x41d00c2000a0381c4168011041c0120b00c0d0f024a801202c0155240c40f01c03404c00e01486c0d002c20000b5001062010707a04800c0c0b080d86071140042c2141c00c21481c2075008103025104901a0300091a07030700d168041018400c004030740500c181c040403261450403520381000c0369044040159114000c150b00394885968900c140c4d20345c1500075000b010280e0000d000e01826603c0715070700c00e8008800012040100710f080040034001c1140700c03c01040404070b20130041a9110342840c2e1030401644409007150b1355194401d590558403400b8001402441100060b070350601000381c018140b42e01140c015a010700b003000d0f070720900000c400a070750110160b803001a120788621510145d200d01e40901281405200741401d041540e00126450b29154079100c59030044080e000e41025810b407102030600030542d001c10514010800c6040c1340f040030fa200703843e40f112401203c200100840e5140844000e1061603040070004003c002c0d101e0505c0d05184070400e02808043c401628809a078450b130b442c8584c1d00c01146406d070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 981054001 1250 981052751 981052757
    0x1a01020d02100203100504020a17062425060204090c080c1206040e1b120309010504300506100f1d0c0f041e05040203010b180103090816060b0a06 64
    0x8034590101c02c2d0003508054040c483c11065500081282e8483d0b100034180704a1941300e44220340140b88247e0312480000702850302840c054040769081c0d020398a01c15104600c1e210b40e880e00c54128060801c0c1041d210041c00c200300d07035281c800ca000c1c007010345d0090090304d400550520548802000c10b64141d5019101e407211200200401040c0b04081400c07250495001407001c180000140c01b06850800840c4039441d50640040c2c0c090310b2480c162600050003030034100a036050501c02e0b070010701180200d200b4214003042110a00320442c2d0540452043d81000e012600e6000007581041543d038401106c0c8560342d142200d4000c126034030780194020480e086c403280c0b02c1d0b0405045465030b03202100541441203402050000d10151440d441c09000980b0f540f04c1d460002c840f503c0c00c0d240041089500c803c0c0142d20400061003040118022141c860303a00d45101d54090182c000100e004001001000e1300a0f540450103000480c0d8803141c100304a03015100c148141c4418000700409003180303102d40004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 981055251 1250 981054001 981054013
    0x2010b100c03031b03240e040b04141014101a0d0b060c010c09120803010302040e03070f03021c02010612022b031205130b06060306030109080d1a01020d02 68
    0x910400380005240e1003071501081500c072144e10440c2d03220b601c84400700440c2e281c01c500c0002200258000c2c803000d00e10a940041345141c101141c2003194054409020000c03010005810f0004060702c2000109802d401c032a1074000d0b4001d80802094000c039002c04000643c0e01103039503102c103240e212007510440040320301d20004006c28408541e0002c422165a1a1501106503660750351502400741204800c0c00442c0714081c9520061842d01e107034110f8a0301c035440c2c0184801040c082d1040e40d043d00d43c181d81c0011001c184800162a60241101c001e210304032001080c001c140e404140702d030f5000340146800c010141d54490990980d0424002c030100c0a520030700ca040580b402070600d65540c1d14010f540d102003502400030b5280d895060134160080f1fa090b0180308100496440b8a90b44000320a01c0c03c0150350042d56181144e85000d081c1d54441d4001202080c80c40d5004e5020711803c0768008566a0f0715101c0503801e1014050650741e0040212036244c208034254004525111450120b50107011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 981056501 1250 981055251 981055279
    0x507021203070306050a0b09010e06040e060409240c1d010c11011b06050403080a0e0a1101030213060309051507090e0c070804080a0212030913020c25031202010b 71
    0x10707400c0140524201911140001130a07107071400e814000d008030005003640d880d001030025100440d0f900615000d101e0811040000007120040c1e0394021408640126480b825820400c2080c80070344150342c05616a001c8280000030241c0c01464544550b0722010341035007080144540c4482c0c2d202d1424041124070b0360440000340c0890303c202116105043c4211103011500c80310f84804541c0e08104c4110f40d0341c03800e1000b410f0300414626030111200c0380610444008030222038a0b800702c00313002884140444001c0b841c0380c0c029015502860344403200c04d00c2a50b96040c004016000d8503106440c6400744070fa20003800040da45116105845139240c002601d071401c403080a184400400d0b00144500a100ba80c0006500c4801072008201ca9001403820054500401c100c120b0304400d00c000c2c035401000452581c0e103480b802c400c0b105480003c0141c4945050003028109012884040e600c0c15400f250320f16a070b0301c401d91039000d0741d0041c0403070b907250100c1d0101a4204e5140c1e070980380c1e010000d42e061003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 981057751 1250 981056501 981056533
    0x1c0210091523070309032618030705041e0b1009120311010213211e06060f03050d020d02060603120702180a050a0c08010b0d0e070e0103030203070b0a050702 69
    0xb154020440c10000500c4405041880d060303084002d044001500300c100802c18080e004289808101c0400c0c1029807890007180c41452500c1034000020000140e4000501d03940d40c2030290340d00402015009000d074042c140c441400003250315118280e41450a00c2403041800c0034100d00c01c160321962a00001e40d420305192801c8001c00340310840c1040b40515617582c981c0740a0001c2d0207804c02d00300321010007908050001402c1205074444e4407402c65105007000200711f0305450740c03c0c0d290401c08001d5411400341031150243c91075410030b4901201d001000020444d000a80b02c00000140d400c1e030b00d0256844604a868100075030b40642c0c50b9000b100074280c100755150003042407610081281403039103101c80c050003803120201c4000140640d104108a141050381c02000743c1d03031480740b60282c7e1641c104181c042e0b150040e00d0704000c0d115601c1c901c4000b50142045088050103c9210669aa603035901d0003c6d03482e8854001121032100500100300c1414060040a00415181e0060705114103291128 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 981059001 1250 981057751 981057767
    0x90c1c17070f12050a0e0105070302150615042c15041e090308010f0803040614031f090204050112090f0f0201350f07020604080d06051c02100915 64
    0x5075002c10310000c0410000341050700352060b03100180c50320380d11001da0940103050300c3c00400701039060180401441000a6002c00c5000481443d0402c012181e11a0703800708149044465101252050000700440c0054000c5016010102407508603401000751084034030301500184c0c1c68260642e41c0c0100c1026a10700b9070059000058403140814507240c4e2000010300340c0315210000d40c0415605030040c403446598442c82d201a100800c0111310b41482c164005064920443c0402c0314008040040b603e490303503807408040c540b0700a103c1c0000780f903100c4400500962003440743c03901140d04d000d00c00102d4200c50044202e00382c2c00800e41100e00d8030603202c8150301d001ba14412410440c040200008250349003140c4001d400c450b03583c0011740c800086005009200c060611081e071106401080003656000598661240e4002d0030b0980b107541c0b004501000c1e240fa40c002590bc182040d01c400c0c441000d031000346d440e1300e000f118550b058668010040c0d501c80070314022144a0381c5c190005801d094081c08403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 981060251 1250 981059001 981059003
    0x6020f0c010c2418200907021e0a020d12030515150d0b04020406110c0303030f0613060806250921080f1b0d02150106080c12090c1c1707 60
    0x228440c0d00c40e0b4664005482e02d09021550210201e809a40301081c5e0070070814410f8060b2640103d608000101941e2110202c41890401c0000040c8507002002031005009881d8040d040b04544104d03481c00d100050b04003140c243c000ba00d81400a0140318652004200c1d66038080c10f102c0030465000d80070303d55503010600340c640042c0c4038100340703110b40c850f44010b20083c030b03180d59450407419420700803a00b851007d00f5014400c2e8000d00c00d02007508240741d0059000300301102c803600c0c20304004900d100506115840700c2658000c0a0030401c00c05200780c00b032040f07215812025517040100a20035210500b190180ca1020320112440b140d40c5030307114503102c441c40d0059000d58188144c031001391205034030501ca05010f840084043e141c0c00d002c2041542c4485000d4005459209050002e00c1d01418051041c070b020080c0d00c0c0041071140c107660040b14a01e0703207000c0c8050081c1c80c0100c0041e036602c1c00014641e000b0741c034090654000415800d41a41621b512142c0c420500d500a00c07501042d0b00001c0b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 981061501 1250 981060251 981060323
    0x3020306041e050114040e060a0c0c1b0311010810140301140114042d0203040309030b0f060a060e010504050609010315030b160c03081f080706020f0c010c 68
    0x100740d00d55010341c038180e03a04200984001c20300b903042c0007080440d09030090300640224244401b0050701d03540888d07060351005240078001101e8100c03d4045840503400e6402502c6510b2840480400070700858070075054074090040003250780714100044403606c80c01c589925010794016014890b800301c0c0c4000400907500180003190b121400080354000001c2a440390200e40348205100b1001c1c00c04e80900114500e00d2803205105624a0b543c8000d038299044035200c20560000c00a41054042c4400c80003542d000ba10740307041e42c908011801c111040a0b40d515121308003800c0001003991261301010007810069441c9401d00b032a102c140035031500003501103030600d07440f0024103481c50790841010004602400058003c1d062204a42404003140b080e414100045841c401c030210b17411030701542c0c00c070441400c11210b01d40040344601d0036281c1c5030031020140c01542d1000401546c0003801701c150f5003070401580c013400e1400005461803203da080c000c00c0302000140810001b24882030300d030141d042100f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 981062751 1250 981061501 981061511
    0x50f090f04080f0d0b030609011803080601050d0501030b04020f19030311030c030a02160608270c030607030f0e0604110603040503131517220203030417030304020907140403030302030604 82
    0xf1100c555801c01074000d00e0090f603800c080e11080c501003001c16000030004000700260402074000309000501c2c184c2c09800d0044040201303244e80d100c3c104640c4100800c0204200c296180d25260403091003d80b4264801c819a07852158145440000494804050040e00c10414910b613000c0da0310446503040300e149800180900d5141030414402841000c039290301400090656892203100846030781c008a0402c030816041040c2c41e1448800c0380854603000f6802c5c55004010a1603500e00005103840c15014003c010901070b0564150704011800c200c17a0205100502000320140e42e290400c5401401c0c10700001d480c0b81d5035050a00c02143c0244c05141a40d1400744100d40c02c544424065100780c0310b0001010300010055440003c81c1320400c51007070b408030241409a0f141c59000705032000b240b54240e4550b4280c04540d4200100da0040407104810403605440b420301e1907e9410445040c3d0141140b078001482c80c910845040060017240804203003420f095440403402504001c2000760803d07610 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 981064001 1250 981062751 981062767
    0x120613080c0709060f0b070c33020601050a1202060f0f0d0905150702010b011e210e0f0f1f0905150412020304051c0f1704030c050f090f0408 62
    0x2d20030303074001c0c02800300045032591500359841410300d855840f6456411062122100240007011444210303003114005014210701401085000059042c21045c003941103400485030310703000700e0100d04070b46089422504140c0d680002220b9441000710084d8030071b1042100104650031440a04002c900b111060703400c20203050213160448001d440309441f1944988919558021150021580041c0c1071000340401c00c08107002803c40e19014031078064100f00003c0300300d5000e110740d1040711b03884686030402c0a1074038100349002c0107120040d5081964000c405407401071480001d2078082d1400c80708001e100c100c090740f81c0d401840c1e003120081d801150b00c0b0702600c00032513801c10100c68415107880306050182018500300c1313851040d0414440940d0000e0108002c182d540e000d004800001c4050041d20034084c41c904402c444882d020700074407951510300d0170341c0059030302740c064000d1340d01c03e2410050203074440081200007101c0d0502036a01441c40c2001031510320005030140e0b04180719000c06800c2c40c140d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 981065251 1250 981064001 981064003
    0x20603150907021015060c0f1514060406080c010c151103070503092e05040501060905091005100e04062f0a090f03021f0e0a12030806120613080c 64
    0xd80d00b4000590108120b504804c4851140c9070703403d801309000f2454907282800c080c2c1882c408440240803441703a4217003242400b007501603001030000e00d0242000034199204c0c000070080c4c800d450083c0074519000e008a404800040c0705082448140c44004075250a640d841039009464155039582a40f1040e81c410b0820380800514001ca000380c6456449281074100784e40340100946030703000702d4800030054580c1035044102c030409400c140c000c04680c0b50ba03035050607405042c050303200d54421031170700342084086403000c101c04007000790700d845c1440381c0c0d26004003048201d803443c011039540084200c0401d001550590140ca8031110380d08d88400f1b07003002503c00c03c880c21000981c0c03c504100000d56440d02660180310100604544800e5003030171401c50b008210901051007100c86a440741c1d1404149450041040c500e84140090040000c1d60b110030f00c0100c01900031a003240441c3c92180071404601e001049410780d158220000e011590312080394001d10030030300400342c5070040c1c204110048808 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 981066501 1250 981065251 981065269
    0x8240d052802180705041e030c1205060108032712070603050a06060219060b01021e010903030b102c120105040b090d0509011409030a150c021902060315 67
    0x8040607036110582d006002500c000d003100c0c04120b200101c20040f00c0c036001420745050ba010103008041c40c1013000b202e2203005a051f000504511078a00d0300180c120707000398003031040034414415101705903650f565050340da00030710454005840d0b0b010741e0444603451840494200710300c024580d008080d1525492402c1000907001103000a0301c07030782081021142401050000c141c0d5200a09040c0301010750790301c46140303001c0b009204984440d4030044aa10811524404441080350064510102400d02d80245a031100440100381001c1c00140c0701e140c590035001001c80c0f25220506c0b50003001c545a581a885d8a0044c070500c281c4520f21642600c50340b036460042e014000000410341018148029442002000c2c007e071548551050018241d010082e54400c0c1820300300101c04030400b400800303160040949058040c4109014030041c8225100021103e260411040001303103542d410403030320340300c501020300300074039003036940100504080c4025940000c0c41c00043c3e0a6060f00d03800541c10396 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 981067751 1250 981066501 981066553
    0xe0706020715171501110a080706020306040608060703091e1236090e2a0604090f0c0306060e0618040207141f1a0d050c100c0308240d05 60
    0x2420181d841184c5580021448140340d6200e00141040c9a940d0380d40103052291b0800217100d0781d00880403480c41c3d16203410480140a000055a00318a000c860080c005c01c0003000a41c2c020103040884070945001002c0c500308580c01104481180031045025030b2491040c80725100c4881420341d400c3c412102250b603400c0240922400d03144103d20b0600003005448050218891540140741c81c03080d10810714113510070b030394005541c44544010381000a00c03d03000f1640a105e0b0103080020b00e00494074642e200c02020b84480e02c0810a0316141d8402700c1d290a445c0200756000b190030070980144400b02800d440d090a00100050b14202d6180d03210301c0c100d4494010301000d580300500541140010400d13005400c400510108862010081107007213250045440710b0084000d501000d0901400b40b014038207020010309040b04240351604000e1450510000a40011f004c0e0808280759910032003900269200007622400d40e0040c810070000c54043c5204112414170a40718032080c0c003509100d10405075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 981069001 1250 981067751 981067771
    0x402030a021210060b040e010302010f12050c0705060f0402060f1608040b1918051003090c170c031501090b0105040f030c090b010e090f0601091205010b0102010e070602071517 77
    0x10f145510740f0041034070345640103070b09102c20070f200500c40c0b080b4880c08141100d0302484c0201251071030710811345040c000c0c0380401e01d0487c1018100807005080b0801885241e210314103d60072513a40194010342c001090350020342c0f05400304440700d148907280c40509080140b13400c521070885903ea031140a1907126500001c0039290118100c0b9110202c0300c00c3c6e940c2d084550402c0c8080114004040e000d20300320b03008092055a035119082c02c090b101e0f82c010b0301c19991100c0c02c008225140c82400d0031012080d0324041481c85030f500c4000c0c0604000ca071840541c102441582c101d6428038000b079004c0c00d200c51a01341000400d010000d080e14140b1007400c000c60156401e9101e0a05240700c0d0301c00c1e1900007602d54180140058904050b4a0b00424103601213040e5100182c079458010040f121059513910840d4524005a2104107000c41980710400c001ca00360001c03c41c1002d030125554903803c06102e9140036030410402040a040c0482c540a4034401c14504003010140326045400b84c0c0d8402d480360042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 981070251 1250 981069001 981069013
    0x907061d0619020d1403160504090c021c021218012604030e060f071212020a180f030812070e06030f16091818050105090a06050c09010c02090402030a0212 68
    0x142d0140000d10b0003451354a4030340c1c41d0342da800c1102c045a11010348480700c0c1e58611289944410b00c1f03803003a030b4080c0c0740c0c0c0b04044c0441101e40000035660484503500c1c00e0b0588690101b0881c1e03d0000903510a8070240c40381c602c0c00c0001074101d0309040a03401a016040c00041e40c1244070800d154020031644030351011048049080c5030500400048a2192180c041c803406c02c00140200035003425184016400207a000815003000011a00c100c0c40a44804c441d90010488510300390b044030f40d01c417124040c004c901c4012959084403010540180c03201424816081101025210610200941c00b1019007028012481c00c040410381a80c000c4440404c51107944040c4034826010301080058000c1c02e10b04856010b00b4a00d55080c10285510f03901040390b50703800c4400f03007214510000c0c42c449810500800003882c0241c2c00c5071722000c0c0c149049600354034100000b802d0000752029150000010ba4808850040b50340c00c0c07111116014009a9040c4500c00021005a50b540c0c0204000001d60700540340f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 981071501 1250 981070251 981070297
    0x91403041701150302010507080c01320901020906310b1b0d27080a0b0105100c0503030601080a14101802160f150c0507031202030907061d06 62
    0x1007160026100c401410210f401c080000d1307a80300c4143d6081d690000225552440742942450050042c21501c40104100004074090a00712407800c005282500485080315a1810a05801c03845020b624a520030410f004050914000103140c803010403d50070701ea03082014071000030038810000d0703204a080f810005801c41403004045860104000b10708010036085428800162180c4441c022111065403403441051001a10740041d200a103510001c0c0c0c0c403821024280400c0030142405000d0003002c221122500d9144160221081180c0120184d0704503141d0200464217440080c2c500004140c81d400081180107040310302c130340150a481e1024607010b241c4550507207001120848510745620511400ca600200042a03000003a0b105140050807145451b1020030800703c01c600100d1a4640080700300c155030804010001c4500075290415910107000d951016031200316010141c0390800c100c2008501e000b11110100c000001d0152100c0b03804900100c0c045070005458000b1041c50080140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 981072751 1250 981071501 981071503
    0x1009240f0b04020a0e12030409020c0706020606010503010b0f030601090302180108010f021201030822061706101d0a120308270d0c0206090a0803030915100302040914030417 76
    0x11041a070241d5040d403c3c5100540068007004598002c0b60190928801041100c0c400b40111005071480e18411910b4091040e0180d03680c2c2c0780b90280d40f000d4400e2030b01040141d03000c0c2c8141d0f0304903590f04040c140340040381c0074800003942014040e103041c80300508010006070744e2000d911440100342e40307a08880d58509280c89003515803801410344400d20400800051103014046a81540d40103139035070750786106110701c1014040d444616100300c112100703c00304140f40d011075002c1d41aa021400d07945561a0542004106080c1ea9515000310740c0200001000340300115984000f40c01c000d04800c180c030340c0c1e040d07800b440300c640140490008a90000b080340c2d000103446219803959a11802106200b19004110358030380c010f0400506010054581400f159107000803500d10790700c0070740305c03096580d502c2e90103d50b245c106076000003107400344105030403c418103401d115201d02990325848502920316002e2200500f0b010b1400c0d00d400c10400b00b400303400d20f0208002e2000346034401030451100c2c0c8149240d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 981074001 1250 981072751 981072761
    0xd0503032a0a021015050310090f021507170f160203070308030106020102090915101d0a0e0f060909061305150f090d08060105090105030c1204030806030c010e031009240f 75
    0x50905c0054038288040e880018000280032082800000c101d81d05090400c2c6002c03001c80000e510446084281841202a034054401588030b8404181004160000340000340104d4010821512041c0016a55003212610040700a400903041e01c0245480f5150b0044035442600007802507034000131440240e0401c0131205500001a6000101440641d00050122042030351420308001c042504020301da0301000109900c403070001c00b040f01440d0380302c4c0c3d4980625021944001d2130103404000400605000203030503c140c8100d0041c1c0f44556a1511840400c01074600c242ca2a00c0707110350005547d1646040d1034003400c4100d0400d4100e141c204070300d0b407400030211100350400c03404d0420710407981d80100550740842c02c00d0070500e413250345d0114162072a0045c81221600030281101348010705400400d59130003000164203a48080c0b80f05e2006580610210765281d406900010341000e4025466100242c0c451042c10b10380107060201d02c032502512040e82824400d180c1e00e100194240d101c40c864 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 981075251 1250 981074001 981074021
    0x2040f060f0b0705150c04091a092406180603090f0c010f0905061602101d03030702032d0a0c0504050a0b012c030a1109060d0503032a0a0210 62
    0x16241886036a1125100c1c07554103075401c4545e0520000c554401b4030302096a018200700d14040001a9240d41c802c215240c501030402d00584046021802d00b6089a44241c0118080f4002d04900803040d01448243e5014001240c0011104c070030900e07503940d40780b0081d80150120343c0100743c60300395007540904041c2c004080605004806080200c0030350452031500856804980c2d0b251100a00b420f05000c000604200961002d031045c081c1c00e1450f04420138102003450320300540d02004d80034040c982c2d40e105104010b1351590120041c90030210310340c5c051000041560381010700080600216a04d1301600920840303c0c00b001c3c81d4240541d08091182e1984420200c40503c500c0580100183c41303002c90003140c44058400140c0804121503103608100300d003c0280c1144c0185095081601d1480c0300001c40c14401c003501c10100306a072505071605107900c1d4100b000b440c1340d501c580c13164191250401c1c0d0600502e0405135164200b009039200605444e1180360003506c0c0220070390750550200d0780c070680 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 981076501 1250 981075251 981075269
    0xe300c120303190522080a09080102040513050a0905120c010509060f01060503070c0b0106020f10092a1a1207030e070504020f0f071211070b2502040f060f 68
    0xb0030095200c030b24414401414080f2080000c994558901c9902c518002e0590600700c601e05591850401c080d000050401c1c9600e6600c10010503100d601e500c0c21f0748150f22809a0028940401c0d620305291030740503d8002ea0b1200f00080c070070046130395003420000880e04400408071f01003030a20802500703004441e440060078010707055502e8604024851948107000e00310410001000280216014040301011160007000140d8990b80d5110000c0da9010f40c40c248103101e0047c80501c00c41d2216500801d1009030b44281c1d00607101300900d81842c010403540303403499076603548111700081100941c03940c0d5901c4040d031a47c00e60303502d00c1c01c074091700c42c008003800707207010103290039100540c1c6e40000c1024001c2c0ca6040780c0c0560364103565900558103016204040c0b5510000050401c108120340000c80442101d94551600c0306c9094003145403100d4007445880c0310340d01d0030815000c8079005801e8010400d417a1070034401406059401040803600d00d194008038a42c1d0b503130b100340914071711010040000e041f103407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 981077751 1250 981076501 981076507
    0x9020415030b01061701120f020405102d060f0212070b0103030806030a21020304090e0f15190f0908121515090909010b0306101a0403030e300c1203 65
    0x7117041744807280705129214010180000400400003441c01c80309821360010420311141c20001360039600d031407940c8151844440c0070f10081c60400c002800002c1ea00d000c10003680e103081e14000c0182c0390a603905110a00318000d000b079040c210070081003d022650700901c205002c1d981113107009003030722802070803040c0f1a600126070b1000103110080700c2000504406030390041c083c0e4002003a40756010300c0d0840384c01e0b542000201c8000c400300040000d48801b8240882d418040d80c85c0041082500580c0d558014800c000d25900c03030b41450b0f03000342e00248000100011881501d844d4403096400c40f604040d503100b03c11043c044010050318117081c1c514411282424154201c0e440b040682c070a050300607001d04651400504180e4080d84000c20b601c0e406001c0e42c0d0b09141a5402461b006030600a8400203400c01e000718250f15440801d4809a075850b40b5040d070032203030000c00c1110540f110040c495441022420309801507040c43c0500506400a20041040b10b088408001000c1d2074040a03110550040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 981079001 1250 981077751 981077777
    0x9010b031b06030403030f0617010519060f060521012d06052706030c0304260726041205070e0f06090408041e031b030b15010309020415030b0106 64
    0x14030300f01d0782c00c6075041c14005a1305182c82095006800b0b5940161101e0f6035582007803a50040c19006184502210560100d2550383c46c2014000c840e414090700c000c10054000900a0718050b0005100c45003114040040c0d44c5d00c07074804103946803400d80048040c40c2800f14000e554000c0ca54030b15500000c0d004041c4061030a04c0d1000f4028050241e449606905503022401201e0850040840c1210041d007120303070340c1c9854000301105074000d460441303144404001c520008a01049040c481004500840d4a000426110200c494281182c04042d140f4041c2805030ba5403510401000100300300b02810818a00030304010381402d2403580610003038540001002000c02d01042e5081c0d00c01411201a2a1038549090240003400b5642114200c0d00e040b21400e01020f00e6400440e0450303203c0c07031140034511148208201c00b0ba42c107110003011203040001081c42c030000542014403aa4061400064100013a0001019200c80072402d102010001c1428010300800d400c1440c0902041d00700b020b206040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 981080251 1250 981079001 981079009
    0xf05030f07180237091e06050c031b07082806022506050f16080402060901111002040905090609030d02030a1107060c090501030b130506031509010b031b 67
    0x10075500440915800508006a0060f8010140680b00310001c4038004e81c0d012440e0540c0341c140c1009040101d5440140040e5400407a00d000d202800c0d02c1e10384c1c2c0703012882c20300192400e4010030ba0318202c40c01f01b80840c9400d01c0411030080c6000d44000001c0c80741507d004805420580c008a100e00614000d121094010060407180075800760300c25001a91400405001c82c4680c1c01c00c1e09120002e603916007840c052000382d0b000386000c4c00c40c6407551115074661150050710071580d01070040210f405d00002801503e4500081d010b500c3c018101449180f1030380410500b404520285440c07113075401b150522403038815205841d4401c040300c00a10b654201074005907528042c0140c0140103940000009020344d4664003e020081003515900fa00d501403488c0c0800a8104450101b00040180713100182d9984240189505100b02800d00031845c0440302020b806003000a020035014800d07001850350a90801c5d03072061003214214000a061000d5104042c2019a03544542d84e540a00c05881e041c3c9542d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 981081501 1250 981080251 981080279
    0x6151002030a0c1502040b1201090c030c02061305100c03021b06011811090d0503092409040f0902060f0c010c05121807080304120b180a020d0302160f05030f07 70
    0x74000200b541c0e11040904c00c0c2000c2e12584d00500c6034440d000ca100d90300f4040c1c0078036441c181e989003802403098076030200080b0103c03460180002c0050b4000d1000ca0320382c88002c4001c2d500980107070140c60b000100183e181042d201400e0560340007d40c001400c01d6950180f8a607406040c2a110103003100c0e500d014000300f003031228407800340c100e5641c1e40d9030318134400d5031002120441c0101070102c0301550501d090040d00d980200301418080d08285d504c030300c0a02031807880c1004000f01450308905050702d900503c0010407000300d03124095640c031034490001d607413554007a000100ea5030809032b0707541d129119014290380c21131000f1810721806201010b01074691513141644040b103001c0c2c8240700803003250014540b0b02030f503000007141d0000140115103100181441c0c0140740c095483c1c444180c0300c03c0940070a418094985000d40d07003100f05a1001031030040541c12a07540644110b0700302e000840c00707004050115603c850130040c0c4070f4070f040000d1f080c00c2c000d00841d40c00c40b4019103002480c040384140014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 981082751 1250 981081501 981081503
    0x2918060f0a061e03050d08071e0e030303040c050a0e01050603190b15030108070b040b0f0a232808150a120c0801110c210c06151002030a0c 61
    0xd28440001140c10040340d106000400c5204a4031080c60072500501603292010f000c00e540700d009201652040f240142c2e00d9030300030340140d65a0780d0083c1c0e9602c1940e00301011074000c10100030103020a9103941d81d08101440c01540152031600c00180f4080030080000780c1540031120b0001941c00412281d030715101030340e91003450340d414007100d0b8a13029640e03002003400241c0301d68400c210003580340c0c0380c3d0a107070007960503100c10104440c1c2541d194004101c4a000311710031040440400c004e0b2080c0380503502c001d4a508646401c00411000d100c492280418030fa000001512500101e210002500307824150401d0b0403681c801d058031000c59107002058688001d11008100c0c0401518610680b0b03184285001800046446200d000040c50041c102903503e03c111176480d800e2001e10b0386140c00500031a8078030910007000300a0300c4509262421107400d83c06014401800912031010200401d00c5014401c580205042c0820200304c001c02080307034100b24400045501c03c0c405000c02e1038005400417445 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 981084001 1250 981082751 981082771
    0x4030206040f08090306042d020d0f0516032904152c010509070b04050d030e0a2126040e06132a080705030703020306030a291806 57
    0x7460528041a21545001e01d4146c86404100000d2240c00c2000064101080b00800d01d17008070f8040e0941021070300304010394484142c2c5000400078440c0703141482010301c5282500c43c0c5004000c17044102080c650b1060b2070200001d40a0160300f42a0203014403040403520015006050588400c24070741d81c40c50651503a5a521040004c40741101180003140c1680d459141c604502601e4500d0701030201a84c1c0c40d409417050920108484111500341c40550300040c116284090850310304950540421a02d0340e003160f94000d012440c2c107045208100c81440112800c5801d03034991800a0407414401710b84101201c400011074441440441206c08543e18421a1140c5444943c00100e06011131007031351020506d072a0481030390710103400a50040d410440e441c5ca20300d02201d80c0030b8681d040e04032407100003d4001c000042d86207019601a6070041e0740030701210784104d030076079901c0b00680e03103400c413480c01c46015251020401150480300303901c01d6031000151560035001081c03641da8034001c1c10421074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 981085251 1250 981084001 981084023
    0x30310090e0c04020f0d0e0f120d110f04142209031218030f030c02060109110d0509030301090f020f1e1603050a12020c0a0809010923010207050102060403020604 71
    0x1429000c014165a00e88010004c541e40d81040c01100040d611403006801c40c1420301801c600014400f044d05076803401c910000c0d281c0240101007620059001040070000c1075503444025004060074000b0b0642e05402c400480d5a0350704000c1401070118200c64080c0c400e5000c51006140f0070190301fa00c05403100c1c4840041034201d814a8240c48046c4000c0581c07a00368580320960b0140120318803d402d1310760080d100e000400000c10f00440590340412565800759100e8001009400d1a0741e02070000590b403c0c004c0d90802604200c034034141d031019140b0720b4080c0e2001c00103006040d06032080350103502e0301c0701e421441c10076000007094050180303a2000d06001840c1700ea004a103c0c036881150b02e41d031070313100180c03102203030a1030003820503002901100c0004500300a10041940d50348211026003d00800800e01c0445603910740c0e0312944030560160410041100002d00159020105103400400214440215032002d000910b040b6860b40410704541c040410b01c0040f9401154050b0010740000024031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 981086501 1250 981085251 981085271
    0x3180201200c131401050117041e05031204230709020d021e0301090c03180f020301020d0204030308062403010605030603070302120c090108060108030f090f030f0604120203031009 79
    0x41001548040550805070180200500903103a82c4044c9100d0103c0801409030f1342ca40e0011214141040002c01004051070701281c0410401d90b2a0502c03061101214141c0942503a0ba00e4159040105000d0100700c030801400100700e5081c100b41810300310164401400750b020189143c1c0d601d12882000f000e1030380082c0e4692500309540480d484441d00d240c030052880d420b8201ca054076802485501039483c5448007211481e171290064011403423200306c41d400d4800f01500d402d00800303880707801288d00d07641c00c000d49840400c150000d17100950181c0c0b50407100785000030601500010b200d0050380f9805050402e5030400304001e05480c1500c0207842e14070740b079544131000300e843c103202904080d6100c80d82c0c0b0030118051100165038066204203890340515030341d0b0b6004a50b6503060a0003440d41070b8000b070000c005400c05803000f80920341701c0107002ca6400000680400c0c142a116480c90303040381c000340b04000c14000000440000350440f440210300e54500074001c0e0442e54050b004003450203440c1e07060700c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 981087751 1250 981086501 981086503
    0xb06190309060b10080711030307050901030b0d021e090a0b0303040608070207180f0b0a03020f060f090a14031603120503040311010c020f0708011a0103090804030507090c0318020120 80
    0x58140c3c10080c05011800c15a1803024144180c2140c0307040000345080d20f000d00d46030020080e24011005c0d608c480d420142c00c0700040d03000d40000801e0a4004202c1c1c3d00c0c41015076900340b65164003049a11300704201e40c090030188014050002c002240342802c0103403411082d1800000c503401c0301c0303462800c2002078403a094201c2c14500f49034030620410325003400303507019211160710a4900b01e26403003003003022800000900c04140058400a50b004041405040c1c10b81050001402d0221421615510b043d9000c0d0002d5007040c8070fa00a103801c03900040c1200350301d0a04104010301140108558400c252070750707031040004480160781008000011002c10201400b03004c021100b000d50360001e10000010001c02550780f0509031a1400a20511000180e864010700c1456184a25514101d0b01c4042600042d000b80005450071184106c0400c000804540180400005400d500c1c4001c1509040071340700400b0342d0342c01c00c1619240c1ca9014030140050703800003091035410042030413805031010240321403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 981089001 1250 981087751 981087761
    0x3150b01020606130c140f04090b12070905090703050f0d08071b11010c050307050a0201320a021609141e161224080606130b130f0b040b0619030906 65
    0x1d00d901107800b0900d0200640e10387d0140042c0d075102002000401c1c00f00c020010100c9902000c2003041d040300005101c0400d140e000a0b03030114000f8215000b141d9640c1d00c2c5890817402203440710f510b4010301d1007180c03915030001034260802c6441c5400103005141503034517585040c10301d03001090600244815417050340261900b091032a0050196600d40307030182050750f02c900c4111002c030300054082404107880f030380300c100074040c0d00c0145480c1e01d80c1c507450102e480080e43c4152110015840740c2402619000110502803001d00300c000000b2800c030740500d081a4907400003038062007401030144281ea800307841000e9695032048141c0300c040c400c4002c40c001643c032023504002e4100740904148900036002c011050752603040c102964904c0280d680c0c0c103406521603106030788a96112580017600358042c03c2c950090308012500030203c64012000b4240001110070030990404800d4544107000e500c0c0c9070034420080390003c00e9800501d890469020048410310340d81d41e05050560752030160041c00850781c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 981090251 1250 981089001 981089027
    0xb12030319061a13051201050601080702010e0312100b0c0f0601090902060906030601141303051e0c0d05010e061008010b1509060d021c14180a02090406140103150b01020606130c 78
    0x1010421000e06d446a002e0076040320744a001c16403d0f80411042d620500c5040f0440c01224051410442c40e0f01c02130341e021034080c120500350f0000000201e0450040d030001d01140034003d001340620701012480c00d00346541640240c2015140c81008405070b1500003c4a0900c00200c1d12241c2c1d0340c1e03070382c0f006032200d40d00101c2845800c1ca0103c0c0041c01c50901032102010b8901410465980d460041d0900c0700350f6460302c042c1c0350190030151385805113082544100300003610507000815481c165400c058a042800c0322a0520503003646010000c50000b84034640c04640e00751080c481600d01403e03d01d60034800c8019a43c040c03040000e501001700d610b503041d540c41111450725110401c07014100741c8090078002114200c4082d1b4039000c581070800b4044450811103044010b410280d2140e020400b035980020010380303650b078441911580c070460382f500342c5010358811180c4802e60710f401c4480c44103c0342c1c90280c1906561100b0300703011032582c64007041400c03401c528401054400070004200e03021400303045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 981091501 1250 981090251 981090259
    0x1608151902131e090204150806030a1a0402010806030d0207060f170109090308161d0402040521121206120a02030601031a060607020603190b12030319061a1305 70
    0x3030081a95a01212503c1ea216004aa40c2c00e40580301c90000c0101e103d0791103034000f04041d507083d0817251409422030f582d1140004060300c000891a440d4110011060207e140e200600394003040210f681001078550402401d400609100b0705d07140c0013a5403000f05c0c0c0212024010700c1800550024400c400034898480f0415240c0c00d2543e46115450180000070710441c080750260340062514501c0004e0321000001079610395404840031014030030300340380c42100c060300141c0801000c10681c0380c0180004d800344540b4020000805040a01418008041c2030075590303040070041d1081003040b030b4007981c2c1c12840807100c440706400da81450915103a010503000b0b4060007290000011b001b440501518110407650541156071364200c1005a07a10030440000d51080c01800030035150074140003058642c074a841000035070100c503000015441c000b03910088419610000c204001d0050500814001410359a803d014450038400e00103001080607a09420021021603040780c15040002040c0040c50060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 981092751 1250 981091501 981091537
    0x9040b0a0c0e061b0705130e2512080403060911040e06072f01060608090c010206130318030819030b0d050304120c0504060b07060506090f150f0306091608151902 71
    0x301d010340141100c25905402c0380204c8007042012500544a80d02d118280b20143c103186062014105422112800c2552f01c1c88041c000440007407118400e034112240521444440302141c20100300903a046002c42c03016942268060018807a00904d4030000540d41da045110b8180c0d1480c4848090485100c100d4815805c0c000001070058129407128014107400c03058413651803280006907a40d05094035800354202d03000740320f0b2000c0f0b80300b1894104210740030411115400c0d0340340c444018a4001d0351a11000c00c0d910044000c68903094801c4004030001654a40304901c05070320340503101e010321f10940500141000308c4408100b1300c6419607000e0b2000500070000d00d9181c40c100e40d801d0f0445030703040b0341b284e15180220721b8511340710200611400c0c031801e22008590310140342050128000401c20340050502140b010641e5041c8100d621808850004005c060001ca0f450040d14486612010309a0000e9000144031444518003682c0840d8141c8440c00b65210405ea03032009100c0c807040e03a11050100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 981094001 1250 981092751 981092779
    0x1b03110c070f17011e091e06061805090304050108060d1b051002210c03120103112704030f0e030a0c080601060905010509040f0b09040b0a0c0e061b0705 67
    0x2981c0c1c0882a94600310f0024100600c07516400c0c01c0701e01c44540c52108040c441803003d00e94007150420440c02d071041c2e8482d403a50000141803148640d24003005c44010381c03540400d03c101c510a03000b41e90301d20442e02043c0117908242c62075075200d00c22401b41b581003140042c0066441c0e10380c1038074419210703440000b02c104010100444481001e250040d144240030600f002c610540c8000340142c401c4188003031490100405030144d8032242d12401c8101d10501003802030081d5000c0180d0814000d5020b04030803c0e28050710000c0055142151022021107003503141c0c4046081120f100c1154019494100195144c0280d4403d407180030102400da9414812843c8260420920721001d80c01c85003103004441d02c990b00c411095450350b00901841d400190280b11141d41480d058001d419804a94a00080d10085010200f6145201207400f9250b099000b424400000744505c10403401804615188840031401c000144c114443c10341154004803d80c5084001e484082c0420001004000d0000b00c180c030304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 981095251 1250 981094001 981094019
    0x20a18020a03180515190e0a151e020d061715091908071b030f170301050a05040b0102010f050702070e060604050a060503130203030d0902131b03110c07 67
    0xc5400301d500000e0034101c082c081010716141c0c8100c40c90303114024010303c0303124400c0c0a040d034800030706000080c91a1003101d00032041e40c2c840c0000c040111405029507840c5420401d141c007840050f0490351918020f907407d030b900a90b601d40700d03000030044005640d6405a0542c1e001801c081c1c0c02038126074007440080d403c60500000d000c403200380d014803c0301c000e03510320401e151121545107007211004400a1141d0000d01c03028014880700307104810b031660427082c0b41115826003565030801c49640000800e140e0511410b081c0f54a00d620510600b82e242d503040c500030a00326a4140306250046440b038030440f165a000b9000600400070b05102008076280409009644211131b00c10341d601c1d90030b030701c011030003d00b07040c070444059032009041c3d88511480c001c0c08a840350b00007858a94080c02c0000007400594052000744228890030768046215031031401000b41d44a00ea80007010018906020380d0b80343d042c042840410052503003000503012000310b089240f103110703000c400e02060040031004601511 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 981096501 1250 981095251 981095257
    0xb030c09090f0105031b040906090308100806060d020d020121021305091b031b070b04030809030c0c060c010f1e11120103020d083a02090d0f020a1802 66
    0x80444180706540c6495200306440d20082c06816056003100200c0c0707014081408a0310b9800c403018200040e43c00c030307503114941201c0243d0022000140c01c4010700070810590002000a03222640107803c50303042c2240000c036460018807009004030442540d50055a001c5d410001c4940180b200300242001d065080c1002540a99240118080c0407000802c0e28200740562911501c01c0300f0403018000c2549000955581004012502c092039042814665200da80e016101040c03007501c03400f030f0f02d05180c500500041d8009000d040d003580305125a0180c2d01c000102c44180000c1503e925a0303402d008019280900402d13000e00d5440b42c00d0050906521201103990b900b00c000c5580304100e80c1c000c2800e110314502c59000f5010040b09400018009072030529a05480300d8841c504031407170140b8000a1500301c14040c0a841c5000ba500807002410f2101e41ea4038030001c1d002136008520300384488000420341c41c5030600c098440350084222030215152902104090185880c08820802c20f5802c40340282d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 981097751 1250 981096501 981096517
    0x4060207080c0619020a0504050f0406050d03120b0916030e070f0609080c010e01090b0904090209070f0207080304060f05090402040b1612031a040203060102011e061d0708010513060b030c 82
    0x21134903d089100300510710a9805c0d06a0713a0741c9140c035251412003008000d003481c2075920740c0b0a540b5900000c40d40d0301c2d140800e030b6862090b1104940e040d860700c1c128007115000040d143c05420803000300982c00d090b551340d2604401050a0001c0c034040d4084100346010040d420a0405400080010510704e40040212040380d2462048030043c0416500440f00340c02c03402d840c2804620a040e0502581d000c000c042c01030010f02402c000343d00d0720590002140300c501951940702094440d205d400c000da50502004003e425040c000313510300b83c908640204812400c0600c20100038000c0794a03241580c843c1c04440007001400001504c078050000a1030040f00e80e2170044a24030040100480d8990090054007800d5088514050080d0500303000d00020b5407005010303d0442d50380d01852402d8004003a100c0c00e10749001c10380040c2e076905004c0b01c005a01c9150b03117a20400350a0300c0400c100035502c00110385c1500d0050742d440740500300215501c00a000d0a400851500e90088100002c4c407500f03001401c010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 981099001 1250 981097751 981097771
    0x90b0702031b030405010801031e02091e06010212090f0d0b010f080d030e100902030a140706090501080f04030c0c180c030b0f18070504051c11120c0904060207080c06 73
    0x204002c000c0e07a81d928840e82c4a4140407406140041002c9102c0004182003600114280d49180e1502d40c0050300b04e880c100c030a10354600400d4084401c500b6541c440c1c56003c2000e00052113910003240400c2c1090290000440c8106003154850315542c95841058501ca64480c910b0011f55854418150411025000701807052140000b540c10040c440c0c0240c602e804e07184400b03001b007040d05c1442d05002d00254541641c25110762181800000c00000b00201031008203800f4203041801c100340200100f0450b48110704218030305050207500040c503002242c0150749400d2541400700d01d0f140847d8801d02c1c59008404880316065401c40c4506103411800130303903440703560400030100345108100f1526211000b141e00f0688031401003501d441c90f140f4454100e4603605000742003960b1940050503e141d03005903418400700e00000b00781085000c0d5000b00390310b40101c652104003e0b12420070380d500c01c10b4030141423066244c400842c060040c0d9504071494035030004100c0355a81030840300b0540c0c50030149d50121071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 981100251 1250 981099001 981099037
    0xa09150506310f022703060702012c0f0a0503090307050604030f23030403030e0a0905040512070303091406160311090111030f040f14030318040c03090b070203 70
    0x881941191039003920404041420411400118020003c05102c02d500360f0041c0d007000000b5190b11000c0d4425408420004110000c11107076041c103003410406081c0c281960b041c40c0c4410602c40a0004405060b1510016910441c5c00b0f02da0f20307480c000103501105214000e02e061441404030200040000301e00990464055541d17680600207640700f00d00c00544210403024440c03000500b0302410a11031541200c5040c0d20000180286045501c90341c0110003083e01c0300b103a0708890510701a80c1c0002c001280c02004a0b16298491a446541c403216240384810005560802c142c040d500c140c404035000981010000640001c40303658403425100c0d410070f51141040c11041a119000e1a000040c860341450f0034121042c0041d50a182440700981d404e01080c8030440003a69880d000e003000341001c035412803441d0b1030108075500c0b03500c0c1c0c04180c41c00f94000300a144481d030f402c0000c1c6004030380e0a40b0000791039100c441c8110000c0400e08801004030300013000b40241240c2c00805003020041c4001d0f1495 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 981101501 1250 981100251 981100279
    0x230907080a030e040e0a0b0a060305060f040305120c070c090501031a0907141f0e10020102041224291903020f0a0f0e15030a0b040602030a09150506 65
    0x15890400e907400030001414843c01200ba030600e43c01034001d820f20710080f141c4104841d42c80d16038101003192103000666440c2ea0070410300000f000860b40010500070046e0960400742c6004169204000007904050414404103001d08400c2003150300035034101c02c5804038203451f0b032850405040c0030b220580f10441c1d881e40d60301c03080146d4215030340150140ca00900c0040d203080078844441c200391450079400445050080304036002c2c401940c0c2d6080c11542d4500e0501814010407142d040800010411a8414042840405040c0041086141e00000088502c4040076440c0d1140c001c89002d0544050500200034030b00052080a1040c0d402e90400c260401848081441070a01823191244842c0150420400240c20419102501c0071005042d9088a50711048060840b120070307480f140701c1e00d80d50310401c040d007880f203c0b01040d1940d040f8090040c18215071586404800041c1000e40220360010100c0c0f22400260b2021655561108010f04100620035100c0010203085404034000c0c0f46e0b4402c984 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 981102751 1250 981101501 981101503
    0x3040803100b0c01140c0306090a0b040e0609010e15040b07080604110c0607090504020c0c101413030507050105041518050307120204180201050a03051906030f0c0b0307020c0d0623090708 82
    0xa40308001c00b40c08000b0f130340d0b81c0706c404ac00500070f42101c0c207400a603501c03120b07410005c043c8401d5210303004400000c6040c031500c40b203441c43d0200d050581004082c0c14001c0c0000610b5003019036410101c0d82c6406035442d103030f80e80041d008003041407058003110800035440032801d401107281c1f407003003480d0313102e00716555901c00600007030344240f144c0742104e60045c01c10f004051602654921003000c0a00e840307621070078491a01c0c02070358891721481d403411555040800c200941040800043c11080c40c3c039505052800c2c41103507040740480180010f01c0021301c080d030b500e882c80440c440003c020060850700c1d042d95405075207641c0b001d8048164091400c10050100c01d0b2200f8800c0d61542d035040e55030742d140250441e0220010407016020269070000c003e10000c03500e040b03008190195000300000c0e100f10107103140c49250a200c0380d0143c4d044050501c10850019004101c041c0b20200a80d0880002c2d071251400d4401003001004041044a4001c41400e0110000400f540f003208441c0407144000e4840442ca = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 981104001 1250 981102751 981102757
    0x2101110a200c03030d150e100e06040b06030402010309150606050c07080d020309011808011e0e06070207050d061103010e0106020d020115060318020429011403040803100b0c01140c 79
    0xa58160b402009041d0707130000150301c011ba002c1400c0340d1703041c1c800d82c440714107440034901903d0b41c0c41e1004101d682803040c60001d40d440c54004008036020060804503002148040c00000d10180c1070550b01d0518200740004441c0c0c9403a11300c00c0000401606c2c1e10752034098015000141e10740703004d2240c9100400c05050001d2540e102c0040d0f40c0046050150081c01144c0001d0841805070381050f0039803002035000802d0040c41540b0040d00f88404100c415108c18004442240310200c0306540700b0000d01000035004900181a140103440100e8460340368200a8050a0345020191816800000001b0102d405002050681b180e035402c0e2480c007055018200d081e104d020801180e0640180f404006090290303019003c18204100070300319548130f9800040c20bc0381b045825110984800b05042034580c490403140d076a030482400c10382c0742e03111000408161408020300040044030000041210002d00e403c03c076000304040b400c4103917035141e2004a0303400380046a4040940b41952000700d214600f880c010f0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 981105251 1250 981104001 981104023
    0x715050a18020d2324060f1813080d0518070b0a1b0f030309110a0303020606060a0215040507180203090309040f060b040b120709052101110a20 63
    0xa0001c640c013520390300001d141030a86003000c00a680400041c0c40b9081c0407a0380e803040d401205403420f40e0940d18010403400c0c003c00241c81400360030310800455a94104150318005038150302ca07156510000700b89400c01200c0e4000c3c00f15480030a840f041e102190b000303a8401c41c2255000c4c0001d130b0b50b00a099540b00390500400072915010310101041501c5500100c43e003080307020100200d4407080e00d032001806168901500021b4460180009024006400036030b82c2d4003d9540299503403071078030000e4a07000040c04051060310001003050f80c0e0307442000369444004110040b0402e605043c030300b00340d50300c000d442855440181c000c4400026003a520030340784501c540360007540c603006041040100a0161141c030369201c542c1c0303800100c0c220045201034400f074018007008a56407907a103004781c1a01000148840100162a08140110340f55000b81c0040c500448a9440725030481d035040070301610000a1141e891440490081083c1d0ba1021290500d0f01d4038807640940d030070b2500d071015150003140a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 981106501 1250 981105251 981105259
    0x1020606092d0a021209030a09030f06060b03010f06030509060f0105010f020a080c030a03061a12040f02061c0506092814010f050a06020613080307050715050a1802 72
    0xa611185048004001c0300006403a0382001d01c4078003061044050195020480140d010400d9822000045c610303940098503800158209600044004c1c1407181c07a0000034594400205107404000c140d81042c4080e007100101541c07250303100d60518180310821310412001a0800d0045299030401003101070040140c41900e520680c00d143c0152000b06180300140c045101d18000701c40415004000750420300021409035a481003541c0c1c0060070740e96141c009001c0c403050403014a4071580340e1421549041185041050555250704201b80320001804010b07402c1000001d0314180320000320207031004501025020031407600c6140c00e01001810856410410030807000000c0d408a40c90700c0d4407581d15800d2000072901e80f85084801c001c00c0d80a91100783c00000346242070295107005040e9002800c09403000b003110b0310b008406068101d4054602911964001000c100e407144600122442c154004007948090b00036000d03c0c0c001031034100e0760488514a000b84a00d041d842e0b01e520000c0c040c2d0020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 981107751 1250 981106501 981106519
    0x41e050318061b0606010f210b0a080d030b0411070209040204020306030a0501091a1b040501050a112a01050f03060418021207081204032a051c0c0501020606 69
    0x16480030403400c074060300d1030340407805000d030b0784102c5040e0450750081548000a0480e90402c0c00c0054410340c80201c2d88018021000100c1034480c1c543d200704114100c0404012402410990200e40c00020540242c1040d02415100b0440107415400c401e00d5a042502c0c01c103d890300c0c1c1842c1149500402100039072110889010030090b18040d0003450f00654010241e0302c0e1058666269421545241402c55101050b40a01c0100e40490300080351304c8482840030200440b40d550955030240304500800d8140800402c03140c0d0824400d000700b40f0386810344c6041b600b000c40c00c0c128003156001079105100e2003900085240c2013651064094600c0100450300b1282103442e007104020151900810841d07020b02d504900c5400740ea5002d103580500030b1613001604034a41002e0955051245a0484d0309544408000400c0098000d42c1c00303440c0c0407503034180b403c1c0f034407504c084498400c40e05610403075000e1111103401e0440003081d036800e28905e2140440402040d55500160b03150103040f902958414001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 981109001 1250 981107751 981107767
    0x20906011d0307180e0708070e07140c031e090f0904020607050102120406290405040606050a0b0918010f0b030711060a020417070302130b0f0a0905041e0503 69
    0x90821029071400081c00c001d040c0c01da040c0482d18003032440d8024001000c0d46880a0650001d600c100d00500d14804081c101d03040c10304c03803070fa80d60706003d03c1a00701c180207410004031820f10801c42054115a4011300710394501540b100c460343ca030405240000c01d1011081e6968442401208032140044060158221280f100c020410300020081c01aa0490020001d1600051080c801000c1803860b044460840e800c1600300402100c0c9a01c6562a52401c0c0003881d20341d40011620180390000c0c120380214031b5580c1e074034192020f4102d680c04650084000c01303000c10050940e070301401c4062000c0d03580d0201c00b6480300400c81100c0d001e200c0d158901048078424050034036900002c56001889050182c05020000703001894248100c9100844030380c082030a204402070b02d03030100801c1c4a09001400c520741160001aa9422100d00e802c3d909a03841030196641e403940010201102802411400306654030f1035404080c0c54119421102d59850400340c802c40b90541e644244000c0e00070340114280881 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 981110251 1250 981109001 981109007
    0x3160f0804030f14010501032a15020d09322e2c062803061a0315120703051e0c060721050706050a0605040e0102090306040b071407200d02090601 64
    0x1000c00900c0c190046420214440c102b02280200403140c0354000c0c609540304500052139002c03550030010103400000404012085034030401100b901d5981d26010100c07242c0c6000400c03514074211100426001491075500d00c0002c444201d80c000016194002d140703200d01e00540b4520035400c045982005181118042c0e0704224000c0c3c2035040d8188100716034504c1188400078503001170b98104d000280c175030718280329085c41130810600451943d440c65045081203a0302c000342d210f055079941c0c05a035040ca5408031a403402c101d0700c0010364100c000d40700080c00610b0a1010302c0c80b064440d0f000f0303114010224500d0b0074080b08607400b00d90000c00c04911000f4100c0005075020300441c546003002003d00150020402c40d108540c012000e02d00000b5501d8902030034170055400358a04000141d2040c000c5207803546000c1a2158456805144007410b50381e441400c0d5a9a810240c103170500c070740003141a40422454000c12441c48074501c00003a4140780c96020014090480c650094000f544040441c2c52540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 981111501 1250 981110251 981110303
    0x4020903210f0c0c03010f140601032403050115080d0915021f0b030706090513020c070312050a0809160b130b0a03090204060506030903160f0804030f1401050103 71
    0x8800d0011920b440d004800001c402d8004140401558011003c0b8190074642407080412040d8048014001c0a0303180004171914000101680d050540f200c204030401d01c50003a4000c04003150400fa06106526810701c24002c0c0706030260300241003940c84010426000000d015640401d240d510400500d0134079031004002c115150016040d88500c164561240d0f038000070b4035980c030b2542d2000059810740300c000c05240c24401ea000106004110000340016100c0340603002d01d003918000d02596485884111030700e0400d4692000e820405459107440487c0e9014005208141055562800307030380780c002d42030303440c1c100c41c0d180210180b41044003044108000350103840c110804c00200300e102c540c0c0345d0f411301440e400030744031070700080d43c0d10a02c40851406110b5100a00b000340d4285044d85010040503541c1d1103040b000c5050044441d03521810040c00908207000c50f0740c803082c0c260f03c42e40d0781d29001c5007400403600708a40281c203a01507115003c1c0140701c1d10303040b2900107919541d00c0c410b140540349004c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 981112751 1250 981111501 981111553
    0x2010914030717010b0315041203050f0a0209060409020406170a0b223b0613031b1703060a2c070903051b01140c120a0504090e07090b04020903 63
    0x4d5240d07121005113a50a00c442880603080c0d40304801149424508401d0715507040030040e040c146442e0901c941c00714000d5400368084203407034006a40301030880c0015040d000c2d6a00c00b2803105e00018011840988c0009510308021070031900750961348030004014280e6595010701d076040786001d00c489940310403c4418165034800f5a1340020030212040c0f0705040f080c220240380000c00040c400c0c1e10452011a103001ea444400c5402600060900d455035005402590801400b0031250485000111112002111302294801b60700030b1307507485c10048007225410480e00248524003005001411400340b14601c0703000030940170310301c0084d191440a014200307000b80441003040307a021804400200104506c4c0c0509000c00003480242c10090001809000342054030031030071030140114044e201d0002108554844003080d120b85600f01c400b400c50f02400380e90b00100d10b89003030210034180f0801c00300700d800a403404201c2c01e212006120042c001644903000c1100c1d0941c0c01500c0940180d24183c507400035807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 981114001 1250 981112751 981112753
    0x60a0b040e0105090a0c0f08060c0a0203130305070612020a05161e0803010f05150a03020c0c0a121502190e041d06090c01080f010e0a1b030902010914030717 69
    0x1d811490000d81c00c41c0d0702102c640803281e1141040c0c405000c03e0150b50b10060500d95029040ca90a2885c03443d00d94901810006090801003446400503000f0f200365400c40341940700c0c01880a60742e091443c0c0d1000a031294102280034682200081d50090080700c1c4001c01d80e48400b494024140290030101000c814251010300c0000c6000400c4018040c030401d02a0007641c0e11500c07541018410080220590301080c40f41c8403d64500b020940040c003510070a0700d6170b00b0010384507a203000e06e0a0404007502c41c0300b50301c803028180c042219400c0e01c3c51910038070b000c1c1101c40310061501c11248220702c910710991000b02d60600c801030800348100c03100c0c501100003a1000c1180b50b10745407500341c0f990f12188c45107d15001841002a1a10108480400000c0034a0094200e0401d1070030006030b10811b0258044603c02400044c04281598003c04440e650802030450b1080c05104010000d168002e01240011007030701d0005104c00311200403446020b401000b40c00024900081030b005000707804000040c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 981115107 1106 981114001 981114011
    0x7020d052a04270f0b0414010b030a020109050f0402070f05012304021c02030307020d080c07091b0819020403120f0c1106030702150a021b030705060a0b04 68
    0x5580707682043c0c0f1142c010b600b02900c20310034600d00a0081c1d95079101340001c00c4454210b91926449000082100003183d104040e00d40164203000b900190080c0701c18000392070100008100000000c1c00140341c002603070340f0306000c024210001e881a964840820000d10b88070200a521641a8600c40c0e825103055400102c80c80912291106a824158040e0007103450420840321040d4004201c91400382142ca0b0440c039991000700040c2040c0108400060b0720b980c140581015040205100c41c0035101d050400c8030714540040554126141c00a50b98500c5411840180003640c02025018000e0343c2840c0c1c0a840034003080c000804100e138240413840401c4203d685001e84100c01c480ea2550b130349880304100e02c0c000c200100310110179910814000c0c1c0300d8055000384200c010b919440100c400c42100e08940340e005485000c2c2958224000144000016a22083d4050310042001070 = true := by decide +kernel

theorem cover : BRFrame.Cov 980935251 981115107 := by
  have h0 := BRFrame.cov_init 980935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 980935251 ≤ n) (h2 : n < 981115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
