-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4992
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:23:30.333976+00:00
-- url     : https://prove2.me/submissions/05d107b2-1806-4d04-9163-11b164b2e4ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 897661870 ≤ n < 897841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 897663120 1250 897661870 897661873
    0x40c030b09070801020c0d09050121091e051e1617010209100206011a0c2d1518010e1506010309020a09091109190515030109150c080c0306061308 64
    0x322903291b04955140a082101c03400610032001c0014503502071600b030b464840080540b204003102c0c0181410240440000c00c81d25403200941058205d000424a40c15891140001c1c14413114003944207000304540102984e0320750440c0c0c1c0f004190413008034004048501141d07080c843c822200c0c141394020701580745420f4001104c661921a05940030400a05031a001c00403008540b042d40400c5025000322142910385a100c40c5104600c0e119100356030160800210004d04201d200e0b4200c5401d1500c1c03644803901e844088001e014840c02000100401c0c41c44210003040329450b940c000359601d414144c80790200201a501048059105e50402d002140c3c000c1d21000c0f4050740c4100020044c030729814140d0307070070403c1c200701d04c010300d8841d0803240942d84901d400300c40700840b40d03129401000080c001090f28440710000500988085c01050390503030041a034458661422400d002c1641c504000000401c00064204005400f035501903a40180082d07414603110750300350100398401c0810b60405283c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 897664370 1250 897663120 897663127
    0x50d051e0f07020706050f0a0e0f1e090109141803090604030c2303030a39031707170a0f060b090a1403060402060f0708070b06090609040c030b0907080102 68
    0x80d80407924580c06900154200d810701a0b80300d8044402d03000c0c441504403c694100305184581d44204a1145c0c8850000d07d00982c1a18080005450703030f00b1240c044405a1414450223410324140160324018140e4800a00172585940b500d085030b800e00034183c00840a2416217500041001c03c2500c40311000540184e070307202d442c2c2c01c003940c09490b5440380d501004503640005485081d6203200c4891081301600543c00c1c00007801c0241d503940700c820f0103462140a4003400f00103021002003004809200e4001042c0d1020003420001d084400c07950b02d110054400c00144480180e10840440000701e9410000081e6180d06100c80c0c06002d184030107800d00c3d820310300d0115541e01c1c80300040c010400212080d00510b070343e842a0340e0b90030b4411950280d05030020400900541082c1001b008180f08080e03c05203061a0396850400d55000482c1c295850b2500100300206420140340e48c03030b080340d000ca82440c00c0d440c0940c0c03607503191042400024204c02c4c100c008034840110030002c031005405000025500c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 897665620 1250 897664370 897664381
    0xf120a0501022d09012f01020708030603010b0a0807050d1e031d0d171b0712020f040b030d0f02012003100b0306100c02060d06060809120307050d051e 66
    0x310321826442c64030083c0c426000255424050340455404140603186c4c1e0b0001c242e132070002924500940d0440103201c10340380b1a40c2e4500003e1005000030b0340709180706a00da00f8503c05242c00c4440703083c0c81601078810b40c07030140822540090400d0855500711950222244507103001c02006161640c4003042011420841081680001c0c049082d00007140d200361035016403208100c00104080780c0a0081d00098110070004400d0794000c1411400a2812100708130740c85405918004141e0701600400c14407407083c80440c07400c0501014a0a4100d6080c07040c400031100080d110b1026190a070280240d040306860000c3c000e410018490210200c10f004560710b120b8011019881210f90014141708418045070a1704907a0a82c2c2c0101ca000c0c00316582019074010540700f050404100f0381e440320082c4100c11585401e4010940130785116640c084a50030101c60807403400f502410552030780da4040c0104000c260744281500c441d00290900860181c4a41c424200300c4a2184951840a03181004021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 897666870 1250 897665620 897665647
    0x2070b04081b030f16110d0510050709031a1906170114010f1806031e050d1e18080109051c0201060605030a0c0329030d0e0f120a050102 60
    0x100b20120366044420b803590956859200d104032000d400740c0d10001c0c8115160045003c02041545205032009003c1c03000313400003e901d9090404080340c6640c000041084070b6200d030301800e5081105410a14485402d66407000e11140f0010050a06102800006100050141c509807820403408404010a031380f11103d01c8036070441000d0640f0150700344000c0030868840409024100c8008440b440d201c503060084c40d1801503003820712100215195000480460b5244601e92036400c00d40e07251440d02007680c40d0060814103035145420a220052200082d020114002d24040d0307011403408071403c1c00906072443c3e0300401d1380c01400761503182644071410040c0007c0d0112103020804204181c098890f0301c101d0907219a8006c00e80000c00178000f095517046281c00103030817404e03141000300e410702e0070700485080600c0040144401081c660402d8080c0e040c10301642d248000113140100f4541d04880200e410040714841a0340503403103d42000d8034103101400031900e0382c0d51110095598071584600780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 897668120 1250 897666870 897666877
    0x1505070606180b090f010306090311150403090524030603030d05010f09060803190e010c1a0a060605131809381e0615040e0906010f03031d030102070b0408 68
    0x2c411540c034044580300289044451a8801c503604941c5112582c2590b4602020b403952110031401e214141c00b40c003200d910284a81803482d40d01c0d540664a900d0300e810018a00000d6038000ca015440038071003800c114642180d0207a252085001c0d103552602c45d030010034038501c90680f010000c60701d0038002250700c00641c13140d42e0840f140c0d040184001d9403911601a2280300d90001034044c010594980310984e40100d60444400c4414100404601026110145007001c01821a035070320b125102041080000c521404001c1d00c0145492803c0c405070311641543c901c854010364041c0c03088940110b9138002107410805005a0024412002d000005020040c1040c4000550000d015070303520706140c07220a0181c07500c00c100c4c1c04400158501c08844102c010320380075291a2b084895400e0340e450941601000f0070090148a4601a0520705008064242030060f0002403e2141c114010400b0030703031101406070001030805101d83c40610302c00010780240728080740201022a044c2c108000d2041d8070010707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 897669370 1250 897668120 897668159
    0x30c1e0d1407090c0f180b040303081803160b0402030a05151008031804091b06111c020c090a06210303140705180109080a08190212041505070606 64
    0x40b145002c0d125038034441520340c5042e1120004d01e8128000000d68410090b0744c4215604c260003489213610345000a00541c03003900305401003440c0006006151302d45504103041c841c0540003644c00c02301d079600a9200301240803409080c62194001140940d6000e003d40440c584d0b01100301c403000c42c0c95081e206145041241e4408000036000400201d0b00c40c0402100c0c0a24080105581312580c1d5000308801040814400d4503026010001155462000c40d10f04024103416140d803203000d2031a00140d85040320051413100c228400c0c0d0010340c6c05980005d008030740b028040700c52001d0f40d620710507200300070001d5900903001c80f40d840c503941c1040e142507450340003154000e680c1407000f05410442020211010740b803050024904201c0e041c074240c4100380060402d08145000c52189130740d00407152402034402c000b500c00d618001a00034100005030034038000404280054460396101041020490203540306143c41000e0300c0c1c48020080340b240e0300315040258003040800c801502d400380c110707261440122 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 897670620 1250 897669370 897669373
    0x5101d060c04060207051512040507170a0213090302030d11070c0815040204230c09030c120c01080a0605061903050714090f190803070c05010e030c1e0d14 68
    0x41000d41101c80d0444064070920b80080ca0101e10b80001d00540c009003911094130b5400600140191000700c54029010703e001e140208442403c011800038021b8100c41080f07500c0d80056101c1d0700507102c0402520011012540015490300300781030aa0540c403540300d040151074500b03440c03403814544180c0030700703100d42c000e80b222a5019110301c405ca540e90050010300e2024180240020010324041c0c1007605401201d10700c00300c40c1101100d0b001501c50064031042496107010402d86403c0c242006080380d24002180c8140443e105142a107490b0384149000604104c442d03400540c020103039400100c0188030140c0728130381e42c1c101c40416100012803440303030310002405c2001064859105021705054070410006051500c4407103010850400100c0041c640c0050b0801303c0c1d00e508030050507d10703004004d000d005d141d4550700c6103000d070421f134500d411841c14012606902d0100da00e0000e456142e51a003602c1c04271044a191b01503160344040000c0a9070b000d448040b6000400600c0b003a06071019001d0710 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 897671870 1250 897670620 897670633
    0xb040f031502090915031213031506050603130f200a08061009091106190e01030203010b070f02040b060a020d1b03053a020901080709081905101d 64
    0x4003a40c141c1c80f42d060800d9002202c0c2002c90303c0394054040000007048000c08440306204240c034107440c45d42002e0f00040303071008112010030510200c400003008591001000300800c60504000031021300014101c0a07810301c1c0c201d400820403560104400d0101d400017805201c50304889842590300d281c6c514014054000c1d210002004000091242d0080c403600c0d5850323804500b086148001800c092200303842e0510718031905403d6403910030050440d0401044052001c0120200142c490740340064240d0415104000410083c6d400c0403c6e1410140c0c003d407120076031000380c000240580500000703203070b0090f0009202d889640c1c0005da0040040c040c0d86036055180c550654651462448201c0540421003c2010110b0aa41d842109800340c000c00c00d80031300401d201d080781e8200100c100140c10760550001b51100c10f580c0044207030342c4c061850320308040302e170f82046d02c4643c43d808098100500c1c0300c000c180080401c601800212a4042c040101b04012400049103030b290348801d1903900118040c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 897673120 1250 897671870 897671903
    0x40b060112090c090c050702181f0e040303090303020c1b03011119081e040f0303060e190c0e0d0606050a080a05030a080c090405070f110114060d020103060b040f03 72
    0x5001d184003480d00491107181c1a4a41448800a054040101700801c2020003145005940759041d1800c002080300c00b01c0300c5480c201181c0c0c65035102c1c1040041506a032040104090082c0e03600981e40503034181b84c046002006880e05801901030140b840380039001c2d4501c845007817801c0e450f05010510084000340040e040076030321901140318402d440c03003c002c2d40845000c003890140900940002c40d044507548a280004403004031200f00760350444440040c11303185020b01d41e040c09031202038810a0380b40003446c101440302c50100d110401021b68503549842d4180781490040315132514071034018040d0000552180b900500900e598000c46105400c05440402c0f0841c0c00654524076581c00ba00030740c54503200302c0061303034203c40003031400344a00002c014090280e00c80307000f805d0003509a030700c13031500714103c045c0d01070003d140aa450013520f82c5407451b02e051007540303040c0c075580182080d81c01c503c0000c0d4900040700940442e8012081000c00040e001583e490000c11040440b0b018482c0d503103852141 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 897674370 1250 897673120 897673157
    0x5060a0c151a0f0f240c3904051504020d02091509150706090602070501020c01111c1509140103050c0a14221a010e041407051e03040b0601 61
    0x10f21150000941e1400c10300c182070000945040c40c803d02d0014172007000001d040c560b00c0e4000034100c0c056070005d0030300d07004030614011410001c40d012842c40e40c440d0208041503101074180c03035a55100c0e40e101c002150342e1941500c41141e5420000d0320a6550b03001500480700070703501500c05540555128080303007480c18807050544814680090403d096100d00f0a28800c094011000a5070500d0b603c500d024002603842c40200006813142c1c00141e2074201e4a04590b0071602d1741e14400f106000d0404c050741281c042c150540d401491500790024010410114013074800c0307200d0700420305036854018911603007401ca100030b030b04a920410441c0c007014040340c24001d444001d481805030124030014400400e14000454402c0c80018a102c07560f01c0a82d903002d68191408180415440145400642034950b401004010040816141441810601750390a00c04400040c00318040110200f075140d203069540c9840c900a06188030240d0712420b150a0110b081041940e803280840c0901000c220700004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 897675620 1250 897674370 897674389
    0x30601080304122006040e01171c030e0c120109120509060d09240f1d03090f0a0902040305030d05061c120504031406010515031005060a0c151a 63
    0xb000d28240c003e022580e5204440348103108000341540e072440b061814913403541009003000b04815242e06841d035141016890400030b0b42c0707420503030f503030015800c43c0100252030380792aa0034022480d002035100c0c210680c69003419030f40e4840030350000842d0408803031350805421202c9601d015686042008810040640b407030300c00c840c1502e070050424001c0d5003900805500650003140500107440c0d0f2040c031704141c030018142c540c5083d450650380e0f0040b142401c03168400c1085160300b41070f460013444088803843c0d9407805420140c3d881a20b01c09081c02103600c607030555000400100300c00b9500c5070f440e403919540b20b401180000c05401c0c5003500081d031746d207800320440740d50550758900701c04030343c00e02d40b1018031482c000ba80381802d1210801c80000014004e0070a031402c0c50b108400b0300002c3d4104400c201d030000343d0b00c5180c40011014800c0c0000d881c442c2042204440b01110800c0d903500140509441040c041c03000541006c0101902402e40c42c40b5400c580100c0c929806a5070345416014200b10b110714 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 897676870 1250 897675620 897675629
    0x131208090f0d0f15020d05070306060801090c0e0607020411070506160e0904060b06090a081018021c0f0209040b040308060a0617150406150e09060f09190c020c030601080304 76
    0x200051100c4082a000c07500c0c01031310064600c000d86070450741904c410a80c1c0056038402c0000399905010045190b0004401c1d0242201800610609050313100040486075030860b680d00c5508002290000c554640d8007400784090902d00c2e0035100d03403950030900d45680c011600c0365400080c1c02162110380348a140351001800c0002d02100060310740d030b1a580020030100f0302080c2c000108200b0170405c0d40d60514542c2c002d0607040d00900103080990b05010039102c4003c4111103594283e00c0703201c01a55a103044a0b05004103114244003810b0074102821825123001001c1d403c01440c0341400140715030317401040c2c840d41c06502c81044d19100c201c00e0025100b998420400040c0b0180c02c002d5414030b030f005401e90012070b100f4601900c0606200090300301c40c05036000103001e00d0120042511503400030701499191900f00c40300e82061500c2404646500400d244151141104c040080c1400c070351911243d5000526204c10030001c5803101b00a50b440f080940801d01ca4403c101c000640d00a0000c01c0317a0030f45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 897678120 1250 897676870 897676883
    0xd0318140108150103140a0c0905030d090506070c1e060201140601080a0b150309030408060a11030114060c0f06060411041203050705030403050d0e010e0f090705131208090f0d 77
    0x6a0b6490748641c0f01d641024510380c105038807514080c00041c07244140b24000e84c0b80d8100021400080725001e400f818140d0301542c06a0801407000e45115048012075080312000d64165a480a46282c00c20602c0450b4000a0400d2004030b00c0b014120500301c145025102c0d032341c00800c00348802200e00d9800210403a0001e000070101d070300007240084143c01003a100d0401902038280d00030b01e544440302d160402c0369561120352003c141040180c40810545821002015040080d000301e038000406070b01c014010800e0208583c0c4c5d0014954480a088a00c4080854242d4a050211044e070b551124401c1d640180300314288041c9200d4821410211000c807074000c000c00c11203032032942e000c0c0d915400006040d1000d0009000000101d003017400341e8444200d0aa54003801c091680001400103009012a14021507042e100d5a03259200c0d081141e0304000355061164542010006981208070350340c0004d45044c10500d894420481d0700c401a02000004440018142c511107060110720194000080c3c0031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 897679370 1250 897678120 897678137
    0xd0501061805030307020916091208030919080307030209061b07151d1002031207080403021204060512101a0405090108010e0717070302041803110601151d0d03181401 73
    0x20ba000000ca0f2a03104065403c0c6100c1c11039a810b20ac5160428100050f240c4103000030402130f103102c003409146040c801403d05200b00081c1307910b80c08140d001c0104a4010302d50300191589056840c041071300c014500038140070080007140c2020340c2c1c54605901c12541c02c2e5081d000310401031409094115491241407503903000c207141030380401c403541c48014110350650204109100042c0305100e0511320445a03900c0b400305d82d0070f1a144c028500026024031005900c410f0009110551340503049072028a203500801001e62030f16100a51541c00c903601020018000303c0b0390080f0b20381404040c0044076070444000000e6aa9810a1401da03102c1700a0242560803082051080f0710340f415410b11600d00810403103088035165070200c0c0803601101e6034000d200e00c0b000c05120800d580a00c0050000c1e016074090b20303407940350414040071601c904c0380d040284640c060455403c007103800e212810282c0c00401c0c071421100c0e682400340c510306c221050b1090001e070344400410100d504042c1c0c4c11040b003040e51000076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 897680620 1250 897679370 897679381
    0x901020c060706090605010305060106110d0503160207090f0e1009050d0f03060801050a0b1905150a02011b030209180f071b12020d0e0306010e0115050d05010618050303070209 77
    0x1015400003204894044c0c0ea004420b02180140c8a12800313188503100800d0301c0d50400102522040d10b9180303540341d55100300407698007160301a05403508039079085403e0b4440403040d07034142e0414003150070102a462070710461080c07170000ca8002ea510020490155114540d4500801007030720300314840078100354002070010142a205076403010104090745000a040c0361210a90b5007992400d884099040342c0b14200300d12a1f24204940d58800341c140781504070745500e0070000ca01c1071520340f400d0b0300c0200070120b031540b0030034000c0d00012110780810b074020152055000700a4000d4000807030780e6000d01c0d200b89240c1540e03112404054005c100c281c03c007001c4c940d40c11350219142c415038103c0e601c40d10ba20701090800201014021030300361089030080d048014403090002c0012500d50f40382c1d0b102e50302610040000d98000c0c1c080e00d05581d5499903400c0c0425540606072624416081d00b00461440d142c00000c1c0f003a0b1007410f100343e5940e036114280a25030340308105a075900618201961007481d5401089 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 897681870 1250 897680620 897680629
    0xf110301050a0e091c03060f05010302120c09012604120504060509090406061d180a020a03120302090a030b06010201060b0405060d09140307060e01150305060c07050c0d05031c020901020c 82
    0x1a40118003008a0f40801c0b0611082840c405d6603050010129032200400c0c80130008500580020f0b0000b0b00c0c0c118101025200b6034070105001801e00700224000080620b29641714000080041300d61403003098404c060010707458021502114240c80d841e450440b841c40b941c0c401ca08a4003160046d41e111803e003034412041046800014104951450380d9202c001f03580c0b9080d070108140c0c800380900e150300c030b89803003654400c1c0303004101c03403540c1305801c0200d0400060303403540b1600040d039801c204551242092054190020702c1401c41c0e080c1e110b229078000008000c0c1d20f8502900c501d2080e0b00a200c21640d4081c2110b42e0300682c09081da0260050100f0040b5110540c003e1844074018140c8010f46070300411314500b1907000850560304581c0322126240482401d01a45074840b55032000b11100c3d0f0b01e162100c44d15030344050039041c0200000101c003c24018204001d544a81004180d41d44650709882c00c0c5541394058212101440003110034920800901d2017034030360054068014080da00310460410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 897683120 1250 897681870 897681899
    0xf0b0d0b0d05030304062a0e040b0a05010203160816051c0309030e010f030f05190b03060412141201060f020c030705030d11070e04030c1e11060c0f010c030f110301050a 74
    0x1214a81004892647d40300b01d122054441c10b070f80f525035a00c90045e0009220546038010030f2580a200c8505d002c110599001044403039003100d2490703007a0400a5450302020f0f174461001040081c40d40119008180300b008030f84049000012003a00c400c0d0000400c0503000c0c0d075030b50000900410340e031b002d0080d269402484d803540064540d18000445000e813002c84411110300b0b4480c82d514010900c00f906060f00d80e03104038040920210000c1041c0d14103035583d848810321840d0000200480404140e210903810829200f1500311030004101568607403000422000d9800d00d008014414041100e165050114022080d0303100500034100311203548100340c40d0004e0345c80c07240e49a840b400701c0003d4100b092164a60143d03109540300f103441415404c10f980d001d5440784510482d1040e40d95014001600e40c0396802d00400207907000f5469482004103035003009a001c0245c1055401c011460034642e616520004448145003c04c00240d1844500031006000c240136041d007024500b007090040f602c580400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 897684370 1250 897683120 897683141
    0x112050f0406110d1407110f0c0103021c0e0a0326150d05012307090b16060e0307060902041d06040b150a090c030c0c030c0212070f0b0d0b0d0503030406 67
    0x190b0745060130000c003110840d94248041101580d00c00184110140c0c000c0791204031400080c0140b8000d0290100c05032608481105103040c50340c00a061306404460610080001400b504200700206203203001c02d446412200040340014851918070041021415651064006000b0003000c2a5216040c40360000040f82200d0380c000c01700c24282e07000410034010172070200b0704c40c0c0c0c2003503800c180e902c40640000800342640703051121455081c064044485e003503c0714803824880c640861101030420600503c1010404481c2d8003000440c6400c1c072041c0d03004124454420303581041071a030751002c540355800070b88107516115003099011401140000c1401c2c1e0700001643c014182c103038202d10004072110120780c028801c10303840e01100d12580c2d8162180c10240b501d18209080040b11a82c3c0080450242001c000d12415100010340075100c41001800090301c052610b0134a6181c40c0c1401c04115000188030111803420107901c02018200024407185080d4044001c5056403101d03a101005070140000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 897685620 1250 897684370 897684401
    0x5010c12180b07080723062a0d0510090506011407080d1409010606020105010b07060e1608070e060d03080c21040c061106040c06031e0204140112050f0406 68
    0x40100d1880640002404000d01c0740d403203542d907580d880c906a1b010b04805125090000d0680f000600745100108249500440103868648080d282c810403403103c505559003100c68000102e002d400040040d8400b07800390200200301c44240ba81d801c1d290b015988201c400d140000d100c10399009a054101025000035840382c51030604062080034014120351a4506e02e40c004038928080c000015001e00c1050003801240c4002d11466040114040301071141f01001054a6542caa14910360103080c40300700d07111207030319941420403540c4001c1c0c0c52b41d540b02e60050020301419640411207620b80100f0b003042803641522045c0c031550324851a440e894018442c94804841244016140c81040d07401103882503101b010500402d030b040101c000c104658040303141c0d20f00c0c2d10900034003001c22140da4000089070b41914003c10000201e162924858866403407803400c45001282c00324903801074011003800610282c0e036101c1c028402e18a1801601c4058401d00d4004411001042c080380c400e41214031048144072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 897686870 1250 897685620 897685667
    0xf1b0f0112020708071a0c04050d1401060605130b0418020c030403050a15050c0a080c0c120331030e0f04140a060906080d0207090b01020c121605010c12 67
    0x1140c810707644000800ca07400d00300010290308001c44240825202d03034240f1071b0860301d03250403440c0320440e1146000c0da900c1400f048406c08104200c0e40801030040c0d4162000b401500da072042d000e49150040b00316929444071201001c9400e445601c15034048540240004482400300c40900d402540200071191860108110110105808000b81f88059119002c0300c140303082000103035011a0800340982030030760410011015001d034424404c40d04104044040c42d5140404a13146140040b551900c1400314804020081800c01111001081c20366143ca0344240404000341e20880b4000d01c140140480e1507030740c0815a509060804144000001e400040c0c0b0814078020140d00010465a100b00b075501c46000b441a05454090b45000b060204c006240c9002c1d9400d0184d202c02241c0070318002607603a101403c02c168420080070720b4080b406806404602080c051154540540941d500b1901e04109800240f0354443c1d10f55108542c0c0080c8504000403182c0b20881d680e104580d80750100c2c040c00f2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 897688120 1250 897686870 897686897
    0xe0a0207050d0f1701060503041b080f0f06060909030a261611011802120a1b0e0f01030b01030b0a0e031b280f080c01020316020f1b0f01 60
    0x1004820b03105a0720340c445050703622441e071000f810303941c0281041040c1d00c9001300421403140c0010503030303030000d600000942c039828460030b120f00c040050313034000804c601c54130224982d40000440c0c0340d5150303109842a10180e83e15001800350b107080590340344c14641d01c20080380c11164030032030250100180180f060081c0075900940b040142300161540060b005c91903103116140c0b90064505680c2411920090041d000200784400e0a02d11218000e070003180c0a82020b442000d05000407450b03640c0c842c00b000f410703040360b03140c4030307103500c04c40c01140c4044a10b8408908004000000ca80c122a0f1005454580d80c2c01d40d40c4222074401d000e060011019180c80c030030102e0300c1003400500004289d003100c42c00c160b0340c1203218900c0d01c02003c141600a000d00358242101095401510000307580203c40b05001b01030b585001c00c200d208129a101c0d41b9403000c0700340089044214203101c0128080d500b00d503c070005a42010f51980c00400350003440c420703066611142ca0411000030703800010b05041104190a48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 897689370 1250 897688120 897688123
    0xa1212091110110615030c030d090e0901021c1d06010303020f010b0d020f01050a1b061401060531081b0a0b04080d080a0f15060e06070308010e0a020705 67
    0x19100721040301c0524810316460a00b19140c1800e541a89000040800842d4040351544030291a00600b6604412650841e80b400c101f8070306c4a85010307003281c3d8800f42e48100184500500c1c003696160a2503400420b1100307105009441681c41180c00d107178a010109100700e002040c0c0030141c001c5880a60600552000b805e005540c02140a5009000300c0303e1601146400c541c00761000500c9a41c41300852809a2a0002462500031081c00c0180c0d407803c07401e0003961101e10f0f03d030100b07918599001c802c1080101c00c1d001003070245034402d10b101c2d0b145d8803801d003940c10380100a003c1e075030b42d19403c5036807071100c091b0070351000d2a8194208110005032101041c9080c00392069200c40c070440309801055650500d12100c400030710312068880d00301400d1101b40e80d114a1f0240140342000655030106074040b40e5544034a040e04034418080000c60050800c90380c0180040c0310740800305115035825030150130100111092158942e4030620340380c1c20188080c010020160915640c20390034060000000c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 897690620 1250 897689370 897689381
    0xc0d2a120303050f01060903030c150b100c02010e0a1419090c0804051c0212030903040b04061d011b0803180a0c030b010f0b040501050a0311030c0409050a0501080a1212 74
    0xd990202e154a040c613808003011806034422010050760b04820800f00303900ca1400300025520405241e541c40000500b040074001d14200c8a41c00040c202400c01030680004a8801481c401e80f1212201c8030b04208100071010240314103001c0b04030340100c0c2c160920300054041c0c0e0f020905d800304414945c846141c0401c641030681d0701e40106480b00300380014450100010a00500080c030800080c20407814000d48508103544017003551000480451400d04c810f00540f0040e005444101e03480382c4d503030000144004151001122000d03841031004e4429403280f6540385041d140f034000c0480d044402d0b030340d0015135400180680c1c00c007000c03401d21042170002406041e000600412804a5036815424444691041030f40000505040d2038070801290000c0015a81119001d003011902c40c141903c05401814a400341d0000407480081000448600c0c94054404d58003d0b900400090b52040c6111080340c00030f003c0c82906070301c155900c40008041000e000c100c1401c80c0741c10100c02c0e1000c4c80d2074007641d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 897691870 1250 897690620 897690623
    0xd0609051006261b06030a0b0d3002071211040f0c121803031802090928050709051305072c06010f0f0c080d0504050c0d2a12 55
    0x50040c041140800f080b600e02561140030a40600040443c161145031907801c4040c000340a08004000140028020341c01104050409849030406860b180b078044a84003c8034001495890140c42400310001090950803100400e81c0090001e0303410100c51640c65810000d007141c0d110701d1038207400000d407600d0003003505c40b1903031003c01320704581c004401902000c07905001525440c40c3c401c1c1802c20002062000e81c1d01c039014180006c0c000140d000e144003d2808010280d0020095000d01ca4540070008684283c0700a100c0110f605501c100840124424941c01c040d209600100b001d00080300c8a074812608038050076030b07042440581d075407400d06001056000c0403510200c41038444008000740141c15405100002600341ea160440028120640f142a0300d03040003c0202000c0c0c0d994000c100781c030788a80d0007402698581d00c14101c0c01020784000c4404548074090181c55145a007006040500900d82c4031580508035407428012190780000d00c0c043c4c51040707070007003c0001c401c0d40350003100c03c640c2e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 897693120 1250 897691870 897691889
    0x1a03030f0403110603070857090310020a020f0a06020a021b03030a030911030f010605150f250602040909020f0316060507020f09091c0e0d0609051006 66
    0x180d245043c2403261071001904107008080030020044841d0388030502ca5480304112003035010f2950318046d0b0300c01d850311500d00f100c0c120a4142120004004220a110401001841e4001c6444514101600500400140340d40540c00001003851243c0c654015012501c9940304480c100103c001d411850724000310b5081d900b0640c001801c03041340394140f081d11065040000c45161265220000c01c0d900d1107640000782c2050b46d2221403004019032040303d071802c480024203c07400d0620110559000b03003034038410740f8070680b0014912a40501520150b0350b104110344076017424160000c21011a41c05074441842020f002006804000b420342d00c06000604032a100000e203588552041c80b00041c07004a04078031a61011980c02504208642c00c40d007134a21a2038040e490b46006c0c808035507911384400c4070326445918030003002408a0000f5254054684030b19100c114845503c105803020600751003010303000003044861801149840d0060401244900304903582182c401c102c41044038225041003501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 897694370 1250 897693120 897693127
    0x203030301270203010501210f15080105090c0102060f13080403030f0e01091802071a09010b19050a0e04030512070906090602070b03150613090c0305090105090a0201031a03030f 78
    0x50342d45428031800c0100200b0840c9194103103000a42803041011008602040b11000d2a03081809a046024503242160b0140290000780b0b480254a5006008820003586044d000a2884a002404000c0080d041c1c001d825140c450444107120a5002403901c1136804881182c000000d400200030002540240da5110700c99802c0880201094103d00455040060002c0c0921403440340c0c03040c0209641c104000165035000706e10780049490f848240410f8199036941c1006040d140640003060405021901c1c0054408080c24000c3c405001e0700985800403030740c003002c0c484981000000c0703402a0003401c0070748c1080d00b03503280d5101441c07084944000160030f428082011981141084014100c1030016040709811305131002d07c1400b00034004460b84040701481b0b2400e03162a02152a14507110244a810f40d4841848102406001403c180041d180030001201400306110341d501510135403024014084e91500110080d202c40c4004205176640d10208184a60b010801000c060000d074075810f84 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 897695620 1250 897694370 897694409
    0x120a0f03030b01051c0b0d0203011103010302010306050d0b01090216020607030c1e050303060603180d020304030b0f0c030a05060a091e060b1e13030c030602030916060e0603090a0203030301 83
    0x7900c0040c400103050000902c42c130700c1c170140407051074214015101000074404108200090040307514a201a405500e04005541c0d004201401141a24000e80381884666079440522a080750580d201400ea0480b820050102440d10b0300100b003c03800840320351034005000e0300059840c0d8051101140401d00c0c031305515041000700e07a604103090201941283c0040c8054550719100d201c0203000340e02c41c62000000410000c0c05490306444c80d03080604a5414500301312000e503582c0e100d408181c55400b00c440025580340c0c90452000d209803a4041d1050850b00e44120410207000d0181c0050343c0301d01c81c0744000c20b104045210342c07403040c1a242c880c0040c4030f1039030400300102c0c1c91f0740e0452075141104014440c805250344420b525100c94004400f0381d12030903906801e41c5800950002810180140d000005004450300594001c0042100f03071404108580c03005240041e26201d8100400c020ba190301025190a00207583e1000522040e2200a60a540068103581c4240c1014450300941402c0b0038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 897696870 1250 897695620 897695627
    0xc0403060e0114011a09190b03010e090c060f0702010305060a1703120c120606030901060902030a09050d02012007083106031509051801090c082104050f120a0f03 71
    0x13070042002084a4031605c0c413051007400d10384558480507010340304100351410003800025000300285003507007a450303c1c2c0d6100c403030540c41c0746010744000b4054420a801d1088030b180200440d08640c0d08005514500070040c0e0040d00038101c02040c00c1d602800310000056401c0a240d00851800217410145070342c0e107210503695030114405480e00007100018030000f180b030490500002e030400d1040325060380700e070b6410f000071b0b0240903d03800049145001106020802c015a0090b0090300e201e038090f03031100d03915682c00f01e0803124044003d032806503100304651600c601200041103c94000c411a5103800342c55114034041000d0810441050203000050038880b423801c0307841a010380001d26042c019924031040c444081c00d200d000303c0549554a2000c169195404441a00510f400d41c009025440081c1003480e071310203040c480d0800c18080c2860142e80c601001c00076059039032500c240103047c2802e001c140b2200d445032180681e0130400501e95000c8180040100e90000e81c414064041841001d2400070f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 897698120 1250 897696870 897696911
    0x30c06090f050d060b130c02011a04050f070305061809071d0c040e060111150a0e010204080a0602070201142803060510030e0115060903110303031e0c0403060e01 71
    0x107501003504140305100550b21a01c4581c00c03903070052000f01d01c101510000904041c400d003121000c103458052002c0c1202d0b0190071400c1540312001071148562250070501c0203541080701c00010003905200001c10040c000e5100c50740008018060703a174400c6007070388191162401a6030003205584006410880c2d42060200c2e1000c5011070442100e00d401c0000d0004800e00950098030204002da20004195034812205031020380000d41c00c88000d040c40301070040d03044000380c5150070040d043c00001c2c5a88201402100e04450303d58005085406898480000a4110450403410000a01a200003424812000c0c0c1040381c00340580d819001301d0350400c01c1c45602481081c80a02d8140107082142d6a2031000546040f1403074180070a01c45916450280105808d10381852007448041e00132034015400800c00c001ea81c030074082c41194840c6c540c2015524002255a40039104010100058628007004c0c0560040e4408041030301b829101d540b04800c3c1c444104245c04075070355411601c0445e15060441c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 897699370 1250 897698120 897698129
    0xf0a060621021003091b060f080c180d05030705030a180503010915050a09140309040501050a03080f1b01061403151b0c07030206121605040501021f15030c0609 70
    0x1c007240210741d01080f035905440051606160380c0b81001c105202e20707503c6060704944407089540c407180c0ca82501500500b10881e10200040307801000840c001000740c100c2d08500c071080c480c02c0102c1401c400300124400c50700c2080f0b40f507001c1440fa0200107803040002d4000303940c0070340b1a0904061000740b20140c184840d88218800da05020300207001c21407900080c0110201080301244540c0c0c2c0598100142c007800d00000c0c2924540700d00301420329030200c054004920701b00c40501550340d82d08104807210100780005424450108140b14404c4549002445102507003840c0c1c9510360305070800c141c02c603825984846108281050103042624040c001b1503101040f481141003181812000e01c1640d90b4032164080b00444006185000e403c800c0110b0002568002d1106a03183d5072107a2005802c1c800b60340c0200f00d180c480d0700c00c44246000c3c0c401c0d1002d5903c1030b402420244111031404c580a000d08010580d0072f0307510662814600603c6424002860240200c40c003428500700c0010170581c0503501c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 897700620 1250 897699370 897699419
    0x303140a1b0609050a050705130e1e10050f0106031d060a0e07091109030f03030c180f091e09010b030709051f030c06090e070c03110f0a0606 62
    0x9004030307800054991504509559030510a501850094018a10303120082d0641c821180c056082000006202c4255402507450a00d00d12001c038024080d03c84160000c61030b501b0500031074241c0c801d0010001c04441318041283e00d0140c901c01d049041f1802030703c40079109003030b140040c40381c02d805010350005000c1c014001820f0a07888100d1030340360303403000c2c001007225030301c031030804071540002c000c031101400142d9010403c2c080c012107590983c1d4420110f043c024081c0c000d40c581e4584010080e0381c420810710040c2ca20300300d0008501c00d010328100400a034052414540c041d41c13502c1d001d0b543e9125510440754002150800e00540320400c40041009083d40c0c10000404034648021982c04201d8903400303800714043d1610003603020514a10b440c5403500c0d1900e50400028006c1c1010403c007100e03107685a0001081c0c0303d003110300542404403140f6002c00c08101c02100003902c10300b4040e03800c90235003050b07500d126040356034541004011403040c4c4080340c072564140700508000034104450301080300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 897701870 1250 897700620 897700627
    0x61603050325081504060810020304120c031b0501090804030b10090b0a03080309010605270108011814070503030d0b01020f0304030c150c080d050712050402060f07060b0910030314 79
    0x10b00207058440c028084156081c0d401c44803441074a0b10f4100d40054607032a4292001c486203420464000d400451b001d503002d641c001c0d034406d102c0780a00c6182c002c00c0d4040e0b80304201c90359820030107000807180f200201d50325903988000070007113182a40a003014600c02c40c1c4a89003402c10081e801000102c64010b030b40414030388405d40c04103544030840f1404503035114846585a69803180c4140c01001d89a04c4150801c0c44512041001c9401c440c44664441209928020603600c506805088449040c04180c01105a100c403001080070701c0d12042c844004202265042a11400801d013140c00c02c24161079800e890b81c142003810740e014407900d81c0c0319a8103401142040d145407105034000d2501d100d6030941c0600040740304c2040d44261306003602540c000c60000d503180e0702070a48100030a8211800b00c0000c030b9201c803105000d80c03a030140501540d0010b01d01400c0c01e58100c0c501d02e490340648411100c0581c0c40718104d07107a40310043c55a00c110700c1e02d100201080d255040203024000300c80c848844864081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 897703120 1250 897701870 897701941
    0x6120601121103160c060c0507021327210809010b01020a1e03110f06040b1f14060904090b060411030907030f140a0b15010c08040506090616030503 65
    0x2083c0c9500c0f804048480c84103a803852401d54480b1200c20002d080903041c1041740b202c140d0424010190306200b620740d41c8051003850032000c11101e01c002c0d0840c000102184214100078102440d13074010b4001c081141c0301816100300e24441350561450320b030115500c0c0301003200200081c400d48000301400c0c0042c0c106101074ad900d104000c038405800c5110210704003c0b03041814800c11110b0f000d5149001200d00d03808900c0c00099940300c04941c01c0f207210400078000380b85401c203070f2056024914007007054a000741c03c0007810040a488603040b541c100000348801801540c8a001b004045030140540c41c0c1141040700c1884140d80c3c441d0003111180380104140501c146001401340212504500201104c819a180500c400b139800c150f1044544a0b04a8000600c11010426401a1469201011562072100064581c420b8900014100d1041030001300080d007840401081c0707151340204003915141064408101c14407007903006400080d03011082240042841c0722500c3d400110b0400903c030540702 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 897704370 1250 897703120 897703151
    0x801060f0b04051512090f0601060314180f100209040c020d1b0f080c0d09081c1404080a080c01050615070f11100c030e12030f03070c020612060112 65
    0x714480c10780144500c01e003405009115000381d07440c24146260f40c90300c604001213060787c2c0b03c6e0718059070035260040c4c070000203096009200b2201d13492a18072182d0216521120141001d00038100c60184a000e480b10354048481d050068003a070480c2da0307500503190034900d42480116000010004150351026846101c9580c11180031403498070034001c001407020740c2d0301c1c0071002c800307095030018000e8402254007402901e0204a2144e40809540c81c40c1109a40c1c846050392400300d49503c494600240c501500018816050006003090443c00b1030700e00342e9210384051415820500a0b50300d000003107003039030484600b80602d40e0010001c441c84082c0c2e1540d20b002d05000c0c03003208001000203980c100d0040c200301e000c040000f201030700208030444814800002411035900d05004030001a0314580820403460610f68080a03004404000d50500102140c1820aa440a004030052020159500340160380d200010f00042c000104403443c41c0c1410b60014110503a0315000390710b06820009000415040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 897705620 1250 897704370 897704377
    0x606081803040306180516030305030c0904110a0503010f0801060311090402010e0d060506042a0e0d0b0403022a092706091e0607140a0306090c0206010801060f0b 71
    0x80881080e044840814000d8594450b9900042c42d15040c200303010702c0480001000070300180561706882e00710000641d1028158400d010050100384140045811038a15802030044c040d000b1340002058a141464410300350442440c010008600200602124201c00d005100801010000784182400e6998070402d180400400c50700030018040020190380c406c0f05204943c40c0301420303c85924615044c060003801044a034580030760b091540303400e1600344183e20520500364021110303001c0c0b084c0c090200d034681041d440c2c907070b071105800f100c82c00440c020030380325800381c1e1098000b420b0300f48054500309207204982d4020000042c502a40c0242030b100d036141c02d40d01010701420203220101036030300039004041c1000349001e58483d5504002c1060400240820799000070305d001c046d004030210101d070b583c03c0100ca0200000e528003c2201c13a14414802403c3e000d019824042078441d226a1603100f103a01c0c80000c00016400a401005001020700c0b40034041c10b0030440c00c1042c02c0c140070580c0a07910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 897706870 1250 897705620 897705631
    0x1d0a0207060b220b0d20041103070e150304031707110102070308010305121608092e090e0714090a03020307030b01060e0901061205090c030d020a0b0a060608 69
    0xa400040c01001c016041d80a182080310052010f002821080b640e10740510740808180c200a1400e02180c1491811084903885283e001c00c075a00780540f00880c03881403052298105030019191010310b05549095405188500300d981d0700d22103401c06c0300c0100149400d0703003280c1c004421000c0062002007039003c454013144900078481202c0c0758449150450700d11065005040c00365202249400c04c0507404044241224003030301c1104c25070310600102d8066407190f2103900c0c0c04029800d11900006074001d0240011040061108160102d074403442c4003803100501e014588001c0205000a900790010031a501800d08a00083c0071460403420142130001101e040e4040310802103401c12440d030328144010060b5030b01409680c651903403864441c060310380c20700400b0003007844425103400e0390610a1903d030482d02d00e135959102080c0c0100c00c1d40c00030540a0940c82c014000d00360364549a4808002d0340203001d0030b0f41d006084401d114200140500c40103419294501e042100401580b68071110441e0040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 897708120 1250 897706870 897706891
    0xa0501050f1030020a0e1618050f090c04050d0c290a03180807081c09020a1503022107030f1503140f06090120030405060c09030109022101061d 63
    0x100658000218040d220f07502462480700306d141000000164035044c5002031441d03032200c0303e0f250f5040041111008490007100d03040b031080c402441041c5044070035290003420740c181ca946802d40754400705601c003081800a4524070420081003280c400c01141c146c0602e484220500c1c072421a0305d0140d8070a00c0740c24044409c260b00c80b612002017806060142840e84d0740651804c0d42c070051071420b042981c00469500003080741004101d003d40d5824061820942d038024a8000030301c2c2850014110580d09045c0101016400e010381d4070700c802011540c140b180840d42c8031000764508504000c082d070310b0f82841240c0341400c100601c5413901c01a4081000c1e030341d0007002c040118001061161402040480c65000b522621061050000c0e040d0f00600e20850015125564104100c00182e424030090300d00620079404080007680b41c1403200c002e829480790050000c10043c0307564001902d055112011001155a00e051809041800340304800007040b440c034145040302d221086c1b52040480003010300400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 897709370 1250 897708120 897708209
    0x3080c0c030904091401050906133e0a05010323130b0f010e0610020309040b011103180a090c0207121a010b0a020106080f070303110a0501050f10 64
    0x90103814000d42d002c080740034004022244072802c1c884054803206030302c0300f4294070748008a1155880410014070030b038840036084514120560b242030a0801040d00480c819021058101d081c04851042c180812031513170410a122841d4410442000b0303150340901d050501d03194220400140025420071044803050442d1a01c0d520149070242d8410031450040c21250f1400400c503290000c0203a10b816948654a0700d1455960681800071103001f0411f40401340e80244219002d034580382d08425594a0180360000309140d10441292440e044541c020580c42100302c8241c01d1400c1c002001c02c01022029424890380d13501d600301039111441c5014140088200c001c028045c05081000b8a800710825102140c0179a92140d004129800581031000194242800000c02c60000602010145017440c090f000d021700e03566041c0c5806503415036200c0c00c1d0046112000c0070840a118551140714540200d089902d41003003494115401a00314240000d2015804002114905078560150540b411040310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 897710620 1250 897709370 897709387
    0x1e05031509100906121202010203060105250203030c0f21160305091f02010c020706020c062a010b0117010602060c2802160f050d020904212a03080c 65
    0x1c1c407402c280c100c0800d150074400002035008004030b81c0031080b40600380c5a1403228600354100c1c00c3c1c3c441540e00a0009005010040d000c0451001806034400c6114001103104216404641140c03c04160119286c018030105170a1b40740600290308158010800c40725042110300d0300a1160044d92034411001ca0b42059020402d80603000f100d1104100600c010a0b1032001d985064030710700300040400040d4200380b01c1e00c2c00300d030000402a0544030700750050300c07448440906104d03a03508284001c0e8007108100802642c03d884e81121012129083c1d0004203440e88220009855a80c05c50609008154400300400145501260543e00081242036003075503180826140b0f00c0c0480e4a8007001c503190080044220100d8001030311000c000021210207041c0c0b0390b02c0c22041c0c4521024480c5540102e1000340b250014035100d00c3c43e5611900c10b441e0082000c1200c10391140e0311000e01c00103404030360700060740c1540d51010383c005540c40603256846a0070300200e943c01010004050311295460304007150754507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 897711870 1250 897710620 897710641
    0x130506100845010b1005032a070b0a06050a0e0f0601080a0209040c08040212030403080d150f08060105041406030a020d150c05040f0509040b0f040201020a0803071e05031509 76
    0x1105409803864509002d2400c8018001c183e11850b081c070401301204400285030140003540c0c40740321040381c5140401402c1c18800c4030510201c10043c40b440f010480f1340e00140858150368010020601d00050032410031080c000410140e4010702c056002c91010030040f0140ba0f421107034403410a103005851501c954510801a0003403140c41980305060481001c20a0f03481034079a0b118034021100d107101d00300c1d1065a15242d01c52400003410002040103da41ea040d41e60308041c40c8440786030041c50356a5640d5007094400810380d00041150340102e00100f1480c540f60188001226046074102054100304002940d94180d240c0300034050492901c0c60401d00481e001c2d03501049000050a0005451841004055600501404461000f00b4101083c10304029000c50702c1503034031910090282d01d41d0410078035080001042281103100380da07400e4001074004005035004115035101c000740d000c154148001100a0a0351140400105004118500300c40d04600031b10928140c5101c6a591540781c000e8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 897713120 1250 897711870 897711961
    0x2102040c0f03060519090b0f031f0b0910060e0301110f0a031805060f0a060906090207051009020108061002010b0409050a050d050a0e090c091305061008 67
    0x1a52140c5426400303031038030760441c0000301d1540e031903582084660740b503400b08406603885854208002000c0c51013808500c62990080039000c100600b00040140c00c000003d1528600704500a1034510000c940c1140640714010786400c1001110108107601d08824280b040c050395104480030080d030300100746c2c8551000e6000c114200d6059001c0c541e00c1021200080d025401040d0260000c0d03d0109042c01c1c00340700d00c081515299114000c1c10b00768a82002d080300742d020103084800c400380d80301000100e501140c82030400800340d8820140c2c40360070500b0708504001480b01200e074404d00302000000141e03030112603181e00000441c0c5100c01c220242000b20b00400303a044446801520b051968001e0110004045089034401c0049402228154104483c01d0080b800c0c600085a4045c401e40f5031031400d082c80030303440610840840d05021040c00081c07208a61311a50020050b81c0e0000e2283d1414662004011002c040c24032440e14105204202030082c4104c0d44030014000c0c49552410340008940d85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 897714370 1250 897713120 897713123
    0x43b0c011b02100f120207150506030709020703020714120601030b0a02070f0c05212a040504060905010b040c0c060203100e073b040519090506060a050301090c21 71
    0x40d030f41c070074806a028007110501c07000100803a5a50f40c13048104d028600032a001d1503409103540c214800c0c1000084041d03c006064164036001d440004544068907201812000b400b070350060585600d44800c0c01021800d46200d14003906110a0282d180080081c80904680c1c0c006440340099507102d05420080c01a0040241244140c405507018001e9098051040c0c480c100c500e03c5c100d04074089070842e0000003148000440e00514110808880d0004803031840e60664964030322000c0b0303148000340072101c0440b0100e82065030f0302801c4045c00003d01c180d104800090706c0801c84005040e001400d242e0711110028078298000002808404420701d031880108000d81c064641410064800707440034003488010000d111b0001400c2d0285154070704030b0b1840c42d0082828050100101c1d0500c40605001000c600c40e804088041c0c003202d0341640b06405040f80280c02405c002e041500030046c510200350701680c4281e040000c0e40c1c02140c8140b0912003100e822800006a0110704040451105e868010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 897715620 1250 897714370 897714379
    0x9011e2706020f0c0c1008042103090b0f15030d02150a110c0307060e0a020a170c091f0504201c090f02212109043b0c011b02 55
    0x2039034401100c0020ba50031a880040350662102d043d544400c861f41202258043c020211200038203041c254002c040341040300315842c011038003000c2d07512410800202518a0a1402c10341d5040040c1d00125095a155400d012400b03803049035000440255154908282c00c2403500502020440d141d035580d00403080e450b00c15003140d40b80d1450040d000c2d10b94206003003e031003441c20310a0a824145000c11403110940c2d00500c5c4989640c01c0c03582086100d544840b9002c2d19105d1091044070310340d12007008038420007011040e601e129000706400c054080c010381c8030324000c03030510349001950301a410400d036501150b94207080d03c9034401480c00d18005011030711001140e03d090b200d1801c0c0721280d1050545e4500a44d95581c181040d44000c040e0070724203998000c0240c1000b07070701440d1b500070302c144400643c11169145003801100c000240071207220181c1e208104081d801c1621914224141f52400d40d01540c01004e5002012a81035884200e084081c1c2e0420100c01c0c1d08140d6010301a46042210340c001d030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 897716870 1250 897715620 897715627
    0xc0916030b18070233070f0323100b03090307110d060906020909070e030a031b0b0108030307080c13180906051302090105030c1e01110609011e2706020f 67
    0x1004c2c0d01c920105081002c004412090a101c51900d5000c80342152260381400754035039244041110005a007245000826031220101203a08035000b100a40580d0036612804203170410712075415030701e07215521007082c966090080102e82c03030002c001ea91505811410340094529440d00040f03034521042c0c00188200c1c50f00310308206021a550103030540200a42d040803094a034101e05607105030303140c4a4964183c0c8001384540c0080d01c5840b030301c040ca00c508800c1079209202d40d903d40c0c9082e5800d800000056001108000d0780756802070040d41c0118400c05040e10300760440120000c03101d100d0060803d029820820412072051503440345040c15000907041089003049401e800950b0107801003a441008000f002040a150214502c503404000030140c0140b038000c2e180c4440005a02c0790100e05000f0404074240980c081485464800c5003644000100f2580c00c44405c500c207040014070340925407030041c04194980c0c9035244c1c800744840400c81100c000449180c6400070784203045600d0301040020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 897718120 1250 897716870 897716881
    0xe2703030a050106090501080402030d3005040213060b03042405090d030c0801061b0512070c0806091915060306020f090a2306030a110304140c0916030b18 68
    0x941c8030506131070350b99480110996549004442c80d0f041910040d601da000910f0250300d144c064003120440c0404243d821140e18001c018071070f0005221400c4d03020a9454000f00800c500e0309040d9440b295000920401c401401c0030284038407400b000704010024040003615a490a9030341c003407994541d16104080c850362070420803c0341c5440e000185140071904018405a2060044041e5410307a5031030383c0c0e00d904d544400c100740001155030017415101401070348031002100724202c2c01003d565009588030300b4000d2a0030440351a010b4018406400741d08142d08641d0b00780e4116441484058210400145524100944200810381940004d100d588001074070b020003040c12000d002c6d403000440e0020f0741566910108400009c148001d00c45140640a00440c50710340311000e15008103221034001601440e8866548180c3d00540342900c0101240807040c1649504001044a00100b520174003c00d00300030301011100c540456030b050178180c584151004ca500c03054924404035000c0035400c217881c18031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 897719370 1250 897718120 897718141
    0x50f0a031a040812042109080d03021318020c0d021504081b0607020105071d031015030605010b0d06051f1422080601083904050a0501090507090e270303 67
    0x842811b034400901c04507501700c140d8082c219038000c0302c1b4100041c0071403600e03111081b0025031085503140c050003241e500102d8400303484582e1010006446000590304d4401c4503401d89450000450b100856100c86003044a00039500142500940d0207400300d519004c441c0400000a4520f1481307000c940704840820140350b034150849409138485485031800d101d4912901078001d01041329817909035205040707554651210307038003002c4072801d00e0005c1c82e0f900b40c030b0340d48110035900280e014401c402000b00d444844882c0713a01c5800c00401e02211104100b045040e071014a11b148120b10b01c0a1000c0c46c4c0500f503442101804031903d0500d41010b4000540109440c998101c440d80648140c41c4a010300100e642000090b0200346414000b034210b03203181c0340c80304a101314900034000080d070040002016101d61214081d032401004207090200341c640c100000c0b0000c0b248010481e40400807054010007458a01e0912140c10041498418200a551011000c405210b00b0415581c6100010070440440b05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 897720620 1250 897719370 897719393
    0x6140408030705060a05150102060f1b040308040614091f02030418060806010506041a090a031a040506060103050613090602090a080f1c05040b091f09050f0a031a04081204 75
    0x10060f01b08600e499440c0030611002c950300900e805170b4800e50200e0145000200b010b40d108518419100c641443d01e00305042c2e80e0096401115040c5001c5401d0100a4111542e1728103a84600d01d07150810300c03800000b0301107689940c00b54005008840f4445840751003441110040d20803100c20502c04801004040024030040c821103010380210360010070700c1c0c91320310b0031103044885840f42580302c203e00000600c1594800f00e0055800000f488002001503448540c0804204039500d0384a00e0385000e08015003400001010300f030415250a04000180e40c0d842d01104145074168000a2051841c0c070f0444000d11404508543c011890381c00050542c10024a42801051440a80341b03c0060720760554101c0c19104544400300e00c09001c1070044240003c0a00300e04140140b401a90014084540c050302e0040d051480004070042e5040c005800c060152200c640c1040e2038204041e071458641074020300c00342c1152600352a000300460280580201a82c200034070610b2100a10309151a0124402c00e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 897721870 1250 897720620 897720631
    0xb04060f0f0801020c0c1309051603050d2a0218090d020706261302190515090d060c1403070807320a0507081209120a02070614040803070506 62
    0x100c24207000b051408041c000d80b8840b26030340004001c41118141086203a40721900300408090f0344501e0000403d00c1000b0210403403079480260803009065003043c030308050503c81312506000f4110300b41c03103020902909040e9060800b0140795400c0110380700051585001d03129030a82103003000148002c401c004620951a0b0f0380580803654a50399800701074400d45210706c02108000d205046158968200c1200564042c20b42107003481c0102080d40001d0b840307144030861f24601042141e080c0000d040007000900003440704916181490750b40c100180c20001c40d070a00911040d12031001740e803540d01980c0100100920b401006840b483c104400a018110841e03600c40055600714140d80060900c041d2406200004100c0030201c004404800c00507910543c803950400608100d0000800e44680103840c8031460741d0703101100e40c100220b041d0300d01602034015400f201d00400004c0c24540d00000c2040413183d0034103100720740c641c3d10001c022290040d54010300081c0000150f00702000404101a48660b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 897723120 1250 897721870 897721889
    0xc030408150f01030f06021c05040519050a0809010207050a0608060a06090b03070804030e04020d14090607020319030615230a050405060f04080a15051b0a0c03030b04060f 75
    0x501c4445480440c400003542e0041e0245901801031010807405013500381800c0c02003002624101e64082070580c07446901003141142d40c0e550742071008000040c072440f02d10610f4a002004603480d07684845844240340700c00148100130000708651664002d011850044c0300040c00150341c19600c28000d003c084c001c0710f15a214056440c00030900328020b40d11002035410943c082415039491a100f0754800b0700280007641404403c203044801d942e0345000800d0615030300d03800880c0c4540032211504201f04c001e03048114513004141040385182d40003007a500181944c246081c0c80c3c8400820540040055030000003205030b8110000415503001910300c5856003016402050b100307a02c00401001d40204014000080c104110070080e40c0340c4000074100d110b0150000510701a0750302c400c02e14041552004035841c603030030500e51040040620a00d58011400c28040c01d1044200706030b5402d6109002091040c05005a410002d1612a40c005144594080e01c10401c840d241c86d9201c1c20301a2034407460440c3c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 897724370 1250 897723120 897723133
    0x10f1b1211070804150318030c060b04021305030601082b180e07020c04150506071e060603120309050607051c0c0207090b0301021312051c180501111509120c030408 72
    0x250300c2131242405103087c1c403118046880d49940c0403a03802e061140156085500d80e42202c040e80c6e2148010007043c840020f44150591524090506002d0168451a02d9400a03880c02c1c450030490b1898120b40b00c0f0144411600c01c00c010000d607000400001814610b1504801c0400c5450300f0560550040e109a0215031080000504200543d104080e40380c003902081030781004907082060180460500c2072180c0301802101025803e4215000c40c400e562041c6c541e00b00304184585020a4003440505280c00d200c004115243c0c9641e400000e40400300b0400e00094981c080a4410300e451540482413409001c030680c0386400960350500c500a5050f42c51400d007500d101460f0510884072103078001e01c07803541283c2c0703044038050140700f01c3c05045c0e03801d010b88001c04d02040e540b0150f150307040390280c60715040140c9d0316014000a040c00d81050341802059031015814010025481070f41c2c8145c80c0d8040c07480e54808080501302140305401c81d404040108901034020000300142c429902401c045444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 897725620 1250 897724370 897724409
    0x3010509010e062407140709050f040507050f01050c030a021506060c101104080d170a0915050702030d1a031216060c050906030117010f1b1211070804 66
    0x8210b007040e1a11a40400e444415100d21480340300320f48400c029a1200908103020340d19007a0760700c0940740fa1341e1000e401450042c0329004036071143c0ca03001603075080d5405141c40c2503a5525034642c85d034003c640c402c0b4050300c40202140c0c4140203c0d40c28841003020740b510f4004503000607540300c0403004015241d402c0e40001400340e0070481c082d211005641d80c0141183c0900c85002c01c01402103240c00104404108000716850808201c0c80c07000d000503645841c80c2c0007484001c040c0c00200a014040c005080c201b00f00089501002c078040c190f00300401c0020b9584440400b42d18520480200c41c40e11800c0c0076032200306c1c0d92401e6103150608400d030203403203c1051034000e000003440b40710740c0004005902000100411340700c0c1c0c8207038071061481c240589411a03070b0b80021080c0e00f00f41d12010024089209421001c80b0030b0040082086031408180700d2002000405a55180130705044420072080c0c52000f8010a4284c0182c1d1018020500e90b80da10100b90a064126901c2409180843c4d140c65441e5038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 897726870 1250 897725620 897725639
    0x50304030c142d010809030d02030108061602150105011b0507060c0512130e07140d06180e060105010e0301060e040503190e010e0402070303022a0114061f140703050301050901 77
    0x8009031001000f400c5111610043d10105c8026003007038000c1c4402d100701080e01480e032004502174407001c0014091071a11b03107080010401684100011034000c5101d03800c0340c002d0f0681d06410b49000b42002c0c821980c3c00000c2e084807001d01440900030344600b550003c0c1e038036000700708101128029400c2d6a1904106074180030340740300d0f030b44040c0a48261040104051910040040d421100c0380ca4190412040b50410305e4490308641012003401d9510a42002046650103103900700b1145100c003030002a0581c220070b502c4005c1480f4a5042c800c40240f081c601759403e50000020b0320303040d01d80000d03d080c681880d81ea0394000044908003010408050305400307010307051070046540140c1d148802c034100c0c9001d0002035080f66030308809142e024441420b0000e5503103e83c0e0004c00e440f00e1039400c51021f182d07540b425111003403081d9080300701d13803c00d026168075082008607000400941c0c512040384000000c40304c190109a40b2610f0100c042840e500b0940d0002c02141258404c480c503110750f0343c0f11010007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 897728120 1250 897726870 897726919
    0x50d02060d0c0216060305061008250e04140106140304110411070b0411040f0b0616020105160308060a0e090616110f030403120801120f050304030c14 66
    0x2a61041041c400034007080c5058100d4400001c00388160768041c10111070910b008811a080300002c01d4644003000401c0c1001e060a0000c06a2894490182c1c00d00c104421510b080d520a907240302c00b500b41540b0060f46c002c155810507103030007038010420409209502c092140080c094036000440c0340c079654640b04810000d490117540c1003807610803181361101c00c00c002012605010300d070302c000c2844042d001c2803591101500c1180907452058500c000c1001700f00131035907420b14002c3c00c5072404101828070b031201c00c26590107842440c0800042241800107072003600070b001180c0c50f0810707200240c508141c1d110950b07900511050350741c00c2c44c03551074075030200c0040d000311520305179a403011000a02c3e400b1501348001c420340036410000300c0040e01d01500b9080c0518000c01d22000e03800014200304010402d5590107012559240207086075042480c545c01c00d500210f4050f0240b2024503952060140c140304950055510540d42248146e0304c034807075050b11102c00581072040e00000c50f0140c000c2000e0480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 897729370 1250 897728120 897728123
    0x180a0b27030f13031a060f030d0e190f0f180507050703051303051002070308010909080723010c0e03010e0615130902090403020a050f030408030301060305150a1401020106050d 77
    0x241d8200540e031035656900e40c02a0b88901608503c9000000100f0900c10b00441215800450403010f40f40007400d02c800c0d00c0a0b075a0044c060340c0f0000b542c000742607110b50840c070b9901c03040f551a59940ca0351900c4101d20322a5400032080b5014038803000680d541a88080b0041354003c0000141e880e9410852204444013155010301103441088042e0020f8030880c028408c0c4869001034081841d100d491302071902c12a003041e1031405500168102c141034100001074014140643d0a101d40c109a80c0c40c1c1c101c40c09818030062940c000031003030028000d420900c501043c0c100740f0080244c0000075000500000d010741980703000354a000034400c03070140301007809407080d620380c068080102c016070180f0909080c40101684d0055651903240010396401c2c00d0325004038003a40c001c00141d074090520a00f0081000e018120642c02000200b180c64404000e40303046800505001803107545424800d405031a02904a642c414107071100070800300380030f00d01c81d040301034207078000c1041c00c2d00c44045c84030810500d01d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 897730620 1250 897729370 897729373
    0x1020c0331030605010906050303070f02010f0207120506010501260105010e13090804031e030e060a0c05031201060f0201020901210618090302011121180a0b27 70
    0x9011100030504020206040034000001038286410020a01c0c00054008640e039030340382c20041040b000380b802424050403044000c1d510b0702c4071607591a00c0040c240308000303061041240c0b034841c0d194024030588000307181c2c0d903940a0040c211481c5c02502c82c0024019a40440c00502c0f04214a61100c1e1a045003039680b000c2d4915140d0034130300196420f60b1120280c40d404010148091036000d40b501480e0300007845115465207031405c1d4078090174000c082d8064101414282046400800e60003160004550820b460080c1d1325220004d0454043c0030200024141d440000340c144030708030200c0e1550b412910159100e201c00907401108900381d2049060b56070004942001c120516103000800303d00c14410640005140c03035a81c594450b80710b1840840042c010b41c1c500034a401d0640a008624900741004580c40c0362240307000140503081c50288001c042c0410f02c800180d00c14200c00d10100118030900201c500300546850421400c500c11030b1015801150382d501c1541c642281c001d44010342103185c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 897731870 1250 897730620 897730627
    0x60a050907030902040f0b1c05011e091214030403080c040e0106260108030a111005040302030d0515090a020a0c02031002250b070503090106051503220b1b1c0c020f01020c03 76
    0x200f2000048802c400c1c1a03906560751a110360303200bd007007410303e0341c0180d483c0000b00c4d842c409400c019940e4032260085800b0b00004a1000c15500a41e4088a6100c1e51608090390355885e104071104241c0610303040002950b058a001186c400d82125801010300c40b440061184186011002e1816040c2032260211560007803003400050b40c090203000b091311124100b00c504040b08480402c0940740305035800d9015800c0000d050880340002e02034140e00c400d460b81c09825081a070000304150100c004c1103c0d8040d40c0c08034000010511410079190881e400070104c0e06a11170780c8904c0c0c4c00941c0300240c080c01c1403641c0d422500c1d5081680040c00384c4113400c20070741c06a079540c5000544032680300a00549041d540c0d0300c2e02090640d18146175162250420320019100d00e000c0844d80650141054031055075040a01ca520028800503c07c580c00003500e202010001c40d00380c40030403030740aa46e110401c1e9800f0782014a00c0c40701c1e15441288640c0c0d041d0308580d40b9211402d5103500300e110300303c207401e0703643c0042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 897733120 1250 897731870 897731899
    0x3040b2a070b0901030219081006171b070b0106180f0b0304060c1106130c080109020a090b1302043f0615080307060c03240509060a050907030902040f0b 67
    0x100054044400c060402620b4010521441a071f00c1c030400c09114007041c003140521001040701d01c104030151155081540d0481c1c52140903440c5c205c401420441c03040680c2440c10385074560744060b03540f200d0b0f22440c405c0b00c55031111405000d0701c20901c10110112941c00c0700180345403074803100104413801c50021901d0350300c850311100050000d0451140c1401100303200040d0039001003140600c1001d2140301c000c1000c4c11450074004095450307200604c9a8141f241c0702000d41c0e035242e1164200c0c0d8010303c002803076150110114803188903003107003589054800718001809001e002c154254446032040d48444c02c4a040040c076041900b0304844124041d031f000ca901000405035400a205000ea040d4415181940c402c5c0c06440c51380a407500711401500c079074640b94540c0c7c060007000300d1045e180341803406c000300038000350f002d0100d03074801e841c0b08004000c0030a08544510710844040c01000d40381a40d9032034080b00103400f8016540c07040740110300c1e00104080c0b2505030702ca880075001c00204000480705c0c02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 897734370 1250 897733120 897733139
    0x30e15070210080f0a0e061f0f030812011a0403080f0d0504030c120915030b1f08150a050a14130c020c090f3603040b2a07 54
    0x850820118180811000300542d44515000c000d07030940b6030b01e034009842c04051a1005401c0079120700364982c1440070036058003501145040e8850864010500c20301c06445400308410a694010100304801800200c280455900208540300304404181180e9907503a04013001d00c07075400016401280140310030b20000c0d501070014850030404002d658101410f40340502c08aa01c10343d000c47c0411030201c01801044a52440c1c10008081d5050112400d17141012050785070004000402c00c25640e07100d4540c0950321004400b0303008900c846d01451801c0310060140c02c00a040e10040c010107000d150304d142e64605900084191070f009001c0b0002c0790b1411902d010803032526800780ba8018060710300131314090303494460000700301207650091500b10b80d03940a001c0340c0d55025000c0001c01310b9170402c0000604403501c24000e00400c06a0007501c6040051f81c6c00600c61182c06461500d020004d80082d100b4118800313004001d054144440c4000090220a0f03085011482c4041c2da5420038036041102005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 897735620 1250 897734370 897734389
    0x103020d0606030c06050c01050601020606030d0c030309120201140c0f09060a02011e050a060b0c0d080402210309010e0f01210f0f0608010e0a0c05220e0609010b0d030e 74
    0x10600002c01c00c0d9449607a181d15848480d041200003410118000301d8034002406072507000300080c0044c10350b504280c0013180c0c84032812034045080c4152000d040042610982c045861180c014071b80c810004820b50000b406010141c980748001c030706030f0000c9409262501c1c204c0d044034519100003807400c3c80c010180701d9150444030820301503540e03a030501c880800031b865047c0f50f501d640a1b00040d9514280c4030480444081d600b11300348803101071045c01500500014501d03224521820003012a03a01c0d0300c00a00f100602180e07441c41d01080c4041201c0c014030000c060580d50070b00340c80395080c0c2c0502c8800e000440440b85403243c001503600c01c0c02e0304802450165415040221031021419003810414002500d501c6c81c2d510700c80c2d960f030305000c0051023002e20501c2c01310600c0d0700c0078002e0042c1a841784ca421036214010b07280700f40811400000081e50900d00700090581440003840301c100b0481c18146c64210454540901d9420400303281154074148000c2d05942d9403684607251040c0510b400d1014101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 897736870 1250 897735620 897735623
    0xb061f0230030405010903140702011418060a0201090303060605121b0c0d022d1b01120603060b0a050604061209020a0f0b030403170103110f0420090321030103020d 72
    0x10200c01001c03400280d03401148518062400031a55150354074006190700300c442c1d00b0140200040c0802c80040c0c2e4402045d0003d0400001119210410b8040da00c03001440340c10120340c40b842c0001d012000c60b406421000350070b4080e4400300441a5035010940b21031160201c0040a1001140000c2c0020710f0924045541c641c0803254500f003104014280385001d401e940b204000d64001000105c945d280f0602d0300e00e0005070110152800c00c14488801c4c2e981071012904d4900f4814041e040c405e0380d22464103002c004040b020103004055407402c21074000c14820175850f000307041c04400404c1c107040540454045400d075550341c003041c0000c08001001011140b9040342c4c018603d41002602400381e2091a01030326516140560300e080038680a0000b03000c50b0301d01003096440000410210701d0f11550f20700115425a00071010181c035000250082280042c0084403c4801080c281e04003800d00280c03810300b40a40480b158081801e2071700700c17500222910004c1a80040005000504203001c041440302e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 897738120 1250 897736870 897736933
    0x9010c1103030a02011505190e04110d060204140907050412020307030f2a080c01050a03021e1c1406060705070803181e0904230601030b061f02 63
    0x26810040082d080d0b511081030080181e45035540000301c3c90b490b0305070f0401000c040b40d040985000c01500a4111120b81c441c081c490302440780042c040c4a00103042550540c80180071800d60300c4a0302c2c001d03000750000d0007005503011080052120034104220694040c1e071264542c0c0d8205440c00005400c1e181c1001c008a816005284002000601481085403400e00c542000407048013841c0340d00c1c000c3c10034080041c90110400008012020021890807249c10003031a11541d1041c16a00541c043d200d403054030005108544042e1748600d0012000c0d2030a000e8480c060140075100d004088240c0d05041d906080401000700440c0300c0b031601c0c1d4000d08500b131280c01a100560390300c15420f415608403204050f407590f0044400f0215150081348202c2030215485441a50a8240c0208903810300060004003100d201c03000c0c1d50401c09840c2030240203507134800200c070f00c03c0d070316031400344d042070010341d1024002da4184400d0700c91086040b074196101e580ba640200500500d104500d2203034415900480401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 897739370 1250 897738120 897738143
    0xc1d090702190f0b070504030f2003030a2f0712020315010e04111f0f21060509090d02211e0306030724030e0f030a0c060513020609010c 60
    0x22054030031018409a02540d40b02c90600f080307003001c800c0c2250050200342001000c10080c030008a0500c0c0e0715124076041000055a44e45501100b00047c03416446c040e454480880d482c4009940030784690340348140d900610680e00c0c0c90004941441c80100311ba1687c0d5004890240a202c080c0c0001d1030840340014110750723503c070507400d03201e8090000303800c0f00e01d80c01c41100c100030600644407a070351100c1b44150b0303007a0300038043d4110350400c01d04c000d081d203810400e41007a9070355028071482010315800020007840c1079004895000c00b000f8049842803034001c041c1c090001e56062030100f800a00c0348001c3d0041c1c6160240c56401410707401800302c3c02444054141302240100b40003c1580800e130704c040041c00e540e03081003402c052900d10a40d002018019074042c170100880c071002001c2d01d44182d9410081008900307800140e040100540a07a401484041400100141d00030080c00405000352420446612001c8442d0117587d440a03000c1e401c4142000b1084c61795208180c7c00e802c0c90b00800d2a29036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 897740620 1250 897739370 897739393
    0x6020909040b01150f05030112020a0807080c1203040501271a04140a0302032d0d1e0504030b0c031e0f070906090503060c0f040e190c1d090702 63
    0xc903903100380c030300b600d0000c0360794014800307030070003005030100d84603141015030341d006120b10020301e00d00c81401a2039081516285000454480d0701d4007401a003e11010354008945a02045540e00c41a4100358404e40001c0c2c10500340c24070101c1101c09642060790760031000c200e099024802c141205111808405143c00005080c901c5909404071103061031146507986c900d080392500c1d40d409014188e51141240f8401000143d400003004c80c0a03003106803100d584214002e034840b54100c1c51183c540301501815600c48500355201c80c01380500400c40d42142020b00e2105030403211405140070041c05a0080001319018554090246074049074400656141042c1505a8000c1c42030541301400f41e400c004050101864004215201404c000e103410703032200d454030001966400c8050036015000000103210010000c0500440d00500004845401c0c0d41c108100d00d081c042a111724011511031510340c113400c0c21485090030700c6403d00250401801004e104082164486001d00103109501c03805002c41c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 897741870 1250 897740620 897740629
    0x60c011104060e0f090105040c020f3c0d0327051b06071a040f020a0305030903010507030606021c21060302100e0d030e01021e0a060f0c0516060209 65
    0x40c100c01140c084580c99924084020b003c0c0800a40407a115080c43c0c0902000d58030b51a43c00c0381140d0003220b01050b80804014181e0800205090800390790140d402c032084031240094046040c5840080a0854801c114004803040041070705103454580040c1c922600152007030300091a4403000103001850301c15900c0c603482200044100031034541d04404410b4103851100c445544200400341c0d03210340340c011256540c51001e03144c6111180c21900b8000490f050100380030419000e02d038050140d46100e500e03800d065070b4942103103810a10035801d001c0001d82c028803038041c035001c17544142c004119000d80c1110791103029015010603020030100500741005603040d40351401d184480b00300700151590644c014440c4604541c085d107810f010600008901a4592850712192580c1600e05025071801c1e0000403814645c0e070341d480141c4000d0b56442080c5c0a40c011440d41c0203e0300c0b0351410401410420490002e0343d1003a45950007145092008000308080700f1900202544203190040c6009040c60019 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 897743120 1250 897741870 897741881
    0x3061e0a12290a1113050d0f0203010507020307061802090402010807021c050406030e01020c06040b0c04031226070504060f0e0303030a20090a09020d1806150b0702030a11060c01 78
    0x15080042c10140700d110105071244c008988442802d05140c6011025001010507032482120302801085020138144003540e458410f00d154014001d01030742c281048000c2d0b80e5000014252030030b9190203010264007445800c01545140c0c0035208900b40c0d0340d5600103484000000301150203600884441c804a861101116801d4074200e44400d92034600307000c0002c00700c9140b44291a1140e204010351100c8400008001c1c2e0710540c048404040ca40d00c401200b00c55000d15403000b401203125040307100c100f681081c03050311094544001c04013100059203c640d0110b80558030311020800400080c41100e1140c441c0c0c0d00401e070036080010610345104082481c6030320440c0e203e10307036940e1540a049490301d0f40041e040b802d801d0302034860070b0001e400300140701c1c02001d2080c60491030380082c0f0310050410603005072840c0a40e041090403140381504001003e0120842d04100b00c1129680103d8524082019114072540242c020721043c50540d54414210040c80c0d4001c0e40101c0c18440005440e0b000d0058 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 897744370 1250 897743120 897743183
    0x60b130f060812030c0417122a010912110a1e1703012d1214070f14090406060f15090b030405211e03061e0a12 49
    0x1d0075490907200c00c1c1401603030100502c00303000030018403c0c400919026030b001d54445000596025202c0790010b468034030924405d1442d01000b044420700074200c91410444103106000600c0c0801001040d2400c0300c00d42400101410082104402210700c145032060760403007000c00b1100b06a000da25100044104540c2e0300f590f0880b140004800c22030a0090b8000c50101c4400c0c41e400c65062038050848030100840c0605c03030000f03407001c2c07000650102044030001d26809101d0b0005025a042c8403110443c0742040c10030601c5440000960f111a2240c3c1500f21540e803074000b07840202500800503900c1c03002e08184d41040d11588003150302c3c88441c0212000b4010050400131804902d24040c0c20340d0b0b0654050816501e0034010840072840206609854042403440d00d0022032983c280700a25005001c03ea2810f0b020040440c102c00320030300c1c0150300580701107d91200880c2d440501010090080100b1a0010302060307081085e1100034032503203c02071080307510b903520320f9114001100b1106880718 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 897745620 1250 897744370 897744401
    0x140f0405030d090e07050307050d020406201b0f030c0414090c0a030f0b07020f2e06060507080c151320011e02071d07020607110a060b13 60
    0x4003000103203410014114251520304024208914189810700e00c114004c1c42071003803000000000b00342030710440441d602c0440e440011510790b80c56990007012551070504141200801e142e085103076600001d010b0301140c2c40080f803480c001514406028086e20f400601c1034041c030401c9c0c3c030303407140380d941c1e02540c1c184c940d540d41200c17001c1c0b030308024807440c03c4449102d850041100100501c0424481001c10389155000024003400303842d0300b1400c07458408090009081801140390502061410210304020480c4080d500340491071602900d10450b003003845040e0118000700009400500050081c284604402007034514099807124881c0c0c105208503501644004030326498030810040000e40c84880c90003038800000f0010180000e0b0141030005143d88045504010b0300e8a5a40b0800460020b04032541285000c1d40700c000c466202514240c81940260041800141006104203500e0441524520007050340181c141c8400700100081c40f90141c0280c00c0c8508902907104500034540c0781c40d002c84 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 897746870 1250 897745620 897745627
    0x1091203020d0f020c1f09021c03120c050a020f12040515040b131a1905132402010e12040303030207020a03080c0a050c01020c091609031a1f081903140f 67
    0x383d1800501468101b0742107081e1400e02c0040240e11800c50b01803860315801155808200070382800d0310102c0c0c50100c00c440c0c807030404103d80b5003103610001808404110360221801e03800c104031640d803201c0b01d94058011031001031004119510b408446044070312a9411000d03d004d07200c00c0001c126500c044844095410010820085001201e003000b200214240741d1604084420540610f50441c1c444400d00f0000003003840e411900c5141100f10040120380c42c0344d55651405000d80b5211006075561202651a210442450380000300d1b0341c202c6011150b800038035250a55405074000d4005842c281c1c1c014a40000110020300d0031002000040070160080a8542c071500c1c1c40c500e00200b02c000241103410071144001ca5455503440160480e07465003200fa4651074080086501da15941d01c0030707040c0b211030741d0340186858517058000d001307401426103010308540c2501c045034061681e10036503040f5030000501c25000343d680f4920440442c4213107010117501e000441d41444540007600d5110800d800003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 897748120 1250 897746870 897746893
    0x260403150204080d0f270f060c05010605040c0c03080a20220609170109061b020706020601240e040e0106091401030c0e070302070b010f050f0301091203020d0f020c 72
    0x20042c078200311401e440d04c000880c080d0003004051206e5000700740c0d20715101c00c403444909a174402c5004050050b07080440c0d42d6554400300209001c04508080d60079500c1d008010035141414054404400b08c0f54594120142c407659086a441e1401440104002d9581c0341c0200c070701d1606d86082c5c80810070140c080d81c6580007512011484a69508011a4580707040ad04004094100301c000080b0b990025040780e527030280c040700c9801b40c21104801040c192521040c0c1d8550b204041000c4055140382d03084418481d1101000d80c1e550034207005d411014070b028031400e01c0c40414005c503407002440c0761402000f007103205004582030303c4092241c10000d0751a10b006102c41e403558415611051100b80d2508010b51441d00d0305581c811003405044148500d2500103a02c2500a07011100681c2d0b204140c904e031903a44400d0a101051a8010b80b441040d00803150591842e0500418195641001c0440010080c42c036040c0c00961003044580c01040e11402081031031829840541110044140509602e654a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 897749370 1250 897748120 897748123
    0x6090a030f06022b0c0e010207050f0112060303092606060603090c090408041e030c060e0a030c090504030e0d030225080106080304050f01020a030c0b220c05031926040315020408 78
    0x4200b5607010484000380f840d6147c0e0780011040200c039400c1d195602e8084c1118012100e006000318501e0516013031070300010405034040d0400d030454040f0008031012090130000090100d01002c00c1e43c6c4180e11213404134000d85010002940c00c9101001114181c8800001203044208112010740707116070089410001c942030039000c1d291155a00841010207801c40c4c0d102c40c1c4429072070040750100080104a00c0302a141d11019402840e08021154420b55444010394003500084030120002038050030240001d0500b040ca100d01d00d540354000d01b4040d54821075000450301e428081400c0c0000d003082c00181440c2c02e1140701c001c1d0001c807001c1c55881d0f04003410b10100d00c09000d03815045500104c0c2c03103070200b0792000709280c04640c07140c9444000e49881c01c2c2003144501e202031002a00b5852180c003010400030804182c2121420f400f0341d0000080082c44d00101115024041c1004c0120003282c010301d81c50204030341d580c00d081d400c2c1c0390400342c980c0c584104035000301240c00c0040d5030004c0d0030301c4142c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 897750620 1250 897749370 897749381
    0x10906440a0f060e040b07021e010603021f0518040605040c02060124080711031e0d0605090c0406030f020d06031b090507050a08070e0909010902040b06090a030f06022b 74
    0x12001000c1c0820f42c60400080e03404500208040c00812011002c10f400320f1081c465160b0384032515080003400884429154003c0c0583e1100702d128144c00b8940c040020012550005a00360310307102c40d4246403c03030f1002c001020f07001c180c0d02d03401681d82c440401c49070380d68400c3d060010f555600400305076043c5120380401500001e00003000440340350f0514802984002c032582e0040c8145800e0190818003030495155009902c03040e0541611208404405c100d0340001d00a0086d0800041c0030140c0c0e20811710040d40c50680316a500075100b00000d2001902035040306002108080340146400200c00c4c04074200c81051b081100d40030f034820980400502029101c00180c201c6400801c094188008050868421146103c090141000001c0d00850203000d13844090a00034003260039500c0e0a0f503005008144c200022803059207421960080d60801d0020745280c041d002d40392010840c2161116041c40107001021a40e8070380801c41c00c2d584400c1d42211058401c0c0c0d803009030078500c00004580c01500c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 897751870 1250 897750620 897750641
    0xa0e1c0309060b0d08090111070e0420010c02060a03020c030706050406060f0b0309060403032a031d0304150c0f05031602040b010c020307030b0c0408010216020a05010906440a 77
    0x40c0c0b03032a8440c021569172030071a0201c56090a05072100b0425000140c10040c5950105a42c00d2200041100b40711010103608142c0c540c102043c852001190019290881c80740c101a41204060100011041c0a6401040c03103601d40822a0b0030a09295200410ba58084a0440c0c9440d00e4582c00c100402003020080d020340383c00c034042811071400d030000d2a500c0f44020301c046c041603252241d1140300c280c8a444818207400d00d640302c070a0102a040090080c1100c004044c00c0856460004a40c4e11030101c260390a0311048009a4208040140b0072100400760302001d0f90300d418440100740000b4000c00040c054400b049030b4600c040c4845004000c101c032207088107941030064031b004000060ba004030b4440181c9500a18010554440c0000c0c0d400a001e0354100045561002421007054415401c000e01428821910b5a556940301c900441300d00e8014402e074004038403640b8850146221902075a04110380040d11400100500d034100d0184030742c100040b00d000d151360000d01010030550700811070710700d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 897753120 1250 897751870 897751879
    0x1020181002030304030c021c05030315010906140f130f08210405030c240703090f05100f0e01030209100f09230603060607020334050105030a0e1c0309060b 68
    0x600e842e031005403007803046d848000e2003034451801500d11454100d048c100c4481c0c0010031652a444c10003140000d80c8224004103001c140f40c6200000d90900c90311071103c078130007103800060074100f59800312138947d0402c4e03103030400b4684040c0010601d026440715100050101900030511042e0704009000c0800660401428041080000740b180c0e0300c0004203851415070644038810000c0c4a111451901c950131041a0050900011b40c0d00c18980e000d00541c0c140c1d283c03284a800002e589408120764164440040ca012a0903400c10103c1d8600a101312030340f03d00b06040242c07a0032aa1400500584200c5c207069000c070310495012400c440d8040c0c07032400907100e4860b034a81031060306031000009486021100d0303c05c1f0fa0000004041d500d42009490341d066018044440303944a41c0020501c00000c0d0f600f902c05595544149602e0b07005e1440120122a01a1156451030320f0300e141e01c3c0080c0030b4810b41d00000788070340d1000030044140e007031100381c6407522581d00042c2178409141030030070740d0085803100d4485c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 897754370 1250 897753120 897753127
    0x10140d020d050d08041109150915090115080a0203090a14030f04150305090c03030d0c030209060409020a020d020d0903122714060306030d0302090307151817102018100203 75
    0xa800048d000d8007120798116018080307651040b4103060300c49840011150400140e1000003809055a00c00d51821030b0f96484a01c0d07983e544000280403404102d42d0107a50303074805041d80000c0f581c0581180400013110313060700d14180000070101e050341d129520104c10500310407032032030426601d4403a01d500942c0034800b40100004420009a882c007070840ca1580c0750756640e10546007540282e048a40071503002e842c0c59115036032980b4400094000d581d1000c054043e00d41450180d0b0b1008c04d01d01002040c90300c2d20314506045031509044050000100c1d02400002c03c04884500500902190940d6100c0340c1401403e0500b540c03101c03000050340070719000741418414400c030340e680828801181070281c41c00585503008840040c0c90030b00783e070744114140302c0e0010100280310b0b401240c0e00c00c2e040410741100d54080d90b4820407081c00b078008804220a800481030000074103c1c0c0c2e0020001143c0b6408619040708441c0c8404c4801c0c0c4c400b2a0249203040405205011030034150b4140e80e1411031800035508 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 897755620 1250 897754370 897754381
    0x105091303090315181b05061315030e030c07150306030804050411070b01080a0c0b0304081b21030108010e0106050603041b0320030610140d020d050d08041109 70
    0x4115070b5030000820036101300c94060342ca09020740c003010301034040e03011a010449007410603215140c008054904044060200070419003040c404a03401041e09003980e1504900d0b05500d02e160b0b2090109403010151141142c40e101e83c7e040020f01070228110b0080c1000b98034200040081fa00046890340c141410701d5010008204404c05032401c807070096801146030450110116220304c50f40700020400c244403400400c2040c0300048841c4054030800300c86400c0c40d1140a56441ca00040318010400d01c41044621820801c14140c00030070350001c811104048444201070b03825002c03d80c4000040d81020004200911007401900402c001c0c003802003044505050128040344001017000d4070032107018404401714842128084000c41d04450320794001c034600c000c0500d03800400001c107442481609c0104201c0148484d04004441155040e070481202010520190710321000046ea80613600c80030701c0011607410b01c44044d00418a641d402d82c54075003860800c45e9405180a1240240c681380708200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 897756870 1250 897755620 897755627
    0x50601021009020616031814061804060b04060c0201080a09030c0f080f1b0f0f10091a040515100b0f1c0c0e010e010201021e030702150f0105091303 65
    0x38001400381c0004035490100340003040c0ca904c940c5103101e040c08aa101402c043c503501034402e02c010000c002c0440c200340c0d40c640300d0301032180040303c02503440b1a003041206608940745c115081601809040481c40076030b02c60311001340360803075440300c070110b10218102c0c0701315a80718403040c1c1e000750036a0f401c00010f4000d071801481404420301c000c01201c0c4080349401484000c201750f6590340c001d00c1b0425541d2000900644c60110141c01e41d45d511f200c0d12101c8600040082100c00032000d061000300b00d4100c1c49003801000c1c2079445010703680001120004581020181042885140a90003e0045005180700894400c0004001c0e000b10b9030908020310001070004115006840321103070700754650001e8801503c0300815041080315041c9415a03484102c3c0e00a10058464642622408284030030a40160300381d2042c0c210320303106020308504c00014144620302441c1c0200c1c5910403210034184807002424144002c0d00c428041c448003100420281c6018114544d01240e04a03c0c461010b000e41d4015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 897758120 1250 897756870 897756883
    0xe01020115080c060f130303020a031b050d05130b182403040609030905031f0606230a03020c06011d06180a09031b0602180102010533041a03010f05060102 68
    0x100c4c4200e100040050b1752440d05002d554a00b450150191440c50782c918000e581c4d00c0450070102c010483c0b400e1101020102c04014542c00350f041409440e0300e04100404440c84d0703020f2010b9100304042e0300070104c0e008103a07001921607130950724589003801440b08101b01002c0800010409400b090011541c44016007105a07a001903200b0030104224111340390035224140b940d080140c061280e141c00c403030014149010194122a01d02e005c2014a8446e981280d001043c41d041c0c00c5c40c40c0100030440c0108001c04010800361140c0c4c0b03401420030003e07424180c14030a00f07901c0558449281a514948810205686c0b50040c5085a800340c07082c20f41c40140201c140d005003940d18142d0344800fa030b01414041c180031044510080c0c40f1551050309840d2a40c000e402155415070800700104500d81d0f5035005214180c01014485400f00410503074401c40e203001d01d8074286c03288030711107082c81c03c610544a90090100c181454500d042c1d07220700507000c6c1404c40b0181c0d4004080c15082c03009021403641c021618 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 897759370 1250 897758120 897758143
    0x109090c0909081b06070806040209030c091b0406020304060207060302120106120e0f0307050f1b0d0c0f060302070506100605031306062c090a021e010c0f030e0102011508 75
    0x8603010842d402c00032154066120f41002c03209520302260800b003008548244607420315100c4040e16100d500a0004078080c0c03010003a01644424249c4085203050081c00342d0100000c50b02d02ca01c05228031a16040f40c20075403011000d43e10104081c010a40c05003c075130f01030885807404508002042c0600d172415101031042078140704443c42c2c2c5032100a01900700e0740081c16250200d41c480c6c1e1181c08503555961180d441901e2600408403000300341c8201081c04070500c43c43d054214091a108020070224044941c400c039507055100c00002010882041d0b40b00040809460068564860742415400d0080013042c0600f411004070081c08015005420740f500440d0359044c094440320a40340a03001070400e90014491800080030394104440c601100e40c103500e0110552045d1921048205551501ca0500007035100c5414014254110421001c001c1d044c40c052400b01c415284545a00f80245601c5005400040344100003030100c2d43c0900a07000b051603500e03121038055103054815500d03403107112003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 897760620 1250 897759370 897759389
    0x120203090c04110c01090c050a080c0a09330f150903110312030411041b020c010e0a050d0b09191a040609080c010506031b0d060e07090906140109090c 66
    0x41c1003140e00d0b88409070340c07000306134030000c01001d1018140a1500401c40c85424450700100b20003082c0e03d800442c41480107840134101c031030600d00303021058005e030620785d43c03242e091851000041c02043c22000340c800310b859104400d528075070422200b42018402500411548281c40c1041c0801036480091042201e8002c442d101d9440d02c1a00064104140d601081c06554408030a000074004d021400c03030b034185005c0305c0804c04500b0b041510f44444510084005c0941c0080c0c0c41c0282d55406400c00e0035a011000300f401c0a0b0a490f1000552a048013030300c1603d00040f444200410304030100410219004034000e40b01c19900e05698501c001490402d610440c14503000108080241302d0308010358079540f00c042181c03151407148055000308404c4031580c0c401c3c82200c4613a1020380750302c08002081040500844080241d0b5103e030f502914aa503030701441889404400103003600707284105270146209027008103607078540350550240c88006030013400c101c2c0e160081d4000002c03010240581102c54050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 897761870 1250 897760620 897760631
    0x7031503050d2d051c05060310021c1a010207050915010c05010e0601240302090d08070203070305010e07170d0801060f050712050a1d0913080d0e0d120203090c04 71
    0x440c1030603200c0c0f509048201109550382ca4880c07068101000d050000803403500c002e0410881040304081c0c2e1800ea82d0160541c01109030804404850340042280c0400304680d02a203000010030b00040710203840c4034118008404900100d15a41030000d10002e00040741e0441041c1004015801c1906600c000207052090002031030707080007000e4004102c034501001c01c4d07824560392460000c80141c0c008281e0903c4050101d8000c10141c000e00c26074400d00800703018145a2002ca139124400b6912940c400d0303030f0520804a0001c0050024000c18000d100c1a4010308a0249403860600303a4002c142038403492500918a030003c419406840d45045070002d01c3c020602c1800c03000d080c0c541c1d10600d01c001e0940203010310084003954121000703241082c26071351002c180e0740140381c0e444008071800e40a60391090705074010620400f0320824241c6030302d0280b082103141c0f9180960503000c5070001c030891110b0741c100e80800a0741d9600002804100117420074294903601d410310075580c54008003030505200381e5039007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 897763120 1250 897761870 897761897
    0x506150a0309050c181801020f04090c050730020705030303041b120305191803081c090c08060612030706050c0f0c072c010e060d08040e07031503050d 66
    0x41054041105010f44607101e00c04d0300c0402103001c180c0856000c1e80c42e10061070110341590051007140c0020727036004602d0342003038245858100030381504600344040000901409001c18500c0140e2050503101c5811030355000101d240040c04100300104200a64204c690100a99140030046951066004070360702411213481c010032651950b59004051001d25800029003007640000c010101e07503078040e1000c1c070300b45400d290888041d200b078450f00841c000c03072250820015525201900e14480f5605601291410031a0043c08641d82d0b01c0058907014007800040220710002c0c0f090a8201c0700690700c1031242e0404282c0c071075592051740f000030040c81d504d40c0022060000901601c4c490245080da403603481c45103030041a0b0325000c40c0240506806090b604660500403001011804908050321403901d82c80c0061000d588000286515041941445a41c0000301800c000304050680b0400702252820603040080448454002d10310401450745800c0c408100d00150160501049140001054020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 897764370 1250 897763120 897763123
    0x9140609040c1d1909020d060903020c0429040209060f0c011b020606040e16030308130203030720041e0e1e01090201111b121218040506150a030905 65
    0x12984002d10500051141c0c0d2000c01c030303020500e0f00407000ca008190b88006104c0d9040e013190280000254400f141c3c9405000040d141c3d008045c1c03083c081c0c01990410b4103100d000c90700759601038941601000400604114030b40080141054800003560118140b83c44080820031074440c8903c6002d00740c2000c075075071400403003d4000048180044c030503500c816500400c003039500e80055405521482c100b1038907841740040007a0310142c2404e136044682c00ca919540b01920340c00c201a00320041e0070650212000583c80030402040310030b1003400e0300003500c440d005803002030103c8507103110f10550901c0d1684545205199a00d00c01d40d1429500084400c080c3c412185000680d9200300000d00f0340c04012025140103500c2000c20760700030b072522107208540c1081d0603246c3d4020f08404441d82620b03105412030b82005203000e54480c601100700c0701030006020b400c0c031007500040030403c803a108107115007603e0304040c0501ca4020205441403840c0f98002c00420602d8002c00c0d040c0410581d45510210a0120 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 897765620 1250 897764370 897764393
    0x110430021302030f0f04030e06090a081219050a0905130b04060f080708060412030507050d05010f0906050409050d030b130908070b0606040305123007090914060904 72
    0x1401404000803071503414280019402c1280d00c0e00e440e41d18500011014281c01c40e045204035415603803035601151500422985410000000fa040204a0070114044104215800c40c0101c0130a4158503260b404418120b40c000d8000c0300000c00c03809000400b01d2603041581d200944030100c904140911201074003000030082c2910b00e686c41800c0c2400007c0b050404948002070303c0c900d40c142c0700c1d60b5489114541ea02e29058500a101807000c0207560803191082d800b164000301d4526090b840c0c4100250b210003528800e03000320001c11100e03481084829250b10404c40205803e842c203000b4440c40380c0300d8031b4032500340c9140710050607100d0311343c0d401d2641e030401ea11b00011480b5504000d1181103080c20304503500000030403614820040045100303440c05205a41c2181c0d40301d00241421001820b0042c00c94015080303c404001003840070f84124603401e2140007002c81192820002860301500c014a8090070ba806000302910b896a542640030040310146d5000c1c400361081d000c0f9403603070310b80303802420f6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 897766870 1250 897765620 897765623
    0x406020c0f2b140a1205010f060507020d0204110a0f08010e0f150f030118060c0806130209040f1a24221706100f061209110301060b04030204110430 65
    0x51000076103c0b0fa8540166078044517010a10080145a0300c48600c1d8031040490b000c0d000c0031441c00d204030030051503c4035044501a01c058404200110101d40702540768011070b034070801103604180741c0020281d014003528014079489403101d0301400c03d0401d170031920b0b00141c00e101520a25401141031174a84005180742c1c0d02e0040d0003003240c207084e0b40d0802182d01d01020101c81c0b9a081039104204644030301c1003035000720b100030002403a0000d1003003454000d42c41281c1403500103807940c9402041040c28070404502d00d10600c140f082c2103400f2002c22000e000c148500e040038a03280c011064007808001c0540300780c3c1021a80000002e00700040d503954480341d43c0d20410007206180e46005407030501003655801031000700303001c410140c3c407541410704441541c06003c0015141840e0314a0b0810181c00c03400070203001e8143c104240c4410004030b400d4601c1030304020300507840083e0030021410705210b80302e130410403d030744c4504190400c41c3d20100c0c5104100c0311b4201d0403070b01c140300c10241461742072191810b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 897768120 1250 897766870 897766907
    0x1806061e0d05100207060614010e0907030f09080306040c020a0b1f1505120a0204050904031d0d200904020a03030c030215010618080307050a03050c010b090406020c0f2b 74
    0x720710043e0f010041d52150004484c0f0318104000040d51500d42880803100c003c050316066074200c2260280841e01100424030740170140c844000d800e111440e803180c0d441d4240104601e6940f4030340041070200740d840d000c0901e001c65100da88c11501091440f0340b0140c0021950b211b4020a002030070310700143c0f40031070b00400036400c1d10b00040e8034541d41040060003107801044d00328440d980e4041d914022401075102d15900070042000280000e4400d070a0101e10000c200c441d003c2c2c041c2e0040114003503000c0303004201c4070f81c0454288a00080361040c150081544100c1c1c150142d45842d81c04101500841c1c0703c000e0600c0410198102010300a2201035100d49042d094000c041d03075501c40060802c1c441152030485400b14000200e0072100100032105003c1e00306c001800c504840303940131600ca900400d80420341d9582c1d0101d604132995041c80d40b5010310f00514025884081100c0e43e02d040452045601109a0049008145154641d504c602003204413084030304805d84010003c1d611440240d0780c01300c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 897769370 1250 897768120 897768133
    0x201060b1303020a060503100b0915071b17070b070212030a030c0e041116030912050a02130504230c0a030b090d230706090b040b1806061e0d05 63
    0x30450203010300001c582c001c51303c0b007000c0c1d0350701c005c19212803009840320718452140701010f22018034041d0041102c2c010262807031503c11251002521150801842103e03004001907126543c04a204e0303100020b0020350b982c5083c040300d40e04e05560b96000134440c401200d4004210b1100b55943d18000c003103a69140425a03584050f4910000e0041803090308103400710305400075041c1030303051910500309091524a44e83d46000424071100f441008444011000c0001888004c1554962846c0d150446031007003004040346009841003060021208045641c11880d00f0100320100d0707038501c030320950a00d04415001050072000c0f12079003456101510300c0d8106030340c0c2000204224000100c0d51213206244195a00e205022008440c4011412140d1017400300f0031101c000101702100061080b10f2045000040c5c1003181d42d1262103210040390292440000c440811003641424090000780003030f00000791041d80b4182c00001c0a00340011540c100020030b208030b51029072035080c9008002a0040d049030303007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 897770620 1250 897769370 897769387
    0x2060912030a0305160804030c050f1b040e0a021f090308040303080708060306010e0105010e01021501121704050303030403030504080d1a030c010212030c03091c0203070c120b06040c0201060b 84
    0x25a03074440b060b06030020749090000380b000440340c4402050b055555560300f690391075549080380c500f001c3d80010b503098040e4102c1c940983c20100101c900004115140c41c002007019004c010840d05d0885c2e22020540200700b0703990041e564150030b5441c0a400341149814685042000c40304d503440f40c0c00085c16410005804014160044101da06c0b551807580c4800d032584c0c030007043c1a2a1002031103078410102008006000300c0d800b07003001e94a81340b010f1044960740e410303000c01b80410003c2a44520200d15525a4820034032041d40b205c205049058040240750070325042c04641e881c40000e01c084c0800d691600403408101031071080303a050f800c040c0800d200c004042c1072074423602e10310300c00c0d0130348684a11030b240c0003a07500100350f0003040300d10802b0741c0b41586e541500340156540000c1441405000d14120612100d15030460b54151a0f0701c1d40c011a00e035209803528450941c03c541200743c0100341808903400081440041960100e8140c80104032014414000c3e405032506402c05000d04101158801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 897771870 1250 897770620 897770623
    0x50a0602030f070e31050f04120207080606040f020c060a060609140906040509030c0601120209010f08190503090d030c06140c0a0f170a020307030f0b0607060902060912 74
    0x10702500b03a0206922840c3c6a2560603102c3d25640c01d0000d4101056065402501d100401c00310790800d01803404050601c030b56840d600440c0d100b1200c14130081002410f000c20720061242010650300079000034003081d420305c1c41659850000416851007151680000038044807141c0682d116242d4100840f541400e2910000019104c82e000c1c01c0f00145509800013007091100c1305100074480080c1c039680d02500c4a0701440050500100745260501c8104070300310710180104441c42c02403075005401c429184e40c601c1044400801a4010510441d030900b00340080c020105d202c5030322000c940c0f200c03510910709107055400c60007188541d5520105040c006800c0c150400c0b000c2076030910a0b40d0030054120003517000c00714150305850712442d0700028403c0b1b00606004440181c0e0380b2246042400d02c15070042c5941e4a4188100d654401d1a5004424010701c541c050040c6802520918001e01041d000c0c2c4011940354010344801a02240d120a1001e080d91500740464811100107844440c520484982e040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 897773120 1250 897771870 897771877
    0x30818090a0b0123040b03070c06050f04021c03090305030a200102030f06010c0c050324090a05190c0b0304080406090b04030206030f0705091908120c060a18050a0602 73
    0x49005419480010384060303001d2084107180722050b150049010514080c140c540a42c0300108444c0c0b403000c1002013034483c4a44091881440c4603500c44158840038580102605c601806064066502c601800010303038032444402c10b40d088681e8007001501180c101281c408100e98400b4040340070024081c030005038030611040c0d0311079900758000c240f0103000300030f03500300e01c4200c40e400b2601c0202d10115244e0341c40307451000005030081104105064680300040d08140760340081024442a0202d91070f0314003100c7c0907180c0e000031034501030013200e8055200c10f80c56013001c3d0b00140110104000510420040c1641040a071200c880010b03142c0c509454400d00590080c01a4408146501400611044500d08940a40741d01410680c110384134051090f1100314058407140c2440380178000b00d0342c5e5440b0707503120400361401100a4003004e89816111030502c81c401c2c8114284c03000400c99038440c0f481c00600d40360404100d880001c0c6060380c1d034001e007800301c5608500074443e005a6200340c0500141342c025 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 897774370 1250 897773120 897773167
    0x3011401030b10050105040312030b0612090606120309010e1c0605010e010e0f1003021504150903150204080a0b04050a0b0f0a050a02070f02012f03070b0106210b01090308 75
    0x80410013030701c40006540c1030041740b00c01030507030703980c103036001681442034000c070100396800f621482c1005107001100700303280000c0710180308030303803040c01081000d14018040c2c40559a0b020040c5150a864100007099a00c205072164020a10804031201300282410f850b0105a0040000c006651712840c0c0c9195081c2c0038403c50300c040401c24089446644101c4c040f50280f2089041910030b1441c56080c0004141c109001c00914002800005512500c90040c191521a03d03980c003074085095203040d0170254221440075900c90b01c1400248140350300000d07100072144c1c1029a000642d030310341c900030741780c4030041c3c200600025407103040c17008a1041020700e03801101540b60500a40e07940780e1040f805c03801951405448011181800380240d4000c0150714a0984807043d00a41d0b000303644902c0b00700c2c8940e05a444483d510000c1d01d10140207445500c14050a568a040382002821303001410303040da103d00d11050340c20350f0360a180a803a801445600c0042da4025009520b99103160650f00c3d021084018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 897775620 1250 897774370 897774391
    0x4020a0503150a0608070c08040905090c040f0c0f0c0809040212040b060306071b0c1e1802090603041709031603031e210b0a0807030507090905071403011401030b 71
    0x420120038549440f482041e00d280d5034031141281d0356594111400a2000416203490b0003c00000ca101050f500031103104403940c0d8000d021322411001800200c54100e603003810468a13020106c82601d031f100ea21106050b40e1841d107000000c2281c00c01580c00d02c1484113156016100050b0781c23458001c0004818070460141403d08403581d1004241500d4990840304100001c616000e04100000324181200c407184c000c8601800158030f400726800d452150900344854082c0512040000c04000d851031802414400415814144004003041c46800040d0000300542990311130503c0b01c80341c40c015181c041c60300508648440200c44182c85121800d0b0006500040120043c5519840706c0020303060220200c2d5245004100c0c88418075443d0028080c5043d10140c843c049100a59038005401010b4243c0401824203580355151581c81c0400c15803250001c142001300b21008268040381540403a0705502120a070304025000090040c2592003142c40400d0031000080705000043d02c005100300031484 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 897776870 1250 897775620 897775651
    0x412080a02090a091d070308090a14030c01050702011403040b150103090308042003070f0f060207080c0d062c0609011a040c051308010b03161d1504020a0503 69
    0x4110900340d2181c1e484003a00f2081d084020803c010b520ba002074200306a184401e000500c2c9041e000382090190b1340199004d52010801003c0c1d441c0111080f0000e1965501c0c039042c0784c1d40c240201e52030310309143c09241449408a000e00a690160b072400c03401c3e41d84c40d100c0316905d01d090301d0501613401081d0340d206800c1c16080a03c000b0340d4020b12412810716055100d581c829a9190750711040d810059800c64452100c2404d0b81700f080d00c040007207002902a01c1c0310001ca0906044000c450220180d0196085510142003004031050115600c1c070f0000040d03032a494034011906049000d0215210b50440c0000d00300510040034200c1a00901901407040940b0310310b4440d000140c0c02d8400c0030044e0300e0305203598076403d812858150311440121000c4d081890414148582900441009a024180300d17511910324115910701404200050860710303914120140c02d00f0480e0410854440952076043d0500340825080c2200700c04a07240851300500c19903980d512000d006020f90802d50b03860b8689070809 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 897778120 1250 897776870 897776881
    0xc0812150909030909060a0803040e16020a120c03210b0307051e060d090614010602060f07140a11010e03071b0e160e1f020c040509100b0a0e041208 65
    0x320788540070710500b100840c14020102e00b00038080c44042e10f42c0741c1c03000e084200010600b1062010340002c0047c2d002444051038080b041d004480c0183c4030202c1150003580d404000220300c10703001420000c491070803959000f12440c01707507402da616030302202c20315101000e800800851900040d034040340a400307403000699184c05003d2000d00555071881084603001c8801d00504004000c0c0044000300400401d084803541c4648040720401002c08082c518203c0041c848d00d03404005d41d5801c10082190803e070f034903214400500c40c0c8041d8562802804002a00c60045440b62008940c60143d080003003080e8151007803130720344d03030f03400104116400810083c1c50454240028040400c03180141d140404d20750f030314030310543e1170100800f0700303018007040d00e054020390b072103001000b00c0070005441e14400d10190804060301d0040c480c2c128510843c01e010802c03071425808100404c0510300c0080104e484158640060f44020250f00000c0d0306c182600c00300400e2103070b0001d0307104244613142c41c0c503055521074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 897779370 1250 897778120 897778129
    0x306040f150e1e012022120f05010e0609030a03060501020102030108101503080c0615030a0f060c09240318050d0507020406080f0c100516120c081215 66
    0x412490060343d0700020450380301c03e403556590000100a45000284825001d241c0c801800c8001d0032490900c0404940410500040500e03504484c1d0800104280a4a03245042c14000c0340b11400410409001003d4804c11a094100d50368002d8640240c071448d14201d002c150390b0740c00c10980c03040001e0400c14002805e50040c0f003200c0c16100898041c12a005840b03500e10064000700c02524034045101000201091490014125400909024154500301024544410a1b00402c804c0c400e4007d411400000340c80300110400c1c5c4c0f580310001080c00100520140d0f0205801c0c2d104910744a05110f07030749104001e10b4500e034509041502c2c10480449090000280840b00100040266104117402e81c6624012405019118401040864006c3c0c81d802801e081001e0601e0201311030340132038070b045460715102c203461000080030302e840e905003818484041941440c0210180543c0d4894035564111441100b180c01c215412030140c5030b582d00d908a820081306002c0300c0d00d4264118031800403503103260 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 897780620 1250 897779370 897779381
    0x6091506030206090420040b07060507032306060f0d0203010e0f010302031509120409140c191b0b042105030103030e060306130606020a0b060d17070804050306040f15 73
    0x100a814a81041e80d01401c2c070001b4002c190712035900c50f5402c800c810011100400401c041c0540010260b103482107842d2000c266440070308000140360401c5a10020100c0a08031020076000e40c02908070b00d61141c001280040c450344446d20664040011080400200c070f4000314101d60903c0c00c04034542d0b44000300d020300c0c50020301000354140c0090b04204154410a000f064100080c101a2000030400c030490310415401607202c5120940c407140b101c55a81c8000c50b010ba40507541042042c0f4014603000175030440208142d820f0148042d408208000d0040308034000c000350b0b03000d29040d07480d040c1303030601401c415a0b42072201041081c10741500c082070b21940c1501c0c1200c1e40350711010382026031031040110708d0f04001e000ca500b120b0461450382da07042150123040c00400240c0c0162a0400c128201400100401080316001b910764001070000554980e01c0c1c2d01d039102d64081d04540365001803400452034070440d070040b41d1601c038000034802408a0880c00e1707c9a107100b0701414240300801c65141040d42e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 897781870 1250 897780620 897780623
    0x180e090607050304060b0904200102011e0f0609020d0b090114030c0f0310060e01050a0b0c1207211d091005060306030106030507090902030f06220c030f0609150603 72
    0x20000800315000e14010780c003544d00144140030214100545002050407000200c2c1c003a90496648081c680201020342201c12a551003840244070101c615410b40c80024100f030400322041c3c0e0307103082c0741000c480164002c1018100e11001550303510580700901018214541c00c0714810114a00009500d00c510340003019401d5002d80a0701001504400300480f00211403130082d090300440c4108500060383d07210b80009032904600c4003800e0350401c0d0901c030704811580c2214040c40010000b6000100c80042c820010b00320010b00c07140d440300315140510221200d0003024035015100035024030301507041800d10000c600e104410750b420b4500e44e401c10002640c1a100c0e15240301c3c02000520880c01c1080c01180c1c021001b0f0004200f40365a0740c0e80615250441d404810803d07652000002140780502803151800d21002c0200090702b0900740d00e0041c2113240071288108408100d0035020401030030095030085400245440030419a0b040c98006080201c2044030b1007030314103400440b19600c92040704e091f43d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 897783120 1250 897781870 897781873
    0x9071106091b090708010306050705070506070201200c1c0c050304060504050301230711011d01051e0c04061d040f14010e011215060521010e0309060a12060312180e09 73
    0x280d10b141c40f00230041c10b000c0c0c0b201041080410418020034070400c01207010f0701050340006100d40c1d09055080000c100b00c0054412054108840ca0500a0000c0c9094006140c64005e25601900f004151545e40305070354000d01a002c042000542103412902030f00413168140d00904c50450413800c00c258403c2079030781c808148101b03c00070401c1c2034031943c0701e100e40d000d0000c00042c8900001c10082c1030400c242900440380ea444e9003c00030008040c3c00c001c452071480b00d50700c9134130b4241411144c544c2e02440c0550030810502000c81d55010008030010014214058002c00080341c40c9078269000e0312042d4100d480114040b00001031303415034011618126418801200d1071b1400750f542c0c030107420740007004010781e4503100d5801182c2590345401c0f6035049484c140004408299070380d0303424259850b00c507821441d50070034401d006140d102e510454620070902c1c5401c110980f94402510001d01154002600a0100121070784a25030000303a1800104035104550480903500c0d10703007000360642210011210f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 897784370 1250 897783120 897783137
    0x2070b07080a0804030c0204062c04020f011d19080d0e0105090f040608191202060106080f270610090b0a0306020309030f0c0c042909071106091b0907 66
    0x2030741c803d001c0d60f03421034400e2400644907801c40d0001001d5411355003100000101c03e1010110703900c80c0c4581800f092080d060200c01514094001590394041d1070f15481c10301c0302c102062100c410327409043c081c48841c000c0424583c10138900d15400e81e000140203020780c52181d03240c1c1000c45401365001021400707059550358a020700510901111490281902323810913203070080071548910038000c14999000d040c003410900e091904210842403101620141590071190040c40400d1b840031880f5805490740511600b1500c40032540d010307448490004205209001c1901001d0620100744070b401044403440814400b0345421092080318480a802544410f0bd07036000c00c0001c006801a69001d00504180c90401d4448a078410f1a640140400040e540106286400740c0c6443d204000c0182034400400f1200084200000e4072a420003280380d10400c0450f0000b01c13090710a43c042c507100000d210a50f0407a080c988031880d0384141d11058000c500f00784e140e40088605148814074820001036807280203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 897785620 1250 897784370 897784387
    0xf050306030601090c02010905011b1808060f130b0f070e01050a020c0907020f031903050114010e130209151e12010603020a020c1c0512030c0a03151208030702070b0708 74
    0x200200c85c000070030340d502c03210b222000c90428810015000407804003043d4104800400500010326090f40b0140b0001c1e030b0320148940b5400041c0d07203510290140784030409840316008000c47c802c41d900018007038440001001884084200524004d481c00d0f21003c5500b8040390041d102030003070071f09c0040140d2190481c00c0c01072510b205803d402c440580180e400380d02841801504580c00401181d20071154040d0700107159905104841c0140b410007803028903154200d000030401588a0340140c407495020080b1140c000407941103508a0a006103980e000c1000c9000200142e000303118000b104c01c103a5002010821041012255440c1000d00038403040d81c00c00905030000d4118481c04411441031504845031900c6501071240e40449121704086000800d01c0c00a19003410391312650800c8000b8814041018241d00030307210030400da030902140b0728801c071000c98202c800950080c650b100e0018040014070501400a5002c0c40e915801d48510036110000860140320304080107040e440200308051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 897786870 1250 897785620 897785639
    0x11701141e0429090606030d05120703241a0307090612090605070504091506020c04020c0a08190f030b03070924060906020c09012409090e030a0f050306030601 70
    0x780e000c1c1c452401d0003101d482052551509a07076449114290b6040d03c1d00303104007040200841940808214004d20110b521600010b0607405090303d45000c1c1e6401901182e801e030b029030000144100c040416084641041581d211071009500c9a86404030450f000c02c0303214603200c81200d201d0341040d1149004a80390080481d040302d052480c40b0702030f50780c0301480b00c0000c05a0103001d02a803c0c540d42d258a89041c00004c508681c9680e600c40300000040001f0030601e5000b042180b0180003c541c0180c45039403500c0500d040900c031b60350041c080000040c0c0940c0c510616210380d81c05403030742d50740d9440604c0c01c003c0a4040359007101c602e80c3c0c90b0303000341c104110384852030b001822040c40800e20a01d05503100b028006500da00303500b10401145442c0e0702800901d604010300090894100c940b019103500d02582840c41c540c030b900e40282020f0b424022078010500450030070001300103080041008100365004a9202d410000c050030015280b41182c2c040180720300256405040000d0141c01c241c1d19080509 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 897788120 1250 897786870 897786931
    0x2250b0f1906080a0b0601050c070509070509040912080c0703080f041505130b221b030c06030212010609030203102406020714040510031b05060301170114 68
    0x12803400d152081242521194082c040c01802c015008000b45071041c0350080d104000184001c0c1044418898020756070000142101110b000b540c0807600c5455004040740d0500c915580c0eaa001814030403024104245a9480d03843d0f2281075456062540300c1352002c40443c402d2420150006000d0747c00f1403003000d4000d4a80d03401070311694064a020100c0000b16040e104211400000e090b00040810180468000c6490340846d42c130400d08211007a01140e543c0c04030781c0342c002800f60901111964840d903420b040c64000380d0380240564025541d210380c024080e501c04170003424850384840c00000d46501a808100c20769600030090010300a900756400000d14010701000486100b01c0780084441c020300d2244000382145502400e10340303091410000d0456003442c0103e018a02e44400c000401e1b555511060549070b0060792079040e0300c00703141001320540300c50b0021540111300000010390b003604c214440746d8001a9500903c04000244070442c000f0708100c8280500c01134054074643ca411144003030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 897789370 1250 897788120 897788131
    0x30902010206161e050d0f20070f0507080d03060806061507050a120e09160f08190c0e0310050c04051201060b0304030207050915150a0e040c0302250b0f 67
    0x8030074200002d0500d01000300d4420800304c0812800644000d101000740100e418a0342c44041c03e00020059413001c030158803051901c0904030401240071000c12200303440841c54517400100300c0e038100e074481d0b4245880d171903942203800110b4502880010403040100380503108078002400e13150240d4040088507065404006c08817400e00034480d00c07000045040503e080e9078a40d927621960310036030b907200740030b8007020182c10031040041e000e100201481c5d000d442008100c1c00c6141038612038a40d001c20032501015401c140f4145420040c0c0260481e0b80419050010942101100d0310725034040f21400880e04252000080c9682c2040188018108000003404030940007000180181c2d85040500c01504203036421001604442820061481c0048800e60011800c214140501007042c1c00a8001800300340c2103442c9000c0410b181c030b0814000c5103070700f803880400340081c828441d0314907009000394007001600c0d0001d14a40000e51020395081d01c40881c0590088030078030b031500d902c1e041074120b100013403c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 897790620 1250 897789370 897789377
    0x804170904140c0a0306080f0a0813030c08060a0c030c1d0a050315010302030d02030a050a030c0c05151f0b0d090206072f040b0f010c051e1b0103090201020616 70
    0x4000d02c400c140c9120b818882d04807820401c1e10341d2141d40c8014140d0756541c0c018406a4004095040c07100004514540313025404821242da5000201c090b056250450388050245183c003880000d6080c00802d050340b044a2100003000300c0800e5500c1a000c40d44030000300c1c000a14041c05285140003a05559940f9080c0100001c1100741e807000041d107840680303c00c50720080c000c41d004000b182000c001d5950360b0a92070010b503040092207140241107010b280030290800d07840d4502d114900340240d800240107500301c401d81e5164081c451000d202040141c529141000315884280d04c490b1808840009a95144a4440c50600e0005480019240c240c1c2d007071740e1140e010010980040e04090328000d400c08541d030540881c100d1740988602c140c007040c0c50580114180f42010310755607200c0107104a030700000d090844102026081580c94a09445018805600c078901480c1269a002031088144e80300c510386c180320700400000440603503559850081c0943d00c1640855404d5244242801481005c0d15 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 897791870 1250 897790620 897790631
    0x90117040b07030b1008420f0904020d0f0c050d030201020307020f16030611040e040507030605090a081c09140c040e2b2d170402060901050f091806100804170904 71
    0x100307c001300c1a20801a4040d08464044000c5603003400354400201d01e4017114404407620b065008201b0141010700000d2240b1030304402e44040100d06a500c0001d801e010341110701551040c60060700079442952410701500c180f213401000203c0004900080d0100002844242859a07640b176000c0c000f01d0200f010b40141c207100204628103540384591080f8020700003800380c6482d5052600032207901804400251300070044800110b030b00c0f4001c2350b010310040d40c00c030714105100c00806030041080c280002e120601e9032580075100301000449009c0814100c40801150805e40c0290703680d03584100c540d000100c03103801101038103001c0981d02e01c0c82d49114100408204c40c1c044c20402d558900c03020013011082c41a400c0280950f00c400e009000c80203c121103240c5080a400003403440c041c3e045498100308001030210960010002502c10300c24000d48004803042e11090b10551051049480c0342c01095182c440304d4405218140e50341c000c60700501000c143c0113440d1303881c151075404080d140790040c0d100d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 897793120 1250 897791870 897791941
    0x180c0d030201231b0c0a02100c1209050a120f111c0606030606050f0114090609060309060403171905060f060a08090d110c06090117040b07030b1008 65
    0x410701054690903000400c400f0745440c8212800201560004249a00c0e080c031101041c0c2c2c0000802c0045550126052556000c2c121402c85100381c2012000b480e00b540c130b680b8131490540000002d82980c8084482000b1952105650154154100000b4140900902407003010444981400c2110b10000d00840786d003404624000401c6121000125481540c07194200140034191003880050101191002d0700056007a000034000500c0500b004580f4000007000d95541d5101e0044030207161010744565160b242c07030100c0e103440301d81c00c9900394042045070008511070a100c43e9040d1140c5900e1445450801900240400030700000300f083d038001e6030783e00b030441c110b68820b8040d25000c0020380d91070307209181c00e606403030900d00a200b2503014007001e007115013090314011070044c480107025140243c03a110300c00d0048444131410310104451142078030a00c0140031000900e54850712041e1000c2c07004640200900c184074a00100780c2c2c000541c2d9001058088105021b41028003103140340113a01150386 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 897794370 1250 897793120 897793151
    0x2180a3503071205070606060e03030703030e01020c0d120f092a1d0703062106051906060206091614061c0203150916080f0c04080102040e040b180c0d030201 69
    0x8585480042400452005c0401c001401560050501407030900030208010010aa481c06131260040606407140b480741010b41007507050f60440408041118042d42c610b84c40502501000008140d000b8140340f403200c3d034103003140507400350366a11182004000a89041180c18400d40740c1c1d0b608601507039207000003000a801c4210528802d2050f250102500303100b080039084909950190820720100d82c0d2100304003c020540c000665003100010071036070307100845401c4d210b07044203085648518240b40815901e80c0028418819080c02080390481c00c1042070105016545105200040c055075604544038204540070702010f0303c13040c2c03614015002c000034440690b00103c8a81041c05030301452951149000810756801c0b005001c80142da0718480d040061052100400161075100510003150344030102030110750042c00914021512640c07a1b6495007070384a4152015140e03150440080707074030300f0703098540c22181000220080c402030070640e060201f1000c0b07580058096540e10120554007000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 897795620 1250 897794370 897794393
    0x10b040b1c0203070e03060603430603020705100510030213090609060506012003160c0e16080a18020103051005060d1b020703030c170d02180a350307 66
    0xc3c2a180c5c1c030318814118040c1841d003040200340d00d100b544124139208103840309030701094449401c8820440c1e070f4802283d03480000880d00890302d022a202e104000f42541d41940580480c0e44160217603514032070401100000c1d00c80513140e4016100107640d041005107070119120814110b03040010a101003a6201c0c0c03c00c0b01c01201007a501c1945034000c1003030540e030042803554903801660340124030450b440c1d00c4d10b54a006400f13841c03071443e5140b0b1a51090001d101c080000524841100d00140d14041c81090343c00507406000304c0201d04c00300c4c00300b80c00e4030b0180030324095010300441241180d07a0750340045019160140c00504844603007030004c00e05442d110003c225402d4016030214004101c81d02500503d41818240c82c02c6410222081c000254001e0704140c8117500701c0e00342c001341c09031090b000c0c0321481441800c1d0545440000c0046040c0b0b050058204441801c4540000b841d03600c0115024602c0d0350b02c025941d8a4650703e010842d13004d440c6010b9400c3c503d05e8100d07420121190303542607400c076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 897796870 1250 897795620 897795631
    0x801031e06060e04111c0c03060b011713060501050901080a060b040204090c0e03060109021207031a0a03060b0108100f0e150d051006080a03050307030209030c0301110918010b040b1c0203 82
    0x5203080070304411b0524541c800c0400464a01d00c410002c3c164894052000300303400f0041189480b0300203580680e1180404114860003950b03419141c1c1410f507810320044810110841e00c5a0802000040925000c151030781250b00b828043c200c02000d580c0c803100100444a415035100307509110220320f819280c811400561b0700e41d02d40c00c030042c421508040c90188142e00c00e964007070041144034101e05684460710b4001500b03080200709041044442580114003038803554001140d110000103004a64201402122082c0ca0302042a12180d0b26541a0007880c02904001d15400a04003c0f20700d41c8507869500040c000c452500011000c000900742040f403d9080c0d80c00e03886204108130f201c40900c200002003041c140180f66440d0f06a501078043d00000b03000009050b400b14801c0f00c0750701d041c0400015000700500030400d4a076128501e4032213030072110459008058500b00d00e6002109418100e0595102d15600340c2041c0c5801070360001a4042e64111a88409a5401d12802d42d140d001950198 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 897798120 1250 897796870 897796883
    0xa0c06030617010b01021c03020f132405031302031006031b080106050a061d100503240f1903050d050702040c080f1b07050a080c0c010801031e06060e04 67
    0x82d280209207203042ca5055030200e0a80d14100b2102004da03000242e101b41030862580d00d0344c1440b4820005e40c006d008401ea0015012800902c4810f1000c035070003050b041d190104c0b03100076016100d404404002942c6203c0501042c010004510f08426004001c03940510040488042034401e00c0d0580a680440d401200c0d41841038103c81000e00d42041280040c0000000800507a03283c500001c40034451882007109116428020040306041142403001554010300324144802c1810f200071303c10f0348100c540d0a410314420480188455240d003980c0300d1080c000384200d1506860300c0400c03078001d80050310240449842e8900000042d000d002114440015855143d01c2e0a0107005000580b00f80c00c01d1041000704c4001006041c0090800003a00100c3c041000d292403400d44185121034070030500003901c140308500c48401040b401c08010f00301d1166070741c261500380080c80015200c110080c080140044c083d045607103807041040302c1c0b501642e4014480030887c10b99400704451526000c1c3c4e02039800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 897799370 1250 897798120 897798131
    0x3040b0d020a090b031018020904021903180c0506030a02070203060703090506250c020303040b0d0207110301091a090c0a03140607050c071a04030221070602010902010c030e030a0c0603 81
    0x14140c10511400051444e502100d00e14541310a0641c0113100745c0c05040201b442c16034800000704480d0341692040072004d4011596007002100d0301940e2180c88514000203401e08060380b00704212112110a010790040600348502e003408100281d5800040111103040d41c20b00134480942e07020400940541070b251000103010f00c65003030131800c1c40002000030030f60680c1c00c0f1400c42d4852005a0b8021408441c2c40c1c01d44401640c1d02c0024298811070f0701404031868007155038144d12405500038540c0134030486280c20aa5607030b40c01e0600b600c101c3d080c040c110822594009501101803950a6400304403202651000c102200000300482aa03402c2510003072880d049041258408002c215041107040c2043ea0038010100e0340030b6500c6250b8080c484000e00f01041403452203942034207640c091980188034903000d103945007050302060050184042548030310100060000e0042c424900b11980607035540d507030400300da101540c03048400c05000360188103061566011803503109050b0b0103818640e4010a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 897800620 1250 897799370 897799387
    0xd0804050a082106040212060121050c12150607030c06060305070f150e09011404060b0c06070912020907140d0504060c1716030c21090c150804060b0303040b0d02 71
    0x440d40084c40140a1071040009651400c2c0300b105655010100346041d80c1d0030912201c0e07100e030349030445503040080341c02c14052008040c1003001410050401c06204941c95640bc501491464071104200350882ca04012034404070740301e6090085e64a004500c0070034030706d07520303030701c41340303414066481852030f060103840500039000c07142136040e400242e41c03908031049011000022130660044c814410400600100c03075076030303403140d8010000034100d041490352662900a112504c1d18800c0300d40000013008800701103041400c102d00c408002d500505210390598413010141c0380b181d400f003140c00350f821040c090740781a50454002d96118501c10840480c20300c07040d0b00054a4003000c00e55103481000c8100400c50084800307941000404401d15020888070054075040d9592046100e10002c140101c0c40c0c41c8017090a950000740400b442441c40030551070796061000b120301510103c050008441201083c080b5a180d000762074400e0004090341c6c5001d5071203000310010f920100072000c0c4950045030302d50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 897801870 1250 897800620 897800677
    0x11150a020a12110c0f01020f010f09020102070e010602030f130905101e1802030403090e0903040e1b0304150e01061e06030e06041203110304080c0d050901020d0804050a08 75
    0xc50b00700c85418100d5201d0403075180b5a403161072020096005012400f4444140c1e0302c01c110351f44144410f88000c100d081c1140c400900503120a80040c1d0141c440d41500003056040803888504886c100e40c05036007080c80b00e28268059602c4170a02401e81001c0003c00b160b5020396100b0399010f0300c00f800043e4552441d10b506c9071003500643e0030084107202c4616017000b000c40340c070b19040846002c1d15030050390396a4501d0250b50500303054002c030714807405010401508840010007402524003c11007041c40d55501242390141c54034104104810050600200e030000304030580181c99031154000205007070100d9080242181e21039031191400401c4050300c2d81044401210040c090122480c0c14055140443c1c680303a550500940001c22449151101520300d911962204d2001c2c96036941c501e07036a0800341003504550b08040c50b07440003405218040705c8294010300844aa0308810780140c01000b6104005550320a0000d1050f43c0500034200041c0014010800034000554001344410000744000a440d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 897803120 1250 897801870 897801893
    0x120e120607081f0b030406061d0a1a280e1302010306050d0308040b130c0308071406040b06120c0a0602031e030709050f060712020609010b0a030c0311150a020a 70
    0x38250300041c210034a80c46103500c3c0d00d6405894443d00030954039221460544010095980701c1e0201d644014010f601005030304588a01800e446d01090001070b60210000c4248403080070010390143c010513540c90b51403c15021040e20000f070b04c480d00901961203610303800d0503400301c90742c100d2840c0755003107a030031583c051280c8000390005540742d15590103580c2d00581017000242003d001c200c038020010f03540d4060140803680155100c2010401d151303580c60108003e401c682021103510022404040006800103078480c070031b6402c01c92022140c2c030f40c8001c5c01007103100c40d00c0c1d9501c0d9006a403900881600c48030405402000c1c0360b40150703901e50a031901c2030040340207a14185104071040051054041c1d006a010050743d0084072032002083c000340005004d0b1280000040003481c541d000c4540c00c0c0d801158280c8100406d00007409030f4801e0b0002c0003183d03040c5000081218541907018400b0404410140c03100650151134405c0d05450a2200480703500903000107030041e03001c101500e00f0420780c840700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 897804370 1250 897803120 897803131
    0x20d0f0608240105010302160503070f20030c13020c1213230402090109030203150a05090d08150406050d05030c07060819090618081201080c0d120e12060708 69
    0x204004070382d0900c801508141842994101600422440302c041d880c1d94628995a0f402000c499a405003403400c0001c40b09004411b03180b19521410382c4000030041c071400c4519910003000381c0030100c2c00400300508880940b080e041a16401d000d0ae0304007042c00c004408080581000d120b03107035000028408807000d070503008001041a105107402c84040f640d0b5018403101030440780903072a40d0b02c00340100c45100c00c590000e541362043c50301d000c5d0360340c0c003442015015242901091040e0758441e0002a0713582c80e943c1203040014a820000f0741d044020b64148480c6503c000d0000c1385085e0744000040c0b4a004186080d549600300049000000d8400c10440e0000c0c03009042c40700e40c5140c840303004820541501c49440c402516000d080d8100310680d44402043e140a40000c803e01500d81030148040d0028891800d052050030300102d00c00e9400103030707541400d00003083d4001d4281103a451907086404021034005000d50814540b0103581c44804010480e180d48000b0401842e10300783c001c3c00304201821 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 897805620 1250 897804370 897804403
    0xf06080402040b121e010f05150f061c20040b0c0c150409020705010e01020f090a050a030b13170304060203161e200a050d0206150a090c03020d0f0608 66
    0x242450b134480082040032940c4884070144e42e1150f21110540e02408400d03004200d42d618000c100943c104001002c0c20740c1c0041611a02d112036941c0051290fa40704140e080c050051520f0000305080302940c005500c0703841c001c0c242465810b0038071a03c3c2004e40240c0c01a0610060104072042151420801541c6005040f0303041c0480f215031500c040036510650080f01101e41d000140075050050940001ca20300f5480c8008541c0c41242076402d95403500301d0070301d0911542d041c03d8002030303501d0100403000540341c04c100e00510f40c0d11204c20807012014201401c417030300c45106e082c181c02400e456003e180300e40e000e0200940c0d80d21f03105e0040001d81c2402c01081c404c0c88101c000068550350756030012000c1785040e040008203290035058038072840c84500b500106a200d60140712082240c0031880340c079a01c0b460703000c071100c58840066845c2001850700b2569044446031a0070002c000c4d40d40c1241088150500f401841c0500007a1890152480780401500c0c254981d01d00b044280000c0125224561600c107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 897806870 1250 897805620 897805639
    0x312042d03080318160815090309060703090b0a050d050c070f02210a080705060c0403030f050a0c081603020c060f1207090f17010c14030a090c0f06080402040b 70
    0x518044024400d07010140101c0c1002c030018682c0c5800c1c91410310040d0303003030301159003203840c104078980c6000c058000d0101c40e02a4115800142d181c07001d5041c00342c0c1600018600b0030000d0000d210aa03004050140e0070030403c000c0c00609241044020445c041a56680c1c0e0b60b110802c04640c010354801503c095000f940c00c110341000f00b04800009200c480c1d045034007069250501d815502401c0e450300d400300f41030090036001d03410441c880d03004011040c403440030740d1403580d150031607030200c1d014621020f40440c094440d442c0e0200e1040008002005030740c200400401616200d0484c82d410208241800300501881300e002e05070104000040100304640300c510b010001749000e1541c1c000d490010600b10300600110380c0e082d01a2151101800360301c4021442c495848110100c5080a619484050b501e00240c2d80c503814490700a00d0081c90301001035619689071844070a0045c940d086040e40d00701900b000210b210201048070000805e035130380e60f0008a01303060042000b264014211240b0401800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 897808120 1250 897806870 897806939
    0x3150106050d2d0902040f0b010206010e2a0a080c0f07020f1309120905010e010822060e0106080106140d0f05010902062802010e060a1a031204 63
    0xc86141c041c0503440410b0414810b003d0344000b500003101005000103120b0070180307070307607881c4d1045402074000c45003030050310080da24681c222000803aa044c0140c022030014896040000c2c48079802119082c0303004038503903150060b040e4411021001109242d40001d4a80c402a804140340341c00490194080c2e10b44504120342a2580c4a4044024001e41e19904810065504e041d00140c1060074004188664a468603105141c0c00380b040f07001000c2075050501081c554410380a4202101043c0c40ea00340c0c0c4d4a69020528118440f4400d5040c180c2e160003a910028416001d201e640c0111030002207149414080000c1c252100c64000001d0007400823041220b46e0707550101d182500b600144944020030380c1d82084d40c054044a04c0c040c1d0840000680b4036001101d00540700c1007a00c5a11001c814856408822801d03260b05070540c080540c00400442e00b890300b542c4c0003000c01d14100c06a103844820003000b1a0134007034104041422144003040810080c0c81d00c0c0c1c1d08035501040c03084070f080c542205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 897809370 1250 897808120 897808127
    0x25090f0c0806040c18030c030b0709030b040807020301180c06120e0d0e0a0e040b0f06030d0c1205070615090516050d0209131a01140a27030c120203150106 68
    0x103140c540f01c3c80c0c403413000440c0d41d400f405a040312480f00195002c19251281000e050142c040c2c0303c1212255001c0c40081d00441c480c0c002407040d82c1d8850300c0ca6038551640e440740c2c040c40e080480f0980e0305540e9000d50290841c00030140c2074403140701c0c91180175240e14101c0040c00300134000c03411200e500d041002001001d0740c0410346248410b001c0c00c1a0004154420210b913140080f41c101481036413102051005000b00c500e00d540c408e5032a401c0c180f07000d0b521002070546030603b046441001c0342c03803000300b540051014400018070510700e00e0564140406a190441601d01c038800c030001c000c02d00c000503c030403046405a503501064504d007000203103255940040c014400c0c0b141c0c280f482c544c00310b14000590303519288110003a00c00f031020b100c00b142c6090508100c0b402040034501140c117400300b4120b4803019405039170b0b90141548800a0301251642c4141482c140910700e0b0a4040c20300501000140f00a000c1d0302c0074150500341c0604011540c81818500240c0fa208118400344030070040161660 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 897810620 1250 897809370 897809387
    0xf0a0501150812070602040e01030503180114031515070f1703060109150201020409090b0a0506010e0607020108061f0c0b07080f010605090d080307210203250225090f0c 74
    0x4501c0f400c00d907184041c1c10407038024000c5821100402504100020501c00000701030188210b032100c1544009030300100543c0c9480f004180e13600303503640903c00200c42c1004c2001542180c4d00180a07251034120046018295a0109004546d45039000c0d0b9a0790074043d02e26035980215443c100185d1441c1000b60028224504601c1480e0311092404410036846200390103403002051010001d001c0c035501c034038110f0b0b0800301c00c8500034441464a000180103601c030740030901d00c4500103442240b828480f500111114040180819000000c00c014860081112038102412601696941c000c1ca0203601d0080110200075084004004180303083c0f1040c034402c01318140c1160b0460034044c0d910551040030420100752030720064500040030040022440c1c000c0c05010781c0b0345c000e03140300302100c2148003140200d01040c0c500d18500b505080042d000c103c94058100c894203c00d0046070042000707407015011091843c0060703210b010260f607040195088074020300c011242d40510900c1018080d0500614200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 897811870 1250 897810620 897810643
    0x70915080f03250c0303050705010b041a060906070f060c090603020a02030301121406091f1b03050c0f04031101030506010e0906060d090c0905012d0501120e0f0a05011508 75
    0x80c3c0101150160840d07061000d1031641d202180005059a03030501806c1600080010b0b5069420b0988004081c6450321a40c1051503024800000d101944010b0280e650880c1c1641a00000200402400f0800c901c0c2451005481110042003400400c04000c0c0019119403080341814014030044850301e80100a03203046d24200c1040210620082c10158a0440e0408050100303015950601030140c0c40031811072a085515100800041c00f0310790003000b1a00080c400f1680314883c000d090001d944a500440c0c3c012a0f40b4034560304205800c0650401030340144c1c0300300e410300e00c0c049217440b10756018059168000d400342003464500a170500494120b03100200f800340f1803840000c600709440280d603c050001034000300600641501d600400b00100028080c0e0350351001050349802541d642103000c6c0740c4550900c521f0700603851501006548501400144503000350310b40750303840305554081114210542070040184905902d5003441400c503501c081c4000000340d070101050200400c0014921485da = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 897813120 1250 897811870 897811897
    0x22a0303010b0f090103020910080702010c0207230303220302100905101124060f0307180c12090302030703090e0606070807081b151f0510020106030203070915080f03 73
    0x84100f070340106c000340300390322566900c40e06400344060000d034005600740c8520b82c550020020f408101000380d94401d4079105400c440d8000c500b070307045803428140c2d2404203804094210307401c02107075080e03290489501c0000d101100306881010401e5241014110311642c1490500c10f0b400c0d4144030210307030000c201d00711903820702002d525450a810001c00c4144102914003074100b200f203000050841101401740c031024800c0c0203803a06ca000c00e203070208460003180c0d40c941039214000882d101860107000c03036503114024410883d0b01e030320303d464042c0200c0c0c020f24402c0d0b018550380c0c042c42c83e002d0000706490704416183c0c0102801c011b00d54030b0300c0e421920141d40103a1419104c90440c581105107110303010b034000b50b0f80b0420400302c10700c1400260712004095a414003010302c1e038800700e44804c20145c80358015203000b50b1010070031143c14512404662040140300111300180c4a0300468904403513940280700d690f03950308031848501c00602400f809840004d0252142101c824041952030040031030001e140e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 897814370 1250 897813120 897813127
    0x6010f0f0c0215030c12012102120313172104061b020d03111509191a0115020c0613050415090e060601030516170c0c01022a0303010b0f 60
    0x159654944400541001e40f010079541c4d02d040303814150117801514091142024403000411400c2c103203645003e0003080c25060091004d03080c6c0130010001c4801c0b00541c0b090104000c604403109840590718090507400144107820003010810f240b415045204901c5000041401101c102807c071040328204c44c030324a4001d8140c1f408403c40d05818010b98030007035100c407450346079004064103c51314541c20404a4103944500140351102e13204600b0884420000d0703000b00304103848100801c0c6070820706a014204102c126604175029140691082c0c102244180103045d1120000c3c0e81044800110b410603500390b030605038002020382c1d010849000303141c03045423500d041101241280f1040e03001071a01d03034414000081e64044058644100390741141c0001c1c10840001c640c05040400407d451b0700681d101c03401c8007550324500d100120094103a0103a81d0b020062001d5210007400541480c0100c00450311461410f10005880076000b6a03081d0103d40042c00100003030030400c410b0f2460714015130000c503034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 897815620 1250 897814370 897814373
    0x1515031a1f08071101022d0c0a0f061d011407050a080624030c04050a0902040605090904050102042c01090522050718020702090f0105060d0e0717031206010f0f0c 71
    0x1d000c95a51600c2c4d41540c40403c8500d10780c2a0241004881c444100032100258200725801420f84950280050580e05c05001c6200180c41a030070005628010200000c00c01c06025079034240c858002c1800710569181c1c5001400b09d44414185504084e05003031407803821029000c054070700c400040c80c1c41d01c92110000791200c81d8090011082c02080d480d6445540ea1508900c8004142c100303000d120f0141d40441004100e090046c42110709a810700d45406041103081005c10a080400500403a03465400340704c0040d0940204141c83e4a4503000e50308608414041c034240644c02c40141d010520326410039091210080245441c1240c000b45441181c0e400107846c24180d24020003079009160412041480c1c0348040019809854658070031106200680c5a584804580740c400f0b00070903038085001c001001c2e811600d580301f40c0c8100b035032006603001142d40303c00848000700c019091240c603800004a0f0510701003401e51a540c04802402d116030081c2d07401c034000346034500d440c40e00c1d802d006000745c4040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 897816870 1250 897815620 897815627
    0xc03070608130602070311070803040f1401090503010c03060602060c1801050705150f07120510061b080f030405071508010b0d021308010e0f1b041515031a1f0807 71
    0x105950811019582c40c50740b440d004041f00104000305060b8040d005c03000c582c811012045808848549510030340c0c0c5030800c061900300f4440c0400041c1072010180d00001c40342c0b82030160015020807900d00003941c4d4508040079040000050440c0c400003010080301c10800040c2402d800911001e192841d15180c0c54501503203442c8142e00400002c0c3c80d2141001071a4100c0681c6a20070700b810780da106000500908110305881c001c0d103c80b0300c1c200a60105028951040c491300d107900e90b0126403001c5030300072038480f442c181d80310203544d00e0710410010800c410f10904106400051003034800c10500c0d001d56040c020036942c81805003881c00d09002076110f42801017a016240500b55030b42c500c00040d907941d07200a001b801c4803d10244035009035116520101740104041442e100d800c101c0160051000007000000d101d142c00300382e69184100f40c00300d4128000d89000015081c00d803800a150b5081818000d84844058030300c034807a0100102031818004050410701c0410040e040c05e00300358032040c80c2038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 897818120 1250 897816870 897816901
    0x10030e03070327080105270607211503060509030403110d0317130309080c0d0809012105060f06070203030d0906061a120603010e030f070309050a0e180c03070608 71
    0x410078150f00c840801c4000301944614050b080f104900c03c000048240c0c40320310701d1202c10101d0304941000d00000e540038010300308024008148070034419551200004401103610f00d8445404100c81c0d201c0610804c811445210340100d4200000d600341440e5989040740f95519618141c001c125a100c054100760107031100e09180c0311421640411854540c1d460310150440b100140e00082d450800016049800304241c8940c032400342042e81010800d03101c0040315801a02c1070340c10000d00e021031452406031100d002000191010021406041000c04c00885020440380c1d540326036010000000107aa00104030b4421102c080000300c0c0c62161410300100400e031a40c00814110403507103041c0c520303000b401d004101c1142c40c540010303030f181c0718981854200c2e1801c8400383e0300795008004c00d070f107a500088007820609200703140c4100800d031900b012410840203588200d4480142c2400d1000c1c41c03146152145006008000910403008071000103546c412080c403035038041c27018000206d05a540c43c440c0e00f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 897819370 1250 897818120 897818177
    0xf08071206230703020c100c0c030c2a1a0306060a112d06010e040209010515040f0b040501030b2e02100228020d080c0c161410030e030703 61
    0x140c90b2924010001501941c4458600c500a000f5035901469507103c40c4154204410740f6601c02440981030fa4055802e102d4802054900c000c0c20300e40343c081c0c1081d1403041c401800c68001640a00e03031409000c811540008910400d4603602030042004584800c415a081d003505880c20007504101c0310311081c1003a20b6581c103803220022241e0300070002c4009031028507060303503107070100ea5160780d80e52544181501305440095200c80860010009454120701000710103a464404030314042d5110700c1c03003040110503400440a141c2c08541081030b9a0148148401c8010507529014402000a0740610520701c100d500446e42c030020300d02e854010310802540301141210b400440d81d4540901c4000e0b81c044900341c1941c01005680102c50302140b002c01c0001c95401c3c01c1c5c0310001103440c0e141c8820300740c0d003240310030281e1481001d00c440044500702e0f031414002c00100811601407280ca200740708400d007a440040c01818140311110314003003000422104665058074080740b800c01a20003001042e484000d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 897820620 1250 897819370 897819431
    0x2030d02030612060a02040f0f0f14210a0b0a020a0903080d0204270e0a05030f2b06080118050c040b04060e0a05090d03110901200102070305040f08071206 68
    0x1c00c8171130841ca500138015580d13800310740001300740c0c0c925240010800b240610701c400010400f040100c0803407698a40c54100d03008142007164501040e50390511421845280201da01210114084c0068070030620b80204111200f5842c0001c10800600649c040344802045803a0014440040e0346081d0305036006040c2500d0b400f00006500a0740428424003804105d0405291031062103021400082c11101d041c2e200e8003a5003400e100f6042020b1035004140302018516445c6407056803080d58080c645400b43c0700000000c2e80c0c0d414907201500311004802c4080d809980c1c0300303504000c02e500041d2200700c20000c84000c520b5003c001c1c08100601182c1c0c1c4050309101d0400c040c4405606140c10952059015004940d1a10801281281540e2541e0811103199500300103141d10341d403007000714000c84140c030741c0100c821851498000b030032139202c0303181540020804901880a036031144500d0f402002c100000380300d802e013854801600c1d4002c3c1e1100601080c0d0354252400b18941c00c1c00703010b0107a4190340307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 897821870 1250 897820620 897820633
    0x2a01021b070f0803090d0f0f080a0309030e09010f0905090106050d0807051510050d14031b0f0606010801170118150507031b0c02040216030c0b010603050702030d02030612 75
    0x300c080d549010034080c00141c50240d48010846420001c1618040300004100110540f1552a0030308a5545468151642c03086160104003240c4c09800030000c4512654001407540d4a13410010100401e440e8882e10031101000100300711201c1915130002e8544040c0005847d80311141d2081c0104016031080341c000810400d580d040c0000350011b850601c2c005d200b41c4601d41484040209003d20441d0800c0404940038424410780c10300121003061030344180001e4a06201d810074140c81e5801c140e02d6940da4000004408034200310903c0219000310880004069508241e00040c0ac007140500400306000041344005001c514250440c405140f00514074031714070b84050401e20102c51701e015280c3d590381d061a0114070a14442c0c8140c14000100c0d42c2c00300d03d15460880102c0340001d50030310603680039409022500102e52000860290700e0301c40d84594810501c68980a020780005070f000c02c05161030601008810768011080302e0070a0000d20b0700603a699a0320740007505190214498520503c10381 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 897823120 1250 897821870 897821917
    0xe0601080706091403120f070f08030613051905090703080307050417210a0c0b010b0a090617060f060408150123010e040507090b0c06041101052a0102 66
    0x4074426060300e5007581d03022400e98a48130281104081080c00a4040c1d004210121041c400360000e080c070850094011841c0143c03549511842e101c1c01036065880810000a101d0546041042e200c7c5103081ca002c203003c01e00c0c1c0004115401300506600484117034584c80000d4401d8410700c1300402650784039024036201d00b041d290003485900b090051600400042c901c030b100040d40001c028504070201c80c0b01d603101001c810b20b1504550002d0000c0740910246a030b50800145042c58228041c01c008141e154480e000842d000340f03484415441802030091640d03030b02c0f4008800b00f1405a0045040d41c1d07003030b1294001c0e000b1072114820703688616118080e5005480c0031001d11880e05040360108500700346081036940000440e0035090040a0126240d005140c040d401c2682056912144601702401c0381ea644113241d016940c0001c00d0311086800140822042145080014038544800e19045051914070103880c81d49103c1001e01c151050007440000380000003d40440d440900d1142c2d1048220501707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 897824370 1250 897823120 897823123
    0x90c050d1209051e041a0a03050c0414040b01170c040207080a020105090c18100807080307150204261c03092616060b0a0f03110d030e01030f0e060108 66
    0xc0101d6800003400107500014180383c0301142000f405140105113000781e46581c100801800d8024900003035180095000c1340c80d0303070342d110400000e50069000e042650401010003040300c02c1052005582c0b50000d0a010100c3c9140c02e901d8117444101d03d030101040c51407a0800d01d00448503440300e9102c2d000180a03010004048041c08800303810350001d00183d05c030b041e100c90b00c50754015030964100e075402c5044020506031f031134035a402022a513550054150cc41e81c45601704040b0f82c2000d12a940700040781405c02c074400c41c0c1052000194803085080a040c40d440c0300300b9018911200e40261084200340304007240034002148500d11882c0020100070340c8100c00740c0984107040003a00c1120241e803d5034400e10510140c1c0b035505d04c00d442c0c001d1030000561462000c8140c00350040d20000d42d00c0c01d40c414584c5801402d48094001044585205d42c5035207042d1482143c031034009402411083c00d0400040e40051000784542024200030420350980c1d51000300418200981d10384522031100000b44c030040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 897825620 1250 897824370 897824393
    0x80c130e0a030e120609060a0b0d08030901020a0807050c0c0f01032322020306010504090510020c06060f040e060f070c080412030215010815270c040b1005070204090c050d 75
    0x50540304d034024440341d10745a54583c18210341145041c0c0020001914030b41d4903500c0141040001441011244550744900410390001c503641c0c040c0e6980050310702c00340d54010411590142ca545032162510300311225403a1039000002c2950700864400e90354540f1340e8007a403c04402c907100c540e0035022020b54040f102564100030364042c01c0e520000c8090802d4090a0f1403c01205500907004014503460542400014000707080305803424056681240725030000c40c001000405202d030300400c1d070b50510f0010062907000c00d000c498416464001220001200401c03000e034070600e28104402e8941e40d00c01c098454100d0f802c0c005001c0a800980464240d040b041c0c00d00409000f90308441c0d180550ba489a51070500030700402e080340e84400a141018210901c000764000700141942e15880441c0041d40c0c4a9040709171201c03502c0d040582012418209846154500b140454041501640300c8901400382d02c41c0c1c00000c1e000d251280208000c0c0415075801c04000d0501821103408400c0a0400300306003507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 897826870 1250 897825620 897825647
    0x1113060303080601020c0916030623360c0d0905010f05060604030804140312032e1d150919050c0a0918060e0c040603060b0301080c130e0a03 62
    0x1050000410f4140d403001500440c8098040c1a10301e40d81c80381c9444541c0c3c010840f4911003019203d640c0440d601c0400e544643c04080030665103156140b020040059101500d8600c00d5441c19000031003240e895900900014955603030b4400343c030303070f03c03400c18465091040d0000c1c18002800d10000508200e4154080c6403030310750b0034901f0020f9031201020018203204501c40601020000d20050162042400c0e180d040d1810007412105040b0000d0455075858100311241608810305c0c8184115030302c00b044e80e01704c0d00d103c100c0a100704581803224480c07160405500040d9408a88000a0311007541e46e02d94100290380104100e445140403103102050b4145080520711075428100030410b13541c01e04058941503101038a0b0b2900080c02c2c01c1e03c0c01c00c802006405180c00c151548000500d4085242095018814196055940d01d04210020342990070301c0d0302c62a000d410400040003070400101d152051504100c460010340400a99120042c1103080024201809050440000c158102004c40d4419 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 897828120 1250 897826870 897826877
    0x207020409211b020a0510030225110f061602120105011712040e0402010e0f0904080a02121206060f040b0415141822060806041110020705010c1113060303 68
    0x110529100f20201e4070b101030000e41105d0510401e2040c0c2c94500c2c3d003250000300500d07005061543c0c0b504d0803c00070400ca401c81074482840901403091041a003c860071001c401c0e41c11440005074880824803500c20b0521206522040441ca0811561059003080451214100034007a5503104d4000c3e41802600207005440c6110307103080280d2500c0f4540927a8100c54803c066505141c1d56900156000080d102203507034840b00e00313403c081e0a59120998a402640580d45140c0ca07501302d220064900501214560600d21040c044a4911080102216401401958940c0e12210514120f038003034001d0380c100c01074805002c9800f040100510b007116070010710655480e066030342c0a85000d40a40f0640032810328440141c00001e14505202d946940c00400304c0350402120082e150802d412122079802c0700300b20303802900030300003802130031040d00000303007400c0756050312000404030081d507110242d204850509c550480c5e854240030054200c000000805002c91701d18140400380900200b0f150300048011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 897829370 1250 897828120 897828137
    0x21c1a0607051b090106120f091407090c0509032a03031819181104090606050304230304151b080306010215090c04021b1e06010e0f0a020702040921 65
    0x213803804000207812169980c58030404544c1416a03d0f02030a541400c000f10140c440700410000b88500c0ca1b0300c1e00608051024220007800d0100c04c90903200c01d81e4074102004000d01c84050b2307584e804903920403028200140c5450411000c00078040482420307415941c10300001c1901c1070b42041e0348004a40449007118860800807940f081a018990340740200b004118070000d10700c4581c10940e020140590020080341d0900742e5a00c00841034810030b81040000490200902040045009031026000001e400016014021050440c0e60340200c1c07143c04001c0c07919001507240305002e030100382c0c0801c8000c0b445052040c1a420400101d5106580c214014401d45003038040000740e000d1510b000c0c000b008042d01c0080741c050104806508a080418960418624004880c140400600f44a01800b403220980301d604101d09038101031050b84a5100c040040c010880101c50302c1c18100c4c0d004045c0390005860700002d0010a000b0070054000801d000303002c031241400a5000e903484e4482c4855660744ea82c0c1e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 897830620 1250 897829370 897829423
    0x180405040b0a050411041137050a03090506010906080d08060a050f0102242a030c0f0c071e061706060a1206030f1401021c1a060705 58
    0x11a001154050011402980480c81e5806141c01c1140c205001d40e90041c0b5200c8000001400c0701e4500c9403109510000084900150110130084688080c0100181c0001c2000c4002c2401d591031202c0d0303401c01c200300020402210b5000b0740c051040300d90002c048070019a1034904400c020701080c0201000f500c0788840c90301e006403084d819588540005011a28107510307001c00c1c00b2a04040034005410350054040270807294240e08105000c02d60305051850b424144070a010000403540b840728000c0c0c0e008409600e160220784400c880d00300394844030941c0d48150840301d80c46907008003c00d2707a445d4040c2031400a0078050005282c40c4140c2605941e500032a984c0070190b0391114103040103041c80c1013602c005403061600ca13014051100e400d0a10040100844940504544860300100c60f0071480d1328140c010b0104050310594861000301c021450400361740500b1003c61403903408101100e869049a01102d80304c03030740807400140f014003140c3e15900320346010f50301c072416003441400740e0104680889 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 897831870 1250 897830620 897830629
    0x11b0f20130b04092a1e120201050405041401050901050a05010e090a0b030a050a050d050c100c21050121170703031503060504031701080c0105031e0c18 67
    0x2031000c40000e00070090701d80441031240c00381802110150f8015030310480d09000c5003643d055001d0413509420b03110301129091480034000c0398140c00100c1080c081d00805440f814580782030400762801c4400854070003500d4030040b10103220725045660083c1c1000e6540c3e200950034086141a904200d840d00c115a88540c10300c07840030083d11402d0700140311408115401e0414414454010140620100780c1480f24070209262403099842110581d020780300a60a00400340a07000c05403000d1b01d07080d4a020320900d1160f0f83d840d06008480c280ea65514002282580541e9a403030721404080d40040d5400708062170a0014042481001e250007940c0c804102c1007001494554101544103c0030a516644442d01c0d814580040404030107055680c0c80c4010f0040c54681c902d0003c6110b02008a081e00e4507190080c8502c01c820000d0609810304001800071490104903049454420702c0c1054403590303886a408044070202c1084000c5909441c1440300e501c05510040c8440e10349800c035907416401031820701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 897833120 1250 897831870 897831923
    0xc030f120403060f06120503220f21200406150212070809040203040818030609061306110301150801060509010c0b042105040524030c09011b0f 63
    0x804800324200014000a40c290f44528280c50503000c00240c0c042d00d46d0904c0c9a4503100b0b2000b0380c0d4560020511002a00030300c5203040190110141c000240d41c50484601e20307202c1580526060f0441c621504c0e02da220b58404c00746a1950000348411310303120080280300740c200400041e1030045080900104440d5032400e2a8185071050361b00400c45807040078800103980e04604000c0303402a100300282d10441c1c1d00d6001560085015001c0c4568030540c6e0038068542512220115019070044030412039a01000b01c0d2013503000d030840f4803070340c0c0c029014a003a000070144841112580c2401000101e070030f00505204070b20945e401d0312007450590b2141c100342c900307010307642a840c00912a1401d2800048d81040c1d15a08944260074141d21440c140595022004400e00540300065011a00b0001ca01e020841410341c08a800c00001c510326604140300b00c244030040078290544000285035010741d10445050301c40300641210709144401c20300d00b20103542158182621020740d20680d2050413500080030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 897834370 1250 897833120 897833143
    0x108071b0b01050324071b0c0e0118050601020703080d0902220c050c030304110604260610121b030803040302031e04210c0b0c100c0509090f0421020c030f 68
    0x604190750b18402103e40780c000e104250f0120741c00e47c0c4036000140a060140024207076410b1481d0b819810051907000746131040201920403400e0006208290f600441c051017a07a4102000644d181c80812040019116a42c1d000350464090454540c80001518019031401440d1400f0702c192554804121500c1c0101c90400f106500100f022030009050b42d180306014410240840b42000d540304042d14210903401800f0f07000501c1040c07540000101401041e0384817640814942c040d03810004c40c50360400c441031000b4009038191500c0f085004103840c030000110340c0990b00513079034a414503000f526600f000207034480c08201e1040c072561031070185c03007960290340100703d00b0b0407030410740d82600701c04400d203e5056802d849503030700c0860b41300724140041503800740090040c590120121a404101c490340c59040c001c00c0070500c14101c2555800c20459000b0103004181a81515242450b4030300031000c040485ca45508200d101421030f4000c00e140c134640d001142a1010b80c0d00103000305131503000f50b242 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 897835620 1250 897834370 897834433
    0x105071e050717180307060f0507140304050619110a0809010804060e010609093809010e0d09062709020a02030910030e06240108071b0b010503 63
    0x61001941c452009401d14070f001c1c0d0003440c20b03540060a9500503074050310050800c0d4031560284405810100040d100a00482c50404500481460010118003441c5401020650f600500146030441041581c0180038024201c56407014007003030031584402c0d0102c8078400b03d09015048c0341030034000f08036401125000058540307001707005401100c010742c0052045442540d45d041d000300e121000d108100107040d961800060103240c5080200c801d90001c064803550410b10360f00c50300d8540d06c01050b9215004c503090a5141a2034540481c1d01400c48851100d4551081c40181e01015920001c80c0e41159115200c0742c203034040c0c10000240459513000b450f01c0b003aa44e0101003181d01141e0b07005105529051068909000d902ca000079509200443d02000107601e0b0035101c040900203010094001d20600c06070074010103500c0307015440c1c900041885051000a0b00081c1c134081c000c2030980d0b03040c806229104c0b03114195251070790440d0020301903640644541940c0c800107842610701421064503626 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 897836870 1250 897835620 897835667
    0x130509100f0e0702010e0d0e12010522140102030c03150618012a0b040c05010c0512090105390a050304050420030c120c0f0306040c051902030903010507 67
    0x802003150b084003415440456603500240c440c944030a21600d94002141d59410002d00c45070000c004da040b01c040940e482691410003800100c00e812411030070241c3c0600200039018200307041056800201c010400c05550000040065100d0b642e4001c500c16420300015100c500201014000316010340d44440070200c40b800c2e032000c1ca41d80134a00c05030701107250645001e41082901311000d00ea0f864507100b11100d2500c0300600080100740a510304c09081d0a1030305503d01c01703e80e100c030b0355681d001d0b0011b00264100001d03149450303480b030012074407460880580f40c0c10300500c1000030b01c041d0351040380341c1110414801c943e41c1c0c000c00c040390044440350450015410241800700b000000c1402000008052000c2184084500d904501841c4038112107030320f0781d480752010150030300350300c1000b0300700703088194104408040700c00400c090b04d410900c00d036030000300c104c1c6a85c000d0b2414071410010f05046041e452801c01c0072540000103080d10241503000340000d0b161100140c611000714080b01c0c49142a16 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 897838120 1250 897836870 897836879
    0x20c0f0123040305270409030305040209070f020303010e2502031b0c0604090b0616030207140a0605030f18100614041505060f250b0601230a050d02130509100f 70
    0x150202c100e40503511030b5000c1d060380c00700000b40441d00980008ca0100303855504100561505030724481d840b940c1d80c20300006803603800030000d4036480140107961107500e62401150919285001d010030b0030380200d102940d09003520b00c010350343e80c2240c0a0100d80101c0d1091071140e1000125480c111000040c001d00e04040c102020800503106001e121500401c2c01d00c0456911003680d0440300c80b541c000d03000341180034100f0ba035400302c107020922060b001d101002d0381041400d90042c12640e1099425003901200d84421164082c0c03503501e4454801148540404031441c0705d016407107641201c10021046050740c01100501041d143c040083c41282c00c481c0000300b01c5402c00900a10780348425a826520340464213206094010800001038441c00190343d07a4810481002c0800c1c0c0c014500b4245065002111550398034015440501090050b9020508a00c007a01400c16104508a0400e0964075010745c01c0d54480f10715140e20906128071900008111008041043c02041d900c1152840800c517080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 897839370 1250 897838120 897838147
    0x1f080c04091502030c0c100516080601031508070906210303150314072d030201110c091906050d05030a0e010509041a0103110a0801120501020c0f0123040305 69
    0x10a90203a60780030654a0110490b6400d20003103101c0c0c2c03154620341e0380b9480c0207a44036180c4400850f200c20302d980f901003800140792a40d11400c1080c041860044d01d25070b15080101d010300741c01007020240807401c01010031805000f01c0e83d981070303401800040101c60303524078010b1a1500d007081d01d00000e5207244000f40105e8402d401c4186015440350703400b66019640d603240c43e400781d0320300b00c50741d09030b00401c1c400d11981800b8210f56800d01e0401d120074420350b400d66000240e10401748402030500c070001421040007101886403460000004100e000e45140c040d6601800d192021032003003002e0b02c1c04002089a2030070756442003086070010001c0d0b091000c0c1c080c0a8070740c4209540b010341405024006035881d541d503801003143c14070988039030038203035140c110000d000e98032400900c2c4200c02003405204c07021a403080c3d113070b41110f891045200c4949190f04040d8024420b41055010f03a01421092a132100c034150801041902c04070300c03071061303101e2000980001d6241a80c008001490420110180c17415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 897840620 1250 897839370 897839381
    0x203130b1006122c07081002091f020c040f0e0c01080c070803060f1005093303180601170c0a06050a080709170a030809060403080402120f151f080c04 66
    0x2100c62076012541c013100300d11800c451501c02c038003000d507205440c10b0040d12010f2140d403014140501c42941040d40882c0061180d24008000384a103000e440a0a05040d1007009403885009010b041004050f800098040c0600641d00391401144282d101040f26540310b04c890074800d035000b809850612401d560380c85880c0c1e10207015150b0110000003415071907034503a0558800e00d010361b100e240e030720b404420510444070148a0078813145040042002c3c07000151001c181027030114082100c2d6070341e0703e007000801102d0a2990700612880740c5400071a000003089100c1c00111003ca04454403042d0300c604001c032040b25800740400007481440094146805860610780040e42410580e1010741c4620742c4180001040303a00c220158003005e0352105040d002b44c3d0494210500b000941020300d05510b02500b100400742c8001e0189400e0050094040400d010355140350391100240c40d1429119155005150000d841e24046054088502040030803850403002c212040305015003d418410401c2000525 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 897841726 1106 897840620 897840641
    0xc050d030c111f0e01150f080717030d0b030a02130606030c0e0a0e100e0408091201020702011e020a080c030316020d090b0d0f0203130b100612 63
    0x50808021200e0401070190100700408215045401004032801d817505036000940042542188247e502d405ca0720a40c0c21100415110000220090141d1130040a10380c41007000d500c4800480e001000c081c80c0060940da00c8a203183c001c500324a648204510f06180d80c0c0d5020702001c0c0d050f2180c064945041d19100603d0076002000c07400050050140384003801503200003c80446142d54004050300700302c60300c403016003040e2401c080107800c03110000f13114003442c100943c0c0c03441c0144240c80100390140d6880c200104084481d070010824546958218041c0150f0240820450001403804990200066030740b0b00d411028032080503d0074a985d030031500550b501c446d125611004081c2500c4001c0199036a900c28800c1003c010950310000e004c080713001008004510300741c1460110058020361403941c995075980809c080070101d5024000201e15600e008410803041036000b8601074 = true := by decide +kernel

theorem cover : BRFrame.Cov 897661870 897841726 := by
  have h0 := BRFrame.cov_init 897661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 897661870 ≤ n) (h2 : n < 897841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
